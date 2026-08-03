/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Calibrator

/-!
# Deploying a design built under the wrong dynamics

Self-contained: imports only Mathlib.

Designs in this corpus are optimised against an estimated object — a linkage-disequilibrium
operator, a demographic coupling, a covariance pencil — and deployed against the true one. What
decides whether that is tolerable is not the error in the estimated objective, which moves at
first order and always will, but the loss from transplanting the optimizer: build under the
approximate dynamics, evaluate under the true dynamics, compare against what the true dynamics
would have chosen.

With `δ` bounding the operator error and `γ` the spectral gap of the pencil at the extremal — the
margin by which the winning design beats the runner-up — the loss is `min(2δ, 8δ²/γ)`, and both
branches are attained. `transplant_excess_le` proves the quadratic branch from the two
inequalities that carry the argument: the loss is at least `γ` times the squared misalignment,
and at most `2√2 δ` times the misalignment. Eliminating the misalignment gives the constant `8/γ`.
`quadratic_beats_linear_iff` locates the switch: the quadratic branch binds exactly when `4δ < γ`.

The degenerate branch is not a technicality. `crossing_loss_linear` is a witness at `γ = 0`: two
designs whose true values differ by `δ`, and an approximate model within `δ` of the truth
everywhere that ranks them the other way. The transplanted optimizer lands on the wrong branch and
pays the full `δ`. Near-ties between candidate designs are common — two variant panels with almost
equal source performance, two shrinkage levels, two ancestry-weighting schemes — and there the
usual argument that stationarity at the optimum makes small model error cost second order fails.

Operationally this asks for one number. `γ` is the margin between the best and second-best design
in the fitted objective, and with an error budget `δ` it converts into a deployment-loss bound
with no further modelling. The same scalar governs two things the corpus states separately: a
frontier kink is a vanishing gap, and a phase transition in the horizon optimizer is a vanishing
gap. Degeneracy of the extremal, vanishing frontier curvature, and loss of second-order
transplantation stability are one locus.

Empirical status: DERIVED. The bound follows from the two stated inequalities; that a fitted
design satisfies them with a particular `δ` is an empirical input, and `γ` is the quantity this
asks studies to report.
-/

/-- The transplantation bound. `q` is the excess cost of the transplanted design under the true
    dynamics, `s` its misalignment with the true optimizer, `γ` the spectral gap at the extremal
    and `δ` the operator error. From `γ s² ≤ q` and `q ≤ 2√2 δ s`, the loss is quadratic in the
    model error with constant `8/γ`. -/
theorem transplant_excess_le (γ δ s q : ℝ) (hγ : 0 < γ) (hs : 0 ≤ s)
    (hlow : γ * s ^ 2 ≤ q) (hhigh : q ≤ 2 * Real.sqrt 2 * δ * s) :
    q ≤ 8 * δ ^ 2 / γ := by
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases eq_or_lt_of_le hs with hzero | hspos
  · -- No misalignment: the transplanted design is the true optimizer.
    subst hzero
    have hq : q ≤ 0 := by simpa using hhigh
    have hnn : (0 : ℝ) ≤ 8 * δ ^ 2 / γ := div_nonneg (by positivity) hγ.le
    linarith
  · have hchain : γ * s * s ≤ 2 * Real.sqrt 2 * δ * s := by nlinarith [hlow, hhigh]
    have hstep : γ * s ≤ 2 * Real.sqrt 2 * δ :=
      le_of_mul_le_mul_right hchain hspos
    have hfac : (0 : ℝ) ≤ 2 * Real.sqrt 2 * δ :=
      le_trans (le_of_lt (mul_pos hγ hspos)) hstep
    have h1 : q * γ ≤ 2 * Real.sqrt 2 * δ * s * γ :=
      mul_le_mul_of_nonneg_right hhigh hγ.le
    have hre : 2 * Real.sqrt 2 * δ * s * γ = 2 * Real.sqrt 2 * δ * (γ * s) := by ring
    have h2 : 2 * Real.sqrt 2 * δ * (γ * s) ≤ 2 * Real.sqrt 2 * δ * (2 * Real.sqrt 2 * δ) :=
      mul_le_mul_of_nonneg_left hstep hfac
    have h3 : 2 * Real.sqrt 2 * δ * (2 * Real.sqrt 2 * δ) = 8 * δ ^ 2 := by
      rw [show 2 * Real.sqrt 2 * δ * (2 * Real.sqrt 2 * δ)
            = 4 * (Real.sqrt 2 * Real.sqrt 2) * δ ^ 2 by ring, hroot]
      ring
    rw [le_div_iff₀ hγ]
    linarith [h1, h2, h3, hre]

/-- The loss is bounded by the smaller of the two estimates. -/
theorem transplant_excess_le_min (γ δ s q : ℝ) (hγ : 0 < γ) (hs : 0 ≤ s)
    (hcrude : q ≤ 2 * δ) (hlow : γ * s ^ 2 ≤ q) (hhigh : q ≤ 2 * Real.sqrt 2 * δ * s) :
    q ≤ min (2 * δ) (8 * δ ^ 2 / γ) :=
  le_min hcrude (transplant_excess_le γ δ s q hγ hs hlow hhigh)

/-- The quadratic branch binds exactly when the model error is small against the margin,
    `4δ < γ`. Above that the bound is the linear one. -/
theorem quadratic_beats_linear_iff (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) :
    8 * δ ^ 2 / γ < 2 * δ ↔ 4 * δ < γ := by
  rw [div_lt_iff₀ hγ]
  constructor <;> intro h <;> nlinarith

/-! ## The degenerate branch is attained -/

/-- True value of two candidate designs, separated by `δ`. -/
noncomputable def trueDesignValue (δ : ℝ) (i : Fin 2) : ℝ := if i = 0 then 1 else 1 - δ

/-- Value of the same two designs under an approximate model, which is within `δ` of the truth
at each design and ranks them the other way. -/
noncomputable def approxDesignValue (δ : ℝ) (i : Fin 2) : ℝ := if i = 0 then 1 - δ else 1

/-- The approximate model never undervalues a design by more than `δ`. -/
theorem approxDesignValue_lower (δ : ℝ) (hδ : 0 ≤ δ) (i : Fin 2) :
    trueDesignValue δ i - δ ≤ approxDesignValue δ i := by
  by_cases h : i = 0 <;> simp [trueDesignValue, approxDesignValue, h] <;> linarith

/-- The approximate model never overvalues a design by more than `δ`. -/
theorem approxDesignValue_upper (δ : ℝ) (hδ : 0 ≤ δ) (i : Fin 2) :
    approxDesignValue δ i ≤ trueDesignValue δ i + δ := by
  by_cases h : i = 0 <;> simp [trueDesignValue, approxDesignValue, h] <;> linarith

/-- At a degeneracy the loss is linear in the model error: the approximate model prefers design
    `1`, the truth prefers design `0`, and deploying the approximate choice costs exactly `δ`. -/
theorem crossing_loss_linear (δ : ℝ) (hδ : 0 < δ) :
    approxDesignValue δ 0 < approxDesignValue δ 1 ∧
      trueDesignValue δ 1 < trueDesignValue δ 0 ∧
      trueDesignValue δ 0 - trueDesignValue δ 1 = δ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [trueDesignValue, approxDesignValue] <;> linarith

end Calibrator
