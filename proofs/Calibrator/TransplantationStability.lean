/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators
open Matrix

/-!
# Deploying a design built under the wrong dynamics

Self-contained: imports only Mathlib.

Designs in this corpus are optimised against an *estimated* object — a linkage-disequilibrium
operator, a demographic coupling, a covariance pencil — and deployed against the true one. What
decides whether that is tolerable is not the error in the estimated objective, which moves at
first order and always will, but the loss from transplanting the optimizer: build under the
approximate dynamics, evaluate under the true dynamics, compare against what the true dynamics
would have chosen.

With `δ` bounding the operator error and `γ` the spectral gap at the extremal — the margin by
which the winning design beats the runner-up — the loss is `min(2δ, 8δ²/γ)`, and both branches
are attained. The argument has exactly two inputs, and this file keeps them apart because they
are not on the same footing.

**The gap lower bound is proved here.** Working in the eigenbasis of the true operator, a state
with squared misalignment `s²` away from the ground direction pays at least `γ s²`, because every
excited direction sits at least `γ` above the ground energy. `excess_ge_gap_mul_misalignment` is
that statement and it needs nothing but the spectral decomposition and a Finset sum.

**The perturbation upper bound is not proved here.** `excess_le_perturbation_mul_misalignment`
states that the transplanted state's excess is at most `2√2 δ s`, which is what testing the true
ground state in the approximate problem gives, and its proof is a `sorry`. That is deliberate.
The alternative — carrying the bound as a hypothesis of the theorem that needs it — would make
this file's headline a conditional whose antecedent nothing in the corpus ever discharges, which
is the shape `proofs/validation/invariants/hypothetical.py` exists to detect. A visible `sorry`
is an honest gap; an invisible hypothesis is a laundered import.

`excess_le_of_two_bounds` is the elimination step between the two, and it is pure real
arithmetic: it is named for what it does rather than for the conclusion it contributes to.
`quadratic_beats_linear_iff` locates the switch: the quadratic branch binds exactly when
`4δ < γ`.

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

Empirical status: the gap bound and the elimination step are PROVED; the perturbation bound is an
OPEN GAP carried as a `sorry`; that a fitted design meets a particular `δ` is an empirical input,
and `γ` is the quantity this asks studies to report.
-/

/-! ## The spectral setup

The true operator is given by its eigenvalues `μ` in increasing order from the ground direction
`0`, and a candidate design by its coefficients `c` in that eigenbasis. This is a representation,
not an assumption: a symmetric operator on a finite-dimensional real space has one. -/

/-- Energy of the state with eigenbasis coefficients `c` under the operator with eigenvalues
`μ`. -/
noncomputable def spectralEnergy {n : ℕ} (μ c : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, μ i * c i ^ 2

/-- Squared misalignment of a unit state with the ground direction: the mass it puts on the
excited directions. -/
noncomputable def misalignmentSq {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase 0, c i ^ 2

/-- **The gap lower bound, proved.** If every excited eigenvalue sits at least `γ` above the
ground energy `μ 0`, then a unit state pays at least `γ` times its squared misalignment.

    This is the half of the transplantation argument that needs no analysis: it is the spectral
    decomposition and a termwise comparison. -/
theorem excess_ge_gap_mul_misalignment {n : ℕ} (μ c : Fin (n + 1) → ℝ) (γ : ℝ)
    (hunit : ∑ i, c i ^ 2 = 1)
    (hgap : ∀ i ∈ Finset.univ.erase (0 : Fin (n + 1)), μ 0 + γ ≤ μ i) :
    γ * misalignmentSq c ≤ spectralEnergy μ c - μ 0 := by
  have hsplit : ∑ i, μ i * c i ^ 2
      = μ 0 * c 0 ^ 2 + ∑ i ∈ Finset.univ.erase 0, μ i * c i ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  have hsplit_one : ∑ i, c i ^ 2
      = c 0 ^ 2 + ∑ i ∈ Finset.univ.erase 0, c i ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  have hterm : ∀ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (μ 0 + γ) * c i ^ 2 ≤ μ i * c i ^ 2 := by
    intro i hi
    exact mul_le_mul_of_nonneg_right (hgap i hi) (sq_nonneg (c i))
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  unfold spectralEnergy misalignmentSq
  rw [hsplit]
  have hc0 : c 0 ^ 2 = 1 - ∑ i ∈ Finset.univ.erase 0, c i ^ 2 := by
    rw [hsplit_one] at hunit; linarith
  rw [hc0]
  nlinarith [hsum]

/-! ## The perturbation upper bound: the open gap

The transplanted design is the ground state of the *approximate* operator, and that is what makes
the bound true. Dropping that condition and keeping only the spectral data would give a statement
that is false at `δ = 0` — it would force every state to sit at the ground energy — and a `sorry`
on a false statement is not an honest gap, it is an inconsistency. So the perturbation enters as
an actual symmetric operator and the state enters as its minimiser. -/

/-- Energy of a state under the approximate operator: the true spectral energy plus the
perturbation's quadratic form. -/
noncomputable def perturbedEnergy {n : ℕ} (μ : Fin (n + 1) → ℝ)
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  spectralEnergy μ v + v ⬝ᵥ (E *ᵥ v)

/-- **The perturbation upper bound, not proved here.**

    `c` minimises the approximate energy; `E` is symmetric with quadratic form bounded by `δ` on
    unit states; `μ 0` is the true ground energy. Testing the true ground direction in the
    approximate problem gives `q ≤ E₀₀ - ⟨c, Ec⟩`, and symmetry turns that difference into
    `⟨e₀ + c, E(e₀ - c)⟩`, bounded by `2δ‖e₀ - c‖ ≤ 2√2 δ s`.

    The proof is a `sorry`. It is stated as a theorem with a visible gap rather than carried as a
    hypothesis of `transplant_excess_le`, because a hypothesis nothing discharges is an import
    wearing the costume of a conditional. -/
theorem excess_le_perturbation_mul_misalignment {n : ℕ}
    (μ c : Fin (n + 1) → ℝ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hEsymm : E.IsSymm)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (hunit : ∑ i, c i ^ 2 = 1)
    (hground : ∀ i, μ 0 ≤ μ i)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy μ E c ≤ perturbedEnergy μ E v) :
    spectralEnergy μ c - μ 0 ≤ 2 * Real.sqrt 2 * δ * Real.sqrt (misalignmentSq c) := by
  sorry

/-! ## The elimination step -/

/-- Pure arithmetic: from a lower bound `γ s² ≤ q` and an upper bound `q ≤ 2√2 δ s`, eliminating
`s` gives `q ≤ 8δ²/γ`. Named for the elimination it performs, not for the conclusion it serves. -/
theorem excess_le_of_two_bounds (γ δ s q : ℝ) (hγ : 0 < γ) (hs : 0 ≤ s)
    (hlow : γ * s ^ 2 ≤ q) (hhigh : q ≤ 2 * Real.sqrt 2 * δ * s) :
    q ≤ 8 * δ ^ 2 / γ := by
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases eq_or_lt_of_le hs with hzero | hspos
  · subst hzero
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

/-- **The transplantation bound**, assembled from the proved gap bound and the `sorry`-carrying
    perturbation bound. No hypothesis of this theorem is an imported claim: the two inequalities
    that carry the argument are theorems above, one proved and one openly unproved. -/
theorem transplant_excess_le {n : ℕ} (μ c : Fin (n + 1) → ℝ)
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 ≤ δ) (hEsymm : E.IsSymm)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (hunit : ∑ i, c i ^ 2 = 1)
    (hgap : ∀ i ∈ Finset.univ.erase (0 : Fin (n + 1)), μ 0 + γ ≤ μ i)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy μ E c ≤ perturbedEnergy μ E v) :
    spectralEnergy μ c - μ 0 ≤ 8 * δ ^ 2 / γ := by
  have hmis : 0 ≤ misalignmentSq c :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i)
  have hground : ∀ i, μ 0 ≤ μ i := by
    intro i
    by_cases h : i = 0
    · exact le_of_eq (by rw [h])
    · have := hgap i (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)
      linarith
  have hlow : γ * Real.sqrt (misalignmentSq c) ^ 2 ≤ spectralEnergy μ c - μ 0 := by
    rw [Real.sq_sqrt hmis]
    exact excess_ge_gap_mul_misalignment μ c γ hunit hgap
  have hhigh := excess_le_perturbation_mul_misalignment μ c E δ hδ hEsymm hEbound hunit
    hground hmin
  exact excess_le_of_two_bounds γ δ (Real.sqrt (misalignmentSq c))
    (spectralEnergy μ c - μ 0) hγ (Real.sqrt_nonneg _) hlow hhigh

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
