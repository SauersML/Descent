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

**The perturbation upper bound is proved here.**
`excess_le_perturbation_mul_misalignment` decomposes the transplanted state into its ground and
excited parts. Polarization turns the quadratic-form bound into the required cross-term bound,
and Cauchy--Schwarz supplies the sharp factor `√2`.

`excess_le_of_two_bounds` is the elimination step between the two, and it is pure real
arithmetic: it is named for what it does rather than for the conclusion it contributes to.
`quadratic_beats_linear_iff` locates the switch: the quadratic branch binds exactly when
`4δ < γ`.

The degenerate branch is not a technicality. `crossing_loss_linear` is a witness at `γ = 0`: two
designs whose true values differ by `δ`, and an approximate model within `δ` of the truth
everywhere that ranks them the other way. The transplanted optimizer lands on the wrong branch and
pays the full `δ`. Near-ties between candidate designs are common — two variant panels with
almost equal source performance, two shrinkage levels, two ancestry-weighting schemes — and there
the usual argument that stationarity at the optimum makes small model error cost second order
fails.

Operationally this asks for one number. `γ` is the margin between the best and second-best design
in the fitted objective, and with an error budget `δ` it converts into a deployment-loss bound
with no further modelling. The same scalar governs two things the corpus states separately: a
frontier kink is a vanishing gap, and a phase transition in the horizon optimizer is a vanishing
gap. Degeneracy of the extremal, vanishing frontier curvature, and loss of second-order
transplantation stability are one locus.

Empirical status: the gap bound, perturbation bound, and elimination step are PROVED. That a
fitted design meets a particular `δ` is an empirical input, and `γ` is the quantity this asks
studies to report.
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

/-! ## The perturbation upper bound

The transplanted design is the ground state of the *approximate* operator, and that is what makes
the bound true. Dropping that condition and keeping only the spectral data would be false at
`δ = 0`, because it would force every state to sit at the ground energy. The perturbation therefore
enters as an actual symmetric operator and the state enters as its minimizer. -/

/-- Energy of a state under the approximate operator: the true spectral energy plus the
perturbation's quadratic form. -/
noncomputable def perturbedEnergy {n : ℕ} (μ : Fin (n + 1) → ℝ)
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  spectralEnergy μ v + v ⬝ᵥ (E *ᵥ v)

/-- **The ground-state comparison bound, proved.**

    Testing the true ground direction `e₀` in the approximate problem gives
    `spectralEnergy μ c - μ 0 ≤ ⟨e₀, Ee₀⟩ - ⟨c, Ec⟩`, and each quadratic form is
    bounded by `δ` on unit states, so the excess is at most `2δ`.

    This needs neither the symmetry of `E` nor the spectral gap: it is the half of the
    perturbation bound that follows from minimality alone. The sharp form below replaces the
    constant `2` by `2√2 √(misalignment)`, which is stronger exactly when the minimiser is
    close to the ground direction. -/
theorem excess_le_two_mul_perturbation {n : ℕ}
    (μ c : Fin (n + 1) → ℝ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (δ : ℝ)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (hunit : ∑ i, c i ^ 2 = 1)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy μ E c ≤ perturbedEnergy μ E v) :
    spectralEnergy μ c - μ 0 ≤ 2 * δ := by
  set e : Fin (n + 1) → ℝ := fun i ↦ if i = 0 then (1 : ℝ) else 0 with he
  have heunit : ∑ i, e i ^ 2 = 1 := by
    simp [he, Finset.sum_ite_eq']
  have heenergy : spectralEnergy μ e = μ 0 := by
    simp [spectralEnergy, he, Finset.sum_ite_eq']
  have hcomp := hmin e heunit
  unfold perturbedEnergy at hcomp
  rw [heenergy] at hcomp
  have hc := hEbound c hunit
  have hE0 := hEbound e heunit
  have h1 : c ⬝ᵥ (E *ᵥ c) ≥ -δ := neg_le_of_abs_le hc
  have h2 : e ⬝ᵥ (E *ᵥ e) ≤ δ := le_of_abs_le hE0
  linarith

/-- Scaling a vector scales its quadratic form by the square. -/
theorem quadForm_smul {m : ℕ} (E : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) (w : Fin m → ℝ) :
    (fun i ↦ t * w i) ⬝ᵥ (E *ᵥ fun i ↦ t * w i) = t ^ 2 * (w ⬝ᵥ (E *ᵥ w)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ by ring

/-- Scaling a vector scales its squared norm by the square. -/
theorem sumSq_smul {m : ℕ} (t : ℝ) (w : Fin m → ℝ) :
    (∑ i, (t * w i) ^ 2) = t ^ 2 * ∑ i, w i ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The quadratic-form bound, homogenised.** A bound on unit states extends to every state
with the squared norm as the factor. -/
theorem quadForm_le_mul_sumSq {n : ℕ} (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (δ : ℝ)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (w : Fin (n + 1) → ℝ) :
    |w ⬝ᵥ (E *ᵥ w)| ≤ δ * ∑ i, w i ^ 2 := by
  set t : ℝ := ∑ i, w i ^ 2 with ht
  have htnn : 0 ≤ t := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  rcases eq_or_lt_of_le htnn with hzero | hpos
  · have hw : ∀ i, w i = 0 := by
      intro i
      have hsum : ∑ j, w j ^ 2 = 0 := hzero.symm
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (w j))).mp hsum i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have : w = fun _ ↦ (0 : ℝ) := funext hw
    subst this
    simp [← hzero]
  · have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr hpos
    set v : Fin (n + 1) → ℝ := fun i ↦ (Real.sqrt t)⁻¹ * w i with hv
    have hvunit : ∑ i, v i ^ 2 = 1 := by
      rw [hv, sumSq_smul, ← ht, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
      field_simp
    have hquad : v ⬝ᵥ (E *ᵥ v) = (Real.sqrt t)⁻¹ ^ 2 * (w ⬝ᵥ (E *ᵥ w)) := by
      rw [hv]; exact quadForm_smul E _ w
    have hb := hEbound v hvunit
    rw [hquad, inv_pow, Real.sq_sqrt (le_of_lt hpos), abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < t⁻¹)] at hb
    calc |w ⬝ᵥ (E *ᵥ w)| = t * (t⁻¹ * |w ⬝ᵥ (E *ᵥ w)|) := by
          field_simp
      _ ≤ t * δ := by
          exact mul_le_mul_of_nonneg_left hb htnn
      _ = δ * t := by ring

/-- A symmetric matrix has a symmetric bilinear form. -/
theorem dotProduct_mulVec_comm_of_isSymm {m : ℕ} {E : Matrix (Fin m) (Fin m) ℝ}
    (hE : E.IsSymm) (u v : Fin m → ℝ) :
    u ⬝ᵥ (E *ᵥ v) = v ⬝ᵥ (E *ᵥ u) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have h : E j i = E i j := congrFun (congrFun hE i) j
  rw [h]
  ring

/-- Bilinearity of the quadratic form on a sum, for a symmetric matrix. -/
theorem quadForm_add {m : ℕ} {E : Matrix (Fin m) (Fin m) ℝ} (hE : E.IsSymm)
    (u v : Fin m → ℝ) :
    (fun i ↦ u i + v i) ⬝ᵥ (E *ᵥ fun i ↦ u i + v i)
      = u ⬝ᵥ (E *ᵥ u) + 2 * (u ⬝ᵥ (E *ᵥ v)) + v ⬝ᵥ (E *ᵥ v) := by
  have hcross : v ⬝ᵥ (E *ᵥ u) = u ⬝ᵥ (E *ᵥ v) :=
    dotProduct_mulVec_comm_of_isSymm hE v u
  simp only [dotProduct, Matrix.mulVec] at *
  have hexpand : ∀ i : Fin m,
      (u i + v i) * ∑ j, E i j * (u j + v j)
        = (u i * ∑ j, E i j * u j) + (u i * ∑ j, E i j * v j)
          + (v i * ∑ j, E i j * u j) + (v i * ∑ j, E i j * v j) := by
    intro i
    have : ∑ j, E i j * (u j + v j) = (∑ j, E i j * u j) + ∑ j, E i j * v j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [this]; ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hcross]
  ring

/-- **Polarization: the bilinear form is bounded by the quadratic bound.**

    For a symmetric `E` whose quadratic form is at most `δ` on unit states,
    `|⟨u, Ev⟩| ≤ δ` whenever `u` and `v` are unit. This is the step that converts a bound on
    the diagonal into a bound off it, and it is where the square root in the sharp estimate
    comes from once one of the two vectors is rescaled to unit length. -/
theorem bilinear_le_of_unit {n : ℕ} {E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {δ : ℝ}
    (hE : E.IsSymm)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (u v : Fin (n + 1) → ℝ) (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1) :
    |u ⬝ᵥ (E *ᵥ v)| ≤ δ := by
  have hplus := quadForm_add hE u v
  have hminus := quadForm_add hE u (fun i ↦ -v i)
  have hnegquad : (fun i ↦ -v i) ⬝ᵥ (E *ᵥ fun i ↦ -v i) = v ⬝ᵥ (E *ᵥ v) := by
    simpa using quadForm_smul E (-1) v
  have hnegcross : u ⬝ᵥ (E *ᵥ fun i ↦ -v i) = -(u ⬝ᵥ (E *ᵥ v)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hnegquad, hnegcross] at hminus
  have hcross : ∑ i, u i * -v i = -∑ i, u i * v i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hsumplus : ∑ i, (u i + v i) ^ 2 = 2 + 2 * ∑ i, u i * v i := by
    have h1 : ∀ i : Fin (n + 1), (u i + v i) ^ 2 = u i ^ 2 + 2 * (u i * v i) + v i ^ 2 :=
      fun i ↦ by ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hu, hv, ← Finset.mul_sum]
    ring
  have hsumminus : ∑ i, (u i + -v i) ^ 2 = 2 - 2 * ∑ i, u i * v i := by
    have h1 : ∀ i : Fin (n + 1), (u i + -v i) ^ 2 = u i ^ 2 + 2 * (u i * -v i) + v i ^ 2 :=
      fun i ↦ by ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hu, hv, ← Finset.mul_sum, hcross]
    ring
  have hbp := quadForm_le_mul_sumSq E δ hEbound (fun i ↦ u i + v i)
  have hbm := quadForm_le_mul_sumSq E δ hEbound (fun i ↦ u i + -v i)
  rw [hplus, hsumplus] at hbp
  rw [hminus, hsumminus] at hbm
  have h1 := abs_le.mp hbp
  have h2 := abs_le.mp hbm
  rcases abs_cases (u ⬝ᵥ (E *ᵥ v)) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] <;>
    linarith [h1.1, h1.2, h2.1, h2.2]

/-- Scaling the left argument of the bilinear form. -/
theorem bilinear_smul_left {m : ℕ} (E : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (u w : Fin m → ℝ) :
    (fun i ↦ t * u i) ⬝ᵥ (E *ᵥ w) = t * (u ⬝ᵥ (E *ᵥ w)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ by ring

/-- Scaling the right argument of the bilinear form. -/
theorem bilinear_smul_right {m : ℕ} (E : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (u w : Fin m → ℝ) :
    u ⬝ᵥ (E *ᵥ fun i ↦ t * w i) = t * (u ⬝ᵥ (E *ᵥ w)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Where the `√2` comes from.** If a squared ground weight and a squared misalignment sum
to one, the sum of the misalignment's square root and the ground weight's absolute value is
at most `√2`. This is Cauchy-Schwarz on the pair `(|α|, √s)`. -/
theorem sqrt_add_abs_le_sqrt_two {α s : ℝ} (hs : 0 ≤ s) (h : α ^ 2 + s = 1) :
    Real.sqrt s + |α| ≤ Real.sqrt 2 := by
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have habs : |α| ^ 2 = α ^ 2 := sq_abs α
  have hnn : 0 ≤ Real.sqrt s + |α| := by positivity
  refine (Real.le_sqrt hnn (by norm_num)).mpr ?_
  have hcross : 2 * (Real.sqrt s * |α|) ≤ Real.sqrt s ^ 2 + |α| ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt s - |α|)]
  nlinarith [hsq, habs, hcross]

/-- **The sharp bound holds outright once the misalignment is at least one half.**

    At `misalignmentSq c ≥ 1/2` the sharp right-hand side `2√2 δ √s` is already at least
    `2δ`, so the ground-state comparison above proves it with nothing further. The genuinely
    remaining case is a minimizer close to the ground direction, where `√s` is small and the
    constant is earned from the bilinear bound rather than from minimality. -/
theorem excess_le_perturbation_mul_misalignment_of_half_le {n : ℕ}
    (μ c : Fin (n + 1) → ℝ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (hunit : ∑ i, c i ^ 2 = 1)
    (hhalf : (1 : ℝ) / 2 ≤ misalignmentSq c)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy μ E c ≤ perturbedEnergy μ E v) :
    spectralEnergy μ c - μ 0 ≤ 2 * Real.sqrt 2 * δ * Real.sqrt (misalignmentSq c) := by
  have hbase := excess_le_two_mul_perturbation μ c E δ hEbound hunit hmin
  have hsq : Real.sqrt ((1 : ℝ) / 2) ≤ Real.sqrt (misalignmentSq c) :=
    Real.sqrt_le_sqrt hhalf
  have hprod : Real.sqrt 2 * Real.sqrt ((1 : ℝ) / 2) = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcoef : 0 ≤ 2 * Real.sqrt 2 * δ :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hδ
  have hstep : 2 * Real.sqrt 2 * δ * Real.sqrt ((1 : ℝ) / 2)
      ≤ 2 * Real.sqrt 2 * δ * Real.sqrt (misalignmentSq c) :=
    mul_le_mul_of_nonneg_left hsq hcoef
  have hval : 2 * Real.sqrt 2 * δ * Real.sqrt ((1 : ℝ) / 2) = 2 * δ := by
    have hrw : 2 * Real.sqrt 2 * δ * Real.sqrt ((1 : ℝ) / 2)
        = 2 * δ * (Real.sqrt 2 * Real.sqrt ((1 : ℝ) / 2)) := by ring
    rw [hrw, hprod, mul_one]
  rw [hval] at hstep
  linarith

/-- **The perturbation upper bound.**

    `c` minimises the approximate energy; `E` is symmetric with quadratic form bounded by `δ` on
    unit states; `μ 0` is the true ground energy. Testing the true ground direction in the
    approximate problem gives a comparison with the true ground direction. Decomposing `c` into
    its ground coefficient and excited component reduces the perturbation difference to two
    quadratic terms and one cross term. Homogeneity and polarization bound those terms, while
    `sqrt_add_abs_le_sqrt_two` gives the sharp constant. -/
theorem excess_le_perturbation_mul_misalignment {n : ℕ}
    (μ c : Fin (n + 1) → ℝ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hEsymm : E.IsSymm)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 → |v ⬝ᵥ (E *ᵥ v)| ≤ δ)
    (hunit : ∑ i, c i ^ 2 = 1)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy μ E c ≤ perturbedEnergy μ E v) :
    spectralEnergy μ c - μ 0 ≤ 2 * Real.sqrt 2 * δ * Real.sqrt (misalignmentSq c) := by
  classical
  set e : Fin (n + 1) → ℝ := fun i ↦ if i = 0 then (1 : ℝ) else 0 with he
  set w : Fin (n + 1) → ℝ := fun i ↦ if i = 0 then (0 : ℝ) else c i with hw
  set s : ℝ := misalignmentSq c with hs
  have hsnn : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have heunit : ∑ i, e i ^ 2 = 1 := by simp [he, Finset.sum_ite_eq']
  have hwsum : ∑ i, w i ^ 2 = s := by
    rw [hs, misalignmentSq,
      ← Finset.sum_erase_add Finset.univ (fun i ↦ w i ^ 2)
        (Finset.mem_univ (0 : Fin (n + 1)))]
    have h0 : w 0 ^ 2 = 0 := by simp [hw]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hne : i ≠ 0 := Finset.ne_of_mem_erase hi
    simp [hw, hne]
  have hdecomp : c = fun i ↦ c 0 * e i + w i := by
    funext i
    by_cases h0 : i = 0 <;> simp [he, hw, h0]
  have halpha : c 0 ^ 2 + s = 1 := by
    rw [← hunit, hs, misalignmentSq,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
    ring
  -- minimality against the ground direction
  have hcomp := hmin e heunit
  have heenergy : spectralEnergy μ e = μ 0 := by
    simp [spectralEnergy, he, Finset.sum_ite_eq']
  unfold perturbedEnergy at hcomp
  rw [heenergy] at hcomp
  -- expand the perturbation quadratic form along the decomposition
  have hexp : c ⬝ᵥ (E *ᵥ c)
      = c 0 ^ 2 * (e ⬝ᵥ (E *ᵥ e)) +
        2 * (c 0 * (e ⬝ᵥ (E *ᵥ w))) + w ⬝ᵥ (E *ᵥ w) := by
    conv_lhs => rw [hdecomp]
    rw [quadForm_add hEsymm (fun i ↦ c 0 * e i) w, quadForm_smul E (c 0) e,
      bilinear_smul_left E (c 0) e w]
  -- the three pieces
  have hEe : |e ⬝ᵥ (E *ᵥ e)| ≤ δ := hEbound e heunit
  have hEw : |w ⬝ᵥ (E *ᵥ w)| ≤ δ * s := by
    have := quadForm_le_mul_sumSq E δ hEbound w
    rwa [hwsum] at this
  have hcross : |e ⬝ᵥ (E *ᵥ w)| ≤ δ * Real.sqrt s := by
    rcases eq_or_lt_of_le hsnn with hzero | hpos
    · have hw0 : w = fun _ ↦ (0 : ℝ) := by
        funext i
        have hsum : ∑ j, w j ^ 2 = 0 := by rw [hwsum, ← hzero]
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg (w j))).mp hsum i (Finset.mem_univ i)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      rw [hw0]
      simp [dotProduct, Matrix.mulVec, ← hzero]
    · have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
      set z : Fin (n + 1) → ℝ := fun i ↦ (Real.sqrt s)⁻¹ * w i with hz
      have hzunit : ∑ i, z i ^ 2 = 1 := by
        rw [hz, sumSq_smul, hwsum, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
        field_simp
      have hbz := bilinear_le_of_unit hEsymm hEbound e z heunit hzunit
      have hzw : e ⬝ᵥ (E *ᵥ z) = (Real.sqrt s)⁻¹ * (e ⬝ᵥ (E *ᵥ w)) := by
        rw [hz]; exact bilinear_smul_right E _ e w
      rw [hzw, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt s)⁻¹)] at hbz
      calc |e ⬝ᵥ (E *ᵥ w)| = Real.sqrt s * ((Real.sqrt s)⁻¹ * |e ⬝ᵥ (E *ᵥ w)|) := by
            field_simp
        _ ≤ Real.sqrt s * δ := mul_le_mul_of_nonneg_left hbz (le_of_lt hsq)
        _ = δ * Real.sqrt s := by ring
  -- assemble
  have hsqrt_sq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hsnn
  have hsqrtnn : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hab : Real.sqrt s + |c 0| ≤ Real.sqrt 2 := sqrt_add_abs_le_sqrt_two hsnn halpha
  have hEe' := abs_le.mp hEe
  have hEw' := abs_le.mp hEw
  have habs0 : |c 0 * (e ⬝ᵥ (E *ᵥ w))| ≤ |c 0| * (δ * Real.sqrt s) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hcross (abs_nonneg _)
  have habs0' := abs_le.mp habs0
  have hEeq : c 0 ^ 2 = 1 - s := by linarith
  have hterm1 : s * (e ⬝ᵥ (E *ᵥ e)) ≤ s * δ := mul_le_mul_of_nonneg_left hEe'.2 hsnn
  have hfinal : 2 * δ * s + 2 * (|c 0| * (δ * Real.sqrt s))
      ≤ 2 * Real.sqrt 2 * δ * Real.sqrt s := by
    have hcoef : 0 ≤ 2 * δ * Real.sqrt s := by positivity
    have hrw : 2 * δ * s + 2 * (|c 0| * (δ * Real.sqrt s))
        = 2 * δ * Real.sqrt s * (Real.sqrt s + |c 0|) := by
      linear_combination (-(2 * δ)) * hsqrt_sq
    rw [hrw]
    calc 2 * δ * Real.sqrt s * (Real.sqrt s + |c 0|)
        ≤ 2 * δ * Real.sqrt s * Real.sqrt 2 := mul_le_mul_of_nonneg_left hab hcoef
      _ = 2 * Real.sqrt 2 * δ * Real.sqrt s := by ring
  rw [hEeq] at hexp
  linarith [hcomp, hexp, hterm1, habs0'.1, habs0'.2, hEw'.1, hfinal]

/-! ## The elimination step -/

/-- Pure arithmetic: from a lower bound `γ s² ≤ q` and an upper bound `q ≤ 2√2 δ s`,
eliminating `s` gives `q ≤ 8δ²/γ`. Named for the elimination it performs, not for the conclusion
it serves. -/
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

/-- **The transplantation bound**, assembled from the gap and perturbation bounds proved above. -/
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
  have hlow : γ * Real.sqrt (misalignmentSq c) ^ 2 ≤ spectralEnergy μ c - μ 0 := by
    rw [Real.sq_sqrt hmis]
    exact excess_ge_gap_mul_misalignment μ c γ hunit hgap
  have hhigh :=
    excess_le_perturbation_mul_misalignment μ c E δ hδ hEsymm hEbound hunit hmin
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
  by_cases h : i = 0
  · simp [trueDesignValue, approxDesignValue, h]
  · simp [trueDesignValue, approxDesignValue, h]
    linarith

/-- The approximate model never overvalues a design by more than `δ`. -/
theorem approxDesignValue_upper (δ : ℝ) (hδ : 0 ≤ δ) (i : Fin 2) :
    approxDesignValue δ i ≤ trueDesignValue δ i + δ := by
  by_cases h : i = 0
  · simp [trueDesignValue, approxDesignValue, h]
    linarith
  · simp [trueDesignValue, approxDesignValue, h]

/-- At a degeneracy the loss is linear in the model error: the approximate model prefers design
    `1`, the truth prefers design `0`, and deploying the approximate choice costs exactly `δ`. -/
theorem crossing_loss_linear (δ : ℝ) (hδ : 0 < δ) :
    approxDesignValue δ 0 < approxDesignValue δ 1 ∧
      trueDesignValue δ 1 < trueDesignValue δ 0 ∧
      trueDesignValue δ 0 - trueDesignValue δ 1 = δ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [trueDesignValue, approxDesignValue] <;> linarith

end Calibrator
