/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Basic

namespace Calibrator

/-!
# Correction widths: the exact algebraic core

This module formalizes the parts of the correction-width synthesis that do not require importing
an external regularization, Douglas-factorization, Lin-stability, or Gaussian-process theorem as
an assumption.

The central repair is algebraic.  Once the coefficients of a uniform correction are fixed, a
finite dictionary of post-processors is a single post-processor.  Conversely, a nonempty
dictionary can contain any single post-processor.  Thus unbudgeted uniform order collapses exactly
to the cone of maps factoring through the observation operator.  Adaptive coefficients do not
collapse, but their achievable set is invariant under nonzero rescaling of the target, so the
correct quantity is angular.

The normed section proves the elementary half of the Douglas principle directly and turns it into
a quantitative obstruction: every bounded correction is nearly blind on every approximate-kernel
vector.  This is the finite, theorem-kernel-safe core behind the infinite-dimensional 0--1 law;
the analytic extraction of weakly-null depth cascades is intentionally not smuggled in here.
-/

open scoped BigOperators

section AlgebraicCore

variable {𝕜 H Y : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup Y] [Module 𝕜 Y]

/-- A correction is admissible when it factors through the observation operator. -/
def FactorsThrough (A : H →ₗ[𝕜] Y) (C : H →ₗ[𝕜] H) : Prop :=
  ∃ T : Y →ₗ[𝕜] H, C = T.comp A

/-- The single post-processor represented by a finite uniform dictionary and fixed coefficients. -/
noncomputable def combinedPostprocessor {k : ℕ}
    (T : Fin k → Y →ₗ[𝕜] H) (a : Fin k → 𝕜) : Y →ₗ[𝕜] H :=
  ∑ j, a j • T j

/-- Corrections represented by a `k`-term uniform dictionary. -/
def UniformCorrectionFamily (A : H →ₗ[𝕜] Y) (k : ℕ) : Set (H →ₗ[𝕜] H) :=
  {C | ∃ (T : Fin k → Y →ₗ[𝕜] H) (a : Fin k → 𝕜),
    C = (combinedPostprocessor T a).comp A}

/-- Every finite uniform dictionary produces one correction factoring through `A`. -/
theorem uniformCorrectionFamily_subset_factorsThrough
    (A : H →ₗ[𝕜] Y) (k : ℕ) :
    UniformCorrectionFamily A k ⊆ {C | FactorsThrough A C} := by
  intro C hC
  rcases hC with ⟨T, a, rfl⟩
  exact ⟨combinedPostprocessor T a, rfl⟩

/-- Every single factored correction is represented by any nonempty uniform dictionary. -/
theorem factorsThrough_subset_uniformCorrectionFamily
    (A : H →ₗ[𝕜] Y) (k : ℕ) (hk : 0 < k) :
    {C | FactorsThrough A C} ⊆ UniformCorrectionFamily A k := by
  classical
  intro C hC
  rcases hC with ⟨S, rfl⟩
  let j₀ : Fin k := ⟨0, hk⟩
  refine ⟨fun j ↦ if j = j₀ then S else 0,
    fun j ↦ if j = j₀ then 1 else 0, ?_⟩
  unfold combinedPostprocessor
  simp [j₀]

/-- **Uniform-collapse theorem.**  Every positive uniform order represents exactly the same cone:
all corrections factoring through the observation operator. -/
theorem uniformCorrectionFamily_eq_factorsThrough
    (A : H →ₗ[𝕜] Y) (k : ℕ) (hk : 0 < k) :
    UniformCorrectionFamily A k = {C | FactorsThrough A C} := by
  apply Set.Subset.antisymm
  · exact uniformCorrectionFamily_subset_factorsThrough A k
  · exact factorsThrough_subset_uniformCorrectionFamily A k hk

/-- The set of target vectors achievable by target-dependent coefficients from a fixed
dictionary. -/
def adaptiveCorrectionSet {k : ℕ} (A : H →ₗ[𝕜] Y)
    (T : Fin k → Y →ₗ[𝕜] H) (β : H) : Set H :=
  {z | ∃ a : Fin k → 𝕜, z = ∑ j, a j • T j (A β)}

/-- **Adaptive scale invariance.**  Rescaling a nonzero target does not change its achievable
adaptive correction set; coefficients absorb the scale.  Consequently adaptive error on a ball
is fundamentally angular rather than radial. -/
theorem adaptiveCorrectionSet_smul {k : ℕ} (A : H →ₗ[𝕜] Y)
    (T : Fin k → Y →ₗ[𝕜] H) (β : H) (c : 𝕜) (hc : c ≠ 0) :
    adaptiveCorrectionSet A T (c • β) = adaptiveCorrectionSet A T β := by
  classical
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun j ↦ a j * c, ?_⟩
    apply Finset.sum_congr rfl
    intro j _
    simp [smul_smul]
  · rintro ⟨a, rfl⟩
    refine ⟨fun j ↦ a j / c, ?_⟩
    apply Finset.sum_congr rfl
    intro j _
    simp [smul_smul, hc]

/-- A true kernel direction is invisible to every adaptive dictionary. -/
theorem adaptiveCorrectionSet_of_mem_ker {k : ℕ} (A : H →ₗ[𝕜] Y)
    (T : Fin k → Y →ₗ[𝕜] H) (β : H) (hβ : β ∈ LinearMap.ker A) :
    adaptiveCorrectionSet A T β = {0} := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    simp [LinearMap.mem_ker.mp hβ]
  · intro hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨0, by simp⟩

/-- Factored corrections annihilate every true kernel direction. -/
theorem factorsThrough_apply_eq_zero_of_mem_ker
    (A : H →ₗ[𝕜] Y) (C : H →ₗ[𝕜] H) (hC : FactorsThrough A C)
    (β : H) (hβ : β ∈ LinearMap.ker A) : C β = 0 := by
  rcases hC with ⟨T, rfl⟩
  simp [LinearMap.mem_ker.mp hβ]

end AlgebraicCore

section UniformWidths

variable {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [AddCommGroup Y] [Module ℝ Y]

/-- Worst residual of one algebraic correction on a target class.  The surrounding theory uses
bounded classes, for which this supremum has its ordinary extended-real meaning. -/
noncomputable def worstCorrectionResidual
    (B : Set H) (C : H →ₗ[ℝ] H) : ℝ :=
  sSup {r : ℝ | ∃ β ∈ B, r = ‖β - C β‖}

/-- Unbudgeted uniform width of a finite correction dictionary. -/
noncomputable def uniformCorrectionWidth
    (A : H →ₗ[ℝ] Y) (k : ℕ) (B : Set H) : ℝ :=
  sInf (worstCorrectionResidual B '' UniformCorrectionFamily A k)

/-- The correction diameter: optimize over every single correction factoring through `A`. -/
noncomputable def correctionDiameter
    (A : H →ₗ[ℝ] Y) (B : Set H) : ℝ :=
  sInf (worstCorrectionResidual B '' {C | FactorsThrough A C})

/-- **Numerical uniform-collapse theorem.**  On every target class, all positive dictionary orders
have exactly the correction diameter.  This is an equality of the optimization domains, so it does
not require compactness, attainment, or a theorem about `sInf`. -/
theorem uniformCorrectionWidth_eq_correctionDiameter
    (A : H →ₗ[ℝ] Y) (k : ℕ) (B : Set H) (hk : 0 < k) :
    uniformCorrectionWidth A k B = correctionDiameter A B := by
  unfold uniformCorrectionWidth correctionDiameter
  rw [uniformCorrectionFamily_eq_factorsThrough A k hk]

end UniformWidths

section Conjugation

variable {𝕜 H H' : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup H'] [Module 𝕜 H']

/-- Conjugate an operator by a change of coordinates.  Whitening is the positive-isometric
instance of this construction. -/
def conjugateLinearOperator (U : H ≃ₗ[𝕜] H') (A : H →ₗ[𝕜] H) : H' →ₗ[𝕜] H' :=
  U.toLinearMap.comp (A.comp U.symm.toLinearMap)

/-- Conjugation preserves composition. -/
theorem conjugateLinearOperator_comp (U : H ≃ₗ[𝕜] H')
    (T A : H →ₗ[𝕜] H) :
    conjugateLinearOperator U (T.comp A) =
      (conjugateLinearOperator U T).comp (conjugateLinearOperator U A) := by
  ext x
  simp [conjugateLinearOperator]

/-- Conjugation preserves and reflects the factor-through relation. -/
theorem factorsThrough_conjugate_iff (U : H ≃ₗ[𝕜] H')
    (A C : H →ₗ[𝕜] H) :
    FactorsThrough (conjugateLinearOperator U A) (conjugateLinearOperator U C) ↔
      FactorsThrough A C := by
  constructor
  · rintro ⟨T', hT'⟩
    refine ⟨conjugateLinearOperator U.symm T', ?_⟩
    ext x
    apply LinearEquiv.injective U
    have hx := LinearMap.congr_fun hT' (U x)
    simpa [conjugateLinearOperator] using hx
  · rintro ⟨T, rfl⟩
    exact ⟨conjugateLinearOperator U T, conjugateLinearOperator_comp U T A⟩

end Conjugation

section NormedObstruction

variable {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The observation has unit vectors at arbitrarily small observed depth.  For a bounded linear
operator this is the operational negation of a positive lower stability modulus, stated in the
exact witness form used by correction lower bounds. -/
def HasUnitApproxKernel (A : H →L[ℝ] Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ β : H, ‖β‖ = 1 ∧ ‖A β‖ ≤ ε

/-- The zero observation on the real line is the simplest concrete approximate-kernel model. -/
theorem hasUnitApproxKernel_zero_real :
    HasUnitApproxKernel (0 : ℝ →L[ℝ] ℝ) := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  simpa using le_of_lt hε

/-- The elementary, fully proved direction of Douglas admissibility: a post-processor times the
observation is bounded by the post-processor norm times the observation norm. -/
theorem factoredCorrection_apply_norm_le
    (A : H →L[ℝ] Y) (T : Y →L[ℝ] H) (β : H) :
    ‖(T.comp A) β‖ ≤ ‖T‖ * ‖A β‖ := by
  exact T.le_opNorm (A β)

/-- **Approximate-kernel correction barrier.**  Any bounded post-processing correction leaves at
least `‖β‖ - ‖T‖ ‖Aβ‖` residual on target `β`.  This is the quantitative lower bound from which the
uniform modulus and the infinite-dimensional 0--1 obstruction start. -/
theorem correctionResidual_norm_ge
    (A : H →L[ℝ] Y) (T : Y →L[ℝ] H) (β : H) :
    ‖β‖ - ‖T‖ * ‖A β‖ ≤ ‖β - (T.comp A) β‖ := by
  calc
    ‖β‖ - ‖T‖ * ‖A β‖ ≤ ‖β‖ - ‖(T.comp A) β‖ :=
      sub_le_sub_left (factoredCorrection_apply_norm_le A T β) _
    _ ≤ ‖β - (T.comp A) β‖ := norm_sub_norm_le _ _

/-- Unit approximate-kernel vectors force residual arbitrarily close to one at the explicit rate
`1 - ‖T‖ ε`. -/
theorem correctionResidual_norm_ge_of_unit_approxKernel
    (A : H →L[ℝ] Y) (T : Y →L[ℝ] H) (β : H) (ε : ℝ)
    (hunit : ‖β‖ = 1) (hdepth : ‖A β‖ ≤ ε) :
    1 - ‖T‖ * ε ≤ ‖β - (T.comp A) β‖ := by
  calc
    1 - ‖T‖ * ε ≤ ‖β‖ - ‖T‖ * ‖A β‖ := by
      rw [hunit]
      gcongr
    _ ≤ ‖β - (T.comp A) β‖ := correctionResidual_norm_ge A T β

/-- **Uniform one-bit obstruction, witness form.**  If the observation has arbitrarily deep unit
vectors, every fixed bounded post-processor has unit residual in the supremal limit: for every
positive tolerance there is a unit target whose residual is at least `1 - η`.  No compactness,
spectral theorem, or external regularization result is used. -/
theorem correctionResidual_arbitrarily_close_to_one
    (A : H →L[ℝ] Y) (hdeep : HasUnitApproxKernel A)
    (T : Y →L[ℝ] H) (η : ℝ) (hη : 0 < η) :
    ∃ β : H, ‖β‖ = 1 ∧ 1 - η ≤ ‖β - (T.comp A) β‖ := by
  have hden : 0 < ‖T‖ + 1 := by positivity
  obtain ⟨β, hunit, hdepth⟩ := hdeep (η / (‖T‖ + 1)) (div_pos hη hden)
  refine ⟨β, hunit, ?_⟩
  have hmul_depth : ‖T‖ * ‖A β‖ ≤ ‖T‖ * (η / (‖T‖ + 1)) :=
    mul_le_mul_of_nonneg_left hdepth (norm_nonneg T)
  have hratio : ‖T‖ * (η / (‖T‖ + 1)) ≤ η := by
    calc
      ‖T‖ * (η / (‖T‖ + 1)) = (‖T‖ * η) / (‖T‖ + 1) := by ring
      _ ≤ η := (div_le_iff₀ hden).2 (by nlinarith [norm_nonneg T])
  have hmul : ‖T‖ * ‖A β‖ ≤ η := hmul_depth.trans hratio
  calc
    1 - η ≤ ‖β‖ - ‖T‖ * ‖A β‖ := by rw [hunit]; linarith
    _ ≤ ‖β - (T.comp A) β‖ := correctionResidual_norm_ge A T β

/-- A genuine kernel vector is left completely unchanged by every bounded post-processing
correction. -/
theorem correctionResidual_eq_of_mem_ker
    (A : H →L[ℝ] Y) (T : Y →L[ℝ] H) (β : H) (hβ : A β = 0) :
    β - (T.comp A) β = β := by
  simp [hβ]

end NormedObstruction

end Calibrator
