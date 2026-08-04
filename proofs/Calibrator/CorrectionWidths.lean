/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Basic

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
vector. One approximate-kernel witness simultaneously suppresses any fixed finite dictionary;
the whole adaptive span is controlled by its ℓ¹ coefficient budget, yielding residual
`1 - Λε`. This is the finite, theorem-kernel-safe core behind the infinite-dimensional 0--1 law;
the analytic extraction of weakly-null depth cascades is intentionally not smuggled in here.

## Main results

- `uniformCorrectionWidth_order_dichotomy`: exact numerical formula at every uniform order.
- `adaptiveCorrectionSet_smul`: adaptive correction is invariant under nonzero target scaling.
- `not_hasPositiveLowerBound_iff_hasUnitApproxKernel`: exact stability/depth dichotomy.
- `HasUnitApproxKernel.postcomp`: bounded observation processing preserves deep targets.
- `finite_postprocessors_simultaneously_small`: one deep target blinds a finite dictionary.
- `finite_postprocessors_adaptive_span_small`: ℓ¹ control of every adaptive combination.
- `finite_postprocessors_budgeted_adaptive_residual`: the residual lower bound `1 - Λε`.
- `finite_postprocessors_budgeted_adaptive_arbitrarily_close_to_one`: uniform budget barrier.
-/

namespace Calibrator

open scoped BigOperators

section AlgebraicCore

variable {𝕜 H Y : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup Y] [Module 𝕜 Y]

/-- A correction is admissible when it factors through the observation operator. -/
def FactorsThrough (A : H →ₗ[𝕜] Y) (C : H →ₗ[𝕜] H) : Prop :=
  ∃ T : Y →ₗ[𝕜] H, C = T.comp A

/-- The zero correction factors through every observation. -/
theorem FactorsThrough.zero (A : H →ₗ[𝕜] Y) : FactorsThrough A 0 := by
  exact ⟨0, by ext; simp⟩

/-- Factored corrections are closed under addition. -/
theorem FactorsThrough.add (A : H →ₗ[𝕜] Y) (C D : H →ₗ[𝕜] H)
    (hC : FactorsThrough A C) (hD : FactorsThrough A D) :
    FactorsThrough A (C + D) := by
  rcases hC with ⟨T, rfl⟩
  rcases hD with ⟨S, rfl⟩
  exact ⟨T + S, by ext; simp⟩

/-- Factored corrections are closed under scalar multiplication. -/
theorem FactorsThrough.smul (A : H →ₗ[𝕜] Y) (C : H →ₗ[𝕜] H)
    (hC : FactorsThrough A C) (c : 𝕜) :
    FactorsThrough A (c • C) := by
  rcases hC with ⟨T, rfl⟩
  exact ⟨c • T, by ext; simp⟩

/-- Post-composing a factored correction by an arbitrary endomorphism preserves admissibility. -/
theorem FactorsThrough.postcomp (A : H →ₗ[𝕜] Y) (C R : H →ₗ[𝕜] H)
    (hC : FactorsThrough A C) :
    FactorsThrough A (R.comp C) := by
  rcases hC with ⟨T, rfl⟩
  exact ⟨R.comp T, by ext; simp⟩

/-- **Observable-quotient law.**  Every admissible correction is constant on each fiber of the
observation map.  No coefficient choice can distinguish targets that produced the same data. -/
theorem FactorsThrough.apply_eq_of_observation_eq
    (A : H →ₗ[𝕜] Y) (C : H →ₗ[𝕜] H) (hC : FactorsThrough A C)
    (β γ : H) (hobs : A β = A γ) :
    C β = C γ := by
  rcases hC with ⟨T, rfl⟩
  simp only [LinearMap.comp_apply, hobs]

/-- The single post-processor represented by a finite uniform dictionary and fixed coefficients. -/
noncomputable def combinedPostprocessor {k : ℕ}
    (T : Fin k → Y →ₗ[𝕜] H) (a : Fin k → 𝕜) : Y →ₗ[𝕜] H :=
  ∑ j, a j • T j

/-- Corrections represented by a `k`-term uniform dictionary. -/
def UniformCorrectionFamily (A : H →ₗ[𝕜] Y) (k : ℕ) : Set (H →ₗ[𝕜] H) :=
  {C | ∃ (T : Fin k → Y →ₗ[𝕜] H) (a : Fin k → 𝕜),
    C = (combinedPostprocessor T a).comp A}

/-- At order zero the only representable uniform correction is the zero map. -/
theorem uniformCorrectionFamily_zero (A : H →ₗ[𝕜] Y) :
    UniformCorrectionFamily A 0 = {0} := by
  ext C
  constructor
  · rintro ⟨T, a, rfl⟩
    simp [combinedPostprocessor]
  · intro hC
    rw [Set.mem_singleton_iff] at hC
    subst C
    refine ⟨fun j ↦ Fin.elim0 j, fun j ↦ Fin.elim0 j, ?_⟩
    simp [combinedPostprocessor]

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

/-- The exact order dichotomy: order zero contains only zero, while every positive order is the
full factor-through cone. -/
theorem uniformCorrectionFamily_order_dichotomy
    (A : H →ₗ[𝕜] Y) (k : ℕ) :
    UniformCorrectionFamily A k =
      if k = 0 then {0} else {C | FactorsThrough A C} := by
  by_cases hk : k = 0
  · subst k
    simp [uniformCorrectionFamily_zero]
  · simp only [hk, ↓reduceIte]
    exact uniformCorrectionFamily_eq_factorsThrough A k (Nat.pos_of_ne_zero hk)

/-- The set of target vectors achievable by target-dependent coefficients from a fixed
dictionary. -/
def adaptiveCorrectionSet {k : ℕ} (A : H →ₗ[𝕜] Y)
    (T : Fin k → Y →ₗ[𝕜] H) (β : H) : Set H :=
  {z | ∃ a : Fin k → 𝕜, z = ∑ j, a j • T j (A β)}

/-- With no adaptive dictionary entries, the only achievable vector is zero. -/
theorem adaptiveCorrectionSet_zero_order (A : H →ₗ[𝕜] Y) (β : H) :
    adaptiveCorrectionSet A (fun j : Fin 0 ↦ Fin.elim0 j) β = {0} := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨fun j ↦ Fin.elim0 j, by simp⟩

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

/-- Targets lying on a nonzero eigen-direction of one factored correction form the elementary
thin class on which one adaptive coefficient is exact. -/
def NonzeroCorrectionEigencone (A : H →ₗ[𝕜] Y) (T : Y →ₗ[𝕜] H) : Set H :=
  {β | ∃ eigenvalue : 𝕜, eigenvalue ≠ 0 ∧ T (A β) = eigenvalue • β}

/-- **One-direction adaptive exactness.**  A target on a nonzero eigen-direction is recovered
exactly by a one-term adaptive dictionary: the free coefficient supplies the inverse eigenvalue.
This is the abstract one-sparse mechanism behind the maximal uniform/adaptive gap on thin
classes. -/
theorem mem_adaptiveCorrectionSet_singleton_of_mem_nonzeroEigencone
    (A : H →ₗ[𝕜] Y) (T : Y →ₗ[𝕜] H) (β : H)
    (hβ : β ∈ NonzeroCorrectionEigencone A T) :
    β ∈ adaptiveCorrectionSet A (fun _ : Fin 1 ↦ T) β := by
  rcases hβ with ⟨eigenvalue, heigenvalue, heigen⟩
  refine ⟨fun _ ↦ eigenvalue⁻¹, ?_⟩
  simp [heigen, smul_smul, heigenvalue]

/-- The nonzero eigencone is closed under arbitrary target rescaling. -/
theorem NonzeroCorrectionEigencone.smul_mem
    (A : H →ₗ[𝕜] Y) (T : Y →ₗ[𝕜] H) (β : H)
    (hβ : β ∈ NonzeroCorrectionEigencone A T) (c : 𝕜) :
    c • β ∈ NonzeroCorrectionEigencone A T := by
  rcases hβ with ⟨eigenvalue, heigenvalue, heigen⟩
  refine ⟨eigenvalue, heigenvalue, ?_⟩
  simp [heigen, smul_smul, mul_comm]

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

/-- At order zero, the numerical width is exactly the worst residual of the zero correction. -/
theorem uniformCorrectionWidth_zero
    (A : H →ₗ[ℝ] Y) (B : Set H) :
    uniformCorrectionWidth A 0 B = worstCorrectionResidual B 0 := by
  unfold uniformCorrectionWidth
  rw [uniformCorrectionFamily_zero]
  simp

/-- **Complete numerical order dichotomy.** Uniform order zero does nothing; every positive
order optimizes over the same full factor-through cone and therefore equals the correction
diameter. There is no intermediate dependence on dictionary size. -/
theorem uniformCorrectionWidth_order_dichotomy
    (A : H →ₗ[ℝ] Y) (k : ℕ) (B : Set H) :
    uniformCorrectionWidth A k B =
      if k = 0 then worstCorrectionResidual B 0 else correctionDiameter A B := by
  by_cases hk : k = 0
  · subst k
    simp [uniformCorrectionWidth_zero]
  · rw [if_neg hk]
    exact uniformCorrectionWidth_eq_correctionDiameter A k B (Nat.pos_of_ne_zero hk)

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

/-- The observation has a strictly positive global lower stability bound. -/
def HasPositiveLowerBound (A : H →L[ℝ] Y) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ β : H, c * ‖β‖ ≤ ‖A β‖

/-- The observation has unit vectors at arbitrarily small observed depth.  For a bounded linear
operator this is the operational negation of a positive lower stability modulus, stated in the
exact witness form used by correction lower bounds. -/
def HasUnitApproxKernel (A : H →L[ℝ] Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ β : H, ‖β‖ = 1 ∧ ‖A β‖ ≤ ε

/-- **Stability/approximate-kernel dichotomy.**  Failure of every positive lower bound is
equivalent to the existence of unit targets at arbitrarily small observation depth.  This is
proved directly by normalization and does not import a closed-range theorem. -/
theorem not_hasPositiveLowerBound_iff_hasUnitApproxKernel (A : H →L[ℝ] Y) :
    ¬ HasPositiveLowerBound A ↔ HasUnitApproxKernel A := by
  constructor
  · intro hnot ε hε
    have hfailure : ¬ ∀ β : H, ε * ‖β‖ ≤ ‖A β‖ := by
      intro hbound
      exact hnot ⟨ε, hε, hbound⟩
    push_neg at hfailure
    obtain ⟨x, hx⟩ := hfailure
    have hxnorm : 0 < ‖x‖ := by
      by_contra hzero
      have hxzero : ‖x‖ = 0 := le_antisymm (le_of_not_gt hzero) (norm_nonneg x)
      have hx_eq_zero : x = 0 := norm_eq_zero.mp hxzero
      subst x
      simp at hx
    let β : H := (‖x‖)⁻¹ • x
    refine ⟨β, ?_, ?_⟩
    · simp only [β, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr hxnorm)]
      exact inv_mul_cancel₀ (ne_of_gt hxnorm)
    · have hscale : ‖A β‖ = (‖x‖)⁻¹ * ‖A x‖ := by
        simp only [β, map_smul, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (inv_pos.mpr hxnorm)]
      rw [hscale]
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hx) (le_of_lt (inv_pos.mpr hxnorm))
      calc
        (‖x‖)⁻¹ * ‖A x‖ ≤ (‖x‖)⁻¹ * (ε * ‖x‖) := hmul
        _ = ε := by field_simp
  · intro hdeep hstable
    rcases hstable with ⟨c, hc, hbound⟩
    obtain ⟨β, hunit, hdepth⟩ := hdeep (c / 2) (half_pos hc)
    have hlower : c ≤ ‖A β‖ := by simpa [hunit] using hbound β
    linarith

/-- **Approximate-kernel data processing.** Bounded downstream processing cannot repair an
observation operator that has arbitrarily deep unit targets. This covers compression, feature
maps, and bounded re-encodings before any correction dictionary is applied. -/
theorem HasUnitApproxKernel.postcomp
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : H →L[ℝ] Y} (hdeep : HasUnitApproxKernel A) (B : Y →L[ℝ] Z) :
    HasUnitApproxKernel (B.comp A) := by
  intro ε hε
  have hden : 0 < ‖B‖ + 1 := by positivity
  obtain ⟨β, hunit, hdepth⟩ := hdeep (ε / (‖B‖ + 1)) (div_pos hε hden)
  refine ⟨β, hunit, ?_⟩
  have hscaled : ‖B‖ * ‖A β‖ ≤ ‖B‖ * (ε / (‖B‖ + 1)) :=
    mul_le_mul_of_nonneg_left hdepth (norm_nonneg B)
  calc
    ‖(B.comp A) β‖ ≤ ‖B‖ * ‖A β‖ := B.le_opNorm (A β)
    _ ≤ ‖B‖ * (ε / (‖B‖ + 1)) := hscaled
    _ ≤ ε := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hden).2 (by nlinarith [norm_nonneg B])

/-- No bounded downstream observation map can restore a positive lower stability bound after
approximate-kernel depth has appeared. -/
theorem not_hasPositiveLowerBound_postcomp
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : H →L[ℝ] Y} (hdeep : HasUnitApproxKernel A) (B : Y →L[ℝ] Z) :
    ¬ HasPositiveLowerBound (B.comp A) := by
  exact (not_hasPositiveLowerBound_iff_hasUnitApproxKernel (B.comp A)).2 (hdeep.postcomp B)

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

/-- **Simultaneous finite-dictionary blindness.** If `A` has unit approximate-kernel vectors,
then for every fixed finite family of bounded post-processors and every positive tolerance there
is one unit target on which all corrected observations are smaller than that tolerance.

The same witness works for the whole dictionary; choosing a different deep vector for each
operator would not be enough for an adaptive span obstruction. -/
theorem finite_postprocessors_simultaneously_small
    (A : H →L[ℝ] Y) (hdeep : HasUnitApproxKernel A)
    {κ : Type*} [Fintype κ] (T : κ → Y →L[ℝ] H) (ε : ℝ) (hε : 0 < ε) :
    ∃ β : H, ‖β‖ = 1 ∧ ∀ j : κ, ‖(T j) (A β)‖ < ε := by
  classical
  let budget : ℝ := ∑ j, ‖T j‖ + 1
  have hbudget : 0 < budget := by
    dsimp [budget]
    have hsum : 0 ≤ ∑ j, ‖T j‖ := Finset.sum_nonneg fun j _ ↦ norm_nonneg (T j)
    linarith
  obtain ⟨β, hunit, hdepth⟩ := hdeep (ε / budget) (div_pos hε hbudget)
  refine ⟨β, hunit, ?_⟩
  intro j
  have hjSum : ‖T j‖ ≤ ∑ i, ‖T i‖ :=
    Finset.single_le_sum (fun i _ ↦ norm_nonneg (T i)) (Finset.mem_univ j)
  have hjBudget : ‖T j‖ < budget := by
    dsimp [budget]
    linarith
  have hscaledPos : 0 < ε / budget := div_pos hε hbudget
  calc
    ‖(T j) (A β)‖ ≤ ‖T j‖ * ‖A β‖ := (T j).le_opNorm (A β)
    _ ≤ ‖T j‖ * (ε / budget) :=
      mul_le_mul_of_nonneg_left hdepth (norm_nonneg (T j))
    _ < budget * (ε / budget) := mul_lt_mul_of_pos_right hjBudget hscaledPos
    _ = ε := by field_simp

/-- **Adaptive-span budget law.** The simultaneous witness controls the entire moving span:
every coefficient vector produces a corrected observation of norm at most the tolerance times
its ℓ¹ coefficient budget. Free coefficients can amplify a deep signal only by paying this
explicit coefficient cost. -/
theorem finite_postprocessors_adaptive_span_small
    (A : H →L[ℝ] Y) (hdeep : HasUnitApproxKernel A)
    {κ : Type*} [Fintype κ] (T : κ → Y →L[ℝ] H) (ε : ℝ) (hε : 0 < ε) :
    ∃ β : H, ‖β‖ = 1 ∧ ∀ coefficients : κ → ℝ,
      ‖∑ j, coefficients j • (T j) (A β)‖ ≤
        ε * ∑ j, |coefficients j| := by
  classical
  obtain ⟨β, hunit, hsmall⟩ :=
    finite_postprocessors_simultaneously_small A hdeep T ε hε
  refine ⟨β, hunit, ?_⟩
  intro coefficients
  calc
    ‖∑ j, coefficients j • (T j) (A β)‖ ≤
        ∑ j, ‖coefficients j • (T j) (A β)‖ := norm_sum_le _ _
    _ = ∑ j, |coefficients j| * ‖(T j) (A β)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j, |coefficients j| * ε :=
      Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hsmall j).le (abs_nonneg (coefficients j))
    _ = ε * ∑ j, |coefficients j| := by
      rw [← Finset.sum_mul]
      ring

/-- **Budgeted adaptive residual barrier.** For a fixed finite dictionary, every adaptive
combination with ℓ¹ coefficient budget at most `Λ` leaves residual at least `1 - Λε` on one
common unit approximate-kernel target. -/
theorem finite_postprocessors_budgeted_adaptive_residual
    (A : H →L[ℝ] Y) (hdeep : HasUnitApproxKernel A)
    {κ : Type*} [Fintype κ] (T : κ → Y →L[ℝ] H) (ε Λ : ℝ) (hε : 0 < ε) :
    ∃ β : H, ‖β‖ = 1 ∧ ∀ coefficients : κ → ℝ,
      (∑ j, |coefficients j|) ≤ Λ →
        1 - Λ * ε ≤ ‖β - ∑ j, coefficients j • (T j) (A β)‖ := by
  classical
  obtain ⟨β, hunit, hspan⟩ :=
    finite_postprocessors_adaptive_span_small A hdeep T ε hε
  refine ⟨β, hunit, ?_⟩
  intro coefficients hcoefficients
  have hcorrection : ‖∑ j, coefficients j • (T j) (A β)‖ ≤ ε * Λ :=
    (hspan coefficients).trans
      (mul_le_mul_of_nonneg_left hcoefficients hε.le)
  calc
    1 - Λ * ε = 1 - ε * Λ := by ring
    _ ≤ ‖β‖ - ‖∑ j, coefficients j • (T j) (A β)‖ := by
      rw [hunit]
      linarith
    _ ≤ ‖β - ∑ j, coefficients j • (T j) (A β)‖ := norm_sub_norm_le _ _

/-- **Finite-order adaptive obstruction at every fixed budget.** For any finite dictionary and
nonnegative ℓ¹ coefficient budget, one common unit target leaves residual arbitrarily close to
one for every adaptive coefficient choice in that budget. The witness may depend on the budget
and tolerance, but not on the coefficients selected after seeing the target. -/
theorem finite_postprocessors_budgeted_adaptive_arbitrarily_close_to_one
    (A : H →L[ℝ] Y) (hdeep : HasUnitApproxKernel A)
    {κ : Type*} [Fintype κ] (T : κ → Y →L[ℝ] H) (Λ η : ℝ)
    (hΛ : 0 ≤ Λ) (hη : 0 < η) :
    ∃ β : H, ‖β‖ = 1 ∧ ∀ coefficients : κ → ℝ,
      (∑ j, |coefficients j|) ≤ Λ →
        1 - η ≤ ‖β - ∑ j, coefficients j • (T j) (A β)‖ := by
  classical
  have hden : 0 < Λ + 1 := by linarith
  obtain ⟨β, hunit, hresidual⟩ :=
    finite_postprocessors_budgeted_adaptive_residual
      A hdeep T (η / (Λ + 1)) Λ (div_pos hη hden)
  refine ⟨β, hunit, ?_⟩
  intro coefficients hcoefficients
  have hbudgetFraction : Λ * (η / (Λ + 1)) ≤ η := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).2 (by nlinarith)
  exact (by linarith : 1 - η ≤ 1 - Λ * (η / (Λ + 1))).trans
    (hresidual coefficients hcoefficients)

/-- **Approximate-kernel correction barrier.**  Any bounded post-processing correction leaves at
least `‖β‖ - ‖T‖ ‖Aβ‖` residual on target `β`.  This is the quantitative lower bound from which
the uniform modulus and the infinite-dimensional 0--1 obstruction start. -/
theorem correctionResidual_norm_ge
    (A : H →L[ℝ] Y) (T : Y →L[ℝ] H) (β : H) :
    ‖β‖ - ‖T‖ * ‖A β‖ ≤ ‖β - (T.comp A) β‖ := by
  calc
    ‖β‖ - ‖T‖ * ‖A β‖ ≤ ‖β‖ - ‖(T.comp A) β‖ :=
      sub_le_sub_left (factoredCorrection_apply_norm_le A T β) _
    _ ≤ ‖β - (T.comp A) β‖ := norm_sub_norm_le _ _

/-- **Budget--depth exchange.**  A post-processor of norm at most `Λ` cannot remove more than
`Λ * ε` of a target observed at depth at most `ε`.  This is the proved lower half of the
budgeted-width/modulus sandwich. -/
theorem correctionResidual_norm_ge_of_budget_depth
    (A : H →L[ℝ] Y) (T : Y →L[ℝ] H) (β : H) (Λ ε : ℝ)
    (hbudget : ‖T‖ ≤ Λ) (hdepth : ‖A β‖ ≤ ε)
    (hΛ : 0 ≤ Λ) :
    ‖β‖ - Λ * ε ≤ ‖β - (T.comp A) β‖ := by
  have hproduct : ‖T‖ * ‖A β‖ ≤ Λ * ε :=
    mul_le_mul hbudget hdepth (norm_nonneg (A β)) hΛ
  calc
    ‖β‖ - Λ * ε ≤ ‖β‖ - ‖T‖ * ‖A β‖ := sub_le_sub_left hproduct _
    _ ≤ ‖β - (T.comp A) β‖ := correctionResidual_norm_ge A T β

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
