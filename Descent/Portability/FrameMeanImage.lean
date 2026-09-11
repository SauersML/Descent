/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GramAuditGeometry

assert_below Descent.Decision Descent.Program

/-!
The attainable mean image in Decision-Directed Portability, Theorem 12.
The registered outcome mean box has a compact convex image under the actual
frame residual-correlation map. Every point of that image is attained by
explicit bounded endpoint outcome laws. Thus restricting confidence sets
to this image has a concrete probability interpretation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FrameMeanImage

open MeasureTheory Matrix GramAuditGeometry DecisionLossContrasts BoundedAuditCompletion
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The exact residual correlations compatible with the registered row-wise mean bands. -/
noncomputable def meanImage (w f lo hi : ι → ℝ) (φ : ι → κ → ℝ) : Set (κ → ℝ) :=
  estimate w f φ '' Set.Icc lo hi

/-- Residual correlations vary continuously with the finite vector of conditional means. -/
theorem estimate_continuous (w f : ι → ℝ) (φ : ι → κ → ℝ) :
    Continuous (estimate w f φ) := by
  apply continuous_finset_sum
  intro i _
  exact (continuous_const.mul ((continuous_apply i).sub continuous_const)).smul continuous_const

/-- The baseline offset preserves affine combinations of conditional means. -/
theorem estimate_affine (w f m n : ι → ℝ) (φ : ι → κ → ℝ) (a b : ℝ)
    (hab : a + b = 1) :
    estimate w f φ (a • m + b • n) = a • estimate w f φ m + b • estimate w f φ n := by
  unfold estimate
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, ← add_smul]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = w i * (a * m i + b * n i - (a + b) * f i) := by rw [hab]; ring
    _ = _ := by ring

/-- The attainable image is compact, including degenerate mean bands. -/
theorem meanImage_compact (w f lo hi : ι → ℝ) (φ : ι → κ → ℝ) :
    IsCompact (meanImage w f lo hi φ) :=
  isCompact_Icc.image (estimate_continuous w f φ)

/-- The attainable image is convex without any linear phenotype assumption. -/
theorem meanImage_convex (w f lo hi : ι → ℝ) (φ : ι → κ → ℝ) :
    Convex ℝ (meanImage w f lo hi φ) := by
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ a b ha hb hab
  exact ⟨a • m + b • n, (convex_Icc lo hi) hm hn ha hb hab,
    estimate_affine w f m n φ a b hab⟩

/-- Consistent row bands always have at least one attainable residual vector. -/
theorem meanImage_nonempty (w f lo hi : ι → ℝ) (φ : ι → κ → ℝ)
    (hband : lo ≤ hi) : (meanImage w f lo hi φ).Nonempty :=
  ⟨estimate w f φ lo, lo, ⟨le_refl lo, hband⟩, rfl⟩

/-- Every actual outcome law with the specified means produces a point in the image. -/
theorem residual_mem (μ : ι → Measure ℝ) (w f lo hi : ι → ℝ) (φ : ι → κ → ℝ)
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    residual μ w f φ ∈ meanImage w f lo hi φ :=
  ⟨fun i ↦ ∫ y, y ∂μ i, ⟨fun i ↦ (hm i).1, fun i ↦ (hm i).2⟩, rfl⟩

/-- Every image point is attained by actual supported probability laws with finite risks. -/
theorem attained (w f L U lo hi : ι → ℝ) (φ : ι → κ → ℝ)
    (hLU : ∀ i, L i < U i)
    (hband : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i)
    (r : κ → ℝ) (hr : r ∈ meanImage w f lo hi φ) :
    ∃ μ : ι → Measure ℝ, (∀ i, IsProbabilityMeasure (μ i)) ∧
      (∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) ∧
      (∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) ∧
      (∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) ∧ residual μ w f φ = r := by
  obtain ⟨m, hm, rfl⟩ := hr
  let μ (i : ι) := endpointLaw (L i) (U i) (m i)
  have hb (i : ι) : L i ≤ m i ∧ m i ≤ U i :=
    ⟨(hband i).1.trans (hm.1 i), (hm.2 i).trans (hband i).2.2⟩
  have hp (i : ι) : IsProbabilityMeasure (μ i) :=
    endpointLaw_probability _ _ _ (hLU i) (hb i)
  have hs (i : ι) : ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i) :=
    endpointLaw_support _ _ _ (hLU i).le
  have he (i : ι) : (∫ y, y ∂μ i) = m i := endpoint_mean _ _ _ (hLU i) (hb i)
  refine ⟨μ, hp, hs, ?_, ?_, ?_⟩
  · intro i
    rw [he i]
    exact ⟨hm.1 i, hm.2 i⟩
  · intro i
    letI := hp i
    exact memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  · simp only [DecisionLossContrasts.residual, he, estimate]

end Descent.Portability.FrameMeanImage
