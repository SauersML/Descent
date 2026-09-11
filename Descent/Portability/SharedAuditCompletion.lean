/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BoundedAuditCompletion
import Descent.Portability.IndependentContrastLaw

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 4 and Corollary 7. One independent audit
has unbiased linear contrasts and an exactly computed full covariance. The
bounded-outcome envelope holds in every quadratic direction. A single family
of independent endpoint outcome laws attains all covariance entries at once.
Contrast coefficients include any frame normalization and tolerance scaling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SharedAuditCompletion

open MeasureTheory ProbabilityTheory AugmentedAuditLaw AuditVarianceGeometry
open BoundedAuditCompletion IndependentContrastLaw
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The actual independent joint law of all augmented audit observations. -/
noncomputable def frameLaw (μ : ι → Measure ℝ) (p q : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i ↦ auditLaw (μ i) (p i) (q i))

/-- The complete audit experiment is a probability measure. -/
theorem frameLaw_probability (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    IsProbabilityMeasure (frameLaw μ p q) := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) (hp i)
  unfold frameLaw
  infer_instance

/-- Every contrast is unbiased under the full audit, even with heterogeneous wrong proxies. -/
theorem frame_contrast_mean (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q w : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    (∫ x, contrast w x ∂frameLaw μ p q) = ∑ i, w i * ∫ y, y ∂μ i := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  unfold frameLaw
  rw [contrast_integral _ (fun i ↦ (audit_memLp (μ i) (p i) (q i) (hY i)).integrable
    (by norm_num : (1 : ENNReal) ≤ 2))]
  apply Finset.sum_congr rfl
  intro i _
  rw [audit_mean (μ i) (p i) (q i) (hp i)
    ((hY i).integrable (by norm_num : (1 : ENNReal) ≤ 2))]

/-- The actual covariance matrix is obtained by summing marginal audit variances. -/
theorem frame_covariance (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q w v : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    cov[contrast w, contrast v; frameLaw μ p q] =
      ∑ i, w i * v i * (Var[fun y : ℝ ↦ y; μ i] / p i +
        (1 / p i - 1) * ((∫ y, y ∂μ i) - q i) ^ 2) := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  unfold frameLaw
  rw [contrast_covariance _ (fun i ↦ audit_memLp (μ i) (p i) (q i) (hY i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [audit_variance (μ i) (p i) (q i) (hp i) (hY i)]

/-- The sharp covariance upper bound holds in every direction, not entrywise. -/
theorem frame_variance_upper (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi w : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    Var[contrast w; frameLaw μ p q] ≤
      ∑ i, w i ^ 2 * envelope (L i) (U i) (p i) (q i)
        (clip (lo i) (hi i) (vertex (L i) (U i) (p i) (q i))) := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  have hY (i : ι) := memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  unfold frameLaw
  rw [contrast_variance _ (fun i ↦ audit_memLp (μ i) (p i) (q i) (hY i))]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (worst_case_upper (μ i) (L i) (U i) (p i) (q i) (lo i) (hi i) (hp i) (hs i) (hm i))
    (sq_nonneg _)

/-- One endpoint law for every unit attains the entire covariance envelope simultaneously. -/
theorem simultaneous_attainment (L U p q lo hi : ι → ℝ)
    (hLU : ∀ i, L i < U i) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hband : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i) :
    ∃ μ : ι → Measure ℝ,
      (∀ i, IsProbabilityMeasure (μ i)) ∧
      (∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i)) ∧
      (∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) ∧
      IsProbabilityMeasure (frameLaw μ p q) ∧
      ∀ w v, cov[contrast w, contrast v; frameLaw μ p q] =
        ∑ i, w i * v i * envelope (L i) (U i) (p i) (q i)
          (clip (lo i) (hi i) (vertex (L i) (U i) (p i) (q i))) := by
  let m (i : ι) := clip (lo i) (hi i) (vertex (L i) (U i) (p i) (q i))
  let μ (i : ι) := endpointLaw (L i) (U i) (m i)
  have hm (i : ι) : lo i ≤ m i ∧ m i ≤ hi i :=
    clip_mem _ _ _ (hband i).2.1
  have hs (i : ι) : L i ≤ m i ∧ m i ≤ U i :=
    ⟨(hband i).1.trans (hm i).1, (hm i).2.trans (hband i).2.2⟩
  letI (i : ι) : IsProbabilityMeasure (μ i) := endpointLaw_probability _ _ _ (hLU i) (hs i)
  have hb (i : ι) : ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i) :=
    endpointLaw_support _ _ _ (hLU i).le
  refine ⟨μ, fun i ↦ inferInstance, hb, ?_,
    frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩), ?_⟩
  · intro i
    change lo i ≤ (∫ y, y ∂endpointLaw (L i) (U i) (m i)) ∧ _
    rw [endpoint_mean _ _ _ (hLU i) (hs i)]
    exact hm i
  · intro w v
    letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
    unfold frameLaw
    rw [contrast_covariance _ (fun i ↦ audit_memLp (μ i) (p i) (q i)
      (memLp_of_bounded (hb i) measurable_id.aestronglyMeasurable 2))]
    apply Finset.sum_congr rfl
    intro i _
    rw [endpoint_audit_variance (L i) (U i) (p i) (q i) (m i) (hLU i) (hp i) (hs i)]

/-- The minimax proxy gives the simple variance envelope used by the allocation program. -/
theorem minimax_frame_upper (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p lo hi w : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    Var[contrast w; frameLaw μ p (fun i ↦ proxy (L i) (U i) (lo i) (hi i))] ≤
      ∑ i, w i ^ 2 * ((U i - proxy (L i) (U i) (lo i) (hi i)) *
        (proxy (L i) (U i) (lo i) (hi i) - L i) / p i) := by
  let q (i : ι) := proxy (L i) (U i) (lo i) (hi i)
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  have hY (i : ι) := memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  change Var[contrast w; frameLaw μ p q] ≤ _
  unfold frameLaw
  rw [contrast_variance _ (fun i ↦ audit_memLp (μ i) (p i) (q i) (hY i))]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (minimax_upper (μ i) (L i) (U i) (p i) (lo i) (hi i) (hp i) (hs i) (hm i))
    (sq_nonneg _)

end Descent.Portability.SharedAuditCompletion
