/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SharedAuditCompletion
import Descent.Portability.AuditCenteredObservations

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 20: actual audit laws can omit
labels for rows whose decision contrast is zero. The positive sampling
condition is retained on every nonzero coefficient. For bounded binary
means the midpoint proxy gives an attained variance bound, including these
unsampled irrelevant rows, without invoking an inverse-probability theorem
at a zero sampling probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SparseBinaryAudit

open MeasureTheory ProbabilityTheory SharedAuditCompletion IndependentContrastLaw
open AugmentedAuditLaw BoundedAuditCompletion AuditVarianceGeometry
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Sampling may be zero only at rows irrelevant to the audited contrast. -/
def Admissible (p w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∀ i, w i ≠ 0 → 0 < p i

/-- A sparse audit still estimates its entire target contrast without bias. -/
theorem unbiased (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q w : ι → ℝ) (hp : Admissible p w)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    (∫ z, contrast w z ∂frameLaw μ p q) = ∑ i, w i * ∫ y, y ∂μ i := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) (hp.1 i)
  unfold frameLaw
  rw [contrast_integral _ (fun i ↦ (audit_memLp (μ i) (p i) (q i) (hY i)).integrable
    (by norm_num : (1 : ENNReal) ≤ 2))]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hw : w i = 0
  · simp only [hw, zero_mul]
  · rw [audit_mean (μ i) (p i) (q i) ⟨hp.2 i hw, (hp.1 i).2⟩
      ((hY i).integrable (by norm_num : (1 : ENNReal) ≤ 2))]

/-- Midpoint-proxy variance remains bounded when irrelevant rows have zero inclusion probability. -/
theorem variance_upper (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p w : ι → ℝ) (hp : Admissible p w)
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (0 : ℝ) 1) :
    Var[contrast w; frameLaw μ p (fun _ ↦ 1 / 2)] ≤ ∑ i, w i ^ 2 / (4 * p i) := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (1 / 2) (hp.1 i)
  have hY (i : ι) := memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  unfold frameLaw
  rw [contrast_variance _ (fun i ↦ audit_memLp (μ i) (p i) (1 / 2) (hY i))]
  apply Finset.sum_le_sum
  intro i _
  by_cases hw : w i = 0
  · simp only [hw, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div, le_refl]
  · have hm := AuditCenteredObservations.mean_interval (μ i) 0 1 (hs i)
    have hh := minimax_upper (μ i) 0 1 (p i) 0 1 ⟨hp.2 i hw, (hp.1 i).2⟩ (hs i) hm
    have hproxy : proxy 0 1 0 1 = (1 : ℝ) / 2 := by norm_num [proxy, clip]
    rw [hproxy] at hh
    have he : (1 - (1 : ℝ) / 2) * (1 / 2 - 0) / p i = 1 / (4 * p i) := by ring
    rw [he] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (w i))
    convert hmul using 1 <;> ring

/-- The independent fair binary outcome law attains the full sparse-audit variance envelope. -/
theorem variance_attained (p w : ι → ℝ) (hp : Admissible p w) :
    Var[contrast w; frameLaw (fun _ ↦ endpointLaw 0 1 (1 / 2)) p (fun _ ↦ 1 / 2)] =
      ∑ i, w i ^ 2 / (4 * p i) := by
  let μ : ι → Measure ℝ := fun _ ↦ endpointLaw 0 1 (1 / 2)
  letI : IsProbabilityMeasure (endpointLaw 0 1 (1 / 2)) :=
    endpointLaw_probability _ _ _ (by norm_num) (by norm_num)
  letI (i : ι) := auditLaw_probability (μ i) (p i) (1 / 2) (hp.1 i)
  have hY (i : ι) : MemLp (fun y : ℝ ↦ y) 2 (μ i) := memLp_of_bounded
    (endpointLaw_support 0 1 (1 / 2) (by norm_num)) measurable_id.aestronglyMeasurable 2
  change Var[contrast w; frameLaw μ p (fun _ ↦ 1 / 2)] = _
  unfold frameLaw
  rw [contrast_variance _ (fun i ↦ audit_memLp (μ i) (p i) (1 / 2) (hY i))]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hw : w i = 0
  · simp only [hw, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div]
  · have hh := endpoint_audit_variance 0 1 (p i) (1 / 2) (1 / 2) (by norm_num)
      ⟨hp.2 i hw, (hp.1 i).2⟩ (by norm_num)
    change Var[fun y : ℝ ↦ y; auditLaw (μ i) (p i) (1 / 2)] = _ at hh
    rw [hh]
    unfold envelope
    ring

end Descent.Portability.SparseBinaryAudit
