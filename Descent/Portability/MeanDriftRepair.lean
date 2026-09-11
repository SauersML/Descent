/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DecisionLossContrasts
import Descent.Portability.BoundedAuditCompletion
import Mathlib.Data.Real.Sign

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 23. Changes in actual outcome laws
affect the expected paired squared-loss gain only through their means. The
absolute mean-drift penalty is sharp: explicit bounded endpoint laws attain
it whenever the adverse mean choices are feasible. Both separate risks have
finite second moments throughout these statements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MeanDriftRepair

open MeasureTheory DecisionLossContrasts AugmentedAuditLaw BoundedAuditCompletion
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The actual expected frame gain of a fixed correction vector. -/
noncomputable def gain (μ : ι → Measure ℝ) (w f d : ι → ℝ) : ℝ :=
  frameRisk μ w f - frameRisk μ w (fun i ↦ f i + d i)

/-- The paired gain is derived from the separate finite expected losses. -/
theorem gain_identity (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f d : ι → ℝ) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    gain μ w f d = ∑ i, w i * (2 * d i * ((∫ y, y ∂μ i) - f i) - d i ^ 2) := by
  unfold gain frameRisk
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub, expected_gain (μ i) (f i) (d i) (hY i)]

/-- Exact sensitivity of expected gain to the conditional means of the future outcome laws. -/
theorem gain_change (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (w f d : ι → ℝ) (hμ : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hν : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (ν i)) :
    gain ν w f d - gain μ w f d =
      2 * ∑ i, w i * d i * ((∫ y, y ∂ν i) - ∫ y, y ∂μ i) := by
  rw [gain_identity ν w f d hν, gain_identity μ w f d hμ,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Arbitrary conditional-variance or tail-shape drift preserves gain when means are unchanged. -/
theorem same_mean_gain (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (w f d : ι → ℝ) (hμ : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hν : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (ν i))
    (hm : ∀ i, (∫ y, y ∂ν i) = ∫ y, y ∂μ i) :
    gain ν w f d = gain μ w f d := by
  have hh := gain_change μ ν w f d hμ hν
  simp only [hm, sub_self, mul_zero, Finset.sum_const_zero] at hh
  exact sub_eq_zero.mp hh

/-- A scalar linear contrast loses at most its absolute coefficient times the mean radius. -/
theorem drift_product_lower (d δ t : ℝ) (hδ : |δ| ≤ t) : -(|d| * t) ≤ d * δ := by
  have ha : |d * δ| ≤ |d| * t := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hδ (abs_nonneg d)
  exact (neg_le_neg ha).trans (neg_abs_le _)

/-- The deterministic drift penalty bounds actual future frame gain. -/
theorem drift_lower (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (w f d t : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (hν : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (ν i))
    (ht : ∀ i, |(∫ y, y ∂ν i) - ∫ y, y ∂μ i| ≤ t i) :
    gain μ w f d - 2 * ∑ i, w i * |d i| * t i ≤ gain ν w f d := by
  have hs : -(∑ i, w i * |d i| * t i) ≤
      ∑ i, w i * d i * ((∫ y, y ∂ν i) - ∫ y, y ∂μ i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      (drift_product_lower (d i) _ (t i) (ht i)) (hw i)
    nlinarith
  have hg := gain_change μ ν w f d hμ hν
  linarith

/-- The sign choice attaining the scalar adverse drift penalty. -/
theorem adverse_product (d t : ℝ) : d * (-t * Real.sign d) = -(|d| * t) := by
  rcases lt_trichotomy d 0 with hn | hz | hp
  · rw [Real.sign_of_neg hn, abs_of_neg hn]
    ring
  · subst d
    simp
  · rw [Real.sign_of_pos hp, abs_of_pos hp]
    ring

/-- The adverse sign choice respects its mean-drift radius, including zero corrections. -/
theorem adverse_size (d t : ℝ) (ht : 0 ≤ t) : |-t * Real.sign d| ≤ t := by
  rcases Real.sign_apply_eq d with hs | hs | hs <;> rw [hs] <;> simp [abs_of_nonneg ht, ht]

/-- Actual bounded outcome laws attain the sharp mean-drift penalty whenever means are feasible. -/
theorem attained_drift_penalty (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f d t L U : ι → ℝ) (hμ : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (ht : ∀ i, 0 ≤ t i) (hLU : ∀ i, L i < U i)
    (hmean : ∀ i, L i ≤ (∫ y, y ∂μ i) - t i * Real.sign (d i) ∧
      (∫ y, y ∂μ i) - t i * Real.sign (d i) ≤ U i) :
    ∃ ν : ι → Measure ℝ,
      (∀ i, IsProbabilityMeasure (ν i)) ∧
      (∀ i, ∀ᵐ y ∂ν i, y ∈ Set.Icc (L i) (U i)) ∧
      (∀ i, MemLp (fun y : ℝ ↦ y) 2 (ν i)) ∧
      (∀ i, |(∫ y, y ∂ν i) - ∫ y, y ∂μ i| ≤ t i) ∧
      gain ν w f d = gain μ w f d - 2 * ∑ i, w i * |d i| * t i := by
  let m (i : ι) := (∫ y, y ∂μ i) - t i * Real.sign (d i)
  let ν (i : ι) := endpointLaw (L i) (U i) (m i)
  letI (i : ι) : IsProbabilityMeasure (ν i) :=
    endpointLaw_probability _ _ _ (hLU i) (hmean i)
  have hs (i : ι) : ∀ᵐ y ∂ν i, y ∈ Set.Icc (L i) (U i) :=
    endpointLaw_support _ _ _ (hLU i).le
  have hν (i : ι) : MemLp (fun y : ℝ ↦ y) 2 (ν i) :=
    memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  have hm (i : ι) : (∫ y, y ∂ν i) - (∫ y, y ∂μ i) = -t i * Real.sign (d i) := by
    change (∫ y, y ∂endpointLaw (L i) (U i) (m i)) - (∫ y, y ∂μ i) = _
    rw [endpoint_mean _ _ _ (hLU i) (hmean i)]
    ring
  refine ⟨ν, fun i ↦ inferInstance, hs, hν, ?_, ?_⟩
  · intro i
    rw [hm i]
    exact adverse_size (d i) (t i) (ht i)
  · have hg := gain_change μ ν w f d hμ hν
    have he : (∑ i, w i * d i * ((∫ y, y ∂ν i) - ∫ y, y ∂μ i)) =
        -(∑ i, w i * |d i| * t i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hm i, mul_assoc, adverse_product]
      ring
    rw [he] at hg
    linarith

end Descent.Portability.MeanDriftRepair
