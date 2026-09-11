/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialLabelExperiment

assert_below Descent.Decision Descent.Program

/-!
Fisher information is computed from the differentiated likelihood under the
actual partial-revelation observation law. The formula includes both endpoint
designs and is backed by integrability of the actual observed score.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialLabelFisher

open scoped NNReal
open MeasureTheory ProbabilityTheory RareEventInformationLaw RareEventSampleLaw
open PartialLabelExperiment

/-- At the null the actual erased outcome marginal is exactly the centered Gaussian. -/
theorem null_erased_law (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) (v : ℝ≥0) :
    (experimentLaw η v 0).map Prod.snd = gaussianReal 0 v := by
  rw [experimentLaw, Measure.map_add _ _ measurable_snd,
    Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_snd (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)]
  simp only [Function.comp_def]
  rw [← add_smul, ← ENNReal.ofReal_add (sub_nonneg.mpr hη.2) hη.1]
  simp

/-- Exact integration through the independent label-revelation channel. -/
theorem observation_integral (q η : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (v : ℝ≥0) (θ : ℝ)
    (f : Observation → ℝ) (hf : Measurable f)
    (hl : Integrable (fun zy ↦ f (.inl zy)) (experimentLaw η v θ))
    (he : Integrable (fun y ↦ f (.inr y)) ((experimentLaw η v θ).map Prod.snd)) :
    (∫ o, f o ∂observationLaw q η v θ) =
      q * (∫ zy, f (.inl zy) ∂experimentLaw η v θ) +
        (1 - q) * (∫ y, f (.inr y) ∂(experimentLaw η v θ).map Prod.snd) := by
  have hi : Integrable f ((experimentLaw η v θ).map Sum.inl) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_inl.aemeasurable).mpr hl
  have hj : Integrable f (((experimentLaw η v θ).map Prod.snd).map Sum.inr) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_inr.aemeasurable).mpr he
  rw [observationLaw, integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top)
    (hj.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map measurable_inl.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hq.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hq.2),
    smul_eq_mul]

/-- The squared observed score is integrable on the labeled channel. -/
theorem labeled_score_integrable (q η : ℝ) (v : ℝ≥0) :
    Integrable (fun zy ↦ nullScore q η v (.inl zy) ^ 2) (experimentLaw η v 0) := by
  by_cases hq : q = 0
  · simp [nullScore, hq]
  · simp only [nullScore, hq, if_false]
    apply experiment_integrable η v 0 _ ((markedEstimate_measurable (v : ℝ)).pow_const 2)
    · simp [markedEstimate]
    · simpa [markedEstimate, div_eq_mul_inv, mul_comm] using
        ((memLp_id_gaussianReal (μ := 0) (v := v) 2).const_mul (1 / (v : ℝ))).integrable_sq

/-- The squared observed score is integrable on the erased channel. -/
theorem erased_score_integrable (q η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) (v : ℝ≥0) :
    Integrable (fun y ↦ nullScore q η v (.inr y) ^ 2)
      ((experimentLaw η v 0).map Prod.snd) := by
  rw [null_erased_law η hη v]
  by_cases hq : q = 1
  · simp [nullScore, hq]
  · simpa [nullScore, hq, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      ((memLp_id_gaussianReal (μ := 0) (v := v) 2).const_mul (η / v)).integrable_sq

/-- Exact expected squared score in the actual partial observation experiment. -/
theorem nullScore_second (q η : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (hη : 0 < η ∧ η < 1) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ o, nullScore q η v o ^ 2 ∂observationLaw q η v 0) =
      (q * η + (1 - q) * η ^ 2) / v := by
  have hl : (∫ zy, markedEstimate (v : ℝ) zy ^ 2 ∂experimentLaw η v 0) = η / v := by
    have hh := marked_fisher_integral η hη v hv
    simp_rw [(marked_log_score η hη v hv _ _).deriv] at hh
    exact hh
  have he : (∫ y : ℝ, (η * y / v) ^ 2
      ∂(experimentLaw η v 0).map Prod.snd) = η ^ 2 / v := by
    have hh := erased_fisher_integral η ⟨hη.1.le, hη.2.le⟩ v hv
    simp_rw [(erased_log_score η v hv _).deriv] at hh
    exact hh
  rw [observation_integral q η hq v 0 _ ((nullScore_measurable q η v).pow_const 2)
    (labeled_score_integrable q η v) (erased_score_integrable q η ⟨hη.1.le, hη.2.le⟩ v)]
  by_cases hq0 : q = 0
  · subst q
    simp [nullScore, he]
  by_cases hq1 : q = 1
  · subst q
    simp [nullScore, hl]
  simp only [nullScore, hq0, hq1, if_false, hl, he]
  ring

/-- Fisher information from the actual log likelihood and actual observed probability measure. -/
theorem partial_fisher_information (q η : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (hη : 0 < η ∧ η < 1) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ o, (deriv (fun θ ↦ Real.log (observationDensity q η v θ o)) 0) ^ 2
      ∂observationLaw q η v 0) = (q * η + (1 - q) * η ^ 2) / v := by
  simp_rw [(observation_log_score q η hη v hv _).deriv]
  exact nullScore_second q η hq hη v hv

end Descent.Portability.PartialLabelFisher
