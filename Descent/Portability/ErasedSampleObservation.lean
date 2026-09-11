/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RareEventSampleLaw

assert_below Descent.Decision Descent.Program

/-!
The phenotype-only finite-sample estimator is evaluated under its actual erased
observation law. Erasing every mark from the product experiment is proved equal
to the product of the erased marginals; its mean and variance follow through
that exact pushforward identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ErasedSampleObservation

open scoped NNReal
open MeasureTheory ProbabilityTheory RareEventInformationLaw RareEventSampleLaw IIDAverageLaw

/-- The actual independent observation law when every genotype-event mark is hidden. -/
noncomputable def erasedSampleLaw (η : ℝ) (v : ℝ≥0) (θ : ℝ) (M : ℕ) : Measure (Fin M → ℝ) :=
  Measure.pi (fun _ ↦ (experimentLaw η v θ).map Prod.snd)

/-- Erasing all marks commutes exactly with constructing the independent sample law. -/
theorem erased_sample_map (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) (v : ℝ≥0) (θ : ℝ) (M : ℕ) :
    (Measure.pi (fun _ : Fin M ↦ experimentLaw η v θ)).map
      (fun x i ↦ (x i).2) = erasedSampleLaw η v θ M := by
  letI := experimentLaw_probability η hη v θ
  letI := Measure.isProbabilityMeasure_map
    (μ := experimentLaw η v θ) measurable_snd.aemeasurable
  exact Measure.pi_map_pi (fun _ : Fin M ↦ measurable_snd.aemeasurable)

/-- Erasure is a measurable coordinatewise observation channel. -/
theorem erasure_measurable (M : ℕ) :
    Measurable (fun x : Fin M → Bool × ℝ ↦ fun i ↦ (x i).2) :=
  measurable_pi_lambda _ (fun i ↦ measurable_snd.comp (measurable_pi_apply i))

/-- The phenotype-only estimator is measurable without any genotype coordinate. -/
theorem outcome_average_measurable (η : ℝ) (M : ℕ) :
    Measurable (average (fun y : ℝ ↦ y / η) M) := by
  unfold IIDAverageLaw.average
  fun_prop

/-- The estimator under the actual erased law is unbiased for every effect size. -/
theorem erased_observation_unbiased (η : ℝ) (hη : 0 < η ∧ η ≤ 1)
    (v : ℝ≥0) (θ : ℝ) (M : ℕ) (hM : 0 < M) :
    (∫ y, average (fun u : ℝ ↦ u / η) M y ∂erasedSampleLaw η v θ M) = θ := by
  rw [← erased_sample_map η ⟨hη.1.le, hη.2⟩ v θ M,
    integral_map (erasure_measurable M).aemeasurable
      (outcome_average_measurable η M).aestronglyMeasurable]
  exact erased_sample_unbiased η hη v θ M hM

/-- The actual phenotype-only experiment attains the report's finite-sample null variance. -/
theorem erased_observation_variance (η : ℝ) (hη : 0 < η ∧ η ≤ 1)
    (v : ℝ≥0) (M : ℕ) (hM : 0 < M) :
    variance (average (fun u : ℝ ↦ u / η) M) (erasedSampleLaw η v 0 M) =
      (v : ℝ) / ((M : ℝ) * η ^ 2) := by
  rw [← erased_sample_map η ⟨hη.1.le, hη.2⟩ v 0 M,
    variance_map (outcome_average_measurable η M).aemeasurable
      (erasure_measurable M).aemeasurable]
  exact erased_sample_variance η hη v M hM

end Descent.Portability.ErasedSampleObservation
