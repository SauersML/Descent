/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.Prod

assert_below Descent.Decision Descent.Program

namespace Descent.Portability.PartialMetricMixture

open MeasureTheory

/-!
# Partial metrics after a general upstream law and finite conditional outcomes

The upstream sample space can be continuous. Conditional outcome weights are measurable,
nonnegative, and normalized at every sample. A joint probability measure is constructed as
the finite sum of the weighted upstream measures embedded in their respective outcome slices.
The joint integral is then proved equal to integration of the exact finite inner expectation.

For a partial metric, the definedness mass and the unnormalized metric numerator are each
integrated over this joint law. Their ratio is taken once, after both random stages have
been integrated. Per-outcome integrability is explicit: integrability of an aggregate alone
does not silently imply measurability or integrability of its separate summands.

An outcome may encode pipeline failure by a distinguished value whose metric is `none`.
No numeric metric value is assigned to failure, and no inner conditional mean is averaged.
-/

variable {Sample Outcome : Type*} [MeasurableSpace Sample] [Fintype Outcome]

/-- A finite conditional probability law with measurable real-valued weights. -/
structure FiniteOutcomeKernel (Sample Outcome : Type*) [MeasurableSpace Sample]
    [Fintype Outcome] where
  weight : Sample → Outcome → ℝ
  weight_nonneg : ∀ sample outcome, 0 ≤ weight sample outcome
  weight_sum_one : ∀ sample, ∑ outcome, weight sample outcome = 1
  weight_measurable : ∀ outcome, Measurable (fun sample ↦ weight sample outcome)

namespace FiniteOutcomeKernel

/-- An independent finite outcome law is a measurable conditional kernel for every sample
space, providing a reusable concrete constructor with no additional hypotheses. -/
def constant (law : FiniteReportLaw Outcome) : FiniteOutcomeKernel Sample Outcome where
  weight := fun _ ↦ law.mass
  weight_nonneg := fun _ ↦ law.mass_nonneg
  weight_sum_one := fun _ ↦ law.mass_sum
  weight_measurable := fun _ ↦ measurable_const

/-- A deterministic outcome constructs a measurable kernel without any probability premise. -/
noncomputable def deterministic (selected : Outcome) : FiniteOutcomeKernel Sample Outcome :=
  constant (FiniteReportLaw.pointMass selected)

/-- The already formalized finite law at a fixed upstream realization. -/
noncomputable def lawAt (kernel : FiniteOutcomeKernel Sample Outcome) (sample : Sample) :
    FiniteReportLaw Outcome where
  mass := kernel.weight sample
  mass_nonneg := kernel.weight_nonneg sample
  mass_sum := kernel.weight_sum_one sample

variable [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]

/-- One outcome slice carries the upstream measure weighted by its conditional probability. -/
noncomputable def branchMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (outcome : Outcome) : Measure (Sample × Outcome) :=
  (μ.withDensity (fun sample ↦ ENNReal.ofReal (kernel.weight sample outcome))).map
    (fun sample ↦ (sample, outcome))

/-- The actual joint measure of upstream sample and finite conditional outcome. -/
noncomputable def jointMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) : Measure (Sample × Outcome) :=
  ∑ outcome, kernel.branchMeasure μ outcome

theorem branchMeasure_univ (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (outcome : Outcome) :
    kernel.branchMeasure μ outcome Set.univ =
      ∫⁻ sample, ENNReal.ofReal (kernel.weight sample outcome) ∂μ := by
  rw [branchMeasure, Measure.map_apply
    (measurableEmbedding_prod_mk_right outcome).measurable MeasurableSet.univ]
  simp only [Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

/-- Normalization of the constructed joint measure follows from the upstream probability
law and the conditional weight sums, rather than being supplied as an additional field. -/
instance jointMeasure_probability (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (kernel.jointMeasure μ) where
  measure_univ := by
    unfold jointMeasure
    rw [Measure.finset_sum_apply]
    simp_rw [kernel.branchMeasure_univ μ]
    rw [← lintegral_finset_sum Finset.univ
      (fun outcome _ ↦ (kernel.weight_measurable outcome).ennreal_ofReal)]
    have hsum : ∀ sample, (∑ outcome, ENNReal.ofReal (kernel.weight sample outcome)) = 1 := by
      intro sample
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun outcome _ ↦ kernel.weight_nonneg sample outcome), kernel.weight_sum_one sample]
      simp
    simp_rw [hsum]
    simp

/-- Weighted upstream integrability is exactly what is required on each outcome slice. -/
theorem integrable_branchMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → ℝ) (outcome : Outcome)
    (hmetric : Integrable
      (fun sample ↦ kernel.weight sample outcome * metric (sample, outcome)) μ) :
    Integrable metric (kernel.branchMeasure μ outcome) := by
  unfold branchMeasure
  rw [(measurableEmbedding_prod_mk_right outcome).integrable_map_iff]
  apply (integrable_withDensity_iff_integrable_smul'
    (kernel.weight_measurable outcome).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mpr
  simpa only [Function.comp_apply, ENNReal.toReal_ofReal (kernel.weight_nonneg _ _),
    smul_eq_mul] using hmetric

/-- Exact integral on one outcome slice, including its probability weight. -/
theorem integral_branchMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → ℝ) (outcome : Outcome) :
    (∫ pair, metric pair ∂kernel.branchMeasure μ outcome) =
      ∫ sample, kernel.weight sample outcome * metric (sample, outcome) ∂μ := by
  rw [branchMeasure, (measurableEmbedding_prod_mk_right outcome).integral_map]
  rw [integral_withDensity_eq_integral_toReal_smul
    (kernel.weight_measurable outcome).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (kernel.weight_nonneg _ _), smul_eq_mul]

/-- Per-outcome weighted integrability supplies integrability on the constructed joint law. -/
theorem integrable_jointMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → ℝ)
    (hmetric : ∀ outcome, Integrable
      (fun sample ↦ kernel.weight sample outcome * metric (sample, outcome)) μ) :
    Integrable metric (kernel.jointMeasure μ) := by
  unfold jointMeasure
  exact integrable_finset_sum_measure.mpr
    (fun outcome _ ↦ kernel.integrable_branchMeasure μ metric outcome (hmetric outcome))

/-- Exact finite-outcome marginalization over an arbitrary upstream measure. This connects
the constructed joint measure to the existing finite-law expectation evaluator. -/
theorem integral_jointMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → ℝ)
    (hmetric : ∀ outcome, Integrable
      (fun sample ↦ kernel.weight sample outcome * metric (sample, outcome)) μ) :
    (∫ pair, metric pair ∂kernel.jointMeasure μ) =
      ∫ sample, (kernel.lawAt sample).expectation (fun outcome ↦ metric (sample, outcome)) ∂μ := by
  unfold jointMeasure
  rw [integral_finset_sum_measure
    (fun outcome _ ↦ kernel.integrable_branchMeasure μ metric outcome (hmetric outcome))]
  simp_rw [kernel.integral_branchMeasure μ metric]
  rw [← integral_finset_sum Finset.univ (fun outcome _ ↦ hmetric outcome)]
  rfl

/-- For an independent finite outcome draw, exact joint evaluation is the probability-
weighted sum of the upstream slice integrals. This uses the constructed constant kernel
and the joint-measure integration theorem, with integrability checked before summation. -/
theorem integral_constant_kernel (law : FiniteReportLaw Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → ℝ)
    (hmetric : ∀ outcome, Integrable
      (fun sample ↦ law.mass outcome * metric (sample, outcome)) μ) :
    (∫ pair, metric pair ∂(constant law).jointMeasure μ) =
      ∑ outcome, law.mass outcome * (∫ sample, metric (sample, outcome) ∂μ) := by
  rw [(constant law).integral_jointMeasure μ metric hmetric]
  change (∫ sample, ∑ outcome, law.mass outcome * metric (sample, outcome) ∂μ) = _
  rw [integral_finset_sum Finset.univ (fun outcome _ ↦ hmetric outcome)]
  simp only [integral_const_mul]

/-- A deterministic outcome reduces the joint experiment exactly to its selected slice. -/
theorem integral_deterministic_kernel (selected : Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → ℝ)
    (hmetric : Integrable (fun sample ↦ metric (sample, selected)) μ) :
    (∫ pair, metric pair ∂(deterministic selected).jointMeasure μ) =
      ∫ sample, metric (sample, selected) ∂μ := by
  classical
  have hslice : ∀ outcome, Integrable (fun sample ↦
      (FiniteReportLaw.pointMass selected).mass outcome * metric (sample, outcome)) μ := by
    intro outcome
    by_cases h : outcome = selected
    · subst outcome
      simpa [FiniteReportLaw.pointMass] using hmetric
    · simp [FiniteReportLaw.pointMass, h]
  simpa [deterministic, FiniteReportLaw.pointMass] using
    integral_constant_kernel (FiniteReportLaw.pointMass selected) μ metric hslice

end FiniteOutcomeKernel

variable {Space : Type*} [MeasurableSpace Space]

/-- Definedness mass under an actual measure. Integrability of this indicator is explicit
in the mixture theorem, so the integral is not used on a nonmeasurable metric domain. -/
noncomputable def definedMass (μ : Measure Space) (metric : Space → Option ℝ) : ℝ :=
  ∫ sample, (if (metric sample).isSome then 1 else 0) ∂μ

/-- Unnormalized metric numerator under an actual measure. -/
noncomputable def weightedMetric (μ : Measure Space) (metric : Space → Option ℝ) : ℝ :=
  ∫ sample, (metric sample).getD 0 ∂μ

/-- A single normalization after all random stages have been integrated. Nonintegrable
metric data are rejected rather than accepted through the totalized Bochner integral. -/
noncomputable def conditionalMetric (μ : Measure Space) (metric : Space → Option ℝ) : Option ℝ := by
  classical
  exact if Integrable (fun sample ↦ if (metric sample).isSome then (1 : ℝ) else 0) μ ∧
      Integrable (fun sample ↦ (metric sample).getD 0) μ then
    if definedMass μ metric = 0 then none
    else some (weightedMetric μ metric / definedMass μ metric)
  else none

variable [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]

/-- The probability mass of defined outputs is integrated before conditioning. -/
theorem definedMass_jointMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → Option ℝ)
    (hdefined : ∀ outcome, Integrable (fun sample ↦ kernel.weight sample outcome *
      (if (metric (sample, outcome)).isSome then 1 else 0)) μ) :
    definedMass (kernel.jointMeasure μ) metric =
      ∫ sample, (kernel.lawAt sample).definedMass
        (fun outcome ↦ metric (sample, outcome)) ∂μ := by
  exact kernel.integral_jointMeasure μ
    (fun pair ↦ if (metric pair).isSome then 1 else 0) hdefined

/-- The same joint measure independently integrates the unnormalized metric numerator. -/
theorem weightedMetric_jointMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → Option ℝ)
    (hmetric : ∀ outcome, Integrable (fun sample ↦ kernel.weight sample outcome *
      (metric (sample, outcome)).getD 0) μ) :
    weightedMetric (kernel.jointMeasure μ) metric =
      ∫ sample, (kernel.lawAt sample).weightedDefinedMetric
        (fun outcome ↦ metric (sample, outcome)) ∂μ := by
  exact kernel.integral_jointMeasure μ (fun pair ↦ (metric pair).getD 0) hmetric

/-- Exact partial-metric law for a continuous or discrete upstream sample and finite
conditional outcomes. In general this is not the expectation of inner conditional means. -/
theorem conditionalMetric_jointMeasure (kernel : FiniteOutcomeKernel Sample Outcome)
    (μ : Measure Sample) (metric : Sample × Outcome → Option ℝ)
    (hdefined : ∀ outcome, Integrable (fun sample ↦ kernel.weight sample outcome *
      (if (metric (sample, outcome)).isSome then 1 else 0)) μ)
    (hmetric : ∀ outcome, Integrable (fun sample ↦ kernel.weight sample outcome *
      (metric (sample, outcome)).getD 0) μ) :
    conditionalMetric (kernel.jointMeasure μ) metric =
      let mass := ∫ sample, (kernel.lawAt sample).definedMass
        (fun outcome ↦ metric (sample, outcome)) ∂μ
      if mass = 0 then none else some
        ((∫ sample, (kernel.lawAt sample).weightedDefinedMetric
          (fun outcome ↦ metric (sample, outcome)) ∂μ) / mass) := by
  have hdefinedJoint := kernel.integrable_jointMeasure μ
    (fun pair ↦ if (metric pair).isSome then 1 else 0) hdefined
  have hmetricJoint := kernel.integrable_jointMeasure μ (fun pair ↦ (metric pair).getD 0) hmetric
  simp only [conditionalMetric, hdefinedJoint, hmetricJoint, and_self, if_true]
  rw [definedMass_jointMeasure kernel μ metric hdefined,
    weightedMetric_jointMeasure kernel μ metric hmetric]

end Descent.Portability.PartialMetricMixture
