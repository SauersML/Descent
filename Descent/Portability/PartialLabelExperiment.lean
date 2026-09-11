/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RareEventSampleLaw

assert_below Descent.Decision Descent.Program

/-!
An explicit observation channel that independently reveals a genotype-event mark
with probability q. A labeled observation contains both mark and phenotype;
an unlabeled observation contains only phenotype. The likelihood score is
derived for the actual observation type, including the endpoint designs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialLabelExperiment

open scoped NNReal
open MeasureTheory ProbabilityTheory RareEventInformationLaw RareEventSampleLaw

/-- Labeled data retain the event; unlabeled data have no event coordinate. -/
abbrev Observation := Sum (Bool × ℝ) ℝ

/-- Actual independently randomized revelation law on the observed data. -/
noncomputable def observationLaw (q η : ℝ) (v : ℝ≥0) (θ : ℝ) : Measure Observation :=
  ENNReal.ofReal q • (experimentLaw η v θ).map Sum.inl +
    ENNReal.ofReal (1 - q) • ((experimentLaw η v θ).map Prod.snd).map Sum.inr

/-- Density of the observed data with respect to the disjoint counting-Lebesgue reference. -/
noncomputable def observationDensity (q η : ℝ) (v : ℝ≥0) (θ : ℝ) : Observation → ℝ
  | .inl zy => q * markedDensity η v θ zy.1 zy.2
  | .inr y => (1 - q) * erasedDensity η v θ y

/-- Null likelihood score, with zero scores on categories absent from endpoint designs. -/
noncomputable def nullScore (q η : ℝ) (v : ℝ≥0) : Observation → ℝ
  | .inl zy => if q = 0 then 0 else markedEstimate (v : ℝ) zy
  | .inr y => if q = 1 then 0 else η * y / v

/-- Independent revelation defines a probability measure for every valid design fraction. -/
theorem observationLaw_probability (q η : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (hη : 0 ≤ η ∧ η ≤ 1) (v : ℝ≥0) (θ : ℝ) :
    IsProbabilityMeasure (observationLaw q η v θ) := by
  letI := experimentLaw_probability η hη v θ
  constructor
  simp only [observationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_inl : Measurable (Sum.inl : Bool × ℝ → Observation))
      MeasurableSet.univ,
    Measure.map_apply (measurable_inr : Measurable (Sum.inr : ℝ → Observation))
      MeasurableSet.univ,
    Measure.map_apply measurable_snd MeasurableSet.univ,
    Set.preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add hq.1 (sub_nonneg.mpr hq.2)]
  norm_num

/-- Multiplying a nonzero likelihood by a parameter-independent weight preserves its log score. -/
theorem scaled_log_score (f : ℝ → ℝ) (hf : ∀ θ, f θ ≠ 0) (a s : ℝ) (ha : a ≠ 0)
    (hs : HasDerivAt (fun θ ↦ Real.log (f θ)) s 0) :
    HasDerivAt (fun θ ↦ Real.log (a * f θ)) s 0 := by
  have hh := (hasDerivAt_const (0 : ℝ) (Real.log a)).add hs
  convert hh using 1
  · funext θ
    exact Real.log_mul ha (hf θ)
  · simp

/-- The marked Gaussian likelihood is everywhere positive for an interior event probability. -/
theorem markedDensity_pos (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (θ : ℝ) (z : Bool) (y : ℝ) :
    0 < markedDensity η v θ z y := by
  cases z
  · exact mul_pos (sub_pos.mpr hη.2) (gaussianPDFReal_pos _ _ _ hv)
  · exact mul_pos hη.1 (gaussianPDFReal_pos _ _ _ hv)

/-- Erasing the event gives a strictly positive Gaussian-mixture likelihood. -/
theorem erasedDensity_pos (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (θ y : ℝ) : 0 < erasedDensity η v θ y :=
  add_pos (mul_pos (sub_pos.mpr hη.2) (gaussianPDFReal_pos _ _ _ hv))
    (mul_pos hη.1 (gaussianPDFReal_pos _ _ _ hv))

/-- The actual observed likelihood has the stated null score, including q=0 and q=1. -/
theorem observation_log_score (q η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (o : Observation) :
    HasDerivAt (fun θ ↦ Real.log (observationDensity q η v θ o)) (nullScore q η v o) 0 := by
  cases o with
  | inl zy =>
    by_cases hq : q = 0
    · simp only [observationDensity, nullScore, hq, if_true, zero_mul]
      exact hasDerivAt_const _ _
    · simp only [observationDensity, nullScore, hq, if_false]
      exact scaled_log_score _ (fun θ ↦ (markedDensity_pos η hη v hv θ zy.1 zy.2).ne')
        q _ hq (marked_log_score η hη v hv zy.1 zy.2)
  | inr y =>
    by_cases hq : q = 1
    · simp only [observationDensity, nullScore, hq, if_true, sub_self, zero_mul]
      exact hasDerivAt_const _ _
    · simp only [observationDensity, nullScore, hq, if_false]
      exact scaled_log_score _ (fun θ ↦ (erasedDensity_pos η hη v hv θ y).ne')
        (1 - q) _ (sub_ne_zero.mpr (Ne.symm hq)) (erased_log_score η v hv y)

/-- The null score is a measurable statistic of exactly the data that were revealed. -/
theorem nullScore_measurable (q η : ℝ) (v : ℝ≥0) : Measurable (nullScore q η v) := by
  change Measurable (Sum.elim
    (fun zy ↦ if q = 0 then 0 else markedEstimate (v : ℝ) zy)
    (fun y ↦ if q = 1 then 0 else η * y / v))
  apply Measurable.sumElim
  · by_cases hq : q = 0
    · simpa only [hq, if_true] using (measurable_const : Measurable (fun _ : Bool × ℝ ↦ (0 : ℝ)))
    · simpa only [hq, if_false] using markedEstimate_measurable (v : ℝ)
  · by_cases hq : q = 1 <;> simp only [hq, if_true, if_false] <;> fun_prop

end Descent.Portability.PartialLabelExperiment
