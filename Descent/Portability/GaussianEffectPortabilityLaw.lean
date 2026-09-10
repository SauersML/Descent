/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CalibrationLaw
import Descent.Portability.PartialMetricMixture

assert_below Descent.Decision Descent.Program

/-!
Gaussian causal-effect integration for fixed genotypes, sample splits, and a
label-dependent learner. Calibrated binary-label probabilities and per-run
accuracy ratios retain their dependence on the same effect vector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianEffectPortabilityLaw

open MeasureTheory ProbabilityTheory FiniteReportLaw SimulationAccuracy CalibrationLaw
open TrainingNoiseAccuracy PartialMetricMixture
open scoped ENNReal

variable {U I S T J K : Type*}
  [Fintype U] [Fintype I] [DecidableEq I] [Fintype S] [Fintype T] [Fintype J] [Fintype K]

/-- Fixed genetic data and cohort maps. The learner is still supplied as a
label-dependent function; this structure does not assert PLINK equivalence. -/
structure FixedDesign (U I S T J K : Type*)
    [Fintype U] [Fintype S] [Fintype T] where
  cohort : FiniteReportLaw U
  source : FiniteReportLaw S
  target : FiniteReportLaw T
  causalGenotype : U → K → ℝ
  sourceGenotype : S → J → ℝ
  targetGenotype : T → J → ℝ
  trainingIndex : I → U
  sourceIndex : S → U
  targetIndex : T → U
  baseline : U → ℝ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  baseline_bound : ∀ u, -(7 / 10) ≤ baseline u ∧ baseline u ≤ 7 / 10
  learn : (I → Bool) → Option (J → ℝ)

variable (design : FixedDesign U I S T J K)

noncomputable def effectLaw (K : Type*) [Fintype K] : Measure (K → ℝ) :=
  Measure.pi (fun _ : K ↦ gaussianReal 0 1)

instance effectLaw_probability : IsProbabilityMeasure (effectLaw K) := by
  unfold effectLaw
  infer_instance

noncomputable def caseProbability (effects : K → ℝ) (i : I) : ℝ :=
  let raw := linearScore design.causalGenotype effects
  ProbitTrainingLaw.caseProbability
    (calibratedIntercept design.cohort design.baseline design.epsilon design.epsilon_pos
      design.baseline_bound raw + design.baseline (design.trainingIndex i) +
        standardize design.cohort design.epsilon raw (design.trainingIndex i)) 1

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem caseProbability_measurable (i : I) :
    Measurable (fun effects ↦ caseProbability design effects i) :=
  calibrated_effectProbability_measurable design.cohort design.baseline design.causalGenotype
    design.epsilon design.epsilon_pos design.baseline_bound (design.trainingIndex i)

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem caseProbability_bounds (effects : K → ℝ) (i : I) :
    0 ≤ caseProbability design effects i ∧ caseProbability design effects i ≤ 1 :=
  ProbitTrainingLaw.caseProbability_bounds _ _

noncomputable def labelKernel : FiniteOutcomeKernel (K → ℝ) (I → Bool) where
  weight := fun effects ↦ labelMass (caseProbability design effects)
  weight_nonneg := fun effects ↦ labelMass_nonneg _ (caseProbability_bounds design effects)
  weight_sum_one := fun effects ↦ labelMass_sum (caseProbability design effects)
  weight_measurable := by
    intro outcome
    unfold labelMass
    apply Finset.measurable_prod
    intro i _
    cases outcome i
    · exact measurable_const.sub (caseProbability_measurable design i)
    · exact caseProbability_measurable design i

noncomputable def jointLaw : Measure ((K → ℝ) × (I → Bool)) :=
  (labelKernel design).jointMeasure (effectLaw K)

instance jointLaw_probability : IsProbabilityMeasure (jointLaw design) := by
  unfold jointLaw
  infer_instance

noncomputable def report (effects : K → ℝ) (outcome : I → Bool) : Option ℝ :=
  (design.learn outcome).bind fun weights ↦
    formRatio design.source design.target design.sourceGenotype design.targetGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s))
      (fun t ↦ design.causalGenotype (design.targetIndex t)) weights effects

omit [Fintype U] [Fintype I] [DecidableEq I] [Fintype T] in
theorem crossForm_effects_continuous (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ) (weights : J → ℝ) :
    Continuous (fun effects ↦ crossForm p scoreGenotype causalGenotype weights effects) := by
  unfold crossForm
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  exact (continuous_const.mul (continuous_apply k)).mul continuous_const

omit [Fintype U] [Fintype I] [DecidableEq I] [Fintype T] [Fintype J] in
theorem varianceForm_effects_continuous (p : FiniteReportLaw S)
    (genotype : S → K → ℝ) :
    Continuous (fun effects ↦ varianceForm p genotype effects) := by
  unfold varianceForm
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  exact ((continuous_apply j).mul (continuous_apply k)).mul continuous_const

omit [Fintype U] [Fintype I] [DecidableEq I] in
theorem formRatio_observable_measurable (source : FiniteReportLaw S)
    (target : FiniteReportLaw T) (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (observe : Option ℝ → ℝ) (ho : Measurable (fun r ↦ observe (some r))) :
    Measurable (fun effects ↦ observe
      (formRatio source target sourceScore targetScore
        sourceCausal targetCausal weights effects)) := by
  let vs := varianceForm source sourceScore weights
  let vt := varianceForm target targetScore weights
  let gs := fun effects ↦ varianceForm source sourceCausal effects
  let gt := fun effects ↦ varianceForm target targetCausal effects
  let cs := fun effects ↦ crossForm source sourceScore sourceCausal weights effects
  let ct := fun effects ↦ crossForm target targetScore targetCausal weights effects
  let rs := fun effects ↦ cs effects ^ 2 / (vs * gs effects)
  let rt := fun effects ↦ ct effects ^ 2 / (vt * gt effects)
  have hgs : Measurable gs := (varianceForm_effects_continuous source sourceCausal).measurable
  have hgt : Measurable gt := (varianceForm_effects_continuous target targetCausal).measurable
  have hcs : Measurable cs :=
    (crossForm_effects_continuous source sourceScore sourceCausal weights).measurable
  have hct : Measurable ct :=
    (crossForm_effects_continuous target targetScore targetCausal weights).measurable
  have hrs : Measurable rs := (hcs.pow_const 2).div (measurable_const.mul hgs)
  have hrt : Measurable rt := (hct.pow_const 2).div (measurable_const.mul hgt)
  have heq : (fun effects ↦ observe
      (formRatio source target sourceScore targetScore sourceCausal targetCausal weights effects)) =
      (fun effects ↦ if 0 < vs ∧ 0 < gs effects then
        if 0 < vt ∧ 0 < gt effects then
          if 0 < rs effects then observe (some (rt effects / rs effects)) else observe none
        else observe none
      else observe none) := by
    funext effects
    dsimp only [formRatio, formAccuracy, vs, vt, gs, gt, cs, ct, rs, rt]
    split_ifs <;> simp_all
  have hsource : MeasurableSet {effects : K → ℝ | 0 < vs ∧ 0 < gs effects} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_const).inter
      (measurableSet_lt measurable_const hgs)
  have htarget : MeasurableSet {effects : K → ℝ | 0 < vt ∧ 0 < gt effects} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_const).inter
      (measurableSet_lt measurable_const hgt)
  rw [heq]
  apply Measurable.ite hsource _ measurable_const
  apply Measurable.ite htarget _ measurable_const
  exact Measurable.ite (measurableSet_lt measurable_const hrs)
    (ho.comp (hrt.div hrs)) measurable_const

omit [Fintype I] [DecidableEq I] in
theorem report_observable_measurable (outcome : I → Bool)
    (observe : Option ℝ → ℝ) (ho : Measurable (fun r ↦ observe (some r))) :
    Measurable (fun effects ↦ observe (report design effects outcome)) := by
  unfold report
  cases h : design.learn outcome with
  | none =>
    simp only [Option.bind_none]
    exact measurable_const
  | some weights =>
    exact formRatio_observable_measurable design.source design.target
      design.sourceGenotype design.targetGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s))
      (fun t ↦ design.causalGenotype (design.targetIndex t)) weights observe ho

omit [Fintype I] [DecidableEq I] in
theorem report_eq_ratio (effects : K → ℝ) (outcome : I → Bool) :
    report design effects outcome =
      ratio design.source design.target design.sourceGenotype design.targetGenotype
        (linearScore (fun s ↦ design.causalGenotype (design.sourceIndex s)) effects)
        (linearScore (fun t ↦ design.causalGenotype (design.targetIndex t)) effects)
        design.learn outcome := by
  rw [ratio_eq_formRatio]
  rfl

omit [Fintype I] [DecidableEq I] in
theorem report_nonneg (effects : K → ℝ) (outcome : I → Bool) (r : ℝ)
    (hr : report design effects outcome = some r) : 0 ≤ r := by
  rw [report_eq_ratio] at hr
  exact ratio_nonneg design.source design.target design.sourceGenotype design.targetGenotype
    _ _ design.learn outcome hr

noncomputable def clippedReport (cap : ℝ) (effects : K → ℝ) (outcome : I → Bool) : Option ℝ :=
  (report design effects outcome).map (fun r ↦ min r cap)

omit [Fintype I] [DecidableEq I] in
theorem clippedReport_defined (cap : ℝ) (effects : K → ℝ) (outcome : I → Bool) :
    (clippedReport design cap effects outcome).isSome = (report design effects outcome).isSome := by
  simp [clippedReport]

omit [Fintype I] [DecidableEq I] in
theorem clippedReport_value_bounds (cap : ℝ) (hc : 0 ≤ cap)
    (effects : K → ℝ) (outcome : I → Bool) :
    0 ≤ (clippedReport design cap effects outcome).getD 0 ∧
      (clippedReport design cap effects outcome).getD 0 ≤ cap := by
  unfold clippedReport
  cases h : report design effects outcome with
  | none => simpa using hc
  | some r =>
    simp only [Option.map_some, Option.getD_some]
    exact ⟨le_min (report_nonneg design effects outcome r h) hc, min_le_right _ _⟩

omit [Fintype I] [DecidableEq I] in
theorem clippedReport_value_measurable (cap : ℝ) (outcome : I → Bool) :
    Measurable (fun effects ↦ (clippedReport design cap effects outcome).getD 0) :=
  report_observable_measurable design outcome
    (fun value ↦ (value.map (fun r ↦ min r cap)).getD 0) (measurable_id.min measurable_const)

omit [Fintype I] [DecidableEq I] in
theorem report_defined_measurable (outcome : I → Bool) :
    Measurable (fun effects ↦ if (report design effects outcome).isSome then (1 : ℝ) else 0) :=
  report_observable_measurable design outcome
    (fun value ↦ if value.isSome then (1 : ℝ) else 0) measurable_const

omit [Fintype J] in
theorem labelWeight_le_one (effects : K → ℝ) (outcome : I → Bool) :
    (labelKernel design).weight effects outcome ≤ 1 := by
  rw [← (labelKernel design).weight_sum_one effects]
  exact Finset.single_le_sum
    (fun other _ ↦ (labelKernel design).weight_nonneg effects other) (Finset.mem_univ outcome)

omit [Fintype J] in
private theorem weighted_observable_integrable (outcome : I → Bool) (value : (K → ℝ) → ℝ)
    (hmeas : Measurable value) (cap : ℝ)
    (hb : ∀ effects, 0 ≤ value effects ∧ value effects ≤ cap) :
    Integrable (fun effects ↦ (labelKernel design).weight effects outcome * value effects)
      (effectLaw K) := by
  apply (integrable_const cap).mono'
    (((labelKernel design).weight_measurable outcome).mul hmeas).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro effects
  have hnonneg := mul_nonneg ((labelKernel design).weight_nonneg effects outcome) (hb effects).1
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact le_trans (mul_le_of_le_one_left (hb effects).1
    (labelWeight_le_one design effects outcome)) (hb effects).2

theorem weighted_clipped_integrable (cap : ℝ) (hc : 0 ≤ cap) (outcome : I → Bool) :
    Integrable (fun effects ↦ (labelKernel design).weight effects outcome *
      (clippedReport design cap effects outcome).getD 0) (effectLaw K) :=
  weighted_observable_integrable design outcome _
    (clippedReport_value_measurable design cap outcome) cap
    (fun effects ↦ clippedReport_value_bounds design cap hc effects outcome)

theorem weighted_defined_integrable (outcome : I → Bool) :
    Integrable (fun effects ↦ (labelKernel design).weight effects outcome *
      (if (report design effects outcome).isSome then (1 : ℝ) else 0)) (effectLaw K) := by
  apply weighted_observable_integrable design outcome _ (report_defined_measurable design outcome) 1
  intro effects
  split_ifs <;> norm_num

noncomputable def successProbability : ℝ :=
  ∫ effects, ∑ outcome, (labelKernel design).weight effects outcome *
    (if (report design effects outcome).isSome then (1 : ℝ) else 0) ∂effectLaw K

noncomputable def innerValue (effects : K → ℝ) : ℝ :=
  ∑ outcome, (labelKernel design).weight effects outcome * (report design effects outcome).getD 0

noncomputable def clippedInner (cap : ℝ) (effects : K → ℝ) : ℝ :=
  ∑ outcome, (labelKernel design).weight effects outcome *
    (clippedReport design cap effects outcome).getD 0

noncomputable def clippedNumerator (cap : ℝ) : ℝ :=
  ∫ effects, clippedInner design cap effects ∂effectLaw K

noncomputable def clippedExpectation (cap : ℝ) : Option ℝ :=
  PartialMetricMixture.conditionalMetric (jointLaw design)
    (fun pair ↦ clippedReport design cap pair.1 pair.2)

/-- Every clipped ratio is integrable under the constructed effect/label law.
The clipping does not change which runs can report an accuracy ratio. -/
theorem clippedExpectation_formula (cap : ℝ) (hc : 0 ≤ cap) :
    clippedExpectation design cap =
      if successProbability design = 0 then none
      else some (clippedNumerator design cap / successProbability design) := by
  have hd : ∀ outcome, Integrable (fun effects ↦ (labelKernel design).weight effects outcome *
      (if (clippedReport design cap effects outcome).isSome then (1 : ℝ) else 0))
        (effectLaw K) := by
    intro outcome
    simp only [clippedReport_defined]
    exact weighted_defined_integrable design outcome
  have h := PartialMetricMixture.conditionalMetric_jointMeasure (labelKernel design) (effectLaw K)
    (fun pair ↦ clippedReport design cap pair.1 pair.2) hd
    (weighted_clipped_integrable design cap hc)
  simpa only [clippedExpectation, jointLaw, successProbability, clippedNumerator,
    FiniteReportLaw.definedMass, FiniteReportLaw.weightedDefinedMetric,
    FiniteOutcomeKernel.lawAt, clippedInner, clippedReport_defined] using h

/-- An explicit Gaussian effect integral for each binary label configuration.
The target/source quotient remains inside both the label sum and effect integral. -/
theorem clippedNumerator_eq_sum_integrals (cap : ℝ) (hc : 0 ≤ cap) :
    clippedNumerator design cap =
      ∑ outcome, ∫ effects, (labelKernel design).weight effects outcome *
        (clippedReport design cap effects outcome).getD 0 ∂effectLaw K := by
  unfold clippedNumerator clippedInner
  exact integral_finset_sum _ (fun outcome _ ↦ weighted_clipped_integrable design cap hc outcome)

omit [Fintype I] [DecidableEq I] in
theorem reportValue_nonneg (effects : K → ℝ) (outcome : I → Bool) :
    0 ≤ (report design effects outcome).getD 0 := by
  cases h : report design effects outcome with
  | none => rfl
  | some r => exact report_nonneg design effects outcome r h

omit [Fintype I] [DecidableEq I] in
theorem reportValue_measurable (outcome : I → Bool) :
    Measurable (fun effects ↦ (report design effects outcome).getD 0) :=
  report_observable_measurable design outcome (fun value ↦ value.getD 0) measurable_id

theorem innerValue_nonneg (effects : K → ℝ) : 0 ≤ innerValue design effects := by
  apply Finset.sum_nonneg
  intro outcome _
  exact mul_nonneg ((labelKernel design).weight_nonneg effects outcome)
    (reportValue_nonneg design effects outcome)

theorem innerValue_measurable : Measurable (innerValue design) := by
  apply Finset.measurable_sum
  intro outcome _
  exact ((labelKernel design).weight_measurable outcome).mul (reportValue_measurable design outcome)

theorem clippedInner_nonneg (cap : ℝ) (hc : 0 ≤ cap) (effects : K → ℝ) :
    0 ≤ clippedInner design cap effects := by
  apply Finset.sum_nonneg
  intro outcome _
  exact mul_nonneg ((labelKernel design).weight_nonneg effects outcome)
    (clippedReport_value_bounds design cap hc effects outcome).1

theorem clippedInner_measurable (cap : ℝ) : Measurable (clippedInner design cap) := by
  apply Finset.measurable_sum
  intro outcome _
  exact ((labelKernel design).weight_measurable outcome).mul
    (clippedReport_value_measurable design cap outcome)

theorem clippedInner_integrable (cap : ℝ) (hc : 0 ≤ cap) :
    Integrable (clippedInner design cap) (effectLaw K) :=
  integrable_finset_sum _ (fun outcome _ ↦ weighted_clipped_integrable design cap hc outcome)

omit [Fintype I] [DecidableEq I] in
theorem clippedReport_value_eq_min (cap : ℝ) (hc : 0 ≤ cap)
    (effects : K → ℝ) (outcome : I → Bool) :
    (clippedReport design cap effects outcome).getD 0 =
      min ((report design effects outcome).getD 0) cap := by
  unfold clippedReport
  cases h : report design effects outcome <;> simp [min_eq_left hc]

theorem clippedInner_le_innerValue (cap : ℝ) (hc : 0 ≤ cap) (effects : K → ℝ) :
    clippedInner design cap effects ≤ innerValue design effects := by
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ ((labelKernel design).weight_nonneg effects outcome)
  rw [clippedReport_value_eq_min design cap hc]
  exact min_le_left _ _

theorem clippedInner_nat_mono : Monotone (fun n : ℕ ↦ clippedInner design (n : ℝ)) := by
  intro m n hmn effects
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ ((labelKernel design).weight_nonneg effects outcome)
  rw [clippedReport_value_eq_min design m (Nat.cast_nonneg _),
    clippedReport_value_eq_min design n (Nat.cast_nonneg _)]
  exact min_le_min_left _ (Nat.cast_le.mpr hmn)

theorem innerValue_eq_iSup_clipped (effects : K → ℝ) :
    ENNReal.ofReal (innerValue design effects) =
      ⨆ n : ℕ, ENNReal.ofReal (clippedInner design (n : ℝ) effects) := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := exists_nat_gt (∑ outcome : I → Bool,
      (report design effects outcome).getD 0)
    have hcap (outcome : I → Bool) : (report design effects outcome).getD 0 ≤ (n : ℝ) := by
      exact le_trans (Finset.single_le_sum
        (fun other _ ↦ reportValue_nonneg design effects other) (Finset.mem_univ outcome)) hn.le
    have heq : clippedInner design (n : ℝ) effects = innerValue design effects := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [clippedReport_value_eq_min design n (Nat.cast_nonneg _), min_eq_left (hcap outcome)]
    exact le_iSup_of_le n (le_of_eq (congrArg ENNReal.ofReal heq.symm))
  · exact iSup_le (fun n ↦ ENNReal.ofReal_le_ofReal
      (clippedInner_le_innerValue design n (Nat.cast_nonneg _) effects))

noncomputable def extendedNumerator : ENNReal :=
  ∫⁻ effects, ENNReal.ofReal (innerValue design effects) ∂effectLaw K

theorem ofReal_clippedNumerator (cap : ℝ) (hc : 0 ≤ cap) :
    ENNReal.ofReal (clippedNumerator design cap) =
      ∫⁻ effects, ENNReal.ofReal (clippedInner design cap effects) ∂effectLaw K :=
  ofReal_integral_eq_lintegral_ofReal (clippedInner_integrable design cap hc)
    (Filter.Eventually.of_forall (clippedInner_nonneg design cap hc))

/-- Monotone convergence recovers the untruncated nonnegative numerator without
assuming that its expectation is finite. This is a limit of the exact clipped
Gaussian-effect/label integrals, not a ratio of marginal accuracy expectations. -/
theorem extendedNumerator_eq_iSup_clipped :
    extendedNumerator design = ⨆ n : ℕ, ENNReal.ofReal (clippedNumerator design (n : ℝ)) := by
  unfold extendedNumerator
  simp_rw [innerValue_eq_iSup_clipped]
  rw [lintegral_iSup]
  · congr 1
    funext n
    exact (ofReal_clippedNumerator design n (Nat.cast_nonneg _)).symm
  · intro n
    exact (clippedInner_measurable design n).ennreal_ofReal
  · intro m n hmn effects
    exact ENNReal.ofReal_le_ofReal (clippedInner_nat_mono design hmn effects)

/-- Finiteness is an explicit analytic condition on the derived integrand;
Lean's totalized real integral is never used to disguise a divergent expectation. -/
theorem integrable_innerValue_iff :
    Integrable (innerValue design) (effectLaw K) ↔ extendedNumerator design < ∞ := by
  rw [Integrable, hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (innerValue_nonneg design))]
  exact and_iff_right (innerValue_measurable design).aestronglyMeasurable

theorem successProbability_eq_joint_defined :
    successProbability design = PartialMetricMixture.definedMass (jointLaw design)
      (fun pair ↦ report design pair.1 pair.2) := by
  exact (PartialMetricMixture.definedMass_jointMeasure (labelKernel design) (effectLaw K)
    (fun pair ↦ report design pair.1 pair.2) (weighted_defined_integrable design)).symm

theorem successProbability_bounds :
    0 ≤ successProbability design ∧ successProbability design ≤ 1 := by
  rw [successProbability_eq_joint_defined]
  unfold PartialMetricMixture.definedMass
  have hi := (labelKernel design).integrable_jointMeasure (effectLaw K)
    (fun pair ↦ if (report design pair.1 pair.2).isSome then (1 : ℝ) else 0)
    (weighted_defined_integrable design)
  constructor
  · apply integral_nonneg
    intro pair
    dsimp only
    split_ifs <;> norm_num
  · have h : (∫ pair, if (report design pair.1 pair.2).isSome then (1 : ℝ) else 0
        ∂jointLaw design) ≤ ∫ _ : (K → ℝ) × (I → Bool), (1 : ℝ) ∂jointLaw design := by
      apply integral_mono hi (integrable_const 1)
      intro pair
      dsimp only
      split_ifs <;> norm_num
    simpa using h

theorem weighted_report_integrable (hfinite : extendedNumerator design < ∞) (outcome : I → Bool) :
    Integrable (fun effects ↦ (labelKernel design).weight effects outcome *
      (report design effects outcome).getD 0) (effectLaw K) := by
  have hi := (integrable_innerValue_iff design).mpr hfinite
  apply hi.mono'
    (((labelKernel design).weight_measurable outcome).mul
      (reportValue_measurable design outcome)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro effects
  have hn := mul_nonneg ((labelKernel design).weight_nonneg effects outcome)
    (reportValue_nonneg design effects outcome)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact Finset.single_le_sum (fun other _ ↦ mul_nonneg
    ((labelKernel design).weight_nonneg effects other) (reportValue_nonneg design effects other))
    (Finset.mem_univ outcome)

theorem extendedNumerator_toReal (hfinite : extendedNumerator design < ∞) :
    (extendedNumerator design).toReal = ∫ effects, innerValue design effects ∂effectLaw K := by
  have h := ofReal_integral_eq_lintegral_ofReal ((integrable_innerValue_iff design).mpr hfinite)
    (Filter.Eventually.of_forall (innerValue_nonneg design))
  have hn : 0 ≤ ∫ effects, innerValue design effects ∂effectLaw K :=
    integral_nonneg (innerValue_nonneg design)
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal hn] at h'
  exact h'.symm

/-- Exact expectation after integrating Gaussian causal effects and calibrated
training labels, when the derived nonnegative integral is finite. The actual
per-realization target/source ratio is evaluated before either random stage is
integrated; the success normalization is applied once after both stages. -/
theorem finite_reportedExpectation_formula (hfinite : extendedNumerator design < ∞) :
    PartialMetricMixture.conditionalMetric (jointLaw design)
      (fun pair ↦ report design pair.1 pair.2) =
      if successProbability design = 0 then none
      else some ((extendedNumerator design).toReal / successProbability design) := by
  rw [extendedNumerator_toReal design hfinite]
  exact PartialMetricMixture.conditionalMetric_jointMeasure
    (labelKernel design) (effectLaw K) (fun pair ↦ report design pair.1 pair.2)
    (weighted_defined_integrable design) (weighted_report_integrable design hfinite)

/-- Extended expectation retains possible nonintegrability and rejects a
zero-probability reporting event. No finiteness or divergence is asserted. -/
noncomputable def extendedExpectation : Option ENNReal :=
  if successProbability design = 0 then none
  else some (extendedNumerator design / ENNReal.ofReal (successProbability design))

end Descent.Portability.GaussianEffectPortabilityLaw
