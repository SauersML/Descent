/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DistanceBinnedPortabilityLaw

assert_below Descent.Decision Descent.Program

/-!
Geometry of the actual target/source squared-correlation ratio. Covariance
alignment cancels its source cross-form denominator. A trait-variance comparison
then bounds the ratio without imposing a positive source-accuracy floor. The
conditions concern the realized genotype matrices and learned weights; they are
not asserted for arbitrary demographies or for the simulation's fitted scores.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityRatioGeometry

open MeasureTheory FiniteReportLaw TrainingNoiseAccuracy SimulationAccuracy
open GaussianEffectPortabilityLaw
open scoped ENNReal

variable {S T J K : Type*} [Fintype S] [Fintype T] [Fintype J] [Fintype K]

noncomputable def covarianceVector (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (k : K) : ℝ :=
  ∑ j, weights j * p.covariance (fun s ↦ scoreGenotype s j) (fun s ↦ causalGenotype s k)

omit [Fintype T] in
/-- Effects enter the score/trait covariance through a finite coefficient vector. -/
theorem crossForm_eq_dot (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ) :
    crossForm p scoreGenotype causalGenotype weights effects =
      ∑ k, covarianceVector p scoreGenotype causalGenotype weights k * effects k := by
  unfold crossForm covarianceVector
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (source : FiniteReportLaw S) (target : FiniteReportLaw T)
  (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
  (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
  (weights : J → ℝ)

/-- A finite coefficient identity suffices for covariance alignment at all effects. -/
theorem crossForm_aligned (factor : ℝ)
    (halign : ∀ k, covarianceVector target targetScore targetCausal weights k =
      factor * covarianceVector source sourceScore sourceCausal weights k) (effects : K → ℝ) :
    crossForm target targetScore targetCausal weights effects =
      factor * crossForm source sourceScore sourceCausal weights effects := by
  rw [crossForm_eq_dot, crossForm_eq_dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [halign]
  ring

/-- Reporting a ratio supplies all positivity conditions and a nonzero source
cross form. Zero source accuracy is excluded by the existing reporting rule. -/
theorem formRatio_some_domain (effects : K → ℝ) (value : ℝ)
    (h : formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects = some value) :
    0 < varianceForm source sourceScore weights ∧
      0 < varianceForm source sourceCausal effects ∧
      0 < varianceForm target targetScore weights ∧
      0 < varianceForm target targetCausal effects ∧
      crossForm source sourceScore sourceCausal weights effects ≠ 0 := by
  unfold formRatio formAccuracy at h
  split_ifs at h with hs ht hr
  all_goals simp only [Option.bind_some, Option.bind_none] at h
  all_goals try { contradiction }
  exact ⟨hs.1, hs.2, ht.1, ht.2, fun hz ↦ by simp [hz] at h⟩

/-- On every reportable realization, aligned cross vectors cancel exactly;
what remains is a ratio of trait variances and a fixed score-variance factor. -/
theorem formRatio_aligned_value (factor : ℝ)
    (halign : ∀ k, covarianceVector target targetScore targetCausal weights k =
      factor * covarianceVector source sourceScore sourceCausal weights k)
    (effects : K → ℝ) (value : ℝ)
    (h : formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects = some value) :
    value = (factor ^ 2 * varianceForm source sourceScore weights /
      varianceForm target targetScore weights) *
      (varianceForm source sourceCausal effects / varianceForm target targetCausal effects) := by
  obtain ⟨hss, hsc, hts, htc, hcross⟩ := formRatio_some_domain source target
    sourceScore targetScore sourceCausal targetCausal weights effects value h
  have hv := formRatio_value source target sourceScore targetScore sourceCausal targetCausal
    weights effects hss hsc hts htc hcross
  rw [h] at hv
  have heq := Option.some.inj hv
  rw [heq, crossForm_aligned source target sourceScore targetScore sourceCausal targetCausal
    weights factor halign effects]
  field_simp

/-- Variance domination is sufficient for a finite bound even when arbitrarily
small positive source accuracies are allowed by the reporting rule. -/
theorem formRatio_aligned_le (factor domination : ℝ)
    (halign : ∀ k, covarianceVector target targetScore targetCausal weights k =
      factor * covarianceVector source sourceScore sourceCausal weights k)
    (hdom : ∀ effects, varianceForm source sourceCausal effects ≤
      domination * varianceForm target targetCausal effects)
    (effects : K → ℝ) (value : ℝ)
    (h : formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects = some value) :
    value ≤ factor ^ 2 * varianceForm source sourceScore weights /
      varianceForm target targetScore weights * domination := by
  obtain ⟨hss, hsc, hts, htc, hcross⟩ := formRatio_some_domain source target
    sourceScore targetScore sourceCausal targetCausal weights effects value h
  rw [formRatio_aligned_value source target sourceScore targetScore sourceCausal targetCausal
    weights factor halign effects value h]
  apply mul_le_mul_of_nonneg_left ((div_le_iff₀ htc).mpr (hdom effects))
  exact div_nonneg (mul_nonneg (sq_nonneg factor) hss.le) hts.le


omit [Fintype T] in
theorem varianceForm_nonneg (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (coefficients : J → ℝ) :
    0 ≤ varianceForm p genotype coefficients := by
  simpa only [variance_linearScore, varianceForm] using
    p.variance_nonneg (linearScore genotype coefficients)

/-- The domination condition is exactly positivity of the difference of two
finite trait covariance forms, so it is a condition on the genotype matrices. -/
theorem trait_domination_iff (domination : ℝ) :
    (∀ effects, varianceForm source sourceCausal effects ≤
      domination * varianceForm target targetCausal effects) ↔
    ∀ effects : K → ℝ, 0 ≤ ∑ j, ∑ k, effects j * effects k *
      (domination * target.covariance (fun t ↦ targetCausal t j) (fun t ↦ targetCausal t k) -
        source.covariance (fun s ↦ sourceCausal s j) (fun s ↦ sourceCausal s k)) := by
  have heq (effects : K → ℝ) :
      (∑ j, ∑ k, effects j * effects k *
        (domination * target.covariance (fun t ↦ targetCausal t j) (fun t ↦ targetCausal t k) -
          source.covariance (fun s ↦ sourceCausal s j) (fun s ↦ sourceCausal s k))) =
      domination * varianceForm target targetCausal effects -
        varianceForm source sourceCausal effects := by
    simp only [mul_sub, Finset.sum_sub_distrib, varianceForm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [heq, sub_nonneg]

structure AlignmentCertificate where
  factor : ℝ
  domination : ℝ
  domination_nonneg : 0 ≤ domination
  aligned : ∀ k, covarianceVector target targetScore targetCausal weights k =
    factor * covarianceVector source sourceScore sourceCausal weights k
  dominated : ∀ effects, varianceForm source sourceCausal effects ≤
    domination * varianceForm target targetCausal effects

namespace AlignmentCertificate

variable (certificate : AlignmentCertificate source target sourceScore targetScore
  sourceCausal targetCausal weights)

noncomputable def bound : ℝ :=
  certificate.factor ^ 2 * varianceForm source sourceScore weights /
    varianceForm target targetScore weights * certificate.domination

theorem bound_nonneg : 0 ≤ certificate.bound :=
  mul_nonneg (div_nonneg
    (mul_nonneg (sq_nonneg _) (varianceForm_nonneg source sourceScore weights))
    (varianceForm_nonneg target targetScore weights)) certificate.domination_nonneg

theorem ratio_le_bound (effects : K → ℝ) :
    (formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects).getD 0 ≤ certificate.bound := by
  cases h : formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects with
  | none => exact certificate.bound_nonneg
  | some value =>
    exact formRatio_aligned_le source target sourceScore targetScore sourceCausal targetCausal
      weights certificate.factor certificate.domination certificate.aligned certificate.dominated
      effects value h

end AlignmentCertificate

section Effects

variable {U I : Type*} [Fintype U] [Fintype I] [DecidableEq I]
  (design : FixedDesign U I S T J K)

abbrev LearnedCertificate (weights : J → ℝ) :=
  AlignmentCertificate design.source design.target design.sourceGenotype design.targetGenotype
    (fun s ↦ design.causalGenotype (design.sourceIndex s))
    (fun t ↦ design.causalGenotype (design.targetIndex t)) weights

variable (certificates : ∀ outcome weights, design.learn outcome = some weights →
  LearnedCertificate design weights)

noncomputable def outcomeBound (outcome : I → Bool) : ℝ :=
  match h : design.learn outcome with
  | none => 0
  | some weights => (certificates outcome weights h).bound

omit [Fintype I] [DecidableEq I] in
theorem outcomeBound_nonneg (outcome : I → Bool) :
    0 ≤ outcomeBound design certificates outcome := by
  unfold outcomeBound
  split
  · exact le_rfl
  · rename_i weights h
    exact AlignmentCertificate.bound_nonneg _ _ _ _ _ _ _ (certificates outcome weights h)

omit [Fintype I] [DecidableEq I] in
theorem report_le_outcomeBound (effects : K → ℝ) (outcome : I → Bool) :
    (report design effects outcome).getD 0 ≤ outcomeBound design certificates outcome := by
  unfold outcomeBound
  split
  · rename_i h
    simp only [report, h, Option.bind_none, Option.getD_none]
    exact le_rfl
  · rename_i weights h
    simp only [report, h, Option.bind_some]
    exact AlignmentCertificate.ratio_le_bound _ _ _ _ _ _ _
      (certificates outcome weights h) effects

include certificates

/-- Coefficient alignment and covariance-form domination for every possible
learned score imply integrability over the actual shared Gaussian effect and
calibrated-label law. No lower bound on source R² is assumed. -/
theorem certified_innerValue_integrable : Integrable (innerValue design) (effectLaw K) := by
  apply (integrable_const (∑ outcome, outcomeBound design certificates outcome)).mono'
    (innerValue_measurable design).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro effects
  rw [Real.norm_eq_abs, abs_of_nonneg (innerValue_nonneg design effects)]
  apply Finset.sum_le_sum
  intro outcome _
  exact (mul_le_of_le_one_left (reportValue_nonneg design effects outcome)
    (labelWeight_le_one design effects outcome)).trans
    (report_le_outcomeBound design certificates effects outcome)

theorem certified_extendedNumerator_finite : extendedNumerator design < ∞ :=
  (integrable_innerValue_iff design).mp (certified_innerValue_integrable design certificates)

/-- The derived certificate discharges the finiteness premise of the ordinary
conditional expectation theorem for the untruncated portability ratio. -/
theorem certified_expected_ratio :
    PartialMetricMixture.conditionalMetric (jointLaw design)
      (fun pair ↦ report design pair.1 pair.2) =
      if successProbability design = 0 then none else
        some ((extendedNumerator design).toReal / successProbability design) :=
  finite_reportedExpectation_formula design
    (certified_extendedNumerator_finite design certificates)

end Effects


section DistanceBins

open DistanceBinnedPortabilityLaw

variable {D U I : Type*} [Fintype D] [DecidableEq D]
  [Fintype U] [Fintype I] [DecidableEq I]
  (design : FixedDesign U I S S J K) (targets : TargetCohorts D U S J)
  (certificates : ∀ deme outcome weights, design.learn outcome = some weights →
    LearnedCertificate (targetDesign design targets deme) weights)

omit [DecidableEq D] [Fintype I] [DecidableEq I] in
/-- Common run acceptance can only remove nonnegative contributions. The
average of an available bin is bounded by the sum over all evaluation demes. -/
theorem binReport_le_sum (distance : ℕ) (effects : K → ℝ) (outcome : I → Bool) :
    (binReport design targets distance effects outcome).getD 0 ≤
      ∑ deme : D, (report (targetDesign design targets deme) effects outcome).getD 0 := by
  classical
  unfold binReport
  split_ifs with h
  · have hcard : (1 : ℝ) ≤ (binMembers targets distance).card := by
      exact_mod_cast h.1.card_pos
    apply le_trans (div_le_self
      (Finset.sum_nonneg (fun deme _ ↦
        reportValue_nonneg (targetDesign design targets deme) effects outcome)) hcard)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun deme _ _ ↦ reportValue_nonneg (targetDesign design targets deme) effects outcome)
  · exact Finset.sum_nonneg (fun deme _ ↦
      reportValue_nonneg (targetDesign design targets deme) effects outcome)

theorem binInner_le_sum (distance : ℕ) (effects : K → ℝ) :
    binInner design targets distance effects ≤
      ∑ deme : D, innerValue (targetDesign design targets deme) effects := by
  unfold binInner innerValue
  simp only [target_labelKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro outcome _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (binReport_le_sum design targets distance effects outcome)
    ((labelKernel design).weight_nonneg effects outcome)

include certificates in
/-- Covariance certificates for the learned score in every deme discharge
integrability for the actual common-acceptance distance-bin endpoint. -/
theorem certified_bin_integrable (distance : ℕ) :
    Integrable (binInner design targets distance) (effectLaw K) := by
  have hi : Integrable (fun effects ↦
      ∑ deme : D, innerValue (targetDesign design targets deme) effects) (effectLaw K) := by
    apply integrable_finset_sum
    intro deme _
    exact certified_innerValue_integrable (targetDesign design targets deme) (certificates deme)
  apply hi.mono' (binInner_measurable design targets distance).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro effects
  rw [Real.norm_eq_abs, abs_of_nonneg (binInner_nonneg design targets distance effects)]
  exact binInner_le_sum design targets distance effects

include certificates in
theorem certified_bin_extended_finite (distance : ℕ) :
    binExtendedNumerator design targets distance < ∞ :=
  (binInner_integrable_iff design targets distance).mp
    (certified_bin_integrable design targets certificates distance)

include certificates in
theorem certified_bin_expectation (distance : ℕ) :
    PartialMetricMixture.conditionalMetric (jointLaw design)
      (fun pair ↦ binReport design targets distance pair.1 pair.2) =
      if binSuccessProbability design targets distance = 0 then none else
        some ((binExtendedNumerator design targets distance).toReal /
          binSuccessProbability design targets distance) :=
  finite_bin_expectation design targets distance
    (certified_bin_extended_finite design targets certificates distance)

end DistanceBins

end Descent.Portability.PortabilityRatioGeometry
