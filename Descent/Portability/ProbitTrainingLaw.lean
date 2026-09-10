/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ScoreMomentLaw
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

assert_below Descent.Decision Descent.Program

/-!
Exact integration of independent Gaussian threshold noise for a finite
label-dependent learner, conditional on fixed genetic data and liabilities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ProbitTrainingLaw

open MeasureTheory ProbabilityTheory TrainingNoiseAccuracy
open scoped NNReal

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def caseProbability (mean : ℝ) (variance : ℝ≥0) : ℝ :=
  (gaussianReal mean variance).real (Set.Ioi 0)

theorem caseProbability_bounds (mean : ℝ) (variance : ℝ≥0) :
    0 ≤ caseProbability mean variance ∧ caseProbability mean variance ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

noncomputable def labels (liabilities : I → ℝ) : I → Bool :=
  fun i ↦ decide (0 < liabilities i)

noncomputable def environmentLaw (mean : I → ℝ) (variance : I → ℝ≥0) : Measure (I → ℝ) :=
  Measure.pi fun i ↦ gaussianReal (mean i) (variance i)

instance environmentLaw_probability (mean : I → ℝ) (variance : I → ℝ≥0) :
    IsProbabilityMeasure (environmentLaw mean variance) := by
  unfold environmentLaw
  infer_instance

noncomputable def outcomeLaw (mean : I → ℝ) (variance : I → ℝ≥0) :
    FiniteReportLaw (I → Bool) :=
  labelLaw (fun i ↦ caseProbability (mean i) (variance i))
    (fun i ↦ caseProbability_bounds (mean i) (variance i))

omit [Fintype I] [DecidableEq I] in
theorem labelEvent_eq_pi (outcome : I → Bool) :
    {x : I → ℝ | labels x = outcome} =
      Set.pi Set.univ (fun i ↦ if outcome i then Set.Ioi 0 else Set.Iic 0) := by
  ext x
  simp only [Set.mem_setOf_eq, funext_iff, Set.mem_pi, Set.mem_univ, true_implies]
  apply forall_congr'
  intro i
  cases outcome i <;> simp [labels]

theorem gaussian_controlProbability (mean : ℝ) (variance : ℝ≥0) :
    (gaussianReal mean variance).real (Set.Iic 0) = 1 - caseProbability mean variance := by
  simpa [caseProbability] using
    (measureReal_compl (μ := gaussianReal mean variance) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi)

/-- The finite label probabilities are derived from thresholding the product
Gaussian measure, rather than assumed as a supplied outcome kernel. -/
theorem threshold_probability (mean : I → ℝ) (variance : I → ℝ≥0)
    (outcome : I → Bool) :
    (environmentLaw mean variance).real {x | labels x = outcome} =
      (outcomeLaw mean variance).mass outcome := by
  rw [labelEvent_eq_pi]
  unfold environmentLaw Measure.real
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ i, (gaussianReal (mean i) (variance i)).real
      (if outcome i then Set.Ioi 0 else Set.Iic 0)) =
    ∏ i, if outcome i then caseProbability (mean i) (variance i)
      else 1 - caseProbability (mean i) (variance i)
  apply Finset.prod_congr rfl
  intro i _
  cases outcome i
  · exact gaussian_controlProbability _ _
  · rfl

theorem threshold_probabilities_sum_one (mean : I → ℝ) (variance : I → ℝ≥0) :
    (∑ outcome : I → Bool,
      (environmentLaw mean variance).real {x | labels x = outcome}) = 1 := by
  simp_rw [threshold_probability]
  exact (outcomeLaw mean variance).mass_sum

omit [DecidableEq I] in
theorem labelEvent_measurable (outcome : I → Bool) :
    MeasurableSet {x : I → ℝ | labels x = outcome} := by
  rw [labelEvent_eq_pi]
  apply MeasurableSet.pi (Set.toFinite Set.univ).countable
  intro i _
  cases outcome i <;> simp

/-- Exact integration over the Gaussian environmental draws, allowing the
entire score-selection and evaluation routine to depend on their binary labels. -/
theorem integral_readout (mean : I → ℝ) (variance : I → ℝ≥0)
    (readout : (I → Bool) → ℝ) :
    (∫ x, readout (labels x) ∂environmentLaw mean variance) =
      (outcomeLaw mean variance).expectation readout := by
  classical
  let μ := environmentLaw mean variance
  have hpoint (x : I → ℝ) :
      (∑ outcome : I → Bool,
        Set.indicator {z | labels z = outcome} (fun _ ↦ readout outcome) x) =
      readout (labels x) := by
    simp [Set.indicator, Set.mem_setOf_eq]
  have hint (outcome : I → Bool) :
      Integrable (Set.indicator {x | labels x = outcome} (fun _ ↦ readout outcome)) μ :=
    (integrable_const _).indicator (labelEvent_measurable outcome)
  calc
    (∫ x, readout (labels x) ∂μ) =
        ∫ x, ∑ outcome : I → Bool,
          Set.indicator {z | labels z = outcome} (fun _ ↦ readout outcome) x ∂μ := by
      congr 1
      funext x
      exact (hpoint x).symm
    _ = ∑ outcome : I → Bool,
        ∫ x, Set.indicator {z | labels z = outcome} (fun _ ↦ readout outcome) x ∂μ := by
      exact integral_finset_sum _ (fun outcome _ ↦ hint outcome)
    _ = ∑ outcome : I → Bool,
        μ.real {x | labels x = outcome} * readout outcome := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [integral_indicator_const _ (labelEvent_measurable outcome), smul_eq_mul]
    _ = (outcomeLaw mean variance).expectation readout := by
      simp only [μ, threshold_probability, FiniteReportLaw.expectation]

noncomputable def reportedExpectation (mean : I → ℝ) (variance : I → ℝ≥0)
    (readout : (I → Bool) → Option ℝ) : Option ℝ :=
  let probability := ∫ x, (if (readout (labels x)).isSome then (1 : ℝ) else 0)
    ∂environmentLaw mean variance
  if probability = 0 then none
  else some ((∫ x, (readout (labels x)).getD 0 ∂environmentLaw mean variance) / probability)

/-- Both numerator and reporting probability are integrated before normalization.
This theorem includes label-dependent selection and undefined evaluations. -/
theorem reportedExpectation_eq_finite_sum (mean : I → ℝ) (variance : I → ℝ≥0)
    (readout : (I → Bool) → Option ℝ) :
    reportedExpectation mean variance readout =
      conditionalExpectation (fun i ↦ caseProbability (mean i) (variance i)) readout := by
  unfold reportedExpectation
  rw [integral_readout mean variance (fun outcome ↦ if (readout outcome).isSome then 1 else 0),
    integral_readout mean variance (fun outcome ↦ (readout outcome).getD 0)]
  rfl

/-- Gaussian label noise integrated exactly, with the learned score evaluated
through the cohort's genotype covariance matrix and trait covariance vector. -/
theorem reportedAccuracy_eq_moment_sum {S J : Type*} [Fintype S] [Fintype J]
    (mean : I → ℝ) (variance : I → ℝ≥0)
    (evaluation : FiniteReportLaw S) (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) :
    reportedExpectation mean variance (accuracy evaluation genotype liability learn) =
      conditionalExpectation (fun i ↦ caseProbability (mean i) (variance i))
        (fun outcome ↦ (learn outcome).bind fun weights ↦
          let scoreVariance := ∑ j, ∑ k, weights j * weights k *
            evaluation.covariance (fun s ↦ genotype s j) (fun s ↦ genotype s k)
          if 0 < scoreVariance ∧ 0 < evaluation.variance liability then
            some ((∑ j, weights j *
              evaluation.covariance (fun s ↦ genotype s j) liability) ^ 2 /
              (scoreVariance * evaluation.variance liability))
          else none) := by
  rw [reportedExpectation_eq_finite_sum]
  apply congrArg (conditionalExpectation (fun i ↦ caseProbability (mean i) (variance i)))
  funext outcome
  simp only [accuracy, FiniteReportLaw.squaredCorrelation,
    covariance_linearScore, variance_linearScore]

theorem reportedAccuracy_bounds {S J : Type*} [Fintype S] [Fintype J]
    (mean : I → ℝ) (variance : I → ℝ≥0)
    (evaluation : FiniteReportLaw S) (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) {r : ℝ}
    (hr : reportedExpectation mean variance
      (accuracy evaluation genotype liability learn) = some r) :
    0 ≤ r ∧ r ≤ 1 := by
  rw [reportedExpectation_eq_finite_sum] at hr
  exact conditionalAccuracy_mem_unitInterval _
    (fun i ↦ caseProbability_bounds (mean i) (variance i)) evaluation genotype liability learn hr

theorem reportedRatio_bounds {S T J : Type*} [Fintype S] [Fintype T] [Fintype J]
    (mean : I → ℝ) (variance : I → ℝ≥0)
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceGenotype : S → J → ℝ) (targetGenotype : T → J → ℝ)
    (sourceLiability : S → ℝ) (targetLiability : T → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (floor : ℝ) (hf : 0 < floor)
    (hfloor : ∀ outcome value,
      accuracy source sourceGenotype sourceLiability learn outcome = some value →
      0 < value → floor ≤ value)
    {r : ℝ} (hr : reportedExpectation mean variance
      (ratio source target sourceGenotype targetGenotype sourceLiability targetLiability learn) =
      some r) : 0 ≤ r ∧ r ≤ 1 / floor := by
  rw [reportedExpectation_eq_finite_sum] at hr
  exact conditionalRatio_bounds _
    (fun i ↦ caseProbability_bounds (mean i) (variance i)) source target
    sourceGenotype targetGenotype sourceLiability targetLiability learn floor hf hfloor hr

theorem reportedSourceRatio_eq_one {S J : Type*} [Fintype S] [Fintype J]
    (mean : I → ℝ) (variance : I → ℝ≥0)
    (source : FiniteReportLaw S) (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ))
    (hd : definedProbability (fun i ↦ caseProbability (mean i) (variance i))
      (ratio source source genotype genotype liability liability learn) ≠ 0) :
    reportedExpectation mean variance
      (ratio source source genotype genotype liability liability learn) = some 1 := by
  rw [reportedExpectation_eq_finite_sum]
  exact conditionalSourceRatio_eq_one _ source genotype liability learn hd

/-- The bound is finite and uniform over the environmental means and variances
for this fixed learner and genetic data. It is not asserted uniform over genetic
resampling or over demographic inputs. -/
theorem fixedData_reportedRatio_bounded {S T J : Type*}
    [Fintype S] [Fintype T] [Fintype J]
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceGenotype : S → J → ℝ) (targetGenotype : T → J → ℝ)
    (sourceLiability : S → ℝ) (targetLiability : T → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (mean : I → ℝ) (variance : I → ℝ≥0) (r : ℝ),
      reportedExpectation mean variance
        (ratio source target sourceGenotype targetGenotype sourceLiability targetLiability learn) =
        some r → 0 ≤ r ∧ r ≤ bound := by
  obtain ⟨δ, hδ, hfloor⟩ := positive_source_floor source sourceGenotype sourceLiability learn
  refine ⟨1 / δ, one_div_pos.mpr hδ, ?_⟩
  intro mean variance r hr
  exact reportedRatio_bounds mean variance source target sourceGenotype targetGenotype
    sourceLiability targetLiability learn δ hδ hfloor hr

end Descent.Portability.ProbitTrainingLaw
