/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw
import Descent.Portability.EmpiricalAUCComparison

assert_below Descent.Decision Descent.Program

namespace Descent.Portability.FiniteReportLaw

/-!
# Exact finite-law metric evaluation and conditional marginalization

An explicitly supplied finite joint law determines moment metrics and binary AUC exactly.
Undefined correlations, slopes, and AUCs remain `none`. Most importantly, when upstream and
downstream randomness are composed, a skip-undefined average is the ratio of the combined
weighted numerator to the combined definedness probability. Averaging the inner conditional
means computes a different quantity. The normalization theorem below derives the correct
composition from the finite probability law and exhibits a strict numerical separation.

These are exact finite-model identities. Constructing the biologically appropriate law,
or an exact discretization of a continuous model, is a separate obligation.
-/

variable {State Next : Type*} [Fintype State] [Fintype Next]

private theorem expectation_add_same (p : FiniteReportLaw State) (f g : State → ℝ) :
    p.expectation (fun s ↦ f s + g s) = p.expectation f + p.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

private theorem expectation_sub_same (p : FiniteReportLaw State) (f g : State → ℝ) :
    p.expectation (fun s ↦ f s - g s) = p.expectation f - p.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

private theorem expectation_mul_constant (p : FiniteReportLaw State)
    (f : State → ℝ) (c : ℝ) :
    p.expectation (fun s ↦ f s * c) = p.expectation f * c := by
  simp [expectation, Finset.sum_mul, mul_assoc]

private theorem expectation_constant (p : FiniteReportLaw State) (c : ℝ) :
    p.expectation (fun _ ↦ c) = c := by
  simp only [expectation, ← Finset.sum_mul, p.mass_sum, one_mul]

/-- Covariance under the complete finite score/outcome law. -/
noncomputable def covariance (p : FiniteReportLaw State) (score outcome : State → ℝ) : ℝ :=
  p.expectation fun s ↦
    (score s - p.expectation score) * (outcome s - p.expectation outcome)

/-- Variance under the same finite law. -/
noncomputable def variance (p : FiniteReportLaw State) (score : State → ℝ) : ℝ :=
  p.covariance score score

theorem covariance_eq_rawMoments (p : FiniteReportLaw State) (score outcome : State → ℝ) :
    p.covariance score outcome =
      p.expectation (fun s ↦ score s * outcome s) -
        p.expectation score * p.expectation outcome := by
  calc
    p.covariance score outcome = p.expectation (fun s ↦
        score s * outcome s - score s * p.expectation outcome -
          outcome s * p.expectation score + p.expectation score * p.expectation outcome) := by
      unfold covariance
      congr 1
      funext s
      ring
    _ = _ := by
      rw [expectation_add_same, expectation_sub_same, expectation_sub_same,
        expectation_mul_constant, expectation_mul_constant, expectation_constant]
      ring

theorem variance_eq_rawMoments (p : FiniteReportLaw State) (score : State → ℝ) :
    p.variance score = p.expectation (fun s ↦ score s ^ 2) - (p.expectation score) ^ 2 := by
  simpa [variance, pow_two] using p.covariance_eq_rawMoments score score

theorem variance_nonneg (p : FiniteReportLaw State) (score : State → ℝ) :
    0 ≤ p.variance score := by
  unfold variance covariance expectation
  exact Finset.sum_nonneg fun s _ ↦
    mul_nonneg (p.mass_nonneg s) (mul_self_nonneg _)

theorem covariance_sq_le_variance_mul (p : FiniteReportLaw State)
    (score outcome : State → ℝ) :
    p.covariance score outcome ^ 2 ≤ p.variance score * p.variance outcome := by
  let f := fun s ↦ Real.sqrt (p.mass s) * (score s - p.expectation score)
  let g := fun s ↦ Real.sqrt (p.mass s) * (outcome s - p.expectation outcome)
  have hcov : (∑ s, f s * g s) = p.covariance score outcome := by
    unfold covariance expectation
    apply Finset.sum_congr rfl
    intro s _
    dsimp [f, g]
    unfold expectation
    rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt (p.mass_nonneg s)]
  have hf : (∑ s, f s ^ 2) = p.variance score := by
    unfold variance covariance expectation
    apply Finset.sum_congr rfl
    intro s _
    dsimp [f]
    unfold expectation
    rw [mul_pow, Real.sq_sqrt (p.mass_nonneg s)]
    ring
  have hg : (∑ s, g s ^ 2) = p.variance outcome := by
    unfold variance covariance expectation
    apply Finset.sum_congr rfl
    intro s _
    dsimp [g]
    unfold expectation
    rw [mul_pow, Real.sq_sqrt (p.mass_nonneg s)]
    ring
  simpa only [hcov, hf, hg] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

/-- Exact squared Pearson correlation, defined precisely when both variances are positive. -/
noncomputable def squaredCorrelation (p : FiniteReportLaw State)
    (score outcome : State → ℝ) : Option ℝ :=
  if 0 < p.variance score ∧ 0 < p.variance outcome then
    some (p.covariance score outcome ^ 2 / (p.variance score * p.variance outcome))
  else none

theorem squaredCorrelation_mem_unitInterval (p : FiniteReportLaw State)
    (score outcome : State → ℝ) {r : ℝ}
    (hr : p.squaredCorrelation score outcome = some r) : 0 ≤ r ∧ r ≤ 1 := by
  unfold squaredCorrelation at hr
  split_ifs at hr with h
  · have heq := Option.some.inj hr
    rw [← heq]
    have hden := mul_pos h.1 h.2
    exact ⟨div_nonneg (sq_nonneg _) hden.le,
      (div_le_one hden).mpr (p.covariance_sq_le_variance_mul score outcome)⟩

theorem squaredCorrelation_eq_rawMoments (p : FiniteReportLaw State)
    (score outcome : State → ℝ)
    (hscore : 0 < p.expectation (fun s ↦ score s ^ 2) - (p.expectation score) ^ 2)
    (houtcome : 0 < p.expectation (fun s ↦ outcome s ^ 2) - (p.expectation outcome) ^ 2) :
    p.squaredCorrelation score outcome = some
      ((p.expectation (fun s ↦ score s * outcome s) -
          p.expectation score * p.expectation outcome) ^ 2 /
        ((p.expectation (fun s ↦ score s ^ 2) - (p.expectation score) ^ 2) *
          (p.expectation (fun s ↦ outcome s ^ 2) - (p.expectation outcome) ^ 2))) := by
  simp [squaredCorrelation, variance_eq_rawMoments, covariance_eq_rawMoments, hscore, houtcome]

/-- Exact least-squares slope, with its nonconstant-score domain explicit. -/
noncomputable def calibrationSlope (p : FiniteReportLaw State)
    (score outcome : State → ℝ) : Option ℝ :=
  if 0 < p.variance score then some (p.covariance score outcome / p.variance score) else none

theorem calibrationSlope_eq_rawMoments (p : FiniteReportLaw State)
    (score outcome : State → ℝ)
    (hscore : 0 < p.expectation (fun s ↦ score s ^ 2) - (p.expectation score) ^ 2) :
    p.calibrationSlope score outcome = some
      ((p.expectation (fun s ↦ score s * outcome s) -
          p.expectation score * p.expectation outcome) /
        (p.expectation (fun s ↦ score s ^ 2) - (p.expectation score) ^ 2)) := by
  simp [calibrationSlope, variance_eq_rawMoments, covariance_eq_rawMoments, hscore]

/-- Exact raw mean squared prediction error; for binary outcomes this is Brier loss. -/
noncomputable def meanSquaredError (p : FiniteReportLaw State)
    (prediction outcome : State → ℝ) : ℝ :=
  p.expectation fun s ↦ (prediction s - outcome s) ^ 2

theorem meanSquaredError_eq_rawMoments (p : FiniteReportLaw State)
    (prediction outcome : State → ℝ) :
    p.meanSquaredError prediction outcome =
      p.expectation (fun s ↦ prediction s ^ 2) + p.expectation (fun s ↦ outcome s ^ 2) -
        2 * p.expectation (fun s ↦ prediction s * outcome s) := by
  calc
    p.meanSquaredError prediction outcome = p.expectation (fun s ↦
        prediction s ^ 2 + outcome s ^ 2 - (prediction s * outcome s) * 2) := by
      unfold meanSquaredError
      congr 1
      funext s
      ring
    _ = _ := by
      rw [expectation_sub_same, expectation_add_same, expectation_mul_constant]
      ring

/-- Probability of a case in the supplied population law. -/
noncomputable def binaryCaseMass (p : FiniteReportLaw State) (outcome : State → Bool) : ℝ :=
  p.expectation fun s ↦ if outcome s then 1 else 0

/-- Independent case-control comparison before conditioning on either outcome class. -/
noncomputable def binaryAUCNumerator (p : FiniteReportLaw State)
    (score : State → ℝ) (outcome : State → Bool) : ℝ :=
  p.expectation fun caseState ↦ p.expectation fun controlState ↦
    if outcome caseState && !outcome controlState then
      empiricalAUCComparison (score caseState) (score controlState) else 0

/-- Exact population binary AUC, including half-credit ties and explicit class-definedness. -/
noncomputable def binaryAUC (p : FiniteReportLaw State)
    (score : State → ℝ) (outcome : State → Bool) : Option ℝ :=
  let cases := p.binaryCaseMass outcome
  if 0 < cases ∧ cases < 1 then
    some (p.binaryAUCNumerator score outcome / (cases * (1 - cases))) else none

theorem binaryAUC_eq_double_sum (p : FiniteReportLaw State)
    (score : State → ℝ) (outcome : State → Bool)
    (hcases : 0 < p.binaryCaseMass outcome) (hcontrols : p.binaryCaseMass outcome < 1) :
    p.binaryAUC score outcome = some
      ((∑ c, ∑ t, p.mass c * p.mass t *
          (if outcome c && !outcome t then empiricalAUCComparison (score c) (score t) else 0)) /
        (p.binaryCaseMass outcome * (1 - p.binaryCaseMass outcome))) := by
  simp only [binaryAUC, hcases, hcontrols, and_self, if_true]
  congr 2
  simp [binaryAUCNumerator, expectation, Finset.mul_sum, mul_assoc]

/-- Probability that a partial metric is defined. -/
noncomputable def definedMass (p : FiniteReportLaw State) (metric : State → Option ℝ) : ℝ :=
  p.expectation fun s ↦ if (metric s).isSome then 1 else 0

/-- Unnormalized metric integral. Undefined states contribute no mass to this numerator. -/
noncomputable def weightedDefinedMetric (p : FiniteReportLaw State)
    (metric : State → Option ℝ) : ℝ :=
  p.expectation fun s ↦ (metric s).getD 0

/-- Exact skip-undefined average. Zero definedness probability produces `none`. -/
noncomputable def conditionalMetric (p : FiniteReportLaw State)
    (metric : State → Option ℝ) : Option ℝ :=
  if p.definedMass metric = 0 then none
  else some (p.weightedDefinedMetric metric / p.definedMass metric)

theorem definedMass_joint (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) (metric : State × Next → Option ℝ) :
    (p.joint kernel).definedMass metric =
      p.expectation (fun state ↦ (kernel state).definedMass (fun next ↦ metric (state, next))) := by
  exact expectation_joint p kernel (fun pair ↦ if (metric pair).isSome then 1 else 0)

theorem weightedDefinedMetric_joint (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) (metric : State × Next → Option ℝ) :
    (p.joint kernel).weightedDefinedMetric metric =
      p.expectation (fun state ↦
        (kernel state).weightedDefinedMetric (fun next ↦ metric (state, next))) := by
  exact expectation_joint p kernel (fun pair ↦ (metric pair).getD 0)

/-- Exact nested marginalization: aggregate inner numerators and definedness masses, then
divide once. This handles arbitrary dependence of metric-definedness on the upstream state. -/
theorem conditionalMetric_joint (p : FiniteReportLaw State)
    (kernel : State → FiniteReportLaw Next) (metric : State × Next → Option ℝ) :
    (p.joint kernel).conditionalMetric metric =
      let mass := p.expectation (fun state ↦
        (kernel state).definedMass (fun next ↦ metric (state, next)))
      if mass = 0 then none else some
        (p.expectation (fun state ↦
          (kernel state).weightedDefinedMetric (fun next ↦ metric (state, next))) / mass) := by
  simp only [conditionalMetric, definedMass_joint, weightedDefinedMetric_joint]

namespace ConditionalWitness

noncomputable def outerLaw : FiniteReportLaw (Fin 2) where
  mass := fun _ ↦ 1 / 2
  mass_nonneg := fun _ ↦ by norm_num
  mass_sum := by norm_num [Fin.sum_univ_two]

noncomputable def innerLaw (state : Fin 2) : FiniteReportLaw (Fin 2) where
  mass := ![if state = 0 then 1 / 4 else 3 / 4, if state = 0 then 3 / 4 else 1 / 4]
  mass_nonneg := by
    intro next
    fin_cases state <;> fin_cases next <;> norm_num
  mass_sum := by fin_cases state <;> norm_num [Fin.sum_univ_two]

noncomputable def metric (state : Fin 2 × Fin 2) : Option ℝ :=
  if state.2 = 0 then some (if state.1 = 0 then 0 else 1) else none

theorem exact_joint_conditionalMetric :
    (outerLaw.joint innerLaw).conditionalMetric metric = some (3 / 4) := by
  rw [conditionalMetric_joint]
  norm_num [outerLaw, innerLaw, metric, definedMass, weightedDefinedMetric,
    expectation, Fin.sum_univ_two]

theorem mean_of_inner_conditionalMetrics :
    outerLaw.expectation (fun state ↦
      ((innerLaw state).conditionalMetric (fun next ↦ metric (state, next))).getD 0) = 1 / 2 := by
  norm_num [outerLaw, innerLaw, metric, conditionalMetric, definedMass,
    weightedDefinedMetric, expectation, Fin.sum_univ_two]

/-- The tempting average of inner conditional means disagrees with the exact joint answer. -/
theorem averaging_inner_conditionalMetrics_is_wrong :
    (outerLaw.joint innerLaw).conditionalMetric metric ≠ some
      (outerLaw.expectation (fun state ↦
        ((innerLaw state).conditionalMetric (fun next ↦ metric (state, next))).getD 0)) := by
  rw [exact_joint_conditionalMetric, mean_of_inner_conditionalMetrics]
  norm_num

end ConditionalWitness

end Descent.Portability.FiniteReportLaw
