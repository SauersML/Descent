/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ProbitTrainingLaw

assert_below Descent.Decision Descent.Program

/-!
Real-arithmetic reduction of the simulation's held-out squared correlation.
Global score/liability standardization and within-deme liability centering cancel
from evaluation, including its undefinedness condition. This does not remove
standardization from the training-label probabilities, and makes no claim about
bit-for-bit floating-point equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimulationAccuracy

open FiniteReportLaw TrainingNoiseAccuracy

variable {S J K : Type*} [Fintype S] [Fintype J] [Fintype K]

noncomputable def affine (a b : ℝ) (f : S → ℝ) : S → ℝ := fun s ↦ a * f s + b

theorem expectation_affine (p : FiniteReportLaw S) (a b : ℝ) (f : S → ℝ) :
    p.expectation (affine a b f) = a * p.expectation f + b := by
  unfold expectation affine
  simp only [mul_add, Finset.sum_add_distrib]
  have hsum : (∑ s, p.mass s * (a * f s)) = a * ∑ s, p.mass s * f s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum, ← Finset.sum_mul, p.mass_sum, one_mul]

theorem covariance_affine (p : FiniteReportLaw S) (a b c d : ℝ) (f g : S → ℝ) :
    p.covariance (affine a b f) (affine c d g) = a * c * p.covariance f g := by
  unfold covariance
  rw [expectation_affine, expectation_affine]
  unfold expectation affine
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem variance_affine (p : FiniteReportLaw S) (a b : ℝ) (f : S → ℝ) :
    p.variance (affine a b f) = a ^ 2 * p.variance f := by
  simpa [variance, pow_two] using covariance_affine p a b a b f f

/-- Affine invariance preserves `none` as well as every defined correlation. -/
theorem squaredCorrelation_affine (p : FiniteReportLaw S)
    (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (f g : S → ℝ) :
    p.squaredCorrelation (affine a b f) (affine c d g) =
      p.squaredCorrelation f g := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  unfold squaredCorrelation
  rw [variance_affine, variance_affine, covariance_affine]
  have hfa : 0 < a ^ 2 * p.variance f ↔ 0 < p.variance f :=
    mul_pos_iff_of_pos_left ha2
  have hgc : 0 < c ^ 2 * p.variance g ↔ 0 < p.variance g :=
    mul_pos_iff_of_pos_left hc2
  simp only [hfa, hgc]
  split_ifs
  · congr 1
    field_simp [ha, hc]
  · rfl

noncomputable def standardize (p : FiniteReportLaw S) (epsilon : ℝ) (f : S → ℝ) : S → ℝ :=
  fun s ↦ (f s - p.expectation f) / (Real.sqrt (p.variance f) + epsilon)

/-- The strictly positive regularizer used by the simulation makes the
standardization denominator nonzero even for constant inputs. -/
theorem standardize_eq_affine (p : FiniteReportLaw S) (epsilon : ℝ) (f : S → ℝ) :
    standardize p epsilon f =
      affine (1 / (Real.sqrt (p.variance f) + epsilon))
        (-p.expectation f / (Real.sqrt (p.variance f) + epsilon)) f := by
  funext s
  simp only [standardize, affine]
  ring

/-- Centering and scaling parameters may come from the whole cohort or the fit
cohort; only their being constant on the evaluation cohort is needed. -/
theorem squaredCorrelation_standardized_restriction {U : Type*} [Fintype U]
    (whole : FiniteReportLaw U) (evaluation : FiniteReportLaw S)
    (select : S → U) (epsilon : ℝ) (he : 0 < epsilon) (f g : U → ℝ) :
    evaluation.squaredCorrelation
      (fun s ↦ standardize whole epsilon f (select s))
      (fun s ↦ standardize whole epsilon g (select s)) =
    evaluation.squaredCorrelation (f ∘ select) (g ∘ select) := by
  have hf : Real.sqrt (whole.variance f) + epsilon ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) he)
  have hg : Real.sqrt (whole.variance g) + epsilon ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) he)
  simp only [standardize_eq_affine]
  exact squaredCorrelation_affine evaluation _ _ _ _
    (one_div_ne_zero hf) (one_div_ne_zero hg) (f ∘ select) (g ∘ select)

omit [Fintype S] in
/-- The causal matrix is column-centered before multiplying by the effect
vector. This changes the liability by exactly one cohort-wide constant. -/
theorem linearScore_center_columns (genotype : S → J → ℝ)
    (center weights : J → ℝ) :
    linearScore (fun s j ↦ genotype s j - center j) weights =
      affine 1 (-(∑ j, weights j * center j)) (linearScore genotype weights) := by
  funext s
  simp only [linearScore, affine, mul_sub, Finset.sum_sub_distrib, one_mul]
  ring

/-- Subsequent global standardization cancels column-centering exactly, also
for the training liability. Its scale factor is still retained. -/
theorem standardize_shift (p : FiniteReportLaw S) (epsilon shift : ℝ) (f : S → ℝ) :
    standardize p epsilon (affine 1 shift f) = standardize p epsilon f := by
  funext s
  simp only [standardize, expectation_affine, variance_affine, affine, one_pow, one_mul]
  congr 1
  ring

theorem standardize_linearScore_center_columns (p : FiniteReportLaw S)
    (epsilon : ℝ) (genotype : S → J → ℝ) (center weights : J → ℝ) :
    standardize p epsilon (linearScore (fun s j ↦ genotype s j - center j) weights) =
      standardize p epsilon (linearScore genotype weights) := by
  rw [linearScore_center_columns, standardize_shift]

/-- Evaluation uses two different feature matrices: the PGS's BED dosages and
the causal reservoir's dosages. No equality between those encodings is assumed. -/
noncomputable def crossForm (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ) : ℝ :=
  ∑ j, ∑ k, weights j * effects k *
    p.covariance (fun s ↦ scoreGenotype s j) (fun s ↦ causalGenotype s k)

noncomputable def varianceForm (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (weights : J → ℝ) : ℝ :=
  ∑ j, ∑ k, weights j * weights k *
    p.covariance (fun s ↦ genotype s j) (fun s ↦ genotype s k)

theorem covariance_two_scores (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ) :
    p.covariance (linearScore scoreGenotype weights) (linearScore causalGenotype effects) =
      crossForm p scoreGenotype causalGenotype weights effects := by
  rw [covariance_linearScore]
  unfold crossForm
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_symmetric, covariance_linearScore, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [covariance_symmetric]
  ring

noncomputable def formAccuracy (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ) : Option ℝ :=
  if 0 < varianceForm p scoreGenotype weights ∧ 0 < varianceForm p causalGenotype effects then
    some (crossForm p scoreGenotype causalGenotype weights effects ^ 2 /
      (varianceForm p scoreGenotype weights * varianceForm p causalGenotype effects))
  else none

/-- The exact quadratic-form expression includes degenerate score and trait
configurations instead of assigning an arbitrary numerical accuracy to them. -/
theorem squaredCorrelation_eq_formAccuracy (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ) :
    p.squaredCorrelation (linearScore scoreGenotype weights) (linearScore causalGenotype effects) =
      formAccuracy p scoreGenotype causalGenotype weights effects := by
  simp only [squaredCorrelation, covariance_two_scores, variance_linearScore,
    formAccuracy, varianceForm]

theorem squaredCorrelation_affine_eq_formAccuracy (p : FiniteReportLaw S)
    (scoreGenotype : S → J → ℝ) (causalGenotype : S → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ)
    (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    p.squaredCorrelation (affine a b (linearScore scoreGenotype weights))
      (affine c d (linearScore causalGenotype effects)) =
      formAccuracy p scoreGenotype causalGenotype weights effects := by
  rw [squaredCorrelation_affine p a b c d ha hc, squaredCorrelation_eq_formAccuracy]

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T]

noncomputable def formRatio (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ) : Option ℝ :=
  (formAccuracy source sourceScore sourceCausal weights effects).bind fun sourceR2 ↦
    (formAccuracy target targetScore targetCausal weights effects).bind fun targetR2 ↦
      if 0 < sourceR2 then some (targetR2 / sourceR2) else none

/-- The only source-accuracy denominator is the squared cross form. This is a
pathwise identity on its stated positive-variance domain, not an integrability
claim about resampling the causal effects. -/
theorem formRatio_value (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
    (weights : J → ℝ) (effects : K → ℝ)
    (hss : 0 < varianceForm source sourceScore weights)
    (hsc : 0 < varianceForm source sourceCausal effects)
    (hts : 0 < varianceForm target targetScore weights)
    (htc : 0 < varianceForm target targetCausal effects)
    (hcross : crossForm source sourceScore sourceCausal weights effects ≠ 0) :
    formRatio source target sourceScore targetScore sourceCausal targetCausal weights effects =
      some ((crossForm target targetScore targetCausal weights effects ^ 2 *
        (varianceForm source sourceScore weights * varianceForm source sourceCausal effects)) /
        ((varianceForm target targetScore weights * varianceForm target targetCausal effects) *
          crossForm source sourceScore sourceCausal weights effects ^ 2)) := by
  have hp : 0 < crossForm source sourceScore sourceCausal weights effects ^ 2 /
      (varianceForm source sourceScore weights * varianceForm source sourceCausal effects) :=
    div_pos (sq_pos_of_ne_zero hcross) (mul_pos hss hsc)
  simp only [formRatio, formAccuracy, hss, hsc, hts, htc, and_self, ite_true,
    Option.bind_some, hp]
  congr 1
  field_simp

omit [Fintype I] [DecidableEq I] in
/-- A nonzero scaling or a constant shift of the evaluation liability does not
change the learner. Its label probabilities still use the actual normalized trait. -/
theorem accuracy_affine_liability (p : FiniteReportLaw S)
    (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (outcome : I → Bool)
    (c d : ℝ) (hc : c ≠ 0) :
    accuracy p genotype (affine c d liability) learn outcome =
      accuracy p genotype liability learn outcome := by
  unfold accuracy
  cases h : learn outcome with
  | none => rfl
  | some weights =>
    simp only [Option.bind_some]
    have hid : affine (1 : ℝ) 0 (linearScore genotype weights) =
        linearScore genotype weights := by
      funext s
      simp [affine]
    have hcaf := squaredCorrelation_affine p 1 0 c d one_ne_zero hc
      (linearScore genotype weights) liability
    rw [hid] at hcaf
    exact hcaf

omit [Fintype I] [DecidableEq I] in
/-- Each run's target/source quotient is retained inside the readout; neither
source nor target accuracy is averaged before this division. -/
theorem ratio_eq_formRatio (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
    (effects : K → ℝ) (learn : (I → Bool) → Option (J → ℝ)) (outcome : I → Bool) :
    ratio source target sourceScore targetScore
      (linearScore sourceCausal effects) (linearScore targetCausal effects) learn outcome =
      (learn outcome).bind (fun weights ↦
        formRatio source target sourceScore targetScore
          sourceCausal targetCausal weights effects) := by
  unfold ratio accuracy
  cases h : learn outcome with
  | none => rfl
  | some weights =>
    simp only [Option.bind_some, squaredCorrelation_eq_formAccuracy, formRatio]

omit [Fintype I] [DecidableEq I] in
theorem ratio_affine_eq_formRatio (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
    (effects : K → ℝ) (learn : (I → Bool) → Option (J → ℝ)) (outcome : I → Bool)
    (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    ratio source target sourceScore targetScore
      (affine a b (linearScore sourceCausal effects))
      (affine c d (linearScore targetCausal effects)) learn outcome =
      (learn outcome).bind (fun weights ↦
        formRatio source target sourceScore targetScore
          sourceCausal targetCausal weights effects) := by
  have h : ratio source target sourceScore targetScore
      (affine a b (linearScore sourceCausal effects))
      (affine c d (linearScore targetCausal effects)) learn outcome =
      ratio source target sourceScore targetScore
        (linearScore sourceCausal effects) (linearScore targetCausal effects) learn outcome := by
    unfold ratio
    rw [accuracy_affine_liability source _ _ learn outcome a b ha,
      accuracy_affine_liability target _ _ learn outcome c d hc]
  rw [h, ratio_eq_formRatio]

/-- Exact elimination of Gaussian environmental noise for the actual per-run
ratio form, conditional on the genotypes, causal effects, split, and learner.
The means retain the simulator's global normalization and calibrated intercept.
Genetic/effect averaging and the executable P+T learner remain separate obligations. -/
theorem reportedRatio_eq_form_sum (mean : I → ℝ) (noiseVariance : I → NNReal)
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
    (effects : K → ℝ) (learn : (I → Bool) → Option (J → ℝ))
    (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    ProbitTrainingLaw.reportedExpectation mean noiseVariance
      (ratio source target sourceScore targetScore
        (affine a b (linearScore sourceCausal effects))
        (affine c d (linearScore targetCausal effects)) learn) =
      conditionalExpectation
        (fun i ↦ ProbitTrainingLaw.caseProbability (mean i) (noiseVariance i))
        (fun outcome ↦ (learn outcome).bind (fun weights ↦
          formRatio source target sourceScore targetScore
            sourceCausal targetCausal weights effects)) := by
  rw [ProbitTrainingLaw.reportedExpectation_eq_finite_sum]
  congr 1
  funext outcome
  exact ratio_affine_eq_formRatio source target sourceScore targetScore
    sourceCausal targetCausal effects learn outcome a b c d ha hc

end Descent.Portability.SimulationAccuracy
