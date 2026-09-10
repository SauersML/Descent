/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianSlabLaw

assert_below Descent.Decision Descent.Program

/-!
The source covariance kernel distinguishes genuine nonaligned poles from
rank-one cancellation. The kernel condition is intrinsic to the realized finite
covariance forms. It is not inferred from failure of an upper-bound certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RatioSourceDegeneracy

open FiniteReportLaw TrainingNoiseAccuracy SimulationAccuracy PortabilityRatioGeometry
open RatioPoleLaw GaussianSlabLaw GaussianEffectPortabilityLaw MeasureTheory Filter Topology
open scoped ENNReal

variable {S T J K : Type*} [Fintype S] [Fintype T] [Fintype J] [Fintype K]

omit [Fintype T] in
theorem form_cauchy (p : FiniteReportLaw S)
    (score : S → J → ℝ) (causal : S → K → ℝ) (weights : J → ℝ) (effects : K → ℝ) :
    crossForm p score causal weights effects ^ 2 ≤
      varianceForm p score weights * varianceForm p causal effects := by
  simpa only [covariance_two_scores, variance_linearScore, varianceForm] using
    p.covariance_sq_le_variance_mul (linearScore score weights) (linearScore causal effects)

omit [Fintype T] in
theorem trait_variance_pos_of_cross_ne (p : FiniteReportLaw S)
    (score : S → J → ℝ) (causal : S → K → ℝ) (weights : J → ℝ) (effects : K → ℝ)
    (hc : crossForm p score causal weights effects ≠ 0) :
    0 < varianceForm p causal effects := by
  have hmul : 0 < varianceForm p score weights * varianceForm p causal effects :=
    (sq_pos_of_ne_zero hc).trans_le (form_cauchy p score causal weights effects)
  exact pos_of_mul_pos_right hmul (varianceForm_nonneg p score weights)

omit [Fintype T] [Fintype J] in
theorem traitCross_symmetric (p : FiniteReportLaw S) (causal : S → K → ℝ) (x y : K → ℝ) :
    crossForm p causal causal x y = crossForm p causal causal y x := by
  rw [← covariance_two_scores, covariance_symmetric, covariance_two_scores]

omit [Fintype T] [Fintype J] in
theorem traitCross_affine_left (p : FiniteReportLaw S) (causal : S → K → ℝ)
    (x direction y : K → ℝ) (t : ℝ) :
    crossForm p causal causal (fun k ↦ x k + t * direction k) y =
      crossForm p causal causal x y + t * crossForm p causal causal direction y := by
  rw [traitCross_symmetric, crossForm_affine_line]
  rw [traitCross_symmetric p causal y x, traitCross_symmetric p causal y direction]

omit [Fintype T] [Fintype J] in
theorem traitCross_zero_of_variance_zero (p : FiniteReportLaw S) (causal : S → K → ℝ)
    (x y : K → ℝ) (hx : varianceForm p causal x = 0) :
    crossForm p causal causal x y = 0 := by
  have hc := form_cauchy p causal causal x y
  rw [hx, zero_mul] at hc
  nlinarith [sq_nonneg (crossForm p causal causal x y)]

/-- Every direction invisible to source score/trait covariance also has zero
source trait variance. With a nonzero cross vector this is the rank-one case. -/
def SourceKernelDegenerate (p : FiniteReportLaw S)
    (score : S → J → ℝ) (causal : S → K → ℝ) (weights : J → ℝ) : Prop :=
  ∀ effects, crossForm p score causal weights effects = 0 → varianceForm p causal effects = 0

omit [Fintype T] in
/-- The kernel condition forces an exact rank-one factorization of the source
trait quadratic form; no factorization is supplied as an assumption. -/
theorem kernel_factorization (p : FiniteReportLaw S)
    (score : S → J → ℝ) (causal : S → K → ℝ) (weights : J → ℝ)
    (hkernel : SourceKernelDegenerate p score causal weights)
    (direction : K → ℝ) (hd : crossForm p score causal weights direction ≠ 0)
    (effects : K → ℝ) :
    varianceForm p causal effects =
      (varianceForm p causal direction / crossForm p score causal weights direction ^ 2) *
        crossForm p score causal weights effects ^ 2 := by
  let t := crossForm p score causal weights effects / crossForm p score causal weights direction
  let residual := fun k ↦ effects k + (-t) * direction k
  have hresCross : crossForm p score causal weights residual = 0 := by
    rw [crossForm_affine_line p score causal weights]
    dsimp [t]
    field_simp
    ring
  have hresVariance := hkernel residual hresCross
  have hresEffects := traitCross_zero_of_variance_zero p causal residual effects hresVariance
  have hresDirection := traitCross_zero_of_variance_zero p causal residual direction hresVariance
  rw [traitCross_affine_left p causal effects direction effects] at hresEffects
  rw [traitCross_affine_left p causal effects direction direction] at hresDirection
  rw [traitCross_symmetric p causal direction effects] at hresEffects
  have hself (x : K → ℝ) : crossForm p causal causal x x = varianceForm p causal x := rfl
  rw [hself] at hresEffects hresDirection
  have hquadratic : varianceForm p causal effects = t ^ 2 * varianceForm p causal direction := by
    have hct : crossForm p causal causal effects direction =
        t * varianceForm p causal direction := by linarith [hresDirection]
    rw [hct] at hresEffects
    nlinarith [hresEffects]
  rw [hquadratic]
  dsimp [t]
  field_simp

omit [Fintype T] in
/-- For a nonzero source cross vector, the intrinsic kernel condition is
equivalent to a positive rank-one factorization, including every effect vector. -/
theorem kernel_iff_positive_factorization (p : FiniteReportLaw S)
    (score : S → J → ℝ) (causal : S → K → ℝ) (weights : J → ℝ)
    (hnontrivial : ∃ direction, crossForm p score causal weights direction ≠ 0) :
    SourceKernelDegenerate p score causal weights ↔
      ∃ factor : ℝ, 0 < factor ∧ ∀ effects, varianceForm p causal effects =
        factor * crossForm p score causal weights effects ^ 2 := by
  constructor
  · intro hkernel
    obtain ⟨direction, hd⟩ := hnontrivial
    refine ⟨varianceForm p causal direction / crossForm p score causal weights direction ^ 2,
      div_pos (trait_variance_pos_of_cross_ne p score causal weights direction hd)
        (sq_pos_of_ne_zero hd), ?_⟩
    exact kernel_factorization p score causal weights hkernel direction hd
  · rintro ⟨factor, _, hfactor⟩ effects hcross
    rw [hfactor, hcross, zero_pow (by norm_num), mul_zero]

omit [Fintype T] in
/-- The rank-one case has a constant positive source accuracy wherever its
source cross form is nonzero, even if the target cross vector is not aligned. -/
theorem source_accuracy_constant (p : FiniteReportLaw S)
    (score : S → J → ℝ) (causal : S → K → ℝ) (weights : J → ℝ)
    (factor : ℝ) (hf : 0 < factor)
    (hfactor : ∀ effects, varianceForm p causal effects =
      factor * crossForm p score causal weights effects ^ 2)
    (hs : 0 < varianceForm p score weights) (effects : K → ℝ)
    (hc : crossForm p score causal weights effects ≠ 0) :
    formAccuracy p score causal weights effects =
      some (1 / (varianceForm p score weights * factor)) := by
  have hv : 0 < varianceForm p causal effects := by
    rw [hfactor]
    exact mul_pos hf (sq_pos_of_ne_zero hc)
  rw [formAccuracy, if_pos ⟨hs, hv⟩, hfactor]
  congr 1
  field_simp

/-- Source rank-one cancellation gives a uniform ratio bound without any target
alignment or target/source trait-variance domination hypothesis. -/
theorem factorized_ratio_bounds
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (factor : ℝ) (hf : 0 < factor)
    (hfactor : ∀ effects, varianceForm source sourceCausal effects =
      factor * crossForm source sourceScore sourceCausal weights effects ^ 2)
    (effects : K → ℝ) :
    0 ≤ (formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects).getD 0 ∧
    (formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects).getD 0 ≤ factor * varianceForm source sourceScore weights := by
  cases h : formRatio source target sourceScore targetScore sourceCausal targetCausal
      weights effects with
  | none =>
    exact ⟨le_rfl, mul_nonneg hf.le (varianceForm_nonneg source sourceScore weights)⟩
  | some value =>
    obtain ⟨hss, hsc, hts, htc, hc⟩ := formRatio_some_domain source target sourceScore targetScore
      sourceCausal targetCausal weights effects value h
    have hv := formRatio_value source target sourceScore targetScore sourceCausal targetCausal
      weights effects hss hsc hts htc hc
    rw [h, hfactor] at hv
    have hvalue : value = factor * varianceForm source sourceScore weights *
        (crossForm target targetScore targetCausal weights effects ^ 2 /
          (varianceForm target targetScore weights *
            varianceForm target targetCausal effects)) := by
      rw [Option.some.inj hv]
      field_simp
    have htarget : crossForm target targetScore targetCausal weights effects ^ 2 /
        (varianceForm target targetScore weights * varianceForm target targetCausal effects) ≤ 1 :=
      (div_le_one (mul_pos hts htc)).mpr
        (form_cauchy target targetScore targetCausal weights effects)
    simp only [Option.getD_some, hvalue]
    refine ⟨by positivity, ?_⟩
    exact (mul_le_mul_of_nonneg_left htarget (mul_nonneg hf.le hss.le)).trans_eq (mul_one _)

/-- The kernel-degenerate case is integrable under every finite effect measure,
including Gaussian effects. This conclusion does not require covariance alignment. -/
theorem kernel_ratio_integrable
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (hkernel : SourceKernelDegenerate source sourceScore sourceCausal weights)
    (hnontrivial : ∃ direction, crossForm source sourceScore sourceCausal weights direction ≠ 0)
    (μ : Measure (K → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun effects ↦ (formRatio source target sourceScore targetScore sourceCausal
      targetCausal weights effects).getD 0) μ := by
  obtain ⟨factor, hf, hfactor⟩ := (kernel_iff_positive_factorization source sourceScore sourceCausal
    weights hnontrivial).mp hkernel
  apply (integrable_const (factor * varianceForm source sourceScore weights)).mono'
    (formRatio_observable_measurable source target sourceScore targetScore sourceCausal targetCausal
      weights (fun r ↦ r.getD 0) measurable_id).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro effects
  have hb := factorized_ratio_bounds source target sourceScore targetScore sourceCausal targetCausal
    weights factor hf hfactor effects
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- Nonalignment of the finite cross vectors supplies a source-invisible
direction with nonzero target cross form. -/
theorem nonalignment_kernel_direction
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (hnontrivial : ∃ direction, crossForm source sourceScore sourceCausal weights direction ≠ 0)
    (hnonaligned : ¬ ∃ factor : ℝ, ∀ k,
      covarianceVector target targetScore targetCausal weights k =
        factor * covarianceVector source sourceScore sourceCausal weights k) :
    ∃ effects : K → ℝ, crossForm source sourceScore sourceCausal weights effects = 0 ∧
      crossForm target targetScore targetCausal weights effects ≠ 0 := by
  classical
  obtain ⟨direction, hd⟩ := hnontrivial
  let factor := crossForm target targetScore targetCausal weights direction /
    crossForm source sourceScore sourceCausal weights direction
  have hcoordinate : ∃ k, covarianceVector target targetScore targetCausal weights k ≠
      factor * covarianceVector source sourceScore sourceCausal weights k := by
    by_contra! hcoords
    exact hnonaligned ⟨factor, hcoords⟩
  obtain ⟨k, hk⟩ := hcoordinate
  let basis : K → ℝ := Pi.single k 1
  have hsBasis : crossForm source sourceScore sourceCausal weights basis =
      covarianceVector source sourceScore sourceCausal weights k := by
    rw [crossForm_eq_dot]
    simp [basis, Pi.single_apply]
  have htBasis : crossForm target targetScore targetCausal weights basis =
      covarianceVector target targetScore targetCausal weights k := by
    rw [crossForm_eq_dot]
    simp [basis, Pi.single_apply]
  let t := -(crossForm source sourceScore sourceCausal weights basis /
    crossForm source sourceScore sourceCausal weights direction)
  refine ⟨fun j ↦ basis j + t * direction j, ?_, ?_⟩
  · rw [crossForm_affine_line]
    dsimp [t]
    field_simp
    ring
  · rw [crossForm_affine_line]
    intro hzero
    apply hk
    have htarget := hzero
    rw [htBasis] at htarget
    dsimp [t] at htarget
    dsimp [factor]
    rw [hsBasis] at htarget
    field_simp at htarget ⊢
    nlinarith

/-- Source trait variance surviving on the covariance kernel and cross-vector
nonalignment construct a genuine pole witness. Target variance positivity is
derived from its nonzero cross form by covariance Cauchy–Schwarz. -/
theorem nondegenerate_nonaligned_witness
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (hss : 0 < varianceForm source sourceScore weights)
    (hts : 0 < varianceForm target targetScore weights)
    (hnontrivial : ∃ direction, crossForm source sourceScore sourceCausal weights direction ≠ 0)
    (hnonaligned : ¬ ∃ factor : ℝ, ∀ k,
      covarianceVector target targetScore targetCausal weights k =
        factor * covarianceVector source sourceScore sourceCausal weights k)
    (hkernel : ¬ SourceKernelDegenerate source sourceScore sourceCausal weights) :
    ∃ effects₀ : K → ℝ, PoleWitness source target sourceScore targetScore sourceCausal
      targetCausal weights effects₀ := by
  classical
  simp only [SourceKernelDegenerate, not_forall] at hkernel
  obtain ⟨u, hsu, hqu⟩ := hkernel
  have hquPos : 0 < varianceForm source sourceCausal u :=
    lt_of_le_of_ne (varianceForm_nonneg source sourceCausal u) (Ne.symm hqu)
  by_cases htu : crossForm target targetScore targetCausal weights u = 0
  · obtain ⟨v, hsv, htv⟩ := nonalignment_kernel_direction source target sourceScore targetScore
      sourceCausal targetCausal weights hnontrivial hnonaligned
    let line := fun t : ℝ ↦ fun k ↦ u k + t * v k
    have hline : Continuous line := by
      apply continuous_pi
      intro k
      exact continuous_const.add (continuous_id.mul continuous_const)
    have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < varianceForm source sourceCausal (line t) := by
      apply ((varianceForm_effects_continuous source sourceCausal).comp hline).continuousAt
        |>.eventually
      simpa [line] using lt_mem_nhds hquPos
    obtain ⟨delta, hdelta, hlocal⟩ := Metric.mem_nhds_iff.mp hevent
    let t := delta / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hst : 0 < varianceForm source sourceCausal (line t) := hlocal (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
      dsimp [t]
      linarith)
    have hsource : crossForm source sourceScore sourceCausal weights (line t) = 0 := by
      rw [crossForm_affine_line, hsu, hsv]
      ring
    have htarget : crossForm target targetScore targetCausal weights (line t) ≠ 0 := by
      rw [crossForm_affine_line, htu, zero_add]
      exact mul_ne_zero ht.ne' htv
    exact ⟨line t, hss, hts, hst,
      trait_variance_pos_of_cross_ne target targetScore targetCausal weights (line t) htarget,
      hsource, hnontrivial, htarget⟩
  · exact ⟨u, hss, hts, hquPos,
      trait_variance_pos_of_cross_ne target targetScore targetCausal weights u htu,
      hsu, hnontrivial, htu⟩

/-- Under nonalignment and positive score variances, the source kernel criterion
is exactly the obstruction to a witnessed covariance-hyperplane pole. -/
theorem witness_exists_iff_not_kernel
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (hss : 0 < varianceForm source sourceScore weights)
    (hts : 0 < varianceForm target targetScore weights)
    (hnontrivial : ∃ direction, crossForm source sourceScore sourceCausal weights direction ≠ 0)
    (hnonaligned : ¬ ∃ factor : ℝ, ∀ k,
      covarianceVector target targetScore targetCausal weights k =
        factor * covarianceVector source sourceScore sourceCausal weights k) :
    (∃ effects₀, PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀) ↔ ¬ SourceKernelDegenerate source sourceScore sourceCausal weights := by
  constructor
  · rintro ⟨effects₀, hwitness⟩ hkernel
    exact hwitness.source_trait_pos.ne' (hkernel effects₀ hwitness.source_cross_zero)
  · exact nondegenerate_nonaligned_witness source target sourceScore targetScore sourceCausal
      targetCausal weights hss hts hnontrivial hnonaligned

/-- The full nonaligned dichotomy for a fixed score: the Gaussian ratio is
integrable exactly in the source rank-one cancellation case. Nonalignment alone
does not imply divergence. Score positivity and nontriviality are explicit. -/
theorem nonaligned_integrable_iff_kernel
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ) (weights : J → ℝ)
    (hss : 0 < varianceForm source sourceScore weights)
    (hts : 0 < varianceForm target targetScore weights)
    (hnontrivial : ∃ direction, crossForm source sourceScore sourceCausal weights direction ≠ 0)
    (hnonaligned : ¬ ∃ factor : ℝ, ∀ k,
      covarianceVector target targetScore targetCausal weights k =
        factor * covarianceVector source sourceScore sourceCausal weights k) :
    Integrable (fun effects ↦ (formRatio source target sourceScore targetScore sourceCausal
      targetCausal weights effects).getD 0) (effectLaw K) ↔
        SourceKernelDegenerate source sourceScore sourceCausal weights := by
  constructor
  · intro hintegrable
    by_contra hkernel
    obtain ⟨effects₀, hwitness⟩ := nondegenerate_nonaligned_witness source target sourceScore
      targetScore sourceCausal targetCausal weights hss hts hnontrivial hnonaligned hkernel
    have htop := witnessed_ratio_gaussian_integral_top source target sourceScore targetScore
      sourceCausal targetCausal weights hwitness
    exact hintegrable.lintegral_lt_top.ne htop
  · intro hkernel
    exact kernel_ratio_integrable source target sourceScore targetScore sourceCausal targetCausal
      weights hkernel hnontrivial (effectLaw K)

/-- An actual successful fixed learner outcome with nonaligned cross vectors
and a surviving source-kernel trait direction forces the calibrated-label
numerator to diverge. The pole witness is derived from these algebraic conditions. -/
theorem nondegenerate_nonaligned_label_numerator_top {U I : Type*} [Fintype U] [Fintype I]
    [DecidableEq I] (design : FixedDesign U I S T J K)
    (outcome : I → Bool) (weights : J → ℝ) (hlearn : design.learn outcome = some weights)
    (hss : 0 < varianceForm design.source design.sourceGenotype weights)
    (hts : 0 < varianceForm design.target design.targetGenotype weights)
    (hnontrivial : ∃ direction, crossForm design.source design.sourceGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights direction ≠ 0)
    (hnonaligned : ¬ ∃ factor : ℝ, ∀ k,
      covarianceVector design.target design.targetGenotype
        (fun t ↦ design.causalGenotype (design.targetIndex t)) weights k =
      factor * covarianceVector design.source design.sourceGenotype
        (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights k)
    (hkernel : ¬ SourceKernelDegenerate design.source design.sourceGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights) :
    (∫⁻ effects, ENNReal.ofReal (innerValue design effects) ∂effectLaw K) = ∞ := by
  obtain ⟨effects₀, hwitness⟩ := nondegenerate_nonaligned_witness design.source design.target
    design.sourceGenotype design.targetGenotype
    (fun s ↦ design.causalGenotype (design.sourceIndex s))
    (fun t ↦ design.causalGenotype (design.targetIndex t)) weights hss hts hnontrivial
    hnonaligned hkernel
  exact witnessed_gaussian_label_numerator_top design outcome weights hlearn hwitness

/-- When every successfully learned score has source rank-one cancellation,
the full calibrated-label numerator is integrable. Learner failures contribute
no reported ratio. Target covariance alignment is not required. -/
theorem kernel_label_numerator_integrable {U I : Type*} [Fintype U] [Fintype I]
    [DecidableEq I] (design : FixedDesign U I S T J K)
    (hkernels : ∀ outcome weights, design.learn outcome = some weights →
      SourceKernelDegenerate design.source design.sourceGenotype
        (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights)
    (hnontrivial : ∀ outcome weights, design.learn outcome = some weights →
      ∃ direction, crossForm design.source design.sourceGenotype
        (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights direction ≠ 0) :
    Integrable (innerValue design) (effectLaw K) := by
  apply integrable_finset_sum
  intro outcome _
  cases hlearn : design.learn outcome with
  | none =>
    simpa only [report, hlearn, Option.bind_none, Option.getD_none, mul_zero] using
      (integrable_zero (K → ℝ) ℝ (effectLaw K))
  | some weights =>
    have hi : Integrable (fun effects ↦ (report design effects outcome).getD 0) (effectLaw K) := by
      simpa only [report, hlearn, Option.bind_some] using
        kernel_ratio_integrable design.source design.target design.sourceGenotype
          design.targetGenotype (fun s ↦ design.causalGenotype (design.sourceIndex s))
          (fun t ↦ design.causalGenotype (design.targetIndex t)) weights
          (hkernels outcome weights hlearn) (hnontrivial outcome weights hlearn) (effectLaw K)
    apply hi.mono' (((labelKernel design).weight_measurable outcome).mul
      (reportValue_measurable design outcome)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro effects
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      ((labelKernel design).weight_nonneg effects outcome)
        (reportValue_nonneg design effects outcome))]
    exact mul_le_of_le_one_left (reportValue_nonneg design effects outcome)
      (labelWeight_le_one design effects outcome)

/-- The nonaligned integrability dichotomy survives calibrated label selection:
under the stated nonalignment/nondegeneracy conditions for each successful
learner output, finite numerator is equivalent to source rank-one cancellation
for every such output. No matrix condition is asserted for the actual simulator. -/
theorem nonaligned_label_integrable_iff_kernels {U I : Type*} [Fintype U] [Fintype I]
    [DecidableEq I] (design : FixedDesign U I S T J K)
    (hconditions : ∀ outcome weights, design.learn outcome = some weights →
      0 < varianceForm design.source design.sourceGenotype weights ∧
      0 < varianceForm design.target design.targetGenotype weights ∧
      (∃ direction, crossForm design.source design.sourceGenotype
        (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights direction ≠ 0) ∧
      ¬ ∃ factor : ℝ, ∀ k,
        covarianceVector design.target design.targetGenotype
          (fun t ↦ design.causalGenotype (design.targetIndex t)) weights k =
        factor * covarianceVector design.source design.sourceGenotype
          (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights k) :
    Integrable (innerValue design) (effectLaw K) ↔
      ∀ outcome weights, design.learn outcome = some weights →
        SourceKernelDegenerate design.source design.sourceGenotype
          (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights := by
  constructor
  · intro hi outcome weights hlearn
    by_contra hkernel
    obtain ⟨hss, hts, hnontrivial, hnonaligned⟩ := hconditions outcome weights hlearn
    have htop := nondegenerate_nonaligned_label_numerator_top design outcome weights hlearn
      hss hts hnontrivial hnonaligned hkernel
    exact hi.lintegral_lt_top.ne htop
  · intro hkernels
    exact kernel_label_numerator_integrable design hkernels
      (fun outcome weights hlearn ↦ (hconditions outcome weights hlearn).2.2.1)

end Descent.Portability.RatioSourceDegeneracy
