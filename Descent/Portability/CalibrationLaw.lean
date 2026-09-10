/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimulationAccuracy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

assert_below Descent.Decision Descent.Program

/-!
Calibration of Gaussian-threshold prevalence for the simulation's globally
standardized genetic liabilities and bounded affine deme baselines.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CalibrationLaw

open MeasureTheory ProbabilityTheory FiniteReportLaw SimulationAccuracy
open scoped Topology NNReal

noncomputable def normalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic x)

private instance normal_noAtoms : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero

theorem normalCDF_continuous : Continuous normalCDF := by
  have hrepr (x : ℝ) : normalCDF x = normalCDF 0 +
      ∫ z in (0 : ℝ)..x, (1 : ℝ) ∂gaussianReal 0 1 := by
    have h := intervalIntegral.integral_Iic_sub_Iic
      ((integrable_const (1 : ℝ)).integrableOn :
        IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Iic 0) (gaussianReal 0 1))
      ((integrable_const (1 : ℝ)).integrableOn :
        IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Iic x) (gaussianReal 0 1))
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at h
    unfold normalCDF
    linarith
  have heq : normalCDF = fun x ↦ normalCDF 0 +
      ∫ z in (0 : ℝ)..x, (1 : ℝ) ∂gaussianReal 0 1 := funext hrepr
  rw [heq]
  exact continuous_const.add ((integrable_const (1 : ℝ)).continuous_primitive 0)

theorem normalCDF_strictMono : StrictMono normalCDF := by
  intro x y hxy
  have hpos : 0 < (gaussianReal 0 1).real (Set.Ioc x y) := by
    apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
    by_contra! hzero
    have hv := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero
      (le_antisymm hzero (zero_le _))
    simp only [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hv
    linarith
  have hsum := measureReal_union
    (μ := gaussianReal 0 1) (s₁ := Set.Iic x) (s₂ := Set.Ioc x y)
    (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
  rw [Set.Iic_union_Ioc_eq_Iic hxy.le] at hsum
  unfold normalCDF
  linarith

theorem caseProbability_eq_normalCDF (mean : ℝ) :
    ProbitTrainingLaw.caseProbability mean 1 = normalCDF mean := by
  have hmap : (gaussianReal 0 1).map (fun x ↦ mean - x) = gaussianReal mean 1 := by
    simpa using gaussianReal_map_const_sub (μ := 0) (v := 1) mean
  unfold ProbitTrainingLaw.caseProbability normalCDF
  rw [← hmap, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  have hset : (fun x : ℝ ↦ mean - x) ⁻¹' Set.Ioi 0 = Set.Iio mean := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, sub_pos]
  rw [hset]
  exact congrArg ENNReal.toReal (measure_congr Iio_ae_eq_Iic)

theorem normalCDF_mem_openUnitInterval (x : ℝ) : 0 < normalCDF x ∧ normalCDF x < 1 := by
  constructor
  · exact lt_of_le_of_lt (measureReal_nonneg : 0 ≤ normalCDF (x - 1))
      (normalCDF_strictMono (by linarith : x - 1 < x))
  · exact lt_of_lt_of_le (normalCDF_strictMono (by linarith : x < x + 1))
      (measureReal_le_one : normalCDF (x + 1) ≤ 1)

theorem gaussian_labelMass_pos {I : Type*} [Fintype I]
    (mean : I → ℝ) (outcome : I → Bool) :
    0 < TrainingNoiseAccuracy.labelMass
      (fun i ↦ ProbitTrainingLaw.caseProbability (mean i) 1) outcome := by
  unfold TrainingNoiseAccuracy.labelMass
  apply Finset.prod_pos
  intro i _
  have h := normalCDF_mem_openUnitInterval (mean i)
  dsimp only
  rw [caseProbability_eq_normalCDF]
  cases outcome i
  · simp only [Bool.false_eq_true, ite_false]
    linarith
  · exact h.1

theorem gaussian_second_moment (mean : ℝ) :
    (∫ x, x ^ 2 ∂gaussianReal mean 1) = mean ^ 2 + 1 := by
  have h := ProbabilityTheory.variance_eq_sub
    (memLp_id_gaussianReal (μ := mean) (v := 1) 2)
  simp only [variance_id_gaussianReal, integral_id_gaussianReal,
    NNReal.coe_one, Pi.pow_apply, id_eq] at h
  linarith

theorem gaussian_squared_tail (mean threshold : ℝ) (ht : 0 < threshold) :
    (gaussianReal mean 1).real {x | threshold ^ 2 ≤ x ^ 2} ≤
      (mean ^ 2 + 1) / threshold ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianReal mean 1) (f := fun x : ℝ ↦ x ^ 2)
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg x))
    ((memLp_id_gaussianReal (μ := mean) (v := 1) 2).integrable_sq) (threshold ^ 2)
  rw [gaussian_second_moment] at h
  exact (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by simpa [mul_comm] using h)

theorem gaussian_upper_tail (mean threshold : ℝ) (ht : 0 < threshold) :
    (gaussianReal mean 1).real (Set.Ioi threshold) ≤
      (mean ^ 2 + 1) / threshold ^ 2 := by
  refine le_trans (measureReal_mono ?_) (gaussian_squared_tail mean threshold ht)
  intro x hx
  simp only [Set.mem_Ioi] at hx
  simp only [Set.mem_setOf_eq]
  nlinarith

theorem gaussian_lower_tail (mean threshold : ℝ) (ht : 0 < threshold) :
    (gaussianReal mean 1).real (Set.Iic (-threshold)) ≤
      (mean ^ 2 + 1) / threshold ^ 2 := by
  refine le_trans (measureReal_mono ?_) (gaussian_squared_tail mean threshold ht)
  intro x hx
  simp only [Set.mem_Iic] at hx
  simp only [Set.mem_setOf_eq]
  nlinarith

theorem shifted_caseProbability (mean shift : ℝ) :
    ProbitTrainingLaw.caseProbability (mean + shift) 1 =
      (gaussianReal mean 1).real (Set.Ioi (-shift)) := by
  unfold ProbitTrainingLaw.caseProbability
  rw [← gaussianReal_map_add_const (μ := mean) (v := 1) shift,
    map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

theorem shifted_caseProbability_upper (mean shift threshold : ℝ)
    (ht : 0 < threshold) (hshift : shift ≤ -threshold) :
    ProbitTrainingLaw.caseProbability (mean + shift) 1 ≤
      (mean ^ 2 + 1) / threshold ^ 2 := by
  rw [shifted_caseProbability]
  refine le_trans (measureReal_mono ?_) (gaussian_upper_tail mean threshold ht)
  intro x hx
  simp only [Set.mem_Ioi] at hx ⊢
  linarith

theorem shifted_controlProbability_upper (mean shift threshold : ℝ)
    (ht : 0 < threshold) (hshift : threshold ≤ shift) :
    1 - ProbitTrainingLaw.caseProbability (mean + shift) 1 ≤
      (mean ^ 2 + 1) / threshold ^ 2 := by
  rw [shifted_caseProbability]
  have hc := measureReal_compl (μ := gaussianReal mean 1) (s := Set.Ioi (-shift))
    measurableSet_Ioi
  simp only [Set.compl_Ioi, measureReal_univ_eq_one] at hc
  rw [← hc]
  refine le_trans (measureReal_mono ?_) (gaussian_lower_tail mean threshold ht)
  intro x hx
  simp only [Set.mem_Iic] at hx ⊢
  linarith

variable {S : Type*} [Fintype S]

theorem standardized_mean_zero (p : FiniteReportLaw S) (epsilon : ℝ) (f : S → ℝ) :
    p.expectation (standardize p epsilon f) = 0 := by
  rw [standardize_eq_affine, expectation_affine]
  ring

theorem standardized_second_moment_le_one (p : FiniteReportLaw S)
    (epsilon : ℝ) (he : 0 < epsilon) (f : S → ℝ) :
    p.expectation (fun s ↦ standardize p epsilon f s ^ 2) ≤ 1 := by
  have hv := p.variance_nonneg f
  have hs := Real.sqrt_nonneg (p.variance f)
  have hsq := Real.sq_sqrt hv
  have hd : 0 < Real.sqrt (p.variance f) + epsilon := add_pos_of_nonneg_of_pos hs he
  have hvar : p.variance (standardize p epsilon f) ≤ 1 := by
    rw [standardize_eq_affine, variance_affine]
    have heq : (1 / (Real.sqrt (p.variance f) + epsilon)) ^ 2 * p.variance f =
        p.variance f / (Real.sqrt (p.variance f) + epsilon) ^ 2 := by
      field_simp
    rw [heq]
    apply (div_le_one (sq_pos_of_pos hd)).mpr
    nlinarith [mul_nonneg hs he.le]
  rw [p.variance_eq_rawMoments, standardized_mean_zero] at hvar
  simpa using hvar

noncomputable def prevalence (p : FiniteReportLaw S) (linear : S → ℝ) (intercept : ℝ) : ℝ :=
  p.expectation (fun s ↦ normalCDF (intercept + linear s))

theorem prevalence_continuous (p : FiniteReportLaw S) (linear : S → ℝ) :
    Continuous (prevalence p linear) := by
  unfold prevalence expectation
  apply continuous_finset_sum
  intro s _
  exact continuous_const.mul (normalCDF_continuous.comp (continuous_id.add continuous_const))

theorem prevalence_strictMono (p : FiniteReportLaw S) (linear : S → ℝ) :
    StrictMono (prevalence p linear) := by
  have hex : ∃ s, 0 < p.mass s := by
    by_contra! h
    have hz : ∑ s, p.mass s = 0 := Finset.sum_eq_zero (fun s _ ↦
      le_antisymm (h s) (p.mass_nonneg s))
    rw [p.mass_sum] at hz
    norm_num at hz
  obtain ⟨s₀, hs₀⟩ := hex
  intro a b hab
  unfold prevalence expectation
  apply Finset.sum_lt_sum
  · intro s _
    exact mul_le_mul_of_nonneg_left
      (normalCDF_strictMono (by linarith : a + linear s < b + linear s)).le (p.mass_nonneg s)
  · exact ⟨s₀, Finset.mem_univ _, mul_lt_mul_of_pos_left
      (normalCDF_strictMono (by linarith : a + linear s₀ < b + linear s₀)) hs₀⟩

private theorem expectation_second_bound (p : FiniteReportLaw S) (g : S → ℝ)
    (threshold : ℝ)
    (hg : p.expectation (fun s ↦ g s ^ 2) ≤ 1) :
    (∑ s, p.mass s * ((g s ^ 2 + 1) / threshold ^ 2)) ≤ 2 / threshold ^ 2 := by
  have heq : (∑ s, p.mass s * ((g s ^ 2 + 1) / threshold ^ 2)) =
      (p.expectation (fun s ↦ g s ^ 2) + 1) / threshold ^ 2 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, mul_add, mul_one,
      Finset.sum_add_distrib, p.mass_sum, expectation]
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The lower bracket remains valid for every causal effect vector after
standardization, including a constant genetic score. -/
theorem prevalence_lower_bracket (p : FiniteReportLaw S) (g baseline : S → ℝ)
    (hg : p.expectation (fun s ↦ g s ^ 2) ≤ 1)
    (hb : ∀ s, baseline s ≤ 7 / 10) :
    prevalence p (fun s ↦ baseline s + g s) (-20) < 3 / 20 := by
  have hbound : prevalence p (fun s ↦ baseline s + g s) (-20) ≤
      2 / (193 / 10 : ℝ) ^ 2 := by
    refine le_trans ?_ (expectation_second_bound p g (193 / 10) hg)
    unfold prevalence expectation
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (p.mass_nonneg s)
    dsimp only
    rw [← caseProbability_eq_normalCDF]
    have heq : -20 + (baseline s + g s) = g s + (-20 + baseline s) := by ring
    rw [heq]
    exact shifted_caseProbability_upper (g s) (-20 + baseline s) (193 / 10)
      (by norm_num) (by linarith [hb s])
  exact lt_of_le_of_lt hbound (by norm_num)

/-- The upper bracket follows from the same second-moment estimate on the
control probability. No pointwise bound on genetic liability is assumed. -/
theorem prevalence_upper_bracket (p : FiniteReportLaw S) (g baseline : S → ℝ)
    (hg : p.expectation (fun s ↦ g s ^ 2) ≤ 1)
    (hb : ∀ s, -(7 / 10) ≤ baseline s) :
    3 / 20 < prevalence p (fun s ↦ baseline s + g s) 20 := by
  have hbound : 1 - prevalence p (fun s ↦ baseline s + g s) 20 ≤
      2 / (193 / 10 : ℝ) ^ 2 := by
    have heq : 1 - prevalence p (fun s ↦ baseline s + g s) 20 =
        ∑ s, p.mass s * (1 - normalCDF (20 + (baseline s + g s))) := by
      simp only [prevalence, expectation, mul_sub, mul_one, Finset.sum_sub_distrib, p.mass_sum]
    rw [heq]
    refine le_trans ?_ (expectation_second_bound p g (193 / 10) hg)
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (p.mass_nonneg s)
    dsimp only
    rw [← caseProbability_eq_normalCDF]
    have heq : 20 + (baseline s + g s) = g s + (20 + baseline s) := by ring
    rw [heq]
    exact shifted_controlProbability_upper (g s) (20 + baseline s) (193 / 10)
      (by norm_num) (by linarith [hb s])
  linarith

/-- A unique prevalence-calibrating intercept lies strictly inside the exact
bracket used by the simulation. This is an existence/uniqueness theorem for the
real equation, rather than a claim about a numerical root finder's tolerance. -/
theorem exists_unique_calibrated_intercept (p : FiniteReportLaw S)
    (g baseline : S → ℝ) (hg : p.expectation (fun s ↦ g s ^ 2) ≤ 1)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) :
    ∃! intercept : ℝ, intercept ∈ Set.Ioo (-20) 20 ∧
      prevalence p (fun s ↦ baseline s + g s) intercept = 3 / 20 := by
  have hlo := prevalence_lower_bracket p g baseline hg (fun s ↦ (hb s).2)
  have hhi := prevalence_upper_bracket p g baseline hg (fun s ↦ (hb s).1)
  have hc : ContinuousOn (prevalence p (fun s ↦ baseline s + g s)) (Set.Icc (-20) 20) :=
    (prevalence_continuous p (fun s ↦ baseline s + g s)).continuousOn
  have hex := intermediate_value_Icc (a := (-20 : ℝ)) (b := 20)
    (by norm_num : (-20 : ℝ) ≤ 20) hc ⟨hlo.le, hhi.le⟩
  obtain ⟨c, hc, hvalue⟩ := hex
  have hmono := prevalence_strictMono p (fun s ↦ baseline s + g s)
  refine ⟨c, ⟨?_, hvalue⟩, ?_⟩
  · exact ⟨lt_of_le_of_ne hc.1 (by intro h; subst c; linarith),
      lt_of_le_of_ne hc.2 (by intro h; subst c; linarith)⟩
  · intro y hy
    exact hmono.injective (hy.2.trans hvalue.symm)

theorem standardized_calibrated_intercept (p : FiniteReportLaw S)
    (raw baseline : S → ℝ) (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) :
    ∃! intercept : ℝ, intercept ∈ Set.Ioo (-20) 20 ∧
      prevalence p (fun s ↦ baseline s + standardize p epsilon raw s) intercept = 3 / 20 :=
  exists_unique_calibrated_intercept p (standardize p epsilon raw) baseline
    (standardized_second_moment_le_one p epsilon he raw) hb

theorem expectation_continuous (p : FiniteReportLaw S) :
    Continuous (fun raw : S → ℝ ↦ p.expectation raw) := by
  unfold expectation
  apply continuous_finset_sum
  intro s _
  exact continuous_const.mul (continuous_apply s)

theorem variance_continuous (p : FiniteReportLaw S) :
    Continuous (fun raw : S → ℝ ↦ p.variance raw) := by
  simp_rw [p.variance_eq_rawMoments]
  apply Continuous.sub _ ((expectation_continuous p).pow 2)
  unfold expectation
  apply continuous_finset_sum
  intro s _
  exact continuous_const.mul ((continuous_apply s).pow 2)

theorem standardize_coordinate_continuous (p : FiniteReportLaw S)
    (epsilon : ℝ) (he : 0 < epsilon) (s : S) :
    Continuous (fun raw : S → ℝ ↦ standardize p epsilon raw s) := by
  unfold standardize
  apply ((continuous_apply s).sub (expectation_continuous p)).div
    (((variance_continuous p).sqrt).add continuous_const)
  intro raw
  exact ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) he)

theorem normalized_prevalence_continuous (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon) (intercept : ℝ) :
    Continuous (fun raw : S → ℝ ↦
      prevalence p (fun s ↦ baseline s + standardize p epsilon raw s) intercept) := by
  unfold prevalence expectation
  apply continuous_finset_sum
  intro s _
  exact continuous_const.mul (normalCDF_continuous.comp
    (continuous_const.add (continuous_const.add
      (standardize_coordinate_continuous p epsilon he s))))

noncomputable def calibratedIntercept (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) (raw : S → ℝ) : ℝ :=
  (standardized_calibrated_intercept p raw baseline epsilon he hb).exists.choose

theorem calibratedIntercept_spec (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) (raw : S → ℝ) :
    calibratedIntercept p baseline epsilon he hb raw ∈ Set.Ioo (-20) 20 ∧
      prevalence p (fun s ↦ baseline s + standardize p epsilon raw s)
        (calibratedIntercept p baseline epsilon he hb raw) = 3 / 20 :=
  (standardized_calibrated_intercept p raw baseline epsilon he hb).exists.choose_spec

theorem calibratedIntercept_lt_iff (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) (raw : S → ℝ) (a : ℝ) :
    calibratedIntercept p baseline epsilon he hb raw < a ↔
      3 / 20 < prevalence p (fun s ↦ baseline s + standardize p epsilon raw s) a := by
  have hmono := prevalence_strictMono p (fun s ↦ baseline s + standardize p epsilon raw s)
  have h := hmono.lt_iff_lt
    (a := calibratedIntercept p baseline epsilon he hb raw) (b := a)
  rw [(calibratedIntercept_spec p baseline epsilon he hb raw).2] at h
  exact h.symm

theorem lt_calibratedIntercept_iff (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) (raw : S → ℝ) (a : ℝ) :
    a < calibratedIntercept p baseline epsilon he hb raw ↔
      prevalence p (fun s ↦ baseline s + standardize p epsilon raw s) a < 3 / 20 := by
  have hmono := prevalence_strictMono p (fun s ↦ baseline s + standardize p epsilon raw s)
  have h := hmono.lt_iff_lt
    (a := a) (b := calibratedIntercept p baseline epsilon he hb raw)
  rw [(calibratedIntercept_spec p baseline epsilon he hb raw).2] at h
  exact h.symm

theorem calibratedIntercept_continuous (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) :
    Continuous (calibratedIntercept p baseline epsilon he hb) := by
  apply continuous_iff_continuousAt.mpr
  intro raw
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hf := (lt_calibratedIntercept_iff p baseline epsilon he hb raw a).mp ha
    have hevent := Filter.Tendsto.eventually_lt_const hf
      (normalized_prevalence_continuous p baseline epsilon he a).continuousAt.tendsto
    filter_upwards [hevent] with other hother
    exact (lt_calibratedIntercept_iff p baseline epsilon he hb other a).mpr hother
  · intro a ha
    have hf := (calibratedIntercept_lt_iff p baseline epsilon he hb raw a).mp ha
    have hevent := Filter.Tendsto.eventually_const_lt hf
      (normalized_prevalence_continuous p baseline epsilon he a).continuousAt.tendsto
    filter_upwards [hevent] with other hother
    exact (calibratedIntercept_lt_iff p baseline epsilon he hb other a).mpr hother

/-- The calibrated intercept is a measurable function of the complete raw
liability vector. Its dependence is retained when integrating causal effects. -/
theorem calibratedIntercept_measurable (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) :
    Measurable (calibratedIntercept p baseline epsilon he hb) :=
  (calibratedIntercept_continuous p baseline epsilon he hb).measurable

theorem calibrated_caseProbability_measurable (p : FiniteReportLaw S) (baseline : S → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) (s : S) :
    Measurable (fun raw : S → ℝ ↦ ProbitTrainingLaw.caseProbability
      (calibratedIntercept p baseline epsilon he hb raw + baseline s +
        standardize p epsilon raw s) 1) := by
  simp_rw [caseProbability_eq_normalCDF]
  exact normalCDF_continuous.measurable.comp
    (((calibratedIntercept_measurable p baseline epsilon he hb).add_const (baseline s)).add
      (standardize_coordinate_continuous p epsilon he s).measurable)

omit [Fintype S] in
theorem linearScore_effects_continuous {K : Type*} [Fintype K]
    (genotype : S → K → ℝ) :
    Continuous (fun effects : K → ℝ ↦ TrainingNoiseAccuracy.linearScore genotype effects) := by
  apply continuous_pi
  intro s
  unfold TrainingNoiseAccuracy.linearScore
  apply continuous_finset_sum
  intro k _
  exact (continuous_apply k).mul continuous_const

/-- The actual calibrated Bernoulli probability is measurable in the causal
effect vector, with normalization and the solved intercept both retained. -/
theorem calibrated_effectProbability_measurable {K : Type*} [Fintype K]
    (p : FiniteReportLaw S) (baseline : S → ℝ) (genotype : S → K → ℝ)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hb : ∀ s, -(7 / 10) ≤ baseline s ∧ baseline s ≤ 7 / 10) (s : S) :
    Measurable (fun effects : K → ℝ ↦
      let raw := TrainingNoiseAccuracy.linearScore genotype effects
      ProbitTrainingLaw.caseProbability
        (calibratedIntercept p baseline epsilon he hb raw + baseline s +
          standardize p epsilon raw s) 1) :=
  (calibrated_caseProbability_measurable p baseline epsilon he hb s).comp
    (linearScore_effects_continuous genotype).measurable

end Descent.Portability.CalibrationLaw
