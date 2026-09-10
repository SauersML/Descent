/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityRatioGeometry

assert_below Descent.Decision Descent.Program

/-!
Conditional local poles of the target/source squared-correlation ratio. A witness
is a fixed effect vector on the source covariance hyperplane, with nonzero target
covariance and positive trait and score variances. The lower bound holds on an
open neighborhood off the hyperplane, not merely on one line. No witness is
asserted for the simulator's realized genotypes or fitted weights.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RatioPoleLaw

open FiniteReportLaw TrainingNoiseAccuracy SimulationAccuracy GaussianEffectPortabilityLaw
open PortabilityRatioGeometry Filter Topology MeasureTheory
open scoped ENNReal

variable {S T J K : Type*} [Fintype S] [Fintype T] [Fintype J] [Fintype K]
  (source : FiniteReportLaw S) (target : FiniteReportLaw T)
  (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
  (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
  (weights : J → ℝ)

/-- The factor remaining after multiplication by the squared source cross form. -/
noncomputable def numeratorFactor (effects : K → ℝ) : ℝ :=
  (crossForm target targetScore targetCausal weights effects ^ 2 *
    (varianceForm source sourceScore weights * varianceForm source sourceCausal effects)) /
    (varianceForm target targetScore weights * varianceForm target targetCausal effects)

/-- These hypotheses are local, directly checkable covariance conditions. -/
structure PoleWitness (effects : K → ℝ) : Prop where
  source_score_pos : 0 < varianceForm source sourceScore weights
  target_score_pos : 0 < varianceForm target targetScore weights
  source_trait_pos : 0 < varianceForm source sourceCausal effects
  target_trait_pos : 0 < varianceForm target targetCausal effects
  source_cross_zero : crossForm source sourceScore sourceCausal weights effects = 0
  source_cross_nontrivial : ∃ direction,
    crossForm source sourceScore sourceCausal weights direction ≠ 0
  target_cross_ne : crossForm target targetScore targetCausal weights effects ≠ 0

include sourceScore targetScore sourceCausal targetCausal weights

theorem numeratorFactor_pos {effects : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects) :
    0 < numeratorFactor source target sourceScore targetScore sourceCausal targetCausal
      weights effects :=
  div_pos (mul_pos (sq_pos_of_ne_zero h.target_cross_ne)
    (mul_pos h.source_score_pos h.source_trait_pos))
    (mul_pos h.target_score_pos h.target_trait_pos)

theorem numeratorFactor_continuousAt {effects : K → ℝ}
    (hts : 0 < varianceForm target targetScore weights)
    (htc : 0 < varianceForm target targetCausal effects) :
    ContinuousAt (numeratorFactor source target sourceScore targetScore sourceCausal
      targetCausal weights) effects := by
  apply ContinuousAt.div
  · have hc := (crossForm_effects_continuous target targetScore targetCausal weights).continuousAt
      (x := effects)
    exact (hc.pow 2).mul (continuousAt_const.mul
      (varianceForm_effects_continuous source sourceCausal).continuousAt)
  · exact continuousAt_const.mul
      (varianceForm_effects_continuous target targetCausal).continuousAt
  · exact (mul_pos hts htc).ne'

theorem formRatio_eq_factor {effects : K → ℝ}
    (hss : 0 < varianceForm source sourceScore weights)
    (hsc : 0 < varianceForm source sourceCausal effects)
    (hts : 0 < varianceForm target targetScore weights)
    (htc : 0 < varianceForm target targetCausal effects)
    (hc : crossForm source sourceScore sourceCausal weights effects ≠ 0) :
    formRatio source target sourceScore targetScore sourceCausal targetCausal weights effects =
      some (numeratorFactor source target sourceScore targetScore sourceCausal targetCausal
        weights effects / crossForm source sourceScore sourceCausal weights effects ^ 2) := by
  rw [formRatio_value source target sourceScore targetScore sourceCausal targetCausal weights
    effects hss hsc hts htc hc]
  simp only [numeratorFactor, div_div]

/-- A witnessed pole gives uniform positive lower and finite upper coefficients
throughout an open neighborhood. All points off the hyperplane are reportable. -/
theorem open_neighborhood_pole {effects₀ : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∃ neighborhood : Set (K → ℝ), IsOpen neighborhood ∧ effects₀ ∈ neighborhood ∧
        ∀ effects ∈ neighborhood,
          crossForm source sourceScore sourceCausal weights effects ≠ 0 →
          ∃ value : ℝ,
            formRatio source target sourceScore targetScore sourceCausal targetCausal
              weights effects = some value ∧
            lower / crossForm source sourceScore sourceCausal weights effects ^ 2 ≤ value ∧
            value ≤ upper / crossForm source sourceScore sourceCausal weights effects ^ 2 := by
  let f := numeratorFactor source target sourceScore targetScore sourceCausal targetCausal weights
  have hf : 0 < f effects₀ := numeratorFactor_pos source target sourceScore targetScore
    sourceCausal targetCausal weights h
  have hcont : ContinuousAt f effects₀ := numeratorFactor_continuousAt source target sourceScore
    targetScore sourceCausal targetCausal weights h.target_score_pos h.target_trait_pos
  have hevent : ∀ᶠ effects in 𝓝 effects₀,
      0 < varianceForm source sourceCausal effects ∧
      0 < varianceForm target targetCausal effects ∧
      f effects₀ / 2 < f effects ∧ f effects < 2 * f effects₀ := by
    filter_upwards
      [(varianceForm_effects_continuous source sourceCausal).continuousAt.eventually
        (lt_mem_nhds h.source_trait_pos),
       (varianceForm_effects_continuous target targetCausal).continuousAt.eventually
        (lt_mem_nhds h.target_trait_pos),
       hcont.eventually (lt_mem_nhds (show f effects₀ / 2 < f effects₀ by linarith)),
       hcont.eventually (gt_mem_nhds (show f effects₀ < 2 * f effects₀ by linarith))]
      with effects hsc htc hlo hhi
    exact ⟨hsc, htc, hlo, hhi⟩
  obtain ⟨neighborhood, hsub, hopen, hmem⟩ := mem_nhds_iff.mp hevent
  refine ⟨f effects₀ / 2, 2 * f effects₀, by positivity, by positivity,
    neighborhood, hopen, hmem, ?_⟩
  intro effects heffects hc
  obtain ⟨hsc, htc, hlo, hhi⟩ := hsub heffects
  refine ⟨f effects / crossForm source sourceScore sourceCausal weights effects ^ 2,
    formRatio_eq_factor source target sourceScore targetScore sourceCausal targetCausal
      weights h.source_score_pos hsc h.target_score_pos htc hc, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right hlo.le (sq_nonneg _)
  · exact div_le_div_of_nonneg_right hhi.le (sq_nonneg _)

omit [Fintype T] targetScore targetCausal in
/-- The cross form is linear in the effects, including transverse perturbations. -/
theorem crossForm_affine_line (effects direction : K → ℝ) (t : ℝ) :
    crossForm source sourceScore sourceCausal weights (fun k ↦ effects k + t * direction k) =
      crossForm source sourceScore sourceCausal weights effects +
        t * crossForm source sourceScore sourceCausal weights direction := by
  simp only [crossForm_eq_dot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact inverse-square coefficient along every direction transverse to
 the source covariance hyperplane. The filter excludes the undefined point. -/
theorem transverse_scaled_limit {effects₀ : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀) (direction : K → ℝ)
    (hd : crossForm source sourceScore sourceCausal weights direction ≠ 0) :
    Tendsto (fun t : ℝ ↦ t ^ 2 *
      (formRatio source target sourceScore targetScore sourceCausal targetCausal weights
        (fun k ↦ effects₀ k + t * direction k)).getD 0)
      (𝓝[≠] 0)
      (𝓝 (numeratorFactor source target sourceScore targetScore sourceCausal targetCausal
        weights effects₀ / crossForm source sourceScore sourceCausal weights direction ^ 2)) := by
  let line := fun t : ℝ ↦ fun k ↦ effects₀ k + t * direction k
  have hline : Continuous line := by
    apply continuous_pi
    intro k
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hline₀ : line 0 = effects₀ := by ext k; simp [line]
  have hsc : ∀ᶠ t in 𝓝 0, 0 < varianceForm source sourceCausal (line t) := by
    apply ((varianceForm_effects_continuous source sourceCausal).comp hline).continuousAt.eventually
    simpa only [Function.comp_apply, hline₀] using lt_mem_nhds h.source_trait_pos
  have htc : ∀ᶠ t in 𝓝 0, 0 < varianceForm target targetCausal (line t) := by
    apply ((varianceForm_effects_continuous target targetCausal).comp hline).continuousAt.eventually
    simpa only [Function.comp_apply, hline₀] using lt_mem_nhds h.target_trait_pos
  have heq : (fun t : ℝ ↦ t ^ 2 *
      (formRatio source target sourceScore targetScore sourceCausal targetCausal weights
        (line t)).getD 0) =ᶠ[𝓝[≠] 0]
      (fun t ↦ numeratorFactor source target sourceScore targetScore sourceCausal targetCausal
        weights (line t) / crossForm source sourceScore sourceCausal weights direction ^ 2) := by
    filter_upwards [hsc.filter_mono nhdsWithin_le_nhds,
      htc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hst htt ht
    have ht' : t ≠ 0 := ht
    have hc : crossForm source sourceScore sourceCausal weights (line t) =
        t * crossForm source sourceScore sourceCausal weights direction := by
      rw [crossForm_affine_line source sourceScore sourceCausal weights,
        h.source_cross_zero, zero_add]
    rw [formRatio_eq_factor source target sourceScore targetScore sourceCausal targetCausal weights
      h.source_score_pos hst h.target_score_pos htt (by rw [hc]; exact mul_ne_zero ht' hd)]
    simp only [Option.getD_some, hc]
    field_simp
  apply Tendsto.congr' heq.symm
  have hf := (numeratorFactor_continuousAt source target sourceScore targetScore sourceCausal
    targetCausal weights h.target_score_pos h.target_trait_pos).tendsto
  have hl : Tendsto line (𝓝[≠] 0) (𝓝 effects₀) := by
    simpa only [hline₀] using (hline.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  exact (hf.comp hl).div_const _

/-- A witness rules out coefficient alignment; this is a geometric condition
on the realized matrices and fixed learned weights. -/
theorem witness_not_aligned {effects₀ : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀) :
    ¬ ∃ factor : ℝ, ∀ k,
      covarianceVector target targetScore targetCausal weights k =
        factor * covarianceVector source sourceScore sourceCausal weights k := by
  rintro ⟨factor, halign⟩
  apply h.target_cross_ne
  rw [crossForm_aligned source target sourceScore targetScore sourceCausal targetCausal
    weights factor halign, h.source_cross_zero, mul_zero]

/-- Nontriviality of the source cross vector guarantees an actual transverse
path with a strictly positive inverse-square coefficient. -/
theorem witness_inverse_square_limit {effects₀ : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀) :
    ∃ (direction : K → ℝ) (coefficient : ℝ), 0 < coefficient ∧
      Tendsto (fun t : ℝ ↦ t ^ 2 *
        (formRatio source target sourceScore targetScore sourceCausal targetCausal weights
          (fun k ↦ effects₀ k + t * direction k)).getD 0)
        (𝓝[≠] 0) (𝓝 coefficient) := by
  obtain ⟨direction, hd⟩ := h.source_cross_nontrivial
  refine ⟨direction, _, ?_, transverse_scaled_limit source target sourceScore targetScore
    sourceCausal targetCausal weights h direction hd⟩
  exact div_pos (numeratorFactor_pos source target sourceScore targetScore sourceCausal
    targetCausal weights h) (sq_pos_of_ne_zero hd)

omit sourceScore targetScore sourceCausal targetCausal weights in
/-- A positive mass in shrinking slabs, not merely a singular line, forces an
infinite nonnegative integral. The quantitative mass assumption must be proved
for the relevant sampling law before applying this criterion. -/
theorem lintegral_top_of_quadratic_slabs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (slab : ℕ → Set Ω)
    (hslab : ∀ n, MeasurableSet (slab n)) (lower mass : ℝ)
    (hlower : 0 < lower) (hmass : 0 < mass)
    (hprob : ∀ n : ℕ, ENNReal.ofReal (mass / (n + 1 : ℝ)) ≤ μ (slab n))
    (hvalue : ∀ (n : ℕ) x, x ∈ slab n → lower * (n + 1 : ℝ) ^ 2 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ∞ := by
  let integral := ∫⁻ x, ENNReal.ofReal (f x) ∂μ
  have hbound (n : ℕ) : ENNReal.ofReal (lower * mass * (n + 1 : ℝ)) ≤ integral := by
    have hn : 0 < (n + 1 : ℝ) := by positivity
    calc
      ENNReal.ofReal (lower * mass * (n + 1 : ℝ)) =
          ENNReal.ofReal (lower * (n + 1 : ℝ) ^ 2) *
            ENNReal.ofReal (mass / (n + 1 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal (lower * (n + 1 : ℝ) ^ 2) * μ (slab n) :=
        mul_le_mul_left' (hprob n) _
      _ = ∫⁻ _ in slab n, ENNReal.ofReal (lower * (n + 1 : ℝ) ^ 2) ∂μ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x in slab n, ENNReal.ofReal (f x) ∂μ :=
        setLIntegral_mono' (hslab n) (fun x hx ↦ ENNReal.ofReal_le_ofReal (hvalue n x hx))
      _ ≤ integral := setLIntegral_le_lintegral _ _
  by_contra hfinite
  have hreal (n : ℕ) : lower * mass * (n + 1 : ℝ) ≤ integral.toReal := by
    have hb := ENNReal.toReal_mono hfinite (hbound n)
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ lower * mass * (n + 1 : ℝ))] using hb
  obtain ⟨n, hn⟩ := exists_nat_gt (integral.toReal / (lower * mass))
  have hp : 0 < lower * mass := mul_pos hlower hmass
  have hlt : integral.toReal < lower * mass * (n : ℝ) := by
    exact (div_lt_iff₀ hp).mp hn |>.trans_eq (mul_comm _ _)
  have hb := hreal n
  nlinarith

/-- A tube around the source covariance hyperplane, with the hyperplane itself
removed. Its width is reciprocal in the truncation index. -/
def poleSlab (neighborhood : Set (K → ℝ)) (n : ℕ) : Set (K → ℝ) :=
  {effects | effects ∈ neighborhood ∧
    crossForm source sourceScore sourceCausal weights effects ≠ 0 ∧
    |crossForm source sourceScore sourceCausal weights effects| ≤ 1 / (n + 1 : ℝ)}

omit targetScore targetCausal [Fintype T] in
theorem poleSlab_measurable {neighborhood : Set (K → ℝ)}
    (hopen : IsOpen neighborhood) (n : ℕ) :
    MeasurableSet (poleSlab source sourceScore sourceCausal weights neighborhood n) := by
  have hc := (crossForm_effects_continuous source sourceScore sourceCausal weights).measurable
  exact hopen.measurableSet.inter
    ((measurableSet_eq_fun hc measurable_const).compl.inter
      (measurableSet_le hc.abs measurable_const))

omit sourceScore targetScore sourceCausal targetCausal weights in
private theorem inverse_square_lower {a lower : ℝ} (hlower : 0 < lower) (ha : a ≠ 0)
    (n : ℕ) (hsmall : |a| ≤ 1 / (n + 1 : ℝ)) :
    lower * (n + 1 : ℝ) ^ 2 ≤ lower / a ^ 2 := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have habs : |a| * (n + 1 : ℝ) ≤ 1 := (le_div_iff₀ hn).mp hsmall
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ |a| * (n + 1 : ℝ)) habs
  have hsq : a ^ 2 * (n + 1 : ℝ) ^ 2 ≤ 1 := by
    simpa only [← pow_two, mul_pow, sq_abs, one_pow] using hs
  apply (le_div_iff₀ (sq_pos_of_ne_zero ha)).mpr
  calc
    lower * (n + 1 : ℝ) ^ 2 * a ^ 2 = lower * (a ^ 2 * (n + 1 : ℝ) ^ 2) := by ring
    _ ≤ lower * 1 := mul_le_mul_of_nonneg_left hsq hlower.le
    _ = lower := mul_one _

/-- Local tube mass proportional to tube width turns the witnessed open-set
pole into an infinite nonnegative expectation under the supplied measure. This
is a conditional integrability criterion; it does not assert this mass bound
for the simulation or suppress conditioning on successful reports. -/
theorem ratio_lintegral_top_of_local_slab_mass (μ : Measure (K → ℝ))
    {effects₀ : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀)
    (hdensity : ∀ neighborhood : Set (K → ℝ), IsOpen neighborhood → effects₀ ∈ neighborhood →
      ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ, ENNReal.ofReal (mass / (n + 1 : ℝ)) ≤
        μ (poleSlab source sourceScore sourceCausal weights neighborhood n)) :
    (∫⁻ effects, ENNReal.ofReal
      ((formRatio source target sourceScore targetScore sourceCausal targetCausal
        weights effects).getD 0) ∂μ) = ∞ := by
  obtain ⟨lower, upper, hlower, _, neighborhood, hopen, hmem, hbound⟩ :=
    open_neighborhood_pole source target sourceScore targetScore sourceCausal targetCausal weights h
  obtain ⟨mass, hmass, hprob⟩ := hdensity neighborhood hopen hmem
  apply lintegral_top_of_quadratic_slabs μ _
    (poleSlab source sourceScore sourceCausal weights neighborhood)
    (poleSlab_measurable source sourceScore sourceCausal weights hopen)
    lower mass hlower hmass hprob
  intro n effects heffects
  obtain ⟨heffects, hc, hsmall⟩ := heffects
  obtain ⟨value, hvalue, hlo, _⟩ := hbound effects heffects hc
  rw [hvalue, Option.getD_some]
  exact (inverse_square_lower hlower hc n hsmall).trans hlo

end Descent.Portability.RatioPoleLaw

namespace Descent.Portability.RatioPoleLaw

open MeasureTheory FiniteReportLaw TrainingNoiseAccuracy GaussianEffectPortabilityLaw
open CalibrationLaw Filter Topology
open scoped ENNReal

variable {U I S T J K : Type*} [Fintype U] [Fintype I] [DecidableEq I]
  [Fintype S] [Fintype T] [Fintype J] [Fintype K]
  (design : FixedDesign U I S T J K)

omit [Fintype I] [DecidableEq I] [Fintype J] in
/-- The solved prevalence intercept and shared effect normalization remain in
this continuity statement for the actual calibrated label probability. -/
theorem calibrated_probability_continuous (i : I) :
    Continuous (fun effects ↦ caseProbability design effects i) := by
  unfold caseProbability
  simp_rw [caseProbability_eq_normalCDF]
  have hraw := linearScore_effects_continuous design.causalGenotype
  exact normalCDF_continuous.comp
    ((((calibratedIntercept_continuous design.cohort design.baseline design.epsilon
      design.epsilon_pos design.baseline_bound).comp hraw).add continuous_const).add
        ((standardize_coordinate_continuous design.cohort design.epsilon design.epsilon_pos
          (design.trainingIndex i)).comp hraw))

omit [Fintype J] in
/-- Every finite binary-label outcome has positive probability at every finite
causal-effect vector. This does not say that the learner succeeds on that outcome. -/
theorem calibrated_label_weight_pos (effects : K → ℝ) (outcome : I → Bool) :
    0 < (labelKernel design).weight effects outcome := by
  change 0 < ∏ i, if outcome i then caseProbability design effects i
    else 1 - caseProbability design effects i
  apply Finset.prod_pos
  intro i _
  have hp : 0 < caseProbability design effects i ∧ caseProbability design effects i < 1 := by
    unfold caseProbability
    rw [caseProbability_eq_normalCDF]
    exact normalCDF_mem_openUnitInterval _
  cases outcome i
  · exact sub_pos.mpr hp.2
  · exact hp.1

omit [Fintype J] in
theorem calibrated_label_weight_continuous (outcome : I → Bool) :
    Continuous (fun effects ↦ (labelKernel design).weight effects outcome) := by
  change Continuous (fun effects ↦ ∏ i, if outcome i then caseProbability design effects i
    else 1 - caseProbability design effects i)
  apply continuous_finset_prod
  intro i _
  cases outcome i
  · exact continuous_const.sub (calibrated_probability_continuous design i)
  · exact calibrated_probability_continuous design i

/-- A successful fixed learner outcome with a witnessed pole forces the full
Gaussian-effect/calibrated-label numerator to diverge if the Gaussian law has
the stated local tube mass. Label positivity is derived, not assumed. The tube
mass hypothesis and a realized learner witness still require separate proofs.
This pairwise theorem does not discard acceptance requirements for distance bins. -/
theorem gaussian_label_numerator_top_of_slab_mass (outcome : I → Bool) (weights : J → ℝ)
    (hlearn : design.learn outcome = some weights) {effects₀ : K → ℝ}
    (h : PoleWitness design.source design.target design.sourceGenotype design.targetGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s))
      (fun t ↦ design.causalGenotype (design.targetIndex t)) weights effects₀)
    (hdensity : ∀ neighborhood : Set (K → ℝ), IsOpen neighborhood → effects₀ ∈ neighborhood →
      ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ, ENNReal.ofReal (mass / (n + 1 : ℝ)) ≤
        effectLaw K (poleSlab design.source design.sourceGenotype
          (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights neighborhood n)) :
    (∫⁻ effects, ENNReal.ofReal (innerValue design effects) ∂effectLaw K) = ∞ := by
  obtain ⟨lower, upper, hlower, _, neighborhood, hopen, hmem, hbound⟩ :=
    open_neighborhood_pole design.source design.target design.sourceGenotype design.targetGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s))
      (fun t ↦ design.causalGenotype (design.targetIndex t)) weights h
  let labelLower := (labelKernel design).weight effects₀ outcome / 2
  have hlabel : 0 < labelLower := div_pos (calibrated_label_weight_pos design effects₀ outcome)
    (by norm_num)
  have hevent : ∀ᶠ effects in 𝓝 effects₀,
      labelLower < (labelKernel design).weight effects outcome :=
    (calibrated_label_weight_continuous design outcome).continuousAt.eventually
      (lt_mem_nhds (by dsimp [labelLower] at *; linarith))
  obtain ⟨labelNeighborhood, hsub, hlabelOpen, hlabelMem⟩ := mem_nhds_iff.mp hevent
  let smaller := neighborhood ∩ labelNeighborhood
  have hsmallerOpen : IsOpen smaller := hopen.inter hlabelOpen
  obtain ⟨mass, hmass, hprob⟩ := hdensity smaller hsmallerOpen ⟨hmem, hlabelMem⟩
  apply lintegral_top_of_quadratic_slabs (effectLaw K) (innerValue design)
    (poleSlab design.source design.sourceGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights smaller)
    (poleSlab_measurable design.source design.sourceGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights hsmallerOpen)
    (labelLower * lower) mass (mul_pos hlabel hlower) hmass hprob
  intro n effects heffects
  obtain ⟨⟨heffects, hlocalLabel⟩, hc, hsmall⟩ := heffects
  obtain ⟨value, hvalue, hlo, _⟩ := hbound effects heffects hc
  have hreport : report design effects outcome = some value := by
    simp only [report, hlearn, Option.bind_some, hvalue]
  have hvalueLower := (inverse_square_lower hlower hc n hsmall).trans hlo
  have hterm : (labelKernel design).weight effects outcome * value ≤ innerValue design effects := by
    have hsum := Finset.single_le_sum (s := (Finset.univ : Finset (I → Bool)))
      (f := fun other ↦ (labelKernel design).weight effects other *
        (report design effects other).getD 0)
      (fun other _ ↦ mul_nonneg ((labelKernel design).weight_nonneg effects other)
        (reportValue_nonneg design effects other)) (Finset.mem_univ outcome)
    simpa only [hreport, Option.getD_some, innerValue] using hsum
  calc
    labelLower * lower * (n + 1 : ℝ) ^ 2 =
        labelLower * (lower * (n + 1 : ℝ) ^ 2) := by ring
    _ ≤ (labelKernel design).weight effects outcome * value :=
      mul_le_mul (hsub hlocalLabel).le hvalueLower (by positivity)
        ((labelKernel design).weight_nonneg effects outcome)
    _ ≤ innerValue design effects := hterm

end Descent.Portability.RatioPoleLaw
