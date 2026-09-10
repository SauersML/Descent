/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RatioPoleLaw
import Mathlib.MeasureTheory.Integral.Marginal

assert_below Descent.Decision Descent.Program

/-!
Positive local mass of thin linear slabs under a finite product of standard
Gaussian measures. A single nonzero coefficient supplies a coordinate graph;
Tonelli integration over that coordinate gives a bound proportional to width.
The resulting ratio theorem remains conditional on a realized matrix/learner
witness and makes no claim about the simulation's fitted weights or distance bins.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianSlabLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory GaussianEffectPortabilityLaw RatioPoleLaw
open Filter Topology Set
open scoped ENNReal NNReal

variable {K : Type*} [Fintype K]

noncomputable def linearForm (a x : K → ℝ) : ℝ := ∑ k, a k * x k

theorem linearForm_continuous (a : K → ℝ) : Continuous (linearForm a) := by
  apply continuous_finset_sum
  intro k _
  exact continuous_const.mul (continuous_apply k)

variable [DecidableEq K]

theorem linearForm_update (a x : K → ℝ) (k : K) (z : ℝ) :
    linearForm a (Function.update x k z) = linearForm a x + a k * (z - x k) := by
  unfold linearForm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add _ (fun j ↦ a j * x j) (Finset.mem_univ k)]
  have hsum : (∑ j ∈ Finset.univ.erase k, a j * Function.update x k z j) =
      ∑ j ∈ Finset.univ.erase k, a j * x j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hsum, Function.update_self]
  ring

noncomputable def graphCenter (a : K → ℝ) (k : K) (x : K → ℝ) : ℝ :=
  x k - linearForm a x / a k

noncomputable def graphPoint (a : K → ℝ) (k : K) (x : K → ℝ) (t : ℝ) : K → ℝ :=
  Function.update x k (graphCenter a k x + t)

theorem graphCenter_update (a : K → ℝ) (k : K) (ha : a k ≠ 0) (x : K → ℝ) (z : ℝ) :
    graphCenter a k (Function.update x k z) = graphCenter a k x := by
  simp only [graphCenter, Function.update_self, linearForm_update]
  field_simp
  ring

theorem graphPoint_update (a : K → ℝ) (k : K) (ha : a k ≠ 0)
    (x : K → ℝ) (z t : ℝ) :
    graphPoint a k (Function.update x k z) t = graphPoint a k x t := by
  simp only [graphPoint, graphCenter_update a k ha, Function.update_idem]

theorem linearForm_graphPoint (a : K → ℝ) (k : K) (ha : a k ≠ 0)
    (x : K → ℝ) (t : ℝ) : linearForm a (graphPoint a k x t) = a k * t := by
  rw [graphPoint, linearForm_update]
  unfold graphCenter
  field_simp
  ring

omit [DecidableEq K] in
theorem graphCenter_continuous (a : K → ℝ) (k : K) : Continuous (graphCenter a k) :=
  (continuous_apply k).sub ((linearForm_continuous a).div_const _)

theorem graphPoint_continuous (a : K → ℝ) (k : K) :
    Continuous (fun p : (K → ℝ) × ℝ ↦ graphPoint a k p.1 p.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j = k
  · subst j
    simpa only [graphPoint, Function.update_self] using
      ((graphCenter_continuous a k).comp continuous_fst).add continuous_snd
  · simpa only [graphPoint, Function.update_of_ne hj] using
      (continuous_apply j).comp continuous_fst

private theorem standardDensity_continuous : Continuous (gaussianPDFReal 0 1) := by
  unfold gaussianPDFReal
  fun_prop

private instance standardGaussian_openPos : IsOpenPosMeasure (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure

instance effectLaw_openPos : IsOpenPosMeasure (effectLaw K) := by
  unfold effectLaw
  infer_instance

/-- A cylinder independent of the selected coordinate admits uniformly bounded
positive-density graph segments inside any prescribed open neighborhood. -/
theorem local_cylinder (a x₀ : K → ℝ) (k : K) (ha : a k ≠ 0)
    (hzero : linearForm a x₀ = 0) (U : Set (K → ℝ)) (hU : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ (B : Set (K → ℝ)) (radius density : ℝ),
      IsOpen B ∧ x₀ ∈ B ∧ 0 < radius ∧ 0 < density ∧ |a k| * radius ≤ 1 ∧
      (∀ x z, Function.update x k z ∈ B ↔ x ∈ B) ∧
      ∀ x ∈ B, ∀ t : ℝ, 0 < t → t < radius →
        graphPoint a k x t ∈ U ∧ density ≤ gaussianPDFReal 0 1 (graphCenter a k x + t) := by
  have hcenter : graphCenter a k x₀ = x₀ k := by simp [graphCenter, hzero]
  have hpoint : graphPoint a k x₀ 0 = x₀ := by simp [graphPoint, hcenter]
  let density := gaussianPDFReal 0 1 (x₀ k) / 2
  have hdensity : 0 < density := div_pos (gaussianPDFReal_pos 0 1 (x₀ k) one_ne_zero)
    (by norm_num)
  have hevent : ∀ᶠ p : (K → ℝ) × ℝ in 𝓝 (x₀, 0),
      graphPoint a k p.1 p.2 ∈ U ∧
      density < gaussianPDFReal 0 1 (graphCenter a k p.1 + p.2) := by
    have hfirst := (graphPoint_continuous a k).continuousAt (x := (x₀, (0 : ℝ))) |>.eventually
      (hU.mem_nhds (show graphPoint a k x₀ 0 ∈ U by rw [hpoint]; exact hx₀))
    have hsecond := (standardDensity_continuous.comp
      (((graphCenter_continuous a k).comp continuous_fst).add continuous_snd)).continuousAt
      (x := (x₀, (0 : ℝ)))
    have hgap : density < gaussianPDFReal 0 1 (graphCenter a k x₀ + 0) := by
      rw [hcenter, add_zero]
      dsimp [density] at *
      linarith
    exact hfirst.and (hsecond.eventually (lt_mem_nhds hgap))
  obtain ⟨V, W, hV, hxV, hW, hzeroW, hsub⟩ := mem_nhds_prod_iff'.mp hevent
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hW 0 hzeroW
  let radius := min epsilon (1 / (|a k| + 1))
  have hradius : 0 < radius := lt_min hepsilon (by positivity)
  let B := {x : K → ℝ | Function.update x k (x₀ k) ∈ V}
  have hBopen : IsOpen B := hV.preimage (by
    apply continuous_pi
    intro j
    by_cases hj : j = k
    · subst j; simpa only [Function.update_self] using continuous_const
    · simpa only [Function.update_of_ne hj] using continuous_apply j)
  refine ⟨B, radius, density, hBopen, ?_, hradius, hdensity, ?_, ?_, ?_⟩
  · simpa [B] using hxV
  · have hb : radius ≤ 1 / (|a k| + 1) := min_le_right _ _
    have hp : 0 < |a k| + 1 := by positivity
    have hmul := (le_div_iff₀ hp).mp hb
    nlinarith [abs_nonneg (a k)]
  · intro x z
    simp only [B, Set.mem_setOf_eq, Function.update_idem]
  · intro x hx t ht htr
    have htW : t ∈ W := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
      exact htr.trans_le (min_le_left _ _))
    obtain ⟨hinside, hpdf⟩ := hsub (show (Function.update x k (x₀ k), t) ∈ V ×ˢ W from ⟨hx, htW⟩)
    rw [graphPoint_update a k ha] at hinside
    rw [graphCenter_update a k ha] at hpdf
    exact ⟨hinside, hpdf.le⟩

noncomputable def linearSlab (a : K → ℝ) (U : Set (K → ℝ)) (n : ℕ) : Set (K → ℝ) :=
  {x | x ∈ U ∧ linearForm a x ≠ 0 ∧ |linearForm a x| ≤ 1 / (n + 1 : ℝ)}

omit [DecidableEq K] in
theorem linearSlab_measurable (a : K → ℝ) (U : Set (K → ℝ)) (hU : IsOpen U) (n : ℕ) :
    MeasurableSet (linearSlab a U n) := by
  have hc := (linearForm_continuous a).measurable
  exact hU.measurableSet.inter ((measurableSet_eq_fun hc measurable_const).compl.inter
    (measurableSet_le hc.abs measurable_const))

/-- Conditional on all other coordinates, a moving interval has Gaussian mass
bounded below by density times length and lies inside the desired slab. -/
theorem section_lower (a : K → ℝ) (k : K) (ha : a k ≠ 0) (x : K → ℝ)
    (U : Set (K → ℝ)) (radius density : ℝ) (hradius : 0 < radius) (hdensity : 0 < density)
    (hscale : |a k| * radius ≤ 1)
    (hlocal : ∀ t : ℝ, 0 < t → t < radius →
      graphPoint a k x t ∈ U ∧ density ≤ gaussianPDFReal 0 1 (graphCenter a k x + t))
    (n : ℕ) :
    ENNReal.ofReal (density * radius / (n + 1 : ℝ)) ≤
      gaussianReal 0 1 {z | Function.update x k z ∈ linearSlab a U n} := by
  let center := graphCenter a k x
  let width := radius / (n + 1 : ℝ)
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hn1 : 1 ≤ (n + 1 : ℝ) := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hwidth : 0 < width := div_pos hradius hn
  have hwidth_le : width ≤ radius := div_le_self hradius.le hn1
  have htime {z : ℝ} (hz : z ∈ Ioo center (center + width)) :
      0 < z - center ∧ z - center < radius := by
    exact ⟨sub_pos.mpr hz.1, (sub_lt_iff_lt_add'.mpr hz.2).trans_le hwidth_le⟩
  have hpoint (z : ℝ) : graphPoint a k x (z - center) = Function.update x k z := by
    simp only [graphPoint, center, add_sub_cancel]
  have hinside : Ioo center (center + width) ⊆
      {z | Function.update x k z ∈ linearSlab a U n} := by
    intro z hz
    obtain ⟨ht, htr⟩ := htime hz
    have hlocalz := hlocal (z - center) ht htr
    have hcross : linearForm a (Function.update x k z) = a k * (z - center) := by
      rw [← hpoint z, linearForm_graphPoint a k ha]
    refine ⟨by rw [← hpoint z]; exact hlocalz.1, ?_, ?_⟩
    · rw [hcross]
      exact mul_ne_zero ha ht.ne'
    · rw [hcross, abs_mul, abs_of_pos ht]
      calc
        |a k| * (z - center) ≤ |a k| * width :=
          mul_le_mul_of_nonneg_left (sub_lt_iff_lt_add'.mpr hz.2).le (abs_nonneg _)
        _ = (|a k| * radius) / (n + 1 : ℝ) := by dsimp [width]; rw [mul_div_assoc]
        _ ≤ 1 / (n + 1 : ℝ) := div_le_div_of_nonneg_right hscale hn.le
  calc
    ENNReal.ofReal (density * radius / (n + 1 : ℝ)) =
        ENNReal.ofReal density * volume (Ioo center (center + width)) := by
      rw [Real.volume_Ioo, add_sub_cancel_left, ← ENNReal.ofReal_mul hdensity.le]
      congr 1
      exact mul_div_assoc _ _ _
    _ = ∫⁻ _ in Ioo center (center + width), ENNReal.ofReal density := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ z in Ioo center (center + width), gaussianPDF 0 1 z := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro z hz
      obtain ⟨ht, htr⟩ := htime hz
      have hb := (hlocal (z - center) ht htr).2
      simpa only [center, add_sub_cancel, gaussianPDF] using ENNReal.ofReal_le_ofReal hb
    _ = gaussianReal 0 1 (Ioo center (center + width)) :=
      (gaussianReal_apply 0 one_ne_zero _).symm
    _ ≤ gaussianReal 0 1 {z | Function.update x k z ∈ linearSlab a U n} := measure_mono hinside

/-- Tonelli integration of the positive conditional interval over a fixed open
cylinder gives a positive mass coefficient independent of slab width. -/
theorem local_slab_mass (a x₀ : K → ℝ) (k : K) (ha : a k ≠ 0)
    (hzero : linearForm a x₀ = 0) (U : Set (K → ℝ)) (hU : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ,
      ENNReal.ofReal (mass / (n + 1 : ℝ)) ≤ effectLaw K (linearSlab a U n) := by
  obtain ⟨B, radius, density, hB, hxB, hradius, hdensity, hscale, hinvariant, hlocal⟩ :=
    local_cylinder a x₀ k ha hzero U hU hx₀
  have hmassB : 0 < (effectLaw K).real B :=
    ENNReal.toReal_pos (hB.measure_ne_zero (effectLaw K) ⟨x₀, hxB⟩)
      (measure_ne_top _ _)
  refine ⟨density * radius * (effectLaw K).real B, by positivity, ?_⟩
  intro n
  let c := ENNReal.ofReal (density * radius / (n + 1 : ℝ))
  have hslab := linearSlab_measurable a U hU n
  have hcompare : c * effectLaw K B ≤ effectLaw K (linearSlab a U n) := by
    rw [← lintegral_indicator_const hB.measurableSet,
      ← lintegral_indicator_one hslab]
    change (∫⁻ x, B.indicator (fun _ ↦ c) x ∂Measure.pi (fun _ : K ↦ gaussianReal 0 1)) ≤
      ∫⁻ x, (linearSlab a U n).indicator 1 x ∂Measure.pi (fun _ : K ↦ gaussianReal 0 1)
    apply lintegral_le_of_lmarginal_le {k}
      (measurable_const.indicator hB.measurableSet) (measurable_one.indicator hslab)
    rw [lmarginal_singleton, lmarginal_singleton]
    intro x
    dsimp only
    by_cases hx : x ∈ B
    · have hleft : (∫⁻ z, B.indicator (fun _ ↦ c) (Function.update x k z)
          ∂gaussianReal 0 1) = c := by
        have heq : (fun z : ℝ ↦ B.indicator (fun _ ↦ c) (Function.update x k z)) =
            fun _ : ℝ ↦ c := by
          funext z
          exact Set.indicator_of_mem ((hinvariant x z).mpr hx) _
        rw [heq, lintegral_const, measure_univ, mul_one]
      rw [hleft]
      have hsection : MeasurableSet {z : ℝ | Function.update x k z ∈ linearSlab a U n} :=
        hslab.preimage (measurable_pi_iff.mpr (by
          intro j
          by_cases hj : j = k
          · subst j; simpa only [Function.update_self] using measurable_id
          · simpa only [Function.update_of_ne hj] using measurable_const))
      have hright : (∫⁻ z, (linearSlab a U n).indicator 1 (Function.update x k z)
          ∂gaussianReal 0 1) = gaussianReal 0 1
          {z : ℝ | Function.update x k z ∈ linearSlab a U n} := by
        simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_setOf_eq] using
          lintegral_indicator_one (μ := gaussianReal 0 1) hsection
      rw [hright]
      exact section_lower a k ha x U radius density hradius hdensity hscale (hlocal x hx) n
    · have hleft : (∫⁻ z, B.indicator (fun _ ↦ c) (Function.update x k z)
          ∂gaussianReal 0 1) = 0 := by
        have heq : (fun z : ℝ ↦ B.indicator (fun _ ↦ c) (Function.update x k z)) =
            fun _ : ℝ ↦ 0 := by
          funext z
          exact Set.indicator_of_notMem (fun hz ↦ hx ((hinvariant x z).mp hz)) _
        rw [heq, lintegral_zero]
      rw [hleft]
      exact zero_le _
  calc
    ENNReal.ofReal (density * radius * (effectLaw K).real B / (n + 1 : ℝ)) =
        c * effectLaw K B := by
      rw [← ofReal_measureReal (μ := effectLaw K) (s := B),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ effectLaw K (linearSlab a U n) := hcompare

omit [DecidableEq K] in
/-- Nontriviality of the finite linear form supplies the nonzero coordinate
needed for the local Gaussian slab estimate. -/
theorem nontrivial_local_slab_mass (a x₀ : K → ℝ)
    (hnontrivial : ∃ direction, linearForm a direction ≠ 0) (hzero : linearForm a x₀ = 0)
    (U : Set (K → ℝ)) (hU : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ,
      ENNReal.ofReal (mass / (n + 1 : ℝ)) ≤ effectLaw K (linearSlab a U n) := by
  classical
  have hcoordinate : ∃ k, a k ≠ 0 := by
    by_contra! hzeroa
    obtain ⟨direction, hdirection⟩ := hnontrivial
    exact hdirection (by simp only [linearForm, hzeroa, zero_mul, Finset.sum_const_zero])
  obtain ⟨k, hk⟩ := hcoordinate
  exact local_slab_mass a x₀ k hk hzero U hU hx₀

end Descent.Portability.GaussianSlabLaw

namespace Descent.Portability.GaussianSlabLaw

open MeasureTheory GaussianEffectPortabilityLaw RatioPoleLaw SimulationAccuracy
open PortabilityRatioGeometry
open scoped ENNReal

variable {S T J K : Type*} [Fintype S] [Fintype T] [Fintype J] [Fintype K]

omit [Fintype T] in
/-- The Gaussian mass premise of the ratio pole law follows from the actual
finite covariance coefficient vector, with no density hypothesis remaining. -/
theorem crossForm_local_slab_mass (source : FiniteReportLaw S)
    (sourceScore : S → J → ℝ) (sourceCausal : S → K → ℝ) (weights : J → ℝ)
    (effects₀ : K → ℝ)
    (hnontrivial : ∃ direction, crossForm source sourceScore sourceCausal weights direction ≠ 0)
    (hzero : crossForm source sourceScore sourceCausal weights effects₀ = 0)
    (U : Set (K → ℝ)) (hU : IsOpen U) (hx₀ : effects₀ ∈ U) :
    ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ, ENNReal.ofReal (mass / (n + 1 : ℝ)) ≤
      effectLaw K (poleSlab source sourceScore sourceCausal weights U n) := by
  have hn : ∃ direction,
      linearForm (covarianceVector source sourceScore sourceCausal weights) direction ≠ 0 := by
    simpa only [linearForm, crossForm_eq_dot] using hnontrivial
  have hz : linearForm (covarianceVector source sourceScore sourceCausal weights) effects₀ = 0 := by
    simpa only [linearForm, crossForm_eq_dot] using hzero
  simpa only [linearSlab, poleSlab, linearForm, crossForm_eq_dot] using
    nontrivial_local_slab_mass (covarianceVector source sourceScore sourceCausal weights)
      effects₀ hn hz U hU hx₀

/-- A witnessed nonaligned pole is nonintegrable under the full finite product
Gaussian effect distribution. Applicability requires the stated matrix witness. -/
theorem witnessed_ratio_gaussian_integral_top
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceScore : S → J → ℝ) (targetScore : T → J → ℝ)
    (sourceCausal : S → K → ℝ) (targetCausal : T → K → ℝ)
    (weights : J → ℝ) {effects₀ : K → ℝ}
    (h : PoleWitness source target sourceScore targetScore sourceCausal targetCausal
      weights effects₀) :
    (∫⁻ effects, ENNReal.ofReal ((formRatio source target sourceScore targetScore sourceCausal
      targetCausal weights effects).getD 0) ∂effectLaw K) = ∞ := by
  apply ratio_lintegral_top_of_local_slab_mass source target sourceScore targetScore
    sourceCausal targetCausal weights (effectLaw K) h
  exact crossForm_local_slab_mass source sourceScore sourceCausal weights effects₀
    h.source_cross_nontrivial h.source_cross_zero

/-- For the calibrated-label law, only a successful fixed learner outcome and
its covariance witness remain as hypotheses. No Gaussian density assumption is
supplied. This does not assert such a witness for the simulator's fitted score. -/
theorem witnessed_gaussian_label_numerator_top {U I : Type*} [Fintype U] [Fintype I]
    [DecidableEq I] (design : FixedDesign U I S T J K)
    (outcome : I → Bool) (weights : J → ℝ) (hlearn : design.learn outcome = some weights)
    {effects₀ : K → ℝ}
    (h : PoleWitness design.source design.target design.sourceGenotype design.targetGenotype
      (fun s ↦ design.causalGenotype (design.sourceIndex s))
      (fun t ↦ design.causalGenotype (design.targetIndex t)) weights effects₀) :
    (∫⁻ effects, ENNReal.ofReal (innerValue design effects) ∂effectLaw K) = ∞ := by
  apply gaussian_label_numerator_top_of_slab_mass design outcome weights hlearn h
  exact crossForm_local_slab_mass design.source design.sourceGenotype
    (fun s ↦ design.causalGenotype (design.sourceIndex s)) weights effects₀
    h.source_cross_nontrivial h.source_cross_zero

end Descent.Portability.GaussianSlabLaw
