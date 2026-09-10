/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Descent.Layer

assert_below Descent.Decision Descent.Program

/-!
Calibration transport on arbitrary probability spaces. A measurable nonnegative
Radon--Nikodym density represents the change of predictor law. Conditional change
of measure and positivity of its denominator under the target law are derived,
not postulated; no finite partition or discrete predictor assumption is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReportCalibrationTransport

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {m : MeasurableSpace Ω}
  {r : Ω → ℝ≥0}

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- The density changes integrability by multiplication exactly. -/
theorem density_integrable_iff (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞))) (f : Ω → ℝ) :
    Integrable f ν ↔ Integrable (fun x ↦ (r x : ℝ) * f x) μ := by
  rw [hν]
  simpa only [NNReal.smul_def, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul hr (g := f) (μ := μ))

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- Set integrals transform under the same density, including score-measurable sets. -/
theorem density_setIntegral (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞))) (f : Ω → ℝ)
    {s : Set Ω} (hs : @MeasurableSet Ω m₀ s) :
    (∫ x in s, f x ∂ν) = ∫ x in s, (r x : ℝ) * f x ∂μ := by
  rw [hν]
  simpa only [NNReal.smul_def, smul_eq_mul] using
    (setIntegral_withDensity_eq_setIntegral_smul hr f hs (μ := μ))

/-- Weighted target conditional means equal weighted outcomes after conditioning
under the source law. This follows from the defining set-integral property. -/
theorem weighted_conditional_mean (hm : m ≤ m₀) (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞)))
    (f : Ω → ℝ) (hf : Integrable f ν) :
    (fun x ↦ ν[f | m] x * μ[(fun x ↦ (r x : ℝ)) | m] x) =ᵐ[μ]
      μ[(fun x ↦ (r x : ℝ) * f x) | m] := by
  have hw := (density_integrable_iff hr hν f).mp hf
  have hc := (density_integrable_iff hr hν (ν[f | m])).mp integrable_condExp
  have hd : Integrable (fun x ↦ (r x : ℝ)) μ := by
    simpa using (density_integrable_iff hr hν (fun _ ↦ (1 : ℝ))).mp (integrable_const 1)
  have he : μ[(fun x ↦ (r x : ℝ) * ν[f | m] x) | m] =ᵐ[μ]
      μ[(fun x ↦ (r x : ℝ) * f x) | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hw
    · intro s _ _
      exact integrable_condExp.integrableOn
    · intro s hs _
      rw [setIntegral_condExp hm hc hs,
        ← density_setIntegral hr hν (ν[f | m]) (hm s hs),
        setIntegral_condExp hm hf hs, density_setIntegral hr hν f (hm s hs)]
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
  have hp := condExp_mul_of_stronglyMeasurable_right
    (stronglyMeasurable_condExp (μ := ν) (f := f) (m := m)) hc hd
  filter_upwards [hp, he] with x hx he
  simpa only [Pi.mul_apply, mul_comm] using hx.symm.trans he

/-- The conditional density is strictly positive target-a.e.; zero-density
score fibers receive no target probability. -/
theorem conditional_density_pos_target_ae (hm : m ≤ m₀) (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞))) :
    ∀ᵐ x ∂ν, 0 < μ[(fun x ↦ (r x : ℝ)) | m] x := by
  let d := μ[(fun x ↦ (r x : ℝ)) | m]
  have hd : Integrable (fun x ↦ (r x : ℝ)) μ := by
    simpa using (density_integrable_iff hr hν (fun _ ↦ (1 : ℝ))).mp (integrable_const 1)
  have hset : MeasurableSet[m] {x | d x = 0} :=
    measurableSet_eq_fun stronglyMeasurable_condExp.measurable measurable_const
  have hz : (∫ x in {x | d x = 0}, (1 : ℝ) ∂ν) = 0 := by
    rw [density_setIntegral hr hν _ (hm _ hset)]
    simp only [mul_one]
    rw [← setIntegral_condExp hm hd hset]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact hx
  have hzero : ν {x | d x = 0} = 0 := by
    apply (measureReal_eq_zero_iff (μ := ν) (s := {x | d x = 0})).mp
    simpa using hz
  have hne : ∀ᵐ x ∂ν, d x ≠ 0 := by
    simpa only [ae_iff, not_not] using hzero
  have hac : ν ≪ μ := by rw [hν]; exact withDensity_absolutelyContinuous _ _
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ d x :=
    hac.ae_le (condExp_nonneg (Filter.Eventually.of_forall (fun x ↦ (r x).coe_nonneg)))
  filter_upwards [hne, hnonneg] with x hx hn
  exact lt_of_le_of_ne hn (Ne.symm hx)

/-- Conditional change of measure, with denominator positivity derived above. -/
theorem conditional_change_of_measure (hm : m ≤ m₀) (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞)))
    (f : Ω → ℝ) (hf : Integrable f ν) :
    ν[f | m] =ᵐ[ν] (fun x ↦ μ[(fun x ↦ (r x : ℝ) * f x) | m] x /
      μ[(fun x ↦ (r x : ℝ)) | m] x) := by
  have hac : ν ≪ μ := by rw [hν]; exact withDensity_absolutelyContinuous _ _
  have he := hac.ae_eq (weighted_conditional_mean hm hr hν f hf)
  filter_upwards [he, conditional_density_pos_target_ae hm hr hν] with x hx hp
  exact (eq_div_iff (ne_of_gt hp)).mpr hx

/-- Theorem 3: mechanism drift plus within-score risk reweighting. Products
are integrable precisely as stated, and all equalities hold target-a.e. -/
theorem calibration_transport (hm : m ≤ m₀) (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞)))
    (etaS etaT : Ω → ℝ) (_hS : Integrable etaS μ) (hST : Integrable etaS ν)
    (hT : Integrable etaT ν) :
    (fun x ↦ ν[etaT | m] x - μ[etaS | m] x) =ᵐ[ν]
      (fun x ↦
        μ[(fun x ↦ (r x : ℝ) * (etaT x - etaS x)) | m] x /
          μ[(fun x ↦ (r x : ℝ)) | m] x +
        (μ[(fun x ↦ (r x : ℝ) * etaS x) | m] x -
          μ[(fun x ↦ (r x : ℝ)) | m] x * μ[etaS | m] x) /
            μ[(fun x ↦ (r x : ℝ)) | m] x) := by
  have hac : ν ≪ μ := by rw [hν]; exact withDensity_absolutelyContinuous _ _
  have ht := (density_integrable_iff hr hν etaT).mp hT
  have hs := (density_integrable_iff hr hν etaS).mp hST
  have he := condExp_sub ht hs m
  have hd : μ[(fun x ↦ (r x : ℝ) * (etaT x - etaS x)) | m] =ᵐ[ν]
      (fun x ↦ μ[(fun x ↦ (r x : ℝ) * etaT x) | m] x -
        μ[(fun x ↦ (r x : ℝ) * etaS x) | m] x) := by
    simpa only [mul_sub] using hac.ae_eq he
  filter_upwards [conditional_change_of_measure hm hr hν etaT hT, hd,
    conditional_density_pos_target_ae hm hr hν] with x hx hd hp
  rw [hx, hd]
  field_simp
  ring

/-- The canonical finite nonnegative representative of the Radon--Nikodym density. -/
noncomputable def rnDensity (ν μ : Measure Ω) (x : Ω) : ℝ≥0 := (ν.rnDeriv μ x).toNNReal

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem rnDensity_measurable : @Measurable Ω ℝ≥0 m₀ _ (rnDensity ν μ) :=
  (Measure.measurable_rnDeriv ν μ).ennreal_toNNReal

/-- Absolute continuity alone supplies the density representation used above;
the finite representative differs only on a source-null set. -/
theorem rnDensity_represents (hac : ν ≪ μ) :
    ν = μ.withDensity (fun x ↦ (rnDensity ν μ x : ℝ≥0∞)) := by
  calc
    ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hac).symm
    _ = μ.withDensity (fun x ↦ (rnDensity ν μ x : ℝ≥0∞)) :=
      withDensity_congr_ae (coe_toNNReal_ae_eq (Measure.rnDeriv_lt_top ν μ)).symm

/-- Report Theorem 3 under its actual source/target absolute-continuity condition,
without supplying a density function or assuming denominator positivity. -/
theorem calibration_transport_of_absolutelyContinuous (hm : m ≤ m₀) (hac : ν ≪ μ)
    (etaS etaT : Ω → ℝ) (hS : Integrable etaS μ) (hST : Integrable etaS ν)
    (hT : Integrable etaT ν) :
    (fun x ↦ ν[etaT | m] x - μ[etaS | m] x) =ᵐ[ν]
      (fun x ↦
        μ[(fun x ↦ (rnDensity ν μ x : ℝ) * (etaT x - etaS x)) | m] x /
          μ[(fun x ↦ (rnDensity ν μ x : ℝ)) | m] x +
        (μ[(fun x ↦ (rnDensity ν μ x : ℝ) * etaS x) | m] x -
          μ[(fun x ↦ (rnDensity ν μ x : ℝ)) | m] x * μ[etaS | m] x) /
            μ[(fun x ↦ (rnDensity ν μ x : ℝ)) | m] x) :=
  calibration_transport hm rnDensity_measurable (rnDensity_represents hac) etaS etaT hS hST hT

/-- Mean invariance transfers the full conditional-mean score exactly. This is
stronger information than score-distribution or prevalence matching. -/
theorem invariant_conditional_mean_transfers (hm : m ≤ m₀) (eta : Ω → ℝ)
    (heta : StronglyMeasurable[m] eta) (hT : Integrable eta ν) :
    ν[eta | m] = eta := condExp_of_stronglyMeasurable hm heta hT

/-- Under conditional-mean invariance, zero within-score covariance is necessary
and sufficient for preserving the calibration curve, target-almost-everywhere. -/
theorem invariant_curve_iff_covariance_zero (hm : m ≤ m₀)
    (hr : @Measurable Ω ℝ≥0 m₀ _ r)
    (hν : ν = μ.withDensity (fun x ↦ (r x : ℝ≥0∞))) (eta : Ω → ℝ)
    (hS : Integrable eta μ) (hT : Integrable eta ν) :
    ν[eta | m] =ᵐ[ν] μ[eta | m] ↔
      (fun x ↦ μ[(fun x ↦ (r x : ℝ) * eta x) | m] x -
        μ[(fun x ↦ (r x : ℝ)) | m] x * μ[eta | m] x) =ᵐ[ν] (fun _ ↦ 0) := by
  have he := calibration_transport hm hr hν eta eta hS hT hT
  have hz : μ[(fun _ : Ω ↦ (0 : ℝ)) | m] = fun _ ↦ (0 : ℝ) := condExp_zero
  simp only [sub_self, mul_zero, hz, zero_div, zero_add] at he
  have hp := conditional_density_pos_target_ae hm hr hν
  constructor
  · intro hc
    filter_upwards [he, hp, hc] with x hx hp hc
    rw [hc, sub_self] at hx
    exact (div_eq_zero_iff.mp hx.symm).resolve_right (ne_of_gt hp)
  · intro hc
    filter_upwards [he, hc] with x hx hc
    rw [hc, zero_div] at hx
    exact sub_eq_zero.mp hx

end Descent.Portability.ReportCalibrationTransport
