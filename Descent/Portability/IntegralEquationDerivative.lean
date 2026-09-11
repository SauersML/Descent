/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateRealization
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

assert_below Descent.Decision Descent.Program

/-!
# The almost-everywhere derivative of the integrable-rate propagator

NOTE1 section 2.4 characterises the propagator of a rate history with integrable rates as a
continuous solution of `U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`, the Carathéodory form of `U' = A(t) U`
(`IntegrableRateRealization`). This module proves the differential equation itself at almost
every time.

For a generator path whose norm is integrable on `[0, T]` and any continuous solution of the
integral equation, the integrand `A U` is integrable on the horizon and so is each of its
entries. Lebesgue's differentiation theorem differentiates each entry of the indefinite integral
at almost every time, and at a time strictly inside the horizon the solution agrees with the
indefinite integral on a neighbourhood. So each entry of `U` has the corresponding entry of
`A(t) U(t)` as its derivative at almost every time of the horizon
(`ae_hasDerivAt_entry_of_integral_eq`): `U' = A(t) U` holds entrywise, which for matrices over a
finite index set is the equation itself.

The solution is also absolutely continuous on the horizon
(`absolutelyContinuousOnInterval_of_integral_eq`). Over finitely many disjoint subintervals its
total change is at most the integral of `‖A U‖` over their union, the union has measure at most
its total length, and the integral of an integrable function over a short set is small
(`exists_pos_setLIntegral_lt_of_measure_lt`). `integrableRateHistory_ae_hasDerivAt_entry` gives
both for the propagator of every rate history with integrable rate coordinates.

## Empirical status

None. The bodies here are real analysis about a stated linear integral equation and its
solution; no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IntegralEquationDerivative

open Coalescent
open MeasureTheory Filter Topology
open Descent.Portability.RateGeneratorLipschitz
open Descent.Portability.IntegrableRateRealization
open scoped Matrix.Norms.Operator

noncomputable section

/-- NOTE1 section 2.4, `U' = A(t) U` at almost every time. Assumes: a generator path with
integrable norm on `[0, T]` and a continuous solution of `U(t) = 1 + ∫₀ᵗ A U` on the horizon.
Then at almost every time strictly inside the horizon each entry of `U` is differentiable, with
derivative the corresponding entry of `A(t) U(t)`. -/
theorem ae_hasDerivAt_entry_of_integral_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A U : ℝ → Matrix ι ι ℝ} {T : ℝ} (hA : IntervalIntegrable A volume 0 T) (hU : Continuous U)
    (hequation : ∀ t ∈ Set.Icc 0 T, U t = 1 + ∫ s in (0 : ℝ)..t, A s * U s) :
    ∀ᵐ t, t ∈ Set.Ioo 0 T → ∀ row column : ι,
      HasDerivAt (fun time ↦ U time row column) ((A t * U t) row column) t := by
  have hproduct : IntervalIntegrable (fun s ↦ A s * U s) volume 0 T :=
    hA.mul_continuousOn hU.continuousOn
  have hentry : ∀ row column : ι,
      IntervalIntegrable (fun s ↦ (A s * U s) row column) volume 0 T := fun row column ↦
    ⟨(LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ row column)).integrable_comp
        hproduct.1,
      (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ row column)).integrable_comp
        hproduct.2⟩
  have hall : ∀ᵐ t, ∀ row column : ι, t ∈ Set.uIcc 0 T → ∀ c ∈ Set.uIcc 0 T,
      HasDerivAt (fun x ↦ ∫ s in c..x, (A s * U s) row column) ((A t * U t) row column) t := by
    rw [ae_all_iff]
    intro row
    rw [ae_all_iff]
    intro column
    exact (hentry row column).ae_hasDerivAt_integral
  refine hall.mono fun t hderivative hmem row column ↦ ?_
  have hT : 0 ≤ T := (hmem.1.trans hmem.2).le
  have htime : t ∈ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hT]
    exact Set.Ioo_subset_Icc_self hmem
  refine ((hderivative row column htime 0 Set.left_mem_uIcc).const_add
    ((1 : Matrix ι ι ℝ) row column)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with time hnear
  have hsub : IntervalIntegrable (fun s ↦ A s * U s) volume 0 time :=
    hproduct.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hnear.1.le hnear.2.le))
  have hcomm := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ row column)).intervalIntegral_comp_comm hsub
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.entryLinearMap_apply] at hcomm
  rw [hequation time (Set.Ioo_subset_Icc_self hnear), Matrix.add_apply, hcomm]

/-- NOTE1 section 2.4, absolute continuity of the propagator. Assumes: a horizon `0 ≤ T`, a
generator path with integrable norm on `[0, T]` and a continuous solution of
`U(t) = 1 + ∫₀ᵗ A U` on the horizon. Then `U` is absolutely continuous on `[0, T]`: over finitely
many disjoint subintervals its total change is at most the integral of `‖A U‖` over their union,
and that integral is small whenever the union is short. -/
theorem absolutelyContinuousOnInterval_of_integral_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A U : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T)
    (hU : Continuous U)
    (hequation : ∀ t ∈ Set.Icc 0 T, U t = 1 + ∫ s in (0 : ℝ)..t, A s * U s) :
    AbsolutelyContinuousOnInterval U 0 T := by
  have hproduct : IntervalIntegrable (fun s ↦ A s * U s) volume 0 T :=
    hA.mul_continuousOn hU.continuousOn
  have hfinite : ∫⁻ s in Set.Ioc 0 T, ‖A s * U s‖ₑ ≠ ⊤ := hproduct.1.hasFiniteIntegral.ne
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt hfinite (ENNReal.ofReal_pos.mpr hε).ne'
  have hcap : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hcappos : 0 < (min δ 1).toReal := ENNReal.toReal_pos (lt_min hδ zero_lt_one).ne' hcap
  refine ⟨(min δ 1).toReal, hcappos, fun E hE hlength ↦ ?_⟩
  have hIcc : ∀ t ∈ Set.uIcc 0 T, t ∈ Set.Icc 0 T := fun t ht ↦ by
    rwa [Set.uIcc_of_le hT] at ht
  have hsubinterval : ∀ t ∈ Set.uIcc 0 T, IntervalIntegrable (fun s ↦ A s * U s) volume 0 t :=
    fun t ht ↦ hproduct.mono_set (Set.uIcc_subset_uIcc_left ht)
  have hregion : ∀ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2 ⊆ Set.Ioc 0 T := by
    intro i hi s hs
    have hfirst := hIcc _ (hE.1 i hi).1
    have hsecond := hIcc _ (hE.1 i hi).2
    rcases Set.mem_uIoc.mp hs with ⟨hlow, hhigh⟩ | ⟨hlow, hhigh⟩
    · exact ⟨by linarith [hfirst.1], by linarith [hsecond.2]⟩
    · exact ⟨by linarith [hsecond.1], by linarith [hfirst.2]⟩
  have hpoint : ∀ i ∈ Finset.range E.1, dist (U (E.2 i).1) (U (E.2 i).2) ≤
      (∫⁻ s in Set.uIoc (E.2 i).1 (E.2 i).2, ‖A s * U s‖ₑ).toReal := by
    intro i hi
    have hfirst := (hE.1 i hi).1
    have hsecond := (hE.1 i hi).2
    rw [dist_eq_norm, hequation _ (hIcc _ hfirst), hequation _ (hIcc _ hsecond),
      add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hsubinterval _ hfirst) (hsubinterval _ hsecond)]
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans (le_of_eq ?_)
    rw [Set.uIoc_comm, integral_norm_eq_lintegral_enorm
      (hproduct.1.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (hregion i hi) le_rfl))]
  have hunion : ∑ i ∈ Finset.range E.1,
      (∫⁻ s in Set.uIoc (E.2 i).1 (E.2 i).2, ‖A s * U s‖ₑ).toReal =
        (∫⁻ s in ⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2,
          ‖A s * U s‖ₑ).toReal := by
    rw [lintegral_biUnion_finset hE.2 (fun i _ ↦ measurableSet_uIoc), ENNReal.toReal_sum]
    intro i hi
    exact ne_top_of_le_ne_top hfinite (lintegral_mono_set (hregion i hi))
  have hsubset : (⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2) ⊆ Set.Ioc 0 T :=
    Set.iUnion₂_subset hregion
  have hmeasurable : MeasurableSet (⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2) :=
    Finset.measurableSet_biUnion _ fun i _ ↦ measurableSet_uIoc
  have hshort : volume.restrict (Set.Ioc 0 T)
      (⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2) < δ := by
    rw [Measure.restrict_apply' measurableSet_Ioc, Set.inter_eq_left.mpr hsubset]
    have hlengths : ∑ i ∈ Finset.range E.1, |(E.2 i).2 - (E.2 i).1| < (min δ 1).toReal := by
      simpa [Real.dist_eq, abs_sub_comm] using hlength
    calc volume (⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2)
        ≤ ∑ i ∈ Finset.range E.1, volume (Set.uIoc (E.2 i).1 (E.2 i).2) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ Finset.range E.1, ENNReal.ofReal |(E.2 i).2 - (E.2 i).1| :=
          Finset.sum_le_sum fun i _ ↦
            (measure_mono Set.uIoc_subset_uIcc).trans_eq Real.volume_interval
      _ = ENNReal.ofReal (∑ i ∈ Finset.range E.1, |(E.2 i).2 - (E.2 i).1|) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ ↦ abs_nonneg _).symm
      _ < ENNReal.ofReal (min δ 1).toReal := (ENNReal.ofReal_lt_ofReal_iff hcappos).mpr hlengths
      _ = min δ 1 := ENNReal.ofReal_toReal hcap
      _ ≤ δ := min_le_left _ _
  have hintegral := hsmall _ hshort
  rw [Measure.restrict_restrict hmeasurable, Set.inter_eq_left.mpr hsubset] at hintegral
  calc ∑ i ∈ Finset.range E.1, dist (U (E.2 i).1) (U (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1,
          (∫⁻ s in Set.uIoc (E.2 i).1 (E.2 i).2, ‖A s * U s‖ₑ).toReal :=
        Finset.sum_le_sum hpoint
    _ = (∫⁻ s in ⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2,
          ‖A s * U s‖ₑ).toReal := hunion
    _ < ε := ENNReal.toReal_lt_of_lt_ofReal hintegral

/-- NOTE1 section 2.4 for rate histories with integrable rates, in differential form. Assumes:
rate coordinates integrable on `[0, T]`. The propagator of the rate history, the continuous
solution of the integral equation with the corpus generator, is absolutely continuous on the
horizon and satisfies `U' = A(t) U` entrywise at almost every time of the horizon. -/
theorem integrableRateHistory_ae_hasDerivAt_entry {D : ℕ} (rates : ℝ → ManyDemeLDRates D)
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T) :
    ∃ propagator : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ,
      Continuous propagator ∧
      (∀ t ∈ Set.Icc 0 T, propagator t =
        1 + ∫ s in (0 : ℝ)..t, augmentedLowOrderLDGenerator (rates s) * propagator s) ∧
      AbsolutelyContinuousOnInterval propagator 0 T ∧
      ∀ᵐ t, t ∈ Set.Ioo 0 T → ∀ row column,
        HasDerivAt (fun time ↦ propagator time row column)
          ((augmentedLowOrderLDGenerator (rates t) * propagator t) row column) t := by
  obtain ⟨propagator, hcontinuous, hequation, _, _⟩ :=
    integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable
  have hgenerator := intervalIntegrable_augmentedLowOrderLDGenerator hintegrable
  exact ⟨propagator, hcontinuous, hequation,
    absolutelyContinuousOnInterval_of_integral_eq hT hgenerator hcontinuous hequation,
    ae_hasDerivAt_entry_of_integral_eq hgenerator hcontinuous hequation⟩

end

end Descent.Portability.IntegralEquationDerivative
