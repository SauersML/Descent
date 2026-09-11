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
finite index set is the equation itself. `integrableRateHistory_ae_hasDerivAt_entry` applies this
to the propagator of every rate history with integrable rate coordinates.

Not formalised yet here: absolute continuity of the propagator on the horizon.

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

/-- NOTE1 section 2.4 for rate histories with integrable rates, in differential form. Assumes:
rate coordinates integrable on `[0, T]`. The propagator of the rate history, the continuous
solution of the integral equation with the corpus generator, satisfies `U' = A(t) U` entrywise
at almost every time of the horizon. -/
theorem integrableRateHistory_ae_hasDerivAt_entry {D : ℕ} (rates : ℝ → ManyDemeLDRates D)
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T) :
    ∃ propagator : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ,
      Continuous propagator ∧
      (∀ t ∈ Set.Icc 0 T, propagator t =
        1 + ∫ s in (0 : ℝ)..t, augmentedLowOrderLDGenerator (rates s) * propagator s) ∧
      ∀ᵐ t, t ∈ Set.Ioo 0 T → ∀ row column,
        HasDerivAt (fun time ↦ propagator time row column)
          ((augmentedLowOrderLDGenerator (rates t) * propagator t) row column) t := by
  obtain ⟨propagator, hcontinuous, hequation, _, _⟩ :=
    integrableRateHistory_preserves_locusExchangeable_realization rates hT hintegrable
  exact ⟨propagator, hcontinuous, hequation, ae_hasDerivAt_entry_of_integral_eq
    (intervalIntegrable_augmentedLowOrderLDGenerator hintegrable) hcontinuous hequation⟩

end

end Descent.Portability.IntegralEquationDerivative
