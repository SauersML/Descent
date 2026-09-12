/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableRateRealization
import Descent.Portability.NonnegativeCoalescenceRealization

assert_below Descent.Decision Descent.Program

/-!
# Realizability under integrable rate histories at nonnegative coalescence

NOTE1 section 2.4 lets the rates vary in time, and NOTE1 section 2.2 allows `c_i ≥ 0`.
`Descent.Portability.IntegrableRateRealization` proves the time-varying theorem for corpus rate
laws, whose coalescence is strictly positive, and
`Descent.Portability.NonnegativeCoalescenceRealization` proves the constant-rate theorem at
nonnegative coalescence. This module proves both at once: a rate history
`rates : ℝ → NonnegativeLDRates D` whose rate coordinates are integrable on `[0, T]`, including
one in which some deme has no coalescence on a set of positive measure or at all times.

The generator at time `s` is `(rates s).generator`, the linear map
`RateGeneratorLipschitz.generatorLinearMap` at the rate coordinates, so the generator path is
integrable (`intervalIntegrable_nonnegativeGenerator`). The approximation raises every coalescence
rate by `ε` (`rateCoordinates_perturb`), which gives a corpus rate history, and then approximates
that corpus history in `L¹` by one with continuous rates.
`exists_continuous_rates_near_nonnegative` bounds the total distance by
`ε (1 + T + T ‖u‖)`, where `u` is the unit-coalescence direction.

`exists_nonnegativeIntegrablePropagator` is the existence half. Along `ε = 1 / (k + 1)` the
generator paths of the continuous approximations are within a fixed multiple of `ε` of the
limit generator in `L¹`, so
`IntegrableRateRealization.exists_integral_solution_of_continuous_approximation` gives a
continuous solution of `U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`, and the approximating fundamental matrices
converge to it at the horizon. Each approximation preserves locus-exchangeable realizability by
`IntegrableRateHistoryRealization.rateHistory_preserves_locusExchangeable_realization`, and the
realizable states form the closed set `IntegrableRateHistoryRealization.exchangeableStates`, so
the solution at `T` preserves it too.

`nonnegativeIntegrablePropagator_preserves_locusExchangeable_realization` is NOTE1 Theorem 2 in
this setting, for every continuous solution of the integral equation: by
`IntegrableRateRealization.eq_of_integral_eq` it agrees with the solution just built.
Corollary 2.1 follows for the propagated state: it lies in the stored realization body
(`nonnegativeIntegrablePropagator_mulVec_mem_realizationBody`), its `DD` block is positive
semidefinite (`nonnegativeIntegrablePropagator_dd_quadraticForm_nonneg`), obeys Cauchy–Schwarz
(`nonnegativeIntegrablePropagator_dd_cauchySchwarz`) and has a nonnegative diagonal
(`nonnegativeIntegrablePropagator_dd_diagonal_nonneg`). At positive coalescence the coordinates
are the corpus ones (`coordinates_ofRates`), and the constant coalescence-free history is
integrable (`intervalIntegrable_coalescenceFree_coordinates`), so the theorem reaches histories
that no corpus rate history can express.

Scope. Integrability is assumed for the rate coordinates, as in `IntegrableRateRealization`. The
propagator is characterized by the integral equation; its almost-everywhere derivative is not
restated here. No microscopic kernel at vanishing coalescence is built: the result is reached
through the limit of perturbed histories.

## Empirical status

None. The bodies here are calculus and point-set topology: integral inequalities, a uniform limit
of fundamental matrices, and membership in a closed set, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonnegativeIntegrableRealization

open Coalescent
open MeasureTheory Filter Topology
open Descent.Portability.LinearFundamentalMatrix
open Descent.Portability.IntegrableRateHistoryRealization
open Descent.Portability.RateGeneratorLipschitz
open Descent.Portability.IntegrableRateRealization
open Descent.Portability.NonnegativeCoalescenceRealization
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## Rate coordinates of nonnegative rate histories -/

/-- At positive coalescence the rate coordinates of the nonnegative rate law are the corpus rate
coordinates. -/
theorem coordinates_ofRates {D : ℕ} (rates : ManyDemeLDRates D) :
    (NonnegativeLDRates.ofRates rates).coordinates = rateCoordinates rates :=
  rfl

/-- Raising every coalescence rate by `amount` moves the rate coordinates by `amount` times the
unit-coalescence direction. -/
theorem rateCoordinates_perturb {D : ℕ} (rates : NonnegativeLDRates D) (amount : ℝ)
    (hamount : 0 < amount) :
    rateCoordinates (rates.perturb amount hamount) =
      rates.coordinates + amount • unitCoalescenceDirection D := by
  refine Prod.ext (funext fun index ↦ ?_)
    (Prod.ext (funext fun origin ↦ funext fun destination ↦ ?_)
      (Prod.ext (funext fun index ↦ ?_) (funext fun index ↦ ?_)))
  all_goals simp [rateCoordinates, NonnegativeLDRates.perturb, NonnegativeLDRates.coordinates,
    unitCoalescenceDirection]

/-- The constant coalescence-free rate history has integrable rate coordinates on every
horizon. -/
theorem intervalIntegrable_coalescenceFree_coordinates (D : ℕ) (T : ℝ) :
    IntervalIntegrable (fun _ : ℝ ↦ (coalescenceFreeRates D).coordinates) volume 0 T :=
  intervalIntegrable_const

/-- A rate history at nonnegative coalescence with integrable coordinates has an integrable
generator path. -/
theorem intervalIntegrable_nonnegativeGenerator {D : ℕ} {rates : ℝ → NonnegativeLDRates D}
    {T : ℝ} (hintegrable : IntervalIntegrable (fun t ↦ (rates t).coordinates) volume 0 T) :
    IntervalIntegrable (fun t ↦ (rates t).generator) volume 0 T := by
  let bounded := LinearMap.toContinuousLinearMap (generatorLinearMap D)
  exact ⟨bounded.integrable_comp hintegrable.1, bounded.integrable_comp hintegrable.2⟩

/-- **Continuous corpus rate histories approximate a nonnegative integrable one in `L¹`.** For
every `ε > 0` there is a corpus rate history with continuous coordinates within
`ε (1 + T + T ‖u‖)` of the given history, where `u` is the unit-coalescence direction: raise every
coalescence rate by `ε`, then approximate the resulting corpus history. -/
theorem exists_continuous_rates_near_nonnegative {D : ℕ} {rates : ℝ → NonnegativeLDRates D}
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ (rates t).coordinates) volume 0 T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ path : ℝ → ManyDemeLDRates D, Continuous (fun t ↦ rateCoordinates (path t)) ∧
      ∫ t in (0 : ℝ)..T, ‖rateCoordinates (path t) - (rates t).coordinates‖ ≤
        ε * (1 + T + T * ‖unitCoalescenceDirection D‖) := by
  have hperturbed : IntervalIntegrable
      (fun t ↦ rateCoordinates ((rates t).perturb ε hε)) volume 0 T := by
    simp only [rateCoordinates_perturb]
    exact hintegrable.add intervalIntegrable_const
  obtain ⟨path, hpath, hclose⟩ := exists_continuous_rates_integral_norm_sub_le hT hperturbed hε
  refine ⟨path, hpath, ?_⟩
  have hdifference : IntervalIntegrable
      (fun t ↦ ‖rateCoordinates (path t) - rateCoordinates ((rates t).perturb ε hε)‖)
      volume 0 T :=
    ((hpath.intervalIntegrable 0 T).sub hperturbed).norm
  calc ∫ t in (0 : ℝ)..T, ‖rateCoordinates (path t) - (rates t).coordinates‖
      ≤ ∫ t in (0 : ℝ)..T,
          (‖rateCoordinates (path t) - rateCoordinates ((rates t).perturb ε hε)‖ +
            ε * ‖unitCoalescenceDirection D‖) := by
        refine intervalIntegral.integral_mono_on hT
          ((hpath.intervalIntegrable 0 T).sub hintegrable).norm
          (hdifference.add intervalIntegrable_const) fun t _ ↦ ?_
        rw [rateCoordinates_perturb]
        calc ‖rateCoordinates (path t) - (rates t).coordinates‖
            = ‖(rateCoordinates (path t) -
                ((rates t).coordinates + ε • unitCoalescenceDirection D)) +
                  ε • unitCoalescenceDirection D‖ := by
              congr 1
              abel
          _ ≤ _ := (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_of_nonneg hε.le])
    _ = (∫ t in (0 : ℝ)..T,
            ‖rateCoordinates (path t) - rateCoordinates ((rates t).perturb ε hε)‖) +
          T * (ε * ‖unitCoalescenceDirection D‖) := by
        rw [intervalIntegral.integral_add hdifference intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ ε * (1 + T + T * ‖unitCoalescenceDirection D‖) := by nlinarith [hclose]

/-! ## NOTE1 section 2.4 at nonnegative coalescence -/

/-- **A realizability-preserving solution of the integral equation.** For a rate history at
nonnegative coalescence whose rate coordinates are integrable on `[0, T]`, the integral equation
`U(t) = 1 + ∫₀ᵗ A(s) U(s) ds` with the nonnegative-coalescence generator at each time has a
continuous solution whose value at `T` carries every locus-exchangeably realizable stored state to a
locus-exchangeably realizable one. -/
theorem exists_nonnegativeIntegrablePropagator {D : ℕ} (rates : ℝ → NonnegativeLDRates D)
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ (rates t).coordinates) volume 0 T) :
    ∃ propagator : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ,
      Continuous propagator ∧
      (∀ t ∈ Set.Icc 0 T,
        propagator t = 1 + ∫ s in (0 : ℝ)..t, (rates s).generator * propagator s) ∧
      ∀ {state : AffineLowOrderLDCoordinate D → ℝ},
        LocusExchangeableLowOrderLDHaplotypeRealization state →
        Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
          ((propagator T).mulVec state)) := by
  let bounded := LinearMap.toContinuousLinearMap (generatorLinearMap D)
  have hstep : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  choose path hpath hpathClose using fun k : ℕ ↦
    exists_continuous_rates_near_nonnegative hT hintegrable (hstep k)
  have hgenerator := intervalIntegrable_nonnegativeGenerator hintegrable
  have hpathGenerator : ∀ k, Continuous fun t ↦ augmentedLowOrderLDGenerator (path k t) :=
    fun k ↦ continuous_augmentedLowOrderLDGenerator (hpath k)
  have hspread : 0 ≤ 1 + T + T * ‖unitCoalescenceDirection D‖ :=
    add_nonneg (add_nonneg zero_le_one hT) (mul_nonneg hT (norm_nonneg _))
  have hscale : 0 ≤ ‖bounded‖ * (1 + T + T * ‖unitCoalescenceDirection D‖) :=
    mul_nonneg (norm_nonneg _) hspread
  have happroximation : ∀ k : ℕ,
      ∫ s in (0 : ℝ)..T, ‖generatorPath (path k) T s - (rates s).generator‖ ≤
        ‖bounded‖ * (1 + T + T * ‖unitCoalescenceDirection D‖) * (1 / ((k : ℝ) + 1)) := by
    intro k
    calc ∫ s in (0 : ℝ)..T, ‖generatorPath (path k) T s - (rates s).generator‖
        ≤ ∫ s in (0 : ℝ)..T,
            ‖bounded‖ * ‖rateCoordinates (path k s) - (rates s).coordinates‖ := by
          refine intervalIntegral.integral_mono_on hT
            (((continuous_generatorPath hT (hpathGenerator k).continuousOn).intervalIntegrable
              0 T).sub hgenerator).norm
            ((((hpath k).intervalIntegrable 0 T).sub hintegrable).norm.const_mul _)
            fun s hs ↦ ?_
          rw [generatorPath_of_mem (path k) hs, augmentedLowOrderLDGenerator_eq_generatorLinearMap,
            NonnegativeLDRates.generator, ← map_sub]
          exact bounded.le_opNorm _
      _ = ‖bounded‖ *
            ∫ s in (0 : ℝ)..T, ‖rateCoordinates (path k s) - (rates s).coordinates‖ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ ‖bounded‖ * (1 / ((k : ℝ) + 1) * (1 + T + T * ‖unitCoalescenceDirection D‖)) :=
          mul_le_mul_of_nonneg_left (hpathClose k) (norm_nonneg _)
      _ = ‖bounded‖ * (1 + T + T * ‖unitCoalescenceDirection D‖) * (1 / ((k : ℝ) + 1)) := by
          ring
  obtain ⟨propagator, hcontinuous, hequation, hlimit⟩ :=
    exists_integral_solution_of_continuous_approximation hT hgenerator hscale
      (fun k ↦ generatorPath (path k) T)
      (fun k ↦ continuous_generatorPath hT (hpathGenerator k).continuousOn) happroximation
  refine ⟨propagator, hcontinuous, hequation, fun {state} realization ↦ ?_⟩
  have hmapped : Tendsto
      (fun k ↦ (fundamentalMatrix (generatorPath (path k) T) T T).mulVec state)
      atTop (𝓝 ((propagator T).mulVec state)) :=
    ((EulerInvariantSet.mulVecMap state).continuous_of_finiteDimensional.tendsto _).comp hlimit
  refine (mem_exchangeableStates_iff _).mp ((isClosed_exchangeableStates D).mem_of_tendsto
    hmapped (Eventually.of_forall fun k ↦ (mem_exchangeableStates_iff _).mpr ?_))
  exact rateHistory_preserves_locusExchangeable_realization (path k) hT
    (hpathGenerator k).continuousOn realization

/-! ## NOTE1 Theorem 2 and Corollary 2.1 for every solution -/

section EverySolution

variable {D : ℕ} {rates : ℝ → NonnegativeLDRates D} {T : ℝ} (hT : 0 ≤ T)
  (hintegrable : IntervalIntegrable (fun t ↦ (rates t).coordinates) volume 0 T)
  {propagator : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ}
  (hcontinuous : Continuous propagator)
  (hequation : ∀ t ∈ Set.Icc 0 T,
    propagator t = 1 + ∫ s in (0 : ℝ)..t, (rates s).generator * propagator s)
  {state : AffineLowOrderLDCoordinate D → ℝ}
  (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)

include hT hintegrable hcontinuous hequation realization

/-- **NOTE1 Theorem 2 for integrable rate histories at nonnegative coalescence.** Every continuous
solution of the integral equation of a rate history at nonnegative coalescence with integrable
coordinates carries a locus-exchangeably realizable stored state, at the horizon, to a
locus-exchangeably realizable one. -/
theorem nonnegativeIntegrablePropagator_preserves_locusExchangeable_realization :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization ((propagator T).mulVec state)) := by
  obtain ⟨solution, hsolution, hsolutionEquation, hpreserves⟩ :=
    exists_nonnegativeIntegrablePropagator rates hT hintegrable
  rw [eq_of_integral_eq hT (intervalIntegrable_nonnegativeGenerator hintegrable) hcontinuous
    hsolution hequation hsolutionEquation T ⟨hT, le_rfl⟩]
  exact hpreserves realization

/-- The propagated state lies in the stored realization body. -/
theorem nonnegativeIntegrablePropagator_mulVec_mem_realizationBody :
    (propagator T).mulVec state ∈
      RealizationBody.realizationBody (RealizationBody.lowOrderLDFeature D) := by
  obtain ⟨propagated⟩ := nonnegativeIntegrablePropagator_preserves_locusExchangeable_realization
    hT hintegrable hcontinuous hequation realization
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    propagated.toLowOrderLDHaplotypeRealization

/-- **NOTE1 Corollary 2.1: the propagated `DD` block is positive semidefinite.** Every finite
linear combination of deme-specific linkage disequilibria has nonnegative second moment under the
propagated haplotype law. -/
theorem nonnegativeIntegrablePropagator_dd_quadraticForm_nonneg (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second,
      weight first * (propagator T).mulVec state (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ := nonnegativeIntegrablePropagator_preserves_locusExchangeable_realization
    hT hintegrable hcontinuous hequation realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) for the propagated state: the cross-deme `DD` entries obey Cauchy–Schwarz against
the diagonals. -/
theorem nonnegativeIntegrablePropagator_dd_cauchySchwarz (first second : Fin D) :
    (propagator T).mulVec state (some (.DD first second)) ^ 2 ≤
      (propagator T).mulVec state (some (.DD first first)) *
        (propagator T).mulVec state (some (.DD second second)) := by
  obtain ⟨propagated⟩ := nonnegativeIntegrablePropagator_preserves_locusExchangeable_realization
    hT hintegrable hcontinuous hequation realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The propagated within-deme `DD` diagonal is nonnegative. -/
theorem nonnegativeIntegrablePropagator_dd_diagonal_nonneg (deme : Fin D) :
    0 ≤ (propagator T).mulVec state (some (.DD deme deme)) := by
  obtain ⟨propagated⟩ := nonnegativeIntegrablePropagator_preserves_locusExchangeable_realization
    hT hintegrable hcontinuous hequation realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg deme

end EverySolution

end

end Descent.Portability.NonnegativeIntegrableRealization
