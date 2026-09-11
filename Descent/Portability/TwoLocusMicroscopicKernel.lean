/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PulseStageKernel
import Descent.Portability.EnlargedLowOrderLDGenerator

assert_below Descent.Decision Descent.Program

/-!
# The assembled two-locus microscopic kernel

NOTE1 section 2.3 builds one microscopic step out of five kinds of stage: single-draw
resampling in each deme, a haplotype migration pulse along each ordered deme pair, a
recombination pulse in each deme, and the two single-locus allele-flip mutation pulses.  Its
formalization alternative replaces composition of the stages by a step that CHOOSES one stage
uniformly at random and runs it at `S` times the intended parameter, so that the mixture's
first-order term is the sum of the stage generators with no composition lemma.

`Descent.Portability.PulseStageKernel` presents all five stages as probability kernels with
one common branch type and proves the per-stage estimate, and
`Descent.Portability.RandomStageKernel` proves the uniform-mixture assembly.  This module ties
them to the enlarged feature family of NOTE1 equation (6): `enlargedCoordinateJet` names the
corpus diffusion jet behind every enlarged coordinate, `enlargedStageExpansion` supplies the
five per-stage certificates for each of them, `microscopicKernel` is the assembled step, and
`microscopicKernel_expansion` is NOTE1 equation (11) with an explicit error that vanishes with
the step size.

`twoLocusMicroscopicApproximation` packages this as the `MicroscopicApproximation` that NOTE1
Theorem 1 consumes.  It carries ONE hypothesis, stated explicitly and never hidden in an
existential: that the rate-weighted stage velocities sum to the enlarged generator applied to
the feature vector, coordinate by coordinate.  That identification is the remaining
mathematical content of NOTE1 equation (11), and it is a finite list of per-stage,
per-coordinate identities rather than an analytic statement.  Four of them are proved in
`PulseJetExpansion` (the two heterozygosity migration rows, the `DD` recombination row and the
heterozygosity mutation row) and the drift stage's whole contribution is the corpus's own
`twoLocusWeightedJetDrift_*_eq_lowOrderLDDrift` family; the rest are not yet formalized, and
until they are the hypothesis is what a caller must supply.

Scope.  `microscopicError` is a sum of per-coordinate, per-stage slacks and is therefore a
crude but explicit bound; no attempt is made to make it sharp.  Multinomial resampling, NOTE1
equation (10), is not formalized anywhere in this package: the single-draw alternative of
NOTE1 section 2.3 is used instead, and it is equally physical.  Nothing here forms a semigroup
or takes a limit; that is NOTE1 Theorem 1, proved in
`Descent.Portability.KernelRealizationPreservation`.

## Empirical status

None.  The bodies here are algebra: finite averages of polynomial coordinates against
probability weights, and bounds between them.  Whether a population's microscopic step is this
list of stages is a modelling question asked wherever a composed prediction meets data, not
here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TwoLocusMicroscopicKernel

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.PulseJetExpansion
open Descent.Portability.ResamplingJetExpansion
open Descent.Portability.RandomStageKernel
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator

noncomputable section

/-! ## The diffusion jet behind every enlarged coordinate -/

/-- The corpus diffusion jet read by each coordinate of the enlarged family: the constant jet
for the affine coordinate, the closed low-order jet for a stored coordinate, and the
right-locus heterozygosity jet for the coordinates NOTE1 equation (6) adds. -/
def enlargedCoordinateJet {D : ℕ} : AffineEnlargedCoordinate D → TwoLocusDiffusionJet D
  | none => TwoLocusDiffusionJet.const 1
  | some (.inl coordinate) => twoLocusCoordinateJet coordinate
  | some (.inr pair) => twoLocusRightHJet pair.1 pair.2

/-- The jet reads exactly the enlarged feature coordinate. -/
theorem enlargedCoordinateJet_value {D : ℕ} (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    (enlargedCoordinateJet coordinate).value state =
      enlargedLowOrderLDFeature state coordinate := by
  cases coordinate with
  | none => rfl
  | some enlarged =>
    cases enlarged with
    | inl coordinate => rfl
    | inr pair => exact twoLocusRightHJet_value state pair.1 pair.2

/-- The observable read by one enlarged coordinate is the value of its jet. -/
theorem enlargedFeature_eq_jet_value {D : ℕ} (coordinate : AffineEnlargedCoordinate D) :
    (fun state ↦ enlargedLowOrderLDFeature state coordinate) =
      (enlargedCoordinateJet coordinate).value := by
  funext state
  exact (enlargedCoordinateJet_value coordinate state).symm

/-- The constant observable carries all five stage certificates, with zero velocity in each
stage and no remainder. -/
def constantStageExpansion {D : ℕ} :
    StageExpansion (TwoLocusDiffusionJet.const (D := D) 1) where
  drift := resamplingExpansionConst 1
  migration source recipient := PulseExpansion.const D (migrationPulse source recipient) 1
  recombination deme := PulseExpansion.const D (recombinationPulseAt deme) 1
  mutationLeft deme := PulseExpansion.const D (leftMutationPulseAt deme) 1
  mutationRight deme := PulseExpansion.const D (rightMutationPulseAt deme) 1

/-- Every coordinate of the enlarged family carries the five stage certificates. -/
def enlargedStageExpansion {D : ℕ} :
    (coordinate : AffineEnlargedCoordinate D) →
      StageExpansion (enlargedCoordinateJet coordinate)
  | none => constantStageExpansion
  | some (.inl coordinate) => coordinateStageExpansion coordinate
  | some (.inr pair) => rightHeterozygosityStageExpansion pair.1 pair.2

/-! ## The assembled step and its error -/

/-- Nonnegativity of the deterministic pulse stage's slack. -/
private theorem pulseStageSlack_nonneg (rate valueBound velocityBound remainder tau : ℝ)
    (hrate : 0 ≤ rate) (hvalue : 0 ≤ valueBound) (hvelocity : 0 ≤ velocityBound)
    (hremainder : 0 ≤ remainder) (htau : 0 ≤ tau) :
    0 ≤ pulseStageSlack rate valueBound velocityBound remainder tau := by
  have hclamp := pulseFraction_nonneg (2 * rate * tau - 1)
  simp only [pulseStageSlack]
  have hquadratic : 0 ≤ remainder * rate ^ 2 * tau :=
    mul_nonneg (mul_nonneg hremainder (sq_nonneg rate)) htau
  have hgain : 0 ≤ (2 * valueBound * rate + rate * velocityBound) *
      pulseFraction (2 * rate * tau - 1) :=
    mul_nonneg (add_nonneg (mul_nonneg (by linarith) hrate)
      (mul_nonneg hrate hvelocity)) hclamp
  linarith

/-- Every stage's slack is nonnegative, so the assembled error bound is a genuine bound. -/
theorem stageSlack_nonneg {D : ℕ} {jet : TwoLocusDiffusionJet D} (rates : ManyDemeLDRates D)
    (certificate : StageExpansion jet) (stage : Stage D) (tau : ℝ) (htau : 0 ≤ tau) :
    0 ≤ stageSlack rates certificate stage tau := by
  cases stage with
  | drift deme =>
      have hbound := certificate.drift.bound_nonneg
      have hremainder := certificate.drift.remainder_nonneg
        (fun _ ↦ TwoLocusHaplotypeFrequencies.maximalCoupling) deme .AB
      have hrate := le_of_lt (rates.coalescence_pos deme)
      simp only [stageSlack, driftStageSlack]
      exact mul_nonneg (mul_nonneg (by linarith)
        (mul_nonneg hrate (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  | migration source recipient =>
      exact pulseStageSlack_nonneg _ _ _ _ _ (rates.migration_nonneg recipient source)
        (certificate.migration source recipient).valueBound_nonneg
        (certificate.migration source recipient).velocityBound_nonneg
        (certificate.migration source recipient).remainder_nonneg htau
  | recombination deme =>
      exact pulseStageSlack_nonneg _ _ _ _ _
        (by linarith [rates.recombination_nonneg deme])
        (certificate.recombination deme).valueBound_nonneg
        (certificate.recombination deme).velocityBound_nonneg
        (certificate.recombination deme).remainder_nonneg htau
  | mutationLeft deme =>
      exact pulseStageSlack_nonneg _ _ _ _ _ (by linarith [rates.mutation_nonneg deme])
        (certificate.mutationLeft deme).valueBound_nonneg
        (certificate.mutationLeft deme).velocityBound_nonneg
        (certificate.mutationLeft deme).remainder_nonneg htau
  | mutationRight deme =>
      exact pulseStageSlack_nonneg _ _ _ _ _ (by linarith [rates.mutation_nonneg deme])
        (certificate.mutationRight deme).valueBound_nonneg
        (certificate.mutationRight deme).velocityBound_nonneg
        (certificate.mutationRight deme).remainder_nonneg htau

/-- One microscopic step: choose one of the stages uniformly at random and run it at the
stage count times the step size.  This is NOTE1 section 2.3's stage-choosing construction.
The deme is taken as data because it is what makes the stage set nonempty. -/
def microscopicKernel {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) (step : ℝ) :
    FiniteMixtureKernel TwoLocusHaplotype (DemeHaplotypeState D) :=
  FiniteMixtureKernel.uniformMixture
    (fun stage ↦ stageKernel rates stage (Fintype.card (Stage D) * step))
    (card_stage_pos deme)

/-- The total slack of one microscopic step over every enlarged coordinate and every stage. -/
def microscopicSlack {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) : ℝ :=
  ∑ coordinate : AffineEnlargedCoordinate D, ∑ stage : Stage D,
    stageSlack rates (enlargedStageExpansion coordinate) stage
      (Fintype.card (Stage D) * step)

/-- The explicit uniform remainder bound of one microscopic step.  The absolute value makes
it nonnegative at every real step size, which the bundled hypothesis structure asks for, and
changes nothing at the positive step sizes where the bound is used. -/
def microscopicError {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) : ℝ :=
  |microscopicSlack rates step|

/-- The assembled error is nonnegative at every step size. -/
theorem microscopicError_nonneg {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) :
    0 ≤ microscopicError rates step := abs_nonneg _

/-- The assembled error vanishes as the step size decreases to zero, which is the `epsilon`
of NOTE1 equation (3). -/
theorem microscopicError_tendsto {D : ℕ} (rates : ManyDemeLDRates D) :
    Filter.Tendsto (microscopicError rates) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hidentity : Filter.Tendsto (fun step : ℝ ↦ step) (nhds 0) (nhds 0) := tendsto_id
  have hscale : Filter.Tendsto
      (fun step : ℝ ↦ (Fintype.card (Stage D) : ℝ) * step) (nhds 0) (nhds 0) := by
    simpa using hidentity.const_mul ((Fintype.card (Stage D) : ℝ))
  have hterms : Filter.Tendsto
      (fun step ↦ ∑ coordinate : AffineEnlargedCoordinate D, ∑ stage : Stage D,
        stageSlack rates (enlargedStageExpansion coordinate) stage
          (Fintype.card (Stage D) * step)) (nhds 0)
      (nhds (∑ _coordinate : AffineEnlargedCoordinate D, ∑ _stage : Stage D, (0 : ℝ))) := by
    refine tendsto_finset_sum _ fun coordinate _ ↦ tendsto_finset_sum _ fun stage _ ↦ ?_
    exact (stageSlack_tendsto rates (enlargedStageExpansion coordinate) stage).comp hscale
  have hwhole : Filter.Tendsto (microscopicSlack rates) (nhds 0) (nhds 0) := by
    simpa [microscopicSlack] using hterms
  have habs := (hwhole.mono_left nhdsWithin_le_nhds).abs
  simpa [microscopicError] using habs

/-- **One microscopic step advances every enlarged coordinate by the summed stage drift.**
This is NOTE1 equation (11) with the sum of rate-weighted stage velocities in place of the
generator; identifying that sum with the generator is the remaining step. -/
theorem microscopicKernel_expansion {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D)
    (step : ℝ) (hstep : 0 < step) (state : DemeHaplotypeState D)
    (coordinate : AffineEnlargedCoordinate D) :
    |(microscopicKernel rates deme step).apply
          (enlargedCoordinateJet coordinate).value state -
        (enlargedCoordinateJet coordinate).value state -
        step * ∑ stage : Stage D,
          stageDrift rates (enlargedStageExpansion coordinate) stage state| ≤
      step * ∑ stage : Stage D,
        stageSlack rates (enlargedStageExpansion coordinate) stage
          (Fintype.card (Stage D) * step) := by
  have hcard : (0 : ℝ) < (Fintype.card (Stage D) : ℝ) := by
    exact_mod_cast card_stage_pos deme
  simp only [microscopicKernel]
  refine apply_uniformStageMixture
    (fun stage ↦ stageKernel rates stage (Fintype.card (Stage D) * step))
    (fun stage ↦ stageDrift rates (enlargedStageExpansion coordinate) stage)
    (fun stage ↦ stageSlack rates (enlargedStageExpansion coordinate) stage
      (Fintype.card (Stage D) * step))
    (card_stage_pos deme) _ state step fun stage ↦ ?_
  exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate) stage
    (Fintype.card (Stage D) * step) (mul_pos hcard hstep) state

/-- **The microscopic approximation of the enlarged generator.**  Every stage is a genuine
probability kernel at every step size, the expansion is uniform in the state and the
coordinate, and the error vanishes with the step, so NOTE1 Theorem 1 applies to the enlarged
family.

Assumes: `stage_generator`, that the rate-weighted stage velocities sum to the enlarged
generator applied to the feature vector at every state and coordinate.  This is NOTE1's
equation (11) identification and the only mathematical content of the present module that is
not discharged here; it is a finite list of per-stage, per-coordinate polynomial identities,
several of which are proved in `Descent.Portability.PulseJetExpansion`. -/
def twoLocusMicroscopicApproximation {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D)
    (stage_generator : ∀ (state : DemeHaplotypeState D)
      (coordinate : AffineEnlargedCoordinate D),
      (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state)
          coordinate =
        ∑ stage : Stage D, stageDrift rates (enlargedStageExpansion coordinate) stage state) :
    MicroscopicApproximation (B := TwoLocusHaplotype)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates) where
  kernel := microscopicKernel rates deme
  error := microscopicError rates
  error_nonneg step := microscopicError_nonneg rates step
  error_tendsto := microscopicError_tendsto rates
  expansion step hstep state coordinate := by
    have hbound := microscopicKernel_expansion rates deme step hstep state coordinate
    rw [stage_generator state coordinate, enlargedFeature_eq_jet_value coordinate,
      ← enlargedCoordinateJet_value coordinate state]
    refine le_trans hbound (mul_le_mul_of_nonneg_left ?_ (le_of_lt hstep))
    refine le_trans (Finset.single_le_sum
      (f := fun other : AffineEnlargedCoordinate D ↦
        ∑ stage : Stage D, stageSlack rates (enlargedStageExpansion other) stage
          (Fintype.card (Stage D) * step)) ?_ (Finset.mem_univ coordinate))
      (le_abs_self _)
    intro other _
    refine Finset.sum_nonneg fun stage _ ↦ ?_
    exact stageSlack_nonneg rates _ stage _ (by positivity)

end

end Descent.Portability.TwoLocusMicroscopicKernel
