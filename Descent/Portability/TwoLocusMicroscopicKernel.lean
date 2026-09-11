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

/-! ## Splitting the stage sum -/

/-- The stage index is the disjoint union of its five constructor families. -/
def stageStructure (D : ℕ) :
    (Fin D ⊕ (Fin D × Fin D) ⊕ Fin D ⊕ Fin D ⊕ Fin D) ≃ Stage D where
  toFun
    | .inl deme => .drift deme
    | .inr (.inl pair) => .migration pair.1 pair.2
    | .inr (.inr (.inl deme)) => .recombination deme
    | .inr (.inr (.inr (.inl deme))) => .mutationLeft deme
    | .inr (.inr (.inr (.inr deme))) => .mutationRight deme
  invFun
    | .drift deme => .inl deme
    | .migration source recipient => .inr (.inl (source, recipient))
    | .recombination deme => .inr (.inr (.inl deme))
    | .mutationLeft deme => .inr (.inr (.inr (.inl deme)))
    | .mutationRight deme => .inr (.inr (.inr (.inr deme)))
  left_inv := by rintro (_ | (_ | (_ | (_ | _)))) <;> rfl
  right_inv := by rintro (_ | _ | _ | _ | _) <;> rfl

/-- A sum over the stages splits into the drift, migration, recombination and two mutation
families.  This is what lets a generator row be matched family by family. -/
theorem sum_stage {D : ℕ} (summand : Stage D → ℝ) :
    ∑ stage : Stage D, summand stage =
      (∑ deme : Fin D, summand (Stage.drift deme)) +
      (∑ pair : Fin D × Fin D, summand (Stage.migration pair.1 pair.2)) +
      (∑ deme : Fin D, summand (Stage.recombination deme)) +
      (∑ deme : Fin D, summand (Stage.mutationLeft deme)) +
      (∑ deme : Fin D, summand (Stage.mutationRight deme)) := by
  rw [← Equiv.sum_comp (stageStructure D) summand]
  simp only [Fintype.sum_sum_type, stageStructure, Equiv.coe_fn_mk]
  ring

/-- A rate-weighted sum against an index indicator reads the rate at that index. -/
private theorem sum_rate_indicator {D : ℕ} (weight : Fin D → ℝ) (target : Fin D) :
    ∑ deme : Fin D, weight deme * (if target = deme then (1 : ℝ) else 0) = weight target := by
  classical
  simp

/-! ## The drift stage reproduces the corpus coalescence row -/

/-- The drift stages sum to the corpus's coalescence generator row on every stored
coordinate.  Both sides are literally `twoLocusWeightedJetDrift`, so the corpus's own
identification is what proves it. -/
theorem driftStage_sum_stored {D : ℕ} (rates : ManyDemeLDRates D)
    (feature : LowOrderLDCoordinate D) (state : DemeHaplotypeState D) :
    ∑ deme : Fin D, stageRate rates (Stage.drift deme) *
        stageVelocity (enlargedStageExpansion (some (.inl feature))) (Stage.drift deme)
          state =
      lowOrderLDDrift rates (twoLocusJetMoment state) feature := by
  have hsum : ∑ deme : Fin D, stageRate rates (Stage.drift deme) *
      stageVelocity (enlargedStageExpansion (some (.inl feature))) (Stage.drift deme) state =
      twoLocusWeightedJetDrift rates.coalescence state feature := rfl
  rw [hsum]
  cases feature with
  | H first second => exact twoLocusWeightedJetDrift_H_eq_lowOrderLDDrift rates state first
      second
  | DD first second => exact twoLocusWeightedJetDrift_DD_eq_lowOrderLDDrift rates state first
      second
  | Dz first second third =>
      exact twoLocusWeightedJetDrift_Dz_eq_lowOrderLDDrift rates state first second third
  | pi2 first second third fourth =>
      exact twoLocusWeightedJetDrift_pi2_eq_lowOrderLDDrift rates state first second third
        fourth

/-- The right-locus heterozygosity block of the enlarged feature vector reads the
right-locus heterozygosity jet. -/
private theorem rightHeterozygosityMoment_heterozygosity {D : ℕ}
    (state : DemeHaplotypeState D) (first second : Fin D) :
    rightHeterozygosityMoment (enlargedLowOrderLDFeature state) (.H first second) =
      (twoLocusRightHJet first second).value state := by
  rw [twoLocusRightHJet_value]
  rfl

/-- The stored heterozygosity block of the enlarged feature vector reads the heterozygosity
jet. -/
private theorem jetMoment_heterozygosity {D : ℕ} (state : DemeHaplotypeState D)
    (first second : Fin D) :
    twoLocusJetMoment state (.H first second) = (twoLocusHJet first second).value state := rfl

/-- The drift stages on a right-locus heterozygosity coordinate reproduce the corpus's own
coalescence row for heterozygosity, read at the right-locus block: a decay at the deme's
coalescence rate exactly when both lineages sit in that deme. -/
theorem driftStage_sum_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    ∑ deme : Fin D, stageRate rates (Stage.drift deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.drift deme) state =
      lowOrderLDDrift rates (rightHeterozygosityMoment (enlargedLowOrderLDFeature state))
        (.H first second) := by
  classical
  have hsum : ∑ deme : Fin D, stageRate rates (Stage.drift deme) *
      stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
        (Stage.drift deme) state =
      ∑ deme : Fin D, rates.coalescence deme *
        (twoLocusRightHJet first second).driftAt deme state := rfl
  rw [hsum]
  simp only [lowOrderLDDrift, rightHeterozygosityMoment_heterozygosity]
  by_cases hsame : first = second
  · subst hsame
    simp [twoLocusRightHJet_driftAt]
  · have hnever : ∀ deme : Fin D, ¬(first = deme ∧ second = deme) := by
      intro deme hboth
      exact hsame (hboth.1.trans hboth.2.symm)
    simp [twoLocusRightHJet_driftAt, hsame, hnever]

/-- The drift stages move the affine constant coordinate not at all. -/
theorem driftStage_sum_constant {D : ℕ} (rates : ManyDemeLDRates D)
    (state : DemeHaplotypeState D) :
    ∑ deme : Fin D, stageRate rates (Stage.drift deme) *
        stageVelocity (enlargedStageExpansion (none : AffineEnlargedCoordinate D))
          (Stage.drift deme) state = 0 := by
  simp [stageVelocity, enlargedStageExpansion, enlargedCoordinateJet,
    TwoLocusDiffusionJet.const]

/-! ## The migration stages reproduce the corpus heterozygosity migration rows -/

/-- The migration stages sum to the corpus's migration generator row on the stored
heterozygosity coordinate.  Each ordered pair contributes only when its recipient is one of
the two lineages, and the pulse velocity is exactly the lineage replacement stencil. -/
theorem migrationStage_sum_leftHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    ∑ pair : Fin D × Fin D, stageRate rates (Stage.migration pair.1 pair.2) *
        stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
          (Stage.migration pair.1 pair.2) state =
      lowOrderLDMigration rates (twoLocusJetMoment state) (.H first second) := by
  classical
  have hvelocity : ∀ pair : Fin D × Fin D,
      stageRate rates (Stage.migration pair.1 pair.2) *
        stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
          (Stage.migration pair.1 pair.2) state =
      rates.migration pair.2 pair.1 *
        ((if first = pair.2 then (twoLocusHJet pair.1 second).value state -
            (twoLocusHJet first second).value state else 0) +
          (if second = pair.2 then (twoLocusHJet first pair.1).value state -
            (twoLocusHJet first second).value state else 0)) := by
    intro pair
    rw [migrationLeftHeterozygosity_velocity]
  simp only [hvelocity, Fintype.sum_prod_type, lowOrderLDMigration,
    jetMoment_heterozygosity, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The migration stages sum to the same replacement row on the right-locus heterozygosity
coordinate.  This is the `H^R` migration row that the stored generator does not carry. -/
theorem migrationStage_sum_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    ∑ pair : Fin D × Fin D, stageRate rates (Stage.migration pair.1 pair.2) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.migration pair.1 pair.2) state =
      lowOrderLDMigration rates
        (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) := by
  classical
  have hvelocity : ∀ pair : Fin D × Fin D,
      stageRate rates (Stage.migration pair.1 pair.2) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.migration pair.1 pair.2) state =
      rates.migration pair.2 pair.1 *
        ((if first = pair.2 then (twoLocusRightHJet pair.1 second).value state -
            (twoLocusRightHJet first second).value state else 0) +
          (if second = pair.2 then (twoLocusRightHJet first pair.1).value state -
            (twoLocusRightHJet first second).value state else 0)) := by
    intro pair
    rw [migrationRightHeterozygosity_velocity]
  simp only [hvelocity, Fintype.sum_prod_type, lowOrderLDMigration,
    rightHeterozygosityMoment_heterozygosity, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## The mutation stages reproduce the corpus heterozygosity mutation rows -/

/-- A right-locus mutation pulse moves no left marginal, so the stored heterozygosity has
zero right-mutation velocity. -/
theorem rightMutationLeftHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((rightMutationCoordinateExpansion target).leftHeterozygosity first second).velocity
      state = 0 := by
  simp [PulseCoordinateExpansion.leftHeterozygosity, PulseExpansion.ofEq, PulseExpansion.add,
    PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
    rightMutationCoordinateExpansion, rightMutationLeftExpansion]

/-- A left-locus mutation pulse moves no right marginal, so the right-locus heterozygosity
has zero left-mutation velocity. -/
theorem leftMutationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((leftMutationCoordinateExpansion target).rightHeterozygosity first second).velocity
      state = 0 := by
  simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq, PulseExpansion.add,
    PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
    leftMutationCoordinateExpansion, leftMutationRightExpansion]

/-- The right-locus heterozygosity obeys the same affine mutation law as the stored one, with
the right-locus contrasts in place of the left: an influx of one half against a decay of the
current heterozygosity, per lineage sitting in the mutating deme. -/
theorem rightMutationRightHeterozygosity_velocity {D : ℕ} (target first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((rightMutationCoordinateExpansion target).rightHeterozygosity first second).velocity
        state =
      2 * ((if first = target then (1 : ℝ) else 0) +
          (if second = target then (1 : ℝ) else 0)) *
        (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) := by
  by_cases hfirst : first = target <;> by_cases hsecond : second = target <;>
    simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq,
      PulseExpansion.add, PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
      rightMutationCoordinateExpansion, rightMutationRightExpansion,
      twoLocusRightHeterozygosity, TwoLocusHaplotypeFrequencies.rightContrast,
      hfirst, hsecond] <;> ring

/-- The two mutation stage families sum to the corpus's complete affine mutation row on the
stored heterozygosity coordinate: the coupling, the recurrent damping and the constant
influx. -/
theorem mutationStage_sum_leftHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme : Fin D, stageRate rates (Stage.mutationLeft deme) *
        stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
          (Stage.mutationLeft deme) state) +
      (∑ deme : Fin D, stageRate rates (Stage.mutationRight deme) *
        stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
          (Stage.mutationRight deme) state) =
      lowOrderLDMutationCoupling rates (twoLocusJetMoment state) (.H first second) +
        lowOrderLDRecurrentMutationDamping rates (twoLocusJetMoment state)
          (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) := by
  classical
  have hright : ∀ deme : Fin D,
      stageRate rates (Stage.mutationRight deme) *
        stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
          (Stage.mutationRight deme) state = 0 := by
    intro deme
    have hzero : ((rightMutationCoordinateExpansion deme).leftHeterozygosity first
        second).velocity state = 0 := rightMutationLeftHeterozygosity_velocity deme first
      second state
    show rates.mutation deme / 2 * _ = 0
    rw [hzero, mul_zero]
  have hleft : ∀ deme : Fin D,
      stageRate rates (Stage.mutationLeft deme) *
        stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
          (Stage.mutationLeft deme) state =
      (1 / 2 - twoLocusLeftHeterozygosity (state first) (state second)) *
          (rates.mutation deme * (if first = deme then (1 : ℝ) else 0)) +
        (1 / 2 - twoLocusLeftHeterozygosity (state first) (state second)) *
          (rates.mutation deme * (if second = deme then (1 : ℝ) else 0)) := by
    intro deme
    have hvelocity : stageVelocity (enlargedStageExpansion (some (.inl (.H first second))))
        (Stage.mutationLeft deme) state =
        2 * ((if first = deme then (1 : ℝ) else 0) +
            (if second = deme then (1 : ℝ) else 0)) *
          twoLocusHMutationVelocity (state first) (state second) :=
      leftMutationLeftHeterozygosity_velocity deme first second state
    show rates.mutation deme / 2 * _ = _
    rw [hvelocity, twoLocusHMutationVelocity_eq]
    ring
  simp only [hright, Finset.sum_const_zero, add_zero, hleft, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_rate_indicator]
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing, jetMoment_heterozygosity, twoLocusHJet_value]
  ring

/-- The same affine mutation row holds on the right-locus heterozygosity coordinate, which is
NOTE1's statement that both heterozygosity families obey one system with one forcing. -/
theorem mutationStage_sum_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (∑ deme : Fin D, stageRate rates (Stage.mutationLeft deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.mutationLeft deme) state) +
      (∑ deme : Fin D, stageRate rates (Stage.mutationRight deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.mutationRight deme) state) =
      lowOrderLDMutationCoupling rates
          (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) +
        lowOrderLDRecurrentMutationDamping rates
          (rightHeterozygosityMoment (enlargedLowOrderLDFeature state)) (.H first second) +
        lowOrderLDMutationForcing rates (.H first second) := by
  classical
  have hleft : ∀ deme : Fin D,
      stageRate rates (Stage.mutationLeft deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.mutationLeft deme) state = 0 := by
    intro deme
    have hzero : ((leftMutationCoordinateExpansion deme).rightHeterozygosity first
        second).velocity state = 0 := leftMutationRightHeterozygosity_velocity deme first
      second state
    show rates.mutation deme / 2 * _ = 0
    rw [hzero, mul_zero]
  have hright : ∀ deme : Fin D,
      stageRate rates (Stage.mutationRight deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.mutationRight deme) state =
      (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) *
          (rates.mutation deme * (if first = deme then (1 : ℝ) else 0)) +
        (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) *
          (rates.mutation deme * (if second = deme then (1 : ℝ) else 0)) := by
    intro deme
    have hvelocity : stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
        (Stage.mutationRight deme) state =
        2 * ((if first = deme then (1 : ℝ) else 0) +
            (if second = deme then (1 : ℝ) else 0)) *
          (1 / 2 - twoLocusRightHeterozygosity (state first) (state second)) :=
      rightMutationRightHeterozygosity_velocity deme first second state
    show rates.mutation deme / 2 * _ = _
    rw [hvelocity]
    ring
  simp only [hleft, Finset.sum_const_zero, zero_add, hright, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_rate_indicator]
  simp only [lowOrderLDMutationCoupling, lowOrderLDRecurrentMutationDamping,
    lowOrderLDMutationForcing, rightHeterozygosityMoment_heterozygosity,
    twoLocusRightHJet_value]
  ring

/-! ## The recombination stages reproduce the corpus recombination row -/

/-- Recombination moves no marginal allele frequency, so the left heterozygosity has zero
recombination velocity. -/
theorem recombinationLeftHeterozygosity_velocity {D : ℕ} (deme first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion deme).leftHeterozygosity first second).velocity
      state = 0 := by
  simp [PulseCoordinateExpansion.leftHeterozygosity, PulseExpansion.ofEq, PulseExpansion.add,
    PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
    recombinationCoordinateExpansion, recombinationLeftExpansion]

/-- The right heterozygosity likewise has zero recombination velocity. -/
theorem recombinationRightHeterozygosity_velocity {D : ℕ} (deme first second : Fin D)
    (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion deme).rightHeterozygosity first second).velocity
      state = 0 := by
  simp [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq, PulseExpansion.add,
    PulseExpansion.mul, PulseExpansion.smul, PulseExpansion.const,
    recombinationCoordinateExpansion, recombinationRightExpansion]

/-- The joint heterozygosity is a product of two heterozygosities, so it too is unmoved by
recombination.  This is the corpus's vanishing `pi2` recombination row. -/
theorem recombinationJointHeterozygosity_velocity {D : ℕ} (deme first second third fourth :
    Fin D) (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion deme).jointHeterozygosity first second third
      fourth).velocity state = 0 := by
  simp [PulseCoordinateExpansion.jointHeterozygosity, PulseExpansion.ofEq, PulseExpansion.mul,
    PulseExpansion.smul, recombinationLeftHeterozygosity_velocity,
    recombinationRightHeterozygosity_velocity]

/-- The generalized `Dz` observable loses its linkage factor at the recombining deme and
nothing else, matching the corpus's `-rho/2 * Dz` row once the pulse fraction carries the
half-rate. -/
theorem recombinationDzObservable_velocity {D : ℕ} (deme first second third : Fin D)
    (state : DemeHaplotypeState D) :
    ((recombinationCoordinateExpansion deme).dzObservable first second third).velocity
        state =
      -(if first = deme then 1 else 0) * (twoLocusDzJet first second third).value state := by
  by_cases hfirst : first = deme <;>
    simp [PulseCoordinateExpansion.dzObservable, PulseExpansion.ofEq, PulseExpansion.mul,
      PulseExpansion.add, PulseExpansion.smul, PulseExpansion.const,
      recombinationCoordinateExpansion, recombinationLinkageExpansion,
      recombinationLeftExpansion, recombinationRightExpansion,
      TwoLocusHaplotypeFrequencies.recombinationLinkageVelocity, twoLocusDzJet,
      TwoLocusDiffusionJet.mul, TwoLocusDiffusionJet.add, TwoLocusDiffusionJet.smul,
      TwoLocusDiffusionJet.const, twoLocusLinkageJet, twoLocusLeftContrastJet,
      twoLocusRightContrastJet, twoLocusLeftFrequencyJet, twoLocusRightFrequencyJet,
      hfirst] <;> ring

/-- The recombination stages sum to the corpus's recombination generator row on every stored
coordinate. -/
theorem recombinationStage_sum_stored {D : ℕ} (rates : ManyDemeLDRates D)
    (feature : LowOrderLDCoordinate D) (state : DemeHaplotypeState D) :
    ∑ deme : Fin D, stageRate rates (Stage.recombination deme) *
        stageVelocity (enlargedStageExpansion (some (.inl feature)))
          (Stage.recombination deme) state =
      lowOrderLDRecombination rates (twoLocusJetMoment state) feature := by
  classical
  have hvelocity : ∀ deme : Fin D,
      stageRate rates (Stage.recombination deme) *
        stageVelocity (enlargedStageExpansion (some (.inl feature)))
          (Stage.recombination deme) state =
      rates.recombination deme / 2 *
        ((recombinationCoordinateExpansion deme).coordinate feature).velocity state :=
    fun _ ↦ rfl
  simp only [hvelocity]
  cases feature with
  | H first second =>
      simp only [PulseCoordinateExpansion.coordinate,
        recombinationLeftHeterozygosity_velocity, mul_zero, Finset.sum_const_zero]
      rfl
  | DD first second =>
      simp only [PulseCoordinateExpansion.coordinate,
        recombinationLinkageProduct_velocity]
      have hsplit : ∀ deme : Fin D,
          rates.recombination deme / 2 *
            (-((if first = deme then (1 : ℝ) else 0) +
                (if second = deme then (1 : ℝ) else 0)) *
              (twoLocusDDJet first second).value state) =
            -((twoLocusDDJet first second).value state / 2) *
              (rates.recombination deme * (if first = deme then (1 : ℝ) else 0)) +
            -((twoLocusDDJet first second).value state / 2) *
              (rates.recombination deme * (if second = deme then (1 : ℝ) else 0)) :=
        fun _ ↦ by ring
      simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, sum_rate_indicator]
      simp only [lowOrderLDRecombination, twoLocusJetMoment, twoLocusCoordinateJet,
        twoLocusDDJet, TwoLocusDiffusionJet.mul, twoLocusLinkageJet]
      ring
  | Dz first second third =>
      simp only [PulseCoordinateExpansion.coordinate, recombinationDzObservable_velocity]
      have hsplit : ∀ deme : Fin D,
          rates.recombination deme / 2 *
            (-(if first = deme then (1 : ℝ) else 0) *
              (twoLocusDzJet first second third).value state) =
            -((twoLocusDzJet first second third).value state / 2) *
              (rates.recombination deme * (if first = deme then (1 : ℝ) else 0)) :=
        fun _ ↦ by ring
      simp only [hsplit, ← Finset.mul_sum, sum_rate_indicator]
      simp only [lowOrderLDRecombination, twoLocusJetMoment, twoLocusCoordinateJet]
      ring
  | pi2 first second third fourth =>
      simp only [PulseCoordinateExpansion.coordinate,
        recombinationJointHeterozygosity_velocity, mul_zero, Finset.sum_const_zero]
      rfl

/-- The recombination stages leave every right-locus heterozygosity coordinate alone, which
is why the enlarged generator's `H^R` rows carry no recombination term. -/
theorem recombinationStage_sum_rightHeterozygosity {D : ℕ} (rates : ManyDemeLDRates D)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    ∑ deme : Fin D, stageRate rates (Stage.recombination deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.recombination deme) state = 0 := by
  have hvelocity : ∀ deme : Fin D,
      stageRate rates (Stage.recombination deme) *
        stageVelocity (enlargedStageExpansion (some (.inr (first, second))))
          (Stage.recombination deme) state =
      rates.recombination deme / 2 *
        ((recombinationCoordinateExpansion deme).rightHeterozygosity first second).velocity
          state := fun _ ↦ rfl
  simp [hvelocity, recombinationRightHeterozygosity_velocity]

end

end Descent.Portability.TwoLocusMicroscopicKernel
