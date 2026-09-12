/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StageCompositionKernel
import Descent.Portability.Pi2GeneratorBridges
import Descent.Portability.SimultaneousMigrationPulse

assert_below Descent.Decision Descent.Program

/-!
# The two-locus microscopic step built by composing the physical stages

NOTE1 section 2.3 defines one microscopic step by composing physical stages: migration,
recombination, allele flips at both loci, and resampling in each deme, each run at step `h`
with its own rate.  The corpus's first approximation of `enlargedLowOrderLDGenerator` chose one
stage at random (`TwoLocusMicroscopicApproximation.enlargedMicroscopicApproximation`).  This
module builds the note's literal composition and proves that it is a second
`MicroscopicApproximation` of the same generator, with nothing assumed.

The physical stages.  `PhysicalStage D` has four kinds: resampling in each deme, one migration
stage, recombination in each deme, and one allele-flip stage per deme.  The migration stage is
the note's stage 1, the deterministic convex haplotype mixture in which every recipient takes
the fraction `h m_ij` from every source at once (`SimultaneousMigrationPulse`); its rate-weighted
velocity is the sum of the corpus's per-pair migration drifts
(`SimultaneousMigrationPulse.simultaneousMigrationExpansion_velocity`).  The allele-flip stage
is the note's stage 3, independent symmetric flips at BOTH loci:
`bothMutationPulseAt` runs the corpus's left-locus pulse and then its right-locus pulse at the
same parameter.  Its three base coordinate laws are exact (`bothMutationPulseAt_leftFrequency`,
`_rightFrequency`, `_linkage`, the last with an explicit quadratic term), so every enlarged
coordinate carries a pulse expansion (`bothMutationExpansion`).  `coordinate_velocity_add` and
`rightHeterozygosity_velocity_add` show that the Leibniz-built velocity of any closed low-order
coordinate is additive in the base velocities, whence the both-loci velocity is the sum of the
left-locus and right-locus velocities of the corpus certificates
(`bothMutationExpansion_velocity`).

Why composition needs a matrix per stage.  `StageCompositionKernel.composeStages_expansion`
controls the cross terms of a composition only when each stage's first-order action on the
feature family is a matrix applied to the features.  The identification the corpus proves,
`Pi2GeneratorBridges.stage_generator_enlarged`, is for the SUM over stages.  Individual stages
are separated through the rates: the stage velocities of the corpus certificates do not depend
on the rates, and `stage_generator_enlarged` holds at every rate law.  Doubling one deme's
coalescence rate, switching off all migration, or zeroing one deme's recombination or mutation
rate changes the generator by exactly that stage's rate-weighted velocity
(`physicalStageDrift_eq_mulVec`).
`physicalGenerator` is that difference of two corpus generators.  The left-locus and right-locus
flips share the parameter `theta_i`, so they are separated only jointly; that is why the
allele-flip stage flips both loci.

The approximation.  `physicalStageKernel_expansion` is the per-stage first-order estimate,
taken from the corpus's `apply_stageKernel_expansion` and `apply_pulseStageKernel_expansion`.
`sum_physicalStageDrift` regroups the four physical kinds into the corpus's five stage
families, so the summed stage matrices agree with `enlargedLowOrderLDGenerator rates` on every
feature vector.  `compositionMicroscopicApproximation` is the resulting
`MicroscopicApproximation`: the kernel at step `h` is the composition of all physical stages
at step `h` in a fixed enumeration (`stageOrder`), and the error is
`StageCompositionKernel.compositeSlack`, the total per-stage slack plus `h` times an explicit
constant.  No deme is needed as data, because a step with no stages is the idle kernel.

Scope.  Resampling here is the corpus's single-draw stage calibrated by
`RandomStageKernel.driftChromosomeCount`.  The composition with NOTE1's multinomial sample of
`ceil (1 / (c h))` chromosomes is
`MultinomialStageComposition.multinomialCompositionApproximation`, which reuses every other
stage and every stage matrix of this module.  The error bound is crude and explicit; no rate of
convergence beyond "vanishes with `h`" is claimed.

## Empirical status

None.  The bodies here are algebra: finite averages of polynomial coordinates against
probability weights, differences of corpus generator matrices, and bounds between them.  No
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TwoLocusStageComposition

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.PulseJetExpansion
open Descent.Portability.RandomStageKernel
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel
open Descent.Portability.Pi2GeneratorBridges
open Descent.Portability.StageCompositionKernel
open Descent.Portability.SimultaneousMigrationPulse

noncomputable section

/-! ## Allele flips at both loci -/

/-- The allele-flip stage of NOTE1 section 2.3 in one deme: independent symmetric flips at both
loci, run as the left-locus pulse followed by the right-locus pulse at the same parameter. -/
def bothMutationPulseAt {D : ℕ} (target : Fin D) (tau : ℝ) (state : DemeHaplotypeState D) :
    DemeHaplotypeState D :=
  rightMutationPulseAt target tau (leftMutationPulseAt target tau state)

/-- Flipping both loci moves each left marginal exactly by the sum of the two single-locus
velocities. -/
theorem bothMutationPulseAt_leftFrequency {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (bothMutationPulseAt target tau state index).leftFrequency =
      (state index).leftFrequency +
        tau * ((leftMutationLeftExpansion target index).velocity state +
          (rightMutationLeftExpansion target index).velocity state) := by
  simp only [bothMutationPulseAt, leftMutationLeftExpansion, rightMutationLeftExpansion]
  rw [rightMutationPulseAt_leftFrequency, leftMutationPulseAt_leftFrequency target index h0 h1]
  ring

/-- Flipping both loci moves each right marginal exactly by the sum of the two single-locus
velocities: the left-locus flip leaves the right contrast alone. -/
theorem bothMutationPulseAt_rightFrequency {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (bothMutationPulseAt target tau state index).rightFrequency =
      (state index).rightFrequency +
        tau * ((leftMutationRightExpansion target index).velocity state +
          (rightMutationRightExpansion target index).velocity state) := by
  have hcontrast : (leftMutationPulseAt target tau state target).rightContrast =
      (state target).rightContrast := by
    simp only [TwoLocusHaplotypeFrequencies.rightContrast]
    rw [leftMutationPulseAt_rightFrequency]
    ring
  simp only [bothMutationPulseAt, leftMutationRightExpansion, rightMutationRightExpansion]
  rw [rightMutationPulseAt_rightFrequency target index h0 h1, hcontrast,
    leftMutationPulseAt_rightFrequency]
  ring

/-- Flipping both loci damps linkage by the sum of the two single-locus velocities, plus the
product term `4 tau² D` of the two damping factors. -/
theorem bothMutationPulseAt_linkage {D : ℕ} (target index : Fin D) {tau : ℝ}
    (h0 : 0 ≤ tau) (h1 : tau ≤ 1) (state : DemeHaplotypeState D) :
    (bothMutationPulseAt target tau state index).linkage =
      (state index).linkage +
        tau * ((leftMutationLinkageExpansion target index).velocity state +
          (rightMutationLinkageExpansion target index).velocity state) +
        4 * tau ^ 2 * (if index = target then (state target).linkage else 0) := by
  have hinner : (leftMutationPulseAt target tau state target).linkage =
      (state target).linkage + tau * (-2 * (state target).linkage) := by
    rw [leftMutationPulseAt_linkage target target h0 h1, if_pos rfl]
  simp only [bothMutationPulseAt, leftMutationLinkageExpansion, rightMutationLinkageExpansion]
  rw [rightMutationPulseAt_linkage target index h0 h1,
    leftMutationPulseAt_linkage target index h0 h1, hinner]
  by_cases hindex : index = target
  · simp only [if_pos hindex]
    ring
  · simp only [if_neg hindex]
    ring

/-- The left marginal under the both-loci flip, with velocity the sum of the single-locus
velocities and no remainder. -/
def bothMutationLeftExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (bothMutationPulseAt target) (fun state ↦ (state index).leftFrequency) where
  velocity state := (leftMutationLeftExpansion target index).velocity state +
    (rightMutationLeftExpansion target index).velocity state
  valueBound := (leftMutationLeftExpansion target index).valueBound
  velocityBound := (leftMutationLeftExpansion target index).velocityBound +
    (rightMutationLeftExpansion target index).velocityBound
  remainder := 0
  value_abs_le state := (leftMutationLeftExpansion target index).value_abs_le state
  velocity_abs_le state := (abs_add_le _ _).trans
    (add_le_add ((leftMutationLeftExpansion target index).velocity_abs_le state)
      ((rightMutationLeftExpansion target index).velocity_abs_le state))
  expansion tau h0 h1 state := by
    rw [bothMutationPulseAt_leftFrequency target index h0 h1 state]
    calc _ = |(0 : ℝ)| := by congr 1; ring
      _ ≤ 0 * tau ^ 2 := by simp

/-- The right marginal under the both-loci flip, with velocity the sum of the single-locus
velocities and no remainder. -/
def bothMutationRightExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (bothMutationPulseAt target) (fun state ↦ (state index).rightFrequency) where
  velocity state := (leftMutationRightExpansion target index).velocity state +
    (rightMutationRightExpansion target index).velocity state
  valueBound := (leftMutationRightExpansion target index).valueBound
  velocityBound := (leftMutationRightExpansion target index).velocityBound +
    (rightMutationRightExpansion target index).velocityBound
  remainder := 0
  value_abs_le state := (leftMutationRightExpansion target index).value_abs_le state
  velocity_abs_le state := (abs_add_le _ _).trans
    (add_le_add ((leftMutationRightExpansion target index).velocity_abs_le state)
      ((rightMutationRightExpansion target index).velocity_abs_le state))
  expansion tau h0 h1 state := by
    rw [bothMutationPulseAt_rightFrequency target index h0 h1 state]
    calc _ = |(0 : ℝ)| := by congr 1; ring
      _ ≤ 0 * tau ^ 2 := by simp

/-- The linkage determinant under the both-loci flip, with velocity the sum of the single-locus
velocities and quadratic remainder one. -/
def bothMutationLinkageExpansion {D : ℕ} (target index : Fin D) :
    PulseExpansion (bothMutationPulseAt target) (fun state ↦ (state index).linkage) where
  velocity state := (leftMutationLinkageExpansion target index).velocity state +
    (rightMutationLinkageExpansion target index).velocity state
  valueBound := (leftMutationLinkageExpansion target index).valueBound
  velocityBound := (leftMutationLinkageExpansion target index).velocityBound +
    (rightMutationLinkageExpansion target index).velocityBound
  remainder := 1
  value_abs_le state := (leftMutationLinkageExpansion target index).value_abs_le state
  velocity_abs_le state := (abs_add_le _ _).trans
    (add_le_add ((leftMutationLinkageExpansion target index).velocity_abs_le state)
      ((rightMutationLinkageExpansion target index).velocity_abs_le state))
  expansion tau h0 h1 state := by
    rw [bothMutationPulseAt_linkage target index h0 h1 state]
    have hquarter := (state target).linkage_abs_le_quarter
    by_cases hindex : index = target
    · simp only [if_pos hindex]
      calc _ = |4 * tau ^ 2 * (state target).linkage| := by congr 1; ring
        _ = 4 * tau ^ 2 * |(state target).linkage| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 4 * tau ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hquarter (by positivity)
        _ = 1 * tau ^ 2 := by ring
    · simp only [if_neg hindex]
      calc _ = |(0 : ℝ)| := by congr 1; ring
        _ ≤ 1 * tau ^ 2 := by
            rw [abs_zero]
            positivity

/-- The base coordinate expansions of the both-loci allele flip. -/
def bothMutationCoordinateExpansion {D : ℕ} (target : Fin D) :
    PulseCoordinateExpansion (bothMutationPulseAt target) where
  leftMarginal := bothMutationLeftExpansion target
  rightMarginal := bothMutationRightExpansion target
  linkageDeterminant := bothMutationLinkageExpansion target

/-! ## Velocities are additive in the base velocities -/

/-- **The Leibniz-built velocity of every closed low-order coordinate is additive in the base
velocities.**  If the three base velocities of one pulse family are pointwise the sums of those
of two others, so is the velocity of every `H`, `DD`, `Dz` and `pi2` coordinate. -/
theorem coordinate_velocity_add {D : ℕ}
    {pulse leftPulse rightPulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
    (base : PulseCoordinateExpansion pulse) (leftBase : PulseCoordinateExpansion leftPulse)
    (rightBase : PulseCoordinateExpansion rightPulse)
    (hleft : ∀ index state, (base.leftMarginal index).velocity state =
      (leftBase.leftMarginal index).velocity state + (rightBase.leftMarginal index).velocity state)
    (hright : ∀ index state, (base.rightMarginal index).velocity state =
      (leftBase.rightMarginal index).velocity state +
        (rightBase.rightMarginal index).velocity state)
    (hlinkage : ∀ index state, (base.linkageDeterminant index).velocity state =
      (leftBase.linkageDeterminant index).velocity state +
        (rightBase.linkageDeterminant index).velocity state)
    (feature : LowOrderLDCoordinate D) (state : DemeHaplotypeState D) :
    (base.coordinate feature).velocity state =
      (leftBase.coordinate feature).velocity state +
        (rightBase.coordinate feature).velocity state := by
  cases feature <;>
    simp only [PulseCoordinateExpansion.coordinate, PulseCoordinateExpansion.leftHeterozygosity,
      PulseCoordinateExpansion.rightHeterozygosity, PulseCoordinateExpansion.linkageProduct,
      PulseCoordinateExpansion.dzObservable, PulseCoordinateExpansion.jointHeterozygosity,
      PulseExpansion.ofEq, PulseExpansion.add, PulseExpansion.smul, PulseExpansion.mul,
      PulseExpansion.const, hleft, hright, hlinkage] <;>
    ring

/-- The velocity of every right-locus heterozygosity is additive in the right base velocities. -/
theorem rightHeterozygosity_velocity_add {D : ℕ}
    {pulse leftPulse rightPulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
    (base : PulseCoordinateExpansion pulse) (leftBase : PulseCoordinateExpansion leftPulse)
    (rightBase : PulseCoordinateExpansion rightPulse)
    (hright : ∀ index state, (base.rightMarginal index).velocity state =
      (leftBase.rightMarginal index).velocity state +
        (rightBase.rightMarginal index).velocity state)
    (first second : Fin D) (state : DemeHaplotypeState D) :
    (base.rightHeterozygosity first second).velocity state =
      (leftBase.rightHeterozygosity first second).velocity state +
        (rightBase.rightHeterozygosity first second).velocity state := by
  simp only [PulseCoordinateExpansion.rightHeterozygosity, PulseExpansion.ofEq,
    PulseExpansion.add, PulseExpansion.smul, PulseExpansion.mul, PulseExpansion.const, hright]
  ring

/-- The both-loci allele-flip expansion of every enlarged coordinate. -/
def bothMutationExpansion {D : ℕ} (target : Fin D) :
    (coordinate : AffineEnlargedCoordinate D) →
      PulseExpansion (bothMutationPulseAt target) (enlargedCoordinateJet coordinate).value
  | none => PulseExpansion.const D (bothMutationPulseAt target) 1
  | some (.inl feature) => (bothMutationCoordinateExpansion target).coordinate feature
  | some (.inr pair) =>
      (bothMutationCoordinateExpansion target).rightHeterozygosity pair.1 pair.2

/-- **The both-loci velocity is the sum of the corpus's single-locus velocities**, at every
enlarged coordinate. -/
theorem bothMutationExpansion_velocity {D : ℕ} (target : Fin D)
    (coordinate : AffineEnlargedCoordinate D) (state : DemeHaplotypeState D) :
    (bothMutationExpansion target coordinate).velocity state =
      ((enlargedStageExpansion coordinate).mutationLeft target).velocity state +
        ((enlargedStageExpansion coordinate).mutationRight target).velocity state := by
  rcases coordinate with _ | (feature | ⟨first, second⟩)
  · simp [bothMutationExpansion, enlargedStageExpansion, constantStageExpansion,
      PulseExpansion.const]
  · exact coordinate_velocity_add (bothMutationCoordinateExpansion target)
      (leftMutationCoordinateExpansion target) (rightMutationCoordinateExpansion target)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) feature state
  · exact rightHeterozygosity_velocity_add (bothMutationCoordinateExpansion target)
      (leftMutationCoordinateExpansion target) (rightMutationCoordinateExpansion target)
      (fun _ _ ↦ rfl) first second state

/-! ## The physical stages -/

/-- The physical stages of one composed microscopic step for `demeCount` demes: resampling in
each deme, one simultaneous migration stage for all ordered pairs, recombination in each deme,
and one allele-flip stage at both loci in each deme. -/
inductive PhysicalStage (demeCount : ℕ) where
  | drift (deme : Fin demeCount)
  | migration
  | recombination (deme : Fin demeCount)
  | mutation (deme : Fin demeCount)
deriving DecidableEq, Fintype

/-- The kernel of each physical stage at step `step`, each at its own rate.  The migration
stage runs the simultaneous convex mixture at rate `1 + M`, which gives the literal fractions
`step · m_ij` for small steps. -/
def physicalStageKernel {D : ℕ} (rates : ManyDemeLDRates D) :
    PhysicalStage D → ℝ → FiniteMixtureKernel TwoLocusHaplotype (DemeHaplotypeState D)
  | .drift deme => stageKernel rates (.drift deme)
  | .migration =>
      pulseStageKernel (simultaneousMigrationPulse rates) (1 + totalMigration rates)
  | .recombination deme => stageKernel rates (.recombination deme)
  | .mutation deme => pulseStageKernel (bothMutationPulseAt deme) (rates.mutation deme / 2)

/-- The rate-weighted first-order velocity of each physical stage on one enlarged coordinate. -/
def physicalStageDrift {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) : PhysicalStage D → DemeHaplotypeState D → ℝ
  | .drift deme => stageDrift rates (enlargedStageExpansion coordinate) (.drift deme)
  | .migration => fun state ↦
      (1 + totalMigration rates) * (simultaneousMigrationExpansion rates coordinate).velocity state
  | .recombination deme =>
      stageDrift rates (enlargedStageExpansion coordinate) (.recombination deme)
  | .mutation deme => fun state ↦
      rates.mutation deme / 2 * (bothMutationExpansion deme coordinate).velocity state

/-- The slack of each physical stage on one enlarged coordinate. -/
def physicalStageSlack {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) : PhysicalStage D → ℝ → ℝ
  | .drift deme => stageSlack rates (enlargedStageExpansion coordinate) (.drift deme)
  | .migration =>
      pulseStageSlack (1 + totalMigration rates)
        (simultaneousMigrationExpansion rates coordinate).valueBound
        (simultaneousMigrationExpansion rates coordinate).velocityBound
        (simultaneousMigrationExpansion rates coordinate).remainder
  | .recombination deme =>
      stageSlack rates (enlargedStageExpansion coordinate) (.recombination deme)
  | .mutation deme =>
      pulseStageSlack (rates.mutation deme / 2) (bothMutationExpansion deme coordinate).valueBound
        (bothMutationExpansion deme coordinate).velocityBound
        (bothMutationExpansion deme coordinate).remainder

/-- **Every physical stage expands to first order.**  One stage at step `step` advances every
enlarged coordinate by `step` times its rate-weighted velocity, up to `step` times its slack. -/
theorem physicalStageKernel_expansion {D : ℕ} (rates : ManyDemeLDRates D)
    (stage : PhysicalStage D) (coordinate : AffineEnlargedCoordinate D) (step : ℝ)
    (hstep : 0 < step) (state : DemeHaplotypeState D) :
    |(physicalStageKernel rates stage step).apply
          (fun y ↦ enlargedLowOrderLDFeature y coordinate) state -
        enlargedLowOrderLDFeature state coordinate -
        step * physicalStageDrift rates coordinate stage state| ≤
      step * physicalStageSlack rates coordinate stage step := by
  rw [enlargedFeature_eq_jet_value coordinate, ← enlargedCoordinateJet_value coordinate state]
  cases stage with
  | drift deme =>
      exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate) (.drift deme)
        step hstep state
  | migration =>
      exact apply_pulseStageKernel_expansion (simultaneousMigrationExpansion rates coordinate)
        (1 + totalMigration rates) step (by linarith [totalMigration_nonneg rates]) hstep.le state
  | recombination deme =>
      exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate)
        (.recombination deme) step hstep state
  | mutation deme =>
      exact apply_pulseStageKernel_expansion (bothMutationExpansion deme coordinate)
        (rates.mutation deme / 2) step (by linarith [rates.mutation_nonneg deme]) hstep.le state

/-- Every physical stage's slack vanishes with the step size. -/
theorem physicalStageSlack_tendsto {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (stage : PhysicalStage D) :
    Filter.Tendsto (physicalStageSlack rates coordinate stage) (nhds 0) (nhds 0) := by
  cases stage with
  | drift deme =>
      exact stageSlack_tendsto rates (enlargedStageExpansion coordinate) (.drift deme)
  | migration => exact pulseStageSlack_tendsto _ _ _ _
  | recombination deme =>
      exact stageSlack_tendsto rates (enlargedStageExpansion coordinate) (.recombination deme)
  | mutation deme => exact pulseStageSlack_tendsto _ _ _ _

/-- The physical stage index is the disjoint union of its four constructor families. -/
def physicalStageStructure (D : ℕ) :
    (Fin D ⊕ Unit ⊕ Fin D ⊕ Fin D) ≃ PhysicalStage D where
  toFun
    | .inl deme => .drift deme
    | .inr (.inl _) => .migration
    | .inr (.inr (.inl deme)) => .recombination deme
    | .inr (.inr (.inr deme)) => .mutation deme
  invFun
    | .drift deme => .inl deme
    | .migration => .inr (.inl ())
    | .recombination deme => .inr (.inr (.inl deme))
    | .mutation deme => .inr (.inr (.inr deme))
  left_inv := by rintro (_ | (_ | (_ | _))) <;> rfl
  right_inv := by rintro (_ | _ | _ | _) <;> rfl

/-- A sum over the physical stages splits into its four families. -/
theorem sum_physicalStage {D : ℕ} (summand : PhysicalStage D → ℝ) :
    ∑ stage : PhysicalStage D, summand stage =
      (∑ deme : Fin D, summand (PhysicalStage.drift deme)) +
      summand PhysicalStage.migration +
      (∑ deme : Fin D, summand (PhysicalStage.recombination deme)) +
      (∑ deme : Fin D, summand (PhysicalStage.mutation deme)) := by
  rw [← Equiv.sum_comp (physicalStageStructure D) summand]
  simp only [Fintype.sum_sum_type, physicalStageStructure, Equiv.coe_fn_mk, Fintype.sum_unique]
  ring

/-- **The physical stages carry the same total velocity as the corpus's five stage families.**
The simultaneous migration stage carries every ordered pair's migration drift together, and the
allele-flip stage at both loci the left-locus and right-locus flip velocities together. -/
theorem sum_physicalStageDrift {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (state : DemeHaplotypeState D) :
    ∑ stage : PhysicalStage D, physicalStageDrift rates coordinate stage state =
      ∑ stage : Stage D, stageDrift rates (enlargedStageExpansion coordinate) stage state := by
  rw [sum_physicalStage, sum_stage]
  simp only [physicalStageDrift, simultaneousMigrationExpansion_velocity,
    bothMutationExpansion_velocity, stageDrift, stageRate, stageVelocity, mul_add,
    Finset.sum_add_distrib]
  ring

/-! ## Separating the stages through the rates -/

/-- The rate law with one deme's coalescence rate doubled. -/
def doubledCoalescenceRates {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) :
    ManyDemeLDRates D :=
  { rates with
    coalescence := fun other ↦
      rates.coalescence other + if other = deme then rates.coalescence other else 0
    coalescence_pos := fun other ↦ by
      have hpos := rates.coalescence_pos other
      split_ifs <;> linarith }

/-- The rate law with every migration rate switched off. -/
def withoutMigrationRates {D : ℕ} (rates : ManyDemeLDRates D) : ManyDemeLDRates D :=
  { rates with
    migration := fun _ _ ↦ 0
    migration_nonneg := fun _ _ ↦ le_rfl
    migration_self := fun _ ↦ rfl }

/-- The rate law with one deme's recombination rate switched off. -/
def withoutRecombinationRates {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) :
    ManyDemeLDRates D :=
  { rates with
    recombination := fun other ↦ if other = deme then 0 else rates.recombination other
    recombination_nonneg := fun other ↦ by
      split_ifs
      · exact le_rfl
      · exact rates.recombination_nonneg other }

/-- The rate law with one deme's mutation rate switched off. -/
def withoutMutationRates {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) :
    ManyDemeLDRates D :=
  { rates with
    mutation := fun other ↦ if other = deme then 0 else rates.mutation other
    mutation_nonneg := fun other ↦ by
      split_ifs
      · exact le_rfl
      · exact rates.mutation_nonneg other }

/-- The matrix of one physical stage: the change in the corpus enlarged generator when that
stage's rate is doubled (resampling) or switched off (every other stage). -/
def physicalGenerator {D : ℕ} (rates : ManyDemeLDRates D) :
    PhysicalStage D → Matrix (AffineEnlargedCoordinate D) (AffineEnlargedCoordinate D) ℝ
  | .drift deme =>
      enlargedLowOrderLDGenerator (doubledCoalescenceRates rates deme) -
        enlargedLowOrderLDGenerator rates
  | .migration =>
      enlargedLowOrderLDGenerator rates -
        enlargedLowOrderLDGenerator (withoutMigrationRates rates)
  | .recombination deme =>
      enlargedLowOrderLDGenerator rates -
        enlargedLowOrderLDGenerator (withoutRecombinationRates rates deme)
  | .mutation deme =>
      enlargedLowOrderLDGenerator rates -
        enlargedLowOrderLDGenerator (withoutMutationRates rates deme)

/-- The difference of two corpus enlarged generators, applied to a feature vector, is the sum
of the stage velocities weighted by the rate differences.  The certificates' velocities do not
depend on the rates, so this is two instances of `stage_generator_enlarged` subtracted. -/
theorem generatorDifference_mulVec {D : ℕ} (rates other : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (state : DemeHaplotypeState D) :
    (enlargedLowOrderLDGenerator rates - enlargedLowOrderLDGenerator other).mulVec
        (enlargedLowOrderLDFeature state) coordinate =
      ∑ stage : Stage D, (stageRate rates stage - stageRate other stage) *
        stageVelocity (enlargedStageExpansion coordinate) stage state := by
  rw [Matrix.sub_mulVec, Pi.sub_apply, stage_generator_enlarged, stage_generator_enlarged,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun stage _ ↦ by
    simp only [stageDrift]
    ring

/-- **Each physical stage acts on the features through its own matrix.**  The rate-weighted
velocity of one physical stage on an enlarged coordinate is its generator difference applied
to the feature vector. -/
theorem physicalStageDrift_eq_mulVec {D : ℕ} (rates : ManyDemeLDRates D)
    (stage : PhysicalStage D) (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    physicalStageDrift rates coordinate stage state =
      (physicalGenerator rates stage).mulVec (enlargedLowOrderLDFeature state) coordinate := by
  cases stage with
  | drift deme =>
      have hdifference : ∀ other : Stage D,
          stageRate (doubledCoalescenceRates rates deme) other - stageRate rates other =
            if other = .drift deme then stageRate rates other else 0 := by
        intro other
        cases other with
        | drift otherDeme =>
            show (rates.coalescence otherDeme +
                if otherDeme = deme then rates.coalescence otherDeme else 0) -
                rates.coalescence otherDeme =
              if Stage.drift otherDeme = Stage.drift deme then rates.coalescence otherDeme
              else 0
            by_cases hdeme : otherDeme = deme
            · rw [if_pos hdeme, if_pos (by rw [hdeme])]
              ring
            · rw [if_neg hdeme, if_neg fun hequal ↦ hdeme (Stage.drift.inj hequal)]
              ring
        | _ =>
            rw [if_neg (by simp)]
            exact sub_self _
      rw [physicalGenerator, generatorDifference_mulVec]
      simp only [hdifference, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  | migration =>
      rw [physicalGenerator, generatorDifference_mulVec, sum_stage]
      simp only [physicalStageDrift, simultaneousMigrationExpansion_velocity, stageDrift,
        stageRate, stageVelocity, withoutMigrationRates, sub_self, sub_zero, zero_mul,
        Finset.sum_const_zero, zero_add, add_zero]
  | recombination deme =>
      have hdifference : ∀ other : Stage D,
          stageRate rates other - stageRate (withoutRecombinationRates rates deme) other =
            if other = .recombination deme then stageRate rates other else 0 := by
        intro other
        cases other with
        | recombination otherDeme =>
            show rates.recombination otherDeme / 2 -
                (if otherDeme = deme then 0 else rates.recombination otherDeme) / 2 =
              if Stage.recombination otherDeme = Stage.recombination deme
              then rates.recombination otherDeme / 2 else 0
            by_cases hdeme : otherDeme = deme
            · rw [if_pos hdeme, if_pos (by rw [hdeme])]
              ring
            · rw [if_neg hdeme, if_neg fun hequal ↦ hdeme (Stage.recombination.inj hequal)]
              ring
        | _ =>
            rw [if_neg (by simp)]
            exact sub_self _
      rw [physicalGenerator, generatorDifference_mulVec]
      simp only [hdifference, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  | mutation deme =>
      have hdifference : ∀ other : Stage D,
          stageRate rates other - stageRate (withoutMutationRates rates deme) other =
            (if other = .mutationLeft deme then stageRate rates other else 0) +
              (if other = .mutationRight deme then stageRate rates other else 0) := by
        intro other
        cases other with
        | mutationLeft otherDeme =>
            show rates.mutation otherDeme / 2 -
                (if otherDeme = deme then 0 else rates.mutation otherDeme) / 2 =
              (if Stage.mutationLeft otherDeme = Stage.mutationLeft deme
                then rates.mutation otherDeme / 2 else 0) +
              (if Stage.mutationLeft otherDeme = Stage.mutationRight deme
                then rates.mutation otherDeme / 2 else 0)
            rw [if_neg (show Stage.mutationLeft otherDeme ≠ Stage.mutationRight deme by simp)]
            by_cases hdeme : otherDeme = deme
            · rw [if_pos hdeme, if_pos (by rw [hdeme])]
              ring
            · rw [if_neg hdeme, if_neg fun hequal ↦ hdeme (Stage.mutationLeft.inj hequal)]
              ring
        | mutationRight otherDeme =>
            show rates.mutation otherDeme / 2 -
                (if otherDeme = deme then 0 else rates.mutation otherDeme) / 2 =
              (if Stage.mutationRight otherDeme = Stage.mutationLeft deme
                then rates.mutation otherDeme / 2 else 0) +
              (if Stage.mutationRight otherDeme = Stage.mutationRight deme
                then rates.mutation otherDeme / 2 else 0)
            rw [if_neg (show Stage.mutationRight otherDeme ≠ Stage.mutationLeft deme by simp)]
            by_cases hdeme : otherDeme = deme
            · rw [if_pos hdeme, if_pos (by rw [hdeme])]
              ring
            · rw [if_neg hdeme, if_neg fun hequal ↦ hdeme (Stage.mutationRight.inj hequal)]
              ring
        | _ =>
            rw [if_neg (by simp), if_neg (by simp)]
            exact sub_self _ |>.trans (add_zero 0).symm
      rw [physicalGenerator, generatorDifference_mulVec]
      simp only [hdifference, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [physicalStageDrift, bothMutationExpansion_velocity, stageRate, stageVelocity]
      ring

/-! ## The composed microscopic approximation -/

/-- The fixed enumeration of the physical stages in which the composed step runs them. -/
def stageOrder (D : ℕ) : PhysicalStage D ≃ Fin (Fintype.card (PhysicalStage D)) :=
  Fintype.equivFin (PhysicalStage D)

/-- A uniform bound on every enlarged feature coordinate, read off the resampling
certificates. -/
def compositionFeatureBound (D : ℕ) : ℝ :=
  ∑ coordinate : AffineEnlargedCoordinate D, (enlargedStageExpansion coordinate).drift.bound

/-- Every enlarged feature coordinate is bounded by `compositionFeatureBound`. -/
theorem abs_enlargedFeature_le {D : ℕ} (state : DemeHaplotypeState D)
    (coordinate : AffineEnlargedCoordinate D) :
    |enlargedLowOrderLDFeature state coordinate| ≤ compositionFeatureBound D := by
  rw [← enlargedCoordinateJet_value coordinate state]
  exact ((enlargedStageExpansion coordinate).drift.value_le state).trans
    (Finset.single_le_sum (fun other _ ↦ (enlargedStageExpansion other).drift.bound_nonneg)
      (Finset.mem_univ coordinate))

/-- The feature bound is nonnegative. -/
theorem compositionFeatureBound_nonneg (D : ℕ) : 0 ≤ compositionFeatureBound D :=
  Finset.sum_nonneg fun coordinate _ ↦ (enlargedStageExpansion coordinate).drift.bound_nonneg

/-- A uniform bound on the absolute row sums of every physical stage matrix. -/
def compositionRowBound {D : ℕ} (rates : ManyDemeLDRates D) : ℝ :=
  ∑ stage : PhysicalStage D, ∑ row : AffineEnlargedCoordinate D,
    ∑ column : AffineEnlargedCoordinate D, |physicalGenerator rates stage row column|

/-- Every row of every physical stage matrix has absolute sum at most `compositionRowBound`. -/
theorem physicalGenerator_row_le {D : ℕ} (rates : ManyDemeLDRates D) (stage : PhysicalStage D)
    (row : AffineEnlargedCoordinate D) :
    ∑ column, |physicalGenerator rates stage row column| ≤ compositionRowBound rates :=
  stageRow_le_totalMass (physicalGenerator rates) stage row

/-- The slack of one physical stage over all enlarged coordinates. -/
def compositionStageSlack {D : ℕ} (rates : ManyDemeLDRates D) (stage : PhysicalStage D)
    (step : ℝ) : ℝ :=
  ∑ coordinate : AffineEnlargedCoordinate D, |physicalStageSlack rates coordinate stage step|

/-- The summed stage matrices agree with the corpus enlarged generator on every feature
vector. -/
theorem sum_physicalGenerator_mulVec {D : ℕ} (rates : ManyDemeLDRates D)
    (state : DemeHaplotypeState D) (coordinate : AffineEnlargedCoordinate D) :
    (∑ k, physicalGenerator rates ((stageOrder D).symm k)).mulVec
        (enlargedLowOrderLDFeature state) coordinate =
      (enlargedLowOrderLDGenerator rates).mulVec (enlargedLowOrderLDFeature state)
        coordinate := by
  have hsplit : (∑ k, physicalGenerator rates ((stageOrder D).symm k)).mulVec
      (enlargedLowOrderLDFeature state) coordinate =
      ∑ k, (physicalGenerator rates ((stageOrder D).symm k)).mulVec
        (enlargedLowOrderLDFeature state) coordinate := by
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hsplit, stage_generator_enlarged rates state coordinate]
  simp only [← physicalStageDrift_eq_mulVec]
  rw [Equiv.sum_comp (stageOrder D).symm
    (fun stage ↦ physicalStageDrift rates coordinate stage state)]
  exact sum_physicalStageDrift rates coordinate state

/-- **NOTE1 equation (11) for the composed step, with nothing assumed.**  The step that runs
every physical stage of NOTE1 section 2.3 in a fixed order at step `h`, each at its own rate,
is a family of genuine probability kernels advancing every enlarged coordinate by
`h · enlargedLowOrderLDGenerator rates` applied to the feature vector, uniformly in the state,
with an explicit error that vanishes with `h`.  This is a second `MicroscopicApproximation` of
the enlarged generator, built by composition rather than by a random choice of stage. -/
def compositionMicroscopicApproximation {D : ℕ} (rates : ManyDemeLDRates D) :
    MicroscopicApproximation (B := Fin (Fintype.card (PhysicalStage D)) → TwoLocusHaplotype)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates) :=
  composedMicroscopicApproximation (enlargedLowOrderLDFeature (D := D))
    (compositionFeatureBound D) (compositionFeatureBound_nonneg D) abs_enlargedFeature_le
    (Fintype.card (PhysicalStage D))
    (fun k ↦ physicalStageKernel rates ((stageOrder D).symm k))
    (fun k ↦ physicalGenerator rates ((stageOrder D).symm k)) (compositionRowBound rates)
    (Finset.sum_nonneg fun stage _ ↦ Finset.sum_nonneg fun row _ ↦
      Finset.sum_nonneg fun column _ ↦ abs_nonneg _)
    (fun k row ↦ physicalGenerator_row_le rates ((stageOrder D).symm k) row)
    (fun k step ↦ compositionStageSlack rates ((stageOrder D).symm k) step)
    (fun k step ↦ Finset.sum_nonneg fun coordinate _ ↦ abs_nonneg _)
    (fun k ↦ sum_abs_slack_tendsto
      (fun coordinate step ↦ physicalStageSlack rates coordinate ((stageOrder D).symm k) step)
      fun coordinate ↦ physicalStageSlack_tendsto rates coordinate ((stageOrder D).symm k))
    (fun k step hstep state coordinate ↦ by
      have hbase := physicalStageKernel_expansion rates ((stageOrder D).symm k) coordinate step
        hstep state
      rw [physicalStageDrift_eq_mulVec] at hbase
      refine hbase.trans (mul_le_mul_of_nonneg_left ?_ hstep.le)
      exact (le_abs_self _).trans (Finset.single_le_sum
        (f := fun other ↦ |physicalStageSlack rates other ((stageOrder D).symm k) step|)
        (fun other _ ↦ abs_nonneg _) (Finset.mem_univ coordinate)))
    (enlargedLowOrderLDGenerator rates)
    (fun state coordinate ↦ sum_physicalGenerator_mulVec rates state coordinate)

end

end Descent.Portability.TwoLocusStageComposition
