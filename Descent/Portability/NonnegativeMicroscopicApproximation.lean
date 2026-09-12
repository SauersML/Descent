/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialStageComposition
import Descent.Portability.MultinomialMicroscopicApproximation
import Descent.Portability.NonnegativeCoalescenceRealization
import Descent.Portability.LowOrderLDWitnesses

assert_below Descent.Decision Descent.Program

/-!
# The microscopic step at nonnegative coalescence

NOTE1 section 2.2 allows coalescence rates `c_i ≥ 0`, and section 2.3 omits the sampling stage
in a deme with `c_i = 0`.  `NonnegativeCoalescenceRealization` reaches Theorem 2 at nonnegative
coalescence only through the limit of perturbed corpus epochs, with no microscopic kernel at
`c_i = 0`.  This module constructs that kernel and proves the epoch form of Theorem 2 through it
directly.

The kernel.  The physical stages are those of `TwoLocusStageComposition`.  Resampling in deme
`i` is `nonnegativeDriftKernel`: the multinomial stage of `MultinomialDriftStage` with
`⌈1/(c_i h)⌉` chromosomes when `c_i > 0`, and when `c_i = 0` the omitted stage, which does not
move the state.  Its branches are the census vectors and the one branch of the omitted stage,
placed side by side by `MultinomialMicroscopicApproximation.reindexKernel`.  Migration,
recombination and allele flips are the stages of `TwoLocusStageComposition` at `raisedRates`,
the corpus rate law with every coalescence rate raised by one.  Those stages read only the
migration, recombination and mutation rates, which `raisedRates` carries unchanged.
`nonnegativeComposite rates h` runs every stage at step `h` in the enumeration `stageOrder`, so
a deme with no coalescence contributes no resampling.

The generator.  `nonnegativeEnlargedGenerator rates` is the corpus enlarged generator of
`raisedRates rates` less that of unit coalescence alone,
`LowOrderLDWitnesses.ManyDemeLDRates.unitCoalescence`.  It intertwines with
`NonnegativeLDRates.generator` through the embedding
(`nonnegativeEnlargedGenerator_intertwines`), because the low-order generator is linear in the
rate coordinates (`NonnegativeCoalescenceRealization.generator_perturb`).  Each stage acts on
the features through its own matrix (`nonnegativePhysicalDrift_eq_mulVec`), the difference of
two corpus enlarged generators whose rate laws differ only in that stage's rate.  For resampling
in deme `i` the two laws are `raisedRates rates` and `loweredRates rates i`, in which `c_i + 1`
is lowered to one, so they differ by exactly `c_i`.  The summed stage matrices agree with
`nonnegativeEnlargedGenerator` on every feature vector (`sum_nonnegativeGenerator_mulVec`).

Theorem 2.  `nonnegativeMicroscopicApproximation rates` is the resulting
`MicroscopicApproximation`, assembled by
`MultinomialStageComposition.paddedComposedApproximation`.  At a positive step its kernel moves
the features exactly as the composed step does
(`nonnegativeMicroscopicKernel_apply_feature`).  NOTE1 Theorem 1,
`KernelRealizationPreservation.exp_mulVec_mem_realizationBody`, carries the enlarged body into
itself (`nonnegativeEnlargedPropagator_mulVec_mem_realizationBody`), and
`nonnegativeMicroscopicEpoch_preserves_locusExchangeable_realization` is one epoch of every
nonnegative rate law at every deme count, demes with no coalescence included.

Scope.  Rates are constant within the epoch.  The kernel is padded to a fixed branch type as in
`MultinomialStageComposition`, which keeps its action on the features and nothing else.  The
list induction over histories is not repeated here; `NonnegativeCoalescenceRealization` carries
it out from the same epoch statement, proved there through the limit.

## Empirical status

None.  The bodies here are algebra: finite averages of polynomial coordinates against
probability weights, differences of corpus generator matrices, and bounds between them, followed
by NOTE1 Theorem 1.  No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonnegativeMicroscopicApproximation

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.FiniteReproductiveKernel
open Descent.Portability.RealizationBody
open Descent.Portability.PulseJetExpansion
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel
open Descent.Portability.SimultaneousMigrationPulse
open Descent.Portability.StageCompositionKernel
open Descent.Portability.TwoLocusStageComposition
open Descent.Portability.MultinomialDriftStage
open Descent.Portability.MultinomialJetCertificate
open Descent.Portability.MultinomialStageComposition
open Descent.Portability.MultinomialMicroscopicApproximation
open Descent.Portability.RateGeneratorLipschitz
open Descent.Portability.NonnegativeCoalescenceRealization

noncomputable section

variable {D : ℕ}

/-! ## The generator at nonnegative coalescence -/

/-- The corpus rate law of a nonnegative rate law with every coalescence rate raised by one.  Its
migration, mutation and recombination rates are those of `rates`. -/
def raisedRates (rates : NonnegativeLDRates D) : ManyDemeLDRates D :=
  rates.perturb 1 one_pos

/-- **The enlarged generator at nonnegative coalescence.**  The corpus enlarged generator of the
raised rate law less that of unit coalescence alone. -/
def nonnegativeEnlargedGenerator (rates : NonnegativeLDRates D) :
    Matrix (AffineEnlargedCoordinate D) (AffineEnlargedCoordinate D) ℝ :=
  enlargedLowOrderLDGenerator (raisedRates rates) -
    enlargedLowOrderLDGenerator (LowOrderLDWitnesses.ManyDemeLDRates.unitCoalescence D)

/-- The low-order generator at nonnegative coalescence is the corpus generator of the raised
rate law less that of unit coalescence alone. -/
theorem generator_eq_sub (rates : NonnegativeLDRates D) :
    rates.generator = augmentedLowOrderLDGenerator (raisedRates rates) -
      augmentedLowOrderLDGenerator (LowOrderLDWitnesses.ManyDemeLDRates.unitCoalescence D) := by
  have hcoordinates :
      rateCoordinates (LowOrderLDWitnesses.ManyDemeLDRates.unitCoalescence D) =
        unitCoalescenceDirection D :=
    rfl
  rw [raisedRates, generator_perturb,
    augmentedLowOrderLDGenerator_eq_generatorLinearMap
      (LowOrderLDWitnesses.ManyDemeLDRates.unitCoalescence D),
    hcoordinates, one_smul, add_sub_cancel_right]

/-- **The enlarged generator at nonnegative coalescence intertwines with the low-order generator
through the embedding.** -/
theorem nonnegativeEnlargedGenerator_intertwines (rates : NonnegativeLDRates D) :
    enlargedEmbedding D * rates.generator =
      nonnegativeEnlargedGenerator rates * enlargedEmbedding D := by
  rw [generator_eq_sub, Matrix.mul_sub, nonnegativeEnlargedGenerator, Matrix.sub_mul,
    enlargedGenerator_intertwines, enlargedGenerator_intertwines]

/-- The enlarged propagator at nonnegative coalescence intertwines with the epoch propagator
through the embedding. -/
theorem nonnegativeEnlargedPropagator_mulVec_embed (rates : NonnegativeLDRates D) (duration : ℝ)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (matrixExponential (nonnegativeEnlargedGenerator rates) duration).mulVec
        (embedLowOrderLDState state) =
      embedLowOrderLDState ((matrixExponential rates.generator duration).mulVec state) := by
  have hmatrix := matrixExponential_intertwines (enlargedEmbedding D) rates.generator
    (nonnegativeEnlargedGenerator rates) (nonnegativeEnlargedGenerator_intertwines rates) duration
  rw [← enlargedEmbedding_mulVec, ← enlargedEmbedding_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hmatrix]

/-! ## Resampling at nonnegative coalescence -/

/-- The branch type of the resampling stage of deme `deme` at step `step`: the census vectors of
`multinomialChromosomeCount c_i step` chromosomes, beside the one branch of the omitted stage. -/
abbrev nonnegativeDriftBranch (rates : NonnegativeLDRates D) (deme : Fin D) (step : ℝ) : Type :=
  Counts TwoLocusHaplotype (multinomialChromosomeCount (rates.coalescence deme) step) ⊕ Unit

/-- **The resampling stage at nonnegative coalescence.**  In a deme with coalescence, the
multinomial stage with the note's chromosome count; in a deme with none, the omitted stage,
which does not move the state. -/
def nonnegativeDriftKernel (rates : NonnegativeLDRates D) (deme : Fin D) (step : ℝ)
    (hstep : 0 < step) :
    FiniteMixtureKernel (nonnegativeDriftBranch rates deme step) (DemeHaplotypeState D) :=
  if hrate : 0 < rates.coalescence deme then
    reindexKernel (multinomialDriftKernel deme (one_le_multinomialChromosomeCount
      (rates.coalescence deme) step hrate hstep)) Sum.inl Sum.inl_injective
  else
    reindexKernel (FiniteMixtureKernel.deterministic id) Sum.inr Sum.inr_injective

/-- The slack of the resampling stage of deme `deme` on one enlarged coordinate,
`c_i² h (107 M + B)`, which vanishes when the deme has no coalescence. -/
def nonnegativeDriftSlack (rates : NonnegativeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (deme : Fin D) (step : ℝ) : ℝ :=
  rates.coalescence deme ^ 2 * step *
    (107 * (JetPolynomialCertificate.enlarged coordinate).massBound +
      (enlargedStageExpansion coordinate).drift.bound)

/-- **The resampling stage at nonnegative coalescence expands to first order.**  It advances
every enlarged coordinate by `step · c_i · driftAt`, up to `step` times its slack; in a deme
with no coalescence both sides vanish. -/
theorem nonnegativeDriftKernel_expansion (rates : NonnegativeLDRates D) (deme : Fin D)
    (step : ℝ) (hstep : 0 < step) (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    |(nonnegativeDriftKernel rates deme step hstep).apply
          (fun y ↦ enlargedLowOrderLDFeature y coordinate) state -
        enlargedLowOrderLDFeature state coordinate -
        step * (rates.coalescence deme *
          (enlargedCoordinateJet coordinate).driftAt deme state)| ≤
      step * nonnegativeDriftSlack rates coordinate deme step := by
  rw [enlargedFeature_eq_jet_value coordinate, ← enlargedCoordinateJet_value coordinate state]
  by_cases hrate : 0 < rates.coalescence deme
  · rw [nonnegativeDriftKernel, dif_pos hrate, apply_reindexKernel]
    exact apply_multinomialDriftStage_enlarged coordinate deme (rates.coalescence deme) step
      hrate hstep state
  · have hzero : rates.coalescence deme = 0 :=
      le_antisymm (not_lt.mp hrate) (rates.coalescence_nonneg deme)
    rw [nonnegativeDriftKernel, dif_neg hrate, apply_reindexKernel,
      FiniteMixtureKernel.apply_deterministic, nonnegativeDriftSlack, hzero]
    simp

/-! ## The physical stages at nonnegative coalescence -/

/-- The branch type of each physical stage at nonnegative coalescence and step `step`. -/
def nonnegativePhysicalBranch (rates : NonnegativeLDRates D) (step : ℝ) :
    PhysicalStage D → Type
  | .drift deme => nonnegativeDriftBranch rates deme step
  | .migration => TwoLocusHaplotype
  | .recombination _ => TwoLocusHaplotype
  | .mutation _ => TwoLocusHaplotype

/-- Every physical stage branch type is finite. -/
instance nonnegativePhysicalBranchFintype (rates : NonnegativeLDRates D) (step : ℝ) :
    (stage : PhysicalStage D) → Fintype (nonnegativePhysicalBranch rates step stage)
  | .drift deme => inferInstanceAs (Fintype (nonnegativeDriftBranch rates deme step))
  | .migration => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .recombination _ => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .mutation _ => inferInstanceAs (Fintype TwoLocusHaplotype)

/-- The kernel of each physical stage at nonnegative coalescence and positive step `step`:
resampling through `nonnegativeDriftKernel`, and every other stage as in
`TwoLocusStageComposition` at the raised rate law, whose migration, recombination and mutation
rates are those of `rates`. -/
def nonnegativePhysicalKernel (rates : NonnegativeLDRates D) (step : ℝ) (hstep : 0 < step) :
    (stage : PhysicalStage D) →
      FiniteMixtureKernel (nonnegativePhysicalBranch rates step stage) (DemeHaplotypeState D)
  | .drift deme => nonnegativeDriftKernel rates deme step hstep
  | .migration => physicalStageKernel (raisedRates rates) .migration step
  | .recombination deme => physicalStageKernel (raisedRates rates) (.recombination deme) step
  | .mutation deme => physicalStageKernel (raisedRates rates) (.mutation deme) step

/-- The slack of each physical stage at nonnegative coalescence on one enlarged coordinate. -/
def nonnegativePhysicalSlack (rates : NonnegativeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) : PhysicalStage D → ℝ → ℝ
  | .drift deme => nonnegativeDriftSlack rates coordinate deme
  | .migration => physicalStageSlack (raisedRates rates) coordinate .migration
  | .recombination deme =>
      physicalStageSlack (raisedRates rates) coordinate (.recombination deme)
  | .mutation deme => physicalStageSlack (raisedRates rates) coordinate (.mutation deme)

/-- The rate-weighted first-order velocity of each physical stage at nonnegative coalescence on
one enlarged coordinate: `c_i` times the corpus drift for resampling in deme `i`. -/
def nonnegativePhysicalDrift (rates : NonnegativeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) : PhysicalStage D → DemeHaplotypeState D → ℝ
  | .drift deme => fun state ↦
      rates.coalescence deme * (enlargedCoordinateJet coordinate).driftAt deme state
  | .migration => physicalStageDrift (raisedRates rates) coordinate .migration
  | .recombination deme =>
      physicalStageDrift (raisedRates rates) coordinate (.recombination deme)
  | .mutation deme => physicalStageDrift (raisedRates rates) coordinate (.mutation deme)

/-- **Every physical stage at nonnegative coalescence expands to first order.** -/
theorem nonnegativePhysicalKernel_expansion (rates : NonnegativeLDRates D) (step : ℝ)
    (hstep : 0 < step) (stage : PhysicalStage D) (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    |(nonnegativePhysicalKernel rates step hstep stage).apply
          (fun y ↦ enlargedLowOrderLDFeature y coordinate) state -
        enlargedLowOrderLDFeature state coordinate -
        step * nonnegativePhysicalDrift rates coordinate stage state| ≤
      step * nonnegativePhysicalSlack rates coordinate stage step := by
  cases stage with
  | drift deme => exact nonnegativeDriftKernel_expansion rates deme step hstep coordinate state
  | migration =>
      exact physicalStageKernel_expansion (raisedRates rates) .migration coordinate step hstep
        state
  | recombination deme =>
      exact physicalStageKernel_expansion (raisedRates rates) (.recombination deme) coordinate
        step hstep state
  | mutation deme =>
      exact physicalStageKernel_expansion (raisedRates rates) (.mutation deme) coordinate step
        hstep state

/-- Every physical stage slack at nonnegative coalescence vanishes with the step size. -/
theorem nonnegativePhysicalSlack_tendsto (rates : NonnegativeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (stage : PhysicalStage D) :
    Filter.Tendsto (nonnegativePhysicalSlack rates coordinate stage) (nhds 0) (nhds 0) := by
  cases stage with
  | drift deme =>
      have hcontinuous : Continuous fun step : ℝ ↦ rates.coalescence deme ^ 2 * step *
          (107 * (JetPolynomialCertificate.enlarged coordinate).massBound +
            (enlargedStageExpansion coordinate).drift.bound) := by
        fun_prop
      exact hcontinuous.tendsto' 0 0 (by simp)
  | migration => exact physicalStageSlack_tendsto (raisedRates rates) coordinate .migration
  | recombination deme =>
      exact physicalStageSlack_tendsto (raisedRates rates) coordinate (.recombination deme)
  | mutation deme =>
      exact physicalStageSlack_tendsto (raisedRates rates) coordinate (.mutation deme)

/-! ## The stage matrices -/

/-- The raised rate law with the coalescence rate of deme `deme` lowered from `c_i + 1` to one. -/
def loweredRates (rates : NonnegativeLDRates D) (deme : Fin D) : ManyDemeLDRates D :=
  { raisedRates rates with
    coalescence := fun other ↦ if other = deme then 1 else rates.coalescence other + 1
    coalescence_pos := fun other ↦ by
      split_ifs
      · exact one_pos
      · linarith [rates.coalescence_nonneg other] }

/-- The matrix of each physical stage at nonnegative coalescence: for resampling in deme `i`, the
corpus enlarged generator of the raised rate law less that of `loweredRates rates i`; for every
other stage, the matrix of `TwoLocusStageComposition` at the raised rate law. -/
def nonnegativeGenerator (rates : NonnegativeLDRates D) :
    PhysicalStage D → Matrix (AffineEnlargedCoordinate D) (AffineEnlargedCoordinate D) ℝ
  | .drift deme =>
      enlargedLowOrderLDGenerator (raisedRates rates) -
        enlargedLowOrderLDGenerator (loweredRates rates deme)
  | .migration => physicalGenerator (raisedRates rates) .migration
  | .recombination deme => physicalGenerator (raisedRates rates) (.recombination deme)
  | .mutation deme => physicalGenerator (raisedRates rates) (.mutation deme)

/-- **Each physical stage at nonnegative coalescence acts on the features through its own
matrix.** -/
theorem nonnegativePhysicalDrift_eq_mulVec (rates : NonnegativeLDRates D)
    (stage : PhysicalStage D) (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    nonnegativePhysicalDrift rates coordinate stage state =
      (nonnegativeGenerator rates stage).mulVec (enlargedLowOrderLDFeature state) coordinate := by
  cases stage with
  | drift deme =>
      have hdifference : ∀ other : Stage D,
          stageRate (raisedRates rates) other - stageRate (loweredRates rates deme) other =
            if other = .drift deme then rates.coalescence deme else 0 := by
        intro other
        cases other with
        | drift otherDeme =>
            show (rates.coalescence otherDeme + 1) -
                (if otherDeme = deme then 1 else rates.coalescence otherDeme + 1) =
              if Stage.drift otherDeme = Stage.drift deme then rates.coalescence deme else 0
            by_cases hdeme : otherDeme = deme
            · rw [if_pos hdeme, if_pos (by rw [hdeme]), hdeme]
              ring
            · rw [if_neg hdeme, if_neg fun hequal ↦ hdeme (Stage.drift.inj hequal)]
              ring
        | _ =>
            rw [if_neg (by simp)]
            exact sub_self _
      rw [nonnegativeGenerator, generatorDifference_mulVec]
      simp only [hdifference, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  | migration =>
      exact physicalStageDrift_eq_mulVec (raisedRates rates) .migration coordinate state
  | recombination deme =>
      exact physicalStageDrift_eq_mulVec (raisedRates rates) (.recombination deme) coordinate
        state
  | mutation deme =>
      exact physicalStageDrift_eq_mulVec (raisedRates rates) (.mutation deme) coordinate state

/-- The total absolute mass of the stage matrices at nonnegative coalescence, a uniform bound on
their absolute row sums. -/
def nonnegativeRowBound (rates : NonnegativeLDRates D) : ℝ :=
  ∑ stage : PhysicalStage D, ∑ row : AffineEnlargedCoordinate D,
    ∑ column : AffineEnlargedCoordinate D, |nonnegativeGenerator rates stage row column|

/-- **The summed stage matrices agree with the enlarged generator at nonnegative coalescence on
every feature vector.** -/
theorem sum_nonnegativeGenerator_mulVec (rates : NonnegativeLDRates D)
    (state : DemeHaplotypeState D) (coordinate : AffineEnlargedCoordinate D) :
    (∑ k, nonnegativeGenerator rates ((stageOrder D).symm k)).mulVec
        (enlargedLowOrderLDFeature state) coordinate =
      (nonnegativeEnlargedGenerator rates).mulVec (enlargedLowOrderLDFeature state)
        coordinate := by
  have hsplit : (∑ k, nonnegativeGenerator rates ((stageOrder D).symm k)).mulVec
      (enlargedLowOrderLDFeature state) coordinate =
      ∑ k, (nonnegativeGenerator rates ((stageOrder D).symm k)).mulVec
        (enlargedLowOrderLDFeature state) coordinate := by
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hsplit, nonnegativeEnlargedGenerator, generatorDifference_mulVec]
  simp only [← nonnegativePhysicalDrift_eq_mulVec]
  rw [Equiv.sum_comp (stageOrder D).symm
      (fun stage ↦ nonnegativePhysicalDrift rates coordinate stage state),
    sum_physicalStage, sum_stage]
  simp only [nonnegativePhysicalDrift, physicalStageDrift, simultaneousMigrationExpansion_velocity,
    bothMutationExpansion_velocity, stageDrift, stageRate, stageVelocity, raisedRates,
    NonnegativeLDRates.perturb, LowOrderLDWitnesses.ManyDemeLDRates.unitCoalescence, sub_zero,
    zero_div, add_sub_cancel_right, mul_add, Finset.sum_add_distrib]
  ring

/-! ## The approximation and NOTE1 Theorem 2 -/

/-- The slack of one physical stage at nonnegative coalescence over all enlarged coordinates. -/
def nonnegativeCompositionStageSlack (rates : NonnegativeLDRates D) (stage : PhysicalStage D)
    (step : ℝ) : ℝ :=
  ∑ coordinate : AffineEnlargedCoordinate D,
    |nonnegativePhysicalSlack rates coordinate stage step|

/-- Each physical stage at nonnegative coalescence advances every enlarged coordinate by its own
matrix applied to the features, up to its slack over all coordinates. -/
theorem nonnegativePhysicalKernel_mulVec_expansion (rates : NonnegativeLDRates D) (step : ℝ)
    (hstep : 0 < step) (stage : PhysicalStage D) (state : DemeHaplotypeState D)
    (coordinate : AffineEnlargedCoordinate D) :
    |(nonnegativePhysicalKernel rates step hstep stage).apply
          (fun y ↦ enlargedLowOrderLDFeature y coordinate) state -
        enlargedLowOrderLDFeature state coordinate -
        step * (nonnegativeGenerator rates stage).mulVec (enlargedLowOrderLDFeature state)
          coordinate| ≤
      step * nonnegativeCompositionStageSlack rates stage step := by
  have hbase := nonnegativePhysicalKernel_expansion rates step hstep stage coordinate state
  rw [nonnegativePhysicalDrift_eq_mulVec] at hbase
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ hstep.le)
  exact (le_abs_self _).trans (Finset.single_le_sum
    (f := fun other ↦ |nonnegativePhysicalSlack rates other stage step|)
    (fun other _ ↦ abs_nonneg _) (Finset.mem_univ coordinate))

/-- **The composed step at nonnegative coalescence.**  At a positive step `step`, every physical
stage of NOTE1 section 2.3 at its own rate, with resampling omitted in every deme with no
coalescence, run in the fixed enumeration `stageOrder`. -/
def nonnegativeComposite (rates : NonnegativeLDRates D) (step : ℝ) (hstep : 0 < step) :
    FiniteMixtureKernel ((k : Fin (Fintype.card (PhysicalStage D))) →
      nonnegativePhysicalBranch rates step ((stageOrder D).symm k)) (DemeHaplotypeState D) :=
  composeDependentStages (Fintype.card (PhysicalStage D))
    (fun k ↦ nonnegativePhysicalBranch rates step ((stageOrder D).symm k))
    fun k ↦ nonnegativePhysicalKernel rates step hstep ((stageOrder D).symm k)

/-- **NOTE1 equation (11) at nonnegative coalescence, with nothing assumed.**  The composed step
with resampling omitted where there is no coalescence advances every enlarged coordinate by
`h · nonnegativeEnlargedGenerator rates` applied to the feature vector, uniformly in the state,
with an explicit error that vanishes with `h`.  The kernel is that step padded to a fixed number
of atoms. -/
def nonnegativeMicroscopicApproximation (rates : NonnegativeLDRates D) :
    MicroscopicApproximation (B := Fin (Fintype.card (AffineEnlargedCoordinate D)))
      (enlargedLowOrderLDFeature (D := D)) (nonnegativeEnlargedGenerator rates) :=
  paddedComposedApproximation (enlargedLowOrderLDFeature (D := D)) none (fun _ ↦ rfl)
    (compositionFeatureBound D) (compositionFeatureBound_nonneg D) abs_enlargedFeature_le
    (Fintype.card (PhysicalStage D))
    (fun step k ↦ nonnegativePhysicalBranch rates step ((stageOrder D).symm k))
    (fun step hstep k ↦ nonnegativePhysicalKernel rates step hstep ((stageOrder D).symm k))
    (fun k ↦ nonnegativeGenerator rates ((stageOrder D).symm k)) (nonnegativeRowBound rates)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (fun k row ↦ stageRow_le_totalMass (nonnegativeGenerator rates) ((stageOrder D).symm k) row)
    (fun k step ↦ nonnegativeCompositionStageSlack rates ((stageOrder D).symm k) step)
    (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (fun k ↦ sum_abs_slack_tendsto
      (fun coordinate step ↦
        nonnegativePhysicalSlack rates coordinate ((stageOrder D).symm k) step)
      fun coordinate ↦ nonnegativePhysicalSlack_tendsto rates coordinate ((stageOrder D).symm k))
    (fun step hstep k point other ↦ nonnegativePhysicalKernel_mulVec_expansion rates step hstep
      ((stageOrder D).symm k) point other)
    (nonnegativeEnlargedGenerator rates)
    (fun state coordinate ↦ sum_nonnegativeGenerator_mulVec rates state coordinate)

/-- **The approximation's kernel moves the features exactly as the composed step.** -/
theorem nonnegativeMicroscopicKernel_apply_feature (rates : NonnegativeLDRates D) {step : ℝ}
    (hstep : 0 < step) (state : DemeHaplotypeState D) (coordinate : AffineEnlargedCoordinate D) :
    ((nonnegativeMicroscopicApproximation rates).kernel step).apply
        (fun y ↦ enlargedLowOrderLDFeature y coordinate) state =
      (nonnegativeComposite rates step hstep).apply
        (fun y ↦ enlargedLowOrderLDFeature y coordinate) state :=
  paddedComposedKernel_apply_feature (enlargedLowOrderLDFeature (D := D)) none (fun _ ↦ rfl)
    (Fintype.card (PhysicalStage D))
    (fun step k ↦ nonnegativePhysicalBranch rates step ((stageOrder D).symm k))
    (fun step hstep k ↦ nonnegativePhysicalKernel rates step hstep ((stageOrder D).symm k))
    hstep state coordinate

/-- **NOTE1 Theorem 1 at nonnegative coalescence.**  The enlarged propagator of every nonnegative
rate law carries the enlarged realization body into itself, through the microscopic
approximation. -/
theorem nonnegativeEnlargedPropagator_mulVec_mem_realizationBody (rates : NonnegativeLDRates D)
    (duration : ℝ) (hduration : 0 ≤ duration) (vector : AffineEnlargedCoordinate D → ℝ)
    (hvector : vector ∈ realizationBody (enlargedLowOrderLDFeature (D := D))) :
    (matrixExponential (nonnegativeEnlargedGenerator rates) duration).mulVec vector ∈
      realizationBody (enlargedLowOrderLDFeature (D := D)) :=
  KernelRealizationPreservation.exp_mulVec_mem_realizationBody _ _
    (nonnegativeMicroscopicApproximation rates)
    (EnlargedBodyClosedness.isClosed_enlargedRealizationBody D) duration hduration vector hvector

/-- **NOTE1 Theorem 2 for one epoch at nonnegative coalescence, through the microscopic
kernel.**  For every nonnegative rate law, including one in which some deme has no coalescence,
every deme count and every nonnegative duration, the epoch propagator maps a
locus-exchangeably realizable stored state to a locus-exchangeably realizable one. -/
theorem nonnegativeMicroscopicEpoch_preserves_locusExchangeable_realization
    (rates : NonnegativeLDRates D) (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) := by
  apply TwoLocusRealizabilityPreservation.nonempty_locusExchangeableRealization_of_embed_mem
  change embedLowOrderLDState ((matrixExponential rates.generator duration).mulVec state) ∈ _
  rw [← nonnegativeEnlargedPropagator_mulVec_embed]
  exact nonnegativeEnlargedPropagator_mulVec_mem_realizationBody rates duration hduration _
    (EnlargedBodyClosedness.embed_mem_enlargedRealizationBody_of_realization realization)

end

end Descent.Portability.NonnegativeMicroscopicApproximation
