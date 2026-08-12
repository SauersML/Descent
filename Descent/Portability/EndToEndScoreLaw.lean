/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoDemeLDClosedForm
import Descent.Coalescent.TwoLocusHistory
import Descent.Core.Identifiability
import Descent.PopGen.GeneticArchitectureDiscovery
import Descent.PopGen.Shrinkage
import Descent.Portability.AncestryCalibration
import Descent.Portability.PGSCalibrationTheory.CalibrationDefinitions
import Descent.Portability.PGSCalibrationTheory.PopulationCalibrationDrift
import Descent.Portability.PhenomeWidePortability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# End-to-end selected-score and calibration law

The concrete declarations in this file form the score-construction layer between a demographic
moment law and the metric charts.  Clumping cutoff, physical window, threshold family, and
discovery sample size come from the visible study design.  Marker count, marker positions,
joint GWAS output, and the selected panel instead live inside `RealizedPTGWASDraw`, so mutation
may change them between realizations.  `VariableMarkerPTGWASKernel` is the exact interface an
upstream demographic/ARG construction must inhabit.  Its selected output is a score mean and a
`Core.ScoreMoments` tuple in each deme.  Those moments feed population Gaussian charts; exact
finite-cohort AUC, Brier, observed-risk `R²`, logistic calibration slope, and CITL are evaluated
separately in `DiscriminationLaw` from realized outcomes and predicted risks.

The requested endpoint contract recorded next is broader: it also names cohort layout and the
intermediate coordinates the current concrete construction does not yet reach.  Keeping the
contract and the attained construction in one file makes that gap visible; it does not erase
it with a global retention scalar.

The metric codomain is real only on its named domain.  Finite simulations can produce
undefined metrics (for example, a singleton cohort can contain neither a case-control pair nor
nonzero outcome variance; `BinaryRiskCohort.noAUCDomain_singleton` and
`noR2Domain_singleton` prove the corresponding facts in `DiscriminationLaw`).  Consequently
an unrestricted all-positive-cohort endpoint must ultimately return a partial value or a
definedness probability in addition to a conditional expectation.  The real-valued vocabulary
below records the requested coordinate names; it is not a convention that fills an undefined
metric with zero.
-/

/-! ## The requested endpoint contract

This vocabulary states the proposed endpoint without claiming that the corpus already
constructs it.  The distinction between `VisiblePipelineInput` and a completion must be made
*after* simulator randomness determined by the visible input has been integrated out.  In
particular, if gnomon draws causal positions, effects, and haplotypes from conditional laws
fixed by the visible input, those draws belong inside the expectation; they are not residual
fiber coordinates and cannot be used to manufacture a non-identifiability witness.

`DiscriminationLaw` derives the finite liability prevalence root, the bounded CITL root, the
complete finite Bernoulli outcome sum, and now existence and uniqueness of the exact
ridge-logistic calibration fit directly from the executable case/control guards: continuity
and an explicit bounded-sublevel theorem give existence, while strict convexity gives
uniqueness.  Thus no optimizer proof is hidden in the metric domain.

No `Core.SharpFiberEnvelope` for the real pipeline is declared here.  Such a declaration must
supply derived, attained endpoints for the actual expected semantics.  Four links currently
prevent that construction:

* `PipelineDemographicHistory.twoLocusMoments` now maps an arbitrary finite event history to
  the complete transient many-deme `H/DD/Dz/pi2` operator product.  This supplies a concrete
  candidate for the linkage factor that was previously bracketed.  The tracked exact-rational
  ancestral-configuration reference in `validation/empirical/momentsld/ldchain_reduction.py`
  solves 2-, 3-, and 4-deme chains with verified lumpability and zero full-system residual.  It
  shows that an `F_ST`-matched two-deme surrogate is biased high and that a geometric scalar
  composition is only approximate.  This supports the full-state operator form, but no Lean
  specialization theorem yet identifies its generator/readout with that reference.  The
  preregistered 2-D comparison has now completed 4x4, 5x5, and an additional 6x6 check with
  relative linear-solve residuals below `1e-12`.  Its mechanical verdict rejects the proposed
  Bessel law with the one-dimensional decay length at `rho = 1` and fails it on both shape and
  length at `rho = 5, 20` (the 4x4/5x5 length differences stay below the filed inconclusive
  threshold).  Thus another scalar composition has been ruled out, not fitted into this file.
  The complete ordered operator product remains the derived candidate law, but still lacks the
  specialization proof and independent simulator gate needed for a discharged endpoint;
* the concrete one-locus propagator below is a symmetric-biallelic diffusion component.
  Gnomon's real-P+T study generates an ancestral recombination graph with `msprime`, lays its
  mutation model on that graph, reservoir-selects multi-marker genotype columns, computes
  PCs, and then runs logistic/Firth GWAS plus PLINK clumping and held-out threshold selection.
  Identifying that full joint kernel is strictly stronger than identifying `F_ST` and the
  low-order `DD` coordinate.  The latter collapses the linkage bracket but does not by itself
  construct the deployed score law.  The low-order operator now includes the exact recurrent
  symmetric-biallelic damping and its recurrent one-deme stationary boundary, so it uses the
  same mutation mechanism as the marginal ascertainment propagator.
  `PipelineDemographicHistory.commonDiffusionProjection_exact` now proves that the joint
  operator's exposed `H` coordinate equals the marginal divergence moment after every
  arbitrary compiled history: it includes the ancestral boundary, generator and exponential
  intertwinings, split commutation, reachable-state invariants, paired event induction, and
  terminal readouts.  No fitted biological factor remains in that join.  A realizability
  corollary must still show that the propagated `DD` kernel stays positive
  semidefinite, thereby constructing `LDPairDomain` (and its Cauchy--Schwarz field) whenever
  within-deme `DD` is nonzero.  The input-only linkage function returns `none` rather than
  accepting that proof from its caller, so this formal obligation cannot be hidden;
  moreover, the executable currently calls `msprime.sim_mutations` without a mutation model.
  Current msprime therefore supplies its default discrete-genome recurrent four-state JC69
  process, while `stream_geno.py` immediately adds pairs of genotype-state integers and treats
  their mean divided by two as a biallelic allele frequency.  No msprime version is pinned in
  the executable environment.  An exact shared kernel must first make that protocol explicit
  (or the executable must explicitly choose a binary/infinite-sites model); silently replacing
  the default by this file's biallelic law would predict a different program;
* the cohort-evaluation time-shift candidate is contradicted by its pre-filed check: at the
  `30 ↔ 50` comparison it predicts a gap of `0.0016` against a measured `0.0148`.  The exact
  replacement is now the sample-size-specific Bernstein conditional event
  `Coalescent.targetErosionEvent`, composed directly from a visible history by
  `PipelineDemographicHistory.targetErosion`.  It includes the missing mechanism—
  the sampled polymorphic/monomorphic events themselves change with `n`.  The same joint law
  now yields every identifiable source-polymorphism-conditioned target factorial moment and
  exact conditional heterozygosity, proving that boundary fixation alone is insufficient.
  The distinct pooled-MAF event is now also constructed without pairwise reduction:
  `manyDemeSampleCountMomentMass` expands the complete count-cell likelihood and adds arbitrary
  latent probe exponents before conditioning, while `pooledCommonVariantHeterozygosityProduct`
  and its normalized `CV²`/cross-deme excess coordinates expose the required fourth-order
  finite-panel inputs.  `pooledMAFTerminalProbe` now combines those count cells into one
  terminal Bernstein vector, and `pooledMAFProbeMass_samplingDual` proves that its backward
  propagation through every transposed epoch and sparse split equals the direct Cartesian
  law.  The exact operator specialization is therefore formalized.
  `Coalescent.certifiedManyDemeMomentHistory_pairing_error_le` accumulates rigorous convergent
  Taylor-tail certificates over the whole backward history, and
  `pooledMAFProbeMassCertified_error_le` specializes the result to a finite scalar prediction
  and certified absolute-error radius.  The positive representation has now been derived at
  generator level rather than guessed: `manyDemeBernsteinAnalyticGenerator_eq_killedDual`
  proves for every finite deme count and migration matrix that the diffusion generator on a
  product Bernstein weight is exactly a structured coalescent with positive like-type
  coalescence, lineage migration and symmetric-mutation label flips, plus explicit
  opposite-type killing.  `manyDemeKilledDualGenerator_eq_jump_sub_killing` isolates that
  nonnegative absorption rate, and `manyDemeKilledDualDynamicsMatrix` encodes its finite
  zero-extended restriction.  `ManyDemeKilledDualCoordinate.allTransitions_closed` proves
  that every active coalescence, migration, or label-flip destination from a degree-bounded
  row remains in that finite carrier; killing has no destination.  The distinct-parent split
  merge is closed as well, `splitManyDemeKilledDualPropagator_mulVec` proves its sparse matrix
  is the deterministic lineage merge, and `manyDemeKilledDualHistoryPropagator` composes any
  finite epoch/split sequence.  What remains is the generator-to-semigroup and split
  intertwining with the existing moment law needed to replace that alternating evaluator end to end,
  implement its sparse action without materializing either Cartesian carrier, add certified
  floating-point/interval roundoff control, and run at the executable's 13,750-individual /
  27,500-haplotype grid2d scale, followed by the filed end-to-end cohort validation gate;
* the executable protocol is not yet a function of exactly this visible input type.
  `gnomon/sims/ancestry_calibration/gen_real_pt.py` accepts only its hard-coded `serial1d` and
  `grid2d` constructors rather than an arbitrary event history, hard-codes 250 evaluation
  individuals and 5000 individuals in the chosen training deme, and randomly chooses that
  training deme even though `PipelineStudyDesign.gwasDeme` is a visible constant.  It also
  exposes genome chunk count and chunk length as run-time arguments, varies the resulting
  sequence length and marker reservoir, fixes unit genetic variance and `SIGMA_E = 1` (hence
  liability heritability one half) rather than consuming the advertised arbitrary
  heritability, and emits several phenotype rungs.  `fit_binary.py` then evaluates five
  distinct recalibration methods
  (`linpc`, `znorm`, `calpred`, `rawpgs`, and `gamfit`) while the visible input and
  `PipelineQuantity` index none of them; it also declares discrimination global-only rather
  than reporting the requested within-deme AUCs.  Thus the requested report is not literally
  the executable's current output schema even before its values are derived.
  Either one canonical executable protocol must be fixed and proved to match this contract, or
  those genuine degrees of freedom must become visible coordinates.  Leaving them implicit
  would create a real pipeline fiber, unlike the removed Boolean toy.  The finite composition
  now makes the phenotype rule explicit through `PhenotypeBaseline`; the downstream kernel
  selects one `PhenotypeRung`, and `phenotypeBaselineForRung` implements the executable's four
  individual-level rules rather than accepting an arbitrary baseline.  Moreover,
  `FiniteLiabilityPanel.risk_eq_iff_liability_eq_up_to_common_shift` proves its exact quotient:
  only one common baseline offset is absorbed by the prevalence intercept; every nonconstant
  per-deme baseline change alters at least one true risk.  Selecting among the executable
  phenotype rungs is therefore semantically material, while the selection itself remains a
  missing protocol coordinate.  Finally, the executable sets its realized causal count to
  `min(requested, eligible_pool_size)`, whereas `VariableMarkerPTGWASKernel` now preserves the
  advertised count and returns `none` when a draw cannot realize it.  One of those failure
  semantics must be chosen explicitly before the two programs denote the same experiment.

The definitions below therefore specify the target and route it to the generic core
identification theory.  They do not instantiate the real semantic map, assert a positive
fiber width, or claim an exact endpoint law.

## Where the pieces live

* `Descent/Core/Identifiability.lean` contains only the generic exact-readout and sharp-fiber
  theorems.  It contains no biological counterexample or pipeline verdict.
* `Descent/Coalescent/StructuredPresentDay.lean` contains the finite one-locus moment and
  Bernstein sample-count machinery, including the cohort-size-specific ascertainment event,
  the shared pair-divergence derivative, and the exact matrix-exponential intertwining law.
* `Descent/Coalescent/TwoLocusHistory.lean` contains the arbitrary-deme recurrent
  `H/DD/Dz/pi2` generator, split transforms, epoch semigroups, and ordered composition that
  evaluates the proposed migration-restored linkage factor.
* This file defines the visible history/study contract, compiles both demographic operators,
  proves `commonDiffusionProjection_exact` for arbitrary event histories, specifies the exact
  P+T selection objective on a realized variable-marker draw, and builds the
  total-liability/phenotype layer.
* `Descent/Portability/DiscriminationLaw.lean` evaluates realized and expected finite-cohort
  `R²`, AUC, calibration, Brier, and score variance, preserving undefined coordinates as
  `Option` values.
* `Descent/Portability/PhenomeWidePortability.lean` retains the historical migration-chain
  bracket and now inserts the operator point into it, with exact identities showing that its
  two gaps differ only by the linkage factor.
* `validation/empirical/momentsld/ldchain_reduction.py` and
  `validation/empirical/momentsld/derivation/ld2d_iter.log` are the independent exact-chain
  and preregistered 2-D evidence.  They refute scalar reductions; they are not a simulator
  validation of the Lean operator.
-/

/-- One elapsed epoch followed by a change in an arbitrary finite-deme demographic history. -/
inductive DemographicEvent (demeCount : ℕ) where
  | split (elapsed : ℝ) (elapsed_nonneg : 0 ≤ elapsed)
      (parent child : Fin demeCount) (parent_ne_child : parent ≠ child)
  | sizeChange (elapsed : ℝ) (elapsed_nonneg : 0 ≤ elapsed)
      (effectiveSize : Fin demeCount → ℝ)
      (effectiveSize_pos : ∀ deme, 0 < effectiveSize deme)
  /-- Backward-lineage convention: `migration source parent` is the raw per-generation
  probability/rate that a lineage currently in `source` chooses its parent in `parent`. -/
  | migrationChange (elapsed : ℝ) (elapsed_nonneg : 0 ≤ elapsed)
      (migration : Fin demeCount → Fin demeCount → ℝ)
      (migration_nonneg : ∀ source target, 0 ≤ migration source target)
      (migration_self : ∀ deme, migration deme deme = 0)
  | mutationRateChange (elapsed : ℝ) (elapsed_nonneg : 0 ≤ elapsed) (mutationRate : ℝ)
      (mutationRate_nonneg : 0 ≤ mutationRate)
  | recombinationRateChange (elapsed : ℝ) (elapsed_nonneg : 0 ≤ elapsed)
      (recombinationRate : ℝ)
      (recombinationRate_nonneg : 0 ≤ recombinationRate)

/-- Real time evolved under the preceding rates before one event is applied. -/
def DemographicEvent.elapsed {demeCount : ℕ} : DemographicEvent demeCount → ℝ
  | .split elapsed _ _ _ _ => elapsed
  | .sizeChange elapsed _ _ _ => elapsed
  | .migrationChange elapsed _ _ _ _ => elapsed
  | .mutationRateChange elapsed _ _ _ => elapsed
  | .recombinationRateChange elapsed _ _ _ => elapsed

/-- Every declared event interval lies in the forward-time domain. -/
theorem DemographicEvent.elapsed_nonneg {demeCount : ℕ}
    (event : DemographicEvent demeCount) : 0 ≤ event.elapsed := by
  cases event <;> assumption

/-- A deme label is initially inactive exactly when it occurs as a split child later in the
history. -/
def initialDemeActive {demeCount : ℕ} (events : List (DemographicEvent demeCount))
    (deme : Fin demeCount) : Bool :=
  !(events.any fun event ↦ match event with
    | .split _ _ _ child _ => decide (child = deme)
    | _ => false)

/-- A split activates its child; all other events leave the active set unchanged. -/
def DemographicEvent.updateActive {demeCount : ℕ} (event : DemographicEvent demeCount)
    (active : Fin demeCount → Bool) : Fin demeCount → Bool :=
  match event with
  | .split _ _ _ child _ => fun deme ↦ if deme = child then true else active deme
  | _ => active

/-- Split chronology is valid when every parent is already active and every child is activated
exactly once.  This rules out ghost migration through future deme labels. -/
def demographicEventsWellFormed {demeCount : ℕ} :
    List (DemographicEvent demeCount) → (Fin demeCount → Bool) → Prop
  | [], _ => True
  | event :: remaining, active =>
      match event with
      | .split _ _ parent child _ =>
          active parent = true ∧ active child = false ∧
            demographicEventsWellFormed remaining (event.updateActive active)
      | _ => demographicEventsWellFormed remaining active

/-- The visible demographic argument.  Time runs forward from a common ancestral state.
Each event carries the nonnegative real epoch elapsed under the preceding rates; `finalElapsed`
is the terminal epoch after the last event.  Domain facts live in the type so an exact
propagator never assigns a meaning to negative times, sizes, or rates. -/
structure PipelineDemographicHistory (demeCount : ℕ) where
  ancestralDeme : Fin demeCount
  initialEffectiveSize : Fin demeCount → ℝ
  initialEffectiveSize_pos : ∀ deme, 0 < initialEffectiveSize deme
  /-- Backward-lineage migration matrix in raw generations. -/
  initialMigration : Fin demeCount → Fin demeCount → ℝ
  initialMigration_nonneg : ∀ source target, 0 ≤ initialMigration source target
  initialMigration_self : ∀ deme, initialMigration deme deme = 0
  initialMutationRate : ℝ
  initialMutationRate_nonneg : 0 ≤ initialMutationRate
  initialRecombinationRate : ℝ
  initialRecombinationRate_nonneg : 0 ≤ initialRecombinationRate
  events : List (DemographicEvent demeCount)
  ancestralDeme_active : initialDemeActive events ancestralDeme = true
  events_wellFormed : demographicEventsWellFormed events (initialDemeActive events)
  finalElapsed : ℝ
  finalElapsed_nonneg : 0 ≤ finalElapsed

/-- Raw moments of the symmetric-beta stationary frequency law.  For positive shape this is
`Beta(shape, shape)`; at zero mutation the recursion selects the ancestral-allele boundary
mass at frequency zero. -/
noncomputable def symmetricBetaMoment (shape : ℝ) : ℕ → ℝ
  | 0 => 1
  | degree + 1 =>
      symmetricBetaMoment shape degree *
        (shape + degree) / (2 * shape + degree)

/-- The heterozygosity of the symmetric-beta boundary is exactly the recurrent-biallelic
one-deme `H` boundary used by the two-locus operator.  This is a first-principles bridge
between the marginal ascertainment and linkage systems, including the zero-mutation edge. -/
theorem symmetricBetaHeterozygosity_eq_recurrentLowOrderH
    (effectiveSize mutationRate : ℝ) (effectiveSize_pos : 0 < effectiveSize)
    (mutationRate_nonneg : 0 ≤ mutationRate) :
    2 * (symmetricBetaMoment (4 * effectiveSize * mutationRate) 1 -
      symmetricBetaMoment (4 * effectiveSize * mutationRate) 2) =
      (2 * mutationRate) /
        (1 / (2 * effectiveSize) + 2 * (2 * mutationRate)) := by
  rcases eq_or_lt_of_le mutationRate_nonneg with hzero | hpos
  · subst mutationRate
    norm_num [symmetricBetaMoment]
  · have hshape : 0 < 4 * effectiveSize * mutationRate := by positivity
    have hsize : effectiveSize ≠ 0 := ne_of_gt effectiveSize_pos
    have hshape_ne : 4 * effectiveSize * mutationRate ≠ 0 := ne_of_gt hshape
    have htwoshape : 2 * (4 * effectiveSize * mutationRate) ≠ 0 := by positivity
    have hnext : 2 * (4 * effectiveSize * mutationRate) + 1 ≠ 0 := by positivity
    have hscale : 1 / (2 * effectiveSize) + 2 * (2 * mutationRate) ≠ 0 := by
      positivity
    norm_num [symmetricBetaMoment]
    field_simp [hsize, hshape_ne, htwoshape, hnext, hscale]
    ring

/-- The stationary symmetric-beta shape derived from raw diploid population size and the
per-generation bidirectional mutation rate: `2 u / (1 / (2 Nₑ)) = 4 Nₑ u`.

Empirical status: DERIVED -- the standard scaled mutation parameter read off the history's
own root size and rate; nothing is fitted.  Whether the ancestral population sat at the
symmetric-beta stationary law is the boundary assumption named at `ancestralLDRates`. -/
noncomputable def PipelineDemographicHistory.ancestralMutationShape
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) : ℝ :=
  4 * history.initialEffectiveSize history.ancestralDeme * history.initialMutationRate

/-- The ancestral one-locus moments are derived from the history's own root size and mutation
rate; they are not an additional caller-supplied completion.

Empirical status: DERIVED -- symmetric-beta moments by the exact recurrence, with
`ancestralMoment_zero` and `ancestralMoment_succ` proved beside the definition; no moment
table is supplied from outside and no measurement bears on the recurrence itself. -/
noncomputable def PipelineDemographicHistory.ancestralMoment
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (degree : ℕ) : ℝ :=
  symmetricBetaMoment history.ancestralMutationShape degree

/-- The derived ancestral law is normalized. -/
theorem PipelineDemographicHistory.ancestralMoment_zero
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) :
    history.ancestralMoment 0 = 1 := rfl

/-- Successive ancestral moments obey the exact beta recurrence. -/
theorem PipelineDemographicHistory.ancestralMoment_succ
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (degree : ℕ) :
    history.ancestralMoment (degree + 1) =
      history.ancestralMoment degree *
        (history.ancestralMutationShape + degree) /
          (2 * history.ancestralMutationShape + degree) := rfl

/-- The rate state carried between consecutive forward-time events. -/
structure PipelineRateState (demeCount : ℕ) where
  effectiveSize : Fin demeCount → ℝ
  effectiveSize_pos : ∀ deme, 0 < effectiveSize deme
  migration : Fin demeCount → Fin demeCount → ℝ
  migration_nonneg : ∀ source target, 0 ≤ migration source target
  migration_self : ∀ deme, migration deme deme = 0
  mutationRate : ℝ
  mutationRate_nonneg : 0 ≤ mutationRate
  recombinationRate : ℝ
  recombinationRate_nonneg : 0 ≤ recombinationRate

/-- Initial certified rate state of a visible history. -/
def PipelineDemographicHistory.initialRateState {demeCount : ℕ}
    (history : PipelineDemographicHistory demeCount) : PipelineRateState demeCount where
  effectiveSize := history.initialEffectiveSize
  effectiveSize_pos := history.initialEffectiveSize_pos
  migration := history.initialMigration
  migration_nonneg := history.initialMigration_nonneg
  migration_self := history.initialMigration_self
  mutationRate := history.initialMutationRate
  mutationRate_nonneg := history.initialMutationRate_nonneg
  recombinationRate := history.initialRecombinationRate
  recombinationRate_nonneg := history.initialRecombinationRate_nonneg

/-- Raw-generation symmetric biallelic diffusion rates.  The coalescence coefficient is
`1/(2Nₑ)`; forward and backward mutation both use the history's declared mutation rate. -/
noncomputable def PipelineRateState.toManyDemeRates {demeCount : ℕ}
    (state : PipelineRateState demeCount) (active : Fin demeCount → Bool) :
    Coalescent.ManyDemeRates demeCount where
  coalescence := fun deme ↦ 1 / (2 * state.effectiveSize deme)
  migration := fun source target ↦
    if active source && active target then state.migration source target else 0
  forwardMutation := fun _ ↦ state.mutationRate
  backwardMutation := fun _ ↦ state.mutationRate
  coalescence_pos := fun deme ↦
    one_div_pos.mpr (mul_pos (by norm_num) (state.effectiveSize_pos deme))
  migration_nonneg := by
    intro source target
    split <;> simp_all [state.migration_nonneg]
  migration_self := by
    intro deme
    simp [state.migration_self]
  forwardMutation_nonneg := fun _ ↦ state.mutationRate_nonneg
  backwardMutation_nonneg := fun _ ↦ state.mutationRate_nonneg

/-- Raw-generation rates for the closed `H/DD/Dz/pi2` operator at a physical separation.
The scaled recombination coordinate is `2 r distance`, because a within-deme `DD = E[D²]`
contains two `D` factors; mutation similarly enters the heterozygosity equation as `2 mu`.

Empirical status: DERIVED -- a unit conversion from raw per-generation parameters into the
generator's rate carrier, with the two factors of two argued above from the shape of the
moment equations rather than fitted; the generator the rates feed carries its own status in
`Coalescent.TwoLocusHistory`. -/
noncomputable def PipelineRateState.toManyDemeLDRates {demeCount : ℕ}
    (state : PipelineRateState demeCount) (separationBp : ℝ)
    (separationBp_nonneg : 0 ≤ separationBp) (active : Fin demeCount → Bool) :
    Coalescent.ManyDemeLDRates demeCount where
  coalescence := fun deme ↦ 1 / (2 * state.effectiveSize deme)
  migration := fun source target ↦
    if active source && active target then state.migration source target else 0
  mutation := fun _ ↦ 2 * state.mutationRate
  recombination := fun _ ↦ 2 * state.recombinationRate * separationBp
  coalescence_pos := fun deme ↦
    one_div_pos.mpr (mul_pos two_pos (state.effectiveSize_pos deme))
  migration_nonneg := by
    intro source target
    split <;> simp_all [state.migration_nonneg]
  migration_self := fun deme ↦ by simp [state.migration_self]
  mutation_nonneg := fun _ ↦ mul_nonneg (by norm_num) state.mutationRate_nonneg
  recombination_nonneg := fun _ ↦
    mul_nonneg (mul_nonneg (by norm_num) state.recombinationRate_nonneg) separationBp_nonneg

/-- The one- and two-locus compilers use the same coalescence and migration rates, while the
two-locus recurrent-mutation coordinate is exactly the sum of the forward and backward
biallelic rates.  This is the rate-level part of the common-diffusion projection theorem. -/
theorem PipelineRateState.oneLocus_twoLocus_rate_coherence {demeCount : ℕ}
    (state : PipelineRateState demeCount) (active : Fin demeCount → Bool)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) (deme : Fin demeCount) :
    (state.toManyDemeLDRates separationBp separationBp_nonneg active).coalescence deme =
        (state.toManyDemeRates active).coalescence deme ∧
      (∀ target,
        (state.toManyDemeLDRates separationBp separationBp_nonneg active).migration deme target =
          (state.toManyDemeRates active).migration deme target) ∧
      (state.toManyDemeLDRates separationBp separationBp_nonneg active).mutation deme =
        (state.toManyDemeRates active).forwardMutation deme +
          (state.toManyDemeRates active).backwardMutation deme := by
  refine ⟨rfl, fun _ ↦ rfl, ?_⟩
  simp [PipelineRateState.toManyDemeLDRates, PipelineRateState.toManyDemeRates] <;> ring

/-- The common affine pair-divergence generator exposed by both demographic compilers. -/
noncomputable def PipelineRateState.pairDivergenceGenerator {demeCount : ℕ}
    (state : PipelineRateState demeCount) (active : Fin demeCount → Bool) :
    Matrix (Coalescent.AffinePairDivergenceCoordinate demeCount)
      (Coalescent.AffinePairDivergenceCoordinate demeCount) ℝ :=
  let rates := state.toManyDemeRates active
  Coalescent.augmentedPairDivergenceGenerator rates.coalescence rates.migration
    (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme)

/-- The degree-two marginal compiler exposes the common pair-divergence generator by
definition.  Naming the identity prevents downstream proofs from depending on reducibility
of the rate carrier. -/
theorem PipelineRateState.oneLocus_pairDivergenceGenerator_eq {demeCount : ℕ}
    (state : PipelineRateState demeCount) (active : Fin demeCount → Bool) :
    let rates := state.toManyDemeRates active
    Coalescent.augmentedPairDivergenceGenerator rates.coalescence rates.migration
        (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme) =
      state.pairDivergenceGenerator active := by
  rfl

/-- The `H` subsystem of the two-locus compiler uses exactly the common pair-divergence
generator, including the factor of two converting symmetric forward/back mutation to the
heterozygosity damping rate. -/
theorem PipelineRateState.twoLocus_pairDivergenceGenerator_eq {demeCount : ℕ}
    (state : PipelineRateState demeCount) (active : Fin demeCount → Bool)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    Coalescent.augmentedPairDivergenceGenerator
        (state.toManyDemeLDRates separationBp separationBp_nonneg active).coalescence
        (state.toManyDemeLDRates separationBp separationBp_nonneg active).migration
        (state.toManyDemeLDRates separationBp separationBp_nonneg active).mutation =
      state.pairDivergenceGenerator active := by
  unfold PipelineRateState.pairDivergenceGenerator
  congr 1
  funext deme
  simp [PipelineRateState.toManyDemeLDRates, PipelineRateState.toManyDemeRates]
  ring

/-- A synchronized reachable state of the marginal degree-two diffusion and the complete
two-locus diffusion.  Equality is asserted only after the two exact linear projections; the
full state spaces retain their distinct higher-order coordinates. -/
structure CommonDiffusionState (demeCount : ℕ) where
  marginal : Coalescent.AffineManyDemeMomentCoordinate demeCount 2 → ℝ
  joint : Coalescent.AffineLowOrderLDCoordinate demeCount → ℝ
  projection_eq :
    (Coalescent.manyDemePairDivergenceProjection demeCount).mulVec marginal =
      (Coalescent.lowOrderLDHProjection demeCount).mulVec joint
  marginal_constant : marginal none = 1
  marginal_zeroCoordinate : marginal (some (fun _ ↦ 0)) = 0
  joint_constant : joint none = 1

/-- Evolve both sides of a common-diffusion state through one visible epoch.  The proof field
uses the two matrix-exponential intertwining theorems and the rate compiler's exact generator
identity, so no step-size or closure approximation enters. -/
noncomputable def CommonDiffusionState.evolve {demeCount : ℕ}
    (common : CommonDiffusionState demeCount) (rates : PipelineRateState demeCount)
    (active : Fin demeCount → Bool) (separationBp : ℝ)
    (separationBp_nonneg : 0 ≤ separationBp) (duration : ℝ)
    (duration_nonneg : 0 ≤ duration) : CommonDiffusionState demeCount :=
  let marginalEpoch : Coalescent.ManyDemeMomentEpoch demeCount 2 :=
    { rates := rates.toManyDemeRates active
      duration := duration
      duration_nonneg := duration_nonneg }
  let jointEpoch := (rates.toManyDemeLDRates separationBp separationBp_nonneg active).epoch
    duration duration_nonneg
  { marginal := marginalEpoch.propagator.mulVec common.marginal
    joint := jointEpoch.propagator.mulVec common.joint
    projection_eq := by
      dsimp only [jointEpoch, Coalescent.LowOrderLDEpoch.propagator,
        Coalescent.ManyDemeLDRates.epoch]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Coalescent.manyDemePairDivergenceProjection_propagator_intertwines marginalEpoch
          (fun _ ↦ rfl),
        Coalescent.lowOrderLDHProjection_propagator_intertwines
          (rates.toManyDemeLDRates separationBp separationBp_nonneg active) duration,
        rates.oneLocus_pairDivergenceGenerator_eq active,
        rates.twoLocus_pairDivergenceGenerator_eq active separationBp separationBp_nonneg,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, common.projection_eq]
    marginal_constant := by
      rw [marginalEpoch.propagator_none, common.marginal_constant]
    marginal_zeroCoordinate := by
      rw [marginalEpoch.propagator_zeroCoordinate, common.marginal_zeroCoordinate]
    joint_constant := by
      rw [jointEpoch.propagator_none, common.joint_constant] }

/-- Apply one valid split to both sides of a common-diffusion state.  Exact relabeling commutes
with both projections, while the reachability fields discharge the affine/padding side
conditions that a raw rectangular vector need not satisfy. -/
noncomputable def CommonDiffusionState.split {demeCount : ℕ}
    (common : CommonDiffusionState demeCount) (parent child : Fin demeCount)
    (parent_ne_child : parent ≠ child) : CommonDiffusionState demeCount :=
  { marginal := Coalescent.splitManyDemeMomentState parent child common.marginal
    joint := (Coalescent.lowOrderLDSplitTransform parent child).mulVec common.joint
    projection_eq := by
      rw [Coalescent.manyDemePairDivergenceProjection_split parent child parent_ne_child
          common.marginal (by
            simpa [Coalescent.manyDemeMomentVectorTable] using
              common.marginal_zeroCoordinate),
        Coalescent.lowOrderLDHProjection_split parent child common.joint common.joint_constant,
        common.projection_eq]
    marginal_constant := by
      rw [Coalescent.splitManyDemeMomentState_none, common.marginal_constant]
    marginal_zeroCoordinate := by
      rw [Coalescent.splitManyDemeMomentState_zeroCoordinate,
        common.marginal_zeroCoordinate]
    joint_constant := by
      rw [Coalescent.lowOrderLDSplitTransform_none, common.joint_constant] }

/-- Apply the parameter update carried by an event.  A split changes the moment state, not
the rate state; its instantaneous transform is emitted separately by the compiler below. -/
def DemographicEvent.updateRateState {demeCount : ℕ}
    (event : DemographicEvent demeCount) (state : PipelineRateState demeCount) :
    PipelineRateState demeCount :=
  match event with
  | .split _ _ _ _ _ => state
  | .sizeChange _ _ effectiveSize effectiveSize_pos =>
      { state with effectiveSize := effectiveSize, effectiveSize_pos := effectiveSize_pos }
  | .migrationChange _ _ migration migration_nonneg migration_self =>
      { effectiveSize := state.effectiveSize
        effectiveSize_pos := state.effectiveSize_pos
        migration := migration
        migration_nonneg := migration_nonneg
        migration_self := migration_self
        mutationRate := state.mutationRate
        mutationRate_nonneg := state.mutationRate_nonneg
        recombinationRate := state.recombinationRate
        recombinationRate_nonneg := state.recombinationRate_nonneg }
  | .mutationRateChange _ _ mutationRate mutationRate_nonneg =>
      { state with
        mutationRate := mutationRate
        mutationRate_nonneg := mutationRate_nonneg }
  | .recombinationRateChange _ _ recombinationRate recombinationRate_nonneg =>
      { state with
        recombinationRate := recombinationRate
        recombinationRate_nonneg := recombinationRate_nonneg }

/-- Result of compiling a prefix of demographic events. -/
structure CompiledMomentEvents (demeCount K : ℕ) where
  instructions : List (Coalescent.ManyDemeMomentInstruction demeCount K)
  finalRateState : PipelineRateState demeCount
  finalActive : Fin demeCount → Bool

/-- Result of compiling a prefix into the concrete low-order two-locus operator. -/
structure CompiledLowOrderLDEvents (demeCount : ℕ) where
  instructions : List (Coalescent.LowOrderLDInstruction demeCount)
  finalRateState : PipelineRateState demeCount
  finalActive : Fin demeCount → Bool

/-- Compile the ordered event sequence into exact moment propagation.  Each event first evolves
under the preceding rates for its elapsed interval, then applies its instantaneous split (if
any), and finally updates the rates used by the next interval. -/
noncomputable def compileMomentEvents {demeCount : ℕ} (K : ℕ) :
    List (DemographicEvent demeCount) → PipelineRateState demeCount →
      (Fin demeCount → Bool) → CompiledMomentEvents demeCount K
  | [], state, active =>
      { instructions := [], finalRateState := state, finalActive := active }
  | event :: remaining, state, active =>
      let epoch : Coalescent.ManyDemeMomentEpoch demeCount K :=
        { rates := state.toManyDemeRates active
          duration := event.elapsed
          duration_nonneg := event.elapsed_nonneg }
      let front : List (Coalescent.ManyDemeMomentInstruction demeCount K) :=
        match event with
        | .split _ _ parent child _ => [.evolve epoch, .split parent child]
        | _ => [.evolve epoch]
      let tail := compileMomentEvents K remaining (event.updateRateState state)
        (event.updateActive active)
      { instructions := front ++ tail.instructions
        finalRateState := tail.finalRateState
        finalActive := tail.finalActive }

/-- Compile the same ordered history into the derived arbitrary-deme two-locus
generator.  Unlike a scalar distance recurrence, every epoch propagates the complete closed
moment state and every split applies the exact label pullback.

Empirical status: DERIVED -- a structural recursion turning the visible event list into
epoch and split instructions; it invents no rates and drops no event, and the composed
prediction it feeds is the untested composite named in `Coalescent.TwoLocusHistory`'s
module status. -/
noncomputable def compileLowOrderLDEvents {demeCount : ℕ}
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    List (DemographicEvent demeCount) → PipelineRateState demeCount →
      (Fin demeCount → Bool) → CompiledLowOrderLDEvents demeCount
  | [], state, active =>
      { instructions := [], finalRateState := state, finalActive := active }
  | event :: remaining, state, active =>
      let epoch := (state.toManyDemeLDRates separationBp separationBp_nonneg active).epoch
        event.elapsed event.elapsed_nonneg
      let front : List (Coalescent.LowOrderLDInstruction demeCount) :=
        match event with
        | .split _ _ parent child _ =>
            [.evolve epoch, Coalescent.LowOrderLDInstruction.split parent child]
        | _ => [.evolve epoch]
      let tail := compileLowOrderLDEvents separationBp separationBp_nonneg remaining
        (event.updateRateState state) (event.updateActive active)
      { instructions := front ++ tail.instructions
        finalRateState := tail.finalRateState
        finalActive := tail.finalActive }

/-- Result of executing the two synchronized diffusion states directly over a visible event
list.  The final rate and active-deme states are retained so the terminal epoch can be applied
without reinterpreting the event sequence. -/
structure CommonDiffusionEventRun (demeCount : ℕ) where
  state : CommonDiffusionState demeCount
  finalRateState : PipelineRateState demeCount
  finalActive : Fin demeCount → Bool

/-- Direct synchronized execution of an arbitrary finite event list.  Each event evolves both
states under the preceding rates, applies the exact split pullback when present, and then
updates the rate/active carriers for the recursive suffix. -/
noncomputable def runCommonDiffusionEvents {demeCount : ℕ}
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    List (DemographicEvent demeCount) → PipelineRateState demeCount →
      (Fin demeCount → Bool) → CommonDiffusionState demeCount →
        CommonDiffusionEventRun demeCount
  | [], rates, active, common =>
      { state := common, finalRateState := rates, finalActive := active }
  | event :: remaining, rates, active, common =>
      let evolved := common.evolve rates active separationBp separationBp_nonneg
        event.elapsed event.elapsed_nonneg
      let afterEvent := match event with
        | .split _ _ parent child parent_ne_child =>
            evolved.split parent child parent_ne_child
        | _ => evolved
      runCommonDiffusionEvents separationBp separationBp_nonneg remaining
        (event.updateRateState rates) (event.updateActive active) afterEvent

/-- The marginal component of synchronized execution is exactly the existing degree-two
one-locus instruction compiler followed by its fold, for every event list and starting state. -/
theorem runCommonDiffusionEvents_marginal {demeCount : ℕ}
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp)
    (events : List (DemographicEvent demeCount)) (rates : PipelineRateState demeCount)
    (active : Fin demeCount → Bool) (common : CommonDiffusionState demeCount) :
    (runCommonDiffusionEvents separationBp separationBp_nonneg events rates active common).state.marginal =
      Coalescent.propagateManyDemeMomentInstructions
        (compileMomentEvents 2 events rates active).instructions common.marginal := by
  induction events generalizing rates active common with
  | nil => rfl
  | cons event remaining ih =>
      cases event <;>
        simp [runCommonDiffusionEvents, compileMomentEvents,
          Coalescent.propagateManyDemeMomentInstructions, List.foldl_append,
          Coalescent.ManyDemeMomentInstruction.apply,
          CommonDiffusionState.evolve, CommonDiffusionState.split, ih]

/-- The joint component of synchronized execution is exactly the existing low-order two-locus
instruction compiler followed by its fold. -/
theorem runCommonDiffusionEvents_joint {demeCount : ℕ}
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp)
    (events : List (DemographicEvent demeCount)) (rates : PipelineRateState demeCount)
    (active : Fin demeCount → Bool) (common : CommonDiffusionState demeCount) :
    (runCommonDiffusionEvents separationBp separationBp_nonneg events rates active common).state.joint =
      Coalescent.propagateLowOrderLDInstructions
        (compileLowOrderLDEvents separationBp separationBp_nonneg events rates active).instructions
        common.joint := by
  induction events generalizing rates active common with
  | nil => rfl
  | cons event remaining ih =>
      cases event <;>
        simp [runCommonDiffusionEvents, compileLowOrderLDEvents,
          Coalescent.propagateLowOrderLDInstructions, List.foldl_append,
          Coalescent.LowOrderLDInstruction.apply, Coalescent.LowOrderLDInstruction.split,
          CommonDiffusionState.evolve, CommonDiffusionState.split, ih]

/-- Direct synchronized execution and both independent instruction compilers finish with the
same rate and active-deme carriers. -/
theorem runCommonDiffusionEvents_finalCarriers {demeCount : ℕ}
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp)
    (events : List (DemographicEvent demeCount)) (rates : PipelineRateState demeCount)
    (active : Fin demeCount → Bool) (common : CommonDiffusionState demeCount) :
    let run := runCommonDiffusionEvents separationBp separationBp_nonneg events rates active common
    let marginalCompiled := compileMomentEvents 2 events rates active
    let jointCompiled := compileLowOrderLDEvents separationBp separationBp_nonneg events rates active
    run.finalRateState = marginalCompiled.finalRateState ∧
      run.finalActive = marginalCompiled.finalActive ∧
      run.finalRateState = jointCompiled.finalRateState ∧
      run.finalActive = jointCompiled.finalActive := by
  induction events generalizing rates active common with
  | nil => simp [runCommonDiffusionEvents, compileMomentEvents, compileLowOrderLDEvents]
  | cons event remaining ih =>
      cases event <;>
        simp only [runCommonDiffusionEvents, compileMomentEvents, compileLowOrderLDEvents]
      all_goals exact ih _ _ _

/-- Exact one-locus moment instructions for the whole visible event history.  Recombination
updates are retained in the rate state for the two-locus compiler; they correctly have no
effect on this one-locus generator. -/
noncomputable def PipelineDemographicHistory.oneLocusMomentInstructions
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ) :
    List (Coalescent.ManyDemeMomentInstruction demeCount K) :=
  let compiled := compileMomentEvents K history.events history.initialRateState
    (initialDemeActive history.events)
  let finalEpoch : Coalescent.ManyDemeMomentEpoch demeCount K :=
    { rates := compiled.finalRateState.toManyDemeRates compiled.finalActive
      duration := history.finalElapsed
      duration_nonneg := history.finalElapsed_nonneg }
  compiled.instructions ++ [.evolve finalEpoch]

/-- Constant ancestral one-deme rates implied by the visible history.  The ancestral
population is assumed to have occupied its initial epoch long enough to reach the stationary
low-order law; this is the same equilibrium boundary condition used by coalescent genome
simulation rather than an extra fitted moment table.

Empirical status: DERIVED, with one named assumption -- the rates are the root epoch's own
parameters in generator units, and the stationarity of the ancestral boundary is an
assumption this docstring states rather than hides; it is the boundary condition coalescent
simulators impose, so a battery comparing the composed pipeline against `msprime` shares it
rather than testing it. -/
noncomputable def PipelineDemographicHistory.ancestralLDRates
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    Coalescent.ManyDemeLDRates 1 where
  coalescence := fun _ ↦ 1 / (2 * history.initialEffectiveSize history.ancestralDeme)
  migration := fun _ _ ↦ 0
  mutation := fun _ ↦ 2 * history.initialMutationRate
  recombination := fun _ ↦ 2 * history.initialRecombinationRate * separationBp
  coalescence_pos := fun _ ↦ one_div_pos.mpr
    (mul_pos (by norm_num) (history.initialEffectiveSize_pos history.ancestralDeme))
  migration_nonneg := fun _ _ ↦ le_rfl
  migration_self := fun _ ↦ rfl
  mutation_nonneg := fun _ ↦ mul_nonneg (by norm_num) history.initialMutationRate_nonneg
  recombination_nonneg := fun _ ↦
    mul_nonneg (mul_nonneg (by norm_num) history.initialRecombinationRate_nonneg)
      separationBp_nonneg

/-- The ancestral marginal and linkage compilers start from the same heterozygosity.
The left side is the one-locus symmetric-beta boundary used by finite-cohort ascertainment;
the right side is the `H` coordinate of the recurrent two-locus stationary boundary.  The
identity holds at every marker separation (including zero mutation), so neither side carries
an independent boundary constant that could leave a hidden gap between the two factors. -/
theorem PipelineDemographicHistory.ancestralHeterozygosity_eq_lowOrderH
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    2 * (history.ancestralMoment 1 - history.ancestralMoment 2) =
      Coalescent.oneDemeStationaryLowOrderLDState
        (history.ancestralLDRates separationBp separationBp_nonneg)
          (some (.H 0 0)) := by
  simpa [PipelineDemographicHistory.ancestralMoment,
    PipelineDemographicHistory.ancestralMutationShape,
    PipelineDemographicHistory.ancestralLDRates,
    Coalescent.oneDemeStationaryLowOrderLDState] using
    symmetricBetaHeterozygosity_eq_recurrentLowOrderH
      (history.initialEffectiveSize history.ancestralDeme)
      history.initialMutationRate
      (history.initialEffectiveSize_pos history.ancestralDeme)
      history.initialMutationRate_nonneg

/-- The two concrete compilers begin in one common projected state.  This packages the
symmetric-beta/recurrent-two-locus boundary identity together with the affine reachability
invariants required by every later split. -/
noncomputable def PipelineDemographicHistory.initialCommonDiffusionState
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    CommonDiffusionState demeCount :=
  { marginal := Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment
    joint := Coalescent.commonAncestralLowOrderLDState
      (history.ancestralLDRates separationBp separationBp_nonneg)
    projection_eq := by
      rw [Coalescent.manyDemePairDivergenceProjection_commonAncestor,
        Coalescent.lowOrderLDHProjection_commonAncestral]
      funext coordinate
      cases coordinate with
      | none => rfl
      | some pair =>
          exact history.ancestralHeterozygosity_eq_lowOrderH separationBp
            separationBp_nonneg
    marginal_constant := rfl
    marginal_zeroCoordinate := by
      simp [Coalescent.commonAncestorManyDemeMomentState,
        Coalescent.ManyDemeMomentCoordinate.degree]
    joint_constant := rfl }

/-- Synchronized present-day state after the complete event list and terminal epoch. -/
noncomputable def PipelineDemographicHistory.presentCommonDiffusionState
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    CommonDiffusionState demeCount :=
  let run := runCommonDiffusionEvents separationBp separationBp_nonneg history.events
    history.initialRateState (initialDemeActive history.events)
    (history.initialCommonDiffusionState separationBp separationBp_nonneg)
  run.state.evolve run.finalRateState run.finalActive separationBp separationBp_nonneg
    history.finalElapsed history.finalElapsed_nonneg

/-- The synchronized present marginal is exactly the public degree-two one-locus history
evaluation, including the terminal epoch. -/
theorem PipelineDemographicHistory.presentCommonDiffusionState_marginal
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    (history.presentCommonDiffusionState separationBp separationBp_nonneg).marginal =
      Coalescent.propagateManyDemeMomentInstructions
        (history.oneLocusMomentInstructions 2)
        (Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment) := by
  let initial := history.initialCommonDiffusionState separationBp separationBp_nonneg
  let run := runCommonDiffusionEvents separationBp separationBp_nonneg history.events
    history.initialRateState (initialDemeActive history.events) initial
  let compiled := compileMomentEvents 2 history.events history.initialRateState
    (initialDemeActive history.events)
  have hstate := runCommonDiffusionEvents_marginal separationBp separationBp_nonneg
    history.events history.initialRateState (initialDemeActive history.events) initial
  have hcarriers := runCommonDiffusionEvents_finalCarriers separationBp separationBp_nonneg
    history.events history.initialRateState (initialDemeActive history.events) initial
  change (run.state.evolve run.finalRateState run.finalActive separationBp separationBp_nonneg
      history.finalElapsed history.finalElapsed_nonneg).marginal = _
  change run.state.marginal = _ at hstate
  change run.finalRateState = compiled.finalRateState ∧
    run.finalActive = compiled.finalActive ∧ _ at hcarriers
  simp only [CommonDiffusionState.evolve]
  rw [hstate, hcarriers.1, hcarriers.2.1]
  simp [CommonDiffusionState.evolve,
    PipelineDemographicHistory.oneLocusMomentInstructions,
    PipelineDemographicHistory.initialCommonDiffusionState,
    Coalescent.propagateManyDemeMomentInstructions,
    Coalescent.ManyDemeMomentInstruction.apply, List.foldl_append, compiled, initial]

/-- Complete concrete two-locus history at one physical marker separation.

Empirical status: DERIVED -- the ancestral boundary, the compiled instruction list, and the
final epoch assembled into one `Coalescent.LowOrderLDHistory`; each part carries its own
status and this composition adds no new quantity.  The composed present-day prediction is
the untested composite named in `Coalescent.TwoLocusHistory`'s module status. -/
noncomputable def PipelineDemographicHistory.lowOrderLDHistory
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    Coalescent.LowOrderLDHistory demeCount :=
  let compiled := compileLowOrderLDEvents separationBp separationBp_nonneg history.events
    history.initialRateState (initialDemeActive history.events)
  let finalEpoch := (compiled.finalRateState.toManyDemeLDRates
    separationBp separationBp_nonneg compiled.finalActive).epoch
      history.finalElapsed history.finalElapsed_nonneg
  { initial := Coalescent.commonAncestralLowOrderLDState
      (history.ancestralLDRates separationBp separationBp_nonneg)
    initial_constant := rfl
    instructions := compiled.instructions ++ [.evolve finalEpoch] }

/-- The synchronized present joint state is exactly the public low-order two-locus history
evaluation, including the same terminal epoch. -/
theorem PipelineDemographicHistory.presentCommonDiffusionState_joint
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (separationBp : ℝ) (separationBp_nonneg : 0 ≤ separationBp) :
    (history.presentCommonDiffusionState separationBp separationBp_nonneg).joint =
      (history.lowOrderLDHistory separationBp separationBp_nonneg).present := by
  let initial := history.initialCommonDiffusionState separationBp separationBp_nonneg
  let run := runCommonDiffusionEvents separationBp separationBp_nonneg history.events
    history.initialRateState (initialDemeActive history.events) initial
  let compiled := compileLowOrderLDEvents separationBp separationBp_nonneg history.events
    history.initialRateState (initialDemeActive history.events)
  have hstate := runCommonDiffusionEvents_joint separationBp separationBp_nonneg
    history.events history.initialRateState (initialDemeActive history.events) initial
  have hcarriers := runCommonDiffusionEvents_finalCarriers separationBp separationBp_nonneg
    history.events history.initialRateState (initialDemeActive history.events) initial
  change (run.state.evolve run.finalRateState run.finalActive separationBp separationBp_nonneg
      history.finalElapsed history.finalElapsed_nonneg).joint = _
  change run.state.joint = _ at hstate
  change _ ∧ _ ∧ run.finalRateState = compiled.finalRateState ∧
    run.finalActive = compiled.finalActive at hcarriers
  simp only [CommonDiffusionState.evolve]
  rw [hstate, hcarriers.2.2.1, hcarriers.2.2.2]
  simp [CommonDiffusionState.evolve, PipelineDemographicHistory.lowOrderLDHistory,
    PipelineDemographicHistory.initialCommonDiffusionState,
    Coalescent.LowOrderLDHistory.present, Coalescent.propagateLowOrderLDInstructions,
    Coalescent.LowOrderLDInstruction.apply, List.foldl_append, compiled, initial]

/-- The arbitrary-deme, arbitrary-event two-locus moment family constructed from the visible
demographic history.  This is the concrete missing bridge from history to `DD/Dz/pi2`; marker
separation is typed nonnegative and all rate changes are compiled into the epoch product. -/
noncomputable def PipelineDemographicHistory.twoLocusMoments
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) :
    Coalescent.DemographicTwoLocusMoments demeCount :=
  Coalescent.LowOrderLDHistory.toDemographicTwoLocusMoments fun separation ↦
    history.lowOrderLDHistory separation.value separation.value_nonneg

/-- Complete present-day finite one-locus moment state at a requested truncation degree. -/
noncomputable def PipelineDemographicHistory.presentMomentState
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ) :
    Coalescent.AffineManyDemeMomentCoordinate demeCount K → ℝ :=
  Coalescent.propagateManyDemeMomentInstructions
    (history.oneLocusMomentInstructions K)
    (Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment)

/-- The visible history preserves the normalized affine constant through every epoch and
split. -/
theorem PipelineDemographicHistory.presentMomentState_none
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ) :
    history.presentMomentState K none = 1 := by
  rw [PipelineDemographicHistory.presentMomentState,
    Coalescent.propagateManyDemeMomentInstructions_none]
  rfl

/-- Exact present-day mixed one-locus moment produced by the visible event history.  The
matrix dimension is finite for every requested degree, and every epoch is a matrix
exponential; no closure or fitted attenuation enters. -/
noncomputable def PipelineDemographicHistory.oneLocusMoment
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ)
    (exponent : Fin demeCount → ℕ) : ℝ :=
  if ∀ deme, exponent deme = 0 then 1
  else
    Coalescent.manyDemeMomentVectorTable K
      (fun coordinate ↦ history.presentMomentState K (some coordinate)) exponent

/-- The public one-locus moment is exactly the augmented-state readout for every exponent,
including the normalized degree-zero monomial. -/
theorem PipelineDemographicHistory.oneLocusMoment_eq_stateReadout
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ)
    (exponent : Fin demeCount → ℕ) :
    history.oneLocusMoment K exponent =
      Coalescent.manyDemeMomentStateReadout K (history.presentMomentState K) exponent := by
  by_cases hzero : ∀ deme, exponent deme = 0
  · simp [PipelineDemographicHistory.oneLocusMoment,
      Coalescent.manyDemeMomentStateReadout, hzero,
      history.presentMomentState_none]
  · simp [PipelineDemographicHistory.oneLocusMoment,
      Coalescent.manyDemeMomentStateReadout, hzero]

/-- Exact train-target mixed frequency moment from the arbitrary-deme history. -/
noncomputable def PipelineDemographicHistory.pairMoment
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ)
    (train target : Fin demeCount) (sourceDegree targetDegree : ℕ) : ℝ :=
  history.oneLocusMoment K
    (Coalescent.pairExponent train target sourceDegree targetDegree)

/-- Exact joint allele-count law for any train-target pair and cohort sizes.  Sample size
enters both the propagated moment degree `ns + nt` and this Bernstein event polynomial. -/
noncomputable def PipelineDemographicHistory.jointSampleCount
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (train target : Fin demeCount) (ns nt sourceCount targetCount : ℕ) : ℝ :=
  if sourceCount ≤ ns ∧ targetCount ≤ nt then
    (Nat.choose ns sourceCount : ℝ) * (Nat.choose nt targetCount : ℝ) *
      (∑ a ∈ Finset.range (ns - sourceCount + 1),
        ∑ b ∈ Finset.range (nt - targetCount + 1),
          (Nat.choose (ns - sourceCount) a : ℝ) *
          (Nat.choose (nt - targetCount) b : ℝ) * (-1 : ℝ) ^ (a + b) *
          history.pairMoment (ns + nt) train target
            (sourceCount + a) (targetCount + b))
  else 0

/-! ### Exact pooled-panel ascertainment over every deme -/

/-- One allele-count cell for a many-deme sample layout.  The dependent finite type makes an
out-of-range count unrepresentable. -/
abbrev ManyDemeSampleCount {demeCount : ℕ} (sampleSize : Fin demeCount → ℕ) :=
  ∀ deme, Fin (sampleSize deme + 1)

/-- The number of complement factors remaining after fixing a many-deme count cell. -/
abbrev ManyDemeBernsteinRemainder {demeCount : ℕ}
    (sampleSize : Fin demeCount → ℕ) (count : ManyDemeSampleCount sampleSize) :=
  ∀ deme, Fin (sampleSize deme - count deme + 1)

/-- Total haplotype count in a many-deme panel. -/
def manyDemeTotalSampleSize {demeCount : ℕ} (sampleSize : Fin demeCount → ℕ) : ℕ :=
  ∑ deme, sampleSize deme

/-- Total derived-allele count in one many-deme sample cell. -/
def ManyDemeSampleCount.total {demeCount : ℕ} {sampleSize : Fin demeCount → ℕ}
    (count : ManyDemeSampleCount sampleSize) : ℕ :=
  ∑ deme, (count deme : ℕ)

/-- A typed count cell cannot contain more derived alleles than the panel contains
haplotypes. -/
theorem ManyDemeSampleCount.total_le_totalSampleSize
    {demeCount : ℕ} {sampleSize : Fin demeCount → ℕ}
    (count : ManyDemeSampleCount sampleSize) :
    count.total ≤ manyDemeTotalSampleSize sampleSize := by
  unfold ManyDemeSampleCount.total manyDemeTotalSampleSize
  apply Finset.sum_le_sum
  intro deme _
  have := (count deme).isLt
  omega

/-- Total degree of a many-deme probe monomial. -/
def manyDemeExponentDegree {demeCount : ℕ} (exponent : Fin demeCount → ℕ) : ℕ :=
  ∑ deme, exponent deme

/-- Exact joint count-cell mass multiplied by an arbitrary latent-frequency monomial.

For count cell `c`, sample layout `n`, and probe exponent `q`, this is

`E[(∏ p_d^(q_d)) (∏ choose(n_d,c_d) p_d^(c_d) (1-p_d)^(n_d-c_d))]`.

Every complement power is expanded by the finite binomial theorem, so the result is one
finite sum of propagated moments at degree `Σ n_d + Σ q_d`.  Adding probe lineages before
conditioning is essential: reusing the ascertaining sample's empirical frequency would
compute a different, selection-biased statistic. -/
noncomputable def PipelineDemographicHistory.manyDemeSampleCountMomentMass
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (count : ManyDemeSampleCount sampleSize)
    (probeExponent : Fin demeCount → ℕ) : ℝ := by
  classical
  exact
    (∏ deme, (Nat.choose (sampleSize deme) (count deme) : ℝ)) *
      ∑ remainder : ManyDemeBernsteinRemainder sampleSize count,
        (-1 : ℝ) ^ (∑ deme, (remainder deme : ℕ)) *
          (∏ deme,
            (Nat.choose (sampleSize deme - count deme) (remainder deme) : ℝ)) *
          history.oneLocusMoment
            (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent)
            (fun deme ↦ (count deme : ℕ) + (remainder deme : ℕ) + probeExponent deme)

/-- Terminal coefficient vector for one many-deme sample-count cell with an additional
frequency monomial.  It is the exact Bernstein polynomial expressed in the augmented moment
basis, before any demographic propagation is performed. -/
noncomputable def manyDemeSampleCountMomentProbe
    {demeCount : ℕ} (sampleSize : Fin demeCount → ℕ)
    (count : ManyDemeSampleCount sampleSize)
    (probeExponent : Fin demeCount → ℕ) :
    Coalescent.AffineManyDemeMomentCoordinate demeCount
      (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) → ℝ := by
  classical
  let K := manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent
  exact (∏ deme, (Nat.choose (sampleSize deme) (count deme) : ℝ)) •
    ∑ remainder : ManyDemeBernsteinRemainder sampleSize count,
      ((-1 : ℝ) ^ (∑ deme, (remainder deme : ℕ)) *
        (∏ deme,
          (Nat.choose (sampleSize deme - count deme) (remainder deme) : ℝ))) •
        Coalescent.manyDemeMomentReadoutProbe K
          (fun deme ↦ (count deme : ℕ) + (remainder deme : ℕ) + probeExponent deme)

/-- Pairing the cell probe with the propagated moment state reproduces the original exact
Bernstein count-cell mass.  Thus the cell law needs one propagated vector, not one separate
history solve for every complement term. -/
theorem manyDemeSampleCountMomentProbe_dot_present
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (count : ManyDemeSampleCount sampleSize)
    (probeExponent : Fin demeCount → ℕ) :
    manyDemeSampleCountMomentProbe sampleSize count probeExponent ⬝ᵥ
        history.presentMomentState
          (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) =
      history.manyDemeSampleCountMomentMass sampleSize count probeExponent := by
  classical
  unfold manyDemeSampleCountMomentProbe
  rw [smul_dotProduct]
  simp_rw [sum_dotProduct, smul_dotProduct,
    Coalescent.manyDemeMomentReadoutProbe_dotProduct,
    ← history.oneLocusMoment_eq_stateReadout]
  simp [PipelineDemographicHistory.manyDemeSampleCountMomentMass, smul_eq_mul]

/-- An exact rational minor-allele-frequency threshold.  The field
`2 * numerator ≤ denominator` pins the conventional minor-frequency range `[0,1/2]`; the
positive denominator forbids a vacuous ratio. -/
structure PooledMAFThreshold where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  twice_numerator_le_denominator : 2 * numerator ≤ denominator

/-- Whether a pooled derived count passes a rational MAF threshold.  Cross multiplication
avoids floating-point rounding and treats either allele orientation identically. -/
def PooledMAFThreshold.Accepts (threshold : PooledMAFThreshold)
    (totalCount derivedCount : ℕ) : Prop :=
  threshold.numerator * totalCount ≤
    threshold.denominator * min derivedCount (totalCount - derivedCount)

/-- The pooled MAF event is invariant to which allele is called derived.  The count-domain
hypothesis is supplied automatically by `ManyDemeSampleCount.total_le_totalSampleSize` for
every cell summed by the ascertainment law. -/
theorem PooledMAFThreshold.accepts_alleleComplement
    (threshold : PooledMAFThreshold) (totalCount derivedCount : ℕ)
    (derived_le : derivedCount ≤ totalCount) :
    threshold.Accepts totalCount (totalCount - derivedCount) ↔
      threshold.Accepts totalCount derivedCount := by
  unfold PooledMAFThreshold.Accepts
  rw [Nat.sub_sub_self derived_le, min_comm]

/-- The executable causal reservoir's declared one-percent pooled-MAF threshold, represented
exactly as `1/100`. -/
def gnomonCausalMAFThreshold : PooledMAFThreshold where
  numerator := 1
  denominator := 100
  denominator_pos := by norm_num
  twice_numerator_le_denominator := by norm_num

/-- Unnormalized probe-moment mass of a pooled-MAF ascertainment event.  The sum ranges over
the complete Cartesian sample-count grid for every finite number of demes; no pairwise
projection can replace this event because the acceptance predicate couples all coordinates. -/
noncomputable def PipelineDemographicHistory.pooledMAFProbeMass
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) : ℝ := by
  classical
  exact ∑ count : ManyDemeSampleCount sampleSize,
    if threshold.Accepts (manyDemeTotalSampleSize sampleSize) count.total then
      history.manyDemeSampleCountMomentMass sampleSize count probeExponent
    else 0

/-- One terminal vector for the complete pooled-MAF event and requested probe monomial.
All accepted count cells are combined before demographic propagation. -/
noncomputable def pooledMAFTerminalProbe
    {demeCount : ℕ} (sampleSize : Fin demeCount → ℕ)
    (threshold : PooledMAFThreshold) (probeExponent : Fin demeCount → ℕ) :
    Coalescent.AffineManyDemeMomentCoordinate demeCount
      (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) → ℝ := by
  classical
  exact ∑ count : ManyDemeSampleCount sampleSize,
    if threshold.Accepts (manyDemeTotalSampleSize sampleSize) count.total then
      manyDemeSampleCountMomentProbe sampleSize count probeExponent
    else 0

/-- The complete ascertainment polynomial paired with the present moment state is exactly
the pooled-MAF probe mass. -/
theorem pooledMAFTerminalProbe_dot_present
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) :
    pooledMAFTerminalProbe sampleSize threshold probeExponent ⬝ᵥ
        history.presentMomentState
          (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) =
      history.pooledMAFProbeMass sampleSize threshold probeExponent := by
  classical
  unfold pooledMAFTerminalProbe PipelineDemographicHistory.pooledMAFProbeMass
  rw [sum_dotProduct]
  apply Finset.sum_congr rfl
  intro count _
  by_cases accepted :
      threshold.Accepts (manyDemeTotalSampleSize sampleSize) count.total
  · simp [accepted, manyDemeSampleCountMomentProbe_dot_present]
  · simp [accepted]

/-- Exact sampling-dual evaluation of the finite pooled-MAF ascertainment object.  The
terminal Bernstein probe is propagated backward through the transposed epoch generators and
sparse split matrices, then paired once with the common-ancestor moment state. -/
theorem PipelineDemographicHistory.pooledMAFProbeMass_samplingDual
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) :
    history.pooledMAFProbeMass sampleSize threshold probeExponent =
      (Coalescent.manyDemeMomentHistoryDualPropagator
        (history.oneLocusMomentInstructions
          (manyDemeTotalSampleSize sampleSize +
            manyDemeExponentDegree probeExponent))).mulVec
          (pooledMAFTerminalProbe sampleSize threshold probeExponent) ⬝ᵥ
        Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment := by
  rw [← Coalescent.propagateManyDemeMomentInstructions_samplingDual]
  exact (pooledMAFTerminalProbe_dot_present history sampleSize threshold probeExponent).symm

/-- Backward-operator presentation of one pooled-MAF probe mass. -/
noncomputable def PipelineDemographicHistory.pooledMAFProbeMassViaDual
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) : ℝ :=
  (Coalescent.manyDemeMomentHistoryDualPropagator
    (history.oneLocusMomentInstructions
      (manyDemeTotalSampleSize sampleSize +
        manyDemeExponentDegree probeExponent))).mulVec
      (pooledMAFTerminalProbe sampleSize threshold probeExponent) ⬝ᵥ
    Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment

/-- Direct finite Cartesian summation and backward sampling-dual evaluation are the same
scalar, for every finite panel and arbitrary visible demographic history. -/
theorem PipelineDemographicHistory.pooledMAFProbeMassViaDual_eq
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) :
    history.pooledMAFProbeMassViaDual sampleSize threshold probeExponent =
      history.pooledMAFProbeMass sampleSize threshold probeExponent :=
  (history.pooledMAFProbeMass_samplingDual sampleSize threshold probeExponent).symm

/-- Finite certified approximation to one pooled-MAF probe mass.  The caller may assign a
different Taylor order to every demographic epoch; splits remain exact sparse maps. -/
noncomputable def PipelineDemographicHistory.pooledMAFProbeMassCertifiedApproximation
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ)
    (termOrder : Coalescent.ManyDemeMomentEpoch demeCount
      (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) → ℕ) : ℝ :=
  let K := manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent
  let certified := Coalescent.certifyManyDemeMomentHistory termOrder
    (history.oneLocusMomentInstructions K)
  (Coalescent.certifiedManyDemeMomentHistoryApproximation certified).mulVec
      (pooledMAFTerminalProbe sampleSize threshold probeExponent) ⬝ᵥ
    Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment

/-- Proven absolute-error radius for the finite pooled-MAF probe evaluation. -/
noncomputable def PipelineDemographicHistory.pooledMAFProbeMassCertifiedError
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ)
    (termOrder : Coalescent.ManyDemeMomentEpoch demeCount
      (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) → ℕ) : ℝ :=
  let K := manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent
  let certified := Coalescent.certifyManyDemeMomentHistory termOrder
    (history.oneLocusMomentInstructions K)
  Coalescent.certifiedManyDemeMomentHistoryErrorBound certified *
      ‖pooledMAFTerminalProbe sampleSize threshold probeExponent‖ *
    ∑ coordinate : Coalescent.AffineManyDemeMomentCoordinate demeCount K,
      |Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment coordinate|

/-- The exact pooled-MAF probe mass lies in the closed interval centered at the finite
scheduled evaluation with the displayed certified radius. -/
theorem PipelineDemographicHistory.pooledMAFProbeMassCertified_error_le
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ)
    (termOrder : Coalescent.ManyDemeMomentEpoch demeCount
      (manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent) → ℕ) :
    |history.pooledMAFProbeMass sampleSize threshold probeExponent -
        history.pooledMAFProbeMassCertifiedApproximation sampleSize threshold probeExponent
          termOrder| ≤
      history.pooledMAFProbeMassCertifiedError sampleSize threshold probeExponent termOrder := by
  let K := manyDemeTotalSampleSize sampleSize + manyDemeExponentDegree probeExponent
  let instructions := history.oneLocusMomentInstructions K
  let certified := Coalescent.certifyManyDemeMomentHistory termOrder instructions
  have hbound := Coalescent.certifiedManyDemeMomentHistory_pairing_error_le certified
    (pooledMAFTerminalProbe sampleSize threshold probeExponent)
    (Coalescent.commonAncestorManyDemeMomentState history.ancestralMoment)
  rw [Coalescent.certifiedScheduledHistoryExact_eq_dualPropagator] at hbound
  rw [history.pooledMAFProbeMass_samplingDual]
  exact hbound

/-- Exact arbitrary-order many-deme frequency moment conditional on a pooled sample passing
the MAF window.  `none` means the ascertainment event has zero mass.  This operator is finite
for every finite sample layout and exponent and is therefore exactly evaluable without a
frequency grid, density closure, fitted constant, or large-cohort limit. -/
noncomputable def PipelineDemographicHistory.momentGivenPooledMAF
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) : Option ℝ :=
  let denominator := history.pooledMAFProbeMass sampleSize threshold (fun _ ↦ 0)
  if 0 < denominator then
    some (history.pooledMAFProbeMass sampleSize threshold probeExponent / denominator)
  else none

/-- The conditional pooled-MAF moment is exactly the ratio of two history-wide backward
operator evaluations.  This is the single positive law replacing repeated forward solves;
the zero-event branch remains explicitly undefined. -/
theorem PipelineDemographicHistory.momentGivenPooledMAF_eq_samplingDual
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (probeExponent : Fin demeCount → ℕ) :
    history.momentGivenPooledMAF sampleSize threshold probeExponent =
      let denominator :=
        history.pooledMAFProbeMassViaDual sampleSize threshold (fun _ ↦ 0)
      if 0 < denominator then
        some (history.pooledMAFProbeMassViaDual sampleSize threshold probeExponent /
          denominator)
      else none := by
  simp only [PipelineDemographicHistory.momentGivenPooledMAF]
  rw [history.pooledMAFProbeMassViaDual_eq sampleSize threshold (fun _ ↦ 0),
    history.pooledMAFProbeMassViaDual_eq sampleSize threshold probeExponent]

/-- The conditional zeroth moment is exactly one whenever the ascertainment event has
positive mass. -/
theorem PipelineDemographicHistory.momentGivenPooledMAF_zero
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (sampleSize : Fin demeCount → ℕ) (threshold : PooledMAFThreshold)
    (positive : 0 < history.pooledMAFProbeMass sampleSize threshold (fun _ ↦ 0)) :
    history.momentGivenPooledMAF sampleSize threshold (fun _ ↦ 0) = some 1 := by
  simp [PipelineDemographicHistory.momentGivenPooledMAF, positive, div_self positive.ne']

/-- Exact cohort-size-aware target erosion derived directly from the visible demographic
history, rather than from a time-shift surrogate. -/
noncomputable def PipelineDemographicHistory.targetErosion
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (train target : Fin demeCount) (ns nt : ℕ) : Option ℝ :=
  Coalescent.targetErosionEvent (history.jointSampleCount train target ns nt) ns nt

/-- Exact factorial moment of the target allele frequency after source-sample ascertainment.
Both the ascertainment cohort and target evaluation cohort are compiled into the joint
Bernstein law.  No population-frequency plug-in or large-sample limit appears. -/
noncomputable def PipelineDemographicHistory.sourcePolymorphicTargetFactorialMoment
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (train target : Fin demeCount) (ns nt order : ℕ) : Option ℝ :=
  Coalescent.targetFactorialMomentGivenSourcePolymorphic
    (history.jointSampleCount train target ns nt) ns nt order

/-- Exact target heterozygosity conditional on the source sample being polymorphic.  This is
the source-polymorphic tag-spectrum coordinate needed to construct target genotype variance;
target fixation probability is only one boundary event of the same joint law.  The distinct
pooled-MAF causal-panel event is constructed separately. -/
noncomputable def PipelineDemographicHistory.sourcePolymorphicTargetHeterozygosity
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (train target : Fin demeCount) (ns nt : ℕ) : Option ℝ :=
  Coalescent.targetHeterozygosityGivenSourcePolymorphic
    (history.jointSampleCount train target ns nt) ns nt

/-- Study-design constants named by the requested endpoint. -/
structure PipelineStudyDesign (demeCount : ℕ) where
  gwasDeme : Fin demeCount
  gwasSampleSize : ℕ
  gwasSampleSize_pos : 0 < gwasSampleSize
  selectionThresholds : List ℝ
  selectionThresholds_nonempty : selectionThresholds ≠ []
  selectionThresholds_nonneg : ∀ threshold ∈ selectionThresholds, 0 ≤ threshold
  selectionThresholds_le_one : ∀ threshold ∈ selectionThresholds, threshold ≤ 1
  clumpR2Threshold : ℝ
  clumpR2Threshold_nonneg : 0 ≤ clumpR2Threshold
  clumpR2Threshold_lt_one : clumpR2Threshold < 1
  clumpWindowBp : ℕ
  causalLocusCount : ℕ
  causalLocusCount_pos : 0 < causalLocusCount
  heritability : ℝ
  heritability_pos : 0 < heritability
  heritability_lt_one : heritability < 1
  prevalence : ℝ
  prevalence_pos : 0 < prevalence
  prevalence_lt_one : prevalence < 1
  cohortSize : Fin demeCount → ℕ
  cohortSize_pos : ∀ deme, 0 < cohortSize deme

/-- Exactly the arguments the proposed endpoint law is allowed to inspect. -/
structure VisiblePipelineInput (demeCount : ℕ) where
  demography : PipelineDemographicHistory demeCount
  studyDesign : PipelineStudyDesign demeCount

/-- Haploid count corresponding to the diploid GWAS cohort.

Empirical status: NOT AN EMPIRICAL CLAIM -- the diploid-to-haploid factor of two, a ploidy
convention and not a population assertion. -/
def PipelineStudyDesign.gwasHaplotypeCount {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : ℕ :=
  2 * design.gwasSampleSize

/-- A positive diploid GWAS cohort contains at least one haplotype pair. -/
theorem PipelineStudyDesign.two_le_gwasHaplotypeCount {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : 2 ≤ design.gwasHaplotypeCount := by
  unfold PipelineStudyDesign.gwasHaplotypeCount
  have := design.gwasSampleSize_pos
  omega

/-- Haploid count corresponding to one diploid evaluation cohort.

Empirical status: NOT AN EMPIRICAL CLAIM -- the same ploidy convention as
`gwasHaplotypeCount`. -/
def PipelineStudyDesign.evaluationHaplotypeCount {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) (deme : Fin demeCount) : ℕ :=
  2 * design.cohortSize deme

/-- Every positive diploid evaluation cohort contains at least one haplotype pair. -/
theorem PipelineStudyDesign.two_le_evaluationHaplotypeCount {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) (deme : Fin demeCount) :
    2 ≤ design.evaluationHaplotypeCount deme := by
  unfold PipelineStudyDesign.evaluationHaplotypeCount
  have := design.cohortSize_pos deme
  omega

/-- The pooled evaluation cohort is concatenation of the deme cohorts.  Its size is derived,
not an independently supplied constant that could disagree with the evaluator. -/
def PipelineStudyDesign.pooledCohortSize {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : ℕ :=
  ∑ deme, design.cohortSize deme

/-- Concatenating positive deme cohorts produces a nonempty pooled cohort. -/
theorem PipelineStudyDesign.pooledCohortSize_pos {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : 0 < design.pooledCohortSize := by
  have hle : design.cohortSize design.gwasDeme ≤ design.pooledCohortSize := by
    unfold PipelineStudyDesign.pooledCohortSize
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ design.gwasDeme)
  exact lt_of_lt_of_le (design.cohortSize_pos design.gwasDeme) hle

/-- Haplotype layout used by the visible contract's pooled marker ascertainment.  It is
derived from the named per-deme cohort sizes rather than introduced as another free panel. -/
def PipelineStudyDesign.panelAscertainmentHaplotypeCount {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : Fin demeCount → ℕ :=
  design.evaluationHaplotypeCount

/-- Every deme contributes a positive haplotype pair to pooled marker ascertainment. -/
theorem PipelineStudyDesign.two_le_panelAscertainmentHaplotypeCount {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) (deme : Fin demeCount) :
    2 ≤ design.panelAscertainmentHaplotypeCount deme :=
  design.two_le_evaluationHaplotypeCount deme

/-- Exact arbitrary-order joint frequency moment in the visible contract's causal-marker
reservoir, conditional on the pooled one-percent MAF event.  In particular, exponents through
degree four feed the ascertained variance and finite-panel Jensen laws. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantMoment
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (exponent : Fin demeCount → ℕ) : Option ℝ :=
  input.demography.momentGivenPooledMAF
    input.studyDesign.panelAscertainmentHaplotypeCount gnomonCausalMAFThreshold exponent

/-- One-deme marginal moment in the pooled common-variant reservoir. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantAlleleMoment
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (deme : Fin demeCount) (order : ℕ) : Option ℝ :=
  input.pooledCommonVariantMoment (Coalescent.oneDemeExponent deme order)

/-- Two-deme joint moment in the pooled common-variant reservoir.  This single definition
supplies every degree-two through degree-four cross-deme coordinate required by the
drift-heterogeneity law. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantPairMoment
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (first second : Fin demeCount) (firstOrder secondOrder : ℕ) : Option ℝ :=
  input.pooledCommonVariantMoment
    (Coalescent.pairExponent first second firstOrder secondOrder)

/-- Exact common-variant heterozygosity in one deme after the pooled sample-MAF event. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantHeterozygosity
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (deme : Fin demeCount) : Option ℝ :=
  (input.pooledCommonVariantAlleleMoment deme 1).bind fun first ↦
    (input.pooledCommonVariantAlleleMoment deme 2).map fun second ↦
      2 * (first - second)

/-- Exact fourth-order product of per-locus heterozygosities in two demes after pooled-MAF
ascertainment:

`E[H_i H_j | A] = 4(E[p_i p_j|A] - E[p_i² p_j|A]
                         - E[p_i p_j²|A] + E[p_i² p_j²|A])`.

At `i = j` this is the heterozygosity second moment used in the ascertained `CV²`; off the
diagonal it is the cross-deme moment used in the finite-panel correlation correction. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantHeterozygosityProduct
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (first second : Fin demeCount) : Option ℝ :=
  (input.pooledCommonVariantPairMoment first second 1 1).bind fun moment11 ↦
    (input.pooledCommonVariantPairMoment first second 2 1).bind fun moment21 ↦
      (input.pooledCommonVariantPairMoment first second 1 2).bind fun moment12 ↦
        (input.pooledCommonVariantPairMoment first second 2 2).map fun moment22 ↦
          4 * (moment11 - moment21 - moment12 + moment22)

/-- Exact ascertained per-locus heterozygosity coefficient of variation squared,
`E[H_d²|A] / E[H_d|A]² - 1`.  A zero conditional mean has no normalized scatter and is
reported as `none`. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantHeterozygosityCV2
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (deme : Fin demeCount) : Option ℝ :=
  (input.pooledCommonVariantHeterozygosity deme).bind fun mean ↦
    (input.pooledCommonVariantHeterozygosityProduct deme deme).bind fun secondMoment ↦
      if mean ≠ 0 then some (secondMoment / mean ^ 2 - 1) else none

/-- Exact excess cross-deme heterozygosity product,
`E[H_i H_j|A] / (E[H_i|A] E[H_j|A]) - 1`.  This is the `rho_ij` coordinate in the
finite-panel Jensen law, derived from degree-four pooled-ascertained moments rather than
fitted from portability measurements. -/
noncomputable def VisiblePipelineInput.pooledCommonVariantHeterozygosityExcessCorrelation
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (first second : Fin demeCount) : Option ℝ :=
  (input.pooledCommonVariantHeterozygosity first).bind fun firstMean ↦
    (input.pooledCommonVariantHeterozygosity second).bind fun secondMean ↦
      (input.pooledCommonVariantHeterozygosityProduct first second).bind fun productMoment ↦
        if firstMean * secondMean ≠ 0 then
          some (productMoment / (firstMean * secondMean) - 1)
        else none

/-- Exact ascertained-tag erosion at the study's actual source and target cohort sizes.  The
result is `none` exactly when the source-polymorphic conditioning event has zero mass. -/
noncomputable def VisiblePipelineInput.ascertainedTagErosion
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (target : Fin demeCount) : Option ℝ :=
  input.demography.targetErosion input.studyDesign.gwasDeme target
    input.studyDesign.gwasHaplotypeCount
    (input.studyDesign.evaluationHaplotypeCount target)

/-- Exact target frequency factorial moment after source-polymorphism ascertainment at the
study's actual cohort sizes.  Orders one and two supply the tag-spectrum coordinates used by
heterozygosity and genotype variance. -/
noncomputable def VisiblePipelineInput.sourcePolymorphicTargetFactorialMoment
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (target : Fin demeCount) (order : ℕ) : Option ℝ :=
  input.demography.sourcePolymorphicTargetFactorialMoment input.studyDesign.gwasDeme target
    input.studyDesign.gwasHaplotypeCount
    (input.studyDesign.evaluationHaplotypeCount target) order

/-- Exact source-polymorphism-conditioned target heterozygosity for every deme.  Unlike
segregation retention, this retains the entire interior count spectrum and therefore
determines the marginal tag-genotype variance scale required upstream of a `DemeScoreLaw`. -/
noncomputable def VisiblePipelineInput.sourcePolymorphicTargetHeterozygosity
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (target : Fin demeCount) : Option ℝ :=
  input.demography.sourcePolymorphicTargetHeterozygosity input.studyDesign.gwasDeme target
    input.studyDesign.gwasHaplotypeCount
    (input.studyDesign.evaluationHaplotypeCount target)

/-- At every visible target deme, source-polymorphism-conditioned heterozygosity is exactly
`2(m₁-m₂)` for the first two conditional factorial moments.  The cohort-size domain is
discharged from the study design's positive diploid cohort field. -/
theorem VisiblePipelineInput.sourcePolymorphicTargetHeterozygosity_eq_factorialMoments
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (target : Fin demeCount) :
    input.sourcePolymorphicTargetHeterozygosity target =
      (input.sourcePolymorphicTargetFactorialMoment target 1).bind fun first ↦
        (input.sourcePolymorphicTargetFactorialMoment target 2).map fun second ↦
          2 * (first - second) := by
  exact Coalescent.targetHeterozygosityGivenSourcePolymorphic_eq_factorialMoments
    (input.demography.jointSampleCount input.studyDesign.gwasDeme target
      input.studyDesign.gwasHaplotypeCount
      (input.studyDesign.evaluationHaplotypeCount target))
    input.studyDesign.gwasHaplotypeCount
    (input.studyDesign.evaluationHaplotypeCount target)
    (input.studyDesign.two_le_evaluationHaplotypeCount target)

/-- Migration-restored linkage factor on its mathematical correlation domain.  It is the
squared normalized cross-deme `DD` read after the complete demographic operator product.

Empirical status: DERIVED -- `accuracyLinkageFactor_eq` proves this quotient is the squared
normalized correlation, so this inherits the status of `StructuredPresentDay`'s
`accuracyLinkageFactor` applied to the composed history; no battery has compared the composed
factor against simulation yet. -/
noncomputable def VisiblePipelineInput.accuracyLinkageFactorOn
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (separation : Coalescent.MarkerSeparationBp) (target : Fin demeCount)
    (domain : input.demography.twoLocusMoments.LDNormalizationDomain separation
      input.studyDesign.gwasDeme target) : ℝ :=
  input.demography.twoLocusMoments.accuracyLinkageFactor separation
    input.studyDesign.gwasDeme target domain

/-- The visible linkage factor is literally the squared `DD` correlation; migration
restoration is already inside the history generator and is not an added fitted term. -/
theorem VisiblePipelineInput.accuracyLinkageFactor_eq
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (separation : Coalescent.MarkerSeparationBp) (target : Fin demeCount)
    (domain : input.demography.twoLocusMoments.LDNormalizationDomain separation
      input.studyDesign.gwasDeme target) :
    input.accuracyLinkageFactorOn separation target domain =
      (input.demography.twoLocusMoments.crossDemeLDCorrelation separation
        input.studyDesign.gwasDeme target domain) ^ 2 :=
  input.demography.twoLocusMoments.accuracyLinkageFactor_eq_correlation_sq
    separation input.studyDesign.gwasDeme target domain

/-- Exact input-only linkage readout.  The normalization domain is decided from the composed
moments rather than supplied as an extra argument.  `none` covers a zero within-deme `DD`
denominator; failure of a separate Cauchy--Schwarz certificate no longer suppresses an
otherwise exactly evaluable operator quotient. -/
noncomputable def VisiblePipelineInput.accuracyLinkageFactor
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (separation : Coalescent.MarkerSeparationBp) (target : Fin demeCount) : Option ℝ := by
  classical
  exact if domain : input.demography.twoLocusMoments.LDNormalizationDomain separation
        input.studyDesign.gwasDeme target then
      some (input.accuracyLinkageFactorOn separation target domain)
    else none

/-- On a certified nondegenerate moment pair, the input-only readout returns exactly the
squared normalized `DD` correlation. -/
theorem VisiblePipelineInput.accuracyLinkageFactor_eq_some
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (separation : Coalescent.MarkerSeparationBp) (target : Fin demeCount)
    (domain : input.demography.twoLocusMoments.LDNormalizationDomain separation
      input.studyDesign.gwasDeme target) :
    input.accuracyLinkageFactor separation target =
      some ((input.demography.twoLocusMoments.crossDemeLDCorrelation separation
        input.studyDesign.gwasDeme target domain) ^ 2) := by
  classical
  simp [VisiblePipelineInput.accuracyLinkageFactor, domain,
    VisiblePipelineInput.accuracyLinkageFactorOn,
    Coalescent.DemographicTwoLocusMoments.accuracyLinkageFactor_eq_correlation_sq]

/-- A defined input-only linkage factor with a realizable covariance certificate lies in
`[0,1]`.  Evaluation itself requires only positive normalization denominators. -/
theorem VisiblePipelineInput.accuracyLinkageFactor_mem_unitInterval
    {demeCount : ℕ} (input : VisiblePipelineInput demeCount)
    (separation : Coalescent.MarkerSeparationBp) (target : Fin demeCount)
    (domain : input.demography.twoLocusMoments.LDPairDomain separation
      input.studyDesign.gwasDeme target)
    {value : ℝ} (hvalue : input.accuracyLinkageFactor separation target = some value) :
    value ∈ Set.Icc (0 : ℝ) 1 := by
  rw [input.accuracyLinkageFactor_eq_some separation target
    domain.toLDNormalizationDomain] at hvalue
  have heq := Option.some.inj hvalue
  subst value
  rw [← input.accuracyLinkageFactor_eq separation target
    domain.toLDNormalizationDomain]
  exact ⟨input.demography.twoLocusMoments.accuracyLinkageFactor_nonneg
      separation input.studyDesign.gwasDeme target domain.toLDNormalizationDomain,
    input.demography.twoLocusMoments.accuracyLinkageFactor_le_one
      separation input.studyDesign.gwasDeme target domain⟩

/-- Expected within-deme heterozygosity from the exact propagated first two moments. -/
noncomputable def PipelineDemographicHistory.withinHeterozygosity
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (deme : Fin demeCount) : ℝ :=
  2 * (history.oneLocusMoment 2 (Coalescent.oneDemeExponent deme 1) -
    history.oneLocusMoment 2 (Coalescent.oneDemeExponent deme 2))

/-- Expected pairwise allelic divergence between two demes. -/
noncomputable def PipelineDemographicHistory.betweenDivergence
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (first second : Fin demeCount) : ℝ :=
  history.oneLocusMoment 2 (Coalescent.oneDemeExponent first 1) +
  history.oneLocusMoment 2 (Coalescent.oneDemeExponent second 1) -
    2 * history.pairMoment 2 first second 1 1

/-- Every nonconstant exponent is read directly from the propagated rectangular moment state;
the separate normalized-zero branch of `oneLocusMoment` is irrelevant on this domain. -/
theorem PipelineDemographicHistory.oneLocusMoment_eq_presentMomentState
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) (K : ℕ)
    (exponent : Fin demeCount → ℕ) (hnonzero : ¬∀ deme, exponent deme = 0) :
    history.oneLocusMoment K exponent =
      Coalescent.manyDemeMomentVectorTable K
        (fun coordinate ↦ history.presentMomentState K (some coordinate)) exponent := by
  simp [PipelineDemographicHistory.oneLocusMoment, hnonzero]

/-- The public marginal divergence readout is exactly the corresponding coordinate of the
degree-two pair-divergence projection matrix. -/
theorem PipelineDemographicHistory.betweenDivergence_eq_pairProjection
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (first second : Fin demeCount) :
    history.betweenDivergence first second =
      (Coalescent.manyDemePairDivergenceProjection demeCount).mulVec
        (history.presentMomentState 2) (some (first, second)) := by
  have hfirst : ¬∀ deme, Coalescent.oneDemeExponent first 1 deme = 0 := by
    intro h
    simpa [Coalescent.oneDemeExponent] using h first
  have hsecond : ¬∀ deme, Coalescent.oneDemeExponent second 1 deme = 0 := by
    intro h
    simpa [Coalescent.oneDemeExponent] using h second
  have hpair : ¬∀ deme, Coalescent.pairExponent first second 1 1 deme = 0 := by
    intro h
    have hvalue := h first
    by_cases hsame : first = second <;>
      simp [Coalescent.pairExponent, hsame] at hvalue
  rw [Coalescent.manyDemePairDivergenceProjection_mulVec]
  simp only [Coalescent.momentPairDivergence]
  unfold PipelineDemographicHistory.betweenDivergence PipelineDemographicHistory.pairMoment
  rw [history.oneLocusMoment_eq_presentMomentState 2 _ hfirst,
    history.oneLocusMoment_eq_presentMomentState 2 _ hsecond,
    history.oneLocusMoment_eq_presentMomentState 2 _ hpair]

/-- Equality proposition between the marginal frequency-divergence coordinate used by finite
ascertainment and the `H` coordinate propagated inside the joint linkage operator.  The
theorem immediately below proves it for every typed visible history. -/
def PipelineDemographicHistory.CommonDiffusionProjection
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) : Prop :=
  ∀ separation first second,
    history.twoLocusMoments.H separation first second =
      history.betweenDivergence first second

/-- The common-diffusion obligation is discharged for every typed visible history.  The proof
starts from the shared ancestral boundary, intertwines both exact matrix exponentials through
every epoch, commutes both projections through every split, and identifies the public
one-locus and two-locus readouts after the terminal epoch. -/
theorem PipelineDemographicHistory.commonDiffusionProjection_exact
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount) :
    history.CommonDiffusionProjection := by
  intro separation first second
  let common := history.presentCommonDiffusionState separation.value separation.value_nonneg
  have hprojection := congrFun common.projection_eq (some (first, second))
  have hmarginal := history.presentCommonDiffusionState_marginal
    separation.value separation.value_nonneg
  have hjoint := history.presentCommonDiffusionState_joint
    separation.value separation.value_nonneg
  calc
    history.twoLocusMoments.H separation first second =
        (history.lowOrderLDHistory separation.value separation.value_nonneg).present
          (some (.H first second)) := rfl
    _ = common.joint (some (.H first second)) := by
      exact congrFun hjoint (some (.H first second)) |>.symm
    _ = (Coalescent.lowOrderLDHProjection demeCount).mulVec common.joint
          (some (first, second)) := by
      rw [Coalescent.lowOrderLDHProjection_mulVec]
      rfl
    _ = (Coalescent.manyDemePairDivergenceProjection demeCount).mulVec common.marginal
          (some (first, second)) := hprojection.symm
    _ = (Coalescent.manyDemePairDivergenceProjection demeCount).mulVec
          (history.presentMomentState 2) (some (first, second)) := by
      rw [hmarginal]
      rfl
    _ = history.betweenDivergence first second :=
      (history.betweenDivergence_eq_pairProjection first second).symm

/-- Domain on which Hudson differentiation is defined. -/
structure PipelineDemographicHistory.HudsonFstDomain
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (first second : Fin demeCount) : Prop where
  betweenDivergence_pos : 0 < history.betweenDivergence first second

/-- Exact Hudson differentiation coordinate from the propagated demographic moments.

Empirical status: DERIVED -- Hudson's ratio-of-averages built from the pipeline's exact
propagated moments, with the between-pair divergence in the denominator; the convention
ledger entry for this declaration records why it is Hudson and not Nei, and the typed
`HudsonFstDomain` hypothesis excludes the zero-divergence pole instead of clamping it. -/
noncomputable def PipelineDemographicHistory.hudsonFst
    {demeCount : ℕ} (history : PipelineDemographicHistory demeCount)
    (first second : Fin demeCount) (_ : history.HudsonFstDomain first second) : ℝ :=
  1 - ((history.withinHeterozygosity first + history.withinHeterozygosity second) / 2) /
    history.betweenDivergence first second

/-- A population coordinate is either one deme or the pooled population. -/
abbrev EvaluatedPopulation (demeCount : ℕ) := Option (Fin demeCount)

/-- Every requested metric and intermediate quantity.  Natural-number coordinates index
ascertained tags; the real coordinate of `liabilityToRisk` is the liability at which risk is
evaluated. -/
inductive PipelineQuantity (demeCount : ℕ) where
  | observedRiskR2 (population : EvaluatedPopulation demeCount)
  | withinDemeAUC (deme : Fin demeCount)
  | pooledAUC
  | calibrationSlope (population : EvaluatedPopulation demeCount)
  | calibrationInTheLarge (population : EvaluatedPopulation demeCount)
  | brierScore (population : EvaluatedPopulation demeCount)
  | ascertainedTagFixation (deme : Fin demeCount) (tag : ℕ)
  | differentiation (first second : Fin demeCount) (tag : ℕ)
  | linkageRetention (deme : Fin demeCount) (firstTag secondTag : ℕ)
  | linkageRestoredByMigration (deme : Fin demeCount) (firstTag secondTag : ℕ)
  | scoreVariance (population : EvaluatedPopulation demeCount)
  | liabilityToRisk (population : EvaluatedPopulation demeCount) (liability : ℝ)

/-- The endpoint report on the unrestricted finite-cohort domain.  `none` is an actual
undefined metric, not a numeric default; `some value` carries every defined biological
intermediate and evaluation coordinate. -/
abbrev PipelineOutput (demeCount : ℕ) := PipelineQuantity demeCount → Option ℝ

/-- The type of a candidate exact expected semantic map.  `Completion` means only residual
state not probabilistically determined by the visible input; simulator draws already integrated
into the expectation do not belong there. -/
abbrev PipelineCompletionLaw (demeCount : ℕ) (Completion : Type*) :=
  Core.CompletionLaw (VisiblePipelineInput demeCount) Completion (PipelineQuantity demeCount)
    (Option ℝ)

/-- The proposition that the actual completed semantic map factors exactly through the visible
endpoint input. -/
abbrev HasExactPipelineReadout {demeCount : ℕ} {Completion : Type*}
    (law : PipelineCompletionLaw demeCount Completion) : Prop :=
  Core.HasExactReadout law

/-- Real-valued completion laws remain available for coordinates restricted to a domain where
they are defined; only these ordered scalar fibers admit the core sharp-envelope theory. -/
abbrev NumericPipelineCompletionLaw (demeCount : ℕ) (Completion : Type*) :=
  Core.CompletionLaw (VisiblePipelineInput demeCount) Completion (PipelineQuantity demeCount) ℝ

/-- Sharp numeric fibers are deliberately separate from the unrestricted partial endpoint. -/
abbrev PipelineSharpEnvelope {demeCount : ℕ} {Completion : Type*}
    (law : NumericPipelineCompletionLaw demeCount Completion) :=
  Core.SharpFiberEnvelope law

/-! ## Marginalizing simulator-generated state

The following is the positive identification result relevant to gnomon-style semantics.
Random causal positions, effects, haplotypes, GWAS noise, and cohort draws do not create a
completion fiber when their joint distribution is fixed by the visible input.  They form one
sample space and are integrated once.  What remains open is constructing this kernel and
proving that its realized coordinates agree with the actual pipeline—not the marginalization
step itself.
-/

/-- A probabilistic pipeline whose entire draw law is determined by the visible endpoint
input.  `realizedValue` may include every layer of simulator randomness simultaneously. -/
structure PipelineRandomSemantics (demeCount : ℕ) (Sample : Type*)
    [MeasurableSpace Sample] where
  drawLaw : VisiblePipelineInput demeCount → Measure Sample
  drawLaw_probability : ∀ input, IsProbabilityMeasure (drawLaw input)
  realizedValue : VisiblePipelineInput demeCount → Sample → PipelineQuantity demeCount → ℝ
  integrable : ∀ input coordinate,
    Integrable (fun sample ↦ realizedValue input sample coordinate) (drawLaw input)

/-- The exact expected report after all input-determined simulator draws are marginalized. -/
noncomputable def PipelineRandomSemantics.expectedOutput
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PipelineRandomSemantics demeCount Sample) :
    VisiblePipelineInput demeCount → PipelineOutput demeCount :=
  fun input coordinate ↦
    some (∫ sample, semantics.realizedValue input sample coordinate ∂semantics.drawLaw input)

/-- View the marginalized semantics as a completion law with no residual hidden state. -/
noncomputable def PipelineRandomSemantics.expectedCompletionLaw
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PipelineRandomSemantics demeCount Sample) :
    PipelineCompletionLaw demeCount PUnit where
  value := fun input _completion coordinate ↦ semantics.expectedOutput input coordinate

/-- Input-determined random draws integrate out exactly: the expected endpoint has an exact
visible-input readout.  This theorem does not supply the simulator kernel or any biological
coordinate formula; those are the remaining model-specific construction obligations. -/
theorem PipelineRandomSemantics.hasExactExpectedReadout
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PipelineRandomSemantics demeCount Sample) :
    HasExactPipelineReadout semantics.expectedCompletionLaw := by
  exact ⟨semantics.expectedOutput, fun _input _completion _coordinate ↦ rfl⟩

/-! ### Undefined finite-sample branches -/

/-- A pipeline semantics whose realized metric may be undefined.  The value outside the
defined event is deliberately ignored; carrying the event separately avoids smuggling a
numeric sentinel into an expectation. -/
structure PartialPipelineRandomSemantics (demeCount : ℕ) (Sample : Type*)
    [MeasurableSpace Sample] where
  drawLaw : VisiblePipelineInput demeCount → Measure Sample
  drawLaw_probability : ∀ input, IsProbabilityMeasure (drawLaw input)
  defined : VisiblePipelineInput demeCount → Sample → PipelineQuantity demeCount → Bool
  defined_measurable : ∀ input coordinate,
    MeasurableSet {sample | defined input sample coordinate = true}
  realizedValue : VisiblePipelineInput demeCount → Sample → PipelineQuantity demeCount → ℝ
  definedValue_integrable : ∀ input coordinate,
    Integrable (fun sample ↦ if defined input sample coordinate then
      realizedValue input sample coordinate else 0) (drawLaw input)

/-- Probability that one finite pipeline realization defines a requested metric. -/
noncomputable def PartialPipelineRandomSemantics.definedProbability
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PartialPipelineRandomSemantics demeCount Sample)
    (input : VisiblePipelineInput demeCount) (coordinate : PipelineQuantity demeCount) : ℝ :=
  (semantics.drawLaw input
    {sample | semantics.defined input sample coordinate = true}).toReal

/-- Exact conditional mean over the realizations on which the pipeline reports the metric.
This is the population target of a skip-undefined Monte Carlo average.  If the metric is never
defined, the result remains `none`. -/
noncomputable def PartialPipelineRandomSemantics.expectedOutput
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PartialPipelineRandomSemantics demeCount Sample) :
    VisiblePipelineInput demeCount → PipelineOutput demeCount :=
  fun input coordinate ↦
    let mass := semantics.definedProbability input coordinate
    if mass = 0 then none else
      some ((∫ sample, (if semantics.defined input sample coordinate then
        semantics.realizedValue input sample coordinate else 0) ∂semantics.drawLaw input) / mass)

/-- The partial conditional expectation has no residual completion coordinate once the entire
input-determined draw law is integrated. -/
noncomputable def PartialPipelineRandomSemantics.expectedCompletionLaw
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PartialPipelineRandomSemantics demeCount Sample) :
    PipelineCompletionLaw demeCount PUnit where
  value := fun input _completion coordinate ↦ semantics.expectedOutput input coordinate

/-- Exact identification still holds for partial values: simulator randomness determines the
definedness probability and conditional mean, rather than becoming a completion fiber. -/
theorem PartialPipelineRandomSemantics.hasExactExpectedReadout
    {demeCount : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (semantics : PartialPipelineRandomSemantics demeCount Sample) :
    HasExactPipelineReadout semantics.expectedCompletionLaw := by
  exact ⟨semantics.expectedOutput, fun _input _completion _coordinate ↦ rfl⟩

/-! ## B1. The P+T selection law -/

/-- A real quantity known to be strictly positive. -/
structure PositiveScale where
  value : ℝ
  value_pos : 0 < value

/-- Environmental variance implied by a unit-variance genetic liability and the visible
narrow-sense heritability: `h² = 1 / (1 + Vₑ)`. -/
noncomputable def PipelineStudyDesign.residualVariance {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : ℝ :=
  (1 - design.heritability) / design.heritability

/-- The visible heritability keeps its derived residual variance strictly positive. -/
theorem PipelineStudyDesign.residualVariance_pos {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : 0 < design.residualVariance :=
  div_pos (sub_pos.mpr design.heritability_lt_one) design.heritability_pos

/-- Environmental standard deviation derived from the visible heritability, not supplied as
a second phenotype parameter. -/
noncomputable def PipelineStudyDesign.residualSD {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : PositiveScale where
  value := Real.sqrt design.residualVariance
  value_pos := Real.sqrt_pos.2 design.residualVariance_pos

/-- A realized total-liability panel with exactly the visible per-deme cohort layout.

The entries include every phenotype component that shifts liability before the common
environmental residual is added: genetic score, ancestry baseline, and any other rung chosen
by the executable phenotype protocol.  Keeping this type total-liability-valued prevents the
downstream risk law from silently assuming the genetic-only phenotype rung. -/
structure FiniteLiabilityPanel {demeCount : ℕ} (design : PipelineStudyDesign demeCount) where
  liability : ∀ deme, Fin (design.cohortSize deme) → ℝ

/-- Arithmetic mean total liability in one visible deme. -/
noncomputable def FiniteLiabilityPanel.demeMean
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (deme : Fin demeCount) : ℝ :=
  (∑ individual, panel.liability deme individual) / design.cohortSize deme

/-- Conditional event risk under a normal environmental residual and a proposed global
liability intercept. -/
noncomputable def FiniteLiabilityPanel.riskAtIntercept
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (intercept : ℝ)
    (deme : Fin demeCount) (individual : Fin (design.cohortSize deme)) : ℝ :=
  Foundations.Phi
    ((intercept + panel.liability deme individual) / design.residualSD.value)

/-- Cohort-size-weighted mean risk across the concatenated population. -/
noncomputable def FiniteLiabilityPanel.pooledMeanRiskAtIntercept
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (intercept : ℝ) : ℝ :=
  (∑ deme, ∑ individual, panel.riskAtIntercept intercept deme individual) /
    design.pooledCohortSize

/-- Exact domain of the global prevalence intercept.  The proof field contains no fitted
constant; it certifies the unique root of the displayed, exactly evaluable finite sum. -/
structure FiniteLiabilityPanel.PrevalenceInterceptDomain
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) : Prop where
  existsUniqueRoot : ∃! intercept : ℝ,
    panel.pooledMeanRiskAtIntercept intercept = design.prevalence

/-- A finite, exactly evaluable common bound on every absolute total liability in the
visible evaluation panel. -/
noncomputable def FiniteLiabilityPanel.liabilityAbsSum
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) : ℝ :=
  ∑ deme, ∑ individual, |panel.liability deme individual|

/-- Every individual liability is bounded in absolute value by the finite panel sum. -/
theorem FiniteLiabilityPanel.abs_liability_le_liabilityAbsSum
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (deme : Fin demeCount)
    (individual : Fin (design.cohortSize deme)) :
    |panel.liability deme individual| ≤ panel.liabilityAbsSum := by
  unfold FiniteLiabilityPanel.liabilityAbsSum
  have hinner :
      |panel.liability deme individual| ≤
        ∑ other, |panel.liability deme other| :=
    Finset.single_le_sum (fun other _ ↦ abs_nonneg (panel.liability deme other))
      (Finset.mem_univ individual)
  have houter :
      (∑ other, |panel.liability deme other|) ≤
        ∑ otherDeme, ∑ otherIndividual,
          |panel.liability otherDeme otherIndividual| := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin demeCount)))
      (f := fun otherDeme ↦ ∑ otherIndividual,
        |panel.liability otherDeme otherIndividual|)
    · intro otherDeme _
      exact Finset.sum_nonneg fun otherIndividual _ ↦
        abs_nonneg (panel.liability otherDeme otherIndividual)
    · exact Finset.mem_univ deme
  exact hinner.trans houter

/-- The global prevalence intercept exists uniquely for every finite visible panel.  The
proof uses explicit brackets

`sigma_e * Phi⁻¹(K) ± sum |L_i|`.

At the lower bracket every individual probit risk is at most `K`; at the upper bracket every
risk is at least `K`.  A finite sum of continuous strictly increasing Gaussian CDFs is itself
continuous and strictly increasing, so the intermediate value is the unique root.  Thus the
domain is derived from the visible prevalence and panel rather than supplied by a caller. -/
theorem FiniteLiabilityPanel.hasPrevalenceInterceptDomain
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) : panel.PrevalenceInterceptDomain := by
  classical
  let z := Function.invFun Foundations.Phi design.prevalence
  let lower := design.residualSD.value * z - panel.liabilityAbsSum
  let upper := design.residualSD.value * z + panel.liabilityAbsSum
  have hPhiZ : Foundations.Phi z = design.prevalence := by
    exact Foundations.Phi_invFun_eq design.prevalence design.prevalence_pos
      design.prevalence_lt_one
  have hab : lower ≤ upper := by
    dsimp [lower, upper]
    have hsum : 0 ≤ panel.liabilityAbsSum := by
      unfold FiniteLiabilityPanel.liabilityAbsSum
      positivity
    linarith
  have hriskContinuous : ∀ deme individual,
      Continuous (fun intercept ↦ panel.riskAtIntercept intercept deme individual) := by
    intro deme individual
    unfold FiniteLiabilityPanel.riskAtIntercept
    exact Foundations.continuous_Phi.comp
      ((continuous_id.add continuous_const).div_const design.residualSD.value)
  have hcontinuous : Continuous panel.pooledMeanRiskAtIntercept := by
    unfold FiniteLiabilityPanel.pooledMeanRiskAtIntercept
    exact (continuous_finset_sum _ fun deme _ ↦
      continuous_finset_sum _ fun individual _ ↦
        hriskContinuous deme individual).div_const design.pooledCohortSize
  have hriskStrict : ∀ deme individual,
      StrictMono (fun intercept ↦ panel.riskAtIntercept intercept deme individual) := by
    intro deme individual first second hlt
    apply Foundations.strictMono_Phi
    exact div_lt_div_of_pos_right (add_lt_add_right hlt _)
      design.residualSD.value_pos
  have hstrict : StrictMono panel.pooledMeanRiskAtIntercept := by
    intro first second hlt
    unfold FiniteLiabilityPanel.pooledMeanRiskAtIntercept
    have hsums :
        (∑ deme, ∑ individual, panel.riskAtIntercept first deme individual) <
          ∑ deme, ∑ individual, panel.riskAtIntercept second deme individual := by
      apply Finset.sum_lt_sum
      · intro deme _
        exact Finset.sum_le_sum fun individual _ ↦
          (hriskStrict deme individual hlt).le
      · refine ⟨design.gwasDeme, Finset.mem_univ _, ?_⟩
        apply Finset.sum_lt_sum
        · intro individual _
          exact (hriskStrict design.gwasDeme individual hlt).le
        · let witness : Fin (design.cohortSize design.gwasDeme) :=
            ⟨0, design.cohortSize_pos design.gwasDeme⟩
          exact ⟨witness, Finset.mem_univ _, hriskStrict design.gwasDeme witness hlt⟩
    exact div_lt_div_of_pos_right hsums
      (Nat.cast_pos.mpr design.pooledCohortSize_pos)
  have hconstantSum :
      (∑ deme, ∑ _individual : Fin (design.cohortSize deme), design.prevalence) =
        (design.pooledCohortSize : ℝ) * design.prevalence := by
    simp [PipelineStudyDesign.pooledCohortSize, Finset.sum_mul]
  have hlower : panel.pooledMeanRiskAtIntercept lower ≤ design.prevalence := by
    have hterm : ∀ deme individual,
        panel.riskAtIntercept lower deme individual ≤ design.prevalence := by
      intro deme individual
      rw [← hPhiZ]
      apply Foundations.Phi_monotone
      apply (div_le_iff₀ design.residualSD.value_pos).2
      have habsolute := panel.abs_liability_le_liabilityAbsSum deme individual
      dsimp [lower]
      linarith [le_abs_self (panel.liability deme individual)]
    unfold FiniteLiabilityPanel.pooledMeanRiskAtIntercept
    rw [div_le_iff₀ (Nat.cast_pos.mpr design.pooledCohortSize_pos)]
    calc
      (∑ deme, ∑ individual, panel.riskAtIntercept lower deme individual) ≤
          ∑ deme, ∑ _individual : Fin (design.cohortSize deme), design.prevalence :=
        Finset.sum_le_sum fun deme _ ↦ Finset.sum_le_sum fun individual _ ↦
          hterm deme individual
      _ = (design.pooledCohortSize : ℝ) * design.prevalence := hconstantSum
      _ = design.prevalence * design.pooledCohortSize := by ring
  have hupper : design.prevalence ≤ panel.pooledMeanRiskAtIntercept upper := by
    have hterm : ∀ deme individual,
        design.prevalence ≤ panel.riskAtIntercept upper deme individual := by
      intro deme individual
      rw [← hPhiZ]
      apply Foundations.Phi_monotone
      apply (le_div_iff₀ design.residualSD.value_pos).2
      have habsolute := panel.abs_liability_le_liabilityAbsSum deme individual
      dsimp [upper]
      linarith [neg_le_of_abs_le habsolute]
    unfold FiniteLiabilityPanel.pooledMeanRiskAtIntercept
    rw [le_div_iff₀ (Nat.cast_pos.mpr design.pooledCohortSize_pos)]
    calc
      design.prevalence * design.pooledCohortSize =
          (design.pooledCohortSize : ℝ) * design.prevalence := by ring
      _ = ∑ deme, ∑ _individual : Fin (design.cohortSize deme), design.prevalence :=
        hconstantSum.symm
      _ ≤ ∑ deme, ∑ individual, panel.riskAtIntercept upper deme individual :=
        Finset.sum_le_sum fun deme _ ↦ Finset.sum_le_sum fun individual _ ↦
          hterm deme individual
  obtain ⟨root, _, hroot⟩ :=
    intermediate_value_Icc hab hcontinuous.continuousOn ⟨hlower, hupper⟩
  refine ⟨⟨root, hroot, ?_⟩⟩
  intro other hother
  exact hstrict.injective (hother.trans hroot.symm)

/-- The exact global intercept selected by the visible prevalence equation.

Empirical status: DERIVED -- `hasPrevalenceInterceptDomain` proves the unique root exists for
every finite visible panel, and `prevalenceIntercept_spec` proves it attains the requested
pooled prevalence; no caller supplies domain evidence or a fitted constant. -/
noncomputable def FiniteLiabilityPanel.prevalenceIntercept
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) : ℝ :=
  panel.hasPrevalenceInterceptDomain.existsUniqueRoot.exists.choose

/-- The selected intercept attains the requested pooled prevalence exactly. -/
theorem FiniteLiabilityPanel.prevalenceIntercept_spec
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) :
    panel.pooledMeanRiskAtIntercept panel.prevalenceIntercept = design.prevalence :=
  panel.hasPrevalenceInterceptDomain.existsUniqueRoot.exists.choose_spec

/-- Exact individual liability-to-risk transformation after solving the global intercept. -/
noncomputable def FiniteLiabilityPanel.risk
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (deme : Fin demeCount)
    (individual : Fin (design.cohortSize deme)) : ℝ :=
  panel.riskAtIntercept panel.prevalenceIntercept deme individual

/-- The same globally calibrated liability-to-risk curve evaluated at an arbitrary liability,
which is the requested `liabilityToRisk` intermediate rather than an individual lookup. -/
noncomputable def FiniteLiabilityPanel.riskForLiability
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (liability : ℝ) : ℝ :=
  Foundations.Phi
    ((panel.prevalenceIntercept + liability) / design.residualSD.value)

/-- Individual risk is the common liability-to-risk curve evaluated at that individual's
derived genetic liability. -/
theorem FiniteLiabilityPanel.risk_eq_riskForLiability
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (deme : Fin demeCount)
    (individual : Fin (design.cohortSize deme)) :
    panel.risk deme individual =
      panel.riskForLiability (panel.liability deme individual) := rfl

/-- Every transformed risk is strictly inside the Bernoulli probability interval. -/
theorem FiniteLiabilityPanel.risk_mem_unitInterval
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (deme : Fin demeCount)
    (individual : Fin (design.cohortSize deme)) :
    0 < panel.risk deme individual ∧ panel.risk deme individual < 1 := by
  exact ⟨Foundations.Phi_pos _, Foundations.Phi_lt_one _⟩

/-- Add one common liability offset to every individual.  This changes the arbitrary origin
of the liability scale but no relative liability. -/
noncomputable def FiniteLiabilityPanel.shift
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (offset : ℝ) : FiniteLiabilityPanel design where
  liability := fun deme individual ↦ panel.liability deme individual + offset

/-- A common liability offset is absorbed exactly by the derived global intercept. -/
theorem FiniteLiabilityPanel.prevalenceIntercept_shift
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (offset : ℝ) :
    (panel.shift offset).prevalenceIntercept = panel.prevalenceIntercept - offset := by
  apply (panel.shift offset).hasPrevalenceInterceptDomain.existsUniqueRoot.unique
  · exact (panel.shift offset).prevalenceIntercept_spec
  · rw [← panel.prevalenceIntercept_spec]
    unfold FiniteLiabilityPanel.pooledMeanRiskAtIntercept
      FiniteLiabilityPanel.riskAtIntercept FiniteLiabilityPanel.shift
    apply congrArg (fun total : ℝ ↦ total / design.pooledCohortSize)
    apply Finset.sum_congr rfl
    intro deme _
    apply Finset.sum_congr rfl
    intro individual _
    apply congrArg Foundations.Phi
    apply congrArg (fun numerator : ℝ ↦ numerator / design.residualSD.value)
    ring

/-- Consequently every individual true risk is invariant to a common liability offset. -/
theorem FiniteLiabilityPanel.risk_shift
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (panel : FiniteLiabilityPanel design) (offset : ℝ) (deme : Fin demeCount)
    (individual : Fin (design.cohortSize deme)) :
    (panel.shift offset).risk deme individual = panel.risk deme individual := by
  unfold FiniteLiabilityPanel.risk
  rw [panel.prevalenceIntercept_shift]
  unfold FiniteLiabilityPanel.riskAtIntercept FiniteLiabilityPanel.shift
  apply congrArg Foundations.Phi
  apply congrArg (fun numerator : ℝ ↦ numerator / design.residualSD.value)
  ring

/-- Exact identifiability quotient for the finite liability-to-risk transformation: two
panels have the same individual risk vector if and only if their liabilities differ by one
common additive constant.  Thus a global intercept convention is harmless, whereas the
nonconstant per-deme shifts distinguishing gnomon's phenotype rungs are not integrated-away
simulator noise. -/
theorem FiniteLiabilityPanel.risk_eq_iff_liability_eq_up_to_common_shift
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (first second : FiniteLiabilityPanel design) :
    (∀ deme individual, first.risk deme individual = second.risk deme individual) ↔
      ∃ offset : ℝ, ∀ deme individual,
        second.liability deme individual = first.liability deme individual + offset := by
  constructor
  · intro hrisk
    refine ⟨first.prevalenceIntercept - second.prevalenceIntercept, ?_⟩
    intro deme individual
    have harguments := Foundations.strictMono_Phi.injective (hrisk deme individual)
    unfold FiniteLiabilityPanel.risk at harguments
    field_simp [ne_of_gt design.residualSD.value_pos] at harguments
    linarith
  · rintro ⟨offset, hliability⟩
    have hpanel : second = first.shift offset := by
      cases first with
      | mk firstLiability =>
        cases second with
        | mk secondLiability =>
          congr
          funext deme individual
          exact hliability deme individual
    subst second
    exact fun deme individual ↦ (first.risk_shift offset deme individual).symm

/-- Any liability difference outside the common-shift quotient changes at least one exact
individual risk after global prevalence calibration. -/
theorem FiniteLiabilityPanel.exists_risk_ne_of_not_common_shift
    {demeCount : ℕ} {design : PipelineStudyDesign demeCount}
    (first second : FiniteLiabilityPanel design)
    (hshift : ¬ ∃ offset : ℝ, ∀ deme individual,
      second.liability deme individual = first.liability deme individual + offset) :
    ∃ deme, ∃ individual,
      first.risk deme individual ≠ second.risk deme individual := by
  by_contra hsame
  push_neg at hsame
  exact hshift ((first.risk_eq_iff_liability_eq_up_to_common_shift second).mp hsame)

/-- A probability strictly inside the unit interval. -/
structure InteriorProbability where
  value : ℝ
  value_pos : 0 < value
  value_lt_one : value < 1

/-- Parameters of a P+T construction.  They are supplied by a study instance, never selected
inside the law. -/
structure PTParameters where
  clumpR2Cutoff : ℝ
  clumpWindowBp : ℕ
  discoverySampleSize : ℕ
  clumpR2Cutoff_nonneg : 0 ≤ clumpR2Cutoff
  clumpR2Cutoff_lt_one : clumpR2Cutoff < 1
  discoverySampleSize_pos : 0 < discoverySampleSize

/-- P+T parameters projected from the visible study design with no duplicated constants. -/
def PipelineStudyDesign.ptParameters {demeCount : ℕ}
    (design : PipelineStudyDesign demeCount) : PTParameters where
  clumpR2Cutoff := design.clumpR2Threshold
  clumpWindowBp := design.clumpWindowBp
  discoverySampleSize := design.gwasSampleSize
  clumpR2Cutoff_nonneg := design.clumpR2Threshold_nonneg
  clumpR2Cutoff_lt_one := design.clumpR2Threshold_lt_one
  discoverySampleSize_pos := design.gwasSampleSize_pos

/-- The fixed part of P+T conditional on one realized marker panel.  LD geometry is fixed
during the GWAS/clump operation on that panel; the full upstream genome draw may change it. -/
structure PTProtocol (thresholdCount m : ℕ) where
  parameters : PTParameters
  positionBp : Fin m → ℕ
  sourceR2 : Fin m → Fin m → ℝ
  sourceR2_nonnegative : ∀ i j, 0 ≤ sourceR2 i j
  sourceR2_le_one : ∀ i j, sourceR2 i j ≤ 1
  sourceR2_symmetric : ∀ i j, sourceR2 i j = sourceR2 j i
  pThreshold : Fin thresholdCount → ℝ
  pThreshold_nonnegative : ∀ q, 0 ≤ pThreshold q
  pThreshold_le_one : ∀ q, pThreshold q ≤ 1

/-- Build the fixed P+T protocol from the visible study constants and one realized marker
panel.  Positions and source LD belong to the genome draw; clump constants, discovery size,
and every threshold are definitionally the visible design rather than a second supplied copy. -/
noncomputable def PipelineStudyDesign.ptProtocol {demeCount m : ℕ}
    (design : PipelineStudyDesign demeCount)
    (positionBp : Fin m → ℕ) (sourceR2 : Fin m → Fin m → ℝ)
    (sourceR2_nonnegative : ∀ i j, 0 ≤ sourceR2 i j)
    (sourceR2_le_one : ∀ i j, sourceR2 i j ≤ 1)
    (sourceR2_symmetric : ∀ i j, sourceR2 i j = sourceR2 j i) :
    PTProtocol design.selectionThresholds.length m where
  parameters := design.ptParameters
  positionBp := positionBp
  sourceR2 := sourceR2
  sourceR2_nonnegative := sourceR2_nonnegative
  sourceR2_le_one := sourceR2_le_one
  sourceR2_symmetric := sourceR2_symmetric
  pThreshold := fun threshold ↦ design.selectionThresholds.get threshold
  pThreshold_nonnegative := fun threshold ↦
    design.selectionThresholds_nonneg _ (List.get_mem design.selectionThresholds threshold)
  pThreshold_le_one := fun threshold ↦
    design.selectionThresholds_le_one _ (List.get_mem design.selectionThresholds threshold)

/-- A realized marker-panel protocol uses exactly the visible non-genomic study constants.
Only positions and source LD may vary with the genome draw. -/
structure PTProtocol.MatchesStudyDesign {demeCount m : ℕ}
    (design : PipelineStudyDesign demeCount)
    (protocol : PTProtocol design.selectionThresholds.length m) : Prop where
  parameters_eq : protocol.parameters = design.ptParameters
  thresholds_eq : ∀ threshold,
    protocol.pThreshold threshold = design.selectionThresholds.get threshold

/-- Two markers conflict when they lie inside the supplied clumping window and their source
LD reaches the supplied exclusion cutoff.  Equality is excluded, matching retention by a
strict `r² < cutoff` rule. -/
noncomputable def ptConflict {m : ℕ} (parameters : PTParameters) (positionBp : Fin m → ℕ)
    (sourceR2 : Fin m → Fin m → ℝ) (i j : Fin m) : Bool :=
  decide (((positionBp i : ℤ) - (positionBp j : ℤ)).natAbs ≤ parameters.clumpWindowBp ∧
    parameters.clumpR2Cutoff ≤ sourceR2 i j)

/-- Greedy clumping in the supplied significance order.  A marker is kept exactly when no
already-kept marker conflicts with it.  This recursion, rather than an independence
approximation, is the clumping-under-LD law. -/
def greedyClumpAux {α : Type*} (conflict : α → α → Bool) : List α → List α → List α
  | [], kept => kept.reverse
  | x :: xs, kept =>
      if kept.any (fun y ↦ conflict x y) then greedyClumpAux conflict xs kept
      else greedyClumpAux conflict xs (x :: kept)

/-- Run greedy clumping from an empty retained set. -/
def greedyClump {α : Type*} (conflict : α → α → Bool) (ordered : List α) : List α :=
  greedyClumpAux conflict ordered []

/-- A complete P+T design with an arbitrary finite threshold family.  `orderedMarkers` is the
deterministic order used by the clumper; `coversMarkers` prevents silently dropping a marker. -/
structure PTDesign (thresholdCount m : ℕ) where
  protocol : PTProtocol thresholdCount m
  pValue : Fin m → ℝ
  pValue_nonnegative : ∀ i, 0 ≤ pValue i
  pValue_le_one : ∀ i, pValue i ≤ 1
  orderedMarkers : List (Fin m)
  orderedMarkers_nodup : orderedMarkers.Nodup
  orderedMarkers_by_significance :
    orderedMarkers.Pairwise (fun earlier later ↦ pValue earlier ≤ pValue later)
  coversMarkers : ∀ i, i ∈ orderedMarkers

/-- Ordered threshold-eligible markers. -/
noncomputable def PTDesign.eligible {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (q : Fin thresholdCount) : List (Fin m) :=
  d.orderedMarkers.filter fun i ↦ decide (d.pValue i ≤ d.protocol.pThreshold q)

/-- The exact retained marker list at threshold `q`. -/
noncomputable def PTDesign.selected {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (q : Fin thresholdCount) : List (Fin m) :=
  greedyClump
    (ptConflict d.protocol.parameters d.protocol.positionBp d.protocol.sourceR2) (d.eligible q)

/-- A threshold winner is the index whose analytically predicted objective dominates all
other candidates.  Ties are allowed and must be resolved by the caller's declared
ordering, not by an unrecorded search. -/
structure PTWinner {thresholdCount m : ℕ} (d : PTDesign thresholdCount m)
    (objective : Fin thresholdCount → ℝ) where
  index : Fin thresholdCount
  optimal : ∀ q, objective q ≤ objective index

/-- A normalized law over threshold choices.  This is the analytic alternative to selecting
one winner when threshold uncertainty must be propagated. -/
structure PTThresholdMixture (thresholdCount : ℕ) where
  probability : Fin thresholdCount → ℝ
  probability_nonneg : ∀ q, 0 ≤ probability q
  probability_sum_one : ∑ q, probability q = 1

/-- Exact marginalization of any threshold-indexed functional. -/
noncomputable def PTThresholdMixture.expectation {thresholdCount : ℕ}
    (mixture : PTThresholdMixture thresholdCount) (functional : Fin thresholdCount → ℝ) : ℝ :=
  ∑ q, mixture.probability q * functional q

/-- Additive effect-variance mass retained after clumping and thresholding.

Empirical status: DERIVED -- the standard additive-variance summand `2 p (1-p) beta²`
summed over exactly the markers the design keeps; which markers are kept is the design's
combinatorics, proved above, and no retention coefficient is fitted. -/
noncomputable def PTDesign.selectedEffectMass {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (q : Fin thresholdCount)
    (alleleFrequency effect : Fin m → ℝ) : ℝ :=
  (d.selected q).map (fun i ↦
    2 * alleleFrequency i * (1 - alleleFrequency i) * effect i ^ 2) |>.sum

/-- Fraction of total additive effect mass retained by P+T.

Empirical status: DERIVED -- the ratio of `selectedEffectMass` to the same sum over all
markers, defined only where the hypothesis supplies a nonzero total. -/
noncomputable def PTDesign.selectedEffectMassFraction {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (q : Fin thresholdCount)
    (alleleFrequency effect : Fin m → ℝ)
    (_ : (∑ i, 2 * alleleFrequency i * (1 - alleleFrequency i) * effect i ^ 2) ≠ 0) : ℝ :=
  d.selectedEffectMass q alleleFrequency effect /
    (∑ i, 2 * alleleFrequency i * (1 - alleleFrequency i) * effect i ^ 2)

/-- Effect mass surviving the analytically predicted winner.

Empirical status: DERIVED -- `PTDesign.selectedEffectMass` evaluated at the winner index
the design proves optimal; it adds no quantity of its own. -/
noncomputable def PTWinner.selectedEffectMass {thresholdCount m : ℕ}
    {d : PTDesign thresholdCount m} {objective : Fin thresholdCount → ℝ}
    (winner : PTWinner d objective) (alleleFrequency effect : Fin m → ℝ) : ℝ :=
  d.selectedEffectMass winner.index alleleFrequency effect

/-- Effect mass with threshold uncertainty marginalized rather than optimized away.

Empirical status: DERIVED -- the mixture expectation of `selectedEffectMass` under the
supplied threshold law; the marginalization is exact and the mixture is an argument, not a
fit. -/
noncomputable def PTDesign.marginalSelectedEffectMass {thresholdCount m : ℕ}
    (d : PTDesign thresholdCount m) (mixture : PTThresholdMixture thresholdCount)
    (alleleFrequency effect : Fin m → ℝ) : ℝ :=
  mixture.expectation fun q ↦ d.selectedEffectMass q alleleFrequency effect

/-! ## B2. Joint GWAS estimation and selection, conditional on one realized genome -/

/-! ## C. Within-deme accuracy from the selected score moments -/

/-- Exact genotype/outcome primitives in one deme.  Allele-frequency moments from A1 supply
`genotypeMean`; one- and two-locus moments from A1/A2 supply `genotypeCovariance`; the genetic
architecture supplies the score/outcome cross-covariance. -/
structure DemeGeneticMomentPrimitive (markerCount : ℕ) where
  genotypeMean : Fin markerCount → ℝ
  genotypeCovariance : Matrix (Fin markerCount) (Fin markerCount) ℝ
  outcomeCrossCovariance : Fin markerCount → ℝ
  outcomeVariance : ℝ
  prevalence : ℝ
  covariance_symmetric : ∀ i j, genotypeCovariance i j = genotypeCovariance j i
  outcomeVariance_pos : 0 < outcomeVariance
  prevalence_pos : 0 < prevalence
  prevalence_lt_one : prevalence < 1
  cauchy_schwarz : ∀ weight : Fin markerCount → ℝ,
    (∑ i, weight i * outcomeCrossCovariance i) ^ 2 ≤
      (∑ i, ∑ j, weight i * genotypeCovariance i j * weight j) * outcomeVariance

/-- Score mean from weights and genotype means. -/
noncomputable def DemeGeneticMomentPrimitive.scoreMean {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (weight : Fin markerCount → ℝ) : ℝ :=
  ∑ i, weight i * primitive.genotypeMean i

/-- Exact quadratic score variance `w' Sigma w`. -/
noncomputable def DemeGeneticMomentPrimitive.scoreVariance {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (weight : Fin markerCount → ℝ) : ℝ :=
  ∑ i, ∑ j, weight i * primitive.genotypeCovariance i j * weight j

/-- Exact score/outcome covariance `w' Cov(G,Y)`. -/
noncomputable def DemeGeneticMomentPrimitive.predictiveCovariance {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (weight : Fin markerCount → ℝ) : ℝ :=
  ∑ i, weight i * primitive.outcomeCrossCovariance i

/-- A selected score whose variance is genuinely positive.  Cauchy--Schwarz is inherited
from the primitive for this weight vector. -/
structure AdmissibleScoreWeights {markerCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount) where
  weight : Fin markerCount → ℝ
  scoreVariance_pos : 0 < primitive.scoreVariance weight

/-- Zero unselected weights and retain the realised GWAS effect at selected markers. -/
noncomputable def PTDesign.selectedWeight {thresholdCount markerCount : ℕ}
    (design : PTDesign thresholdCount markerCount) (threshold : Fin thresholdCount)
    (estimatedEffect : Fin markerCount → ℝ) : Fin markerCount → ℝ :=
  fun marker ↦ if marker ∈ design.selected threshold then estimatedEffect marker else 0

/-- The per-deme output of A+B.  `scoreMean` is required for calibration and pooling;
second moments alone are insufficient for either. -/
structure DemeScoreLaw where
  scoreMean : ℝ
  moments : Descent.Core.ScoreMoments
  moments_admissible : Descent.Core.ScoreMoments.Admissible moments
  prevalence : ℝ
  prevalence_pos : 0 < prevalence
  prevalence_lt_one : prevalence < 1

/-- The prevalence carried by a deme score law, with its domain evidence.

Empirical status: NOT AN EMPIRICAL CLAIM -- repackaging the law's own prevalence field with
its interiority evidence; the field's value is whatever the constructor supplied. -/
def DemeScoreLaw.prevalenceProbability (law : DemeScoreLaw) : InteriorProbability where
  value := law.prevalence
  value_pos := law.prevalence_pos
  value_lt_one := law.prevalence_lt_one

/-- The exact A+B-to-C constructor. -/
noncomputable def AdmissibleScoreWeights.toDemeScoreLaw {markerCount : ℕ}
    {primitive : DemeGeneticMomentPrimitive markerCount}
    (score : AdmissibleScoreWeights primitive) : DemeScoreLaw where
  scoreMean := primitive.scoreMean score.weight
  moments :=
    { scoreVariance := primitive.scoreVariance score.weight
      predictiveCovariance := primitive.predictiveCovariance score.weight
      outcomeVariance := primitive.outcomeVariance }
  moments_admissible :=
    { scoreVariance_pos := score.scoreVariance_pos
      outcomeVariance_pos := primitive.outcomeVariance_pos
      cauchy_schwarz := primitive.cauchy_schwarz score.weight }
  prevalence := primitive.prevalence
  prevalence_pos := primitive.prevalence_pos
  prevalence_lt_one := primitive.prevalence_lt_one

/-- Distance-resolved output for a train deme and every target deme. -/
structure DistanceResolvedScoreLaw (D : ℕ) where
  train : Fin D
  atDeme : Fin D → DemeScoreLaw

/-- Additive genetic-liability variance induced by a realized distinct causal-marker map and
effect vector in one deme. -/
noncomputable def DemeGeneticMomentPrimitive.causalGeneticVariance
    {markerCount causalCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (causalMarker : Fin causalCount → Fin markerCount)
    (causalEffect : Fin causalCount → ℝ) : ℝ :=
  ∑ first, ∑ second,
    causalEffect first * primitive.genotypeCovariance (causalMarker first) (causalMarker second) *
      causalEffect second

/-- Covariance of one marker with the additive genetic liability from the same architecture.

Empirical status: DERIVED -- bilinear expansion of the supplied genotype covariance against
the realized effect vector; it asserts nothing beyond the moment primitive it reads. -/
noncomputable def DemeGeneticMomentPrimitive.markerLiabilityCovariance
    {markerCount causalCount : ℕ}
    (primitive : DemeGeneticMomentPrimitive markerCount)
    (causalMarker : Fin causalCount → Fin markerCount)
    (causalEffect : Fin causalCount → ℝ) (marker : Fin markerCount) : ℝ :=
  ∑ causal,
    primitive.genotypeCovariance marker (causalMarker causal) * causalEffect causal

/-! ### B1+B2 composed into a variable-marker realized draw -/

/-- Everything needed to construct the selected score after one realized genome, architecture,
phenotype, and GWAS draw.  The marker count is a field, not a type parameter of the stochastic
law: mutation can therefore change it from one realization to the next.  The fields are
construction obligations for the upstream ARG/mutation/GWAS kernel, not independently fitted
inputs.

Selection remains inside the draw.  In particular, `design.pValue`, `estimatedEffect`, the
greedy retained sets, held-out objective, orientation, and winning threshold are jointly
realized before any downstream expectation is taken. -/
structure RealizedPTGWASDraw {D : ℕ} (input : VisiblePipelineInput D) where
  markerCount : ℕ
  design : PTDesign input.studyDesign.selectionThresholds.length markerCount
  design_matches_study : PTProtocol.MatchesStudyDesign input.studyDesign design.protocol
  estimatedEffect : Fin markerCount → ℝ
  genotypeAt : ∀ deme, Fin (input.studyDesign.cohortSize deme) → Fin markerCount → ℝ
  primitiveAt : Fin D → DemeGeneticMomentPrimitive markerCount
  causalMarker : Fin input.studyDesign.causalLocusCount → Fin markerCount
  causalMarker_injective : Function.Injective causalMarker
  causalEffect : Fin input.studyDesign.causalLocusCount → ℝ
  sourceGeneticVariance_eq_one :
    (primitiveAt input.studyDesign.gwasDeme).causalGeneticVariance
      causalMarker causalEffect = 1
  outcomeCrossCovariance_eq : ∀ deme marker,
    (primitiveAt deme).outcomeCrossCovariance marker =
      (primitiveAt deme).markerLiabilityCovariance causalMarker causalEffect marker
  outcomeVariance_eq : ∀ deme,
    (primitiveAt deme).outcomeVariance =
      (primitiveAt deme).causalGeneticVariance causalMarker causalEffect +
        input.studyDesign.residualVariance
  selectionObjective : Fin input.studyDesign.selectionThresholds.length → ℝ
  deploymentSign : ℝ
  deploymentSign_is_orientation : deploymentSign = 1 ∨ deploymentSign = -1
  selectedScoreAt : ∀ threshold deme, AdmissibleScoreWeights (primitiveAt deme)
  selectedWeight_eq : ∀ threshold deme,
    (selectedScoreAt threshold deme).weight =
      fun marker ↦ deploymentSign *
        design.selectedWeight threshold estimatedEffect marker
  winner : PTWinner design selectionObjective

/-- The architecture normalization and derived residual scale recover exactly the visible
source heritability on every draw.  No fitted variance constant remains in this identity. -/
theorem RealizedPTGWASDraw.sourceHeritability_eq
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input) :
    (draw.primitiveAt input.studyDesign.gwasDeme).causalGeneticVariance
        draw.causalMarker draw.causalEffect /
      (draw.primitiveAt input.studyDesign.gwasDeme).outcomeVariance =
        input.studyDesign.heritability := by
  rw [draw.outcomeVariance_eq input.studyDesign.gwasDeme,
    draw.sourceGeneticVariance_eq_one]
  unfold PipelineStudyDesign.residualVariance
  have hne : input.studyDesign.heritability ≠ 0 :=
    ne_of_gt input.studyDesign.heritability_pos
  field_simp [hne]
  ring

/-- Distance-resolved score law generated by one GWAS draw and threshold. -/
noncomputable def RealizedPTGWASDraw.distanceLawAt
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (threshold : Fin input.studyDesign.selectionThresholds.length) :
    DistanceResolvedScoreLaw D where
  train := input.studyDesign.gwasDeme
  atDeme := fun deme ↦ (draw.selectedScoreAt threshold deme).toDemeScoreLaw

/-- Candidate selected by held-out threshold comparison in this realized draw. -/
noncomputable def RealizedPTGWASDraw.winningScoreLaw
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input) :
    DistanceResolvedScoreLaw D :=
  draw.distanceLawAt draw.winner.index

/-- Deployed score of one visible evaluation individual at a specified P+T threshold.  This
is the same selected-weight dot product whose population moments form `distanceLawAt`; it is
kept at individual resolution for the exact finite-cohort evaluator. -/
noncomputable def RealizedPTGWASDraw.scoreValueAt
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (threshold : Fin input.studyDesign.selectionThresholds.length) (deme : Fin D)
    (individual : Fin (input.studyDesign.cohortSize deme)) : ℝ :=
  ∑ marker, (draw.selectedScoreAt threshold deme).weight marker *
    draw.genotypeAt deme individual marker

/-- Individual deployed score after the held-out winning threshold has been chosen. -/
noncomputable def RealizedPTGWASDraw.winningScoreValue
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (deme : Fin D) (individual : Fin (input.studyDesign.cohortSize deme)) : ℝ :=
  draw.scoreValueAt draw.winner.index deme individual

/-- Additive genetic liability of one realized individual from the same causal-marker map,
effect vector, and genotype panel that generated the GWAS score. -/
noncomputable def RealizedPTGWASDraw.geneticLiabilityValue
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (deme : Fin D) (individual : Fin (input.studyDesign.cohortSize deme)) : ℝ :=
  ∑ causal, draw.causalEffect causal *
    draw.genotypeAt deme individual (draw.causalMarker causal)

/-- The executable phenotype protocol's non-genetic liability contribution on the visible
evaluation cohort.  In gnomon this is the quantity that distinguishes the `C`, `A`, `R`, and
`B` phenotype rungs.  It is deliberately not inferred from demography: choosing the rung is
a protocol decision and is not among `VisiblePipelineInput`'s arguments. -/
abbrev PhenotypeBaseline {D : ℕ} (input : VisiblePipelineInput D) :=
  ∀ deme, Fin (input.studyDesign.cohortSize deme) → ℝ

/-- Total liability obtained by composing the realized causal architecture with an explicit
phenotype-baseline rule.  This is the unique input to the derived global prevalence root and
therefore to the true Bernoulli risks used by every finite-cohort metric. -/
noncomputable def RealizedPTGWASDraw.phenotypeLiabilityPanel
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (phenotypeBaseline : PhenotypeBaseline input) :
    FiniteLiabilityPanel input.studyDesign where
  liability := fun deme individual ↦
    phenotypeBaseline deme individual + draw.geneticLiabilityValue deme individual

/-- Two executable phenotype rules on the same genome draw induce identical exact risks only
when their baseline vectors differ by one global constant.  In particular, per-deme centering
(`phenoC`) and nonconstant affine/random deme effects (`phenoA`/`phenoR`) are real semantic
coordinates, not simulator draws that can be marginalized without first choosing a rung. -/
theorem RealizedPTGWASDraw.exists_phenotypeRisk_ne_of_baseline_not_common_shift
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (first second : PhenotypeBaseline input)
    (hshift : ¬ ∃ offset : ℝ, ∀ deme individual,
      second deme individual = first deme individual + offset) :
    ∃ deme, ∃ individual,
      (draw.phenotypeLiabilityPanel first).risk deme individual ≠
        (draw.phenotypeLiabilityPanel second).risk deme individual := by
  apply (draw.phenotypeLiabilityPanel first).exists_risk_ne_of_not_common_shift
    (draw.phenotypeLiabilityPanel second)
  intro panelShift
  apply hshift
  obtain ⟨offset, hliability⟩ := panelShift
  refine ⟨offset, ?_⟩
  intro deme individual
  have := hliability deme individual
  simp only [RealizedPTGWASDraw.phenotypeLiabilityPanel] at this
  linarith

/-- A single stochastic kernel for every visible input.  Its sample space may be continuous,
and a successful `realizedAt input sample` may have a different marker count for every input
and sample.  Failure is explicit: zero mutation or a finite genome with fewer eligible markers
than the advertised causal-locus count cannot construct `RealizedPTGWASDraw`'s injective causal
map.  Returning `none` preserves the study design instead of silently reducing its causal
count, as the current executable's `min` does.

Constructing this kernel from the demographic history is the remaining upstream theorem; this
type states its exact partial target without freezing the number of segregating sites. -/
structure VariableMarkerPTGWASKernel (Sample : Type*) [MeasurableSpace Sample] (D : ℕ) where
  drawLaw : VisiblePipelineInput D → Measure Sample
  drawLaw_probability : ∀ input, IsProbabilityMeasure (drawLaw input)
  realizedAt : (input : VisiblePipelineInput D) → Sample → Option (RealizedPTGWASDraw input)

/-- C1: true within-deme squared accuracy. -/
noncomputable def DemeScoreLaw.r2True (law : DemeScoreLaw) : ℝ := law.moments.r2

/-- C1 on the observed binary-risk scale.  The score moments first determine explained
liability variance; thresholding at prevalence `K` contributes the exact density/Jacobian
factor `phi(Phi⁻¹(1-K))² / (K(1-K))`. -/
noncomputable def DemeScoreLaw.observedRiskR2 (law : DemeScoreLaw) : ℝ :=
  prevalenceScaledR2 law.r2True law.prevalence

/-- Certificate that an A+B moment construction composes with the validated clean-split
portability law.  The score moments remain the primary object; this equality is the independent
clean-split reduction they must satisfy. -/
structure CleanSplitMomentCertificate (law : DemeScoreLaw) (markerCount : ℕ) where
  ancestralR2 : ℝ
  effectMass : Fin markerCount → ℝ
  sourceFrequency : Fin markerCount → ℝ
  sourceEffectiveSize : ℝ
  targetEffectiveSize : ℝ
  generations : ℕ
  ldFactor : ℝ
  r2_reduction : law.r2True =
    cleanSplitTargetR2' ancestralR2 effectMass sourceFrequency
      sourceEffectiveSize targetEffectiveSize generations ldFactor

/-- Linear least-squares calibration slope from the same two score moments.  This is not the
logistic recalibration coefficient evaluated by the binary-risk pipeline. -/
noncomputable def DemeScoreLaw.linearCalibrationSlope (law : DemeScoreLaw) : ℝ :=
  law.moments.calibrationSlope

/-- Domain for charts that divide by unexplained variance. -/
structure DemeScoreLaw.ResidualVariation (law : DemeScoreLaw) : Prop where
  r2_lt_one : law.r2True < 1

/-- C2: probit index spread relative to residual spread,
`sqrt(R^2/(1-R^2))`. -/
noncomputable def DemeScoreLaw.probitRiskSpreadRatio
    (law : DemeScoreLaw) (_ : law.ResidualVariation) : ℝ :=
  Real.sqrt (law.r2True / (1 - law.r2True))

/-- Spearman correlation for a bivariate Gaussian with Pearson correlation `r`. -/
noncomputable def gaussianSpearman (r : ℝ) : ℝ :=
  6 / Real.pi * Real.arcsin (r / 2)

/-- Oriented Pearson correlation, retaining information that `R²` squares away. -/
noncomputable def DemeScoreLaw.pearson (law : DemeScoreLaw) : ℝ :=
  law.moments.predictiveCovariance /
    (Real.sqrt law.moments.scoreVariance * Real.sqrt law.moments.outcomeVariance)

/-- C3: within-deme Spearman accuracy under the bivariate-normal score/liability chart. -/
noncomputable def DemeScoreLaw.spearman (law : DemeScoreLaw) : ℝ :=
  gaussianSpearman law.pearson

/-- Gaussian mean absolute error from its error variance. -/
noncomputable def gaussianMAE (errorVariance : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * Real.sqrt errorVariance

/-- Error variance of the optimally linearly rescaled score. -/
noncomputable def DemeScoreLaw.linearErrorVariance (law : DemeScoreLaw) : ℝ :=
  law.moments.outcomeVariance * (1 - law.r2True)

/-- C3: MAE under the Gaussian residual chart. -/
noncomputable def DemeScoreLaw.mae (law : DemeScoreLaw) : ℝ :=
  gaussianMAE law.linearErrorVariance

/-- Standard normal density. -/
noncomputable def standardNormalDensity (z : ℝ) : ℝ :=
  Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- A standardized Gaussian upper tail with its probability tied to its boundary. -/
structure GaussianUpperTail where
  boundary : ℝ
  mass : ℝ
  mass_pos : 0 < mass
  mass_eq : mass = 1 - Foundations.Phi boundary

/-- A top-decile Gaussian tail. -/
structure GaussianTopDecile extends GaussianUpperTail where
  is_decile : mass = 1 / 10

/-- Conditional RMSE when `(error,Z)` is jointly Gaussian and `Z` is standardized.  The
conditional second moment is
`Var(error) + Cov(error,Z)^2 * a*phi(a)/P(Z>=a)`. -/
noncomputable def gaussianTailRMSE
    (errorVariance errorTailCovariance : ℝ) (tail : GaussianUpperTail) : ℝ :=
  Real.sqrt (errorVariance + errorTailCovariance ^ 2 *
    tail.boundary * standardNormalDensity tail.boundary / tail.mass)

/-- C3: general Gaussian tail-RMSE chart with error/tail covariance explicit. -/
noncomputable def DemeScoreLaw.tailRMSE (law : DemeScoreLaw)
    (errorTailCovariance : ℝ) (tail : GaussianUpperTail) : ℝ :=
  gaussianTailRMSE law.linearErrorVariance errorTailCovariance tail

/-- C3: top-score-decile RMSE after optimal linear rescaling.  The Gaussian residual is
orthogonal, hence independent, of the score, so selecting on the score leaves RMSE unchanged. -/
noncomputable def DemeScoreLaw.topDecileRMSE (law : DemeScoreLaw)
    (tail : GaussianTopDecile) : ℝ :=
  law.tailRMSE 0 tail.toGaussianUpperTail

theorem DemeScoreLaw.topDecileRMSE_eq_residualRMSE (law : DemeScoreLaw)
    (tail : GaussianTopDecile) :
    law.topDecileRMSE tail = Real.sqrt law.linearErrorVariance := by
  simp [DemeScoreLaw.topDecileRMSE, DemeScoreLaw.tailRMSE, gaussianTailRMSE]

/-- Mean liability-model risk in the score tail `z >= q`, divided by prevalence.  This is
the exact Gaussian integral chart for the top-decile risk ratio. -/
noncomputable def topTailRiskRatio
    (r2 : ℝ) (prevalence : InteriorProbability) (tail : GaussianUpperTail) : ℝ :=
  ((∫ z in Set.Ici tail.boundary,
      liabilityRiskAtScore r2 prevalence.value z * standardNormalDensity z) / tail.mass) /
    prevalence.value

/-- C3: top-decile risk ratio at the law's own `R^2` and prevalence. -/
noncomputable def DemeScoreLaw.topDecileRiskRatio (law : DemeScoreLaw)
    (_ : law.ResidualVariation) (tail : GaussianTopDecile) : ℝ :=
  topTailRiskRatio law.r2True law.prevalenceProbability tail.toGaussianUpperTail

/-- C3: OR per SD, using the already validated liability chart. -/
noncomputable def DemeScoreLaw.orPerSD
    (law : DemeScoreLaw) (_ : law.ResidualVariation) : ℝ :=
  orPerSDFromLiability law.r2True law.prevalence

/-- C3: exact liability Brier chart. -/
noncomputable def DemeScoreLaw.brier (law : DemeScoreLaw) : ℝ :=
  PopGen.TransportedMetrics.liabilityBrierExact law.prevalence law.r2True

/-- A strictly positive reference Brier risk. -/
structure ReferenceBrier where
  value : ℝ
  value_pos : 0 < value

/-- C3: Brier skill against an explicitly supplied reference risk. -/
noncomputable def DemeScoreLaw.brierSkill
    (law : DemeScoreLaw) (referenceBrier : ReferenceBrier) : ℝ :=
  1 - law.brier / referenceBrier.value

/-! ## D. Calibration and the phenotype ladder -/

/-- D1--D2: identity-scale per-deme calibration from the score mean, observed outcome mean,
and the same variance/covariance pair used by `r2True`. -/
noncomputable def DemeScoreLaw.identityCalibration (law : DemeScoreLaw)
    (observedMean predictedReferenceMean : ℝ) : CalibrationProfile :=
  identityCalibrationProfile observedMean
    (predictedReferenceMean + law.scoreMean) law.linearCalibrationSlope

/-- Drifted prevalence generated by a liability mean shift.  The threshold is pinned by the
source prevalence; a zero residual scale cannot be supplied.

Empirical status: DERIVED -- the liability-threshold model's prevalence under a mean shift,
with the threshold a genuine `Phi` preimage by `Phi_surjOn_Ioo` rather than an assumed
inverse; `emergentPrevalenceFromLiabilityMean_zero` proves the no-shift anchor.  Whether a
real cohort's prevalence drifts this way is the liability-model question, tested wherever
the calibration ladder is compared against simulation. -/
noncomputable def emergentPrevalenceFromLiabilityMean
    (sourcePrevalence : InteriorProbability) (liabilityMean : ℝ)
    (residualSD : PositiveScale) : InteriorProbability where
  value := Foundations.Phi
    (liabilityMean / residualSD.value - liabilityThreshold sourcePrevalence.value)
  value_pos := Foundations.Phi_pos _
  value_lt_one := Foundations.Phi_lt_one _

/-- With no liability-mean shift, the emergent prevalence is exactly the source prevalence
at every positive residual scale. -/
theorem emergentPrevalenceFromLiabilityMean_zero
    (sourcePrevalence : InteriorProbability) (residualSD : PositiveScale) :
    (emergentPrevalenceFromLiabilityMean sourcePrevalence 0 residualSD).value =
      sourcePrevalence.value := by
  unfold emergentPrevalenceFromLiabilityMean
  have h := liabilityRiskAtScore_at_zero_r2_eq_prevalence
    sourcePrevalence.value 0 sourcePrevalence.value_pos sourcePrevalence.value_lt_one
  unfold liabilityRiskAtScore at h
  norm_num at h ⊢
  exact h

/-- The four phenotype rungs. -/
inductive PhenotypeRung where
  | phenoC
  | phenoA
  | phenoR
  | phenoB
deriving DecidableEq, Repr

/-- Mean realized genetic liability in one visible deme. -/
noncomputable def RealizedPTGWASDraw.demeMeanGeneticLiability
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (deme : Fin D) : ℝ :=
  (∑ individual, draw.geneticLiabilityValue deme individual) /
    input.studyDesign.cohortSize deme

/-- The four individual-level phenotype rules in `gen_real_pt.py`.

`phenoA` and `phenoR` consume their supplied per-deme baseline realization.  `phenoB` adds
nothing.  `phenoC` subtracts the realized within-deme genetic-liability mean, exactly matching
the executable's drift-proof centering operation. -/
noncomputable def RealizedPTGWASDraw.phenotypeBaselineForRung
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (rung : PhenotypeRung) (affineBaseline randomBaseline : Fin D → ℝ) :
    PhenotypeBaseline input :=
  match rung with
  | .phenoA => fun deme _individual ↦ affineBaseline deme
  | .phenoR => fun deme _individual ↦ randomBaseline deme
  | .phenoB => fun _deme _individual ↦ 0
  | .phenoC => fun deme _individual ↦ -draw.demeMeanGeneticLiability deme

/-- The constant-baseline rung is definitionally genetic liability alone. -/
theorem RealizedPTGWASDraw.phenotypeBaselineForRung_phenoB
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (affineBaseline randomBaseline : Fin D → ℝ) (deme : Fin D)
    (individual : Fin (input.studyDesign.cohortSize deme)) :
    draw.phenotypeBaselineForRung .phenoB affineBaseline randomBaseline deme individual = 0 :=
  rfl

/-- The drift-proof rung's baseline is exactly the negative realized deme mean. -/
theorem RealizedPTGWASDraw.phenotypeBaselineForRung_phenoC
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (affineBaseline randomBaseline : Fin D → ℝ) (deme : Fin D)
    (individual : Fin (input.studyDesign.cohortSize deme)) :
    draw.phenotypeBaselineForRung .phenoC affineBaseline randomBaseline deme individual =
      -draw.demeMeanGeneticLiability deme := rfl

/-- The executable phenoC construction has exactly zero realized mean total liability in
every deme; this is the algebraic property its "drift-proof" label promises. -/
theorem RealizedPTGWASDraw.phenotypeLiabilityPanel_phenoC_demeMean
    {D : ℕ} {input : VisiblePipelineInput D} (draw : RealizedPTGWASDraw input)
    (affineBaseline randomBaseline : Fin D → ℝ) (deme : Fin D) :
    (draw.phenotypeLiabilityPanel
      (draw.phenotypeBaselineForRung .phenoC affineBaseline randomBaseline)).demeMean deme =
        0 := by
  unfold FiniteLiabilityPanel.demeMean RealizedPTGWASDraw.phenotypeLiabilityPanel
    RealizedPTGWASDraw.phenotypeBaselineForRung
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  unfold RealizedPTGWASDraw.demeMeanGeneticLiability
  have hsize : (input.studyDesign.cohortSize deme : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (input.studyDesign.cohortSize_pos deme))
  field_simp [hsize]
  ring

/-- Inputs whose provenance distinguishes imposed baselines from the emergent genetic mean.
`affineBaseline` and `randomBaseline` are used only on their named rungs; phenoB uses the
genetic-liability mean generated upstream. -/
structure PhenotypeLadderInput where
  sourcePrevalence : InteriorProbability
  residualSD : PositiveScale
  affineBaseline : ℝ
  randomBaseline : ℝ
  geneticLiabilityMean : ℝ

/-- Explicit affine coordinate map from deployed score mean to genetic-liability mean. -/
structure ScoreLiabilityScale where
  intercept : ℝ
  loading : ℝ

noncomputable def ScoreLiabilityScale.mean
    (scale : ScoreLiabilityScale) (scoreMean : ℝ) : ℝ :=
  scale.intercept + scale.loading * scoreMean

/-- Identity scale for a score already measured as genetic liability. -/
def ScoreLiabilityScale.identity : ScoreLiabilityScale where
  intercept := 0
  loading := 1

/-- Build the phenotype ladder from the demographic score law.  This is the A1-to-phenoB
edge: the emergent rung receives the genetic-liability mean and no target prevalence. -/
noncomputable def PhenotypeLadderInput.ofScoreLaw
    (sourcePrevalence : InteriorProbability) (residualSD : PositiveScale)
    (affineBaseline randomBaseline : ℝ) (scale : ScoreLiabilityScale)
    (law : DemeScoreLaw) : PhenotypeLadderInput where
  sourcePrevalence := sourcePrevalence
  residualSD := residualSD
  affineBaseline := affineBaseline
  randomBaseline := randomBaseline
  geneticLiabilityMean := scale.mean law.scoreMean

/-- D3: per-rung prevalence.  phenoC is the clean floor; phenoA/R apply their imposed
baselines; phenoB obtains its prevalence from the upstream genetic-liability mean and is not
told a target prevalence.

Empirical status: DERIVED -- rung dispatch over `emergentPrevalenceFromLiabilityMean`,
whose status it inherits; the ladder's point is that phenoB's prevalence is computed from
the upstream mean rather than imposed, and that structural claim is what a battery on the
ladder would test. -/
noncomputable def phenotypePrevalence (input : PhenotypeLadderInput)
    (rung : PhenotypeRung) : InteriorProbability :=
  match rung with
  | .phenoC => input.sourcePrevalence
  | .phenoA => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.affineBaseline input.residualSD
  | .phenoR => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.randomBaseline input.residualSD
  | .phenoB => emergentPrevalenceFromLiabilityMean input.sourcePrevalence
      input.geneticLiabilityMean input.residualSD

/-- Replace only the prevalence axis of a score law by a phenotype rung.  Score moments stay
fixed, so discrimination and calibration consume phenoB's emergent prevalence without being
told it independently. -/
noncomputable def DemeScoreLaw.atPhenotypeRung (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (rung : PhenotypeRung) : DemeScoreLaw :=
  let rungPrevalence := phenotypePrevalence input rung
  { law with
    prevalence := rungPrevalence.value
    prevalence_pos := rungPrevalence.value_pos
    prevalence_lt_one := rungPrevalence.value_lt_one }

/-- Difference of marginal prevalence logits at one phenotype rung.  This equals logistic
CITL only in the constant-predictor regime; the exact nonconstant-score pipeline CITL is the
offset likelihood fit in `BinaryRiskCohort.calibrationInTheLarge`. -/
noncomputable def phenotypeMarginalLogitShift (input : PhenotypeLadderInput)
    (predictedPrevalence : InteriorProbability) (rung : PhenotypeRung) : ℝ :=
  prevalenceCITLShift predictedPrevalence.value (phenotypePrevalence input rung).value

/-- Linear-moment calibration profile paired with a marginal-logit prevalence shift.  It is a
population approximation and is deliberately not named as the pipeline's logistic fit. -/
noncomputable def phenotypeLinearCalibrationProfile (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (predictedPrevalence : InteriorProbability)
    (rung : PhenotypeRung) : CalibrationProfile where
  citl := phenotypeMarginalLogitShift input predictedPrevalence rung
  slope := law.linearCalibrationSlope
  link := CalibrationLink.logistic

/-- The clean rung has no intercept shift when predicted at its source prevalence. -/
theorem phenotypeMarginalLogitShift_phenoC_zero (input : PhenotypeLadderInput) :
    phenotypeMarginalLogitShift input input.sourcePrevalence PhenotypeRung.phenoC = 0 := by
  exact no_citl_shift_same_prevalence input.sourcePrevalence.value

/-- D2 is shared by all rungs: changing a baseline changes the intercept/prevalence but not
the variance-attenuation slope supplied by the score law. -/
theorem phenotype_ladder_slope_is_score_slope (law : DemeScoreLaw)
    (input : PhenotypeLadderInput) (rung : PhenotypeRung) :
    law.linearCalibrationSlope = law.moments.calibrationSlope := rfl

/-! ## Inhabitation

A theorem quantified over an uninhabited structure is true and empty -- kernel-checked, clean
axiom report, no content -- so each hypothesis-carrying class above needs one exhibited
inhabitant before anything stated over it is a statement about something.

THE VALUES ARE CHOSEN OFF THE BOUNDARIES THEIR OWN HYPOTHESES EXCLUDE, which is the whole
difference between a witness that discharges a screen and a witness that tests a construction.
`PTProtocol.witness` carries TWO markers a megabase apart against a 250 kb clumping window, so
the conflict predicate is exercised and returns false for a reason rather than vacuously; a
one-marker protocol would inhabit the class while making the clumping recursion unreachable. -/

/-- Inhabitation for the positive scale. -/
noncomputable def PositiveScale.witness : PositiveScale where
  value := 1
  value_pos := by norm_num

/-- Inhabitation for the interior probability, away from both endpoints. -/
noncomputable def InteriorProbability.witness : InteriorProbability where
  value := 1 / 4
  value_pos := by norm_num
  value_lt_one := by norm_num

/-- Inhabitation for the P+T parameters, at a cutoff strictly inside its admitted range. -/
noncomputable def PTParameters.witness : PTParameters where
  clumpR2Cutoff := 1 / 10
  clumpWindowBp := 250000
  discoverySampleSize := 100000
  clumpR2Cutoff_nonneg := by norm_num
  clumpR2Cutoff_lt_one := by norm_num
  discoverySampleSize_pos := by norm_num

/-- Inhabitation for the protocol: two markers a megabase apart, so the clumping window is a
real constraint rather than an unreached branch, and a two-threshold family. -/
noncomputable def PTProtocol.witness : PTProtocol 2 2 where
  parameters := PTParameters.witness
  positionBp := fun i ↦ if i = 0 then 0 else 1000000
  sourceR2 := fun i j ↦ if i = j then 1 else 1 / 2
  sourceR2_nonnegative := by intro i j; split <;> norm_num
  sourceR2_le_one := by intro i j; split <;> norm_num
  sourceR2_symmetric := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  pThreshold := fun q ↦ if q = 0 then 1 / 20 else 1 / 2
  pThreshold_nonnegative := by intro q; split <;> norm_num
  pThreshold_le_one := by intro q; split <;> norm_num

/-- Inhabitation for the design.  Both markers pass both thresholds and neither clumps the
other out, so `selected` returns both and the greedy recursion is genuinely run. -/
noncomputable def PTDesign.witness : PTDesign 2 2 where
  protocol := PTProtocol.witness
  pValue := fun _ ↦ 1 / 100
  pValue_nonnegative := by intro i; norm_num
  pValue_le_one := by intro i; norm_num
  orderedMarkers := [0, 1]
  orderedMarkers_nodup := by decide
  orderedMarkers_by_significance := by simp
  coversMarkers := by decide

/-- Inhabitation for the threshold winner, against a constant objective where every index is
optimal and the tie is the caller's to resolve, which is what the class says. -/
noncomputable def PTWinner.witness : PTWinner PTDesign.witness (fun _ ↦ (0 : ℝ)) where
  index := 0
  optimal := by intro q; norm_num

/-- Inhabitation for the threshold mixture, at the uniform law over two thresholds. -/
noncomputable def PTThresholdMixture.witness : PTThresholdMixture 2 where
  probability := fun _ ↦ 1 / 2
  probability_nonneg := by intro q; norm_num
  probability_sum_one := by simp

/-- Inhabitation for the Gaussian upper tail.  The mass is positive at EVERY boundary because
`Foundations.Phi_lt_one` is strict, so this exhibits the class without choosing a special
point. -/
noncomputable def GaussianUpperTail.witness : GaussianUpperTail where
  boundary := 0
  mass := 1 - Foundations.Phi 0
  mass_pos := by have := Foundations.Phi_lt_one 0; linarith
  mass_eq := rfl

/-- Inhabitation for the reference Brier score. -/
noncomputable def ReferenceBrier.witness : ReferenceBrier where
  value := 1 / 4
  value_pos := by norm_num

end Descent.Portability
