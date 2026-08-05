/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability
import Descent.PopGen.DGP
import Descent.Program.Conclusions
import Descent.Portability.PortabilityDrift
import Descent.Portability.PortabilityMasterTheorem
import Descent.PopGen.HumanDemography
import Descent.PopGen.AdditiveInvariance
import Descent.Blindness.ImitationRigidity
import Descent.Foundations.Conventions
import Descent.PopGen.DemographicCapacity
import Descent.PopGen.DriftRegime
import Descent.Blindness.BlindnessRegistry
import Descent.Program.OpenQuestions
import Descent.Blindness.TrafficInvariantSeparation
import Descent.Foundations.TransportIdentities
import Descent.Spectral.SecondMomentShift
import Descent.Spectral.QuadraticShift
import Descent.Spectral.ProjectionShiftBounds
import Descent.Spectral.ProjectionSolve
import Descent.Spectral.WhiteningEquivalence
import Descent.Portability.PortabilityBounds
import Descent.Portability.MultiAncestryTheory
import Descent.Portability.StratificationConfounding
import Descent.Portability.AncestryCalibration
import Descent.PopGen.LDDecayTheory
import Descent.PopGen.SelectionArchitecture
import Descent.PopGen.DemographicHistory
import Descent.PopGen.SerialFounderChain
import Descent.Portability.ClinicalUtilityFairness
import Descent.PopGen.VarianceComponents
import Descent.Portability.ScoreDistribution
import Descent.Decision.ValidationStatistics
import Descent.Portability.MechanisticPortabilityWitnesses
import Descent.Decision.SelectionValidation
import Descent.PopGen.GeneticArchitectureDiscovery
import Descent.Portability.BayesianPGSTheory
import Descent.Portability.PhenomeWidePortability
import Descent.Portability.TransferLearningPGS
import Descent.Portability.MetricSpecificPortability
import Descent.PopGen.PopulationGeneticsFoundations
import Descent.PopGen.GeneEnvironmentInterplay
import Descent.Portability.RareVariantPortability
import Descent.Portability.StatisticalGeneticsMethodology
import Descent.Portability.EquityAndImplementation
import Descent.PopGen.EpistasisAndNonAdditivity
import Descent.PopGen.PolygenicAdaptation
import Descent.PopGen.AssortativeMatingPGS
import Descent.Portability.ImputationPortability
import Descent.Portability.LongitudinalPortability
import Descent.Decision.PowerAnalysis
import Descent.Foundations.CovarianceStructure
import Descent.Foundations.CausalInference
import Descent.Decision.CertificateGrading
import Descent.Portability.ContinuumCalibration
import Descent.Portability.ContinuumCalibrationProgram
import Descent.Blindness.DecoratedGeometryBlindness
import Descent.Portability.CorrectionBiology
import Descent.Portability.CorrectionWidths
import Descent.Decision.FiniteMinimax
import Descent.Decision.BlindnessMinimaxFloors
import Descent.Spectral.PencilEnvironment
import Descent.Spectral.DirichletTransfer
import Descent.Conditionals.DeclaredInteractionClass
import Descent.Blindness.CountingInvariantBlindness
import Descent.Blindness.CountingInvariantInstances
import Descent.PopGen.PolygenicArchitecture
import Descent.Portability.PolygenicContinuumCalibration
import Descent.Portability.SampleOverlapBias
import Descent.PopGen.HaplotypeTheory
import Descent.PopGen.AncestrySpecificArchitecture
import Descent.Portability.AncestrySpecificPower
import Descent.Portability.PGSCalibrationTheory
import Descent.Blindness.ObservationalCeiling
import Descent.Blindness.Condensation
import Descent.Blindness.CumulantBlindness
import Descent.Blindness.JetBarrier
import Descent.Conditionals.LocalToGlobalCoherence
import Descent.Blindness.HiddenConeAmbiguity
import Descent.Conditionals.LatentMechanismCollapse
import Descent.Spectral.PolygenicSpectroscopy
import Descent.Blindness.EpistaticChaos
import Descent.PopGen.StandardizedGenotypeMoments
import Descent.Blindness.CramerStratum
import Descent.Spectral.FoldedSpectrum
import Descent.Spectral.SpectralDegradation
import Descent.Blindness.SpectralUniversalityFailure
import Descent.Blindness.SpectrumIdentifiability
import Descent.Blindness.XiFromMarkedBreakouts
import Descent.Spectral.EnsembleChannel
import Descent.Spectral.Permeability
import Descent.Spectral.ErgodicCovariancePencil
import Descent.Portability.HorizonCurve
import Descent.Conditionals.DriftingConditionals
import Descent.Spectral.CirculationDefect
import Descent.Blindness.LumpedRateBlindness
import Descent.Portability.TransplantationStability
import Descent.Conditionals.DynamicsContrast
import Descent.Coalescent.Rates
import Descent.Coalescent.StateSpace
import Descent.Coalescent.WrightFisher
import Descent.Coalescent.JumpChain
import Descent.Coalescent.Mutation
import Descent.Coalescent.Restriction
import Descent.Coalescent.Paintbox
import Descent.Coalescent.IntervalPicture
import Descent.Coalescent.Generator
import Descent.Coalescent.Process
import Descent.Coalescent.Kernel
import Descent.Coalescent.Split
import Descent.Coalescent.Extend
import Descent.Coalescent.Ewens
import Descent.Coalescent.CutSets
import Descent.Coalescent.CutCount
import Descent.Coalescent.Path
import Descent.Coalescent.Trajectory
import Descent.Coalescent.Law
import Descent.Coalescent.HoldingTime
import Descent.Coalescent.Infinite
import Descent.Coalescent.Program
-- THE BUILD MUST COVER ITS OWN CORPUS. Everything below was outside this root's import
-- closure, so `lake build Descent` never compiled it -- and a module the build never
-- reaches is not clean, it is UNBUILT. That is not a hypothetical: `ResonanceSpectrum`
-- had been failing all day on a missing `Real.log` import while every whole-corpus build
-- reported zero errors, because no target ever named it. It showed up only as a line in
-- `MODULES_ABSENT`, which is a truthful report in a format nobody interrogated.
--
-- So orphan modules get imported here rather than left to be picked up by whoever
-- remembers to name them. If one of these goes red the ROOT goes red, which is the
-- entire point: that is the signal that was missing. Do not remove an import here to
-- make the root build green -- that restores the blindness rather than fixing the break.
--
-- Check for new orphans with `validation/code/check.py`, which
-- compares the TRANSITIVE closure of this file against every source module on disk.
--
-- A caution about HOW to run that check, learned by getting it wrong here: comparing the
-- files on disk against the imports named IN THIS FILE reports false orphans, because most
-- modules are reached TRANSITIVELY. `BundleRigidity.CoverageInvariance`, `.EntropySplit`,
-- `.Freshness` and `.Realizability` are named nowhere in this file and are all in the
-- closure anyway, via `FoldedSpectrum -> ConditionalGain`. Only a genuine transitive
-- closure distinguishes an orphan from a module someone else already imports;
-- `DeploymentCeiling`, added above, was the only real one.
import Descent.Spectral.ResonanceSpectrum
import Descent.Blindness.BundleRigidity.Coverage
import Descent.Blindness.BundleRigidity.Cycles
import Descent.Blindness.BundleRigidity.DeploymentCeiling
import Descent.Blindness.BundleRigidity.Dichotomy
import Descent.Blindness.BundleRigidity.LinearSCM
import Descent.Blindness.BundleRigidity.Operator
import Descent.Blindness.BundleRigidity.SingleModulus
import Descent.Blindness.BundleRigidity.Telescope
import Descent.Blindness.BundleRigidity.TwoAtom

namespace Descent

/-- The pioneer share map is the same saturation coordinate already used for coalescent time.
The arguments have different biological meanings, but the common algebraic map is made explicit
rather than left as two silently parallel formulas. -/
theorem pioneerWeightFraction_eq_fstFromTau (w : ℝ) :
    XiFromMarks.pioneerWeightFraction w = fstFromTau w := rfl

/-- The same saturation coordinate also appears in the migration/LD chart; this identity keeps
the shared formula explicit without conflating the three scientific arguments. -/
theorem pioneerWeightFraction_eq_sharedLDFromMigration (w : ℝ) :
    XiFromMarks.pioneerWeightFraction w = sharedLDFromMigration w := rfl

/-! ### One formula, several readings

Each theorem below records that two definitions in different modules compute the same
function.  The arguments they serve are different -- that is why both names exist -- but the
identity is stated rather than left for a reader to notice, so a correction to either side
that does not reach the other stops the build. -/

/-- The pooled-environment correlation is a convex combination, and so is the average phase
interaction: mass on the first argument, the rest on the second. -/
theorem averagePhaseInteraction_eq_pooledEnvironmentCorrelation
    (freq_cis interaction_cis interaction_trans : ℝ) :
    averagePhaseInteraction freq_cis interaction_cis interaction_trans =
      pooledEnvironmentCorrelation interaction_cis interaction_trans freq_cis := by
  unfold averagePhaseInteraction pooledEnvironmentCorrelation
  ring

/-- The ancestry-specific effect is the same convex combination at the ancestry weight. -/
theorem ancestrySpecificEffect_eq_pooledEnvironmentCorrelation
    (beta_pop1 beta_pop2 alpha : ℝ) :
    ancestrySpecificEffect beta_pop1 beta_pop2 alpha =
      pooledEnvironmentCorrelation beta_pop1 beta_pop2 alpha := by
  unfold ancestrySpecificEffect pooledEnvironmentCorrelation
  ring

/-- The spike-and-slab variance is the same convex combination at the slab probability. -/
theorem spikeAndSlabVariance_eq_pooledEnvironmentCorrelation
    (pi sigma_sq_large sigma_sq_small : ℝ) :
    spikeAndSlabVariance pi sigma_sq_large sigma_sq_small =
      pooledEnvironmentCorrelation sigma_sq_large sigma_sq_small pi := by
  unfold spikeAndSlabVariance pooledEnvironmentCorrelation
  ring

/-- The overlap-gap profile of the metric chart is the landscape's population overlap
profile: one formula, read once as a metric and once as a landscape. -/
theorem ogpOverlapProfile_eq_populationOverlapProfile (q x : ℝ) :
    ogpOverlapProfile q x = populationOverlapProfile q x := rfl

/-- The epoch sample size of the metric chart is the epoch lineage sample size. -/
theorem epochSampleSize_eq_epochLineageSampleSize (K : ℕ) :
    epochSampleSize K = epochLineageSampleSize K := rfl

/-- **The overlap and the squared norm are one inner product, at their own dimensions.**

`configurationOverlap` pairs two two-coordinate configurations and `transplantSqNorm` pairs a
three-coordinate displacement with itself.  Written out they are the same construction, and
the corpus's same-quantity screen groups them for it -- correctly, since neither file states
what the other computes.  No equation between them typechecks: they live at `Fin 2` and
`Fin 3`.  What can be stated is what each one is, together, and that is this. -/
theorem configurationOverlap_and_transplantSqNorm_are_dotProduct
    (configuration : TwoCoordinateConfiguration) (displacement : Fin 3 → ℝ) :
    configurationOverlap configuration configuration = dotProduct configuration configuration ∧
      transplantSqNorm displacement = dotProduct displacement displacement :=
  ⟨rfl, rfl⟩

/-- The two-state kernel that never moves is the one-hot weight on `Fin 2`: one on the
diagonal, zero off it, whichever way the equality is written. -/
theorem stayKernel_eq_oneHotWeight (i j : Fin 2) :
    stayKernel i j = oneHotWeight (R := ℝ) i j := by
  unfold stayKernel oneHotWeight
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The context-preserving transition is that same one-hot weight. -/
theorem persistentTransition_eq_oneHotWeight (x y : BinaryBiologicalState) :
    persistentTransition x y = oneHotWeight (R := ℝ) x y := by
  unfold persistentTransition oneHotWeight
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The readout quality and the context-preserving transition are one Kronecker delta. -/
theorem contextMatchQuality_eq_persistentTransition (x y : BinaryBiologicalState) :
    contextMatchQuality x y = persistentTransition x y := rfl

/-- And it is the one-hot weight, which is the third name for that delta. -/
theorem contextMatchQuality_eq_oneHotWeight (x y : BinaryBiologicalState) :
    contextMatchQuality x y = oneHotWeight (R := ℝ) x y := by
  rw [contextMatchQuality_eq_persistentTransition, persistentTransition_eq_oneHotWeight]

/-- The stable sieve dimension and the condensation critical degree are the same logarithmic
law, at different arguments: `log L / κ` and `log N / c`. -/
theorem stableSieveDimension_eq_criticalDegree (kappa L : ℝ) :
    SpectrumIdentifiability.stableSieveDimension kappa L = criticalDegree L kappa := rfl

/-
THE WARNING WAS ALREADY WRITTEN DOWN. READ THE PROSE NEXT TO WHAT YOU ARE ABOUT
TO CHANGE, BEFORE YOU CHANGE IT.

On 2026-08-02 three separate defects were introduced, and in ALL THREE the
corpus already contained a correct, specific warning ADJACENT to the mistake.
None of them was a documentation gap. Each was a failure to read documentation
that was already there, at the moment of acting.

  * `validation/extract/coverage_v2.context()` says in its own docstring:
    "168 definitions reported 'could not compile body' here purely because this
    file called translate_def bare." A later audit called the translator bare
    one file over, reported 283 definitions blocked and 31 of them blocked on
    `Pop`, and proposed building `Pop` support. Through the shared context the
    real numbers were 213 blocked and ZERO on `Pop` -- `emit.build_context`
    registers `Pop` already. The whole lever was an artefact of the
    under-provisioned call the docstring warns about.

  * A `DGP.lean` docstring three lines above a deletion site NAMED the consumer
    of the declaration being deleted, while a grep for the bare identifier
    found nothing.

  * An ordering comment above a `field_simp` block in `PortabilityDrift`
    explained why two passes had to stay separate. A commit titled "Finish ...
    in one field pass" merged them and regressed a green proof.

  * AND THE WORST OF THE FOUR, BECAUSE PROXIMITY DID NOT HELP: in
    `validation/differential/corpus.py`, `_all_modules()` carries a comment
    saying that `Descent.lean` is a SIBLING of `Descent/` and that
    a dead-code scan with exactly this blind spot deleted `decaySlope` and
    `LDDecayMechanism` as unreferenced. Forty lines below, `_leanexpr_table()`
    reconstructed the path as `join(CORPUS, mod + ".lean")` and reintroduced
    the assumption the comment was written to prevent. The documentation of the
    bug and the bug were in the same file, in a pair of functions that must
    agree.

    THE OTHER THREE ARE "WARNING HERE, DEFECT THERE"; THIS ONE IS BOTH IN ONE
    PLACE, AND IT STILL FAILED. Proximity is the thing everyone assumes is
    sufficient, and it is not: A COMMENT CANNOT PROTECT CODE IT DOES NOT GATE.
    So the repair was not "read the comment above you" -- it was routing both
    halves through one `_module_path()`, so the two cannot disagree at all. When
    two places must agree, make one of them call the other; a note explaining
    why they must agree is not a mechanism.

AND THE INVERSE SHAPE, WHICH IS WORSE THAN ALL FOUR ABOVE: PROSE THAT IS NOT
IGNORED BUT IS WRONG. The four specimens are warnings that were correct and
went unread. This one is a note that was READ, TRUSTED, AND MISLEADING.

A DEFERRED-WORK NOTE IS A CLAIM, AND IT INHERITS THE ERROR RATE OF THE ANALYSIS
THAT PRODUCED IT. A paragraph in `Conventions.lean` told the next agent that
"the collapse to one name is the fix and has not been done", naming
`geometricDecay` as the name to keep and the other three as uses of it. It was
written from a NAME CENSUS, before the bodies had been read, and it survived
three commits looking like a decision already taken rather than a hypothesis.
Reading the four bodies reversed it: `admixtureLDDecay` is VALIDATED as the
`Nₑ → ∞` limit and MEASURED high by +0.24% to +0.37%, with a theorem proving
the bias is one-sided, so folding it would detach a measured regime from the
name that carries it. One function, four REFERENTS -- not four names for one
thing.

A "TODO" IS THE MOST AUTHORITATIVE-LOOKING SENTENCE IN A CODEBASE, because it
reads as a decision taken by someone who had looked, and the next sweep
executes it rather than re-deriving it. So a deferred-work note must carry the
evidence it rests on and say what would overturn it, exactly as a result must.
When one turns out wrong, WITHDRAW IT IN PLACE AND QUOTE WHAT IT USED TO SAY:
a withdrawn instruction with its reason is more useful than a clean paragraph,
because the clean paragraph loses the fact that a careful reader was misled
here once. Same discipline as the retracted 14-sigma row in the ledger.

WHY IT KEEPS HAPPENING, which is the part worth internalising: A WELL-FORMED
ARGUMENT FOR A FALSE PREMISE IS HARDER TO STOP THAN A WEAK ONE. The reasoning
survives inspection and the premise never gets inspected. "One mechanical
feature beats three" is a good argument; it moved two readers past a
thirty-second check of whether the feature was already implemented. When an
argument feels clean, that is the moment to re-derive its premise, not to act
on it.

AND WHEN A CHECK LOOKS LIKE IT PASSES, ASK WHICH AXIS IT MEASURES. Three
distinct ways a check can be dead were found in one day:
  (1) it CANNOT FIRE -- `prove_contained` documented a 'refuted' verdict its
      body never returns, so a caller branching on it got 0 of 137 and read it
      as a finding;
  (2) it FIRES ON THE WRONG AXIS -- a control asserting one definition
      translates passed under BOTH a bare and a provisioned translator, so it
      certified "the translator works" while the question was "is it
      provisioned as production provisions it";
  (3) its CONDITION IS INERT -- `ceiling.py` chose between call-graph
      candidates with `X if len(...) == 1 else X`, both branches identical, so
      ambiguity was silently resolved to whichever came first.
The third is the hardest to see by reading, because the shape of the intent
survives while the intent itself is gone.

AND A FIFTH SHAPE, WHICH IS THE ONE THAT PRODUCES CONFIDENT WRONG NUMBERS:
A COUNT TAKEN FROM A TRUNCATED LISTING IS NOT A COUNT. Four instances in one
day, each reporting a number that quietly answered a narrower question than the
one asked:
  * `grep -o` ate the trailing subscript of `div_lt_div_iff₀`;
  * `grep -c AGREE` also matched DISAGREE, overstating agreement by exactly the
    disagreement count;
  * an enumeration pattern required a character BEFORE the name it searched
    for, so it could not match the base name it was enumerating -- it returned
    eight derived names and none of the 149 bare occurrences, and looked
    complete;
  * `grep ... | head` reported "two consumers" of the generated tables; there
    were three, and the third would have died on an unexplained ImportError.
      The count was stated as fact in a commit message.

THE FIFTH SHAPE HAS A SECOND AND MORE DANGEROUS FACE:
A SEARCH STRING THAT DOES NOT MATCH IS INDISTINGUISHABLE FROM AN ABSENT
FEATURE. The first face over-counts or under-counts, and you notice eventually
because the number looks wrong. This one returns ZERO, and zero reads as
knowledge rather than as a failed query.

  * `git log -S` returned nothing for `LDDecayMechanism` and was read as "this
    never existed". It existed. That nearly deleted a valid theorem and
    rewrote a correct citation to point at a weaker result.
  * Verifying that a note had landed, a grep for the ALL-CAPS phrasing from the
    commit message found 0 against mixed-case text in the file -- twice read as
    "the edit did not land", inside the very commit that documents this class.
    Writing the lesson down is not the same as being protected by it.
  * And once more, verifying THAT paragraph: a line-oriented `grep` for a
    phrase that WRAPS ACROSS TWO LINES in this file returned 0. Not case, not
    truncation -- line breaks. Three different mechanisms, all reporting the
    same confident zero, within one hour.

THE DISCRIMINATOR IS THE SAME FOR BOTH FACES, AND IT IS CHEAP: RUN THE QUERY A
SECOND WAY AND REQUIRE THE TWO TO AGREE. Case-insensitively as well as
case-sensitively; by content as well as by name; without the pipe as well as
with it. A single query answering zero is a hypothesis, not a result. Two
queries of different shape agreeing on zero is a result.

TWO GUARDS THAT CHECK SOMETHING ADJACENT TO WHAT THEY ARE NAMED FOR, both
verified the hard way:
  * `$?` AFTER A PIPE REPORTS THE PIPE. `cmd | head; echo $?` gives head's
    status, so a "fails loudly, exits non-zero" claim checked that way is not a
    claim about `cmd` at all. Check the exit code in a separate run with no
    pipe. This was caught while verifying a fix for the truncation class above,
    which is the same trap one level up.
  * `git commit -F msg.txt -- <path>` DOES NOT COVER ADDITIONS. It refuses on an
    untracked file (`pathspec did not match any file(s) known to git`), so a
    commit that adds a file must `git add` first -- which reopens the shared
    index window the pathspec form exists to close. On any commit that adds
    files, inspect `git diff --cached --name-status` by hand before committing.
-/

/-- The two-locus block has exactly two loci, so the `2 ≤ t` premise carried by the
two-locus coalescent theorems in `Descent.PopGen.DGP` is discharged here by computation.
It was previously supplied as a `local instance : Fact (2 ≤ 2)`; a `Fact` instance is
resolved silently and so kept the premise out of every signature that depended on it. -/
theorem two_le_two : (2 : ℕ) ≤ 2 := le_refl 2

/-
Proof policy: do not add theorems whose conclusion merely repackages a premise
by trivial algebra, rewriting, or conjunction-introduction. Such statements add
noise without adding usable mathematical content and should be deleted rather
than retained as named results.
-/


/-! The two specialisations below repeat their `DGP` originals' hypothesis blocks, and the
duplication guard reports that.  It stands: what they add is `t := 2`, discharged by
`two_le_two`, and a specialisation's statement IS its hypotheses at the fixed dimension --
there is nothing to factor that would leave the specialisation saying anything.  Deleting
them would remove a result rather than a duplicate, which is the distinction the primed
restatements deleted above did not have: those fixed nothing. -/

/-- Concrete `2 × 2` specialization of the two-locus coalescent covariance-gap theorem. -/
theorem twoLocusCoalescent_covariance_gap_lower_bound_dim_two
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_time : tSource ≤ tTarget) :
    2 *
        (ibdWeight * discreteRecombinationSurvival recombRate tSource *
          (1 - discreteRecombinationSurvival recombRate (tTarget - tSource))) ^ 2 ≤
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix two_le_two ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix two_le_two ibdWeight recombRate tTarget) :=
  twoLocusCoalescent_covariance_gap_lower_bound
    two_le_two ibdWeight recombRate tSource tTarget h_time

/-- Concrete `2 × 2` positivity corollary for the two-locus coalescent witness. -/
theorem covariance_mismatch_pos_of_twoLocusCoalescent_dim_two
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    0 <
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix two_le_two ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix two_le_two ibdWeight recombRate tTarget) :=
  covariance_mismatch_pos_of_twoLocusCoalescent
    two_le_two ibdWeight recombRate tSource tTarget
    h_ibd_pos h_recomb_pos h_recomb_lt_one h_time


/-- The true derivative of expected Brier score with respect to `p`,
    proved via the quadratic-form derivative in `Conclusions`. -/
theorem expectedBrierScore_deriv_proved (p π : ℝ) :
    deriv (fun x ↦ expectedBrierScore x π) p = 2 * (p - π) :=
  expectedBrierScore_deriv p π

/-- Concrete 2x2 matrix representing independent LD. -/
def sigmaS : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, 1]]

/-- Concrete 2x2 matrix representing perfectly correlated LD. -/
def sigmaT : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 1], ![1, 1]]

/-- Source cross-covariances. -/
def crossS : Fin 2 → ℝ := ![1, 0]

/-- The truth configuration of the overlap-energy witness is the cross-population selector. -/
theorem overlapEnergyTruth_eq_crossS : overlapEnergyTruth = crossS := rfl

/-- The positive configuration is the reordering score. -/
theorem overlapEnergyPositive_eq_reorderScore : overlapEnergyPositive = reorderScore := rfl

/-- And it is the two-ancestry conditional, which is the third name for `![0, 1]`. -/
theorem overlapEnergyPositive_eq_twoAncestryConditional :
    overlapEnergyPositive = twoAncestryConditional := rfl

/-! Target cross-covariances were restated here as `crossT`. The same witness
vector `![1, 1]` is `DGP.ldWitnessTargetCross`, and the restatement has been
deleted so that the two `2 × 2` witnesses in this development are one witness. -/

/-- Another target LD matrix with a different correlation structure. -/
def sigmaT2 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0.5], ![0.5, 1]]

/-- **The root's `2 × 2` target witness is `DGP`'s, proved rather than asserted.**

Source LD is independent, so `sigmaS` is the identity and the source ERM weight vector is
the source cross-covariance `crossS` itself. Carrying that weight through the perfectly
correlated target LD `sigmaT` gives the target cross-covariance, and the vector it gives is
`DGP.ldWitnessTargetCross`.

The note above says the local restatement was removed so that the two `2 × 2` witnesses in
this development would be one witness. Removing a name does not by itself make that true:
it leaves two files whose numbers happen to agree. This is the statement that carries it, so
a change to either side is a contradiction rather than a divergence nobody notices. -/
theorem sigmaT_mulVec_crossS_eq_ldWitnessTargetCross :
    sigmaT.mulVec crossS = ldWitnessTargetCross := by
  ext i
  fin_cases i <;>
    simp [sigmaT, crossS, ldWitnessTargetCross, Matrix.mulVec, dotProduct]

/-- A concrete proof that the source ERM is LD-specific and does not solve
    the target normal equations under a new correlation structure. The mismatch is
    exhibited by explicit `2 × 2` witnesses rather than assumed as a hypothesis. -/
theorem source_erm_solves_source_not_target_normal_equations :
    let wS : Fin 2 → ℝ := ![1, 0]
    sigmaS.mulVec wS = crossS ∧
    sigmaT2.mulVec wS ≠ ldWitnessTargetCross := by
  intro wS
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
    · simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · intro heq
    have h : (sigmaT2.mulVec wS) 1 = ldWitnessTargetCross 1 := congrFun heq 1
    revert h
    simp [wS, sigmaT2, ldWitnessTargetCross, Matrix.mulVec, dotProduct]
    norm_num

/-- A concrete proof that ERM mismatch occurs under LD shift, without assuming an
    abstract system-conflict hypothesis.
    Here we construct explicit 2x2 covariance and cross-covariance matrices
    and show that the weights solving the normal equations must strictly differ. -/
theorem source_target_erm_differ_proved :
    let wS : Fin 2 → ℝ := ![1, 0]
    let wT : Fin 2 → ℝ := ![1/2, 1/2]
    sigmaS.mulVec wS = crossS ∧
    sigmaT.mulVec wT = ldWitnessTargetCross ∧
    wS ≠ wT := by
  intro wS wT
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [wS, sigmaS, crossS, Matrix.mulVec, dotProduct]
  · ext i
    fin_cases i <;>
      simp [wT, sigmaT, ldWitnessTargetCross, Matrix.mulVec, dotProduct] <;> ring
  · intro heq
    have h : wS 0 = wT 0 := congrFun heq 0
    simp [wS, wT] at h


/-- Rigorous `2 × 2` target-`R²` drop proof using the two-locus coalescent witness. -/
theorem target_r2_drop_of_twoLocusCoalescent_dim_two
    (mseSource mseTarget varY lam : ℝ)
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_mse_gap_lb :
      lam *
          frobeniusNormSq
            (twoLocusCoalescentCovarianceMatrix two_le_two ibdWeight recombRate tSource -
              twoLocusCoalescentCovarianceMatrix two_le_two ibdWeight recombRate tTarget) ≤
        mseTarget - mseSource)
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY :=
  target_r2_drop_of_twoLocusCoalescent
    two_le_two mseSource mseTarget varY lam
    ibdWeight recombRate tSource tTarget
    h_mse_gap_lb h_lam_pos h_varY_pos
    h_ibd_pos h_recomb_pos h_recomb_lt_one h_time

section NoAxioms

variable {t : ℕ}

/-! `covariance_mismatch_pos_of_fst_and_sparse_array` and
`target_r2_drop_of_fst_and_sparse_array` were each restated here under a primed name, with
their binder blocks -- sixteen lines of hypotheses -- copied verbatim from `Descent.PopGen.DGP`
and a one-line proof citing the original.

The restatements bought nothing.  Both originals are already in the `Descent` namespace,
so every importer of this root module could always write the unprimed name and get the same
theorem; what the copies added was two more places for a hypothesis to drift.  A restatement
earns its keep when it discharges a premise or changes the dimension -- as the `_dim_two`
specialisations above do, instantiating `t := 2` -- and these did neither. -/

/-! ### `ld_decay_implies_nonlinear_calibration_of_exp_tagging` -- READ BEFORE TOUCHING ITS INPUTS

This theorem is the consumer of `LDDecayMechanism` and `decaySlope` in
`Descent.PopGen.DGP`, and it is the ONLY one. It also lives in `Descent.lean`, the
corpus root, one directory *above* `Descent/`.

That combination has already destroyed both definitions once. A dead-code scan walking
only `Descent/` reported `decaySlope` as having "no use anywhere and no theorem
about them" and deleted it; a second pass then deleted `LDDecayMechanism` as having "lost
its only consumer". Both premises were false, and the second inherited the first's error.

**The deletion did not break the build, and that is the dangerous part.** Lean auto-binds
an undefined bare name as an implicit variable rather than reporting it missing, so this
theorem kept elaborating -- with `mech` an arbitrary inhabitant of an arbitrary type and
`decaySlope` an arbitrary function, every hypothesis about them constraining nothing. It
sat here green, among the headline results, as a well-formed claim about nothing, until
an application finally demanded a function. So for this class of name the build cannot
detect the breakage: ABSENCE OF A BUILD FAILURE IS NOT EVIDENCE THAT A DELETION WAS SAFE.

It compounded with a second blind spot: this root module was outside the import closure of
every build target, so nothing elaborated the declaration either way. Two independent
instruments were blind at once.

If you are removing something as unreferenced, grep the full `proofs/` tree INCLUDING this
file and the validation Python -- and grep the surrounding prose too. The section docstring
three lines above the deletion site in `DGP.lean` named this theorem by its full path the
entire time; only the identifier search missed it.
-/

/-- Rigorous proof that exponential LD decay cannot be fit by a linear slope calibration.
    Non-affineness is derived from three explicit distances rather than assumed. -/
theorem ld_decay_implies_nonlinear_calibration_of_exp_tagging {k : ℕ} [Fintype (Fin k)]
    (mech : LDDecayMechanism k)
    (lambda : ℝ) (h_lambda_pos : 0 < lambda)
    (h_tagging : mech.tagging_efficiency = fun d ↦ Real.exp (-lambda * d))
    (c0 c1 c2 : Fin k → ℝ)
    (hd0 : mech.distance c0 = 0)
    (hd1 : mech.distance c1 = 1)
    (hd2 : mech.distance c2 = 2) :
    ∀ (beta0 beta1 : ℝ),
      (fun c ↦ beta0 + beta1 * mech.distance c) ≠
        (fun c ↦ decaySlope mech c) := by
  intro beta0 beta1 h_eq
  have h0 := congr_fun h_eq c0
  have h1 := congr_fun h_eq c1
  have h2 := congr_fun h_eq c2
  unfold decaySlope at h0 h1 h2
  rw [h_tagging] at h0 h1 h2
  rw [hd0] at h0
  rw [hd1] at h1
  rw [hd2] at h2
  simp only [mul_zero, Real.exp_zero, mul_one, add_zero] at h0 h1 h2
  have h_b1 : beta1 = Real.exp (-lambda) - beta0 := by linarith
  have h_b0 : beta0 = 1 := by linarith
  rw [h_b0] at h_b1
  have h_2 : 1 + 2 * (Real.exp (-lambda) - 1) = Real.exp (-lambda * 2) := by linarith
  have h_exp_sq : Real.exp (-lambda * 2) = (Real.exp (-lambda))^2 := by
    rw [mul_comm, ← Real.exp_nat_mul]
    norm_cast
  rw [h_exp_sq] at h_2
  have h_quad : (Real.exp (-lambda) - 1)^2 = 0 := by
    calc (Real.exp (-lambda) - 1)^2
      _ = (Real.exp (-lambda))^2 - 2 * Real.exp (-lambda) + 1 := by ring
      _ = 1 + 2 * (Real.exp (-lambda) - 1) - 2 * Real.exp (-lambda) + 1 := by rw [← h_2]
      _ = 0 := by ring
  have h_exp_eq_one : Real.exp (-lambda) = 1 := by
    have h_zero : Real.exp (-lambda) - 1 = 0 := sq_eq_zero_iff.mp h_quad
    linarith
  have h_lambda_zero : -lambda = 0 := by
    have h_exp_zero : Real.exp 0 = 1 := Real.exp_zero
    rw [← h_exp_zero] at h_exp_eq_one
    exact Real.exp_injective h_exp_eq_one
  linarith

end NoAxioms

section Condensation

/-!
### A VERIFICATION HAZARD: a green build certifies only the tree that was compiled

Recorded here because it is not a Lean fact and will not be caught by anything in this file,
and because the failure was silent in the place anyone would look for it.

`lake build` reported **"Build completed successfully (7368 jobs)"** immediately below a
`git merge` that had **aborted** with "Please commit your changes or stash them before you
merge." The build was real; it was a build of the tree *without* the commit under test. Read
bottom-up, it certified work that had never been compiled.

**The corroborating detail was itself the artifact.** The job count had risen, 7364 → 7368,
which reads as evidence that the new material was picked up. It was not: other modules had
moved. A number that moves in the expected direction is not confirmation that the expected
thing happened.

The same shape one level down, in the same session: a relay invocation ending
`shasum: command not found` returned **exit status 0** while the `&&` chain had died before
`lake` ever ran, so an empty error list meant "no build" rather than "no errors".

Two habits follow, and they are cheap:

* after any build on a shared checkout, confirm **which tree** was compiled — the module's
  `.olean` mtime against the wall clock is enough, and it is what settled it here;
* never read a build verdict from an exit status or from the absence of error lines. Require
  the positive string, and require it to be *about the file you changed*.

This is the fourth specimen of one disease: evidence that fits while answering a different
question. It is the one where the false evidence looked like confirmation rather than like
absence, which is why it is the most dangerous of the four.
-/

/-!
### Concrete specializations of the condensation results

Same policy as the rest of this file: only specializations that instantiate a general
theorem at genuine numbers, not restatements.
-/

/-- A genome-scale **additive** score at a balanced locus is strictly subcritical:
`1 < log (10 ^ 6) / c(1/2)`. The Gaussian score apparatus of
`Descent.Portability.ScoreDistribution` applies with enormous margin, and this is the concrete
witness that the condensation theory does not disturb it. -/
theorem additive_score_subcritical_at_balanced_locus_proved :
    1 < maxSafeEpistaticOrder 1000000 (1 / 2) := by
  have hc : 0 < hweMellinDrift (1 / 2) := by
    rw [hweMellinDrift_half]
    exact Real.log_pos (by norm_num)
  refine additive_score_is_subcritical hc ?_
  rw [hweMellinDrift_half]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Pairwise epistasis at a sufficiently rare variant is supercritical for a
million-term aggregate: the Gaussian surrogate converges to a different limit. -/
theorem pairwise_epistasis_supercritical_proved :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 8 ∧
      Real.log 1000000 < 2 * hweMellinDrift q :=
  exists_maf_supercritical (by norm_num) (by norm_num)

/-- The hard-call lattice point produces a strictly inflated exceedance intensity, so
hard calls and dosage surrogates are not exchangeable at high epistatic order. -/
theorem hardCall_lattice_inflation_proved :
    1 < latticeInflation hardCallLatticeSpan :=
  hardCall_intensity_inflated

/-- The expander frustration floor is a genuine constant above `0.127`, so the
non-bipartite twin sits a constant total-variation distance from every globally
realizable system. -/
theorem frustration_floor_proved : (0.127 : ℝ) < expanderAgreementFloor :=
  expanderAgreementFloor_gt

/-!
### The bundle-rigidity modules are one development

Each of `Coverage`, `CoverageInvariance`, `Realizability` and `SingleModulus` imports only
Mathlib, which is what makes them readable in isolation and also what leaves each of them
unable to contradict any of the others. The two statements below are stated here, the one
place that sees all four, and each is an identification rather than a restatement: it says
two independently written objects are one object.
-/

/-- **Coverage is charge at one slot.**

`CoverageInvariance.chargedTuples` asks that every slot of a tuple have some branch landing
on that slot's value; `Coverage.coverers` asks that a single parameter have some branch
landing on one value. At one slot these are the same condition, so the support-only theorem
that `CoverageInvariance` proves about charge is a theorem about the coverers that
`Coverage`'s single window is built from — not a parallel fact about a similar-looking set. -/
theorem chargedTuples_one_slot_iff {T : Type*} [TopologicalSpace T] {d : ℕ}
    (F : BundleRigidity.ModulusFamily T d) (S : Set T) (v : ℝ) (t : Fin 1 → T) :
    t ∈ BundleRigidity.chargedTuples (fun j x ↦ F.curve j x) {u | u 0 ∈ S} (fun _ ↦ v)
      ↔ t 0 ∈ F.coverers S v := by
  unfold BundleRigidity.chargedTuples BundleRigidity.ModulusFamily.coverers
  simp [Fin.forall_fin_one]

/-- **The symmetric lift's two atom magnitudes are the two sides of a single-modulus
family.**

`Realizability.outerAtom v` is `√(1 + v)` and `Realizability.innerAtom v` is `√(1 - v)`,
introduced there as the magnitudes a symmetric lift uses. `SingleModulus.sq_cases` proves
that every atom of a modulus-`v` family squares to `1 + v` or to `1 - v` and to nothing
else. So the lift is not choosing a parameterization: the only two magnitudes available to
it are the two the dichotomy already forces, and a change to either file's constant is a
contradiction here. -/
theorem singleModulus_atom_sq_eq_realizability_atom_sq {d : ℕ} {v : ℝ}
    (S : BundleRigidity.SingleModulus d v) (hv : 0 ≤ v) (hv1 : v ≤ 1) (j : Fin d) :
    S.atom j ^ 2 = BundleRigidity.outerAtom v ^ 2 ∨
      S.atom j ^ 2 = BundleRigidity.innerAtom v ^ 2 := by
  rw [BundleRigidity.outerAtom_sq hv, BundleRigidity.innerAtom_sq hv1]
  exact S.sq_cases j

/-- **The coupling order is a polynomial grade, and the deployment cost is the benchmark
sample size at that grade.**

`DeploymentCeiling.sampleCost η C k` is `(C/η)^(2k)`, the samples needed to resolve a
direction whose coupling order is `k` from the guarantee `σ_min ≥ (η/C)^k`.
`PowerAnalysis.fixedGradeBenchmarkSampleSize ε K c` is `ε^(-(K/c))`, the sample size that
inverts a fixed-grade risk benchmark. They are the same number at accuracy `η/C`, grade
`2k` and constant `1`.

That is the statement behind the ceiling's own reading of the published cost. Quadratic in
`1/η` is grade `2`, which is `k = 1`; the geometric degradation in `k` is the grade rising,
not a separate phenomenon. Without this the two power laws are two power laws, and the
claim that one specialises the other is prose. -/
theorem sampleCost_eq_fixedGradeBenchmarkSampleSize (η C : ℝ) (k : ℕ)
    (hη : 0 < η) (hC : 0 < C) :
    BundleRigidity.sampleCost η C k
      = fixedGradeBenchmarkSampleSize (η / C) ((2 * k : ℕ) : ℝ) 1 := by
  unfold BundleRigidity.sampleCost fixedGradeBenchmarkSampleSize
  rw [div_one, Real.rpow_neg (div_pos hη hC).le, Real.rpow_natCast,
    div_pow, div_pow, inv_div]

/-- **The panel intensity and the squared characteristic function are one object.**

`ResonanceSpectrum.PhasePanel.intensity` is `|Ψ|²` written as `(∑ w cos)² + (∑ w sin)²`;
`CramerStratum.charFnSq` is `|φ|²` written as
`∑ᵤ ∑ᵥ wᵤ wᵥ cos(t(aᵤ − aᵥ))`. Expanding the
two squares and pairing the terms by `cos (x − y) = cos x cos y + sin x sin y` turns one
into the other exactly, at every panel and every frequency.

`ResonanceSpectrum` says in prose that these are the same object in two encodings, and that
the biological core is served by `CramerStratum` alone so that one argument has one home.
Both halves are better off with the identity written down: it is what makes "two encodings"
checkable, and it is what makes a divergence between them a failure here rather than two
files quietly computing different numbers under one name. It adds no dependence — the root
already imports both — and it gives `ResonanceSpectrum`'s graded spectrum a stated relation
to the dichotomy `CramerStratum` decides, should a result ever need the finer invariant. -/
theorem intensity_eq_charFnSq {n : ℕ} (P : PhasePanel n) (s : ℝ) :
    P.intensity s = charFnSq P.weight P.phase s := by
  unfold PhasePanel.intensity PhasePanel.cosPart PhasePanel.sinPart charFnSq
  rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [mul_sub, Real.cos_sub]
  ring

end Condensation

end Descent
