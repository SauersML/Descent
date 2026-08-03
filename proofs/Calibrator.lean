import Calibrator.Probability
import Calibrator.DGP
import Calibrator.Conclusions
import Calibrator.PortabilityDrift
import Calibrator.HumanDemography
import Calibrator.AdditiveInvariance
import Calibrator.Identification
import Calibrator.ImitationRigidity
import Calibrator.Conventions
import Calibrator.DemographicCapacity
import Calibrator.DriftRegime
import Calibrator.BlindnessRegistry
import Calibrator.OpenQuestions
import Calibrator.TransportIdentities
import Calibrator.SecondMomentShift
import Calibrator.QuadraticShift
import Calibrator.ProjectionShiftBounds
import Calibrator.WhiteningEquivalence
import Calibrator.PortabilityBounds
import Calibrator.MultiAncestryTheory
import Calibrator.StratificationConfounding
import Calibrator.AncestryCalibration
import Calibrator.LDDecayTheory
import Calibrator.SelectionArchitecture
import Calibrator.DemographicHistory
import Calibrator.ClinicalUtilityFairness
import Calibrator.VarianceComponents
import Calibrator.ScoreDistribution
import Calibrator.ValidationStatistics
import Calibrator.SimulationValidation
import Calibrator.SelectionValidation
import Calibrator.GeneticArchitectureDiscovery
import Calibrator.BayesianPGSTheory
import Calibrator.PhenomeWidePortability
import Calibrator.TransferLearningPGS
import Calibrator.MetricSpecificPortability
import Calibrator.PopulationGeneticsFoundations
import Calibrator.GeneEnvironmentInterplay
import Calibrator.RareVariantPortability
import Calibrator.StatisticalGeneticsMethodology
import Calibrator.EquityAndImplementation
import Calibrator.EpistasisAndNonAdditivity
import Calibrator.PolygenicAdaptation
import Calibrator.AssortativeMatingPGS
import Calibrator.ImputationPortability
import Calibrator.LongitudinalPortability
import Calibrator.PowerAnalysis
import Calibrator.CovarianceStructure
import Calibrator.CausalInference
import Calibrator.CertificateGrading
import Calibrator.PencilEnvironment
import Calibrator.DirichletTransfer
import Calibrator.CountingInvariantBlindness
import Calibrator.CountingInvariantInstances
import Calibrator.PolygenicArchitecture
import Calibrator.SampleOverlapBias
import Calibrator.HaplotypeTheory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.AncestrySpecificPower
import Calibrator.PGSCalibrationTheory
import Calibrator.ObservationalCeiling
import Calibrator.Condensation
import Calibrator.CumulantBlindness
import Calibrator.JetBarrier
import Calibrator.LocalToGlobalCoherence
import Calibrator.HiddenConeAmbiguity
import Calibrator.LatentMechanismCollapse
import Calibrator.PolygenicSpectroscopy
import Calibrator.EpistaticChaos
import Calibrator.CondensationUnification
import Calibrator.CramerStratum
import Calibrator.FoldedSpectrum
import Calibrator.SpectralDegradation
import Calibrator.EnsembleChannel
import Calibrator.Permeability
import Calibrator.ErgodicCovariancePencil
-- THE BUILD MUST COVER ITS OWN CORPUS. Everything below was outside this root's import
-- closure, so `lake build Calibrator` never compiled it -- and a module the build never
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
-- Check for new orphans with the closure of this file's imports against the files on
-- disk; the count is 105 modules including this root, all 105 in its closure.
--
-- A caution about HOW to run that check, learned by getting it wrong here: comparing the
-- files on disk against the imports named IN THIS FILE reports false orphans, because most
-- modules are reached TRANSITIVELY. `BundleRigidity.CoverageInvariance`, `.EntropySplit`,
-- `.Freshness` and `.Realizability` are named nowhere in this file and are all in the
-- closure anyway, via `FoldedSpectrum -> ConditionalGain`. Only a genuine transitive
-- closure distinguishes an orphan from a module someone else already imports;
-- `DeploymentCeiling`, added above, was the only real one.
import Calibrator.ResonanceSpectrum
import Calibrator.BundleRigidity.Coverage
import Calibrator.BundleRigidity.Cycles
import Calibrator.BundleRigidity.DeploymentCeiling
import Calibrator.BundleRigidity.Dichotomy
import Calibrator.BundleRigidity.Operator
import Calibrator.BundleRigidity.SingleModulus
import Calibrator.BundleRigidity.Telescope
import Calibrator.BundleRigidity.TwoAtom

namespace Calibrator

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
    saying that `proofs/Calibrator.lean` is a SIBLING of `Calibrator/` and that
    a dead-code scan with exactly this blind spot deleted `decaySlope` and
    `LDDecayMechanism` as unreferenced. Forty lines below, `_leanexpr_table()`
    reconstructed the path as `join(CALIBRATOR, mod + ".lean")` and reintroduced
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

local instance : Fact (2 ≤ 2) := ⟨by decide⟩

/-
Proof policy: do not add theorems whose conclusion merely repackages a premise
by trivial algebra, rewriting, or conjunction-introduction. Such statements add
noise without adding usable mathematical content and should be deleted rather
than retained as named results.
-/


/-- Concrete `2 × 2` specialization of the two-locus coalescent covariance-gap theorem. -/
theorem twoLocusCoalescent_covariance_gap_lower_bound_proved
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_time : tSource ≤ tTarget) :
    2 *
        (ibdWeight * discreteRecombinationSurvival recombRate tSource *
          (1 - discreteRecombinationSurvival recombRate (tTarget - tSource))) ^ 2 ≤
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tTarget) :=
  twoLocusCoalescent_covariance_gap_lower_bound
    (t := 2) ibdWeight recombRate tSource tTarget h_time

/-- Concrete `2 × 2` positivity corollary for the two-locus coalescent witness. -/
theorem covariance_mismatch_pos_of_twoLocusCoalescent_proved
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    0 <
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tTarget) :=
  covariance_mismatch_pos_of_twoLocusCoalescent
    (t := 2) ibdWeight recombRate tSource tTarget
    h_ibd_pos h_recomb_pos h_recomb_lt_one h_time


/-- The true derivative of expected Brier score with respect to `p`,
    proved via the quadratic-form derivative in `Conclusions`. -/
theorem expectedBrierScore_deriv_proved (p π : ℝ) :
    deriv (fun x => expectedBrierScore x π) p = 2 * (p - π) :=
  expectedBrierScore_deriv p π

/-- Concrete 2x2 matrix representing independent LD. -/
def sigmaS : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, 1]]

/-- Concrete 2x2 matrix representing perfectly correlated LD. -/
def sigmaT : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 1], ![1, 1]]

/-- Source cross-covariances. -/
def crossS : Fin 2 → ℝ := ![1, 0]

/-! Target cross-covariances were restated here as `crossT`. The same witness
vector `![1, 1]` is `DGP.ldWitnessTargetCross`, and the restatement has been
deleted so that the two `2 × 2` witnesses in this development are one witness. -/

/-- Another target LD matrix with a different correlation structure. -/
def sigmaT2 : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0.5], ![0.5, 1]]

/-- A concrete proof that the source ERM is LD-specific and does not solve
    the target normal equations under a new correlation structure. The mismatch is
    exhibited by explicit `2 × 2` witnesses rather than assumed as a hypothesis. -/
theorem source_erm_is_ld_specific_proved :
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
  · ext i; fin_cases i <;> simp [wT, sigmaT, ldWitnessTargetCross, Matrix.mulVec, dotProduct] <;> ring
  · intro heq
    have h : wS 0 = wT 0 := congrFun heq 0
    simp [wS, wT] at h


/-- Rigorous `2 × 2` target-`R²` drop proof using the two-locus coalescent witness. -/
theorem target_r2_drop_of_twoLocusCoalescent_proved
    (mseSource mseTarget varY lam : ℝ)
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_mse_gap_lb :
      lam *
          frobeniusNormSq
            (twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tSource -
              twoLocusCoalescentCovarianceMatrix (t := 2) ibdWeight recombRate tTarget) ≤
        mseTarget - mseSource)
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY :=
  target_r2_drop_of_twoLocusCoalescent
    (t := 2) mseSource mseTarget varY lam
    ibdWeight recombRate tSource tTarget
    h_mse_gap_lb h_lam_pos h_varY_pos
    h_ibd_pos h_recomb_pos h_recomb_lt_one h_time

section NoAxioms

variable {t : ℕ}

/-- Abstract API wrapper: any concrete witness for the demographic covariance lower bound
    yields strict covariance mismatch in arbitrary matrix dimension. -/
theorem covariance_mismatch_pos_of_fst_and_sparse_array_proved
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ)
    (h_cov_lb :
      demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity kappa
        ≤ frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_fst : fstSource < fstTarget)
    (h_recomb_pos : 0 < recombRate)
    (h_sparse_pos : 0 < arraySparsity)
    (h_kappa_pos : 0 < kappa) :
    0 < frobeniusNormSq (sigmaSource - sigmaTarget) := by
  exact covariance_mismatch_pos_of_fst_and_sparse_array
    sigmaSource sigmaTarget fstSource fstTarget recombRate arraySparsity kappa
    h_cov_lb h_fst h_recomb_pos h_sparse_pos h_kappa_pos

/-- Abstract API wrapper: once a concrete witness supplies covariance and MSE lower bounds,
    target `R²` strictly drops in arbitrary matrix dimension. -/
theorem target_r2_drop_of_fst_and_sparse_array_proved
    (mseSource mseTarget varY lam : ℝ)
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ)
    (h_mse_gap_lb :
      lam * frobeniusNormSq (sigmaSource - sigmaTarget) ≤ mseTarget - mseSource)
    (h_cov_lb :
      demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity kappa
        ≤ frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_fst : fstSource < fstTarget)
    (h_recomb_pos : 0 < recombRate)
    (h_sparse_pos : 0 < arraySparsity)
    (h_kappa_pos : 0 < kappa) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY := by
  have h_mismatch : 0 < frobeniusNormSq (sigmaSource - sigmaTarget) :=
    covariance_mismatch_pos_of_fst_and_sparse_array_proved
      sigmaSource sigmaTarget fstSource fstTarget recombRate arraySparsity kappa
      h_cov_lb h_fst h_recomb_pos h_sparse_pos h_kappa_pos
  exact target_r2_strictly_decreases_of_covariance_mismatch
    mseSource mseTarget varY lam sigmaSource sigmaTarget
    h_mse_gap_lb h_lam_pos h_mismatch h_varY_pos

/-! ### `ld_decay_implies_nonlinear_calibration_proved` -- READ BEFORE TOUCHING ITS INPUTS

This theorem is the consumer of `LDDecayMechanism` and `decaySlope` in
`Calibrator.DGP`, and it is the ONLY one. It also lives in `proofs/Calibrator.lean`, the
corpus root, one directory *above* `proofs/Calibrator/`.

That combination has already destroyed both definitions once. A dead-code scan walking
only `proofs/Calibrator/` reported `decaySlope` as having "no use anywhere and no theorem
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
theorem ld_decay_implies_nonlinear_calibration_proved {k : ℕ} [Fintype (Fin k)]
    (mech : LDDecayMechanism k)
    (lambda : ℝ) (h_lambda_pos : 0 < lambda)
    (h_tagging : mech.tagging_efficiency = fun d => Real.exp (-lambda * d))
    (c0 c1 c2 : Fin k → ℝ)
    (hd0 : mech.distance c0 = 0)
    (hd1 : mech.distance c1 = 1)
    (hd2 : mech.distance c2 = 2) :
    ∀ (beta0 beta1 : ℝ),
      (fun c => beta0 + beta1 * mech.distance c) ≠
        (fun c => decaySlope mech c) := by
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
`Calibrator.ScoreDistribution` applies with enormous margin, and this is the concrete
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

end Condensation

end Calibrator
