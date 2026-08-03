#!/usr/bin/env python3
"""Model-family inventory: which families have a simulator, and which do not.

Run with the anaconda module (needs only stdlib + defs.json):
    module load python3/3.10.9_anaconda2023.03_libmamba
    python3 families.py

WHY FAMILIES RATHER THAN DEFINITIONS
    A modelling choice lives in a family, not in a definition. The island
    family has 8 definitions across 5 files that all compute 1/(1 + 4 Ne m) and
    none of them says it is the infinite-island limit -- so one simulator that
    varies the deme count settles all eight at once, and no amount of
    definition-by-definition checking would have grouped them.

    The number to drive to zero first is FAMILIES WITH NO SIMULATOR. A family
    with none is a blind spot with many definitions behind it, and it is
    invisible in a per-definition coverage percentage.

    The number to drive to zero SECOND is STATEMENTS IN NO FAMILY AT ALL. Those
    are worse than unsimulated: they are unclassified, so nobody has even said
    what generative process they are a claim about, and a per-definition
    coverage percentage hides them inside "unaccounted". This revision exists
    to drive that number down from 235.

MEMBERSHIP IS MECHANICAL WHERE IT CAN BE
    Families whose members were found by level-set invariance carry
    `found_by: sweep` and their membership is reproducible from
    sweep_inlined.py rather than from reading names. Families assembled by hand
    carry `found_by: manual` and are explicitly less trustworthy -- that
    distinction is recorded rather than smoothed over, because the whole point
    of the sweep was that names do not identify what a definition computes.

TWO BOOKKEEPING DEFECTS FIXED HERE, BOTH OF WHICH INFLATED THE HEADLINE
    1. IN-SLICE WAS COMPUTED BY SHORT NAME. `in_slice` was a set of short
       names, so an out-of-slice definition sharing a short name with an
       in-slice one (there are several: `total`, `fst`, `theta`, `tau`, `var`,
       `delta`, `retention`) was counted as an in-slice statement. Slice
       membership is now decided on the FULLY QUALIFIED name, and short names
       that resolve to more than one declaration are reported rather than
       silently merged.
    2. A FAMILY COULD "COVER" A DEFINITION IT DOES NOT REACH. Coverage was
       credited by short name too. Same fix.

    Both corrections move the headline. That is the point of making them; a
    number that only moves in the flattering direction is not being measured.

THE UN-SIMULATABLE LIST IS THE PLACE THIS WORK CAN QUIETLY FAIL
    Parking a definition as "no generative process" is a claim, and a claim
    needs a falsifier that is RUN. `UNSIMULATABLE` below is deliberately four
    entries long, and `falsify_unsimulatable` executes the test on every one of
    them and prints the result whether it fires or not. The test is stated in
    that function's docstring. A named-but-unrun falsifier reads as more
    careful than a bare assertion while being exactly as unfounded.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.normpath(os.path.join(HERE, "..", "..", "extract"))

SLICE_FILES = [
    "Calibrator/PortabilityDrift.lean",
    "Calibrator/DGP.lean",
    "Calibrator/PopulationGeneticsFoundations.lean",
    "Calibrator/LDDecayTheory.lean",
    "Calibrator/DemographicHistory.lean",
    "Calibrator/PhenomeWidePortability.lean",
    "Calibrator/PortabilityBounds.lean",
]

# ---------------------------------------------------------------------------
# OPERATIONAL PRECONDITIONS FOR EVERY SPEC BELOW.
#
# These are not housekeeping. Each one caused a MISDIAGNOSIS on this cluster
# today, and a spec that omits them produces simulators whose authors read the
# symptom as something else entirely.
#
#   O1  OUTPUT GOES UNDER /projects/standard/hsiehph/sauer354/, NEVER /tmp.
#       /tmp is node-local. The relay does not land on the same node twice --
#       three consecutive calls asking `hostname` and checking one path gave
#       PRESENT once and ABSENT twice, same path, same second. A log in /tmp is
#       therefore invisible to the call that checks it, and absence reads as
#       "the job never started". One agent spent several rounds concluding its
#       run had been killed while `pgrep` reported the process alive.
#
#   O2  UNIQUE FILENAME PER RUN. A fixed path leaves the previous run's log
#       impersonating this one's. Combined with O1, absence then genuinely
#       means not written, rather than not written HERE.
#
#   O3  AN EMPTY LOG IS NOT EVIDENCE OF A KILL. The claim that the relay tears
#       down the process tree on return was a misdiagnosis of O1. Keep
#       `setsid nohup ... & disown`; stop reading silence as death.
#
#   O4  PIN THE THREAD COUNT: OMP_NUM_THREADS=1, OPENBLAS_NUM_THREADS=1,
#       MKL_NUM_THREADS=1. numpy will otherwise take every core, and with
#       several agents on one node one agent's contention gets misdiagnosed as
#       another's deadlock. Anything heavier than a grep goes through srun or
#       sbatch, not the login node.
#
#   O5b AN IDENTIFIER COLLISION IN A MEMBERSHIP TEST ALWAYS OVER-COUNTS,
#       NEVER UNDER-COUNTS, SO IT ALWAYS FLATTERS. Matching members by SHORT
#       name merged thirteen out-of-slice declarations into the slice here --
#       `total`, `fst`, `theta`, `tau`, `var`, `delta`, `retention`,
#       `scoreMean` and more -- and the headline moved from "295" to 316 once
#       fully qualified. The direction is not luck: a collision adds spurious
#       matches to the NUMERATOR and leaves the denominator untouched. Any
#       membership or coverage join must key on the fully qualified name, and a
#       count that improved after a join was loosened should be assumed wrong.
#
#   O5  VECTORISE ONLY WHERE THE VECTORISED DRAW IS PROVABLY THE SAME DRAW.
#       The rule is not "vectorise over replicates"; it is that a batched
#       `multinomial` or `binomial` over a 2-D parameter array draws each
#       element from its own distribution independently, which makes it
#       provably the same experiment as the loop it replaces. Vectorising a
#       step that is NOT distributionally identical -- above all one that
#       shares random state across replicates -- buys speed by silently
#       correlating the replicates, and the error bars then mean nothing.
#       Every spec below that says "vectorised" means it in this sense, and a
#       simulator author who cannot state why their batched draw is the same
#       draw should write the loop.
#
# ---------------------------------------------------------------------------
# Families. `simulator` is None when nothing simulates the family yet -- that
# is the count to drive down, and an honest None is worth more than a
# simulator that only exercises the easy corner of a family.
#
# `spec` is the one-paragraph simulator specification: the process, the
# measured quantities, the analytic reference, and -- the part that decides
# whether the simulator is worth anything -- WHICH CONTROL ISOLATES WHICH
# FACTOR. A simulator that gets a product right by getting both factors wrong
# in compensating directions passes a combined control and fails split ones,
# so every spec names split controls where the reference is a product.
# ---------------------------------------------------------------------------
FAMILIES = [
    # =====================================================================
    # POPULATION-GENETIC FAMILIES (pre-existing; membership extended)
    # =====================================================================
    {
        "name": "drift_retention",
        "model": "closed population, no mutation; heterozygosity retained as "
                 "(1 - 1/(2Ne))^t",
        "simulator": "heavy/h0_heterozygosity_cluster.py",
        "status": "SIMULATED -- MODEL ERROR. Predicted retention 0.1352 at "
                  "t = 2*(2Ne); measured 1.0017 +/- 0.0036 at theta=8, both "
                  "controls green. Algebra correct, premise false.",
        "found_by": "sweep",
        "spec": "Wright-Fisher, no mutation, R replicates vectorised, one "
                "binomial call per generation over the whole replicate axis. "
                "Measure E[2p(1-p)] and E[p] over replicates. Reference "
                "H_t = H_0 (1-1/(2Ne))^t and F_ST = 1 - H_t/H_0. SPLIT "
                "CONTROLS: (a) Ne -> infinity must give retention exactly 1, "
                "isolating the drift factor from any bias in the "
                "heterozygosity estimator; (b) t = 0 must give F_ST exactly 0, "
                "isolating the estimator from the trajectory. CAN-FAIL: the t "
                "grid must reach t ~ 2Ne, where the exponential and the "
                "linearisation 1 - t/(2Ne) differ by 26%; a grid confined to "
                "t << Ne validates both and decides nothing. NOTE the running "
                "measurement already contradicts the reference -- that is a "
                "measurement about the FORMULA'S PREMISE (segregating-site "
                "conditioning), and the mentions query has to be run before "
                "any claim that the corpus is wrong.",
        "members": ["fstDerived", "heterozygosityLossFromDrift",
                    "ldRetainedFraction", "neutralDriftFactor",
                    "wrightFisherDriftRetention",
                    "wrightFisherHeterozygosityLoss", "hetRecurrence",
                    "cumulativeDrift", "heterozygosityLossVariableNe",
                    # newly classified
                    "founderHeterozygosityLoss", "harmonicMeanNe", "fstFromDriftFactor",
                    "targetHetFromFst", "targetHet", "retention",
                    "heterozygosityLoss", "alleleFreqDivergenceRate"],
    },
    {
        "name": "island_migration_fst",
        "model": "infinite island; F_ST = 1/(1 + 4 Ne m), no deme count",
        "simulator": "cluster/fam_coalescent.py (family_island)",
        "status": "SIMULATED -- varies deme count, which no member takes as an "
                  "argument",
        "found_by": "sweep",
        "spec": "d-deme symmetric island coalescent at scaled migration "
                "M = 4 Ne m; measure branch-mode Hudson F_ST between two "
                "demes. Reference 1/(1+M) at d -> infinity, "
                "1/(1 + M (d/(d-1))^2) at finite d. SPLIT CONTROLS: (a) m -> "
                "large panmicts the demes and F_ST -> 0, isolating the "
                "migration factor; (b) m = 0 recovers the pure-split family's "
                "t/(t+2Ne), isolating the drift factor -- the two together pin "
                "both arms of the migration-drift balance separately. CAN-FAIL: "
                "the d grid must include d = 2, where the finite-deme "
                "correction is 4x; a grid of large d validates the "
                "infinite-island limit by construction.",
        "members": ["islandModelFst", "asymmetricFst", "fstMigDriftEquil",
                    "fstMigrationDriftEquilibrium", "equilibriumFst",
                    "sharedLD_from_equilibrium",
                    "neutralAFBenchmarkFromRecurrence", "fstDriftMigration",
                    # newly classified
                    "alleleFreqAfterMigration", "bigM", "scaledMigration",
                    "scaledMigrationRate", "effectiveSymmetricMigration",
                    "effectiveMigration",
                    "fstMigDriftEq", "fstMigrationMutationEquilibrium",
                    "fstEqLimitLowMutationManyDemes",
                    "ldCorrelationFromMigration", "sharedLDFromMigration",
                    "signalRetentionMigrationDrift",
                    "retainedSignalVarianceMigrationDrift",
                    "migrationSharedBoostAt", "migBoost", "migrationLDBoost"],
    },
    {
        "name": "split_fst",
        "model": "clean split, constant sizes; Hudson F_ST = t/(t + 2 Ne)",
        "simulator": "cluster/fam_coalescent.py (family_split)",
        "status": "SIMULATED -- varies daughter sizes, which no member takes",
        "found_by": "sweep",
        "spec": "Clean split at time t, daughters of size Ne_A, Ne_B; measure "
                "branch-mode Hudson F_ST (mutation rate cancels in the ratio). "
                "Reference tau/(1+tau) with tau = t/(2Ne). SPLIT CONTROLS: "
                "(a) t = 0 gives F_ST = 0 identically, pinning the estimator; "
                "(b) Ne_A = Ne_B with t swept pins the time factor alone, so "
                "the size-asymmetry axis is the only remaining degree of "
                "freedom and cannot be absorbed by a compensating time error. "
                "CAN-FAIL: the daughter-size ratio must reach 16x, where a "
                "single-Ne formula and the harmonic-mean reading diverge; equal "
                "daughters validate both.",
        "members": ["coalFst", "fstFromGenerations", "fstFromTau",
                    "coalescentTau", "hudsonFstFromCoalescenceTimes",
                    "pairwiseFstFromBranchTaus", "pairwiseFstFromBranches"],
    },
    {
        "name": "mutation_drift_balance",
        "model": "infinite alleles; H* = theta/(1+theta), theta = 4 Ne mu",
        "simulator": "heavy/h0_heterozygosity_cluster.py (control 2)",
        "status": "SIMULATED -- equilibrium level confirmed at four theta",
        "found_by": "manual",
        "spec": "Wright-Fisher with two-way mutation at rate mu, vectorised "
                "over replicates; run to stationarity and measure E[2p(1-p)]. "
                "Reference H* = theta/(1+theta) and the approach "
                "H_t = H* + (H_0 - H*) lam^t with lam = (1-1/2Ne)(1-2mu). "
                "SPLIT CONTROLS: (a) mu = 0 must reproduce the pure drift "
                "family exactly -- isolates the drift arm; (b) Ne -> infinity "
                "must give the deterministic mutation equilibrium H = 1/2 with "
                "no drift term -- isolates the mutation arm. Without both, a "
                "simulator can land on theta/(1+theta) with a mutation rate "
                "that is wrong by the same factor its Ne is wrong by. CAN-FAIL: "
                "theta must span below and above 1; for theta >> 1 every "
                "candidate gives H ~ 1 and the grid decides nothing.",
        "members": ["hetEquilibrium", "expectedHeterozygosity",
                    "hetMutationDriftRecurrence", "hetTrajectory",
                    "hetStepWithMutation", "hetMutationFloor",
                    "scaledMutationRate", "hetDecayFactor",
                    "fstMutationDriftEquilibrium",
                    "fstMutationDriftTransient",
                    "fstMutationDriftTransientDiscrete",
                    # newly classified
                    "theta", "tau", "tauAt", "hetDecayFromScaled",
                    "hetMutationRecurrence", "hetRatioBetweenBranches",
                    "fstTransient", "fstTransientAt", "fstDriftMutation",
                    "expectedNewMutations", "sharedLDFractionFromMutation",
                    "mutationSharedRetentionAt", "mutErosion",
                    "mutationLDErosion", "covarianceDivergenceMutationDrift",
                    "presentDayPGSVarianceMutationDrift",
                    "presentDayR2MutationDrift"],
    },
    {
        "name": "ld_decay_recurrence",
        "model": "two loci, recombination c, drift; E[D] retention "
                 "(1-c)(1-1/2Ne) and E[r^2] at equilibrium",
        "simulator": "cluster/fam_ld_decay.py",
        "status": "SIMULATED -- two-locus Wright-Fisher, split controls on the "
                  "drift and recombination factors separately.",
        "found_by": "manual",
        "spec": "Two-locus Wright-Fisher on four haplotype frequencies, "
                "vectorised over replicates. Measure E[D_t]/D_0 per generation "
                "and sigma_d^2 = E[D^2]/E[pq(1-p)(1-q)] at stationarity. "
                "References: Hill-Robertson (1-c)(1-1/2Ne) per generation; "
                "Sved 1/(1+4Nc) versus Ohta-Kimura (10+rho)/((2+rho)(11+rho)) "
                "for sigma_d^2. SPLIT CONTROLS: (a) c = 0 forces decay to "
                "(1-1/2Ne)^t exactly, pinning the drift factor alone; (b) Ne "
                "enormous forces (1-c)^t exactly, pinning the recombination "
                "factor alone. CAN-FAIL: the c grid must straddle 1/(2Ne), and "
                "the rho grid must reach below 10, where Sved and Ohta-Kimura "
                "differ by more than 100%.",
        "members": ["ldRetentionPerGen", "ldAfterGenerations", "ldRecurrence",
                    "ldDecayRatePerGen", "ldHalfLife", "driftLDStep",
                    "driftLDRetention", "driftLDEquilibrium",
                    "driftLDTrajectory", "excessLDAfterBottleneck",
                    "bottleneckExcessLD", "driftLDCreationRate", "tagR2",
                    # newly classified
                    "ldRetention", "ldBreakageRate", "sharedLDRetention",
                    "taggingMismatchScale", "ohtaKimuraSigmaDSq", "decaySlope"],
    },
    {
        "name": "stepping_stone",
        "model": "1D lattice, nearest-neighbour migration; decay length and "
                 "F_ST versus distance",
        "simulator": "cluster/fam_stepping_stone.py",
        "status": "SIMULATED. Two engines: a Wright-Fisher frequency lattice "
                  "vectorised over replicates, and the two-lineage coalescent "
                  "on the circle solved exactly as a linear system with the "
                  "Monte Carlo walk of the same chain kept as a control. The "
                  "878% contradiction was resolved before this run by deleting "
                  "continuousSteppingStoneFst; the exponential is now measured "
                  "against the surviving hyperbolic form rather than argued "
                  "against. The migration kernel carries a jump size k, so "
                  "sigma^2 = k^2 is SET and not fitted -- this is the "
                  "fixed-sigma^2 experiment demoSteppingStoneFst's docstring "
                  "records as never having been done.",
        "found_by": "manual",
        "spec": "1D lattice of d demes, nearest-neighbour migration m, "
                "vectorised WF per deme; measure pairwise F_ST as a function "
                "of lattice distance and fit the decay length. Reference: "
                "Kimura-Weiss geometric decay with characteristic length "
                "sqrt(m/(2 mu)) in the continuous limit. SPLIT CONTROLS: "
                "(a) m -> large collapses the lattice to panmixia and every "
                "distance must give F_ST -> 0 -- isolates the migration arm; "
                "(b) d = 2 must reduce EXACTLY to the two-deme island result "
                "already simulated -- isolates the lattice geometry from the "
                "migration rate, and is the control that would have caught the "
                "500x error, since the island reduction fixes the scale that "
                "the characteristic-length formula gets wrong. CAN-FAIL: the "
                "distance grid must exceed the decay length, or every "
                "candidate decay law is linear on the sampled range.",
        "members": ["steppingStoneCharacteristicLength",
                    "continuousSteppingStoneFst", "demoSteppingStoneFst",
                    "steppingStoneCoalescenceTime", "steppingStoneFst",
                    "steppingStoneFstQuadratic",
                    # newly classified
                    "ldCorrelationDecay"],
    },
    {
        "name": "admixture",
        "model": "pulse admixture of two sources; F_ST and LD in the admixed "
                 "population",
        "simulator": "cluster/fam_admixture.py",
        "status": "SIMULATED. admixedFst is now run over three frequency "
                  "spectra rather than one frequency pair, with the ratio "
                  "decomposed into the exact per-locus numerator identity the "
                  "corpus proves and the denominator ratio it omits. The "
                  "admixture-LD definitions run on a two-locus haplotype pool "
                  "whose recombination and drift factors are pinned by "
                  "separate controls.",
        "found_by": "manual",
        "spec": "Two source demes diverged to a target F_ST, then a single "
                "admixture pulse at fraction alpha; measure F_ST of the "
                "admixed population against each source and admixture LD "
                "versus generations since the pulse. References: "
                "p_adm = alpha p_A + (1-alpha) p_B exactly; admixture LD "
                "D_t = alpha(1-alpha) dp_1 dp_2 (1-r)^t. SPLIT CONTROLS: "
                "(a) alpha = 0 or 1 must reproduce a source exactly, pinning "
                "the mixing arm with the LD arm switched off; (b) r = 0 must "
                "hold admixture LD constant forever, pinning the recombination "
                "arm with the mixing arm frozen. CAN-FAIL: alpha must be swept "
                "off 1/2, where alpha(1-alpha) is stationary and a wrong "
                "mixing exponent is invisible; and the frequency pairs must "
                "span the spectrum, since admixedFst's -44% error is a "
                "spectrum-average effect that a single frequency pair hides.",
        "members": ["admixedFst", "admixedAlleleFreq", "admixtureLD",
                    "admixtureLDDecay", "admixtureLDBoost",
                    "admixtureLDTwoLocus",
                    # newly classified
                    "introgressionVariants"],
    },
    {
        "name": "site_frequency_spectrum",
        "model": "standard neutral SFS, E[xi_i] = theta/i",
        "simulator": "cluster/fam_sfs.py",
        "status": "SIMULATED -- NO LONGER EMPTY. The family was recorded as "
                  "having no simulator AND no definitions after "
                  "singletonProportion was removed. The members were missing "
                  "because they do not have 'spectrum' in their names: "
                  "expectedNewMutations and expectedFreqDiffSq are both claims "
                  "about the frequency spectrum. FINDING: "
                  "expectedNewMutations (theta*t/2) is 215x to 4598x above "
                  "segregating sites in a sample and the ratio GROWS in t, "
                  "because the prediction is linear where the observable "
                  "saturates at Watterson's 1419.1. It is EXACT for mutations "
                  "that ARISE population-wide (2*Ne*mu*L*t); the docstring "
                  "names segregating sites and the sole consumer "
                  "sharedLDFractionFromMutation uses it as a per-locus Poisson "
                  "exponent. Scope declaration, not new arithmetic. "
                  "expectedFreqDiffSq is CONFIRMED once p0 is observed from "
                  "ancient samples and second moments are corrected for "
                  "sampling variance: -2.6%, -0.5%, +2.6%, with the "
                  "definition's own factor of 2 measured at 2.06, 1.98, 1.97.",
        "found_by": "manual",
        "spec": "Coalescent with mutation (msprime); measure the unfolded SFS "
                "and, for the two definitions, segregating sites younger than "
                "t and E[(p1-p2)^2] after a clean split with ANCIENT SAMPLES "
                "drawn from the ancestral population at the split time so p0 "
                "is observed rather than proxied. SPLIT CONTROLS: (a) spectrum "
                "SHAPE against theta/i normalised, (b) spectrum SCALE against "
                "Watterson's theta*H, (c) singleton proportion 1/H, which "
                "depends on n and not on theta -- (b) and (c) separate the two "
                "factors that (a) normalises away, and a mutation rate wrong "
                "by 2x passes (a) and fails (b). Every one is judged at 4 "
                "standard errors of the REPLICATE spread, because sites along "
                "a recombining sequence are linked and a per-site binomial "
                "error would be far too small. POSITIVE CONTROL: the identical "
                "statistic and identical 4-sigma rule applied to an "
                "exponentially growing population, which must be REJECTED; it "
                "fires at 58.8 sems. CAN-FAIL: the t grid spans 0.02 to 8.0 "
                "times 2Ne, crossing the point where the sample spectrum "
                "saturates; a grid at small t alone would validate theta*t/2 "
                "because nothing has been lost yet.",
        "members": ["expectedNewMutations", "expectedFreqDiffSq"],
    },
    {
        "name": "selection_regimes",
        "model": "selection-migration balance, stabilizing and directional "
                 "selection, and the portability laws fitted under each",
        "simulator": "cluster/fam_selection.py",
        "status": "SIMULATED -- REGIME DEFECT, and SLiM was not needed. Every "
                  "member is a one-locus deterministic recursion or its fixed "
                  "point, so a Wright-Fisher generation is array arithmetic. "
                  "FINDING: the axis is POPULATION SIZE, which no member "
                  "takes. The continent-island closed forms are exact in the "
                  "deterministic limit (0.00% to 0.02% at N = 10^6, and the "
                  "closed forms solve their own recurrences to 1e-15) and "
                  "collapse at small N: at s = 0.10, m = 0.05, N = 100 the "
                  "allele is LOST in 59.6-70.2% of replicates and E[p] is "
                  "0.176 against a predicted 0.474, an error of +169%. At "
                  "m(1+s) close to s the boundary is absorbing and the allele "
                  "is lost in 100% of replicates at N = 100 where the corpus "
                  "predicts 0.12-0.17. By N = 10^4 the corpus is within 1.8%. "
                  "The formulas are right about the deterministic limit and "
                  "silent about needing it, which is a scope declaration "
                  "rather than new arithmetic. selectedDriftFactor is NOT "
                  "covered and stays UNREACHABLE: s_correction is a free "
                  "parameter the corpus derives from nothing, so any "
                  "measurement can be fitted. The four portability members "
                  "(neutralPortability, neutralPortabilityRatioLD, "
                  "stabilizingPortability, diversifyingPortability) are also "
                  "NOT covered by this simulator -- it is one-locus and they "
                  "are score-level claims.",
        "found_by": "manual",
        "spec": "Forward Wright-Fisher, VECTORIZED OVER REPLICATES, with "
                "selection applied before or after migration (the corpus has "
                "BOTH orderings as separate definitions and they differ at "
                "O(sm)); mutation-selection balance additive and recessive; "
                "and an individual-based stabilizing-selection population for "
                "the linearity claim inside effectVarianceRecurrence. "
                "Predictions come from api.callable_for, i.e. the Lean bodies, "
                "not from retyping them. SPLIT CONTROLS: (0) the VECTORIZED "
                "DRAW IS THE SAME DRAW -- batch versus a scalar loop by "
                "two-sample KS, one batched generation against Binomial(2N,p) "
                "by chi-square, and cross-correlation against the MEASURED "
                "scalar-loop null; a kernel deliberately sharing one variate "
                "must be rejected by all three, and is (KS 0.995, chi2 6.4e4, "
                "corr 1.0000). (1) ALGEBRA: deterministic iteration of the "
                "corpus step map must reach the corpus closed form, isolating "
                "'the closed form solves the recurrence' from 'the recurrence "
                "is right'. (2) the same Wright-Fisher code at N = 10^7 must "
                "reproduce (1), isolating 'the simulator implements the model' "
                "from 'drift matters'. (3) s = 0 must give mu/(mu+nu) and pure "
                "drift must be a martingale -- isolates the mutation/drift "
                "half. (4) mu = 0 deterministic must send q to 0 -- isolates "
                "the selection half; (3) and (4) split what a single "
                "'reproduces mu/(hs)' check would fuse, since compensating "
                "errors in the two halves pass it. (5) POSITIVE CONTROL: a "
                "prediction corrupted by s -> 1.3s must be flagged where the "
                "true one passes. CAN-FAIL: mu/(hs+mu) and the textbook "
                "mu/(hs) CONVERGE as s grows, so the grid runs down to "
                "h*s = 3e-4 where they separate by 3.2%; the N axis spans "
                "5x10^2 to 10^6, which is 4N(hs) from 0.6 to 1200.",
        "members": ["selectionMigrationEquilibrium",
                    "selectionMigrationEquilibriumMigrationFirst",
                    "continentIslandStepSelectionFirst",
                    "continentIslandStepMigrationFirst",
                    "selectedDriftFactor",
                    # newly classified
                    "neutralPortability", "neutralPortabilityRatioLD",
                    "stabilizingPortability", "diversifyingPortability",
                    # mutation-selection balance, covered by fam_selection.py
                    "mutationSelectionStepRare", "mutationSelectionBalance",
                    "mutationSelectionStepRecessive",
                    "mutationSelectionBalanceRecessive",
                    "effectVarianceRecurrence",
                    "equilibriumEffectVariance"],
    },
    {
        "name": "ascertainment",
        "model": "discovery thresholds, winner's curse, tag/causal MAF "
                 "mismatch",
        "simulator": "cluster/fam_ascertainment.py",
        "status": "SIMULATED -- THE CORPUS COMES OUT WELL HERE, AND ONE "
                  "MAGNITUDE CLAIM UNDERSTATES. THE MEMBERSHIP LIST ON THIS "
                  "ENTRY WAS STALE: truncationBias, winnersCurseInflation and "
                  "approxPower were REMOVED from PowerAnalysis.lean and "
                  "tagGenotypeVariance is not in defs.json, so three of the "
                  "five listed members no longer exist and a simulator aimed "
                  "at the list would have checked a corpus that is gone. The "
                  "live members were found by grepping defs.json. "
                  "(1) discoveryNCP: the causal reading is within +/-1.7% at "
                  "all nine frequency cells while the tag reading runs -80.5% "
                  "to +428.9%. Every STRUCTURAL claim in its docstring is "
                  "confirmed -- the convention, 'coincides only when they are "
                  "equal', and the sign pattern (understates for a common "
                  "causal tagged by a rarer SNP, overstates in reverse). Its "
                  "quoted interval '-24% to +33%' is NOT a bound, though: it "
                  "corresponds to mild mismatch, and a 9-fold frequency ratio "
                  "reaches +429%. Scope declaration on the interval. "
                  "(2) The REMOVAL NOTES for winnersCurseInflation are "
                  "CONFIRMED to the digit, having never been simulated: the "
                  "note says the true conditional mean sits 'near 5.6 to 5.9 "
                  "standard errors at genome-wide significance' (measured "
                  "5.599 to 5.897) and that beta+SE is wrong by '-73% to "
                  "+23%' (measured -73.2% to +23.4%). At beta = 0 the true "
                  "two-sided bias is exactly 0 where beta+SE claimed one full "
                  "standard error. "
                  "(3) powerAtThreshold's declared range ncp in [1,20] does "
                  "real work: worst relative error 1.20% inside it and 5.54% "
                  "outside. (4) ascertainment_loss is within -1.0% to +3.6%.",
        "found_by": "manual",
        "spec": "Vectorized GWAS: R replicates x n individuals drawn in one "
                "block per chunk, one causal variant and one tag built from a "
                "haplotype model so r^2 and the tag/causal frequency mismatch "
                "move INDEPENDENTLY -- that separation is the whole design. "
                "Predictions come from api.callable_for. SPLIT CONTROLS: "
                "(1) SAMPLING VARIANCE ALONE, no threshold and no LD: measured "
                "Var(betahat) against standardErrorSq at r2 = 1, isolating the "
                "n*2p(1-p) factor. (2) LD ATTENUATION ALONE at MATCHED "
                "frequencies: the noncentrality ratio must be exactly r^2, "
                "isolating the ld^2 factor -- split from (1) because a "
                "simulator with the genotype variance wrong by 1/r^2 and the "
                "LD term wrong by r^2 passes a combined check and fails both. "
                "(3) THRESHOLD ALONE under the null: rejection rate must equal "
                "2*Phi(-z) and E[betahat | selected] must be ZERO by symmetry, "
                "which is exactly where the removed one-sided truncationBias "
                "went wrong. (4) POWER against the two-sided reference, with "
                "powerAtThreshold REPORTED rather than scored outside the "
                "ncp in [1,20] its own docstring declares. (5) POSITIVE "
                "CONTROL on the mismatch axis: the wrong frequency reading "
                "must be caught where the frequencies differ AND must not be "
                "caught where they agree. (6) the exact two-sided conditional "
                "mean must reproduce a simulated GWAS where selection is "
                "common enough to measure directly, which is what licenses "
                "quoting it in the rare-selection regime no affordable "
                "replicate count reaches. CAN-FAIL: maf_causal and maf_tag are "
                "swept independently at fixed r^2, so the grid contains cells "
                "where the two readings of discoveryNCP COINCIDE and cells "
                "where they differ 9-fold; a matched-frequency grid validates "
                "both readings and settles nothing, which is the failure mode "
                "the discoveryNCP docstring itself names.",
        "members": ["discoveryNCP", "noncentralityParam", "powerAtThreshold",
                    "effectiveSampleSize", "standardErrorSq",
                    "ascertainment_loss",
                    # REMOVED FROM THE CORPUS -- kept here as a record of what
                    # the old membership list pointed at, not as coverage:
                    #   truncationBias, winnersCurseInflation, approxPower
                    #   (removed from PowerAnalysis.lean)
                    #   tagGenotypeVariance (absent from defs.json)
                    ],
    },

    # =====================================================================
    # NEW FAMILIES -- named for the generative process, not the file
    # =====================================================================
    {
        "name": "fst_estimator_sampling",
        "model": "finite samples of individuals drawn from two demes at a "
                 "known parametric divergence; the estimator conventions "
                 "(Nei G_ST, Hudson, Weir-Cockerham, Wright F_IT) and the "
                 "heterozygosity-ratio and drift-factor inversions that the "
                 "corpus treats as interchangeable",
        "simulator": "cluster/fam_fst_estimators.py + "
                     "cluster/fam_fst_allel_crosscheck.py",
        "status": "SIMULATED AND GREEN, 0 cells red, positive control fired. "
                  "The earlier run had not failed -- it was a node-locality "
                  "problem, exactly as O1 predicts, and a foreground rerun "
                  "completed with rc 0. E1: at n = 20000 the corrected Hudson "
                  "estimator matches its parametric limit to four decimals at "
                  "every cell (0.050133/0.0501402, 0.149729/0.149717); at "
                  "n = 50 the UNCORRECTED estimator is inflated to 0.0692 "
                  "while the corrected one holds at 0.0503, so the "
                  "sample-size correction is doing visible work. E2, the "
                  "estimator-convention control at true F_ST = 0: Hudson "
                  "corrected returns -6.5e-05 and 6.3e-06, while Nei returns "
                  "0.0100684 and 0.0025094 against the predicted 1/(2n-1) "
                  "bias of 0.010101 and 0.0025063 -- the offset the corpus "
                  "inherits every time it converts between them. POSITIVE "
                  "CONTROL E3 FIRED: Hudson/Nei = 1.749 at p = 0.5, 1.751 at "
                  "0.1 and 1.751 at 0.02, so the two differ by 75% and "
                  "agreements elsewhere in the arm mean something. wrightFIT "
                  "composition exact to 1e-6 at both F_IS levels. The corpus "
                  "contains at least four "
                  "distinct quantities all called F_ST and converts freely "
                  "between them; the generative process that distinguishes "
                  "them is finite sampling at a swept allele-frequency "
                  "spectrum, which none of them takes as an argument. "
                  "SECOND SIMULATOR, cluster/fam_fst_allel_crosscheck.py, "
                  "AGAINST scikit-allel 1.3.13 -- foreign implementations of "
                  "Hudson and Weir-Cockerham, so an agreement is evidence and "
                  "not a restatement of our own algebra. EVERY NUMBER IS "
                  "LABELLED WITH ITS ESTIMATOR. C1: at 5000 diploids per deme "
                  "HUDSON_allel matches Conventions.hudsonFst to 0.02%-0.7% "
                  "at all eight (p1,p2) cells, and WC_allel agrees with "
                  "HUDSON_allel to six digits. C2: the conversion "
                  "Hudson = 2G/(1+G) proved as hudsonFst_eq_of_neiGst holds "
                  "to 5.6e-14 over 42 points. K2 POSITIVE CONTROL FIRED at the "
                  "docstring's own point (0.2, 0.6): NEI_GST 0.166667, HUDSON "
                  "0.285714, gap +71.4286% against the docstring's 71.4. "
                  "K1 at p1 = p2: HUDSON_allel -6.5e-04 and WC_allel -6.6e-04 "
                  "(corrected, ~0) while NEI_GST_sample returns 0.009775 "
                  "against the predicted 1/(2n-1) = 0.010101 -- the offset the "
                  "corpus inherits on every conversion. "
                  "C3 REFUTES A LIVE DOCSTRING CLAIM: Conventions.neiGst and "
                  "PopulationGeneticsFoundations both say the two estimators "
                  "'agree only when p1 = p2 OR pbar = 1/2'. The second disjunct "
                  "is FALSE. On a grid sitting on pbar = 1/2 EXACTLY with "
                  "p1 != p2, HUDSON/NEI_GST is 1.995 at (0.525, 0.475), 1.923 "
                  "at (0.6, 0.4), 1.724 at (0.7, 0.3) and 1.220 at (0.9, 0.1). "
                  "It follows from the corpus's own conversion: 2G/(1+G) = G "
                  "only at G in {0, 1}, i.e. only at p1 = p2. MENTIONS QUERY "
                  "RUN: MATH_LEDGER already refutes the pbar = 0.5 mechanism as "
                  "an AGGREGATE explanation of the 3.992 constant, but the "
                  "POINTWISE claim was still asserted in two Lean docstrings "
                  "(Conventions.lean:161, PopulationGeneticsFoundations.lean:68) "
                  "and copied into three can-fail clauses in checks.py. The "
                  "checks.py clauses are CORRECTED; the two Lean docstrings are "
                  "OWNED ELSEWHERE and are reported, not edited. "
                  "SINCE REPAIRED by the owning agent, and the repair is the "
                  "right strength: Conventions.lean now carries "
                  "`neiGst_ne_hudsonFst_at_mean_half` at p1 = 9/10, "
                  "p2 = 1/10 -- p-bar = 1/2 EXACTLY, ratio 50/41 = 1.22, which "
                  "is C3's fourth row -- so restoring the false disjunct now "
                  "breaks the build rather than merely contradicting a "
                  "docstring. RESIDUAL, STILL PRESENT, STILL OWNED ELSEWHERE: "
                  "Conventions.lean:207 says a library Hudson F_ST is 'the "
                  "wrong input by the factor above at p-bar != 1/2', which "
                  "still implies the factor is absent at p-bar = 1/2. It is "
                  "not: C3 measures 1.995 to 1.220 across that slice. "
                  "WHY THIS SURVIVED, WHICH IS THE TRANSFERABLE PART: the "
                  "pre-existing witness `neiGst_ne_hudsonFst` sits at "
                  "p1 = 1/5, p2 = 3/5, i.e. p-bar = 2/5, so it could not "
                  "exclude the p-bar = 1/2 slice the claim actually named. "
                  "This is not a check that cannot fail -- it fails fine, at a "
                  "point nobody disputed. It is a WITNESS THAT DOES NOT WITNESS "
                  "THE THING CLAIMED: a false claim sitting next to a witness "
                  "whose point misses the claim's stated exception looks "
                  "checked and is not. Look for it wherever a claim has the "
                  "form 'X except on S' and the accompanying witness is not "
                  "IN S.",
        "found_by": "manual",
        "spec": "Draw a parametric pair (p1, p2) from a Balding-Nichols beta "
                "at a known F_ST, then draw n haploid samples per deme "
                "binomially -- both steps vectorised over the whole locus x "
                "replicate array in one call. Measure each estimator on the "
                "sample and on the parametric frequencies. References: the "
                "closed forms in refs.py (fst_nei_gst, fst_hudson, "
                "fst_hudson_sample, fst_weir_cockerham), which are "
                "independently derived and not read from Lean. SPLIT "
                "CONTROLS: (a) n -> infinity must collapse every sample "
                "estimator onto its own parametric limit -- isolates SAMPLING "
                "BIAS from ESTIMATOR CHOICE; (b) p1 = p2 at finite n must give "
                "0 in expectation for the bias-corrected estimators and a "
                "strictly positive value for Nei's G_ST -- isolates ESTIMATOR "
                "CHOICE from sampling. Running only one of these lets a "
                "simulator with a sampling bug agree with a formula that has a "
                "compensating convention error. CAN-FAIL: the frequency grid "
                "must include rare variants (p < 0.05), where Nei and Hudson "
                "differ by more than a factor of two; a grid confined to "
                "common variants validates both and decides nothing, which is "
                "exactly why the corpus's free conversion has survived.",
        "members": ["neiFst", "neiGstFromFrequencies", "simpleFst", "fst",
                    "wrightFIT", "fstFromHetRatio"],
    },
    {
        "name": "identity_by_descent_recurrence",
        "model": "probability of identity by descent under a per-generation "
                 "'flow' rate: F' = (1-rate)^2 (1/(2Ne) + (1-1/(2Ne)) F). The "
                 "corpus instantiates `rate` as a MUTATION rate in some "
                 "members and a MIGRATION rate in others, from one body.",
        "simulator": "cluster/fam_ibd_recurrence.py",
        "status": "SIMULATED AND GREEN, 0 cells red, and the two readings are "
                  "DECIDED. cluster/fam_ibd_recurrence.py computes the "
                  "discrete-generation ancestral process for two lineages in a "
                  "d-deme island model twice -- an exact 2x2 identity solve and "
                  "an independent Monte Carlo on actual deme labels, which "
                  "share no code -- and evaluates the single corpus body at the "
                  "same parameters under each reading. CONTROLS FIRED: J1 at "
                  "rate = 0 gives f_S = 1 exactly from the exact solve, from "
                  "the MC (20000/20000 resolved, se 0) and from both corpus "
                  "iterations; J2 at Ne = 1e9 gives 2.46e-08 and 2.50e-07 "
                  "against a predicted 0. J3, THE VERDICT: under the MUTATION "
                  "reading the corpus body is EXACT -- relative error 4e-15 to "
                  "1e-14 at every scaled rate from 0.25 to 20, and the MC "
                  "confirms it (0.801237 +- 0.000729 vs 0.79985 at 4Ne*mu = "
                  "0.25; 0.108223 +- 0.000567 vs 0.108148 at 8). Under the "
                  "MIGRATION reading the SAME body is off by 20.1% at 4Ne*m = "
                  "0.25, 33.6% at 0.5, 50.5% at 1, 67.9% at 2 and 94.8% at 8, "
                  "because (1-m)^2 treats migration as ABSORBING when it is "
                  "recurrent -- a migrant lineage can migrate back, a mutated "
                  "one cannot come back. One body cannot be both. J4, THE "
                  "MISSING ARGUMENT: at fixed 4Ne*m the exact F_ST is 0.4988 at "
                  "d = 2, 0.6420 at d = 10 and 0.6636 at d = 100, a spread of "
                  "33% (67% at 4Ne*m = 2), and the corpus body has NO d "
                  "argument -- it is the d -> infinity reading and nothing says "
                  "so. The MC reproduces the exact d = 2 F_ST to 8e-5 at "
                  "4Ne*m = 0.5 and to 0.3 sigma at 2. The mutation floor was "
                  "halved as a control and F_ST moved by 3e-4, so the migration "
                  "arm is not measuring the mutation rate. checks.py section 15 "
                  "registers the analytic half: the mutation-reading check "
                  "agrees to 0.0 relative error (the positive control that "
                  "makes the rest interpretable) while the migration-reading "
                  "check disagrees by up to 52.8% and the missing-deme-count "
                  "check by up to 70.2%.",
        "found_by": "manual",
        "spec": "Iterate the identity recurrence numerically to its fixed "
                "point and, independently, measure identity by descent in a "
                "vectorised two-deme Wright-Fisher with (i) mutation only and "
                "(ii) migration only, at matched scaled rates. Reference: for "
                "mutation, F* = (1-2mu)^2/(2Ne)/(1 - (1-2mu)^2(1-1/2Ne)) "
                "-> 1/(1+theta); for migration the island result 1/(1+M). "
                "SPLIT CONTROLS: (a) rate = 0 must give F* = 1 exactly under "
                "both readings -- isolates the drift arm and proves the "
                "iteration converges; (b) Ne -> infinity must give F* = 0 "
                "exactly -- isolates the flow arm. The two readings are then "
                "distinguished by a THIRD run at matched scaled rate, which is "
                "the whole test and which neither control performs. CAN-FAIL: "
                "the scaled rate must go below 1, where the mutation and "
                "migration readings differ by the factor 2 that the (1-rate)^2 "
                "squaring introduces; above scaled rate 10 both give F* ~ 0.",
        "members": ["ibdFlowStep", "ibdRecurrenceStep", "ibdRecurrenceFixedPoint",
                    "scaledIdentityStep", "islandFstMultiplicativeStep",
                    "fstIslandMultiplicativeEquilibrium", "fstDriftFlowStep",
                    "fstEquilibrium", "fstMigDriftNext"],
    },
    {
        "name": "isolation_with_migration_coalescent",
        "model": "symmetric two-deme structured coalescent in continuous time "
                 "at scaled migration M; first-step analysis of E[T_ss] and "
                 "E[T_st] and their equilibrium, with the discrete-generation "
                 "ordering convention differing at O(1/Ne)",
        "simulator": None,
        "status": "NO SIMULATOR. The definitions state their composition "
                  "convention (continuous time, ordering immaterial) in a "
                  "docstring, and the discrete-generation alternative is named "
                  "there as differing at O(1/Ne) -- so the convention itself "
                  "is a testable claim that has never been tested.",
        "found_by": "manual",
        "spec": "Simulate the symmetric two-deme structured coalescent for two "
                "lineages directly: competing exponential clocks (coalescence "
                "at rate 1 when co-resident, migration at rate M/2 per "
                "lineage), vectorised as one exponential draw per replicate "
                "per event. Measure E[T_ss] and E[T_st]. References: the exact "
                "equilibrium E[T_ss] = 2, E[T_st] = 2 + 2/M (Wakeley), and "
                "delta = 1 - E[T_ss]/E[T_st] = 1/(1+M). SPLIT CONTROLS: "
                "(a) M -> infinity must give E[T_ss] = E[T_st] = 2, the "
                "panmictic value, isolating the coalescence clock from the "
                "migration clock; (b) M -> 0 must send E[T_st] -> infinity "
                "like 2/M while E[T_ss] stays at 2, isolating the migration "
                "clock from the coalescence clock. The E[T_ss] = 2 result "
                "holds at EVERY M and is the single strongest control here, "
                "because it is exactly invariant and a simulator with a wrong "
                "migration rate breaks it. THE CONVENTION TEST, which is the "
                "point: run a DISCRETE-generation version with migration "
                "strictly before coalescence and again strictly after, and "
                "compare both to the continuous-time answer at Ne = 50 where "
                "O(1/Ne) is 2%. CAN-FAIL: M must reach below 1, where "
                "1/(1+M) and the small-M expansion differ materially.",
        "members": ["twoDemeIMFirstStepSame", "twoDemeIMFirstStepDiff",
                    "twoDemeIMEquilibriumETss", "twoDemeIMEquilibriumETst",
                    "twoDemeIMEquilibriumScalars", "twoDemeIMEquilibriumDelta",
                    "delta", "expectedSqMeanPGSDiff_IMEquilibrium"],
    },
    {
        "name": "coalescent_hazard",
        "model": "coalescence as a point process with a time-varying hazard: "
                 "S(t) = exp(-integral of hazard), F = 1 - S; and the "
                 "discrete-generation recombination survival (1-r)^t on a "
                 "lineage of age tmrca",
        "simulator": None,
        "status": "NO SIMULATOR. The hazard-to-survival identity is the one "
                  "place the corpus expresses variable Ne as a process rather "
                  "than as a harmonic mean, and nothing checks that the two "
                  "readings agree.",
        "found_by": "manual",
        "spec": "Draw coalescence times under a piecewise-constant hazard "
                "1/(2Ne(t)) by inverse-transform on the integrated hazard, "
                "vectorised over replicates; measure the empirical survival "
                "function and TMRCA distribution. Reference: "
                "S(t) = exp(-Lambda(t)) exactly, and for a two-locus lineage "
                "P(no recombination by t) = (1-r)^t. SPLIT CONTROLS: "
                "(a) CONSTANT hazard must give an exponential with the "
                "textbook mean 2Ne -- isolates the sampler from the "
                "integration; (b) ZERO hazard over an interval must give "
                "survival exactly flat across it -- isolates the integration "
                "from the sampler. Together they pin the integral and the draw "
                "separately, which matters because a sampler that integrates a "
                "step function with the wrong endpoint convention still "
                "reproduces the constant-hazard mean. THE DISCRIMINATING RUN: "
                "a bottleneck hazard, where the harmonic-mean Ne used "
                "elsewhere in the corpus and the true integrated hazard give "
                "different TMRCA distributions with the SAME mean -- so only a "
                "distributional statistic, not the mean, can separate them. "
                "CAN-FAIL: the bottleneck must be deep enough (10x) that the "
                "harmonic mean and the full hazard differ in the tail.",
        "members": ["integratedCoalescentHazard", "coalescenceSurvivalFromHazard",
                    "coalescenceCdfFromHazard", "discreteRecombinationSurvival",
                    "twoLocusIBDCovariance",
                    "twoLocusCoalescentCovarianceMatrix",
                    # moved here after losing the un-simulatable falsifier:
                    # twoLocusCoalescentCovarianceMatrix returns a real matrix
                    # and names both indices in its body.
                    "twoLocusIdx0", "twoLocusIdx1"],
    },
    {
        "name": "hwe_genotype_score",
        "model": "Hardy-Weinberg genotypes at m independent loci, a polygenic "
                 "score as a weighted allele count; its exact mean and "
                 "variance and the error of the Gaussian approximation to its "
                 "distribution",
        "simulator": "cluster/fam_metrics.py (hwe arm)",
        "status": "SIMULATED AND GREEN. Run on the node: H1 (m=1) within 0.04, "
                  "1.41 and 0.04 analytic standard errors at p = 0.5, 0.1, "
                  "0.01; H2 (equal beta and p) 2.065 measured against 2.058 "
                  "predicted at m=10 and 41.11 against 41.16 at m=200; "
                  "heterogeneous m=150 variance 55.66 against 56.10 and "
                  "cross-covariance -7.98 against -8.21. The "
                  "approximation-error grid spans KS 0.536 at m=1, p=0.01 down "
                  "to 0.010 at m=1000, p=0.5, so it reaches the regime where "
                  "the Gaussian approximation is refutable. Cheapest simulator "

                  "and the only one whose reference is exact rather than "
                  "asymptotic, which is what makes it a usable control for the "
                  "families downstream of it.",
        "found_by": "manual",
        "spec": "Draw genotypes binomially with n = 2 at m loci for R "
                "individuals -- ONE binomial call over the whole (R, m) array "
                "-- and form S = sum beta_j g_j. Measure E[S], Var[S], the "
                "tag/causal cross-covariance, and the Kolmogorov distance "
                "between the standardised S and the standard normal. "
                "References, all exact: E[S] = 2 sum beta_j p_j, "
                "Var[S] = sum beta_j^2 2 p_j (1-p_j) under independence, "
                "Cov = sum beta_j gamma_j 2 p_j (1-p_j). SPLIT CONTROLS: "
                "(a) m = 1 makes the score a scaled binomial whose mean and "
                "variance are known in closed form with no summation at all -- "
                "isolates the per-locus moment from the summation; (b) all "
                "beta_j equal and all p_j equal makes Var[S] = m beta^2 2p(1-p) "
                "exactly -- isolates the summation from the per-locus moment. "
                "A simulator that mis-scales genotypes by 2 and compensates "
                "with a halved beta passes a combined check and fails (a). "
                "CAN-FAIL for the approximation-error arm: m must go DOWN to "
                "1-5 and p must go down to 0.01, where the Gaussian "
                "approximation visibly fails; at m = 1000 and p = 0.5 the "
                "approximation is exact to Monte-Carlo precision and the "
                "approximation-error definition is validated by a grid on "
                "which no candidate error bound could ever bind.",
        "members": ["scoreMean", "scoreVariance", "scoreApproximationError",
                    "causalMean", "tagMean", "crossCovEntry",
                    "sigmaTagCausal", "pgsVarianceFromHet",
                    # moved here after losing the un-simulatable falsifier:
                    # causalMean, tagMean and crossCovEntry name them in their
                    # bodies, so the composition is what gets tested.
                    "CausalVec", "TagVec"],
    },
    {
        "name": "estimator_moments",
        "model": "a data-generating process as a probability measure; the "
                 "mean, variance, covariance, MSE, bias, R^2 and irreducible "
                 "risk read off it, and the relations among them",
        "simulator": "cluster/fam_metrics.py (moments arm)",
        "status": "SIMULATED AND GREEN. Run on the node: M1 (oracle "
                  "predictor) drove the approximation risk to exactly 0 with "
                  "the irreducible risk at 0.7295 and the MSE at 0.7266; M2 "
                  "(zero noise) drove the irreducible risk to exactly 0 with "
                  "the approximation risk and the MSE both 0.7239 -- the two "
                  "terms are therefore separately identified and cannot be "
                  "swapped. The decomposition itself closes to 0.41% on a "
                  "non-linear f with heteroscedastic noise. M3, the SIGN "
                  "control, returned bias +0.747674 against +0.75, positive as "
                  "the E[S] - E[Y] convention requires -- the only cell in the "
                  "corpus that can see a negated bias definition. "
                  "measureVariance and E[Z^2]-E[Z]^2 agree to 1e-6 at a "
                  "non-zero mean, where they are not forced to. These look "
                  "like conventions and are "
                  "not: they fix SIGN and DENOMINATOR conventions "
                  "(measureBias = E[S] - E[Y], R^2 against varY rather than "
                  "varS) that every downstream metric inherits, and a "
                  "convention that no simulation touches is a convention that "
                  "can be inconsistent with its own consumers.",
        "found_by": "manual",
        "spec": "Monte-Carlo a concrete DGP -- Y = f(X) + eps with a chosen "
                "non-linear f and heteroscedastic eps, R draws in one "
                "vectorised call -- and evaluate each moment definition on the "
                "same sample. References: the standard identities "
                "Var = E[Z^2] - E[Z]^2, MSE = bias^2 + Var(Y - S), "
                "R^2 = 1 - MSE/Var(Y), and the fact that the irreducible risk "
                "equals E[Var(Y|X)] and the conditional-mean approximation "
                "risk equals E[(E[Y|X] - S)^2], which SUM to the MSE. SPLIT "
                "CONTROLS: (a) S = E[Y|X] exactly must drive the "
                "approximation risk to 0 while the irreducible risk stays at "
                "the noise variance -- isolates the approximation term; "
                "(b) zero-noise eps = 0 must drive the irreducible risk to 0 "
                "while the approximation risk stays at the model error -- "
                "isolates the irreducible term. The MSE decomposition is a "
                "SUM, so a combined check on the total passes when the two "
                "terms are swapped, and only the split controls detect that. "
                "SIGN CONTROL, which no symmetric check can perform: use a "
                "predictor biased strictly UPWARD, so measureBias must come "
                "out strictly positive under the E[S] - E[Y] convention and "
                "strictly negative under the other. CAN-FAIL: f must be "
                "genuinely non-linear and eps genuinely heteroscedastic, or "
                "the approximation and irreducible terms are not separately "
                "identified.",
        "members": ["measureMean", "measureVariance", "measureCovariance",
                    "measureExpMSE", "measureBias", "var", "rsquared", "mse",
                    "r2FromMSE", "irreduciblePredictionRisk",
                    "conditionalMeanApproximationRisk", "frobeniusNormSq"],
    },
    {
        "name": "liability_threshold_metrics",
        "model": "a Gaussian liability with signal and residual variance, "
                 "dichotomised at a prevalence threshold; the AUC, Brier, "
                 "log-loss and R^2 of a score on that liability, and the "
                 "regret of a miscalibrated score",
        "simulator": "cluster/fam_metrics.py (liability arm)",
        "status": "SIMULATED AND GREEN, with the positive control firing. Run "
                  "on the node: two-Gaussian AUC measured/predicted "
                  "0.637585/0.638163, 0.760175/0.760250, 0.921588/0.921350, "
                  "0.999802/0.999797 at snr = 0.25, 1, 4, 25 -- VALIDATED "
                  "against the model the definition names, on a grid whose low "
                  "end (0.638) is below the 0.75 where competing AUC forms stop "
                  "being distinguishable. L1 (vSignal = 0) exact at 0.5 / "
                  "pi(1-pi) / 0 for three prevalences. Liability-scale R^2 "
                  "0.200543, 0.499787, 0.798804, 0.961677 against 0.2, 0.5, "
                  "0.8, 0.961538. Brier regret and log-loss regret match at all "
                  "twelve (eta, q) cells. POSITIVE CONTROL L4 FIRED: at "
                  "vNoise = 0 the corpus returns Phi(0) = 0.5 and the process "
                  "gives 1.0, so the AUC check demonstrably can fail. SCOPE "
                  "RESULT, not a defect: the liability-threshold AUC measured "
                  "0.833494 at pi = 0.5 rising to 0.925089 at pi = 0.02, a "
                  "spread of 0.0916 -- independent forward-simulation "
                  "corroboration of the prevalence dependence the definition's "
                  "own docstring already records as FALSIFYING the liability "
                  "reading (its bivariate-normal integration gives 0.753 to "
                  "0.921 at R^2 = 0.3). The corpus scoped this correctly; the "
                  "first version of this simulator did not.",
        "found_by": "manual",
        "spec": "Draw liability L = G + E with G ~ N(0, vSignal) and "
                "E ~ N(0, vNoise), R draws in one call; dichotomise at the "
                "(1-pi) quantile; score with G. Measure empirical AUC (by the "
                "Mann-Whitney U identity, not by trapezoid on a binned ROC), "
                "Brier risk of the calibrated probability, log-loss, and R^2 "
                "on the liability scale. References: equal-variance Gaussian "
                "AUC = Phi(sqrt(vSignal/(2 vNoise))); calibrated Brier = "
                "pi(1-pi)(1 - R^2); R^2 = vSignal/(vSignal+vNoise). SPLIT "
                "CONTROLS: (a) vSignal = 0 must give AUC exactly 1/2, Brier "
                "exactly pi(1-pi) and R^2 exactly 0 -- isolates the metric "
                "code from the liability model, since all three are "
                "distribution-free at that point; (b) pi = 1/2 with vNoise "
                "swept isolates the signal-to-noise arm from the prevalence "
                "arm, and pi swept at fixed vNoise isolates the prevalence arm "
                "from the SNR arm. Brier is a PRODUCT pi(1-pi)(1-R^2) and a "
                "combined sweep passes when a prevalence error and an R^2 "
                "error cancel; only the two one-at-a-time sweeps separate "
                "them. POSITIVE CONTROL that the check can fire: evaluate at "
                "vNoise = 0 exactly, where the corpus returns 1/2 and the "
                "measured AUC is 1 -- if that cell comes back green the "
                "harness is not testing anything. CAN-FAIL: the SNR grid must "
                "include AUC below 0.75; above 0.95 every candidate AUC "
                "formula agrees to within Monte-Carlo error at any feasible R.",
        "members": ["equalVarianceGaussianAUCFromSNR",
                    "equalVarianceGaussianAUCFromExplainedR2",
                    "equalVarianceGaussianAUCChart",
                    "equalVarianceGaussianAUCFromVariances",
                    "equalVarianceGaussianAUCFromSourceWeights",
                    "gaussianAUCFromSignalVariance",
                    "presentDayGaussianAUC",
                    "presentDayEqualVarianceGaussianAUC",
                    "calibratedBrier", "calibratedBrierFromVariances",
                    "brierFromR2", "sourceBrierFromR2",
                    "brierRegretPoint", "brierRegretRatio",
                    "logLossRegretPoint", "logLossRegretRatio",
                    "r2FromSignalVariance", "aucApproximationInterval",
                    "r2ApproximationInterval", "prevalenceDGP_trueExpectation",
                    "profileFromSignalVariance",
                    "profileFromSignalVarianceWithPenalty",
                    "metricProfileFromTargetSignalWithPenalty",
                    "targetExactCalibratedBrierRisk",
                    "targetCalibratedBrierFromSourceWeights",
                    "targetMetricProfileFromSourceWeights",
                    "sourceCalibratedBrierFromSourceWeightsAtPrevalence",
                    "sourceMetricProfileFromSourceWeightsAtPrevalence",
                    "sourceMetricProfileFromSourceWeightsAtTargetPrevalence",
                    "exactCalibratedBrierRiskFromR2",
                    "total"],
    },
    {
        "name": "linear_prediction_transport",
        "model": "a score fitted by least squares on tag genotypes in a source "
                 "population and evaluated in a target whose tag-tag and "
                 "tag-causal covariances have shifted; the risk decomposition "
                 "into broken tagging, ancestry-specific LD, source overfit "
                 "and novel untaggable phenotype",
        "simulator": "cluster/fam_linear_transport.py",
        "status": "SIMULATED. The structure is instantiated from a two-"
                  "population genotype process (Balding-Nichols frequency "
                  "drift, population-specific AR(1) LD along the chromosome, "
                  "HWE genotypes as two independent haplotypes), not from "
                  "hand-chosen matrices, and every closed form is compared to "
                  "the same quantity measured on INDEPENDENT target "
                  "individuals. Results in fam_linear_transport_results.json.\n"
                  "  Confirmed against the process, converging with N over one "
                  "fixed world at N = 6k/24k/96k: scoreVarianceFromSource"
                  "Weights (rel err 1.00% -> 0.68% -> 0.04%), predictive"
                  "CovarianceFromSourceWeights (8.9 -> 4.4 -> 3.6%), "
                  "calibrationSlopeFromSourceWeights (8.0 -> 3.8 -> 3.7%), "
                  "targetLinearRisk (6.3 -> 1.6 -> 0.37%), "
                  "explainedR2FromTransportMoments (20.0 -> 8.9 -> 7.2%).\n"
                  "  TWO FINDINGS. (1) r2FromSourceWeights and "
                  "residualVarianceFromSourceWeights do not converge: they hold "
                  "a bias floor of -burden/(Var(y)+burden) = -16.6% and +20.8%. "
                  "The cause is that three of the four terms in "
                  "irreducibleTargetResidualBurden are dot products of vectors "
                  "of COVARIANCES while the fourth and the outcomeVariance they "
                  "are added to are variances. Under g -> c*g with beta -> "
                  "beta/c -- the free choice between raw dosages and "
                  "standardised genotypes, under which the phenotype, the "
                  "score and every measured moment are unchanged bit for bit -- "
                  "the measured R^2 moved 0.000e+00 while the burden grew by "
                  "exactly c^2.000 and r2FromSourceWeights fell 77% relative. "
                  "(2) demographicCovarianceGapLowerBound is identically 0 for "
                  "two equally diverged populations, the generic split, while "
                  "the measured squared Frobenius LD mismatch spanned 2.554 to "
                  "7.346: a missing regime declaration, on a bound that is "
                  "never proved and appears only as a hypothesis. Both are "
                  "registered in differential/checks.py section 14.",
        "found_by": "manual",
        "spec": "Simulate haplotypes in two diverged populations (reuse the "
                "island or split engine), pick tag and causal SNP sets, form "
                "the empirical Sigma_tag and Sigma_tag,causal in each; draw "
                "phenotypes from a true causal effect vector; fit weights by "
                "OLS in the source; evaluate the score in the target. Measure "
                "target R^2, calibration slope, predictive covariance and "
                "residual variance, and compare to the corpus's closed forms "
                "evaluated on the SAME empirical matrices -- so the check is "
                "of the algebra against the process, not of one matrix against "
                "another. SPLIT CONTROLS: (a) IDENTICAL POPULATIONS (F_ST = 0, "
                "same LD): calibration slope must be exactly 1, target R^2 "
                "must equal source R^2, and all four residual terms must be 0 "
                "-- isolates the fitting code from the transport; (b) SAME LD "
                "BUT SHIFTED EFFECTS: only targetEffectHeterogeneity is "
                "non-zero and brokenTaggingResidual must stay 0 -- isolates "
                "the effect-shift term from the LD-shift term; (c) SHIFTED LD "
                "BUT IDENTICAL EFFECTS: the mirror, isolating the LD-shift "
                "term. The residual burden is a SUM of four terms, so a check "
                "on the total passes when two terms are transposed; (a)-(c) "
                "are what separates them. POSITIVE CONTROL: a deliberately "
                "mis-signed weight vector must drive the calibration slope "
                "negative, proving the slope check can fire. CAN-FAIL: the tag "
                "count must approach the sample size in at least one cell, "
                "since sourceSpecificOverfitResidual is identically zero in "
                "the p << n regime and a grid confined there validates it "
                "vacuously.",
        "members": ["sourceERMWeights", "sourceBestLinearWeightsFromLD",
                    "sourceWeightsFromExplicitDrivers", "sourceWeightedTagScore",
                    "crossCovariance", "sigmaTagCausalSourceAt", "totalEffect",
                    "taggingProjection", "directCausalProjection",
                    "proxyTaggingProjection", "targetEffectHeterogeneity",
                    "targetSourceEffectProjection",
                    "targetEffectHeterogeneityProjection",
                    "targetNovelMutationEffectProjection",
                    "targetLinearRisk", "scoreVarianceFromSourceWeights",
                    "predictiveCovarianceFromSourceWeights",
                    "calibrationSlopeFromSourceWeights",
                    "explainedSignalVarianceFromSourceWeights",
                    "r2FromSourceWeights", "residualVarianceFromSourceWeights",
                    "explainedR2FromTransportMoments",
                    "brokenTaggingResidual", "ancestrySpecificLDResidual",
                    "sourceSpecificOverfitResidual",
                    "novelUntaggablePhenotypeResidual",
                    "irreducibleTargetResidualBurden", "residualBurden",
                    "targetIrreduciblePenaltyProfile",
                    "effectiveOutcomeVariance", "ldMismatchFrobenius",
                    "demographicCovarianceGapLowerBound",
                    # The dense 2x2 witness. BOTH the pre-rename and the
                    # post-rename names are listed: defs.json still carries the
                    # six separate constants while the Lean now carries the
                    # three Pop-indexed ones, so a list with only one spelling
                    # would report a phantom gap on whichever side is stale.
                    "witnessSigmaObs", "witnessCross", "witnessW_opt",
                    "sigmaObsSource", "sigmaObsTarget",
                    "crossSource", "crossTarget",
                    "wSource_opt", "wTarget_opt",
                    "Pop.pair", "pair", "withSource", "withTarget",
                    "ldWitnessSourceMoments", "ldWitnessBeta",
                    "ldWitnessSourceWeights", "ldWitnessTargetCross",
                    "ldWitnessSigmaTargetIndependent",
                    "ldWitnessSigmaTargetCorrelated"],
    },
    {
        "name": "generational_transport_kernel",
        "model": "two populations tracked generation by generation: tag and "
                 "causal allele frequencies, their retention, novel-variant "
                 "innovation, and the tag-causal LD kernels rebuilt at "
                 "generation t, feeding the deployed metrics at that "
                 "generation",
        "simulator": None,
        "status": "NO SIMULATOR. The single largest unassigned block: the "
                  "whole `...At` / `...AtGeneration` layer. It is the "
                  "composition of the popgen families with the metric "
                  "families, so it is the one place where a compensating pair "
                  "of errors in the two halves would be invisible to either "
                  "half's own simulator.",
        "found_by": "manual",
        "spec": "Run a two-population forward simulation (drift + mutation + "
                "migration, vectorised over loci and replicates) for t "
                "generations, tracking tag and causal frequencies and the "
                "tag-causal LD; at each generation build the metric model from "
                "the SIMULATED state and compare each `...AtGeneration` "
                "closed form to the metric measured on simulated individuals "
                "at that generation. Reference: the composition of the "
                "drift/mutation/migration references with the "
                "liability-metric references -- there is no independent closed "
                "form for the composite, which is exactly why it must be "
                "measured. SPLIT CONTROLS: (a) t = 0 must reproduce the SOURCE "
                "metrics exactly for every `...AtGeneration` member -- "
                "isolates the metric layer from the generational layer, and is "
                "the only control that can be pinned without simulation; "
                "(b) mutation = migration = 0 must reduce every kernel to the "
                "pure-drift family already simulated -- isolates drift; "
                "(c) Ne -> infinity must freeze all frequencies so every "
                "retention is exactly 1 and novelVariantInnovationAt is "
                "exactly 0 -- isolates the innovation term from the retention "
                "term. Retention and innovation enter the kernels as a SUM, so "
                "a single end-to-end check on the kernel passes when the two "
                "are exchanged; (c) is what separates them. CAN-FAIL: t must "
                "reach the order of 2Ne. At t << 2Ne every retention is 1 to "
                "within noise, every innovation term is 0, and the entire "
                "generational layer degenerates to the metric layer -- a short "
                "time grid would validate the composition without ever "
                "exercising it.",
        "members": ["toGenerationalPopGenParameters", "toMetricModelAt",
                    "toEvo", "coordinateSummary",
                    "betaTargetAt", "tagAlleleFreqTargetAt",
                    "causalAlleleFreqTargetAt", "tagAlleleFreqRetentionAt",
                    "causalAlleleFreqRetentionAt", "novelVariantInnovationAt",
                    "jointTagLDKernelAt", "jointDirectCausalKernelAt",
                    "jointProxyTaggingKernelAt",
                    "jointNovelDirectCausalKernelAt",
                    "jointNovelProxyTaggingKernelAt",
                    "sigmaTagTargetAt", "sigmaTagCausalTargetAt",
                    "directCausalTargetAt", "novelDirectCausalTargetAt",
                    "proxyTaggingTargetAt", "novelProxyTaggingTargetAt",
                    "targetSourceEffectProjectionAt",
                    "targetEffectHeterogeneityProjectionAt",
                    "targetR2AtGeneration", "targetScoreVarianceAtGeneration",
                    "targetResidualVarianceAtGeneration",
                    "targetPredictiveCovarianceAtGeneration",
                    "targetCalibrationSlopeAtGeneration",
                    "targetCalibratedBrierAtGeneration",
                    "targetGaussianAUCAtGeneration",
                    "targetMetricProfileAtGeneration",
                    "sourceNormalizedTargetR2AtGeneration",
                    "effectiveTargetOutcomeVarianceAtGeneration",
                    "alleleFreqMismatchPenalty"],
    },
    {
        "name": "neutral_af_benchmark_transport",
        "model": "the corpus's headline transport law: target predictive "
                 "accuracy obtained from source accuracy by a single scalar "
                 "built from F_ST and shared LD, via "
                 "covarianceRetention = freqCorr * ldOverlap",
        "simulator": None,
        "status": "NO SIMULATOR. This is the family the whole document exists "
                  "to state, and it is the one with the clearest compensating-"
                  "error hazard: the retention scalar is a PRODUCT of a "
                  "frequency term and an LD term, each of which the corpus "
                  "defines by a separate one-line identity, and no check "
                  "varies them independently.",
        "found_by": "manual",
        "spec": "Two populations at a swept F_ST and a swept shared-LD "
                "fraction, simulated independently of each other; fit a score "
                "in the source and measure target R^2, AUC and Brier; compare "
                "to source metrics scaled by the corpus's benchmark ratio. "
                "Reference: predictive covariance scales as (1 - F_ST) times "
                "the LD overlap, giving R^2_target/R^2_source = "
                "covarianceRetention^2 / scoreVarianceRatio. SPLIT CONTROLS, "
                "AND THIS FAMILY IS WHY THEY MATTER: (a) F_ST swept at shared "
                "LD held at 1 -- isolates freqCorrFromFst; (b) shared LD swept "
                "at F_ST held at 0 -- isolates ldOverlapFromSharedLD. The "
                "corpus's retention is the PRODUCT of the two, so a simulator "
                "or a formula that is wrong by a factor k in one and 1/k in "
                "the other reproduces the product exactly at every point of a "
                "joint sweep. Only the two one-at-a-time sweeps can fail, and "
                "a joint-sweep-only check would be the textbook instance of "
                "the compensating-error failure. CAN-FAIL: F_ST must reach "
                "0.15+ (the human continental range and beyond), because at "
                "F_ST = 0.01 the predicted retention is 0.99 and every "
                "candidate law -- (1-F_ST), (1-F_ST)^2, exp(-F_ST) -- agrees "
                "to within 1e-4.",
        "members": ["covarianceRetention", "covarianceDivergenceFromRetention",
                    "freqCorrFromFst", "ldOverlapFromSharedLD",
                    "neutralAFBenchmarkRatio", "neutralAFSharedLDBenchmarkRatio",
                    "neutralAFBenchmarkMetricProfile",
                    "targetR2FromNeutralAFBenchmark",
                    "targetGaussianAUCFromNeutralAFBenchmark",
                    "targetExactGaussianAUCFromNeutralAFBenchmark",
                    "targetBrierFromNeutralAFBenchmark"],
    },
    {
        "name": "pgs_transport_drift",
        "model": "a polygenic score built from ancestral additive variance "
                 "V_A, carried into a population that has drifted to F_ST; the "
                 "present-day score variance, the between-population mean "
                 "shift, and the resulting R^2 and signal-to-noise",
        "simulator": None,
        "status": "NO SIMULATOR. Distinct from drift_retention: that family is "
                  "about heterozygosity, this one is about the VARIANCE OF A "
                  "WEIGHTED SUM under drift, which picks up the "
                  "between-population component 2 F_ST V_A that the "
                  "heterozygosity story does not contain.",
        "found_by": "manual",
        "spec": "Draw m causal effects and ancestral frequencies, drift the "
                "frequencies to a target F_ST in two daughter populations "
                "(Balding-Nichols beta draw, one vectorised call over the "
                "(reps, m) array), and form the score in individuals sampled "
                "from each. Measure within-population score variance and the "
                "squared difference of population mean scores. References: "
                "within-population V = (1 - F_ST) V_A; "
                "Var(mean shift) = 2 F_ST V_A; E|shift| = "
                "sqrt(4 F_ST V_A / pi) under normality. SPLIT CONTROLS: "
                "(a) F_ST = 0 must give within-variance exactly V_A and mean "
                "shift exactly 0 -- isolates the score construction from the "
                "drift; (b) a SINGLE locus at known drifted frequencies, where "
                "both quantities are exact binomial moments with no polygenic "
                "limit -- isolates the drift from the polygenic sum. The two "
                "quantities are (1-F_ST) and 2F_ST times the same V_A, so a "
                "V_A scale error moves both together and cancels in their "
                "ratio; only (a), which fixes the absolute scale, catches it. "
                "CAN-FAIL: F_ST must reach 0.2, where (1-F_ST) and (1-F_ST)^2 "
                "differ by 20%; below F_ST = 0.02 they agree to 2e-4.",
        "members": ["presentDayPGSVariance", "realWorldPGSVariance",
                    "presentDayR2", "presentDaySignalToNoise",
                    "expectedR2", "Var_Delta_Mu", "Expected_Abs_Shift",
                    "expectedSqMeanPGSDiff_pureSplit",
                    "causalPortabilityFromLocalFst"],
    },
    {
        "name": "gxe_and_interaction",
        "model": "data-generating processes whose conditional mean is NOT "
                 "additive in the genetic and environmental components: "
                 "multiplicative GxE, stratified environments, differential "
                 "tagging, heterogeneous effects; and the recalibration slope "
                 "that a linear score is left with",
        "simulator": None,
        "status": "NO SIMULATOR. The corpus's non-additive DGPs are stated as "
                  "structures with a `trueExpectation` field and never "
                  "sampled, so the claim that a linear score's optimal "
                  "recalibration slope takes the stated form has never met a "
                  "sample.",
        "found_by": "manual",
        "spec": "Instantiate each non-additive DGP concretely -- interactive "
                "Y = G(1 + b sum C), additive-environment Y = G + b sum C, "
                "stratified environment, differential tagging -- draw R "
                "samples per DGP in one vectorised call, and regress Y on the "
                "score. Measure the OLS slope and the residual variance. "
                "Reference: slope = Cov(Y,S)/Var(S), which for the linear-noise "
                "case is sigma_g^2/(sigma_g^2 + base + slope_error c). SPLIT "
                "CONTROLS: (a) b = 0 must reduce every interactive DGP to the "
                "additive one and give slope exactly 1 -- isolates the "
                "interaction term; (b) noise = 0 at b non-zero must give the "
                "pure interaction attenuation with no noise attenuation -- "
                "isolates the noise term. The optimal slope is a RATIO whose "
                "numerator and denominator both contain sigma_g^2, so a "
                "combined check is insensitive to a common scale error in it; "
                "(a) fixes that scale. POSITIVE CONTROL that `hasInteraction` "
                "can fire: it must return true on the interactive DGP and "
                "false on the additive one -- a predicate that is never "
                "evaluated on a negative instance is not a predicate. "
                "CAN-FAIL: b must be large enough that the interaction "
                "contributes a detectable share of variance; at b = 0.01 the "
                "interactive and additive DGPs are indistinguishable at any "
                "feasible R and every claim about GxE validates.",
        "members": ["dgpInteractiveBias", "dgpAdditiveBias", "hasInteraction",
                    "optimalSlopeLinearNoise", "optimalSlopeFromVariance",
                    "totalVariance", "toDGP", "trueExp"],
    },
    {
        "name": "ensemble_portability_channel",
        "model": "stationary Gaussian latent target panels with genomic order erased; "
                 "finite Fejer and symmetric fourth-order dependence channels",
        "simulator": "cluster/fam_ensemble_channel.py",
        "status": "QUICK PROFILE RUN ON ACN116 (2026-08-02). Exact Fejer reference "
                  "agreed with brute force to 6.6e-15; finite sample means agreed within "
                  "2.60 SE; equal-Fejer processes separated in several higher symmetric "
                  "channels; ensemble moment RMSE slopes were -0.492 and -0.465. The "
                  "run also falsified the original compound-gain label: gain from an "
                  "arbitrary source includes squared target-mean shift as well as "
                  "predictable variance. The Lean identity and simulator were corrected; "
                  "the corrected operational arm awaits rerun.",
        "found_by": "manual",
        "spec": "Simulate stationary scaled-rotation Gaussian chains with exact stationary "
                "starts. Compare n Var(mean) to the finite Fejer sum, then hold the Fejer "
                "channel fixed while testing the symmetric fourth-order channel. The curve "
                "arm must verify injectivity rather than infer it from low dimension. Do not "
                "interpret `(mass,L)` as sufficient for the full unordered panel law.",
        "members": ["fejerChannel3", "gaussianPairSquareChannel3",
                    "ensembleSquaredLoss", "ensemblePredictorSquaredLoss",
                    "scalarPermeability"],
    },
    {
        "name": "portability_permeability_and_completion",
        "model": "Gaussian estimator-covariance channels, support-floor sealing, and "
                 "finite-dimensional lag completion",
        "simulator": "cluster/fam_permeability.py",
        "status": "FULL PROFILE PASSED ON ACN116 (2026-08-02). In the anisotropic "
                  "two-dimensional covariance experiment, measured/predicted RMSE "
                  "ratios ranged 0.984-1.035 after the CLT controls passed. The sealing "
                  "information converged to the eta-squared law and measured information "
                  "ratios ranged 0.850-1.048. The factorial closing-law fit recovered "
                  "the half-scaled quadratic-risk coefficients and excluded a detectable "
                  "source-by-ensemble cross term; its injected cross-term control fired. "
                  "The lag-completion negative and positive arms both passed. The formal "
                  "core now derives the Gaussian constant from moments, distinguishes "
                  "ordinary squared error 1/(mp) from half-scaled risk 1/(2mp), proves "
                  "the full whitened Hilbert-Schmidt matrix law and its diagonal face, "
                  "and supplies the nonsingular lag-completion criterion. These named "
                  "experiments do not imply an Edgeworth, monodromy, or universal "
                  "minimax theorem. The new deterministic C6 arm passed on ACN116 "
                  "(2026-08-02): the two-channel precision calculation equalled base "
                  "plus conditional-response innovation to machine precision, and its "
                  "constructed redundant probe added exactly zero. C1-C5 retain the "
                  "registered full-profile evidence; C6 is also included in future "
                  "quick/full profiles. Its fixed-budget extension also fired both "
                  "directions of the cost threshold: a 0.4 incremental assay cost "
                  "increased information per dollar from 0.1500 to 0.2579, while cost "
                  "2.0 reduced it to 0.1203.",
        "found_by": "manual",
        "spec": "Measure constants rather than slopes alone. Verify the estimator-draw "
                "CLT before using Gaussian covariance information; keep a level-0 positive "
                "control; distinguish p proportional to eta squared from a linear law; "
                "fit source, ensemble, residual, and cross terms on a factorial grid; and "
                "construct two distinct histories left unidentified by d-1 lag probes. "
                "For correlated non-Gaussian moment probes, independently invert a "
                "two-channel noise covariance and verify the Schur-complement innovation "
                "identity, including strict-value and exact-redundancy controls. Then "
                "vary incremental assay cost across the innovation-information-per-cost "
                "threshold and require both include and exclude decisions to fire.",
        "members": ["scalarPermeability", "covarianceScoreInformation_gaussian",
                    "multivariateGaussianPermeability", "diagonalPermeability",
                    "covarianceMomentPermeability",
                    "covarianceMomentPermeabilityWithPrecision",
                    "twoChannelMomentInformation_eq_base_add_innovation",
                    "twoChannelMomentInformation_eq_first_iff",
                    "twoChannelAugmentedAssay_moreEfficient_iff",
                    "informationAtBudget",
                    "gaussianCovarianceHalfSquaredRisk",
                    "lagObservationDerivative", "lagCompletionPermeability",
                    "completion_count_lower_bound", "quadraticChannel"],
    },
]

# ---------------------------------------------------------------------------
# EXPLICITLY UN-SIMULATABLE.
#
# Four entries. Kept this short on purpose: an earlier tier parked 27
# definitions here, was made to name what would refute each, ran it, and lost
# ALL 27 -- eleven had downstream consumers that made the composition testable
# and sixteen had theorems its own evaluator could not read. So the default
# here is NOT to park: a coercion, a bundler or a projection goes into the
# family of its downstream consumer (`toDGP`, `toEvo`, `toMetricModelAt`,
# `coordinateSummary`, `total`, `delta`, `trueExp` are all placed above for
# exactly that reason), because the COMPOSITION is testable even when the
# projection alone is trivial.
#
# What is left is the case a composition cannot reach: declarations that carry
# no real-valued content at all, so that no measurement of any consumer can
# come out differently depending on them. They are definitionally transparent
# -- `CausalVec c` IS `Fin c -> R`, and `twoLocusIdx0` IS `(0 : Fin t)` -- so
# unfolding them changes no proof obligation and no numeric value.
# ---------------------------------------------------------------------------
# EVERY ENTRY BELOW LOST ITS FALSIFIER. THE PARKED COUNT IS ZERO.
#
# THE PRIOR THE NEXT AGENT SHOULD INHERIT RATHER THAN REDISCOVER:
# ACROSS TWO TIERS AND THIRTY-ONE ATTEMPTS, NOTHING IN THIS SLICE HAS SURVIVED
# THE UN-SIMULATABLE CLAIM. The earlier tier lost 27 of 27; this one lost 4 of
# 4. That is no longer a rule about process, it is an empirical finding about
# this corpus: the probability that any given definition is genuinely beyond
# reach is very low, and a new claim of un-simulatability should be expected to
# lose before it is written.
#
# Note what the record also says about the falsifier requirement itself. It was
# introduced as a safeguard, and its entire recorded effect has been to destroy
# every claim it was applied to. A safeguard with a 31-for-31 record is not a
# safeguard; it is a refutation of the category it was meant to police. The
# machinery is kept live anyway, because the cheapest way to keep the finding
# true is to make the next candidate face the same test.
#
# These four were parked as carrying no real-valued content, with the falsifier
# in `falsify_unsimulatable` named before it was run. It was run, on defs.json
# as of 2026-08-02, and it FIRED ON ALL FOUR through F3, the composition test:
#
#   CausalVec     3 real-valued definitions name it in their BODY --
#                 causalMean, tagMean, crossCovEntry.
#   TagVec        the same three.
#   twoLocusIdx0  twoLocusCoalescentCovarianceMatrix, which returns a real
#                 matrix, names it in its body.
#   twoLocusIdx1  the same.
#
# F1 (returns a real) and F2 (a numeric theorem) held for all four. F3 is what
# took them, and F3 is what took the previous tier's twenty-seven. The rule was
# stated before the run and is honoured after it: a fired falsifier means the
# CLAIM is lost, not that the falsifier was too strict. All four are therefore
# also listed as members of the families of the definitions that consume them
# -- CausalVec and TagVec in hwe_genotype_score, the two indices in
# coalescent_hazard -- and they are NOT counted as parked below.
#
# STANDING RESULT: across two tiers and thirty-one attempts, nothing in this
# corpus slice has survived the un-simulatable claim. The entries are kept
# rather than deleted so the machinery stays live and the loss stays visible;
# the next candidate has to survive the same test rather than inherit an
# exemption from an empty list.
UNSIMULATABLE = [
    {
        "name": "CausalVec",
        "lost": True,
        "reason": "CLAIMED: type abbreviation, `CausalVec c := Fin c -> R`, "
                  "returns a Type and not a number. LOST to F3.",
    },
    {
        "name": "TagVec",
        "lost": True,
        "reason": "CLAIMED: type abbreviation, `TagVec t := Fin t -> R`. "
                  "LOST to F3.",
    },
    {
        "name": "twoLocusIdx0",
        "lost": True,
        "reason": "CLAIMED: index construction, the element `0` of `Fin t`, "
                  "returns a Fin and not a real. LOST to F3.",
    },
    {
        "name": "twoLocusIdx1",
        "lost": True,
        "reason": "CLAIMED: index construction, the element `1` of `Fin t`. "
                  "LOST to F3.",
    },
]


def falsify_unsimulatable(defs_by_short, theorems):
    """RUN the falsifier for every entry parked as un-simulatable.

    THE CLAIM: this declaration carries no real-valued content, so no
    measurement of any consumer can come out differently depending on it.

    WHAT WOULD REFUTE IT, and this is what is executed below:

      F1  RETURN TYPE. If the declaration returns a real, a vector of reals, a
          matrix of reals or a structure of reals, then it denotes a NUMBER and
          the claim is false on its face. Checked against `ret_type` and
          `signature` in defs.json.

      F2  A NUMERIC THEOREM. If any theorem mentioning it states a relation
          between real-valued expressions -- an equality, an inequality, or a
          membership in a real interval, involving `R` or a numeric literal --
          then there is a claim about it that an evaluator could check
          numerically, and the claim is false. Checked against the theorem
          statements in defs.json.

      F3  A REAL-VALUED CONSUMER THAT IS NOT TYPE-LEVEL. If any DEFINITION
          mentions it and itself returns a real, the composition is testable
          through that consumer unless the mention is purely in the consumer's
          TYPE. This is the test that killed the previous tier's list, so it is
          run in the strict direction: a real-valued consumer counts as a
          refutation unless the parked declaration appears only in the
          consumer's signature and not in its body.

    Every entry is reported with the outcome of all three, fired or not. An
    entry that fires any of them is NOT un-simulatable and is printed as a
    LOST claim, not quietly dropped.
    """
    real_markers = ("ℝ", "Matrix", "Profile", "Set ℝ")
    out = []
    for entry in UNSIMULATABLE:
        short = entry["name"]
        decls = defs_by_short.get(short, [])
        f1 = []
        f3 = []
        for d in decls:
            ret = (d.get("ret_type") or "") + " " + (d.get("signature") or "")
            if any(mk in ret for mk in real_markers):
                f1.append(d["name"] + " : " + ret.strip())
        # F3 -- real-valued definitions that mention it in their BODY
        for d in ALL_DEFS:
            body = d.get("body") or ""
            if short not in body:
                continue
            ret = (d.get("ret_type") or "") + " " + (d.get("signature") or "")
            if any(mk in ret for mk in real_markers):
                f3.append(d["name"])
        f2 = []
        for th in theorems:
            if short not in (th.get("mentions") or []):
                continue
            st = th.get("statement") or ""
            if ("ℝ" in st) or any(ch.isdigit() for ch in st):
                f2.append(th["name"])
        fired = bool(f1 or f2 or f3)
        out.append({
            "name": short,
            "reason": entry["reason"],
            "declarations_found": [d["name"] for d in decls],
            "F1_returns_real": f1,
            "F2_numeric_theorems": f2[:10],
            "F2_count": len(f2),
            "F3_real_valued_body_consumers": f3[:10],
            "F3_count": len(f3),
            "falsifier_fired": fired,
            "verdict": ("LOST -- falsifier fired, this is NOT un-simulatable"
                        if fired else
                        "HELD -- no real-valued content found by F1, F2 or F3"),
        })
    return out


def sweep_members():
    """Family membership from sweep_inlined_results.json, not from a hand list.

    The hardcoded lists below went stale INSIDE ONE SESSION: the corpus went
    from 1003 definitions to 994 while this tier was running, and
    islandModelFst, equilibriumFst and hetEquilibrium were collapsed onto other
    definitions by another agent. A hand-maintained membership list silently
    stops describing the corpus -- which is the exact failure this tier flagged
    in someone else's code earlier today, so it is fixed here rather than
    excused.

    Sweep-derived families take their members from the sweep output when it is
    present. Only AFFINE members count: a co-function shares the form's level
    sets without computing it.
    """
    path = os.path.join(HERE, "sweep_inlined_results.json")
    if not os.path.exists(path):
        return {}
    fh = open(path)
    data = json.load(fh)
    fh.close()
    out = {}
    for ref_name, blk in (data.get("references") or {}).items():
        names = []
        for m in blk.get("members", []):
            rel = m.get("relation") or {}
            if rel.get("kind") == "AFFINE":
                names.append(m["definition"].split(".")[-1])
        out[ref_name] = sorted(names)
    return out


SWEEP_TO_FAMILY = {
    "drift_retention": "drift_retention",
    "island_fst": "island_migration_fst",
    "split_fst": "split_fst",
    "sved_ld": "ld_decay_recurrence",
}

ALL_DEFS = []


def load_defs():
    fh = open(os.path.join(EXTRACT, "defs.json"))
    raw = json.load(fh)
    fh.close()
    if isinstance(raw, dict):
        entries = raw.get("definitions") or []
        theorems = raw.get("theorems") or []
    else:
        entries = raw
        theorems = []
    return entries, theorems


def main():
    entries, theorems = load_defs()
    del ALL_DEFS[:]
    ALL_DEFS.extend(entries)
    live = sweep_members()
    for fam in FAMILIES:
        for sweep_name, fam_name in SWEEP_TO_FAMILY.items():
            if fam["name"] != fam_name or sweep_name not in live:
                continue
            declared = set(fam["members"])
            found = set(live[sweep_name])
            fam["members"] = sorted(declared | found)
            fam["found_by"] = "sweep (regenerated)"
            fam["sweep_only"] = sorted(found - declared)
            fam["declared_only"] = sorted(declared - found)

    # SHORT NAME -> list of declarations. A short name may resolve to several
    # fully qualified declarations in different files; the previous version
    # merged them, which is how out-of-slice declarations were being counted as
    # in-slice statements.
    by_short = {}
    for d in entries:
        by_short.setdefault(d.get("short") or d["name"].split(".")[-1],
                            []).append(d)

    # IN-SLICE IS A SET OF FULLY QUALIFIED NAMES.
    in_slice_fq = set()
    in_slice_short = set()
    for d in entries:
        if d.get("file") in SLICE_FILES:
            in_slice_fq.add(d["name"])
            in_slice_short.add(d.get("short") or d["name"].split(".")[-1])

    ambiguous = {}
    for s, ds in by_short.items():
        if len(ds) > 1 and s in in_slice_short:
            ambiguous[s] = [x["name"] + " @ " + str(x.get("file")) for x in ds]

    claimed_fq = set()
    rows = []
    for fam in FAMILIES:
        present, missing, slice_members = [], [], []
        for m in fam["members"]:
            ds = by_short.get(m)
            if not ds:
                missing.append(m)
                continue
            present.append(m)
            for d in ds:
                if d.get("file") in SLICE_FILES:
                    claimed_fq.add(d["name"])
                    slice_members.append(d["name"])
        rows.append({
            "family": fam["name"],
            "model": fam["model"],
            "simulator": fam["simulator"],
            "status": fam["status"],
            "spec": fam.get("spec"),
            "found_by": fam["found_by"],
            "n_members_declared": len(fam["members"]),
            "n_members_present": len(present),
            "n_members_in_slice": len(set(slice_members)),
            "members_in_slice": sorted(set(slice_members)),
            "members_not_found_in_corpus": missing,
            "sweep_only": fam.get("sweep_only", []),
            "declared_only_not_confirmed_by_sweep": fam.get("declared_only", []),
        })

    # Un-simulatable declarations count as ACCOUNTED FOR but NOT covered.
    unsim = falsify_unsimulatable(by_short, theorems)
    # Only entries whose falsifier did NOT fire count as parked. An entry that
    # lost its falsifier is not accounted for by being on this list; it has to
    # earn a family like everything else, and it is credited only through the
    # family it was moved into.
    unsim_fq = set()
    for u in unsim:
        if u["falsifier_fired"]:
            continue
        for n in u["declarations_found"]:
            if n in in_slice_fq:
                unsim_fq.add(n)
    unsim_lost = [u["name"] for u in unsim if u["falsifier_fired"]]

    n_fam = len(rows)
    n_sim = len([r for r in rows if r["simulator"]])
    covered_fq = set()
    for r in rows:
        if r["simulator"]:
            covered_fq |= set(r["members_in_slice"])
    unassigned_fq = sorted(in_slice_fq - claimed_fq - unsim_fq)
    stmts_without = len(claimed_fq - covered_fq)

    print("MODEL FAMILY INVENTORY")
    print("  in-slice statements (FULLY QUALIFIED)  %d" % len(in_slice_fq))
    print("  families                       %d" % n_fam)
    print("  families WITH a simulator      %d" % n_sim)
    print("  families with NO simulator     %d   <- drive to zero first"
          % (n_fam - n_sim))
    print("")
    print("  in-slice statements in a simulated family      %d" % len(covered_fq))
    print("  in-slice statements in an unsimulated family   %d" % stmts_without)
    print("  in-slice statements parked as UN-SIMULATABLE   %d" % len(unsim_fq))
    print("      (%d claims of un-simulatability were made and %d LOST their "
          "falsifier: %s)" % (len(unsim), len(unsim_lost), unsim_lost))
    print("  in-slice statements in NO family at all        %d"
          % len(unassigned_fq))
    print("")
    print("%-38s %-5s %-6s %s" % ("family", "slice", "sim?", "status"))
    for r in sorted(rows, key=lambda x: (x["simulator"] is not None,
                                         -x["n_members_in_slice"])):
        print("%-38s %-5d %-6s %s"
              % (r["family"], r["n_members_in_slice"],
                 "yes" if r["simulator"] else "NO",
                 r["status"].split(".")[0][:60]))
        if r["members_not_found_in_corpus"]:
            print("      declared here but ABSENT FROM defs.json: %s"
                  % r["members_not_found_in_corpus"])
            print("      NOTE: absent from defs.json is NOT absent from the "
                  "corpus. hetDecayFromScaled, ohtaKimuraSigmaDSq, "
                  "neiGstFromFrequencies, steppingStoneFstQuadratic, "
                  "witnessSigmaObs, witnessCross and witnessW_opt are all "
                  "present in the .lean sources and missing from the extract, "
                  "and conversely defs.json still carries sigmaObsSource, "
                  "crossSource and wSource_opt which the Lean has renamed "
                  "away. The extract layer is STALE, so every coverage number "
                  "computed from it -- including the ones printed above -- is "
                  "a number about defs.json, not about the corpus.")
        if r.get("sweep_only"):
            print("      found by sweep, not in the hand list: %s"
                  % r["sweep_only"])
    print("")
    print("UN-SIMULATABLE LIST -- FALSIFIER EXECUTED ON EVERY ENTRY")
    for u in unsim:
        print("  %-16s %s" % (u["name"], u["verdict"]))
        print("      F1 returns-real            : %s"
              % (u["F1_returns_real"] or "no"))
        print("      F2 numeric theorems        : %d %s"
              % (u["F2_count"], u["F2_numeric_theorems"]))
        print("      F3 real-valued body users  : %d %s"
              % (u["F3_count"], u["F3_real_valued_body_consumers"]))
    print("")
    if ambiguous:
        print("SHORT NAMES THAT RESOLVE TO MORE THAN ONE DECLARATION")
        print("  (the previous revision counted every one of these as a single")
        print("   in-slice statement; %d of them)" % len(ambiguous))
        for s in sorted(ambiguous):
            print("      %-34s %s" % (s, ambiguous[s]))
        print("")
    print("  %d in-slice statements belong to no family yet:"
          % len(unassigned_fq))
    for u in unassigned_fq[:60]:
        print("      " + u)
    if len(unassigned_fq) > 60:
        print("      ... and %d more" % (len(unassigned_fq) - 60))

    out = {"families": rows,
           "unsimulatable": unsim,
           "ambiguous_short_names": ambiguous,
           "counts": {"in_slice_fully_qualified": len(in_slice_fq),
                      "families": n_fam, "families_with_simulator": n_sim,
                      "families_without_simulator": n_fam - n_sim,
                      "slice_statements_simulated_family": len(covered_fq),
                      "slice_statements_unsimulated_family": stmts_without,
                      "slice_statements_unsimulatable": len(unsim_fq),
                      "slice_statements_no_family": len(unassigned_fq)},
           "unassigned_in_slice": unassigned_fq}
    fh = open(os.path.join(HERE, "families_results.json"), "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("")
    print("-> families_results.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
