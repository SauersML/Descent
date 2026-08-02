"""Differential checks: corpus definition vs closed-form analytic reference.

Nothing here samples.  Each check states the model it assumes on both sides,
evaluates both over a grid chosen so that a wrong functional form separates
from a right one, and reports the worst relative disagreement.

Verdicts
--------
AGREE      max relative error <= tol over the whole grid
FORMULA    the two disagree under the SAME model -- the algebra is wrong
MODEL      each side is correct under its own model, but they are different
           models, so the definition does not mean what its name says
SCOPE      the definition cannot express the reference at all (missing argument)

Non-vacuity
-----------
Every check is re-run against mutants of the corpus definition (a 5% scaling,
and argument transposition where the arity allows).  A check that still passes
under a mutant cannot fail and is reported as VACUOUS regardless of verdict.
This is the automated form of the objection that sank the earlier symmetric
design in which both sides collapsed to the same number.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass, field

import refs


@dataclass
class Check:
    id: str
    fqn: str                      # fully-qualified Lean name under test
    claim: str
    model_lean: str
    model_ref: str
    reference: str
    grid: list[dict]
    lean: callable                # (D, **params) -> float ; D = corpus table
    ref: callable                 # (**params) -> float
    tol: float = 1e-9
    atol: float = 1e-9            # both sides ~0 is agreement, not 100% error
    kind: str = "formula"         # expected class if it disagrees
    mutable_arg: int | None = None
    # Verdict this check is SUPPOSED to produce. A disagreement that is a
    # documented, intended result -- a convention pin, say -- is not an open
    # defect, but it must not be allowed to quietly become agreement either.
    # Declaring it here means a check that starts passing when it is meant to
    # differ is reported as a REGRESSION rather than silently improving the
    # numbers. Leave None for checks that are simply meant to pass.
    expected_verdict: str | None = None
    note: str = ""
    canfail_clause: str = ""


def _relerr(a: float, b: float, atol: float = 1e-9) -> float:
    """Relative error with an absolute floor.

    Without the floor, two values that are both numerically zero (a closed form
    returning exactly 0 and an iteration returning 2e-11) report 100% error.
    That artefact appears wherever a definition is correct precisely because it
    returns zero -- the allele-loss regime of `selectionMigrationEquilibrium`
    is the live example -- so it must not be read as a disagreement.
    """
    if abs(a - b) <= atol:
        return 0.0
    d = max(abs(a), abs(b))
    return 0.0 if d == 0 else abs(a - b) / d


def grid(**axes) -> list[dict]:
    keys = list(axes)
    return [dict(zip(keys, v)) for v in itertools.product(*(axes[k] for k in keys))]


# ===========================================================================
CHECKS: list[Check] = []


def check(**kw):
    CHECKS.append(Check(**kw))


# --- 1. F_ST estimator conventions ----------------------------------------
_PQ = grid(p1=[0.02, 0.1, 0.3, 0.5], p2=[0.05, 0.2, 0.5, 0.8])

check(
    id="simpleFst-is-nei",
    fqn="Calibrator.PopulationGeneticsFoundations.neiGstFromFrequencies",
    claim="simpleFst p1 p2 equals Nei's G_ST for two equally weighted demes",
    model_lean="biallelic, two demes, parametric allele frequencies",
    model_ref="same",
    reference="refs.fst_nei_gst",
    grid=_PQ,
    lean=lambda D, p1, p2: D["neiGstFromFrequencies"](p1, p2),
    ref=lambda p1, p2: refs.fst_nei_gst(p1, p2),
    canfail_clause=(
        "grid must include |p1-p2| large AND pbar far from 0.5: at p1=p2 both "
        "sides are 0 and at pbar=0.5 the Nei and Hudson denominators coincide, "
        "so a symmetric grid cannot separate the conventions"
    ),
)

check(
    id="simpleFst-vs-hudson",
    fqn="Calibrator.PopulationGeneticsFoundations.neiGstFromFrequencies",
    claim="CONVENTION PIN: is simpleFst Hudson's F_ST rather than Nei's?",
    model_lean="biallelic, two demes, parametric",
    model_ref="Hudson ratio-of-averages, parametric limit (Bhatia 2013 eq 10)",
    reference="refs.fst_hudson",
    grid=_PQ,
    lean=lambda D, p1, p2: D["neiGstFromFrequencies"](p1, p2),
    ref=lambda p1, p2: refs.fst_hudson(p1, p2),
    kind="convention",
    expected_verdict="CONVENTION-DIFFERS",
    note="EXPECTED TO DISAGREE, and the disagreement IS the result. The "
         "definition is Nei's G_ST and is not Hudson; Conventions proves the "
         "exact conversion Hudson = 2G/(1+G), so the gap is 2x as G -> 0 and "
         "vanishes as G -> 1. It is not a constant, which is why no tolerance "
         "or calibration factor may ever absorb it. If this check ever PASSES, "
         "either the definition changed or refs.fst_hudson broke.",
    canfail_clause="needs pbar != 0.5; Nei and Hudson coincide exactly at pbar=0.5",
)

check(
    id="trueHudsonFst-is-hudson",
    fqn="Calibrator.Conventions.trueHudsonFst",
    claim="POSITIVE CONTROL for the convention pin: trueHudsonFst really is "
          "Hudson's parametric F_ST",
    model_lean="(p1-p2)^2 / (p1(1-p2) + p2(1-p1)), Bhatia 2013 eq 10",
    model_ref="same, computed independently in refs",
    reference="refs.fst_hudson",
    grid=_PQ,
    lean=lambda D, p1, p2: D["trueHudsonFst"](p1, p2),
    ref=lambda p1, p2: refs.fst_hudson(p1, p2),
    note=(
        "This exists so that `simpleFst-vs-hudson` failing is INTERPRETABLE. "
        "Without it a reader cannot tell whether that check disagrees because "
        "the corpus definition is Nei or because refs.fst_hudson is wrong. "
        "With it, one of the pair passing to machine precision while the other "
        "differs by up to 50% localises the disagreement to the definition."
    ),
    canfail_clause=(
        "the grid must stay off pbar = 0.5, where Nei and Hudson coincide "
        "exactly and every check in this group goes degenerate. _PQ is chosen "
        "for that."
    ),
)

check(
    id="neiFst-identity",
    fqn="Calibrator.PopulationGeneticsFoundations.neiFst",
    claim="neiFst H_T H_S fed the two-deme heterozygosities reproduces G_ST",
    model_lean="H_T, H_S supplied by the caller",
    model_ref="H_S = mean within-deme het, H_T = het of pooled frequency",
    reference="refs.fst_nei_gst",
    grid=_PQ,
    lean=lambda D, p1, p2: D["neiFst"](
        2 * ((p1 + p2) / 2) * (1 - (p1 + p2) / 2),
        (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2,
    ),
    ref=lambda p1, p2: refs.fst_nei_gst(p1, p2),
    canfail_clause="p1 != p2 required; at p1=p2, H_T=H_S and both sides are 0",
)

check(
    id="hudson-sample-limit",
    fqn="refs.fst_hudson_sample",
    claim="SELF-TEST of the reference: Hudson's finite-n estimator -> parametric",
    model_lean="n = 10^7 haploids per deme",
    model_ref="parametric limit",
    reference="refs.fst_hudson",
    grid=_PQ,
    lean=lambda D, p1, p2: refs.fst_hudson_sample(p1, p2, 10**7, 10**7),
    ref=lambda p1, p2: refs.fst_hudson(p1, p2),
    tol=1e-5,
    atol=1e-6,   # p1 == p2 rows: the finite-n correction leaves a -1e-7 residue
    kind="selftest",
    note="guards the reference itself, not the corpus; the corpus mutants do "
         "not touch it, so its power is demonstrated by the companion check "
         "hudson-sample-small-n rather than by mutation",
    canfail_clause="see hudson-sample-small-n: the same comparison at n=20 fails",
)

check(
    id="hudson-sample-small-n",
    fqn="refs.fst_hudson_sample",
    claim="DEMONSTRATION that the previous check has power: at n=20 it fails",
    model_lean="n = 20 haploids per deme",
    model_ref="parametric limit",
    reference="refs.fst_hudson",
    grid=_PQ,
    lean=lambda D, p1, p2: refs.fst_hudson_sample(p1, p2, 20, 20),
    ref=lambda p1, p2: refs.fst_hudson(p1, p2),
    tol=1e-5,
    atol=1e-6,
    kind="selftest",
    note="expected to DISAGREE; this is the can-fail evidence for hudson-sample-limit",
    canfail_clause="self-evident: this check exists to fail",
)

# --- 2. Split coalescent ---------------------------------------------------
_SPLIT = grid(t=[10.0, 100.0, 1000.0, 2000.0, 8000.0], Ne=[500.0, 1000.0, 10000.0])

check(
    id="coalFst-exact-split",
    fqn="Calibrator.PopulationGeneticsFoundations.coalFst",
    claim="coalFst t Ne is exactly Hudson F_ST after a clean split",
    model_lean="split t generations ago; one size parameter Ne",
    model_ref="clean split, N_daughter = N_ancestral = Ne, infinite sites",
    reference="refs.split_fst_hudson",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["coalFst"](t, Ne),
    ref=lambda t, Ne: refs.split_fst_hudson(t, Ne, Ne, Ne),
    canfail_clause=(
        "t must reach order Ne. For t << Ne every candidate F_ST formula "
        "collapses to t/(2Ne) and the check cannot discriminate."
    ),
)

check(
    id="coalFst-asymmetric-sizes",
    fqn="Calibrator.PopulationGeneticsFoundations.coalFst",
    claim="SCOPE: coalFst has one Ne, so it cannot express unequal daughter sizes",
    model_lean="single Ne; caller must pick one",
    model_ref="N1 = Ne/4, N2 = 4*Ne, N_anc = Ne",
    reference="refs.split_fst_hudson (asymmetric)",
    grid=grid(t=[500.0, 2000.0, 8000.0], Ne=[1000.0]),
    lean=lambda D, t, Ne: D["coalFst"](t, Ne),
    ref=lambda t, Ne: refs.split_fst_hudson(t, Ne / 4, 4 * Ne, Ne),
    kind="scope",
    note="expected to disagree; quantifies the cost of the single-size assumption",
    canfail_clause=(
        "THE asymmetry: N1 != N2. With N1 = N2 the check reduces to "
        "coalFst-exact-split and passes trivially."
    ),
)

check(
    id="fstDerived-is-not-split-fst",
    fqn="Calibrator.PopulationGeneticsFoundations.fstDerived",
    claim="MODEL: the drift recurrence is not the F_ST of a split",
    model_lean="closed population, NO mutation: 1-(1-1/2Ne)^t",
    model_ref="clean split at mutation-drift equilibrium, infinite sites",
    reference="refs.split_fst_hudson",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["fstDerived"](Ne, int(t)),
    ref=lambda t, Ne: refs.split_fst_hudson(t, Ne, Ne, Ne),
    kind="model",
    note="root of the fstDerived/fstFromTau/targetHetFromFst cluster",
    canfail_clause=(
        "REQUIRES t/(2Ne) >= ~0.5. Both sides are t/(2Ne) + O(t^2/Ne^2), so at "
        "t << Ne they agree to <1% and the test is vacuous."
    ),
)

check(
    id="fstDerived-is-coalescence-prob",
    fqn="Calibrator.PopulationGeneticsFoundations.fstDerived",
    claim="what fstDerived actually computes: P(coalesce within t) in a closed pop",
    model_lean="closed population, no mutation",
    model_ref="same",
    reference="refs.prob_coalesce_within",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["fstDerived"](Ne, int(t)),
    ref=lambda t, Ne: refs.prob_coalesce_within(t, Ne),
    canfail_clause="t >= 1 and Ne finite; at t=0 both sides are 0",
)

check(
    id="hetLossFromDrift-duplicates-fstDerived",
    fqn="Calibrator.PopulationGeneticsFoundations.heterozygosityLossFromDrift",
    claim="DUPLICATE: identical body to fstDerived under a different name",
    model_lean="closed population, no mutation",
    model_ref="same",
    reference="refs.prob_coalesce_within",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["heterozygosityLossFromDrift"](int(t), Ne),
    ref=lambda t, Ne: refs.prob_coalesce_within(t, Ne),
    canfail_clause="t >= 1; at t=0 both sides are 0",
)

check(
    id="fstFromGenerations-equals-coalFst",
    fqn="Calibrator.PortabilityDrift.fstFromGenerations",
    claim="cross-file: fstFromGenerations agrees with the exact split F_ST",
    model_lean="tau = t/2Ne, F = tau/(1+tau)",
    model_ref="clean split, equal sizes",
    reference="refs.split_fst_hudson",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["fstFromGenerations"](t, Ne),
    ref=lambda t, Ne: refs.split_fst_hudson(t, Ne, Ne, Ne),
    canfail_clause="t of order Ne (see fstDerived-is-not-split-fst)",
)

check(
    id="pairwiseFstFromBranches",
    fqn="Calibrator.PortabilityDrift.pairwiseFstFromBranches",
    claim="multiplicative branch composition vs the exact two-branch split F_ST",
    model_lean="1-(1-fstS)(1-fstT) with per-branch F_ST",
    model_ref="clean split, both daughters size Ne, total separation tS+tT",
    reference="refs.split_fst_hudson",
    grid=grid(tS=[200.0, 1000.0, 4000.0], tT=[200.0, 1000.0, 4000.0], Ne=[1000.0]),
    lean=lambda D, tS, tT, Ne: D["pairwiseFstFromBranches"](
        D["fstFromGenerations"](tS, Ne), D["fstFromGenerations"](tT, Ne)
    ),
    ref=lambda tS, tT, Ne: refs.split_fst_hudson(tS + tT, Ne, Ne, Ne),
    kind="formula",
    canfail_clause=(
        "needs tS+tT of order Ne AND ideally tS != tT. At tS,tT << Ne the "
        "composition is exact to first order."
    ),
)

# --- 3. Mutation-drift ------------------------------------------------------
_MD = grid(Ne=[100.0, 1000.0, 10000.0], mu=[1e-6, 1e-5, 1e-4, 1e-3])

check(
    id="hetEquilibrium-vs-exact-iam",
    fqn="Calibrator.PopulationGeneticsFoundations.hetEquilibrium",
    claim="theta/(1+theta) vs the exact infinite-alleles stationary heterozygosity",
    model_lean="theta/(1+theta), theta = 4 Ne mu",
    model_ref="exact IAM recursion F' = (1-mu)^2[1/2Ne + (1-1/2Ne)F]",
    reference="refs.iam_het_equilibrium",
    grid=_MD,
    lean=lambda D, Ne, mu: D["hetEquilibrium"](Ne, mu),
    ref=lambda Ne, mu: refs.iam_het_equilibrium(Ne, mu),
    tol=1e-2,
    note="agreement to O(mu) is the claim; tol reflects that",
    canfail_clause="needs mu large enough that (1-mu)^2 != 1-2mu; mu >= 1e-3",
)

check(
    id="hetDecayFactor-vs-exact-eigenvalue",
    fqn="Calibrator.PopulationGeneticsFoundations.hetDecayFactor",
    claim="(1-1/2Ne)(1-theta/2Ne) vs the exact IAM eigenvalue (1-1/2Ne)(1-mu)^2",
    model_lean="theta passed in must be 4*Ne*mu for the SAME Ne",
    model_ref="exact IAM",
    reference="refs.iam_decay_eigenvalue",
    grid=_MD,
    lean=lambda D, Ne, mu: D["hetDecayFactor"](Ne, D["scaledMutationRate"](Ne, mu)),
    ref=lambda Ne, mu: refs.iam_decay_eigenvalue(Ne, mu),
    tol=1e-4,
    canfail_clause="mu >= 1e-3 (difference is mu^2 per generation)",
)

check(
    id="hetMutationDriftRecurrence-trajectory",
    fqn="Calibrator.PopulationGeneticsFoundations.hetMutationDriftRecurrence",
    claim="the corpus recurrence vs the exact IAM trajectory from H0=0",
    model_lean="H' = (1-1/2Ne)H + 2mu(1-H)",
    model_ref="exact IAM trajectory",
    reference="refs.iam_het_trajectory",
    grid=grid(Ne=[100.0, 1000.0], mu=[1e-5, 1e-4, 1e-3], t=[100, 1000, 10000]),
    lean=lambda D, Ne, mu, t: D["hetMutationDriftRecurrence"](Ne, mu, 0.0, t),
    ref=lambda Ne, mu, t: refs.iam_het_trajectory(Ne, mu, 0.0, t),
    tol=1e-2,
    canfail_clause=(
        "H0 must differ from H*, and t must not be so large that both sides "
        "have converged to H* -- at t -> inf the trajectory check degenerates "
        "into the equilibrium check and cannot see a wrong eigenvalue."
    ),
)

check(
    id="transient-discrete-vs-continuous",
    fqn="Calibrator.PopulationGeneticsFoundations.fstMutationDriftTransientDiscrete",
    claim="discrete and continuous transients agree only for large Ne",
    model_lean="discrete: Feq*(1-lambda^t)",
    model_ref="continuous: Feq*(1-exp(-(1+theta)t/2Ne)) [same file]",
    reference="Calibrator.PopulationGeneticsFoundations.fstMutationDriftTransient",
    grid=grid(Ne=[5.0, 50.0, 5000.0], theta=[0.01, 1.0], t=[10, 100]),
    lean=lambda D, Ne, theta, t: D["fstMutationDriftTransientDiscrete"](theta, Ne, t),
    ref=lambda D, Ne, theta, t: D['fstMutationDriftTransient'](theta, float(t), Ne),
    tol=1e-2,
    kind="internal",
    note="internal consistency; reference is another corpus definition",
    canfail_clause="Ne must go down to ~5; at Ne=5000 the two agree to 1e-4",
)

# --- 4. Island model --------------------------------------------------------
check(
    id="islandModelFst-finite-demes",
    fqn="Calibrator.fstMigrationDriftEquilibrium",
    claim="MODEL: 1/(1+4Nm) is the infinite-island limit",
    model_lean="infinite number of demes",
    model_ref="d demes: 1/(1+4Nm(d/(d-1))^2)",
    reference="refs.island_fst_finite_demes",
    grid=grid(Ne=[1000.0], m=[1e-4, 1e-3, 1e-2], d=[2, 5, 10, 40]),
    lean=lambda D, Ne, m, d: D["fstMigrationDriftEquilibrium"](Ne, m),
    ref=lambda Ne, m, d: refs.island_fst_finite_demes(Ne, m, d),
    kind="model",
    canfail_clause=(
        "d must include small values. At d=40 the correction is 5% and at "
        "d -> inf it vanishes, so a large-d-only grid cannot fail."
    ),
)

check(
    id="fstIslandMultiplicative-exact-fixedpoint",
    fqn="Calibrator.PortabilityDrift.fstIslandMultiplicativeEquilibrium",
    claim="the closed form is the exact fixed point of its own step function",
    model_lean="F' = (1-m)^2[1/2Ne + (1-1/2Ne)F]",
    model_ref="same recursion, solved exactly",
    reference="refs.island_fst_exact_recursion",
    grid=grid(Ne=[100.0, 1000.0], m=[1e-4, 1e-2, 0.1, 0.3]),
    lean=lambda D, Ne, m: D["fstIslandMultiplicativeEquilibrium"](Ne, m),
    ref=lambda Ne, m: refs.island_fst_exact_recursion(Ne, m),
    canfail_clause="m must reach ~0.3 so the (1-m)^2 terms matter",
)

check(
    id="islandModelFst-vs-exact-in-m",
    fqn="Calibrator.fstMigrationDriftEquilibrium",
    claim="1/(1+4Nm) vs the exact-in-m island fixed point",
    model_lean="small-m expansion",
    model_ref="exact recursion fixed point",
    reference="refs.island_fst_exact_recursion",
    grid=grid(Ne=[100.0, 1000.0], m=[1e-4, 1e-2, 0.1, 0.3]),
    lean=lambda D, Ne, m: D["fstMigrationDriftEquilibrium"](Ne, m),
    ref=lambda Ne, m: refs.island_fst_exact_recursion(Ne, m),
    tol=1e-2,
    kind="model",
    canfail_clause="m >= 0.1; at m <= 1e-3 the expansion is exact to 0.1%",
)

# --- 5. Stepping stone ------------------------------------------------------
check(
    id="steppingStoneLength-missing-mutation",
    fqn="Calibrator.PopulationGeneticsFoundations.steppingStoneCharacteristicLength",
    claim="FORMULA: the 1D decay scale is sqrt(m/2mu), not sqrt(2 Ne m)",
    model_lean="L = sqrt(m/(2 mu)) -- REPAIRED to the Kimura-Weiss/Malecot "
               "form. Was sqrt(2 Ne m): no mutation argument where the truth "
               "goes as mu^-1/2, and an Ne dependence the truth does not have. "
               "The Ne axis stays in the grid deliberately -- the reference is "
               "flat in Ne and so is the corrected value, so if a later edit "
               "reintroduces an Ne dependence this check fires.",
    model_ref="Malecot/Kimura-Weiss 1D lattice: L = sqrt(m/(2 mu))",
    reference="refs.stepping_stone_decay_scale_malecot",
    grid=grid(Ne=[100.0, 1000.0, 10000.0], m=[1e-3, 1e-2], mu=[1e-8, 1e-6]),
    lean=lambda D, Ne, m, mu: D["steppingStoneCharacteristicLength"](m, mu),
    ref=lambda Ne, m, mu: refs.stepping_stone_decay_scale_malecot(m, mu),
    kind="formula",
    canfail_clause=(
        "the grid MUST vary mu at fixed Ne and m: the Lean value is constant "
        "along that axis while the reference moves as mu^-1/2. Varying only "
        "Ne and m would let a fitted constant hide the error."
    ),
)

# `steppingStone-cross-file-contradiction` was DELETED, not repointed.
#
# It compared 1 - exp(-d/L) against d/(d + 4 Ne m sigma^2) and found an 878%
# disagreement. The contradiction is now resolved by REMOVING ONE SIDE:
# `continuousSteppingStoneFst` has been deleted from the corpus, because the
# coalescent derivation in DemographicHistory yields the hyperbolic form
# exactly and the exponential is not derivable from it -- no choice of L
# reconciles them beyond first order.
#
# A check whose Lean side no longer exists cannot fail informatively, so
# keeping it would have meant a permanent KeyError dressed up as coverage. The
# surviving side is still checked by `demoSteppingStoneFst-exact` below.
check(
    id="demoSteppingStoneFst-exact",
    fqn="Calibrator.DemographicHistory.demoSteppingStoneFst",
    claim="d/(d+4 Ne m sigma^2) is the Hudson F_ST built from its own T(d)",
    model_lean="E[T_within]=2Ne, Delta(d)=d/(2 sigma^2 m)",
    model_ref="same, assembled independently",
    reference="refs.stepping_stone_fst_hudson",
    grid=grid(d=[1.0, 5.0, 20.0], Ne=[500.0, 5000.0], m=[1e-3, 1e-2], sigma_sq=[1.0, 4.0]),
    lean=lambda D, d, Ne, m, sigma_sq: D["demoSteppingStoneFst"](d, Ne, m, sigma_sq),
    ref=lambda d, Ne, m, sigma_sq: refs.stepping_stone_fst_hudson(d, Ne, m, sigma_sq),
    canfail_clause="d > 0 and finite Ne; at d=0 both sides are 0",
)

# --- 6. Linkage disequilibrium ---------------------------------------------
_LD = grid(r=[1e-5, 1e-3, 1e-2, 0.1], Ne=[100.0, 1000.0, 10000.0])

check(
    id="ldRetentionPerGen-exact",
    fqn="Calibrator.LDDecayTheory.ldRetentionPerGen",
    claim="(1-r)(1-1/2Ne) is the exact per-generation retention of E[D]",
    model_lean="two neutral loci, recombination r, Wright-Fisher Ne",
    model_ref="Hill & Robertson (1968)",
    reference="refs.ld_expected_D_retention",
    grid=_LD,
    lean=lambda D, r, Ne: D["ldRetentionPerGen"](r, Ne),
    ref=lambda r, Ne: refs.ld_expected_D_retention(r, Ne),
    canfail_clause="r > 0 and Ne finite; at r=0, Ne=inf both sides are 1",
)

check(
    id="ldHalfLife-drops-recombination",
    fqn="Calibrator.LDDecayTheory.ldHalfLife",
    claim="FORMULA: 2 Ne ln2 is the r=0 half-life; the true one depends on r",
    model_lean="ln2 / -ln[(1-r)(1-1/2Ne)] -- REPAIRED. Was 2 Ne ln 2 with no "
               "recombination argument, which was 2110x wrong at r=0.1, Ne=1e4. "
               "This check is now definitionally equal to the reference and is "
               "EXPECTED TO PASS: that is the fix landing, not the check being "
               "weakened. Grid and tolerance are unchanged from when it failed.",
    model_ref="ln2 / -ln[(1-r)(1-1/2Ne)], from ldRetentionPerGen in the same file",
    reference="refs.ld_half_life_exact",
    grid=_LD,
    lean=lambda D, r, Ne: D["ldHalfLife"](r, Ne),
    ref=lambda r, Ne: refs.ld_half_life_exact(r, Ne),
    kind="formula",
    canfail_clause=(
        "REQUIRES r >> 1/(2Ne). At r=0 the two are identical, and that is "
        "exactly the degenerate point a careless grid would sit on."
    ),
)

check(
    id="ldRetainedFraction-inconsistent-with-retention",
    fqn="Calibrator.LDDecayTheory.ldRetainedFraction",
    claim="INTERNAL: retained fraction is not ldRetentionPerGen^t",
    model_lean="ldRetentionPerGen r Ne ^ t -- REPAIRED. Was (1-1/2Ne)^t with "
               "no recombination argument, inconsistent with ldRetentionPerGen "
               "in its own file by 37000x at r=0.1, Ne=1000, t=100. Expected to "
               "pass now; grid and tolerance unchanged.",
    model_ref="ldRetentionPerGen(r,Ne)^t [same file]",
    reference="Calibrator.LDDecayTheory.ldRetentionPerGen ** t",
    grid=grid(r=[0.0, 1e-4, 1e-2, 0.1], Ne=[1000.0], t=[10, 100]),
    lean=lambda D, r, Ne, t: D["ldRetainedFraction"](r, Ne, t),
    ref=lambda D, r, Ne, t: D['ldRetentionPerGen'](r, Ne) ** t,
    kind="internal",
    canfail_clause="r > 0 required; the r=0 row is in the grid and passes, which is the point",
)

check(
    id="driftLDEquilibrium-exact-fixedpoint",
    fqn="Calibrator.LDDecayTheory.driftLDEquilibrium",
    claim="closed form is the exact fixed point of driftLDStep",
    model_lean="Q' = (1-c)^2[1/2Ne + (1-1/2Ne)Q]",
    model_ref="same recursion solved exactly",
    reference="refs.ld_ibd_equilibrium_exact",
    grid=grid(Ne=[100.0, 1000.0], c=[1e-4, 1e-2, 0.1, 0.3]),
    lean=lambda D, Ne, c: D["driftLDEquilibrium"](Ne, c),
    ref=lambda Ne, c: refs.ld_ibd_equilibrium_exact(Ne, c),
    canfail_clause="c up to 0.3 so the (1-c)^2 factor is not ~1",
)

check(
    id="driftLDEquilibrium-vs-ohta-kimura",
    fqn="Calibrator.LDDecayTheory.driftLDEquilibrium",
    claim="MODEL: the IBD equilibrium is not Ohta-Kimura's sigma_d^2 = E[r^2]",
    model_lean="probability of gametic identity by descent (Sved)",
    model_ref="Ohta & Kimura (1971) (10+rho)/((2+rho)(11+rho))",
    reference="refs.ohta_kimura_sigma_d_sq",
    grid=grid(Ne=[1000.0], c=[1e-6, 1e-5, 1e-4, 1e-3, 1e-2]),
    lean=lambda D, Ne, c: D["driftLDEquilibrium"](Ne, c),
    ref=lambda Ne, c: refs.ohta_kimura_sigma_d_sq(Ne, c),
    kind="model",
    canfail_clause=(
        "REQUIRES rho = 4Nc <~ 10. The two forms converge as rho -> inf "
        "(2% apart at rho=100), so a tightly-linked-only grid is essential."
    ),
)

check(
    id="ohtaKimuraSigmaDSq-matches-simulation",
    fqn="Calibrator.ohtaKimuraSigmaDSq",
    claim="the Ohta-Kimura form reproduces simulated sigma_d^2 where the "
          "identity measure does not",
    model_lean="(10 + rho)/((2 + rho)(11 + rho)), rho = 4 Ne c -- the "
               "Ohta-Kimura APPROXIMATION to sigma_d^2, not E[r^2] itself",
    model_ref="refs.ohta_kimura_sigma_d_sq, written independently",
    reference="refs.ohta_kimura_sigma_d_sq",
    grid=grid(Ne=[150.0], c=[0.5 / 600, 2.0 / 600, 10.0 / 600, 40.0 / 600]),
    lean=lambda D, Ne, c: D["ohtaKimuraSigmaDSq"](Ne, c),
    ref=lambda Ne, c: refs.ohta_kimura_sigma_d_sq(Ne, c),
    note=(
        "PENDING: this check names a definition that does not exist yet. It is "
        "written first deliberately, so the definition arrives with its "
        "validation attached rather than acquiring one later.\n\n"
        "The definition is DELIBERATELY UNCALLED. It exists because the corpus "
        "has no sigma_d^2 at all -- a whole-table search for E[r^2], sigma_d^2 "
        "or expected r-squared returns only identity-by-descent definitions. "
        "A later de-duplication pass should read this reason rather than the "
        "absence of callers.\n\n"
        "Measured against cluster/fam_ld_decay.py: within 3.5% of simulation "
        "at rho = 0.5 and 1% at rho = 2, where the identity measure "
        "driftLDEquilibrium is +76% and +45%. The two converge by rho = 10, "
        "which is why the grid reaches below it."
    ),
    canfail_clause=(
        "rho must reach below 10. Ohta-Kimura and the identity measure agree "
        "to 2% by rho = 100, so a loosely-linked grid validates both forms and "
        "distinguishes nothing."
    ),
)

check(
    id="driftLDTrajectory-converges",
    fqn="Calibrator.LDDecayTheory.driftLDTrajectory",
    claim="iterating driftLDStep from Q0=0 reaches driftLDEquilibrium",
    model_lean="iterated step",
    model_ref="exact fixed point",
    reference="refs.ld_ibd_equilibrium_exact",
    grid=grid(Ne=[100.0, 1000.0], c=[1e-3, 1e-2]),
    lean=lambda D, Ne, c: D["driftLDTrajectory"](Ne, c, 0.0, 60000),
    ref=lambda Ne, c: refs.ld_ibd_equilibrium_exact(Ne, c),
    tol=1e-6,
    canfail_clause="Q0 must differ from the equilibrium; Q0=0 is chosen for that reason",
)

# --- 7. Selection-migration -------------------------------------------------
def _sel_mig_fixed_point(s: float, m: float, selection_first: bool) -> float:
    """Deterministic iteration of the continent-island map to its fixed point.

    MODEL: haploid continent-island, continent fixed for the alternative
    allele, selection coefficient s favouring the island allele, migration m.
    No sampling: the map is deterministic, so iterating it IS the exact answer.
    """
    p = 0.5
    for _ in range(200000):
        if selection_first:
            q = (1 - m) * (p * (1 + s) / (1 + s * p))
        else:
            q = ((1 - m) * p) * (1 + s) / (1 + s * ((1 - m) * p))
        if abs(q - p) < 1e-15:
            return q
        p = q
    return p


check(
    id="selectionMigrationEquilibrium",
    fqn="Calibrator.PopulationGeneticsFoundations.selectionMigrationEquilibrium",
    claim="closed form vs the exact fixed point of its own one-generation map",
    model_lean="max 0 ((s - m - m*s)/s), selection-first ordering",
    model_ref="deterministic iteration of continentIslandStepSelectionFirst",
    reference="_sel_mig_fixed_point",
    grid=grid(s=[0.01, 0.05, 0.2], m=[0.001, 0.01, 0.05, 0.2]),
    lean=lambda D, s, m: D["selectionMigrationEquilibrium"](s, m),
    ref=lambda s, m: _sel_mig_fixed_point(s, m, True),
    tol=1e-6,
    canfail_clause=(
        "grid must straddle m = s. Below it the polymorphism is protected and "
        "any formula of the right shape looks fine; at and above m = s the "
        "allele is lost and a wrong formula returns a positive frequency."
    ),
)

check(
    id="alleleFreqAfterMigration",
    fqn="Calibrator.PopulationGeneticsFoundations.alleleFreqAfterMigration",
    claim="p_c + (p0-p_c)(1-m)^t is the exact solution of the migration recursion",
    model_lean="continent-island, no selection or drift",
    model_ref="deterministic iteration p' = (1-m)p + m*p_c",
    reference="direct iteration",
    grid=grid(p0=[0.1, 0.9], p_c=[0.3, 0.7], m=[0.001, 0.05], t=[1, 10, 200]),
    lean=lambda D, p0, p_c, m, t: D["alleleFreqAfterMigration"](p0, p_c, m, t),
    ref=lambda p0, p_c, m, t: _iterate_migration(p0, p_c, m, t),
    canfail_clause="p0 != p_c required; otherwise the frequency never moves",
)


def _iterate_migration(p0: float, p_c: float, m: float, t: int) -> float:
    p = p0
    for _ in range(t):
        p = (1 - m) * p + m * p_c
    return p


# --- 8. Admixture -----------------------------------------------------------
def _admixed_fst_exact(alpha: float, p_a: float, p_b: float) -> float:
    """Nei G_ST between an admixed population and source A, computed directly.

    MODEL: p_C = alpha*p_A + (1-alpha)*p_B, parametric frequencies, biallelic.
    No approximation -- G_ST is evaluated on the actual frequency pair.
    """
    return refs.fst_nei_gst(p_a, alpha * p_a + (1 - alpha) * p_b)


check(
    id="admixedFst-ratio-not-numerator",
    fqn="Calibrator.DemographicHistory.admixedFst",
    claim="(1-alpha)^2 scaling ignores that F_ST is a ratio, not a numerator",
    model_lean="F_ST(C,A) = (1-alpha)^2 * F_ST(A,B)",
    model_ref="G_ST evaluated directly on (p_A, p_C)",
    reference="_admixed_fst_exact",
    grid=grid(alpha=[0.1, 0.3, 0.5, 0.8], p_a=[0.1, 0.3], p_b=[0.6, 0.9]),
    lean=lambda D, alpha, p_a, p_b: D["admixedFst"](
        alpha, refs.fst_nei_gst(p_a, p_b)
    ),
    ref=lambda alpha, p_a, p_b: _admixed_fst_exact(alpha, p_a, p_b),
    kind="formula",
    canfail_clause=(
        "REQUIRES pbar to move with alpha, i.e. p_a and p_b far apart and "
        "both away from 0.5. If p_a + p_b = 1 the denominators coincide and "
        "the (1-alpha)^2 numerator scaling is exactly right -- a symmetric "
        "frequency pair makes this check unable to fail."
    ),
)

# --- 9. Cross-name duplicates ----------------------------------------------
# The three `dup-islandModelFst-*` entries were REMOVED because the duplication
# they detected has been REPAIRED. islandModelFst, equilibriumFst and
# fstMigDriftEquil were absorbed into fstMigrationDriftEquilibrium in 4decc9cd;
# the corpus previously carried Lean-proved bridge theorems asserting they were
# equal rather than collapsing them. A duplicate-detection check whose two sides
# are now the same definition compares that definition to itself and reports
# 0.0 forever, which is a passing check that has stopped meaning anything.
#
# Kept below: the one pair that is still genuinely two definitions.
for _dup_id, _a, _b, _args in [
    ("dup-effectiveMigration-effectiveSymmetricMigration",
     "effectiveMigration", "effectiveSymmetricMigration",
     grid(Ne=[0.001, 0.02], m=[0.004, 0.05])),
]:
    check(
        id=_dup_id,
        fqn=f"Calibrator.*.{_a}",
        claim=f"DUPLICATE: {_a} and {_b} are the same function",
        model_lean="-", model_ref="-",
        reference=f"Calibrator.*.{_b}",
        grid=_args,
        lean=(lambda a: lambda D, Ne, m: D[a](Ne, m))(_a),
        ref=(lambda b: lambda D, Ne, m: D[b](Ne, m))(_b),
        kind="identity",
        note=f"peer={_b}",
        canfail_clause="arguments differ between rows; identical bodies give 0 error by construction",
    )


# --- 10. Additional differential checks ------------------------------------
check(
    id="pairwiseFstFromBranchTaus-correct-composition",
    fqn="Calibrator.PortabilityDrift.pairwiseFstFromBranchTaus",
    claim="the tau-additive composition IS the exact two-branch split F_ST",
    model_lean="F = fstFromTau(tauS + tauT)",
    model_ref="clean split, total separation tS+tT, equal sizes",
    reference="refs.split_fst_hudson",
    grid=grid(tS=[200.0, 1000.0, 4000.0], tT=[200.0, 1000.0, 4000.0], Ne=[1000.0]),
    lean=lambda D, tS, tT, Ne: D["pairwiseFstFromBranchTaus"](
        D["coalescentTau"](tS, Ne), D["coalescentTau"](tT, Ne)
    ),
    ref=lambda tS, tT, Ne: refs.split_fst_hudson(tS + tT, Ne, Ne, Ne),
    note=(
        "PortabilityDrift contains both compositions; this one is exact and "
        "pairwiseFstFromBranches is not. They are not alternatives."
    ),
    canfail_clause=(
        "tS+tT of order Ne, and tS != tT rows included so an incorrect "
        "symmetric-only composition cannot hide."
    ),
)

check(
    id="expectedHeterozygosity-equals-hetEquilibrium",
    fqn="Calibrator.PopulationGeneticsFoundations.expectedHeterozygosity",
    claim="theta/(1+theta) composed with theta=4Ne mu reproduces hetEquilibrium",
    model_lean="infinite alleles, mutation-drift balance",
    model_ref="same file, hetEquilibrium Ne mu",
    reference="Calibrator.PopulationGeneticsFoundations.hetEquilibrium",
    grid=_MD,
    lean=lambda D, Ne, mu: D["expectedHeterozygosity"](D["scaledMutationRate"](Ne, mu)),
    ref=lambda D, Ne, mu: D["hetEquilibrium"](Ne, mu),
    kind="identity",
    canfail_clause="identity by construction; recorded as a duplicate, not a validation",
)

check(
    id="ldCorrelationFromMigration-vs-sharedLD-squared",
    fqn="Calibrator.PopulationGeneticsFoundations.ldCorrelationFromMigration",
    claim="M^2/(1+M)^2 is exactly the square of PortabilityDrift.sharedLDFromMigration",
    model_lean="proportion of LD that is shared, as a function of M=4Nm",
    model_ref="sharedLDFromMigration(M)^2 = (1 - islandModelFst)^2",
    reference="Calibrator.PortabilityDrift.sharedLDFromMigration ** 2",
    grid=grid(M=[0.1, 1.0, 4.0, 40.0]),
    lean=lambda D, M: D["ldCorrelationFromMigration"](M),
    ref=lambda D, M: D["sharedLDFromMigration"](M) ** 2,
    kind="internal",
    note=(
        "CONSISTENT: PopulationGeneticsFoundations.ldCorrelationFromMigration "
        "is exactly the square of PortabilityDrift.sharedLDFromMigration, i.e. "
        "(1 - islandModelFst)^2. Both are 'shared LD' but one is a correlation "
        "and the other its square; the relation is exact and now recorded."
    ),
    canfail_clause="M must be away from the fixed points of x->x^2 (0 and 1); M=1 gives 0.25 vs 0.5",
)

check(
    id="targetHetFromFst-tautology",
    fqn="Calibrator.PortabilityDrift.targetHetFromFst",
    claim="het_source*(1-fst) is exactly the rearrangement of fstFromHetRatio",
    model_lean="F_ST defined as fractional heterozygosity loss",
    model_ref="PopulationGeneticsFoundations.fstFromHetRatio inverted",
    reference="algebraic inverse of fstFromHetRatio",
    grid=grid(het_source=[0.1, 0.3], fst=[0.05, 0.2, 0.5]),
    lean=lambda D, het_source, fst: D["fstFromHetRatio"](
        D["targetHetFromFst"](het_source, fst), het_source
    ),
    ref=lambda het_source, fst: fst,
    kind="identity",
    note=(
        "confirms the corpus's own VACUOUS annotation: this round-trips to the "
        "identity and so carries no empirical content about F_ST"
    ),
    canfail_clause=(
        "none available. The composition is the identity for every input, so "
        "no grid can make it fail -- which is the finding, not a defect of "
        "the check."
    ),
)

check(
    id="neutralAFBenchmarkRatio-bounded",
    fqn="Calibrator.PortabilityDrift.neutralAFBenchmarkRatio",
    claim="(1-fstT)/(1-fstS) vs the heterozygosity ratio it is meant to be",
    model_lean="ratio of retained heterozygosity, drift-only closed population",
    model_ref="exact IAM heterozygosity ratio between two branches at "
              "mutation-drift balance",
    reference="refs.iam_het_trajectory ratio",
    grid=grid(tS=[500.0, 4000.0], tT=[500.0, 4000.0], Ne=[1000.0], mu=[1e-5]),
    lean=lambda D, tS, tT, Ne, mu: D["neutralAFBenchmarkRatio"](
        D["fstFromGenerations"](tS, Ne), D["fstFromGenerations"](tT, Ne)
    ),
    ref=lambda tS, tT, Ne, mu: (
        refs.iam_het_trajectory(Ne, mu, refs.iam_het_equilibrium(Ne, mu), int(tT))
        / refs.iam_het_trajectory(Ne, mu, refs.iam_het_equilibrium(Ne, mu), int(tS))
    ),
    kind="model",
    note=(
        "the reference starts each branch AT equilibrium, so the true ratio is "
        "1: mutation replenishes what drift removes. The definition predicts a "
        "ratio far from 1 because its model has no mutation."
    ),
    canfail_clause=(
        "tS != tT is mandatory. At tS = tT the definition returns exactly 1 "
        "and so does the reference -- the symmetric design in which both sides "
        "collapse to 1 is precisely the false-validation failure mode."
    ),
)

check(
    id="wrightFIT-composition",
    fqn="Calibrator.PopulationGeneticsFoundations.wrightFIT",
    claim="1-(1-F_IS)(1-F_ST) is Wright's exact F-statistic composition",
    model_lean="hierarchical F-statistics",
    model_ref="Wright (1951): (1-F_IT) = (1-F_IS)(1-F_ST), definitionally",
    reference="Wright's identity",
    grid=grid(f_IS=[0.0, 0.05, 0.3], f_ST=[0.0, 0.05, 0.2, 0.5]),
    lean=lambda D, f_IS, f_ST: D["wrightFIT"](f_IS, f_ST),
    ref=lambda f_IS, f_ST: 1 - (1 - f_IS) * (1 - f_ST),
    canfail_clause="both f_IS and f_ST nonzero in at least one row; at f_IS=0 it reduces to f_ST",
)

# `excessLDAfterBottleneck` is deliberately NOT checked here.  The only
# reference available without simulation is a loose upper bound, and a bound
# with a tolerance wide enough to hold is a check that cannot fail.  It is
# queued for the stochastic tier instead (see HEAVY_QUEUE.md).


# --- 11. The drift/LD recurrences (available since extract added ℕ-recursion) ---

check(
    id="hetRecurrence-at-mutation-drift-balance",
    fqn="Calibrator.hetRecurrence",
    claim="MODEL, THE CLUSTER ROOT: a population AT equilibrium loses no "
          "heterozygosity, where the closed-population recurrence predicts 86%",
    model_lean="closed population, NO mutation: H(t) = H0 (1 - 1/2Ne)^t",
    model_ref="same Ne, same t, but at mutation-drift balance: start at H* and "
              "run the exact infinite-alleles trajectory, which stays at H*",
    reference="refs.iam_het_trajectory started from refs.iam_het_equilibrium",
    grid=grid(Ne=[1000.0], mu=[1e-6, 1e-5, 1e-4], t=[200, 1000, 4000]),
    lean=lambda D, Ne, mu, t: (
        D["hetRecurrence"](Ne, refs.iam_het_equilibrium(Ne, mu), t)
        / refs.iam_het_equilibrium(Ne, mu)
    ),
    ref=lambda Ne, mu, t: (
        refs.iam_het_trajectory(Ne, mu, refs.iam_het_equilibrium(Ne, mu), t)
        / refs.iam_het_equilibrium(Ne, mu)
    ),
    kind="model",
    note=(
        "Both sides are RETENTION RATIOS, so the comparison is scale-free. The "
        "recurrence is correct for what it says -- a closed population with no "
        "mutation -- and the reference is correct for a population at "
        "mutation-drift balance. They are different populations, not two "
        "calibrations of one quantity. Fixing the algebra would change nothing."
    ),
    canfail_clause=(
        "t must reach order 2Ne. At t << 2Ne the recurrence has barely decayed "
        "and both sides sit near 1.0 -- the both-sides-collapse-to-1 geometry "
        "exactly. The mu axis is also required: it moves the reference's "
        "equilibrium but not the recurrence, which has no mu argument at all."
    ),
)

check(
    id="ldRecurrence-drops-drift",
    fqn="Calibrator.ldRecurrence",
    claim="INTERNAL: D0(1-r)^t omits the drift factor that ldRetentionPerGen carries",
    model_lean="D(t) = D0 (1-r)^t; no Ne argument",
    model_ref="ldRetentionPerGen(r, Ne)^t = [(1-r)(1-1/2Ne)]^t [same file]",
    reference="Calibrator.ldRetentionPerGen ** t",
    grid=grid(r=[0.0, 1e-4, 1e-2], Ne=[100.0, 10000.0], t=[10, 500]),
    lean=lambda D, r, Ne, t: D["ldRecurrence"](r, 1.0, t),
    ref=lambda D, r, Ne, t: D["ldRetentionPerGen"](r, Ne) ** t,
    kind="internal",
    note=(
        "ldRecurrence is the Ne -> infinity limit of ldAfterGenerations in the "
        "same file. Under Hill & Robertson the drift factor is not optional: "
        "E[D] decays by (1-r)(1-1/2Ne) per generation, not (1-r)."
    ),
    canfail_clause=(
        "Ne must be SMALL (100) and t large. At Ne=10000 the drift factor is "
        "1-5e-5 per generation and the two agree to <3% over 500 generations, "
        "so a large-Ne-only grid cannot fail."
    ),
)

check(
    id="hetTrajectory-vs-exact-iam",
    fqn="Calibrator.hetTrajectory",
    claim="PortabilityDrift's trajectory reproduces the exact IAM trajectory",
    model_lean="iterated hetStepWithMutation",
    model_ref="exact IAM recursion",
    reference="refs.iam_het_trajectory",
    grid=grid(Ne=[100.0, 1000.0], mu=[1e-5, 1e-4, 1e-3], t=[100, 1000, 10000]),
    lean=lambda D, Ne, mu, t: D["hetTrajectory"](Ne, mu, 0.0, t),
    ref=lambda Ne, mu, t: refs.iam_het_trajectory(Ne, mu, 0.0, t),
    tol=1e-2,
    canfail_clause=(
        "H0 must differ from H*, and t must not be so large that both sides "
        "have converged -- at t -> inf this degenerates into the equilibrium "
        "check and cannot see a wrong eigenvalue."
    ),
)


# --- 12. Variable-Ne drift (callable since extract added sequence arguments) ---

# Deliberately asymmetric size histories. A constant history makes the
# harmonic mean trivially equal to Ne and the product equal to a power, so
# several of these checks would be unable to fail on one.
_BOTTLENECK = [1000.0] * 20 + [10.0] * 5 + [1000.0] * 20
_MILD = [1000.0] * 50
_RAMP = [float(n) for n in range(50, 550, 50)]
_SEVERE = [2.0] * 6

check(
    id="harmonicMeanNe-is-harmonic-mean",
    fqn="Calibrator.harmonicMeanNe",
    claim="T / sum(1/Ne_i) is the harmonic mean, as named",
    model_lean="none; arithmetic",
    model_ref="same",
    reference="refs.harmonic_mean",
    grid=[{"nes": _BOTTLENECK}, {"nes": _RAMP}, {"nes": _MILD}, {"nes": _SEVERE}],
    lean=lambda D, nes: D["harmonicMeanNe"](nes),
    ref=lambda nes: refs.harmonic_mean(nes),
    canfail_clause=(
        "the histories MUST be non-constant. On a constant history the "
        "harmonic mean equals Ne and so does almost any plausible average, so "
        "an equal-size grid cannot distinguish harmonic from arithmetic or "
        "geometric. _BOTTLENECK and _RAMP carry that asymmetry; _MILD is the "
        "degenerate control and is expected to be uninformative."
    ),
)

check(
    id="cumulativeDrift-first-order",
    fqn="Calibrator.cumulativeDrift",
    claim="MODEL: sum 1/(2Ne_i) is the first-order expansion of the exact "
          "cumulative drift, not the drift itself",
    model_lean="sum_i 1/(2 Ne_i)",
    model_ref="-sum_i log(1 - 1/(2 Ne_i)), exact in log units",
    reference="refs.cumulative_drift_log_exact",
    grid=[{"nes": _BOTTLENECK}, {"nes": _RAMP}, {"nes": _MILD}, {"nes": _SEVERE}],
    lean=lambda D, nes: D["cumulativeDrift"](nes),
    ref=lambda nes: refs.cumulative_drift_log_exact(nes),
    tol=1e-3,
    kind="model",
    canfail_clause=(
        "REQUIRES at least one generation with SMALL Ne. The expansion error "
        "is O(1/Ne^2) per generation, so a history that never drops below "
        "Ne=1000 agrees to 1e-7 and the check is vacuous. _SEVERE (Ne=2) and "
        "_BOTTLENECK (Ne=10) supply the regime; _MILD is the control."
    ),
)

check(
    id="fstVariableNe-vs-exact-product",
    fqn="Calibrator.fstVariableNe",
    claim="1 - exp(-sum 1/(2Ne_i)) vs the exact 1 - prod(1 - 1/(2Ne_i))",
    model_lean="exponential approximation of a product of survival terms",
    model_ref="exact Wright-Fisher non-coalescence product",
    reference="refs.cumulative_inbreeding_exact",
    grid=[{"nes": _BOTTLENECK}, {"nes": _RAMP}, {"nes": _MILD}, {"nes": _SEVERE}],
    lean=lambda D, nes: D["fstVariableNe"](nes),
    ref=lambda nes: refs.cumulative_inbreeding_exact(nes),
    tol=1e-3,
    kind="model",
    note=(
        "shares the closed-population no-mutation model of the fstDerived "
        "cluster; this check tests only the approximation, NOT whether the "
        "quantity is a split F_ST -- see hetRecurrence-at-mutation-drift-balance "
        "for that, which is the larger error"
    ),
    canfail_clause=(
        "same as cumulativeDrift: needs a generation at small Ne. On _MILD the "
        "two agree to 1e-5."
    ),
)

check(
    id="fstVariableNe-equals-harmonic-mean-substitution",
    fqn="Calibrator.fstVariableNe",
    claim="the variable-Ne F equals the constant-Ne exponential form evaluated "
          "at the harmonic mean",
    model_lean="1 - exp(-cumulativeDrift Ne)",
    model_ref="1 - exp(-T/(2 * harmonicMeanNe Ne)), same file",
    reference="Calibrator.harmonicMeanNe substituted into the exponential form",
    grid=[{"nes": _BOTTLENECK}, {"nes": _RAMP}, {"nes": _MILD}, {"nes": _SEVERE}],
    lean=lambda D, nes: D["fstVariableNe"](nes),
    ref=lambda D, nes: 1.0 - math.exp(-len(nes) / (2.0 * D["harmonicMeanNe"](nes))),
    kind="identity",
    note=(
        "exact by construction: T/N_harmonic = sum 1/Ne_i. Recorded so the "
        "corpus's harmonic-mean claim is pinned rather than assumed."
    ),
    canfail_clause="identity by construction; reported as such, not as a validation",
)

check(
    id="ldMismatchFrobenius-exact",
    fqn="Calibrator.ldMismatchFrobenius",
    claim="frobeniusNormSq (Sig_S - Sig_T) is the squared Frobenius distance",
    model_lean="none; linear algebra",
    model_ref="same, computed elementwise",
    reference="refs.frobenius_norm_sq",
    grid=[
        {"a": [[1.0, 0.5], [0.5, 1.0]], "b": [[1.0, 0.1], [0.1, 1.0]]},
        {"a": [[1.0, 0.9], [0.9, 1.0]], "b": [[1.0, -0.4], [-0.4, 1.0]]},
        {"a": [[2.0, 0.0], [1.0, 3.0]], "b": [[0.0, 0.0], [0.0, 0.0]]},
    ],
    lean=lambda D, a, b: D["ldMismatchFrobenius"](a, b),
    ref=lambda a, b: refs.frobenius_norm_sq(a, b),
    canfail_clause=(
        "at least one grid row must be ASYMMETRIC (row 3) and one must have "
        "off-diagonals of opposite sign (row 2). On symmetric matrices with "
        "matching diagonals a transposed or diagonal-only reading gives the "
        "same number."
    ),
)
