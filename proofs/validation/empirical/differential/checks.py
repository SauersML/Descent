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
        "grid must include |p1-p2| large: at p1=p2 both sides are 0 and no "
        "grid confined there can separate the conventions. It need NOT avoid "
        "pbar=0.5 -- see the CORRECTION note on simpleFst-vs-hudson; the two "
        "conventions differ at pbar=0.5 too, by up to a factor of 2."
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
    canfail_clause=(
        "needs p1 != p2. Do NOT weaken this to 'needs pbar != 0.5': Nei and "
        "Hudson do not coincide at pbar=0.5, and "
        "cluster/fam_fst_allel_crosscheck.py cell C3 measures it. The exact "
        "conversion Hudson = 2G/(1+G) has 2G/(1+G) = G only at G in {0,1}, so "
        "the two coincide only at p1 = p2 (or complete fixation). At pbar=0.5 "
        "exactly, (p1,p2) = (0.525,0.475) gives NEI_GST 0.0025 against HUDSON "
        "0.0049875, a ratio of 1.995, and (0.9,0.1) gives 0.64 against "
        "0.780488, ratio 1.2195. The clause was harmless here -- _PQ contains "
        "pbar=0.5 rows and they separate the conventions fine -- but it named "
        "a degeneracy that does not exist, which would have licensed dropping "
        "exactly the rows that discriminate best at small divergence."
    ),
)

check(
    id="hudsonFst-is-hudson",
    fqn="Calibrator.Conventions.hudsonFst",
    claim="POSITIVE CONTROL for the convention pin: hudsonFst really is "
          "Hudson's parametric F_ST",
    model_lean="(p1-p2)^2 / (p1(1-p2) + p2(1-p1)), Bhatia 2013 eq 10",
    model_ref="same, computed independently in refs",
    reference="refs.fst_hudson",
    grid=_PQ,
    lean=lambda D, p1, p2: D["hudsonFst"](p1, p2),
    ref=lambda p1, p2: refs.fst_hudson(p1, p2),
    note=(
        "This exists so that `simpleFst-vs-hudson` failing is INTERPRETABLE. "
        "Without it a reader cannot tell whether that check disagrees because "
        "the corpus definition is Nei or because refs.fst_hudson is wrong. "
        "With it, one of the pair passing to machine precision while the other "
        "differs by up to 50% localises the disagreement to the definition."
    ),
    canfail_clause=(
        "the grid must contain p1 != p2; at p1 = p2 every check in this group "
        "goes degenerate because all estimators return 0. The grid does NOT "
        "need to stay off pbar = 0.5 -- "
        "see simpleFst-vs-hudson's clause and cell C3 of "
        "cluster/fam_fst_allel_crosscheck.py, which measures a factor of "
        "1.995 between the conventions AT pbar = 0.5 exactly."
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
    id="heterozygosityLossDerived-is-not-split-fst",
    fqn="Calibrator.PopulationGeneticsFoundations.heterozygosityLossDerived",
    claim="MODEL: the drift recurrence is not the F_ST of a split",
    model_lean="closed population, NO mutation: 1-(1-1/2Ne)^t",
    model_ref="clean split at mutation-drift equilibrium, infinite sites",
    reference="refs.split_fst_hudson",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["heterozygosityLossDerived"](Ne, int(t)),
    ref=lambda t, Ne: refs.split_fst_hudson(t, Ne, Ne, Ne),
    kind="model",
    note="root of the heterozygosityLossDerived/fstFromTau/targetHetFromFst cluster",
    canfail_clause=(
        "REQUIRES t/(2Ne) >= ~0.5. Both sides are t/(2Ne) + O(t^2/Ne^2), so at "
        "t << Ne they agree to <1% and the test is vacuous."
    ),
)

check(
    id="heterozygosityLossDerived-is-coalescence-prob",
    fqn="Calibrator.PopulationGeneticsFoundations.heterozygosityLossDerived",
    claim="what heterozygosityLossDerived actually computes: P(coalesce within t) in a closed pop",
    model_lean="closed population, no mutation",
    model_ref="same",
    reference="refs.prob_coalesce_within",
    grid=_SPLIT,
    lean=lambda D, t, Ne: D["heterozygosityLossDerived"](Ne, int(t)),
    ref=lambda t, Ne: refs.prob_coalesce_within(t, Ne),
    canfail_clause="t >= 1 and Ne finite; at t=0 both sides are 0",
)

check(
    id="hetLossFromDrift-duplicates-heterozygosityLossDerived",
    fqn="Calibrator.PopulationGeneticsFoundations.heterozygosityLossFromDrift",
    claim="DUPLICATE: identical body to heterozygosityLossDerived under a different name",
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
    canfail_clause="t of order Ne (see heterozygosityLossDerived-is-not-split-fst)",
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
    id="islandFstFiniteDemes-is-the-finite-form",
    fqn="Calibrator.PopulationGeneticsFoundations.islandFstFiniteDemes",
    claim="POSITIVE CONTROL for islandModelFst-finite-demes: the corpus's "
          "finite-deme form really is 1/(1+4Nm(d/(d-1))^2)",
    model_lean="d demes of size Ne, symmetric migration m, mutation negligible",
    model_ref="same, computed independently in refs",
    reference="refs.island_fst_finite_demes",
    grid=grid(Ne=[1000.0], m=[1e-4, 1e-3, 1e-2], d=[2, 5, 10, 40]),
    lean=lambda D, Ne, m, d: D["islandFstFiniteDemes"](Ne, m, float(d)),
    ref=lambda Ne, m, d: refs.island_fst_finite_demes(Ne, m, d),
    note=(
        "This exists so that `islandModelFst-finite-demes` failing is "
        "INTERPRETABLE, and it is the same omission that let the F_ST "
        "convention claim survive for three passes: a check that reports a "
        "disagreement cannot say WHICH side is wrong unless something pins "
        "the other side. Until now the finite-deme reference was unpinned, so "
        "'the corpus limit disagrees with refs by 74.5% at d=2' was equally "
        "consistent with refs.island_fst_finite_demes being wrong.\n\n"
        "With the pair, one passing to machine precision while the other "
        "differs localises the disagreement to the infinite-island limit, "
        "which is the thing actually being claimed about."
    ),
    canfail_clause=(
        "shares the grid of islandModelFst-finite-demes deliberately, so the "
        "two are evaluated at identical cells and the comparison between them "
        "is exact rather than approximate. d=2 must stay: it is where the "
        "correction factor is largest (4x) and so where a sign or reciprocal "
        "error in the correction would show up first."
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
    lean=lambda D, Ne, m, mu: D["steppingStoneCharacteristicLength"](m, 1.0, mu),
    ref=lambda Ne, m, mu: refs.stepping_stone_decay_scale_malecot(m, mu),
    kind="formula",
    note=(
        "SIMULATED, and the repair is VALIDATED. cluster/fam_stepping_stone.py "
        "measures the spatial autocovariance decay length on a Wright-Fisher "
        "lattice at mutation-migration-drift equilibrium.\n\n"
        "CONVENTION FIRST, because it is the whole story. The corpus mu is "
        "INFINITE-ALLELES -- the docstring says identity is destroyed in the "
        "two lineages at rate 2*mu -- while the simulator's symmetric "
        "two-allele model at mu_sim decays the covariance at 4*mu_sim. So "
        "mu_corpus = 2*mu_sim. Comparing without that conversion reports a "
        "spurious +44%; applying the definition's OWN DECLARED CONVENTION "
        "gives agreement within 2.2% on every sigma^2 = 1 cell, across 16x in "
        "mu, 25x in Ne and 8x in m. That is a conversion, not a discrepancy, "
        "and it is recorded here so it is not rediscovered as a defect.\n\n"
        "The EXPONENTS are what make this a validation rather than a "
        "coincidence, since each one separates the old body from the new:\n"
        "    d log L / d log mu  = -0.502   (corrected -1/2; OLD BODY 0)\n"
        "    d log L / d log Ne  = -0.000   (corrected 0;    OLD BODY +1/2)\n"
        "    d log L / d log m   = +0.510   (corrected +1/2)\n"
        "A magnitude agreement can be a coincidence; three exponents cannot.\n\n"
        "CLOSED. The fourth exponent, d log L / d log sigma^2 = +0.475 against "
        "a corpus value of 0, was the remaining defect; the definition now "
        "carries sigma_sq and `steppingStoneLength-missing-sigma-squared` "
        "below guards it. That exponent is what settled it, and the reason is "
        "worth keeping: a constant factor on the mutation rate shifts every L "
        "equally and CANNOT MOVE AN EXPONENT, so the sigma^2 finding survives "
        "the very question that dissolved the apparent +44% above into a "
        "convention artefact.\n\n"
        "This check passes 1.0 for sigma_sq because "
        "refs.stepping_stone_decay_scale_malecot is the unit-dispersal "
        "reference. Lean's steppingStoneCharacteristicLength_at_unit_dispersal "
        "proves that slice equals the old two-argument body, so this check "
        "still measures exactly what it measured before the signature changed."
    ),
    canfail_clause=(
        "the grid MUST vary mu at fixed Ne and m: the Lean value is constant "
        "along that axis while the reference moves as mu^-1/2. Varying only "
        "Ne and m would let a fitted constant hide the error.\n\n"
        "It must ALSO keep the Ne axis even though both sides are flat along "
        "it. That axis is not a discriminator, it is a regression guard: the "
        "pre-repair body went as sqrt(Ne), so an edit that reintroduces an Ne "
        "dependence fires here and nowhere else."
    ),
)

# Do NOT add a check comparing 1 - exp(-d/L) against d/(d + 4 Ne m sigma^2).
#
# There is no exponential side to compare: `continuousSteppingStoneFst` is not in
# the corpus. A check of that shape reported an 878% disagreement, and the
# resolution was to remove one side rather than tune a tolerance, because the
# coalescent derivation in DemographicHistory yields the hyperbolic form
# exactly and the exponential is not derivable from it -- no choice of L
# reconciles them beyond first order.
#
# A check whose Lean side no longer exists cannot fail informatively, so
# keeping it would have meant a permanent KeyError dressed up as coverage. The
# surviving side is still checked by `demoSteppingStoneFst-exact` below.
def _ss_length_with_sigma(m: float, mu: float, sigma_sq: float) -> float:
    return math.sqrt(m * sigma_sq / (2.0 * mu))


def _ss_lattice_meeting_time(d: float, D: float, sigma_sq: float, m: float) -> float:
    """Expected time for two lineages d demes apart to first share a deme, on a
    lattice of D demes.

    MODEL: 1D stepping stone, D demes, symmetric nearest-neighbour migration m,
    dispersal variance sigma^2.  The separation is a random walk absorbed at 0
    and D, so the expected absorption time is d(D-d)/(2 sigma^2 m).

    Note what the corpus's `steppingStoneDiffusionTimescale` is instead: this
    divided by (D-d).  That is not a small correction -- at d=1, D=256 the
    corpus value is 5.0 against a measured 1344.2.
    """
    return d * (D - d) / (2.0 * sigma_sq * m)


check(
    id="steppingStoneLength-missing-sigma-squared",
    fqn="Calibrator.PopulationGeneticsFoundations.steppingStoneCharacteristicLength",
    claim="the decay length scales as sqrt(sigma^2); REPAIRED, this is now the "
          "standing check that it still does",
    model_lean="L = sqrt(m sigma^2/(2 mu)) -- three arguments, dispersal "
               "variance carried explicitly",
    model_ref="Malecot/Kimura-Weiss on a lattice of dispersal variance "
              "sigma^2: L = sqrt(m sigma^2/(2 mu))",
    reference="_ss_length_with_sigma",
    grid=grid(m=[1e-2, 0.1], mu=[1e-6, 1e-4], sigma_sq=[1.0, 2.0, 4.0]),
    lean=lambda D, m, mu, sigma_sq: D["steppingStoneCharacteristicLength"](
        m, sigma_sq, mu
    ),
    ref=lambda m, mu, sigma_sq: _ss_length_with_sigma(m, mu, sigma_sq),
    kind="formula",
    note=(
        "MEASURED by cluster/fam_stepping_stone.py, on a migration kernel "
        "whose dispersal variance is SET and then measured back by control "
        "F2, never fitted. Four exponents, measured against corpus and truth:\n"
        "    d log L / d log mu      -0.482   (-0.5 | -0.5)   old body: 0\n"
        "    d log L / d log Ne      +0.003   ( 0.0 |  0.0)   old body: +0.5\n"
        "    d log L / d log m       +0.511   (+0.5 | +0.5)\n"
        "    d log L / d log sigma^2 +0.475   ( 0.0 | +0.5)   <-- this check\n"
        "The first three VALIDATE the sqrt(2 Ne m) -> sqrt(m/(2 mu)) repair on "
        "every axis it was repaired along, and each separates the old body "
        "from the new, so the agreement is not a magnitude coincidence. The "
        "fourth was the defect: -26.9% at sigma^2 = 2, -49.3% at sigma^2 = 4.\n\n"
        "REPAIRED. The definition now takes (m, sigma_sq, mu) and its body is "
        "sqrt(m*sigma_sq/(2*mu)). This check has been converted from kind="
        "'scope' -- where it recorded a defect and was EXPECTED to disagree -- "
        "to kind='formula', where it is expected to AGREE and a disagreement "
        "is a regression. The id and grid are unchanged on purpose: the check "
        "that measured the defect is the check that now guards the repair, so "
        "the history stays attached to it and the sigma^2 axis cannot quietly "
        "stop being swept.\n\n"
        "The two siblings in the same family, demoSteppingStoneFst "
        "(d Ne m sigma_sq) and steppingStoneDiffusionTimescale (d sigma_sq m), "
        "both took sigma_sq explicitly all along; the family is no longer "
        "split on whether its lattice has one.\n\n"
        "Lean-side companion: steppingStoneCharacteristicLength_at_unit_"
        "dispersal proves the OLD two-argument body is exactly the sigma^2 = 1 "
        "slice of the new one, so the correction is a generalisation rather "
        "than a substitution. That is why the sibling check "
        "steppingStoneLength-missing-mutation can still compare against "
        "refs.stepping_stone_decay_scale_malecot -- which is the sigma^2 = 1 "
        "reference -- simply by passing 1.0."
    ),
    canfail_clause=(
        "sigma^2 must exceed 1 somewhere in the grid -- at sigma^2 = 1 the two "
        "sides are identically equal and the check cannot fail, which is "
        "exactly why the sigma_sq = 1.0 row is KEPT: it is the row that must "
        "AGREE, and a reference that disagreed there would be wrong.\n\n"
        "This axis is also the only convention-free one. A grid confined to "
        "mu, m or Ne cannot separate this defect from a mutation-rate "
        "convention mismatch, because a constant factor on mu rescales L "
        "uniformly; sigma^2 changes the exponent, which no constant can."
    ),
)


check(
    id="steppingStoneMeetingTime-lattice-form",
    fqn="Calibrator.DemographicHistory.steppingStoneMeetingTimeOnLattice",
    claim="the lattice meeting time is d(D-d)/(2 sigma^2 m), and the corpus's "
          "per-deme steppingStoneDiffusionTimescale is that divided by (D-d)",
    model_lean="random walk on D demes absorbed at 0 and D",
    model_ref="same, computed independently in refs",
    reference="_ss_lattice_meeting_time",
    grid=grid(d=[1.0, 8.0, 64.0], D=[256.0], sigma_sq=[1.0, 4.0], m=[1e-2, 0.1]),
    lean=lambda D_, d, D, sigma_sq, m: D_["steppingStoneMeetingTimeOnLattice"](
        d, D, sigma_sq, m
    ),
    ref=lambda d, D, sigma_sq, m: _ss_lattice_meeting_time(d, D, sigma_sq, m),
    note=(
        "Added because this definition had NO simulation behind it at all "
        "while carrying a numerical claim: `steppingStoneDiffusionTimescale` "
        "gives 5.0 at d=1, D=256 where the measured meeting time is 1344.2, a "
        "factor of (D-d) = 255. That factor was recorded in a docstring and "
        "nowhere else.\n\n"
        "Why no consumer-level check could have caught the original defect, "
        "which is the reason it needs its OWN check rather than inheriting "
        "coverage from demoSteppingStoneFst: the only consumer feeds it to "
        "`coalFst _ Ne` with the PER-DEME size rather than the metapopulation "
        "size D*Ne, so the lattice size cancels between the two arguments and "
        "the F_ST comes out right to 4.4% anyway. Two compensating omissions "
        "in a ratio are indistinguishable from a correct ratio from outside, "
        "and only a check on the meeting time ITSELF can separate them."
    ),
    canfail_clause=(
        "d must range over both ends: at d << D the (D-d) factor is nearly "
        "constant at D and could be absorbed by a refitted m*sigma^2, so a "
        "small-d-only grid could not distinguish the lattice form from the "
        "per-deme one. d = 64 against D = 256 makes (D-d) move by 25%, which "
        "no rescaling of m or sigma^2 can follow."
    ),
)

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
    note=(
        "SIMULATED, and it WINS. cluster/fam_stepping_stone.py solves the "
        "two-lineage coalescent on a circle of 256 demes exactly and compares "
        "every candidate F_ST(d) the corpus has ever carried. RMS relative "
        "error over d = 1..128 at m = 0.1, sigma^2 = 1:\n"
        "    demoSteppingStoneFst        0.044\n"
        "    steppingStoneFstQuadratic   0.622\n"
        "    steppingStoneFst (linear)   0.335\n"
        "    1 - exp(-d/L), L FITTED     0.163\n"
        "The exponential is given its best possible chance -- L is fitted "
        "freely to the measurement -- and is still 3.7x worse than the "
        "hyperbolic. That is empirical corroboration of the decision to delete "
        "continuousSteppingStoneFst, which was taken by derivation alone.\n\n"
        "Crucially, sigma^2 was SET (by the migration kernel) and not fitted. "
        "A freely fitted sigma^2 absorbs the extra power of the quadratic form "
        "exactly, which is the degeneracy demoSteppingStoneFst's own docstring "
        "records; the simulator holds sigma^2 at a value control F2 measures "
        "back, so the quadratic form can lose, and it does.\n\n"
        "TWO REGIME BOUNDS FOUND, one at each end of the d range.\n\n"
        "FAR END: agreement degrades to -6.6% at d = D/2, because the exact "
        "circle result is d(D-d)/(...) and the corpus form is its d << D "
        "limit. Nothing in the corpus states that limit.\n\n"
        "NEAR END, and this is the experiment the docstring records as never "
        "having been done. Two cells with IDENTICAL m*sigma^2 = 0.1, sigma^2 "
        "set by the kernel and measured back by F2, so the degeneracy the "
        "docstring describes is broken by construction. demoSteppingStoneFst "
        "sees the pair only through m*sigma^2 and predicts the same F_ST in "
        "both:\n"
        "    d=1    measured 0.0968 vs 0.2638   demo 0.0909 both  (2.7x apart)\n"
        "    d=4    measured 0.2893 vs 0.3854   demo 0.2857 both\n"
        "    d=16   measured 0.6057 vs 0.6372   demo 0.6154 both\n"
        "    d=128  measured 0.8673 vs 0.8711   demo 0.9275 both  (0.4% apart)\n"
        "So the m*sigma^2 degeneracy is ITSELF ONLY A LARGE-d PROPERTY. At "
        "separations comparable to the dispersal scale, F_ST depends on the "
        "whole step distribution and not on m*sigma^2 at all. The docstring "
        "says evidence gathered with sigma^2 free constrains m*sigma^2 and "
        "nothing else -- true at long range; at short range even m*sigma^2 is "
        "not sufficient, so the regime is d >> dispersal scale AND d << D."
    ),
    canfail_clause=(
        "d > 0 and finite Ne; at d=0 both sides are 0.\n\n"
        "For the SIMULATED comparison the d grid must reach D/2. Every "
        "candidate here -- hyperbolic, quadratic, linear, exponential -- "
        "agrees with every other to first order in d once its one free scale "
        "is matched at d = 1, so a short-distance grid validates all four and "
        "decides nothing."
    ),
)


check(
    id="steppingStoneDiffusionTimescale-lattice-scale",
    fqn="Calibrator.DemographicHistory.steppingStoneDiffusionTimescale",
    claim="d/(2 sigma^2 m) is not the meeting time in generations; the "
          "meeting time is d(D-d)/(2 sigma^2 m) and depends on lattice size",
    model_lean="T(d) = d/(2 sigma^2 m), a quantity with no lattice size in "
               "its signature",
    model_ref="exact meeting time of two lineages on a circle of D demes, "
              "d(D-d)/V_rel with V_rel = 2 m sigma^2",
    reference="circle hitting time, verified against an exact linear solve",
    # The lattice-size axis is `n_demes`, NOT `D`. run.py decides whether a
    # check consumes the corpus table by testing whether its first parameter is
    # literally named `D`, so a grid axis called `D` silently stops the table
    # being passed and the check dies on a missing argument instead of running.
    # d is a CIRCULAR distance, so it cannot exceed n_demes/2; the unfiltered
    # product contained d = n_demes, where (D - d) = 0 and the reference is
    # identically zero. That point is not a hard case, it is a meaningless
    # one, and leaving it in would have let a degenerate 100% error stand in
    # for the real disagreement.
    grid=[g for g in grid(d=[1.0, 4.0, 16.0, 64.0], sigma_sq=[1.0, 4.0],
                          m=[0.025, 0.1], n_demes=[64.0, 256.0])
          if g["d"] <= g["n_demes"] / 2],
    lean=lambda D, d, sigma_sq, m, n_demes: D["steppingStoneDiffusionTimescale"](
        d, sigma_sq, m),
    ref=lambda d, sigma_sq, m, n_demes: (
        d * (n_demes - d) / (2.0 * m * sigma_sq)),
    kind="scope",
    expected_verdict="SCOPE",
    note=(
        "MEASURED STANDALONE FOR THE FIRST TIME by "
        "cluster/fam_stepping_stone.py. The docstring says 'UNTESTED as a "
        "standalone quantity'; it now is tested, and the ratio of the true "
        "meeting time to this expression is EXACTLY (D - d). On a circle of "
        "256 demes at m = 0.1, sigma^2 = 1: d = 1 gives 1344.2 generations "
        "against 5.0, and d = 128 gives 81987 against 640.\n\n"
        "AND YET THE F_ST IT FEEDS IS RIGHT TO 4.4%. `coalFst` pairs this "
        "quantity with 2*Ne rather than 2*Ne*D -- both sides are per-deme -- "
        "so the lattice size cancels and demoSteppingStoneFst comes out "
        "correct. That is why no consumer-level check could ever have found "
        "this: the error is invisible everywhere the quantity is actually "
        "used, and visible only when the quantity is asked what it claims to "
        "be.\n\n"
        "So the corpus knew this was untested and did not know what it was "
        "untested FOR. The repair is a scale declaration, not arithmetic: the "
        "quantity is a meeting time per deme of lattice, defined only up to "
        "the factor its signature cannot carry."
    ),
    canfail_clause=(
        "D MUST VARY. At a single lattice size (D - d) is very nearly a "
        "constant over the small-d part of any grid, and a refitted m absorbs "
        "a constant exactly -- the same degeneracy that makes a free sigma^2 "
        "useless for demoSteppingStoneFst. Two lattice sizes a factor of 4 "
        "apart are what make the dependence visible. d must also reach a "
        "sizeable fraction of D, since it is only there that (D - d) departs "
        "from D and the shape, not just the scale, disagrees."
    ),
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
    note=(
        "MEASURED against cluster/fam_admixture.py, which is the first time "
        "this definition has been run over a frequency SPECTRUM rather than a "
        "frequency pair. The account closes exactly: the measured ratio\n\n"
        "    F_ST(C,A)/F_ST(A,B) = (1-alpha)^2 / denominator_ratio\n\n"
        "reconstructs the measurement to 1e-16. The NUMERATOR ratio is "
        "(1-alpha)^2 to machine precision, so the corpus's own derivation "
        "step -- `admixed_freq_diff` -- survives intact; what the definition "
        "omits is the DENOMINATOR ratio, which is not 1 and runs from 0.978 "
        "down to 0.428 as alpha and the parental divergence rise.\n\n"
        "Errors are ALWAYS NEGATIVE (the definition understates F_ST(C,A)): "
        "-2.2% to -19.9% for alpha 0.1 -> 0.9 at F_ST(A,B) = 0.222, and -6.4% "
        "to -57.2% at F_ST(A,B) = 0.633. Twenty generations of post-admixture "
        "drift take it to -82.8%. Controls: A1 builds the admixed population "
        "by sampling ancestry per gamete rather than by evaluating "
        "admixedAlleleFreq, and A4b re-runs the comparison with alpha "
        "perturbed 1% and confirms the reported error moves."
    ),
    canfail_clause=(
        "REQUIRES pbar to move with alpha, i.e. p_a and p_b far apart and "
        "both away from 0.5. If p_a + p_b = 1 the denominators coincide and "
        "the (1-alpha)^2 numerator scaling is exactly right -- a symmetric "
        "frequency PAIR makes this check unable to fail.\n\n"
        "A symmetric SPECTRUM does NOT make this check unable to fail; only a "
        "symmetric PAIR does. "
        "cluster/fam_admixture.py ran three spectra -- a 1/p density, a "
        "uniform density, and Beta(1/2,1/2) -- and they agree to the THIRD "
        "DECIMAL (alpha=0.5, F_ST(A,B)=0.633: -0.3179, -0.3173, -0.3167). The "
        "spectrum barely matters; alpha and the parental divergence are what "
        "move the error. Symmetry of a PAIR makes the two denominators "
        "coincide; symmetry of a SPECTRUM does not, because E[p_C(1-p_A)] and "
        "E[p_B(1-p_A)] differ whenever the spectrum has any spread at all.\n\n"
        "This correction matters more than the defect it sits on: a check "
        "whose stated reason for being trustworthy is wrong is worse than one "
        "with no stated reason, because the justification is what stops "
        "anyone re-examining it."
    ),
)

# --- 8b. Admixture: what cluster/fam_admixture.py established ---------------
#
# A NOTE ON THE THREE CHECKS ADDED HERE AND IN SECTION 5 THAT ARE MEANT TO
# DISAGREE (admixedFst-over-a-spectrum, admixtureLDDecay-is-the-infinite-Ne-limit,
# steppingStoneDiffusionTimescale-lattice-scale).
#
# run.py's vacuity test asks whether a check separates the real definition from
# deliberately wrong ones. For a check whose verdict is AGREE that is the right
# question. For a check that is SUPPOSED to disagree it is nearly free: a check
# that disagrees with everything detects every mutant and looks maximally
# non-vacuous while constraining nothing. The mutant test cannot tell "this
# found something" from "this is broken".
#
# So each of the three is also checked in the OTHER direction -- that its
# reference is REACHABLE, i.e. that some body would make it AGREE. Verified
# exactly (max relative error 0 at every grid point):
#
#   steppingStoneDiffusionTimescale  d(D-d)/(2 sigma^2 m)
#   admixtureLDDecay              ((1-r)(1-1/(2Ne)))^g
#   admixedFst                    (1-alpha)^2 * F_ST(A,B) * den_AB/den_CA
#
# That is what makes each of them a measurement of a specific missing factor
# rather than a complaint. It also names the repair: the first two need an
# argument the signature does not have, which is why they are SCOPE and MODEL
# rather than FORMULA, and the third needs a regime declaration.
#
# A DETERMINISTIC spectrum, so nothing here samples and the file's opening
# promise still holds. The pairs below are a fixed, weighted set standing in
# for a differentiated pair of populations; the reference evaluates F_ST as a
# RATIO OF AVERAGES over that set, which is how F_ST is actually computed and
# is exactly what the simulator measured over 200000 sampled loci.
_SPECTRUM = [
    (0.05, 0.35), (0.10, 0.55), (0.20, 0.75), (0.30, 0.05),
    (0.45, 0.90), (0.60, 0.15), (0.75, 0.25), (0.90, 0.40),
]


def _ratio_of_averages_fst(pairs: list[tuple[float, float]]) -> float:
    num = sum((a - b) ** 2 for a, b in pairs)
    den = sum(a * (1 - b) + b * (1 - a) for a, b in pairs)
    return 0.0 if den == 0 else num / den


def _admixed_fst_spectrum(alpha: float) -> float:
    """Hudson F_ST(C, A) over the whole spectrum, C = alpha A + (1-alpha) B."""
    pc = [(alpha * a + (1 - alpha) * b, a) for a, b in _SPECTRUM]
    return _ratio_of_averages_fst(pc)


check(
    id="admixedFst-over-a-spectrum",
    fqn="Calibrator.DemographicHistory.admixedFst",
    claim="(1-alpha)^2 is a NUMERATOR identity; over a spectrum the "
          "denominator moves too and the F_ST identity fails",
    model_lean="F_ST(C,A) = (1-alpha)^2 * F_ST(A,B), i.e. the ratio of the "
               "two F_ST values is exactly (1-alpha)^2",
    model_ref="Hudson F_ST as a ratio of averages over a fixed spectrum, "
              "evaluated directly on (p_A, p_C) at every locus",
    reference="_admixed_fst_spectrum",
    grid=grid(alpha=[0.1, 0.25, 0.5, 0.75, 0.8, 0.9]),
    lean=lambda D, alpha: D["admixedFst"](
        alpha, _ratio_of_averages_fst(_SPECTRUM)
    ),
    ref=lambda alpha: _admixed_fst_spectrum(alpha),
    kind="model",
    expected_verdict="MODEL",
    note=(
        "The companion to `admixedFst-ratio-not-numerator`, which evaluates "
        "one frequency pair at a time. This one is the SPECTRUM version, "
        "because F_ST is a ratio of averages and the averaging correction is "
        "not deducible from a single pair.\n\n"
        "Measured by cluster/fam_admixture.py over 200000 loci and three "
        "spectra: the error is always negative and grows with alpha and with "
        "the parental divergence, reaching -57.2% at alpha = 0.9 with "
        "F_ST(A,B) = 0.633. The decomposition there shows the numerator ratio "
        "is exactly (1-alpha)^2 and the denominator ratio runs 0.978 -> 0.428, "
        "so the repair is a REGIME DECLARATION -- the identity holds for "
        "Var(p_C - p_A) always, and for F_ST only as alpha -> 0 or "
        "F_ST(A,B) -> 0."
    ),
    canfail_clause=(
        "The spectrum must have spread in BOTH coordinates and must not be a "
        "single pair. A degenerate spectrum (all loci at one (p_A, p_B)) "
        "reduces this to the pair check; a spectrum with p_A = p_B "
        "everywhere makes both F_ST values 0 and the comparison vacuous. "
        "alpha must also reach past 0.5: below it (1-alpha)^2 ~ 1 - 2 alpha "
        "and the ratio-versus-numerator distinction is second order."
    ),
)


check(
    id="admixtureLDDecay-is-the-infinite-Ne-limit",
    fqn="Calibrator.PortabilityDrift.admixtureLDDecay",
    claim="(1-r)^g omits drift; the retention of E[D] is (1-r)(1-1/(2Ne)) "
          "per generation",
    model_lean="(1-r)^g -- recombination only, no effective size anywhere in "
               "the signature",
    model_ref="Hill-Robertson: E[D] decays by (1-r)(1-1/(2Ne)) per generation",
    reference="closed form, (1-r)^g vs ((1-r)(1-1/(2Ne)))^g",
    grid=grid(r=[0.0, 0.00125, 0.0025, 0.005, 0.02, 0.1], Ne=[200.0], g=[20]),
    lean=lambda D, r, Ne, g: D["admixtureLDDecay"](r, g),
    ref=lambda r, Ne, g: ((1.0 - r) * (1.0 - 1.0 / (2.0 * Ne))) ** g,
    kind="model",
    expected_verdict="MODEL",
    note=(
        "MEASURED by cluster/fam_admixture.py. Per-generation retention of "
        "E[D] against both forms, Ne = 200:\n"
        "    r=0        measured 0.997575  corpus 1.000000 (+0.24%)  "
        "with drift 0.997500 (-0.01%)\n"
        "    r=0.0025   measured 0.994828  corpus 0.997500 (+0.27%)  "
        "with drift 0.995006 (+0.02%)\n"
        "    r=0.02     measured 0.977596  corpus 0.980000 (+0.25%)  "
        "with drift 0.977550 (-0.00%)\n"
        "    r=0.1      measured 0.896658  corpus 0.900000 (+0.37%)  "
        "with drift 0.897750 (+0.12%)\n"
        "    r=0.5      measured 0.506154  corpus 0.500000 (-1.22%)\n"
        "So (1-r)(1-1/(2Ne)) is right to <= 0.12% across the grid and the "
        "corpus's bare (1-r) is high by exactly the drift factor. This is a "
        "small, clean REGIME: admixtureLDDecay is the Ne -> infinity limit and "
        "does not say so. Controls B1 (Ne infinite) and B2 (r = 0) pin the two "
        "factors separately, which is what makes it readable as a limit rather "
        "than as a fitted discrepancy.\n\n"
        "The r = 0.5 row is recorded because an earlier run reported -41% "
        "there and that number was a MEASUREMENT defect, not a corpus one: the "
        "fit had run below the standard error of its own replicate mean. It is "
        "kept here so nobody re-derives the retracted figure."
    ),
    canfail_clause=(
        "The r grid MUST straddle 1/(2Ne). Where r >> 1/(2Ne) the drift factor "
        "is invisible and (1-r)^g is indistinguishable from the truth; where "
        "r << 1/(2Ne) recombination is invisible. Only near r ~ 1/(2Ne) do "
        "both factors matter at once. The r = 0 row is the extreme case and is "
        "the one where the corpus form is exactly 1 and the truth is not."
    ),
)


# --- 9. Cross-name duplicates ----------------------------------------------
# Do NOT add a duplicate-detection check for islandModelFst, equilibriumFst or
# fstMigDriftEquil: they are all `fstMigrationDriftEquilibrium`.
#
# THE GENERAL RULE: a duplicate-detection check whose two sides have become the
# same definition compares that definition to itself and reports 0.0 forever,
# which is a passing check that has stopped meaning anything. When a duplication
# is repaired by collapsing the names, retire the check that detected it.
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
    id="ldCorrelationMigrationAnsatz-vs-sharedLD-squared",
    fqn="Calibrator.PopulationGeneticsFoundations.ldCorrelationMigrationAnsatz",
    claim="M^2/(1+M)^2 is exactly the square of PortabilityDrift.sharedLDFromMigration",
    model_lean="proportion of LD that is shared, as a function of M=4Nm",
    model_ref="sharedLDFromMigration(M)^2 = (1 - islandModelFst)^2",
    reference="Calibrator.PortabilityDrift.sharedLDFromMigration ** 2",
    grid=grid(M=[0.1, 1.0, 4.0, 40.0]),
    lean=lambda D, M: D["ldCorrelationMigrationAnsatz"](M),
    ref=lambda D, M: D["sharedLDFromMigration"](M) ** 2,
    kind="internal",
    note=(
        "CONSISTENT: PopulationGeneticsFoundations.ldCorrelationMigrationAnsatz "
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

# `neutralAFBenchmarkRatio-bounded` was checked here.  The definition has been
# DELETED from Calibrator.PortabilityDrift as falsified -- the reference starts
# each branch at equilibrium, so the true ratio is 1 while the definition, whose
# model has no mutation, predicts a ratio far from 1 -- so the check has no
# target left to run against.  The finding survives in Lean as
# `PortabilityDrift.benchmarkRatioForm_cannot_reach_measured`, which states the
# ceiling about the written-out expression rather than about the name.
#
# The check's own canfail_clause is preserved here VERBATIM, because it is
# evidence about how we read our own tooling and not merely a comment.  It had
# already named the symmetric design that produced the false VALIDATED, and it
# was read as agreement anyway:
#
#     "tS != tT is mandatory. At tS = tT the definition returns exactly 1 "
#     "and so does the reference -- the symmetric design in which both sides "
#     "collapse to 1 is precisely the false-validation failure mode."
#
# The instrument said so first.  Calibrator.DriftRegime.symmetric_design_has_no_power
# is the same fact proved: on a symmetric design this form and its square are
# indistinguishable, so the design could not have rejected a wrong functional form.

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
    id="heterozygosityLossVariableNe-vs-exact-product",
    fqn="Calibrator.heterozygosityLossVariableNe",
    claim="1 - exp(-sum 1/(2Ne_i)) vs the exact 1 - prod(1 - 1/(2Ne_i))",
    model_lean="exponential approximation of a product of survival terms",
    model_ref="exact Wright-Fisher non-coalescence product",
    reference="refs.cumulative_inbreeding_exact",
    grid=[{"nes": _BOTTLENECK}, {"nes": _RAMP}, {"nes": _MILD}, {"nes": _SEVERE}],
    lean=lambda D, nes: D["heterozygosityLossVariableNe"](nes),
    ref=lambda nes: refs.cumulative_inbreeding_exact(nes),
    tol=1e-3,
    kind="model",
    note=(
        "shares the closed-population no-mutation model of the heterozygosityLossDerived "
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
    id="heterozygosityLossVariableNe-equals-harmonic-mean-substitution",
    fqn="Calibrator.heterozygosityLossVariableNe",
    claim="the variable-Ne F equals the constant-Ne exponential form evaluated "
          "at the harmonic mean",
    model_lean="1 - exp(-cumulativeDrift Ne)",
    model_ref="1 - exp(-T/(2 * harmonicMeanNe Ne)), same file",
    reference="Calibrator.harmonicMeanNe substituted into the exponential form",
    grid=[{"nes": _BOTTLENECK}, {"nes": _RAMP}, {"nes": _MILD}, {"nes": _SEVERE}],
    lean=lambda D, nes: D["heterozygosityLossVariableNe"](nes),
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


# --- 15. Identity-by-descent recurrence: the two readings of `rate` ---------
#
# One body carries nine names in the corpus, and `rate` is instantiated as a
# MUTATION rate in some and a MIGRATION rate in others:
#
#     ibdRecurrenceStep Ne rate x = (1-rate)^2 (1/(2Ne) + (1-1/(2Ne)) x)
#     ibdRecurrenceFixedPoint     = (1-rate)^2/((1-rate)^2 + 2 Ne rate (2-rate))
#     islandFstMultiplicativeStep       := ibdRecurrenceStep
#     fstIslandMultiplicativeEquilibrium := ibdRecurrenceFixedPoint
#     ibdFlowStep / fstMigDriftNext / scaledIdentityStep / fstDriftFlowStep /
#     fstEquilibrium -- the linearised companions, fixed point 1/(1+4 Ne rate)
#
# Every one of them is marked `Empirical status: UNTESTED` in the Lean. The
# checks below are the analytic half; the sampled half is
# cluster/fam_ibd_recurrence.py, which computes the same ancestral process by
# an exact 2x2 identity solve AND by an independent Monte Carlo on deme labels.
#
# WHY THE TWO READINGS CANNOT BOTH BE RIGHT. A mutation destroys identity on
# the lineage it hits and that lineage is gone for good, so `(1-mu)^2` is an
# EXACT factor. A migration event MOVES one lineage; it is still there and can
# migrate back, so `(1-m)^2` is an ABSORBING approximation to a recurrent
# process. The pair `ibdRecurrenceFixedPoint-mutation-reading-exact` (expected
# to AGREE to machine precision) and `ibdRecurrenceFixedPoint-migration-reading`
# (expected to DISAGREE) is what makes the second interpretable: without the
# first a reader cannot tell whether the disagreement is the corpus or the
# reference.

_IBD = grid(Ne=[50.0, 100.0, 1000.0], rate=[1e-4, 1e-3, 5e-3, 2e-2])


def _ibd_exact_identity(ne, m, mu, d):
    """EXACT probability of identity in state for two lineages in a d-deme
    island model, discrete generations, migration then mutation then
    coalescence. Returns (f_same_deme, f_different_demes).

    Two states suffice because migration is uniform over the other d-1 demes,
    so only co-residence matters:
        S -> S : neither moves, (1-m)^2; or both move and land together,
                 m^2/(d-1)
        B -> S : exactly one moves onto the other, 2m(1-m)/(d-1); or both move
                 and land together, m^2 (d-2)/(d-1)^2
    This is an independent derivation, not a rearrangement of the corpus body:
    the corpus body is what it is being compared against.
    """
    if mu <= 0.0:
        return (1.0, 1.0 if (d > 1 and m > 0.0) else 0.0)
    surv = (1.0 - mu) ** 2
    c = 1.0 / (2.0 * ne)
    if d <= 1 or m <= 0.0:
        return (surv * c / (1.0 - surv * (1.0 - c)), 0.0)
    q = 1.0 / (d - 1.0)
    m_ss = (1 - m) ** 2 + m * m * q
    m_sb = 1.0 - m_ss
    m_bs = 2 * m * (1 - m) * q + m * m * (d - 2.0) * q * q
    m_bb = 1.0 - m_bs
    a = surv * m_ss * (1 - c)
    b = surv * m_sb
    u = surv * m_ss * c
    cc = surv * m_bs * (1 - c)
    dd = surv * m_bb
    v = surv * m_bs * c
    det = (1 - a) * (1 - dd) - b * cc
    f_s = (u * (1 - dd) + b * v) / det
    f_b = ((1 - a) * v + cc * u) / det
    return (f_s, f_b)


def _ibd_exact_island_fst(ne, m, d, theta=1e-3):
    """F_ST = (f_S - f_B)/(1 - f_B) at a mutation floor theta = 4*Ne*mu.

    F_ST is only defined relative to some mutation; theta is held three orders
    below the migration scale and the simulator's companion cell halves it and
    confirms F_ST does not move.
    """
    f_s, f_b = _ibd_exact_identity(ne, m, theta / (4.0 * ne), d)
    return (f_s - f_b) / (1.0 - f_b)


def _fixed_point(step, x0=0.0, n=200000):
    """Iterate to the rest point, with the convergence CHECKED rather than a
    fixed iteration count asserted. The cap is unchanged at 200000; the early
    exit fires only once successive iterates stop moving at double precision,
    so the returned value is the same value, reached sooner.
    """
    x = x0
    for _ in range(n):
        nxt = step(x)
        if nxt == x:
            return x
        x = nxt
    return x


check(
    id="ibdRecurrenceFixedPoint-is-fixed-point",
    fqn="Calibrator.PortabilityDrift.ibdRecurrenceFixedPoint",
    claim="the closed form is the rest point of ibdRecurrenceStep",
    model_lean="(1-rate)^2 (1/(2Ne) + (1-1/(2Ne)) x)",
    model_ref="the same map, iterated numerically to convergence",
    reference="numerical iteration of the corpus step, 200000 iterations",
    grid=_IBD,
    lean=lambda D, Ne, rate: D["ibdRecurrenceFixedPoint"](Ne, rate),
    ref=lambda D, Ne, rate: _fixed_point(
        lambda x: D["ibdRecurrenceStep"](Ne, rate, x)),
    tol=1e-7,
    kind="identity",
    note="SELF-CONSISTENCY, not validation. It exists so that a disagreement "
         "in the checks below is known to be about the MODEL and not about "
         "the closed form failing to solve its own recurrence.",
    canfail_clause=(
        "rate must be >0 and Ne finite: at rate=0 both sides are 1 and at "
        "Ne=inf both are 0, and either boundary passes for any body with the "
        "right limits."
    ),
)

check(
    id="ibdRecurrenceFixedPoint-mutation-reading-exact",
    fqn="Calibrator.PortabilityDrift.ibdRecurrenceFixedPoint",
    claim="POSITIVE CONTROL: under the MUTATION reading the corpus body is "
          "exactly the identity probability of the ancestral process",
    model_lean="rate = mu; one panmictic deme",
    model_ref="two lineages in one Wright-Fisher deme of Ne diploids, "
              "infinite alleles at rate mu per lineage per generation, "
              "mutation acting before coalescence; P(coalesce before either "
              "mutates), computed from the 2x2 identity system",
    reference="_ibd_exact_identity(Ne, m=0, mu=rate, d=1)",
    grid=_IBD,
    lean=lambda D, Ne, rate: D["ibdRecurrenceFixedPoint"](Ne, rate),
    ref=lambda Ne, rate: _ibd_exact_identity(Ne, 0.0, rate, 1)[0],
    tol=1e-12,
    note=(
        "EXPECTED TO AGREE to machine precision, and it is what makes "
        "ibdRecurrenceFixedPoint-migration-reading interpretable. The "
        "mutation reading is not an approximation: a mutated lineage is gone "
        "for good, so (1-mu)^2 is exact."
    ),
    canfail_clause=(
        "the reference is derived from the ancestral process, not from the "
        "corpus body; the companion check "
        "ibdRecurrenceFixedPoint-migration-reading uses the SAME reference "
        "machinery with d=2 and disagrees by tens of percent, which is the "
        "demonstration that this reference can produce a different number."
    ),
)

check(
    id="ibdRecurrenceFixedPoint-migration-reading",
    fqn="Calibrator.PortabilityDrift.fstIslandMultiplicativeEquilibrium",
    claim="MODEL: under the MIGRATION reading the same body is NOT the island "
          "F_ST, because migration is recurrent and the body treats it as "
          "absorbing",
    model_lean="rate = m; (1-m)^2 destroys identity outright",
    model_ref="two-deme island model, exact identity system, migration "
              "reversible, F_ST = (f_S - f_B)/(1 - f_B) at a mutation floor",
    reference="_ibd_exact_island_fst(Ne, m, d=2)",
    grid=grid(Ne=[100.0], m=[6.25e-4, 1.25e-3, 2.5e-3, 5e-3, 2e-2, 5e-2]),
    lean=lambda D, Ne, m: D["fstIslandMultiplicativeEquilibrium"](Ne, m),
    ref=lambda Ne, m: _ibd_exact_island_fst(Ne, m, 2),
    kind="model",
    expected_verdict="MODEL",
    note=(
        "EXPECTED TO DISAGREE, and the disagreement is the result. Its "
        "companion ibdRecurrenceFixedPoint-mutation-reading-exact passes to "
        "1e-12 against the same reference machinery, which localises this gap "
        "to the READING of `rate` and not to the reference."
    ),
    canfail_clause=(
        "4*Ne*m must reach BELOW 1 (the grid starts at 0.25). Above 4*Ne*m ~ "
        "10 every candidate gives F_ST ~ 0 and a grid confined there validates "
        "all of them at once."
    ),
)

check(
    id="fstIslandMultiplicativeEquilibrium-missing-deme-count",
    fqn="Calibrator.PortabilityDrift.fstIslandMultiplicativeEquilibrium",
    claim="SCOPE: the island equilibrium has no argument for the NUMBER of "
          "demes, and F_ST depends on it at fixed 4*Ne*m",
    model_lean="Ne and m only",
    model_ref="finite-island F_ST = 1/(1 + 4 Ne m (d/(d-1))^2), d = 2",
    reference="refs.island_fst_finite_demes",
    grid=grid(Ne=[100.0], m=[6.25e-4, 2.5e-3, 1e-2]),
    lean=lambda D, Ne, m: D["fstIslandMultiplicativeEquilibrium"](Ne, m),
    ref=lambda Ne, m: refs.island_fst_finite_demes(Ne, m, 2),
    kind="scope",
    expected_verdict="SCOPE",
    note=(
        "The corpus body returns ONE number for d = 2, 10 and 100 demes; the "
        "finite-island reference differs between them by the factor "
        "(d/(d-1))^2, which is 4 at d=2 and 1.02 at d=100. This is a MISSING "
        "REGIME DECLARATION, not wrong arithmetic: the body is the d -> "
        "infinity reading and nothing says so."
    ),
    canfail_clause=(
        "d must be SMALL. At d = 100 the reference and the d -> infinity form "
        "agree to 2% and the check cannot see the missing argument; d = 2 is "
        "the reach that makes it visible."
    ),
)

check(
    id="ibdFlowStep-linearisation-gap",
    fqn="Calibrator.PortabilityDrift.ibdFlowStep",
    claim="the linearised flow step and the multiplicative recurrence do NOT "
          "share a fixed point",
    model_lean="F + (1-F)/(2Ne) - 2 rate F, iterated to its rest point",
    model_ref="the multiplicative recurrence's rest point, same Ne and rate",
    reference="Calibrator.PortabilityDrift.ibdRecurrenceFixedPoint",
    grid=_IBD,
    lean=lambda D, Ne, rate: _fixed_point(
        lambda x: D["ibdFlowStep"](Ne, rate, x)),
    ref=lambda D, Ne, rate: D["ibdRecurrenceFixedPoint"](Ne, rate),
    kind="model",
    expected_verdict="MODEL",
    note=(
        "Quantifies ibdRecurrenceFixedPoint_lt_linearisation. The two are "
        "the SAME model composed in two different orders -- added versus "
        "multiplied -- so the size of the gap is the cost of the composition "
        "convention, which both docstrings declare as O(rate^2, rate/Ne)."
    ),
    canfail_clause=(
        "rate must reach 2e-2 and Ne must reach 50. At rate=1e-4, Ne=50 the "
        "two agree to better than 1e-3 and the check is vacuous -- which is "
        "the point: the declared O(rate^2, rate/Ne) is exactly the regime "
        "where it stops being vacuous, so the grid must span both."
    ),
)

check(
    id="fstMigDriftNext-duplicates-ibdFlowStep",
    fqn="Calibrator.PortabilityDrift.fstMigDriftNext",
    claim="DUPLICATE: fstMigDriftNext is ibdFlowStep with the terms collected",
    model_lean="(1 - 2m - 1/(2Ne)) F + 1/(2Ne)",
    model_ref="F + (1-F)/(2Ne) - 2 m F, the same map",
    reference="Calibrator.PortabilityDrift.ibdFlowStep",
    grid=grid(Ne=[50.0, 100.0, 1000.0], m=[1e-4, 1e-3, 2e-2],
              F=[0.0, 0.3, 0.9]),
    lean=lambda D, Ne, m, F: D["fstMigDriftNext"](Ne, m, F),
    ref=lambda D, Ne, m, F: D["ibdFlowStep"](Ne, m, F),
    kind="identity",
    note="two names, one map, and neither file mentions the other; recorded "
         "so the duplication is pinned rather than rediscovered",
    canfail_clause=(
        "F must be swept away from the fixed point (the grid runs 0, 0.3, "
        "0.9). At F equal to the common fixed point both sides return it and "
        "any map with the same rest point would pass."
    ),
)

check(
    id="scaledIdentityStep-fixed-point",
    fqn="Calibrator.PopulationGeneticsFoundations.scaledIdentityStep",
    claim="the scaled-time balance has fixed point 1/(1 + scaledRate), which "
          "is the 4*Ne*rate limit of ibdFlowStep",
    model_lean="1 - scaledRate * F at scaledRate = 4*Ne*rate",
    model_ref="rest point of ibdFlowStep at the same Ne and rate",
    reference="Calibrator.PortabilityDrift.ibdFlowStep, iterated",
    grid=_IBD,
    lean=lambda D, Ne, rate: 1.0 / (1.0 + 4.0 * Ne * rate),
    ref=lambda D, Ne, rate: _fixed_point(
        lambda x: D["ibdFlowStep"](Ne, rate, x)),
    tol=1e-9,
    kind="identity",
    note="pins the scaled-time member onto the per-generation one; "
         "scaledIdentityStep itself is exercised by "
         "scaledIdentityStep-is-the-balance below",
    canfail_clause=(
        "needs rate > 0; at rate = 0 both are 1 for any body with that limit."
    ),
)

check(
    id="scaledIdentityStep-is-the-balance",
    fqn="Calibrator.PopulationGeneticsFoundations.scaledIdentityStep",
    claim="scaledIdentityStep really does fix 1/(1+scaledRate)",
    model_lean="1 - scaledRate * F",
    model_ref="the value 1/(1+scaledRate) fed back through the same map",
    reference="algebraic fixed point",
    grid=grid(scaledRate=[0.25, 0.5, 1.0, 2.0, 8.0, 20.0]),
    lean=lambda D, scaledRate: D["scaledIdentityStep"](
        scaledRate, 1.0 / (1.0 + scaledRate)),
    ref=lambda scaledRate: 1.0 / (1.0 + scaledRate),
    tol=1e-12,
    kind="identity",
    canfail_clause=(
        "scaledRate must span below and above 1: at scaledRate=0 the map is "
        "the constant 1 and fixes it trivially."
    ),
)


# --- 14. Linear prediction transport: what cluster/fam_linear_transport.py
#         established. ---------------------------------------------------
#
# The 47-member `linear_prediction_transport` family is matrix algebra over
# `CrossPopulationMetricModel`, and only two of its members survive extraction
# to scalar callables (`explainedR2FromTransportMoments` and
# `demographicCovarianceGapLowerBound`). The rest are checked in
# cluster/fam_linear_transport.py, which instantiates the structure from a
# simulated two-population genotype process rather than from hand-chosen
# matrices. What is registered here is the scalar residue, plus the two
# findings that the simulator settled and that a reader of this file must not
# have to rediscover.
#
# FINDING 1 (measured, exact arithmetic, no sampling).
#   `irreducibleTargetResidualBurden` sums four terms. Three of them --
#   brokenTaggingResidual, ancestrySpecificLDResidual,
#   sourceSpecificOverfitResidual -- are dot products of vectors of
#   COVARIANCES, so they carry units of (genotype scale)^2 x (outcome)^2. The
#   fourth, novelUntaggablePhenotypeResidual, is a plain outcome variance. The
#   sum is then added to `outcomeVariance` inside `effectiveOutcomeVariance`,
#   which is what `r2FromSourceWeights` and
#   `residualVarianceFromSourceWeights` divide by and subtract from.
#
#   Under g -> c*g with beta -> beta/c the phenotype, the ERM weights'
#   predictions and every measured moment are unchanged BIT FOR BIT -- this is
#   the free choice between raw dosages and standardised genotypes. Measured:
#   the target R^2 moved by 0.000e+00 over c in {1,2,4} while the burden grew
#   by exactly c^2.000 (9.276 -> 37.104 -> 148.417 against a fixed Var(y) =
#   32.28) and r2FromSourceWeights fell by 77% relative. Commit 43fcfd04.
#
#   So `r2FromSourceWeights` is not a scale-free R^2: it depends on the units
#   the genotypes were coded in. The one-fixed-world N-convergence arm confirms
#   this is a bias and not sampling: at N = 6k/24k/96k the transport-moment R^2
#   error falls -0.1998 -> -0.0888 -> +0.0717 while r2FromSourceWeights holds a
#   floor of -burden/(Var(y)+burden) = -16.6%, and
#   residualVarianceFromSourceWeights holds +0.277 -> +0.232 -> +0.208.
#
# FINDING 2 (missing regime declaration).
#   `demographicCovarianceGapLowerBound` reads the F_ST DIFFERENCE
#   fstTarget - fstSource, so for two populations equally diverged from one
#   ancestor -- the generic split -- it is identically 0 while the measured
#   squared Frobenius LD mismatch ranged 2.554 to 7.346 across the arms. It is
#   a true lower bound there and a vacuous one, and nothing in the corpus says
#   so: it is never proved, appearing only as a HYPOTHESIS of
#   covariance_mismatch_pos_of_fst_and_sparse_array.

check(
    id="explainedR2FromTransportMoments-is-squared-correlation",
    fqn="Calibrator.explainedR2FromTransportMoments",
    claim="the moment-level transport R^2 is the squared correlation between "
          "score and outcome, and therefore scale-free in BOTH the score and "
          "the outcome",
    model_lean="scoreOutcomeCov^2 / (scoreVariance * outcomeVariance)",
    model_ref="squared Pearson correlation of a linear score with an outcome, "
              "computed from the same three moments independently",
    reference="cov^2/(var_s var_y), the definition of the explained fraction "
              "for the BEST-SCALED version of a score",
    grid=grid(cov=[0.2, 1.0, 3.5, 3.85387],
              vs=[0.5, 3.06, 6.28462, 8.93],
              vy=[1.0, 28.9, 32.28, 79.6]),
    lean=lambda D, cov, vs, vy: D["explainedR2FromTransportMoments"](cov, vs, vy),
    ref=lambda cov, vs, vy: (cov * cov) / (vs * vy),
    kind="identity",
    note=(
        "POSITIVE CONTROL for the pair below. This is the transport R^2 that "
        "cluster/fam_linear_transport.py measured converging on independent "
        "target individuals: relative error -0.1998 at N=6000, -0.0888 at "
        "N=24000, +0.0717 at N=96000, one fixed world, arm B, commit 43fcfd04. "
        "It is the member of the family that DOES behave like an R^2, and it "
        "is registered so that the r2FromSourceWeights finding below is "
        "localised to the effectiveOutcomeVariance denominator rather than to "
        "the moment algebra it shares."
    ),
    canfail_clause=(
        "the grid must contain points where vs != vy AND cov^2 != vs*vy. At "
        "cov^2 = vs*vy the value is 1 for any denominator convention and at "
        "vs = vy a transposed pair of arguments is invisible; either alone "
        "makes the check unable to separate the intended form from a "
        "denominator that multiplies the wrong two moments."
    ),
)

check(
    id="demographicCovarianceGapLowerBound-vacuous-at-equal-divergence",
    fqn="Calibrator.demographicCovarianceGapLowerBound",
    claim="MISSING REGIME DECLARATION: the demography-to-LD lower bound is "
          "identically 0 whenever the two populations are equally diverged, "
          "which is the generic two-population split and precisely the case "
          "the family names ancestry-specific LD",
    model_lean="kappa * recombRate * arraySparsity * (fstTarget - fstSource)",
    model_ref="the squared Frobenius LD mismatch it is assumed to lower-bound, "
              "MEASURED in cluster/fam_linear_transport.py arm E on genotypes "
              "from two populations equally diverged from one ancestor",
    reference="cluster/fam_linear_transport_results.json, E_ld_mismatch",
    grid=[
        {"fstS": 0.05, "fstT": 0.05, "r": 0.01, "a": 0.1, "kappa": 1.0,
         "measured": 2.5539},
        {"fstS": 0.05, "fstT": 0.05, "r": 0.01, "a": 0.1, "kappa": 1.0,
         "measured": 4.62042},
        {"fstS": 0.15, "fstT": 0.15, "r": 0.01, "a": 0.1, "kappa": 1.0,
         "measured": 5.89507},
        {"fstS": 0.15, "fstT": 0.15, "r": 0.01, "a": 0.1, "kappa": 1.0,
         "measured": 7.34606},
    ],
    lean=lambda D, fstS, fstT, r, a, kappa, measured: (
        D["demographicCovarianceGapLowerBound"](fstS, fstT, r, a, kappa)),
    ref=lambda fstS, fstT, r, a, kappa, measured: measured,
    kind="scope",
    expected_verdict="SCOPE",
    note=(
        "EXPECTED TO DISAGREE, and the disagreement IS the result. The bound "
        "is not wrong -- 0 really is a lower bound for a squared Frobenius "
        "norm -- it is uninformative in the regime the family cares about, and "
        "the corpus nowhere says so. It is never proved: it occurs only as a "
        "hypothesis of covariance_mismatch_pos_of_fst_and_sparse_array and of "
        "target_r2_drop_of_fst_and_sparse_array, so no theorem is weakened by "
        "its vacuity and no theorem records it either. The repair is a regime "
        "declaration, not new arithmetic: state that the bound carries "
        "information only when the two populations differ in their divergence "
        "from the reference, and that equal-F_ST populations with different "
        "recombination-scaled LD are outside it.\n\n"
        "MEASURED, arm E, commit 43fcfd04: bound = 0 at all four grid points "
        "while the measured mismatch ranged 2.554 to 7.346, i.e. the bound "
        "leaves the entire quantity unconstrained."
    ),
    canfail_clause=(
        "The grid must hold fstSource == fstTarget. With fstTarget > "
        "fstSource the bound is strictly positive -- measured 1.0e-4 at "
        "fstS=0.05, fstT=0.15, r=0.01, a=0.1, kappa=1 -- so a grid that lets "
        "the F_ST values differ tests the arithmetic and says nothing about "
        "the regime. That positive value is the control showing this check "
        "reports vacuity rather than a formula that is always zero."
    ),
)


# --- generational transport kernel: the allele-frequency retention factor ---
#
# alleleFreqMismatchPenalty is the only locus-resolved factor in every kernel
# of the `...At` layer: jointTagLDKernelAt, jointDirectCausalKernelAt,
# jointProxyTaggingKernelAt and both novel kernels all carry it, once per
# index. On the DIAGONAL of sigmaTagTargetAt, and with mutation and migration
# switched off, the whole kernel is exactly penalty(p_s, p_t)^2 -- every other
# factor is identically 1 -- so the diagonal is the one place where this
# factor can be isolated from the rest of the product. That is the split
# control; a joint check on the full kernel would let a wrong AF factor be
# absorbed by the mutation or migration factor.
check(
    id="alleleFreqMismatchPenalty-is-not-the-variance-retention",
    fqn="Calibrator.alleleFreqMismatchPenalty",
    claim="MODEL: the AF retention factor exp(-|p_target - p_source|) is a "
          "strictly DECREASING function of |delta p|, but the quantity it "
          "multiplies -- the tag locus's contribution to the target second "
          "moment -- retains p_t(1-p_t)/(p_s(1-p_s)), which INCREASES above 1 "
          "whenever drift carries the frequency toward 1/2 and falls to "
          "exactly 0 at fixation. The penalty is bounded below by exp(-2) = "
          "0.135 on the diagonal and can never reach 0",
    model_lean="exp(-|p_t - p_s|), squared because the diagonal of "
               "sigmaTagTargetAt carries tagAlleleFreqRetentionAt at both i "
               "and j; with mu = mig = 0 every other kernel factor is 1",
    model_ref="the MEASURED ratio of the target to the source diagonal of the "
              "tag second-moment matrix, on individuals from a forward "
              "two-deme Wright-Fisher simulation at Ne = 250, mu = 0, "
              "mig = 0, r = 0.004 between adjacent loci, 4000 individuals "
              "per deme, 6 replicates, generations 100 to 1000 = 2*(2Ne)",
    reference="cluster/fam_generational_transport_results.json, "
              "per_locus.drift_only",
    grid=[
        {"t": 100, "ps": 0.588, "pt": 0.590, "measured": 0.98207},
        {"t": 200, "ps": 0.610, "pt": 0.660, "measured": 0.91238},
        {"t": 100, "ps": 0.184, "pt": 0.338, "measured": 1.53984},
        {"t": 200, "ps": 0.574, "pt": 0.732, "measured": 0.77120},
        {"t": 200, "ps": 0.748, "pt": 0.458, "measured": 1.31963},
        {"t": 500, "ps": 0.212, "pt": 0.668, "measured": 1.36577},
        {"t": 500, "ps": 0.266, "pt": 1.000, "measured": 0.00000},
        {"t": 1000, "ps": 0.478, "pt": 0.000, "measured": 0.00000},
    ],
    lean=lambda D, t, ps, pt, measured: (
        D["alleleFreqMismatchPenalty"](ps, pt) ** 2),
    ref=lambda t, ps, pt, measured: measured,
    kind="model",
    expected_verdict="MODEL",
    note=(
        "EXPECTED TO DISAGREE. The two sides are not the same quantity and "
        "the corpus does not say so: alleleFreqMismatchPenalty carries no "
        "regime declaration at all (regime.json: has_regime false, "
        "regime_explicit empty) and its docstring says only that it "
        "'penalizes transport when target allele frequencies drift away from "
        "the source frequencies'. A mentions query finds it in four theorems, "
        "all of which use it as an opaque positive scalar; none pins it to a "
        "measurable retention.\n\n"
        "MEASURED, commit see below, drift-only arm:\n"
        "  delta p = 0.002: penalty^2 = 0.99601 vs measured 0.98207 (1.4%) -- "
        "the two agree in the limit, which is why a small-delta grid decides "
        "nothing.\n"
        "  p_s = 0.184 -> p_t = 0.338: penalty^2 = 0.73492 vs measured "
        "1.53984, rel err 0.52. The penalty predicts a 27% LOSS where the "
        "simulation shows a 54% GAIN; the exact HWE ratio "
        "p_t(1-p_t)/(p_s(1-p_s)) = 1.4903 is within 3% of the measurement, so "
        "the reference is the right closed form and the sign of the effect is "
        "what is wrong.\n"
        "  p_s = 0.212 -> p_t = 0.668: penalty^2 = 0.40172 vs measured "
        "1.36577, rel err 0.71.\n"
        "  p_s = 0.266 -> p_t = 1.000 (fixed): penalty^2 = 0.23039 vs "
        "measured 0.0. At fixation the tag carries no variance and transports "
        "nothing, but exp(-|delta p|)^2 >= exp(-2) = 0.135 for any pair of "
        "frequencies, so the corpus's kernel can never express a lost locus.\n"
        "  p_s = 0.478 -> p_t = 0.000 (fixed): penalty^2 = 0.38443 vs 0.0.\n\n"
        "The repair is a regime declaration plus a reference, not a rescaling: "
        "the factor is monotone in |delta p| by construction and the target "
        "quantity is not monotone in |delta p| at all, so no scaling of "
        "exp(-|delta p|) can fit it."
    ),
    canfail_clause=(
        "The grid MUST contain at least one locus whose target frequency is "
        "CLOSER to 1/2 than its source frequency -- (0.184, 0.338), "
        "(0.748, 0.458) and (0.212, 0.668) are those points, with measured "
        "ratios 1.54, 1.32 and 1.37. Only there does the measured retention "
        "exceed 1, and no strictly decreasing function of |delta p| can "
        "produce a value above 1, so those points alone separate the "
        "functional FORM rather than a constant. The grid must also contain "
        "at least one FIXED target locus (p_t = 0 or 1, measured ratio "
        "exactly 0), which is what exposes the exp(-2) floor. And it must "
        "retain the (0.588, 0.590) point where both sides are 1 to within "
        "1.4%: without it the check would not show that the disagreement is "
        "about the shape and not an overall offset."
    ),
)


# --- 15. The order-free ensemble channel: what cluster/fam_ensemble_channel.py
#         established. --------------------------------------------------------
#
# FIRST CONTACT between Sec. 14 of FoldedSpectrum.lean / EnsembleChannel.lean
# and any number. The simulator is a latent 2-D chain with eigenvalue
# lambda = rho e^{i theta}; because rho R(theta) is a scaled rotation the
# stationary state covariance is exactly isotropic, so gamma(k) =
# amp rho^k cos(k theta) and L = whiteFloor + longRunVariance are closed form
# and every prediction below carries NO FREE CONSTANT.
#
# FINDING 1 (the channel is real, and it is the FEJER sum, not L).
#   Measured n' Var(sample mean) against BOTH references over a rho grid from
#   0 to 0.995 and theta from 0 to pi, 20000 replicates per cell at n' = 4000:
#     - against the exact finite-depth Fejer sum: worst disagreement 1.55
#       sigma over 14 cells. The instrument is sound.
#     - against L, the n' -> infinity limit: 12 of 14 cells inside 2%, worst
#       3.5% at rho = 0.995 where n'/tau = 20.
#   The two cells that miss L are exactly the two with the least depth per
#   mixing time, and the depth sweep pins the mechanism: at rho = 0.99 the
#   deficit against L runs -84.9%, -73.8%, -56.4%, -36.1%, -19.8%, -9.1%,
#   -4.4%, -3.0% as n' runs 32 -> 4096, while the deficit against the Fejer
#   sum stays inside +-1.7% at every one of those depths. So `SampleBudget`'s
#   `depthSufficient` is not a technicality: at n'/tau = 0.3 the channel reads
#   15% of L. The corpus's own Sec. 14c claim that depth past the mixing scale
#   "buys nothing" is confirmed from the other side -- past n'/tau ~ 40 the
#   remaining deficit is at the 1% sampling floor.
#
# FINDING 2 (THE REFUTATION -- Sec. 14a is too strong, and EnsembleChannel.lean
#   is right). Sec. 14a says an order-free sample carries "EXACTLY ONE spectral
#   functional beyond the marginal" and that perturbing off zero frequency
#   "leaves the order-free law unchanged AT EVERY SYMMETRIC ORDER".
#   EnsembleChannel.lean's docstring says the opposite. MEASURED, on two
#   Gaussian MA processes with marginal EXACTLY N(0,1) and L identical to
#   machine precision (b = (1,0,0) against b = (2/3,2/3,-1/3), spectral density
#   at pi of 1 against 1/9), 40000 replicates at n' = 2000:
#     mean channel     1.00060 vs 1.00095   agree     (+0.0 sigma)
#     third moment    15.00608 vs 15.05506  agree     (+0.3 sigma)
#     SECOND moment    1.98537 vs  2.38248  SEPARATE (+18.1 sigma, 20.0%)
#     FOURTH moment   95.65702 vs 110.36811 SEPARATE (+14.2 sigma, 15.4%)
#     mean |F|         0.36166 vs  0.42183  SEPARATE (+15.3 sigma, 16.6%)
#     sample variance  1.98299 vs  2.38136  SEPARATE (+18.2 sigma, 20.1%)
#     empirical CDF at -1 and +1             SEPARATE (+4.9, +4.4 sigma)
#   Six of ten order-free channels separate two processes that share the
#   marginal and share L. The Isserlis closed forms predict all of it with no
#   free constant -- 2*sum gamma^2 = 2.000 against 2.395, and
#   72*sum gamma^2 + 24*sum gamma^4 = 96.00 against 110.46 -- and the
#   measurements sit on those numbers. The pattern is exactly the parity
#   structure of the two files: ODD-order channels see only sum gamma(k), which
#   is L and therefore agrees; EVEN-order channels see sum gamma(k)^2, which L
#   does not determine. The corollary is that Sec. 14a's tangent-space
#   invisibility claim is false as stated and must be restricted to the
#   sample-MEAN channel, which is what `three_mul_sampleMeanVariance3` actually
#   proves.
#
# FINDING 3 (Sec. 14b's rate holds; Sec. 14c's identity holds).
#   Ensemble deconvolution of the chi^2_1 mixing kernel across m cohorts
#   recovers E[L] and Var[L] at fitted rates -0.5167 and -0.4807 against the
#   claimed -1/2, over m = 25 -> 6400 with 640000 cohorts in the pool. The
#   `EnsembleTransfer` variance identity Var(b) = Var(E[b|v]) + E[Var(b|v)]
#   holds to 1e-17 on oracle visibles, with the curve arm's fiber variance
#   exactly 0 (0.043780 = 0.043780 + 0.000000) and the sheet arm's strictly
#   positive (0.023488 = 0.006633 + 0.016855). The sheet arm is what makes the
#   curve arm a result rather than a degeneracy.

check(
    id="fejerChannel3-is-the-depth-3-sample-mean-channel",
    fqn="Calibrator.fejerChannel3",
    claim="the three-locus Fejer channel is exactly 3 Var(sample mean) at "
          "depth 3, i.e. the general Fejer sum "
          "gamma0 + 2 sum_{k=1}^{n-1} (1-k/n) gamma(k) evaluated at n = 3",
    model_lean="gamma0 + (4/3) gamma1 + (2/3) gamma2",
    model_ref="the finite-depth Fejer sum at n = 3, computed from the general "
              "formula rather than from the three-term expansion",
    reference="n Var(mean) = gamma0 + 2 sum_{k=1}^{n-1} (1-k/n) gamma(k), "
              "cluster/fam_ensemble_channel.py fejer_channel",
    grid=grid(g0=[1.0, 2.0, 5.0],
              g1=[0.0, 0.2222222222222222, -0.4, 0.48],
              g2=[0.0, -0.2222222222222222, 0.3]),
    lean=lambda D, g0, g1, g2: D["fejerChannel3"](g0, g1, g2),
    ref=lambda g0, g1, g2: g0 + 2 * (1 - 1 / 3) * g1 + 2 * (1 - 2 / 3) * g2,
    kind="identity",
    note=(
        "POSITIVE CONTROL for the pair below, and the anchor that makes the "
        "simulator's reference the corpus's own. cluster/fam_ensemble_channel.py "
        "measured the same quantity at n' = 4000 across 14 cells and hit the "
        "general Fejer sum to within 1.55 sigma everywhere, so the formula the "
        "corpus states at n = 3 is the formula the process obeys at every "
        "depth. It is registered separately from the L check because the whole "
        "attribution of Sec. 14's depth hypothesis rests on the two being "
        "DIFFERENT quantities."
    ),
    canfail_clause=(
        "the grid must contain profiles with gamma1 and gamma2 of OPPOSITE "
        "sign, and in particular the (1, 2/9, -2/9) profile whose Fejer value "
        "coincides with the white profile's. Without a sign change the two "
        "lag coefficients 4/3 and 2/3 cannot be separated from each other or "
        "from the 2 and 2 of the untruncated sum, and a check restricted to "
        "positive profiles would pass for the long-run variance as well."
    ),
)

check(
    id="fejerChannel3-is-not-the-long-run-variance",
    fqn="Calibrator.fejerChannel3",
    claim="REGIME: the depth-3 channel is NOT the zero-frequency evaluation. "
          "Sec. 14a states the channel as Var(sample mean) -> L/n' with "
          "L = whiteFloor + longRunVariance, but at finite depth the sample "
          "mean sees the FEJER sum, which weights lag k by (1 - k/n) and "
          "therefore depends on rho and theta separately rather than on L "
          "alone. The gap is the content of `SampleBudget.depthSufficient`",
    model_lean="gamma0 + (4/3) gamma1 + (2/3) gamma2, the depth-3 channel",
    model_ref="L = gamma0 + 2 gamma1 + 2 gamma2, the zero-frequency "
              "evaluation the channel is claimed to converge to",
    reference="cluster/fam_ensemble_channel_results.json, T1b_depth_sweep",
    grid=[
        {"g0": 2.0, "g1": 1.8, "g2": 1.62, "note_n": 3},
        {"g0": 2.0, "g1": 0.9, "g2": 0.405, "note_n": 3},
        {"g0": 1.0, "g1": 0.2222222222222222, "g2": -0.2222222222222222,
         "note_n": 3},
    ],
    lean=lambda D, g0, g1, g2, note_n: D["fejerChannel3"](g0, g1, g2),
    ref=lambda g0, g1, g2, note_n: g0 + 2 * g1 + 2 * g2,
    kind="model",
    expected_verdict="MODEL",
    tol=1e-3,
    note=(
        "EXPECTED TO DISAGREE, and the disagreement IS the result. The two "
        "sides are the same quantity only in the n' -> infinity limit, and "
        "nothing in `OrderFreeChannel` records the finite-depth form: its "
        "`variance_eq` field asserts meanVariance = (whiteFloor + "
        "longRunVariance)/sampleSize as an EQUATION at finite sampleSize, "
        "with `fluctuationUniformity` left as an opaque audit Prop.\n\n"
        "MEASURED, cluster/fam_ensemble_channel.py, 20000 replicates per cell. "
        "At rho = 0.99, theta = 0 (L = 200.0) the measured n' Var(mean) runs\n"
        "  n' =   32 (n'/tau = 0.3):  30.25   vs Fejer  29.83   vs L  -84.9%\n"
        "  n' =  128 (n'/tau = 1.3):  87.19   vs Fejer  88.05   vs L  -56.4%\n"
        "  n' =  512 (n'/tau = 5.1): 160.42   vs Fejer 161.55   vs L  -19.8%\n"
        "  n' = 4096 (n'/tau =  41): 194.01   vs Fejer 195.17   vs L   -3.0%\n"
        "so the Fejer sum is hit to better than 1.7% at EVERY depth while L is "
        "missed by up to 85%. The repair is a regime declaration, not new "
        "arithmetic: `variance_eq` is an asymptotic statement and the finite-n' "
        "channel is the Fejer sum. The third grid row is the (1, 2/9, -2/9) "
        "profile where the two sides agree exactly, which is what shows this "
        "is a shape disagreement and not an offset."
    ),
    canfail_clause=(
        "The grid MUST contain the (1, 2/9, -2/9) profile, where the depth-3 "
        "channel and L are both exactly 1 and the check reports agreement. "
        "Without it a reader could not tell this check from one that always "
        "disagrees, and the whole point is that the two quantities coincide on "
        "a codimension-one set and differ by up to 85% off it. The other two "
        "rows must be strongly persistent (gamma1, gamma2 > 0 and decaying "
        "slowly), because for a rapidly decaying profile the truncation is "
        "invisible and the check would report agreement for the wrong reason."
    ),
)

check(
    id="gaussianPairSquareChannel3-separates-equal-fejer-profiles",
    fqn="Calibrator.gaussianPairSquareChannel3",
    claim="THE REFUTATION OF Sec. 14a. The symmetric fourth-order Gaussian "
          "channel separates two covariance profiles with the SAME Fejer "
          "channel, so an order-free sample carries strictly MORE than the "
          "zero-frequency evaluation. Sec. 14a's claim that off-zero "
          "perturbation 'leaves the order-free law unchanged at every "
          "symmetric order' is false as stated",
    model_lean="3 gamma0^2 + 4 gamma1^2 + 2 gamma2^2, the Isserlis pair-square "
               "channel at depth 3",
    model_ref="the MEASURED n' Var of a symmetric fourth-order order-free "
              "statistic, rescaled to depth 3, on two Gaussian MA processes "
              "with marginal exactly N(0,1) and L identical to machine "
              "precision",
    reference="cluster/fam_ensemble_channel_results.json, T2_channels",
    grid=[
        {"g0": 1.0, "g1": 0.0, "g2": 0.0, "measured_ratio": 1.0},
        {"g0": 1.0, "g1": 0.1, "g2": -0.2, "measured_ratio": 1.0},
    ],
    lean=lambda D, g0, g1, g2, measured_ratio: (
        D["gaussianPairSquareChannel3"](g0, g1, g2)
        / D["gaussianPairSquareChannel3"](1.0, 0.0, 0.0)),
    ref=lambda g0, g1, g2, measured_ratio: measured_ratio,
    kind="model",
    expected_verdict="MODEL",
    tol=1e-3,
    note=(
        "EXPECTED TO DISAGREE ON THE SECOND ROW, and that disagreement is the "
        "finding. The two grid rows are exactly the profiles of "
        "`equal_fejer_channel_witness`: fejerChannel3 1 0 0 = "
        "fejerChannel3 1 (1/10) (-1/5) = 1, proved in EnsembleChannel.lean, "
        "while `unequal_symmetric_fourth_channel_witness` proves the "
        "fourth-order values differ (3 against 3 + 4/100 + 2/25 = 3.12, a 4% "
        "separation). The reference column pins BOTH rows at ratio 1, which is "
        "what Sec. 14a of FoldedSpectrum.lean asserts, so the check agrees on "
        "the white row and disagrees on the dependent one.\n\n"
        "MEASURED INDEPENDENTLY, cluster/fam_ensemble_channel.py, 40000 "
        "replicates at n' = 2000 on b = (1,0,0) against b = (2/3,2/3,-1/3) -- "
        "marginal exactly N(0,1) for both, L identical to 1e-16, spectral "
        "density at pi of 1.000 against 0.111:\n"
        "  second-moment channel   1.98537 vs 2.38248, +18.1 sigma, +20.0%; "
        "Isserlis predicts 2.000 vs 2.395\n"
        "  fourth-moment channel  95.65702 vs 110.36811, +14.2 sigma, +15.4%; "
        "Isserlis predicts 96.00 vs 110.46\n"
        "  sample variance         1.98299 vs 2.38136, +18.2 sigma\n"
        "  mean |F|                0.36166 vs 0.42183, +15.3 sigma\n"
        "  empirical CDF at -1     0.13287 vs 0.13952, +4.9 sigma\n"
        "and the ODD channels agree, as the parity structure requires: mean "
        "1.00060 vs 1.00095 (+0.0 sigma), third moment 15.00608 vs 15.05506 "
        "(+0.3 sigma). Odd-order channels see sum gamma(k), which is L; "
        "even-order channels see sum gamma(k)^2, which L does not determine.\n\n"
        "The repair is a restriction, not a rescaling. Sec. 14a is correct "
        "about the sample-MEAN channel and wrong about 'every symmetric "
        "order'; the invisible set is the tangent space of the mean channel "
        "only, and the fourth-order channel is a second, independent "
        "functional that an order-free panel also carries."
    ),
    canfail_clause=(
        "The grid must hold the WHITE row (1,0,0) as well as the dependent "
        "one. On the white row both sides are 1 and the check AGREES; that "
        "agreement is the control showing the check is not one that fires on "
        "everything. The dependent row must also be a profile whose Fejer "
        "value is unchanged -- gamma1 = 1/10, gamma2 = -1/5 gives "
        "1 + 4/30 - 2/15 = 1 exactly -- because on a profile that moves the "
        "Fejer value too, a fourth-order separation would prove nothing about "
        "off-zero invisibility. It must further be a profile with a positive "
        "trigonometric symbol, which `dependent_channel_symbol_positive` "
        "proves for this one and which is what makes it a stationary "
        "covariance profile at all rather than an arbitrary triple."
    ),
)


# ===========================================================================
# 20. THE IDENTITY GATE, applied to the SIMULATION ORACLE'S ESTIMATOR
# ===========================================================================
# A simulation MATCH is evidence only if the oracle could have said no. When
# the oracle estimates its "truth" with an estimator that the definition under
# test reduces to under the model's DEFINING relations alone, the two sides are
# the same expression and the residual is zero for every seed, every design and
# every parameter. The verdict is then a property of the algebra, not of the
# population -- and it looks exactly like a triumph.
#
# `battery_bulk21` banked MATCH for `driftVariance`, `twoPopDriftVariance` and
# `expectedFreqDiffSq` against a Wright-Fisher simulation. All three are
# vacuous. The simulator estimates F_ST on the same run as
#
#     F_ST := Var(p) / (p0 (1 - p0))
#
# which is Wright's definition, not a measurement of it. Substituting it into
# each body collapses the body onto `Var(p)` -- the estimator itself -- using no
# Wright-Fisher property beyond the martingale `E[p_t] = p0`. Computer algebra
# gives residual exactly 0; a body that is genuinely a different function of the
# same inputs does NOT collapse (a planted `p0(1-p0) fst^2` leaves the nonzero
# residual `Var(p)(-Var(p) - p0^2 + p0)/(p0(p0-1))`), so THAT design had power it
# never spent.
#
# WHAT THESE CHECKS DO AND DO NOT SAY, because an earlier version of this note
# got it wrong. They establish an ALGEBRAIC FACT: composing the definition with a
# SAMPLE-ESTIMATED F_ST is the identity. They do NOT say the definitions are
# untestable, and they must not be read that way. `battery_bulk41` group B takes
# F from the MODEL -- `1-(1-1/(2Ne))^t`, a function of the simulation's
# parameters and nothing else -- measures the Hudson and Nei readings separately
# on the same replicates as competitors, and FALSIFIES both while the body
# matches at under 1 sem. That is a real measurement with real discriminating
# power, and all three definitions are VALIDATED on it.
#
# So the vacuity is a property of a DESIGN, not of a definition. The same body
# and the same oracle give opposite verdicts depending only on where F came from,
# which is exactly why `simcov/verdict.py` keys its gate on a declared
# `argument_source` rather than on the definition's name -- a name-keyed gate
# would have discarded battery_bulk41's finding, which is the expensive
# direction to be wrong in.
#
# These checks are recorded as `kind="identity"` so they count as
# duplicate-detection rather than as validations. Their purpose is to keep the
# algebraic fact from lapsing: if a body is ever changed so that the composition
# stops being the identity, the check reports IDENTICAL-BODIES against an
# expected AGREE and run.py returns 1.
_DRIFT_IDENTITY = grid(p0=[0.05, 0.2, 0.5, 0.8], Varp=[1e-4, 1e-3, 1e-2])

check(
    id="driftVariance-is-the-oracle-estimator",
    fqn="Calibrator.AncestrySpecificArchitecture.driftVariance",
    claim="driftVariance(p0, Var(p)/(p0(1-p0))) is exactly Var(p), for all inputs",
    model_lean="Wright F defined as between-population variance over ancestral heterozygosity",
    model_ref="the estimator battery_bulk21 computes on the same simulated run",
    reference="the simulation oracle's own F_ST estimator, inverted",
    grid=_DRIFT_IDENTITY,
    lean=lambda D, p0, Varp: D["driftVariance"](p0, Varp / (p0 * (1 - p0))),
    ref=lambda p0, Varp: Varp,
    kind="identity",
    expected_verdict="AGREE",
    note=(
        "Pins an ALGEBRAIC FACT, not a verdict on the definition. With a "
        "sample-estimated F the body and the oracle's estimator are the same "
        "expression, which is why battery_bulk21's MATCH carried no "
        "information. battery_bulk41 group B feeds the MODEL's F instead and "
        "VALIDATES the body at under 1 sem while falsifying both competing "
        "F_ST conventions, so the definition itself is well tested."
    ),
    canfail_clause=(
        "no grid can make this fail, and that IS the finding rather than a "
        "defect of the check: the composition is the identity at every input. "
        "Power against a WRONG body is supplied instead by the mutant sweep -- "
        "a 5% rescaling of driftVariance breaks the round trip at every point, "
        "so the check is reported non-vacuous. Both directions are therefore "
        "asserted: identity on the real body, separation on a wrong one."
    ),
)

check(
    id="twoPopDriftVariance-is-twice-the-oracle-estimator",
    fqn="Calibrator.AncestrySpecificArchitecture.twoPopDriftVariance",
    claim="twoPopDriftVariance(p0, Var(p)/(p0(1-p0))) is exactly 2 Var(p)",
    model_lean="two lineages drifting independently from a shared ancestor",
    model_ref="the same estimator, doubled -- which is what the oracle computes for Var(p1-p2)",
    reference="the simulation oracle's own F_ST estimator, inverted and doubled",
    grid=_DRIFT_IDENTITY,
    lean=lambda D, p0, Varp: D["twoPopDriftVariance"](p0, Varp / (p0 * (1 - p0))),
    ref=lambda p0, Varp: 2.0 * Varp,
    kind="identity",
    expected_verdict="AGREE",
    note=(
        "With a sample-estimated F, the factor of 2 the docstring argues for "
        "is assumed by the oracle's estimator rather than tested by it. Under "
        "battery_bulk41's model-supplied F it IS tested: dropping the two "
        "misses by up to 168 sems."
    ),
    canfail_clause=(
        "as driftVariance-is-the-oracle-estimator: identity by construction on "
        "the real body, separated from a rescaled body by the mutant sweep."
    ),
)

check(
    id="expectedFreqDiffSq-is-twice-the-oracle-estimator",
    fqn="Calibrator.AncestrySpecificArchitecture.expectedFreqDiffSq",
    claim="expectedFreqDiffSq(Var(p)/(p0(1-p0)), p0) is exactly 2 Var(p)",
    model_lean="E[(p1-p2)^2] under independent per-branch drift",
    model_ref="the same estimator, doubled",
    reference="the simulation oracle's own F_ST estimator, inverted and doubled",
    grid=_DRIFT_IDENTITY,
    lean=lambda D, p0, Varp: D["expectedFreqDiffSq"](Varp / (p0 * (1 - p0)), p0),
    ref=lambda p0, Varp: 2.0 * Varp,
    kind="identity",
    expected_verdict="AGREE",
    note=(
        "Same body as twoPopDriftVariance with the arguments in the other "
        "order, so it inherits the same algebra. A sample-estimated F cannot "
        "answer the factor-of-2 or the Nei-vs-Hudson question, because the "
        "estimator carries the corpus's own convention; a model-supplied F "
        "answers both, and battery_bulk41 does (Nei refuted at 157 sems)."
    ),
    canfail_clause=(
        "identity by construction on the real body; the mutant sweep supplies "
        "the separation. The argument ORDER is also load-bearing here and the "
        "transposition mutant exercises it."
    ),
)


# ===========================================================================
# 21. COALESCENT SCALING INVARIANCE
# ===========================================================================
# Neutral diffusion-scale quantities depend on the population size and the
# per-generation rates only through the scaled products 4*Ne*m, 4*Ne*mu,
# 4*Ne*c and the scaled time t/(2*Ne). Such a quantity is therefore EXACTLY
# invariant under
#
#     Ne -> lam*Ne,   m -> m/lam,   mu -> mu/lam,   c -> c/lam,   t -> lam*t.
#
# This is a dimensional-homogeneity check in the only form that survives the
# corpus's conventions. Assigning generations to `Ne` and per-generation to `m`
# and demanding term-by-term homogeneity flags every discrete per-generation
# recurrence -- `1 - 1/(2*Ne)` mixes a pure number with a rate -- because those
# carry an implicit one-generation step. Scaling invariance asks the same
# question without that false positive, and it needs no parser, no unit table
# and no symbolic algebra: evaluate the definition twice and compare.
#
# It is exact, deterministic, sub-millisecond, and commits to NO F_ST
# convention, which is what makes it admissible as a gate. It applies only to
# definitions declared diffusion-scale; discrete recurrences are NOT invariant
# (their invariance is only asymptotic) and are deliberately absent rather than
# silently exempted.
#
# WHICH DEFINITIONS ARE ADMISSIBLE HERE, AND WHY THE LIST IS SHORT.
# A scaling-invariance check has power only against mutants that BREAK the
# scaling. The harness's own mutant sweep rescales the definition (which cancels,
# since both sides call it) and transposes its first two arguments (which is the
# mutation that bites). So a definition whose first two arguments carry EQUAL and
# OPPOSITE powers of lam -- `fstMigrationDriftEquilibrium(Ne, m)`,
# `hetMutationFloor(Ne, mu)`, `coalFst(t, Ne)` -- is invariant under transposition
# too, and a scaling check on it cannot fail. Those three were written, found
# vacuous by the sweep, and REMOVED rather than relabelled `kind="identity"` to
# get them past the vacuity count. A check that cannot fail is not a weaker
# check, it is not a check; the honest move is to delete it and say so here.
# What remains are the definitions whose argument list makes the check bite.
_LAM = 4.0


def _scale_check(cid, fqn, claim, fn, args, expected=None, note="", extra=""):
    """Assert f(theta) == f(rescaled theta) for a diffusion-scale quantity.

    `args` maps each argument name to (value, exponent), where the exponent is
    the power of `lam` that argument carries: sizes and times +1, per-generation
    rates -1, dimensionless arguments 0.
    """
    base = {k: v for k, (v, _e) in args.items()}
    scaled = {k: v * _LAM ** e for k, (v, e) in args.items()}
    check(
        id=cid,
        fqn=fqn,
        claim=claim,
        model_lean="diffusion scale: depends on Ne and the rates only through 4*Ne*rate",
        model_ref="the same definition at Ne, rates rescaled by lam=%g and 1/lam" % _LAM,
        reference="coalescent scaling invariance of the same definition",
        grid=[{}],
        lean=(lambda f, b: lambda D: f(D, **b))(fn, base),
        ref=(lambda f, s: lambda D: f(D, **s))(fn, scaled),
        kind="internal",
        expected_verdict=expected,
        note=note,
        canfail_clause=(
            "lam must be far from 1 (it is %g) and the quantity must not be "
            "saturated: a formula evaluated where it is pinned at 0 or 1 is "
            "invariant for the wrong reason. Power against a mutated body comes "
            "from the harness's transposition mutant, which is the only mutant "
            "that breaks a scaling relation -- a rescaling of the definition "
            "cancels, since both sides call it. %s" % (_LAM, extra)
        ),
    )


_scale_check(
    "demoSteppingStoneFst-scale-invariant",
    "Calibrator.DemographicHistory.demoSteppingStoneFst",
    "d/(d + 4 Ne m sigma_sq) depends on Ne and m only through their product",
    lambda D, d, Ne, m, s2: D["demoSteppingStoneFst"](d, Ne, m, s2),
    {"d": (4.0, 0), "Ne": (500.0, 1), "m": (0.008, -1), "s2": (1.0, 0)},
    note=(
        "CONTROL for steppingStoneFstQuadratic-scale-VIOLATION below. This is "
        "the sibling that carries the migration rate to the first power, and it "
        "is exactly invariant. The pair together is what makes the violation a "
        "finding rather than a property of the check."
    ),
    extra="F_ST at the base point is 0.20, away from both 0 and 1.",
)

_scale_check(
    "steppingStoneFstQuadratic-scale-VIOLATION",
    "Calibrator.DemographicHistory.steppingStoneFstQuadratic",
    "d/(d + 4 Ne sigma_sq^2 m^2) is NOT a function of the scaled migration rate",
    lambda D, d, Ne, m, s2: D["steppingStoneFstQuadratic"](d, Ne, m, s2),
    {"d": (4.0, 0), "Ne": (500.0, 1), "m": (0.008, -1), "s2": (1.0, 0)},
    expected="INTERNAL-INCONSISTENT",
    note=(
        "PINNED FALSIFIED. sigma_sq^2 * m^2 carries one power of m more than "
        "the diffusion scale admits, so the body changes by a factor of lam "
        "under a rescaling that must leave it fixed. This is a third, "
        "convention-free confirmation of the verdict two independent log-log "
        "slope measurements already reached (battery_core2, battery_bulk17: "
        "fitted exponent 0.974 +- 0.042 against a predicted 2). It costs no "
        "simulation and commits to no F_ST convention. Pinned as an EXPECTED "
        "disagreement: if this ever starts agreeing, either the body was "
        "corrected -- in which case retire the check and the FALSIFIED note "
        "with it -- or the check stopped measuring, and both must be noticed."
    ),
    extra=(
        "The sibling control above must stay AGREE on the same base point; a "
        "check that fired on both would be measuring the harness, not the body."
    ),
)

_scale_check(
    "ibdFst-scale-VIOLATION-under-the-deme-size-reading",
    "Calibrator.AssortativeMatingPGS.ibdFst",
    "d/(4 N sigma_sq + d) is not diffusion-scale if N is read as a deme SIZE",
    lambda D, d, N, s2: D["ibdFst"](d, N, s2),
    {"d": (4.0, 0), "N": (500.0, 1), "s2": (1.0, 0)},
    expected="INTERNAL-INCONSISTENT",
    note=(
        "CONVENTION, NOT A DEFECT -- and the distinction is the point. Under "
        "the deme-size reading the body carries a bare N with no rate to pair "
        "it with, so it is not invariant. That reading is the WRONG one: N here "
        "is a population DENSITY and the body is Rousset's isolation-by-distance "
        "law F/(1-F) = d/(4 N sigma^2), in which dispersal enters through "
        "sigma_sq and abundance through the density, so there is no migration "
        "rate to scale. The check is pinned as an expected disagreement to "
        "record exactly that: what fires here is the deme-size misreading, "
        "which the docstring now rules out. Contrast demoSteppingStoneFst "
        "above, whose Ne IS a deme size and which therefore must and does carry "
        "m -- and is invariant. Registered as DIAGNOSTIC in intent: a scaling "
        "violation is proof of a defect only once the convention is fixed, and "
        "this is the case where fixing it dissolves the violation."
    ),
    extra=(
        "This one cannot be promoted to a defect by the check alone; it needs "
        "the docstring's convention statement, which is why the note carries it."
    ),
)


# ===========================================================================
# ROUND TRIPS: does a definition that claims to INVERT something invert it?
# ===========================================================================
# A whole class of defect survives every proof in the corpus: a definition
# whose form encodes a direction, an inverse, or a ratio, written the wrong way
# round.  It is total, it type-checks, its theorems prove, and it computes the
# reciprocal of what its name says.  Kernel checking cannot see it, because
# nothing is false -- the statements are all true ABOUT THE WRONG FUNCTION.
#
# The shape that catches it is a round trip.  Take a known input, push it
# through an independently written FORWARD model, push the result through the
# corpus's inverse, and require the original back.  A reciprocal error returns
# the input distorted by the square of the artifact, so it separates hard.
#
# These are pinned `expected_verdict="AGREE"`: for this family a disagreement
# is a defect, so it must be reported as a verdict REGRESSION and fail the run
# rather than being recorded as an interesting number.
#
# LIMITATION, stated because the reader needs it: a round trip constrains the
# COMPOSITION, so it cannot by itself distinguish "the inverse is wrong" from
# "the forward reference is wrong in the mirrored way".  What breaks the tie is
# that the reference is built from a different definition in the corpus (the
# inflation law) than the one under test, and that the two are separately
# documented.  A round trip whose forward model is a rearrangement of the
# definition it checks is worthless; see the note in refs.py.

_AM_ROUNDTRIP = grid(
    # true target/source R^2 ratio: perfect portability and two lossy cases
    q=[1.0, 0.7, 0.4],
    # source assorts more strongly than target in every cell (r_t < r_s), which
    # is the regime the corpus's DifferentialAMModel fixes by hypothesis
    r_s=[0.2, 0.5, 0.8],
    r_t=[0.0, 0.1],
    # r_s*h2 <= 0.72 < 1 everywhere, so the stability condition holds and no
    # denominator approaches zero
    h2=[0.3, 0.6, 0.9],
)

check(
    id="amCorrectedPortability-inverts-the-AM-artifact",
    fqn="Calibrator.amCorrectedPortability",
    claim=(
        "Correcting a measured portability for differential assortative mating "
        "returns the true target/source R2 ratio."
    ),
    model_lean="the corpus's AM correction, whatever direction it is written in",
    model_ref=(
        "Fisher AM inflation applied separately in each population "
        "(refs.am_inflated_r2), composed to give the measured ratio"
    ),
    reference="refs.am_measured_portability, inverted",
    grid=_AM_ROUNDTRIP,
    lean=lambda D, q, r_s, r_t, h2: D["amCorrectedPortability"](
        refs.am_measured_portability(q, r_s, r_t, h2), r_s, r_t, h2),
    ref=lambda q, r_s, r_t, h2: q,
    tol=1e-12,
    kind="formula",
    expected_verdict="AGREE",
    canfail_clause=(
        "The historical defect is the live can-fail evidence. The definition "
        "multiplied by (1 - r_source*h2)/(1 - r_target*h2), the artifact itself "
        "rather than its reciprocal, so this round trip returned "
        "q * ((1-r_s*h2)/(1-r_t*h2))^2 instead of q. At q=1, r_s=1/2, r_t=0, "
        "h2=1/2 that is 9/16 against 1 -- a 44% disagreement, far outside tol. "
        "test_roundtrip.py replays that exact planted definition and asserts "
        "this check reports it."
    ),
    note=(
        "Direction check. The q=1 cells alone would be satisfiable by a "
        "definition that always returns its first argument, so the grid also "
        "carries q=0.7 and q=0.4: a pass-through would return the MEASURED "
        "ratio there, not the true one. That is why the grid is not all-ones."
    ),
)


# --- the squaring flow's next floor, off the unit-variance slice -----------
# A ratio whose numerator and divisor were stated at DIFFERENT generality: the
# numerator is the general E[(X^2-1)^4], the divisor was (m4-1)^2, which is
# (E[Y^2])^2 only at m2 = 1. Every call site passes m2 = 1, so nothing computed
# a wrong number -- but the signature took an m2 it then ignored in half the
# expression. The grid therefore spends most of its cells OFF that slice, which
# is the only place the two forms separate.

_SQUARING_FLOW = grid(
    a=[1.5, 2.0, 3.0],
    p=[0.1, 0.25, 0.4],
)

check(
    id="nextFloorFourthMoment-is-the-standardized-fourth-moment-of-Y",
    fqn="Calibrator.nextFloorFourthMoment",
    claim=(
        "The next floor's fourth moment is E[Y^4]/(E[Y^2])^2 for Y = X^2 - 1, "
        "at every variance and not only at unit variance."
    ),
    model_lean="the corpus body, evaluated on the raw moments of an explicit law",
    model_ref="the same law's Y = X^2 - 1, from realised values",
    reference="refs.squaring_flow_next_fourth_moment",
    grid=_SQUARING_FLOW,
    lean=lambda D, a, p: D["nextFloorFourthMoment"](*refs._three_point_moments(a, p)),
    ref=lambda a, p: refs.squaring_flow_next_fourth_moment(a, p),
    tol=1e-9,
    kind="formula",
    expected_verdict="AGREE",
    canfail_clause=(
        "The historical divisor (m4 - 1)^2 is the can-fail evidence: on the "
        "two-point law X = +-2, where Y is constant and the true value is "
        "exactly 1, it returns 9/25. Only the p = 0.25, a = sqrt(2) cell of "
        "this grid sits at m2 = 1, so the old body disagrees almost everywhere "
        "on it."
    ),
    note=(
        "Moments come from an explicit finite law rather than being swept as "
        "four independent axes. Sweeping m2, m4, m6, m8 freely would wander "
        "outside the moment cone, where neither side means anything and a "
        "disagreement would not be evidence."
    ),
)
