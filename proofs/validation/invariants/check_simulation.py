"""FAMILY 3 -- simulation against independent ground truth.

The range and invariant tiers need no reference values, which is why they cover
the corpus in bulk.  What they cannot settle is whether a formula computes the
quantity its NAME claims: `2 * p * (1 - p)` is in range, is continuous, is
symmetric under nothing in particular, and is either the Hardy-Weinberg
genotype variance or it is not.  Only an external reference decides that.

Each spec below pairs a definition with an oracle that SIMULATES the named
quantity from first principles -- draw individuals, draw genotypes, run
generations, measure.  No oracle is obtained by rearranging the Lean formula,
because an oracle obtained that way tests nothing.

The same falsifiability discipline applies as everywhere else in this
directory: a definition counts as covered only when a mutated body is REJECTED
by its oracle.  A comparison that accepts every mutant is measuring Monte Carlo
noise, not the formula.

Run:  python check_simulation.py  ->  results_simulation.json
"""
from __future__ import annotations

import json
import math
import pathlib
import random
import sys
import zlib

import backends
import compile_defs as C
import sim_engines as S
from demo_falsifiable import compile_mutant

HERE = pathlib.Path(__file__).resolve().parent

def _takes_seed(fn):
    import inspect

    try:
        return "seed" in inspect.signature(fn).parameters
    except (TypeError, ValueError):
        return False


def spec(name, oracle, domain, note, tol=0.02, reps=6, oracle_alt=None):
    return dict(name=name, oracle=oracle, domain=domain, note=note,
                tol=tol, reps=reps,
                oracle_alt=oracle_alt or (lambda *a: oracle(*a, seed=1)
                                          if _takes_seed(oracle) else None))


# --------------------------------------------------------------------------
# The registry.  `domain` gives one (lo, hi) per argument IN THE LEAN ORDER.

SPECS = [
    spec("AncestrySpecificPower.genotypeVarianceHWE",
         lambda p, seed=0: S.sim_genotype_variance(p, seed=seed),
         [(0.05, 0.95)],
         "variance of a diploid dosage drawn Binomial(2, p)"),

    spec("AncestrySpecificArchitecture.driftVariance",
         lambda p0, fst, seed=0: S.sim_drift_variance(p0, fst, seed=seed),
         [(0.1, 0.9), (0.01, 0.2)],
         "Var(p_t) from an explicit binomial Wright-Fisher run drifted to the "
         "requested F_ST",
         tol=0.06),

    spec("AncestrySpecificArchitecture.expectedFreqDiffSq",
         lambda fst, p0, seed=0: S.sim_freq_diff_sq(p0, fst, seed=seed),
         [(0.01, 0.2), (0.1, 0.9)],
         "E[(p1-p2)^2] for two Wright-Fisher populations drifting "
         "independently from the same start",
         tol=0.06),

    spec("AncestrySpecificArchitecture.twoPopDriftVariance",
         lambda p0, fst, seed=0: S.sim_freq_diff_sq(p0, fst, seed=seed),
         [(0.1, 0.9), (0.01, 0.2)],
         "Var(p1-p2) between two independently drifting populations",
         tol=0.06),

    spec("AncestryCalibration.epistaticVariancePairwise",
         lambda g, p1, p2, seed=0: S.sim_pairwise_epistatic_variance(g, p1, p2, seed=seed),
         [(0.2, 2.0), (0.1, 0.9), (0.1, 0.9)],
         "variance of the pairwise product of centred Hardy-Weinberg dosages",
         tol=0.05),

    spec("EpistasisAndNonAdditivity.epistaticVariance",
         lambda b12, p1, p2, seed=0: S.sim_pairwise_epistatic_variance(b12, p1, p2, seed=seed),
         [(0.2, 2.0), (0.1, 0.9), (0.1, 0.9)],
         "variance of the pairwise product of centred Hardy-Weinberg dosages",
         tol=0.05),

    spec("Conventions.betweenSubgroupVariance",
         lambda p1, p2, seed=0: S.sim_between_subgroup_variance(p1, p2, seed=seed),
         [(0.05, 0.95), (0.05, 0.95)],
         "between-group component of allele-frequency variance over two "
         "equally sized subgroups",
         tol=0.05),

    spec("CovarianceStructure.haplotypeFreqAdmixed",
         lambda a, pA, qA, pB, qB, seed=0: S.sim_admixed_haplotype_freq(a, pA, qA, pB, qB, seed=seed),
         [(0.1, 0.9), (0.05, 0.95), (0.05, 0.95), (0.05, 0.95), (0.05, 0.95)],
         "frequency of the AB haplotype among individuals drawn from source A "
         "with probability alpha, each source in linkage equilibrium"),

    spec("CovarianceStructure.admixtureLDTwoLocus",
         lambda a, pA, qA, pB, qB, seed=0: S.sim_admixture_ld(a, pA, qA, pB, qB, seed=seed),
         [(0.15, 0.85), (0.05, 0.95), (0.05, 0.95), (0.05, 0.95), (0.05, 0.95)],
         "D = P(AB) - P(A)P(B) measured in a simulated admixed population",
         tol=0.05),

    spec("CovarianceStructure.admixtureLDAtGen",
         lambda a, pA, qA, pB, qB, r, g, seed=0: S.sim_admixture_ld_at_gen(
             a, pA, qA, pB, qB, r, g, seed=seed),
         [(0.2, 0.8), (0.1, 0.9), (0.1, 0.9), (0.1, 0.9), (0.1, 0.9),
          (0.02, 0.3), (1, 8)],
         "admixture LD after g generations of random mating with "
         "recombination, simulated end to end rather than multiplied by a "
         "decay factor",
         tol=0.06),

    spec("DGP.discreteRecombinationSurvival",
         lambda r, t, seed=0: S.sim_no_recombination_prob(r, t, seed=seed),
         [(0.01, 0.3), (1, 12)],
         "P(no recombination in t meioses), sampled"),

    spec("Conventions.geometricDecay",
         lambda r, t, seed=0: (lambda d: None if d is None else d / 0.2)(
             S.sim_ld_decay(0.2, r, t, seed=seed)),
         [(0.02, 0.3), (1, 8)],
         "fraction of LD surviving t generations of recombination, from an "
         "explicit two-locus haplotype pool",
         tol=0.06),

    spec("DGP.r2FromSignalVariance",
         lambda vs, vn, seed=0: S.sim_r2_from_variances(vs, vn, seed=seed),
         [(0.2, 5.0), (0.2, 5.0)],
         "squared correlation between signal and signal+noise, sampled"),

    spec("BayesianPGSTheory.jamesSteinMSE",
         lambda lam, s2, b2, seed=0: S.sim_shrinkage_mse(lam, s2, b2, seed=seed),
         [(0.05, 0.95), (0.2, 3.0), (0.2, 3.0)],
         "MSE of the shrunk estimator lam*(beta+noise) for beta, sampled",
         tol=0.03),

    spec("BayesianPGSTheory.optimalShrinkage",
         lambda s2, b2, seed=0: S.sim_optimal_shrinkage(s2, b2, seed=seed),
         [(0.3, 3.0), (0.3, 3.0)],
         "the shrinkage minimising MSE, found by grid search over a simulated "
         "sample rather than by formula",
         tol=0.03),

    spec("Conclusions.bernoulliLogLoss",
         lambda p, q, seed=0: S.sim_bernoulli_logloss(p, q, seed=seed),
         [(0.1, 0.9), (0.1, 0.9)],
         "E[-log P_q(y)] for y ~ Bernoulli(p), sampled",
         tol=0.02),

    spec("Conclusions.bernoulliKLReal",
         lambda p, q, seed=0: S.sim_bernoulli_kl(p, q, seed=seed),
         [(0.15, 0.85), (0.15, 0.85)],
         "E[log(P_p(y)/P_q(y))] for y ~ Bernoulli(p), sampled",
         tol=0.15),

    spec("Conclusions.expectedBrierScore",
         lambda p, pi, seed=0: S.sim_brier(p, pi, seed=seed),
         [(0.05, 0.95), (0.05, 0.95)],
         "E[(p - y)^2] for y ~ Bernoulli(pi), sampled"),

    spec("Conclusions.brierBernoulliRisk",
         lambda eta, q, seed=0: S.sim_brier(q, eta, seed=seed),
         [(0.05, 0.95), (0.05, 0.95)],
         "E[(q - y)^2] for y ~ Bernoulli(eta), sampled"),

    spec("ClinicalUtilityFairness.numberNeededToScreen",
         lambda sens, pi, seed=0: S.sim_number_needed_to_screen(sens, pi, seed=seed),
         [(0.3, 0.95), (0.02, 0.4)],
         "expected number screened to detect one case, sampled as a waiting "
         "time rather than computed",
         tol=0.03),
]


# --------------------------------------------------------------------------


def _grid(domain, reps, seed):
    rng = random.Random(seed)
    pts = []
    for _ in range(reps):
        p = []
        for lo, hi in domain:
            if isinstance(lo, int) and isinstance(hi, int):
                p.append(float(rng.randint(lo, hi)))
            else:
                p.append(rng.uniform(lo, hi))
        pts.append(p)
    return pts


def oracle_values(sp, pts):
    """Oracle at each point, with a Monte Carlo standard error.

    Run twice under different seeds.  The spread between the two runs
    estimates the sampler's own noise, which is what a comparison has to beat
    before it can be called a disagreement.  Without this a quantity that
    passes through zero -- admixture LD does -- shows an unbounded RELATIVE
    error at points where both numbers are noise, and gets reported as a
    defect.

    The oracle does not depend on the body, so this is computed ONCE per spec
    and reused for every mutant.  That is also what makes the mutation sweep
    affordable.
    """
    out = []
    for x in pts:
        try:
            a = sp["oracle"](*x)
            b = sp["oracle_alt"](*x) if sp.get("oracle_alt") else a
        except Exception as e:
            out.append(dict(value=None, se=None, error=str(e)))
            continue
        if a is None or b is None:
            out.append(dict(value=None, se=None, error="oracle undefined here"))
            continue
        se = abs(a - b) / math.sqrt(2.0)
        out.append(dict(value=0.5 * (a + b), se=se))
    return out


def compare(fn, sp, pts, orc):
    """Lean formula vs the cached oracle.  Returns rows and the worst gap.

    A point counts as disagreeing only when the gap exceeds BOTH the relative
    tolerance and three times the sampler's own standard error there.
    """
    rows, worst = [], 0.0
    for x, o in zip(pts, orc):
        if o["value"] is None:
            continue
        try:
            lean = float(fn(backends.FLOAT, *x))
        except Exception as e:
            rows.append(dict(point=x, error=f"lean: {e}"))
            continue
        ref, se = o["value"], o["se"] or 0.0
        gap = abs(lean - ref)
        allowed = max(sp["tol"] * max(abs(ref), abs(lean)), 3.0 * se)
        excess = gap / allowed if allowed > 0 else 0.0
        worst = max(worst, excess)
        rows.append(dict(point=[round(v, 6) for v in x], lean=lean,
                         oracle=ref, mc_se=se, gap=gap, allowed=allowed,
                         excess=excess))
    return rows, worst


def main(argv):
    defs = C.load_defs()
    cs, _, text = C.compile_all(defs)
    ns = {"backends": backends}
    exec(compile(text, "<calibrator>", "exec"), ns)

    results = {}
    for sp in SPECS:
        k = sp["name"]
        if k not in cs:
            results[k] = dict(verdict="not-compiled",
                              reason="definition absent or outside the "
                                     "arithmetic fragment")
            continue
        c = cs[k]
        if len(c.names) != len(sp["domain"]):
            results[k] = dict(verdict="spec-stale",
                              reason=f"spec has {len(sp['domain'])} arguments, "
                                     f"definition now has {len(c.names)} "
                                     f"({c.names}) -- the definition changed")
            continue
        # `hash()` on a str is SALTED PER PROCESS in Python, so this seed --
        # and therefore this tier's verdicts -- changed from run to run.  The
        # binder-fix re-run flipped `admixtureLDAtGen` from agrees to
        # disagrees with an identical body and identical parameters, which is
        # how it was found.  A simulation tier whose answers are not
        # reproducible cannot be used to adjudicate anything.
        pts = _grid(sp["domain"], sp["reps"],
                    seed=zlib.crc32(k.encode()) % 10000)
        orc = oracle_values(sp, pts)
        rows, worst = compare(c.fn, sp, pts, orc)
        agrees = worst <= 1.0

        # Falsifiability: a mutated body must be REJECTED by this oracle.
        killed, survived = [], []
        for tag, body in C.mutants(c.d["body"]):
            try:
                mc = compile_mutant(defs, ns, c.d, body)
                _, mworst = compare(mc.fn, sp, pts, orc)
            except Exception:
                continue
            if mworst > 1.0:
                killed.append(tag)
            else:
                survived.append(tag)

        results[k] = dict(
            verdict="agrees" if agrees else "disagrees",
            module=c.d["module"], line=c.d["line"],
            oracle=sp["note"], tolerance=sp["tol"],
            worst_excess_over_allowed=worst,
            n_points=len(pts),
            covered=bool(agrees and killed),
            falsifiability=dict(mutants_rejected=killed,
                                mutants_survived=survived),
            uncovered_reason=(
                None if (agrees and killed) else
                "the oracle disagrees with the definition" if not agrees else
                "no mutant of this body was rejected, so the comparison does "
                "not discriminate and this is NOT coverage"),
            worst_point=max((r for r in rows if "excess" in r),
                            key=lambda r: r["excess"], default=None),
        )

    out = HERE / "results_simulation.json"
    out.write_text(json.dumps(results, indent=1, default=str))
    ok = [k for k, v in results.items() if v.get("covered")]
    dis = [k for k, v in results.items() if v.get("verdict") == "disagrees"]
    vac = [k for k, v in results.items()
           if v.get("verdict") == "agrees" and not v.get("covered")]
    print(f"{len(SPECS)} specs -> {out}")
    print(f"  {len(ok)} covered (oracle agrees AND a mutant is rejected)")
    print(f"  {len(dis)} DISAGREE with the simulation")
    print(f"  {len(vac)} agree but no mutant was rejected -- not counted")
    for k in dis:
        v = results[k]
        w = v["worst_point"]
        print(f"\n  DISAGREES {k} ({v['module']}:{v['line']})")
        print(f"    oracle: {v['oracle']}")
        print(f"    at {w['point']}: lean {w['lean']:.6g} vs simulated "
              f"{w['oracle']:.6g}")
        print(f"    gap {w['gap']:.4g}, allowed {w['allowed']:.4g} "
              f"(tolerance or 3x the MC standard error {w['mc_se']:.4g}), "
              f"exceeded by {w['excess']:.1f}x")
    for k in vac:
        print(f"\n  VACUOUS {k}: {results[k]['falsifiability']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
