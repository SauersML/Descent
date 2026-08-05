"""Battery am01: does AM inflate PGS R-squared by 1/(1 - r*h2)?

THE CLAIM.  `AssortativeMatingPGS.AssortativeMatingModel.pgsR2AM` says a score
with random-mating accuracy `R2_rm` has accuracy `R2_rm / (1 - r*h2)` in the
same population under assortative mating, and its docstring derives that from
"PGS variance inflates by 1/(1-r*h2) and residual variance stays roughly
constant".  The residual variance does stay constant.  R-squared is not a ratio
to the residual variance, it is a ratio to the TOTAL variance, and the total
moves when the additive part does.

CONVENTIONS, declared before any number is read.
  * `h2` is NARROW-SENSE and RANDOM-MATING: `V_A / V_P` with `V_P = V_A + V_E`
    in the founding generation, which is exactly how the Lean structure
    computes it (`AssortativeMatingModel.h2 = V_A / V_P`, with `V_A` the field
    documented "additive genetic variance under random mating").  It is NOT the
    AM-inflated heritability; that one is `observedH2` in the same file.
  * `r` is the SPOUSAL PHENOTYPIC CORRELATION, the structure's own field
    documentation.  Not a correlation of breeding values, not a
    variance ratio.  The realised value is measured every generation and the
    realised mean is what the prediction is evaluated at.
  * `R2_rm` is the squared correlation between the score and the phenotype in
    the founding random-mating generation -- a SQUARED CORRELATION, not a
    correlation and not a variance ratio, so the alpha-style sd/variance
    ambiguity cannot enter.

THE MODEL SIMULATED.  `m` unlinked biallelic loci at frequency 1/2, fixed
effects `beta`, environmental variance held FIXED across generations (Fisher's
model: assortment redistributes genetic variance into gametic disequilibrium
and does nothing to the environment).  Mates are paired by a Gaussian copula on
phenotype at target correlation `r`; one allele is transmitted per parent per
locus, so every correlation between loci is built by mating rather than by
linkage.  Twelve generations, which is ~0.5% from the geometric equilibrium.

WHY THIS IS NOT AN IDENTITY, and where the arguments come from.  The
prediction's inputs (`R2_rm`, `h2`, `r`) are measured on FOUR replicates and the
oracle on EIGHT DISJOINT ones at the same parameters, so no input is estimated
from the replicates the oracle measures -- `argument_source="model"` is honest
here in the sense the harness means it.  The inputs are read in the founding
generation and in the mating routine; the oracle is the realised squared
score-phenotype correlation TWELVE generations later, in a population whose
gametic phase structure was not present when the inputs were read.  Nothing in
the founding generation forces that later number to be any particular multiple
of `R2_rm`; the multiple is what is on trial.

COMPETITORS, on the same cells:
  * NUMERATOR-ONLY  `R2_rm / (1 - r*h2)` -- the body this battery replaced: the
    additive variance's inflation factor applied to a ratio whose denominator
    also inflates.  At r = 0.5, h2 = 0.8 it returns 1.33, a squared correlation
    above one.
  * INVERTED    `R2_rm * (1 - r*h2)` -- the sign-of-exponent error that
    `amCorrectedPortability` was carrying in this same file.

The corpus row is the repaired body `R2_rm / (1 - r*h2*(1 - h2))`, which is
`R2_rm*I / (1 + h2*(I - 1))` at `I = 1/(1 - r*h2)`: the same inflation factor
applied to the score's covariance AND carried into the denominator.

`observedH2` is recorded from the SAME cells at `frac = 1`, where the score is
the whole breeding value and its squared correlation with the phenotype IS the
observed heritability.  The two definitions share a denominator and this design
measures it once.

CONTROL: at `r = 0` the same code path must reproduce the heritability implied
by the realised allele frequencies and effects, `V_A/(V_A+V_E)`, as the
realised squared score-phenotype correlation after the same twelve generations.
Both sides are measured independently -- one from frequencies and effects, one
from individual-level phenotypes -- and a bug anywhere in transmission,
phenotype construction or the R-squared computation breaks it.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-AM01-KESTREL-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def copula_pair(phen, r, rng):
    """Pair the population into couples with phenotypic correlation ~r.

    Rank-normalise the phenotype, draw a correlated latent for the partner, and
    match on rank.  At r = 0 this is a uniform random pairing.
    """
    n = len(phen)
    half = n // 2
    idx = rng.permutation(n)
    a, b = idx[:half], idx[half:2 * half]
    # inverse-normal scores within each mating pool
    def rankit(x):
        o = np.argsort(np.argsort(x))
        return _norm_ppf((o + 0.5) / len(x))
    xa = rankit(phen[a])
    target = r * xa + math.sqrt(max(0.0, 1 - r * r)) * rng.normal(size=half)
    # sort pool b by its own score, then assign by rank of `target`
    xb_order = np.argsort(phen[b])
    b_sorted = b[xb_order]
    slot = np.argsort(np.argsort(target))
    return a, b_sorted[slot]


def _norm_ppf(u):
    """Acklam's inverse normal CDF, vectorised (no scipy dependency)."""
    a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
    b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01]
    c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
    d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
         3.754408661907416e+00]
    u = np.asarray(u, dtype=float)
    out = np.empty_like(u)
    lo, hi = u < 0.02425, u > 1 - 0.02425
    mid = ~(lo | hi)
    q = np.sqrt(-2 * np.log(u[lo]))
    out[lo] = (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
              ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    q = np.sqrt(-2 * np.log(1 - u[hi]))
    out[hi] = -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
               ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    q = u[mid] - 0.5
    rr = q * q
    out[mid] = (((((a[0]*rr+a[1])*rr+a[2])*rr+a[3])*rr+a[4])*rr+a[5])*q / \
               (((((b[0]*rr+b[1])*rr+b[2])*rr+b[3])*rr+b[4])*rr+1)
    return out


def run_one(r, h2, gens, n, m, seed, frac=1.0, arm="A"):
    """One AM population.  Returns realised inputs and the realised AM R2.

    `frac` is the fraction of causal loci the score uses, so `R2_rm` can be
    pushed away from `h2` and the body is exercised at `R2_rm != h2`.

    `arm` selects which of the two readings of the module is simulated.

      "A"  THE MODULE'S OWN DECLARED MODEL.  `amVarianceStep` holds the
           transmission coefficient at its random-mating value `r*h2` --
           "the standard Fisher (1918) linearisation; letting h2 track the
           inflating variance gives a different, slowly-converging recursion",
           in that definition's words.  So mates are paired on BREEDING VALUE at
           correlation `r*h2`, which makes `Cov(A_m, A_f) = r*h2*V` exactly, the
           recursion the module derives its equilibrium from.  This is the arm
           that puts the R-squared step alone on trial: the variance law is the
           module's own and is separately pinned by
           `amEquilibriumVariance_isFixedPoint`.

      "P"  THE LITERAL FIELD READING: mates paired on PHENOTYPE at correlation
           `r`, so the transmission coefficient tracks the inflating
           heritability.  The equilibrium variance is then about 6% above the
           linearised one, and the arm is reported rather than recorded --
           mixing it with arm A would compare a body against a model its own
           module disowns.
    """
    rng = np.random.default_rng(seed)
    beta = rng.normal(size=m)
    beta /= math.sqrt(float((beta ** 2).sum()))
    used = np.zeros(m, dtype=bool)
    used[: max(1, int(round(frac * m)))] = True
    w = beta * used

    g = rng.binomial(2, 0.5, (n, m)).astype(float)
    gv = g @ beta
    V_E = float(gv.var()) * (1 - h2) / h2       # FIXED for the whole run
    sd_e = math.sqrt(V_E)

    phen0 = gv + rng.normal(0, sd_e, n)
    score0 = g @ w
    r2_rm = float(np.corrcoef(score0, phen0)[0, 1] ** 2)
    h2_real = float(gv.var() / phen0.var())

    spousal = []
    for _ in range(gens):
        gv = g @ beta
        phen = gv + rng.normal(0, sd_e, n)
        if arm == "A":
            # pair on breeding value at correlation r*h2: the module's own
            # transmission coefficient, held at its random-mating value
            dad, mom = copula_pair(gv, r * h2, rng)
            spousal.append(float(np.corrcoef(gv[dad], gv[mom])[0, 1]))
        else:
            dad, mom = copula_pair(phen, r, rng)
            spousal.append(float(np.corrcoef(phen[dad], phen[mom])[0, 1]))
        a1 = rng.binomial(1, g[dad] / 2.0)
        a2 = rng.binomial(1, g[mom] / 2.0)
        kids = (a1 + a2).astype(float)
        g = np.repeat(kids, 2, axis=0)[:n]

    gv = g @ beta
    phen = gv + rng.normal(0, sd_e, n)
    score = g @ w
    r2_am = float(np.corrcoef(score, phen)[0, 1] ** 2)
    p = g.mean(0) / 2.0
    v_a_freq = float((beta ** 2 * 2 * p * (1 - p)).sum())
    return dict(r2_rm=r2_rm, h2=h2_real, r_real=float(np.mean(spousal)),
                r2_am=r2_am, h2_from_freq=v_a_freq / (v_a_freq + V_E),
                pbar=float(p.mean()))


def cell(r, h2, reps, gens=12, n=8000, m=120, frac=1.0, seed0=0, arm="A"):
    outs = [run_one(r, h2, gens, n, m, seed0 + 977 * i, frac, arm)
            for i in range(reps)]
    agg = {k: np.array([o[k] for o in outs]) for k in outs[0]}
    return agg


def split_cell(r, h2, n_cal, n_test, **kw):
    """Inputs from one set of replicates, oracle from a DISJOINT set.

    This is what keeps `argument_source="model"` honest here: `R2_rm`, `h2` and
    the realised spousal `r` are never read off the replicates whose
    generation-12 R-squared the prediction is compared against.
    """
    seed_cal = kw.pop("seed_cal")
    seed_test = kw.pop("seed_test")
    return (cell(r, h2, n_cal, seed0=seed_cal, **kw),
            cell(r, h2, n_test, seed0=seed_test, **kw))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-AM01-KESTREL-20260804")
    reps = 8
    body, inv, num, h2obs, h2obs_num = [], [], [], [], []
    control = None

    designs = ((0.3, 0.5, 1.0), (0.5, 0.5, 1.0), (0.3, 0.8, 1.0),
               (0.5, 0.8, 1.0), (0.5, 0.5, 0.5))
    for r, h2, frac in designs:
        base = int(1000 * r + 100 * h2 + 7)
        cal, agg = split_cell(r, h2, 4, reps, frac=frac, arm="A",
                              seed_cal=base, seed_test=base + 500003)
        h2_hat = float(cal["h2"].mean())
        # arm A pairs on breeding value, so the realised spousal statistic IS
        # the transmission coefficient r*h2; the model's r is that over h2
        r_hat = float(cal["r_real"].mean()) / h2_hat
        R = float(cal["r2_rm"].mean())
        truth = float(agg["r2_am"].mean())
        sem = float(agg["r2_am"].std(ddof=1) / math.sqrt(reps))
        k = 1 - r_hat * h2_hat
        q = 1 - r_hat * h2_hat * (1 - h2_hat)
        lab = "r=%.1f h2=%.1f frac=%.1f (r^=%.3f h2^=%.3f R2rm=%.3f)" % (
            r, h2, frac, r_hat, h2_hat, R)
        print("  %-58s  body %.5f  num-only %.5f  inverted %.5f  "
              "measured %.5f ± %.5f" % (lab, R / q, R / k, R * k, truth, sem))
        body.append(dict(design=lab, lean=R / q, truth=truth, sem=sem))
        num.append(dict(design=lab, lean=R / k, truth=truth, sem=sem))
        inv.append(dict(design=lab, lean=R * k, truth=truth, sem=sem))
        if frac == 1.0:
            # the score is the whole breeding value, so the measured R2 is the
            # AM-observed heritability itself
            h2obs.append(dict(design=lab, lean=h2_hat / q, truth=truth,
                              sem=sem))
            h2obs_num.append(dict(design=lab, lean=h2_hat / k, truth=truth,
                                  sem=sem))

    # ---- the literal-phenotypic arm, REPORTED and not recorded -------------
    print("\n  arm P (mates paired on PHENOTYPE at correlation r, so the "
          "transmission coefficient tracks the inflating heritability -- the "
          "reading this module's amVarianceStep disowns):")
    for r, h2 in ((0.3, 0.5), (0.5, 0.5), (0.5, 0.8)):
        base = int(1000 * r + 100 * h2 + 7)
        calP, aggP = split_cell(r, h2, 4, reps, arm="P",
                                seed_cal=base + 11, seed_test=base + 500011)
        rP, hP, RP = (float(calP["r_real"].mean()), float(calP["h2"].mean()),
                      float(calP["r2_rm"].mean()))
        qP, kP = 1 - rP * hP * (1 - hP), 1 - rP * hP
        print("    r=%.1f h2=%.1f (r^=%.3f h2^=%.3f): body %.5f  num-only %.5f "
              " measured %.5f ± %.5f"
              % (r, h2, rP, hP, RP / qP, RP / kP,
                 float(aggP["r2_am"].mean()),
                 float(aggP["r2_am"].std(ddof=1) / math.sqrt(reps))))

    # ---- control: r = 0, the same code path, twelve generations -------------
    agg = cell(0.0, 0.5, reps, seed0=31337)
    control = dict(design="r=0: realised R2 after 12 generations equals "
                          "V_A/(V_A+V_E) from the realised frequencies",
                   lean=float(agg["h2_from_freq"].mean()),
                   truth=float(agg["r2_am"].mean()),
                   sem=float(agg["r2_am"].std(ddof=1) / math.sqrt(reps)))
    print("\n  CONTROL %s: predicted %.5f measured %.5f ± %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    print("  (mean allele frequency after the control run: %.5f)"
          % agg["pbar"].mean())

    reg = ("Fisher assortative mating in the linearisation this module "
           "declares: environmental variance held FIXED, mates paired by "
           "Gaussian copula on BREEDING VALUE at the transmission coefficient "
           "r*h2 that amVarianceStep holds at its random-mating value; 120 "
           "unlinked loci at p=1/2, 8000 individuals, 12 generations, one "
           "allele transmitted per parent per locus. h2 is NARROW-SENSE at "
           "RANDOM MATING (V_A/V_P in the founding generation); r is the "
           "REALISED transmission coefficient over the REALISED h2, never "
           "nominal. The oracle is the realised squared score-phenotype "
           "correlation in generation 12")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")

    record("pgsR2AM", "AssortativeMatingPGS.lean",
           "R2_rm / (1 - r * h2 * (1 - h2))", body, **MODEL)
    record("pgsR2AM [numerator-inflation only, the previous body, competing]",
           "AssortativeMatingPGS.lean", "R2_rm / (1 - r * h2)", num, **MODEL)
    record("pgsR2AM [inverted factor, competing]", "AssortativeMatingPGS.lean",
           "R2_rm * (1 - r * h2)", inv, **MODEL)
    record("observedH2", "AssortativeMatingPGS.lean",
           "h2 / (1 - r * h2 * (1 - h2))", h2obs, **MODEL)
    record("observedH2 [numerator-inflation only, the previous body, competing]",
           "AssortativeMatingPGS.lean", "h2 / (1 - r * h2)", h2obs_num, **MODEL)

    dump_results("battery_am01_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-24s %-58s worst %9.2f sems, %8.2f%% rel"
              % (rec["verdict"], rec["name"][:58], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
