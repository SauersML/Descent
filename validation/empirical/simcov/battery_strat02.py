"""Battery strat02: the stratification RISK COEFFICIENT itself, at last.

WHAT `battery_strat01` DECLINED TO DO, AND WHY THIS DOES IT.  `strat01` tested
`standardizedResidualPGSBias`'s proportionality in the confounding magnitude and
recorded no verdict on the coefficient it multiplies:

    pgsStratificationRiskCoefficient L Sbar H' sigma_beta Phi Lambda
      = sqrt(L * Sbar) * sqrt(H') / sigma_beta * ascertainmentAmplification Phi Lambda

Its reason was that the corpus does not say what the score is standardized by, so
"under a coherent sum over ascertained variants the exponent on `L` is 1 and
under a root-mean-square over the loading geometry it is 1/2, and any oracle I
write for it would be testing my reconstruction rather than the definition".
That is a real ambiguity and it is not a reason to leave the body unmeasured
forever, because the ambiguity is resolvable: the two readings are DIFFERENT
FUNCTIONS of quantities a simulation can measure, so a design in which they
disagree decides between them.  This battery pins the reading, states the
pinning where a reader can reject it, and then runs BOTH readings as rivals on
the same cells.

THE READING, pinned here.  Write the GWAS panel's ancestry axis `a` and the
target panel's residual ancestry axis `a'`, both standardized, and let
`r_l = Cor(a, g_l)` and `rho_l = Cor(a', g_l)` over the ASCERTAINED variants.
Under a confounded null with no causal variant, the marginal estimate is
`beta_l = c * Cov(g_l, a) / Var(g_l)` up to noise, so the slope of the score on
the target's axis is

    slope = c * sum_l r_l * rho_l * (sd(g'_l) / sd(g_l))       (*)

and with matched panels the variance ratio is 1.  Cauchy-Schwarz bounds (*) by
`c * sqrt(sum r_l^2) * sqrt(sum rho_l^2)`, with EQUALITY exactly when the two
loading vectors are proportional.  So the corpus body is that bound with

    L * Sbar := sum over the ascertained set of r_l^2      (GWAS susceptibility)
    H'       := sum over the ascertained set of rho_l^2    (residual, in target)

which makes `Sbar` the mean squared ancestry correlation over the `L` variants
that were ascertained -- the reading under which `L * Sbar` is a susceptibility
and not a count, and the one that makes `sqrt` of it dimensionally the same kind
of object as `sqrt(H')`.  UNDER THIS READING THE BODY IS AN EQUALITY IN THE
ALIGNED REGIME AND AN UPPER BOUND OUTSIDE IT, and both halves are tested.

WHY THIS IS NOT A SELF-TEST.  The prediction's two inputs are measured on
REFERENCE PANELS drawn independently of the GWAS panel that ascertains and of
the target panel the oracle regresses on.  Nothing the oracle measures enters
the prediction; the shared object is the population (`p0`, `u`), which is the
model.  The prediction is a product of two sums of squared correlations, the
oracle is one regression slope of a constructed score, and they agree only if
(*) is right and the loading vectors are proportional.

THE DESIGN MAKES `H` AND `H'` SEPARATE, which is the whole discrimination, and
it does so through the LOADINGS and not through the axis.  The target panel's
ancestry gradient is `u' = rho*u + sqrt(1 - rho^2)*u_perp`: the same population
allele frequencies, a gradient partly along the GWAS panel's and partly along an
independent direction.  Then `sum_l r_l * rho_l` falls off as `rho` while
`sqrt(H)*sqrt(H')` does not, so the cells walk the Cauchy-Schwarz inequality
from its equality case out to a factor of two, and each rival below separates
somewhere on that walk.

THE DESIGN THAT WAS TRIED FIRST AND DISCARDED, recorded because it looked like
it worked.  The residual axis was represented by drawing the target panel's
ancestry axis with a SMALLER standard deviation, on the reasoning that
correcting on principal components leaves less of the axis.  Every cell came
back FALSIFIED at up to 62 sems and the numbers were self-consistent, and the
design was measuring nothing: with `p = p0 + a*u`, the regression of genotype on
a STANDARDIZED axis is `2*u_l` whatever the axis's variance is, so the oracle --
a slope on that standardized axis -- cannot move.  Shrinking the variance moved
`H'`, which is a correlation, and left the observable exactly where it was; the
measured bias came back equal to `L*Sbar` alone to within 1.8% across the sweep
because that is algebraically what it had to be.  A design whose predicted side
moves and whose measured side cannot is not a weak test, it is not a test, and
it reads identically to a strong one.  Misalignment moves both.

TWO ARMS, and the corpus row is the first.
  ARM E -- `rho = 1`, the aligned regime, where the body's Cauchy-Schwarz form
    is an EQUALITY and it is therefore making its strongest claim.  The cells
    move `L*Sbar` by the ascertainment threshold and the loading scale, and move
    `H'` AWAY FROM IT by the target loading scale `k`, which shrinks the target's
    gradient without turning it.  So the arm holds the inequality tight while
    breaking `H' = L*Sbar`, and that is what gives it power against the two
    rivals which are only distinguishable when the susceptibilities differ.
    THIS IS THE RECORDED CORPUS ROW.
  ARM M -- `rho < 1`.  Here the body is an upper bound and the measurement says
    by how much it is missed.  Recorded separately and under its own name,
    because a bound reported as an equality is a different claim from a bound.

RIVALS, all on ARM E's cells and the same oracle:
  * exponent 1 on the GWAS side: `(L*Sbar) * sqrt(H')`, which is `strat01`'s
    "coherent sum" reading and the specific ambiguity it named;
  * exponent 1 on the residual side: `sqrt(L*Sbar) * H'`;
  * the arithmetic mean `(L*Sbar + H')/2` in place of the geometric one, which
    is the closest possible rival: it agrees to second order when the two are
    near and separates as they part;
  * the residual susceptibility alone, `H'`, which drops the GWAS side.

CONTROL, independent of every body under test: the same pipeline and the same
code path with the confounder switched off and a real additive effect of known
size put in instead.  The mean marginal estimate must recover it.  It fails on
any error in the genotype draw, the marginal regression or the standardization,
and it cannot be satisfied by any choice of exponent.

WHAT IS NOT TESTED, said plainly.  `ascertainmentAmplification Phi Lambda` is
held at `Phi = Lambda = 0`, where it is 1.  The corpus defines neither `Phi` nor
`Lambda` operationally -- there is no rule here for computing them from an
ascertainment scheme -- so a simulation that assigned them values would be
measuring the assignment.  This battery therefore measures the body at the point
where that factor is the identity, which is the whole of the body that is
identified, and says so rather than quietly folding an untested factor into a
verdict.  `sigma_beta` is a fixed design constant that divides every cell of
both the prediction and the oracle, so no reading of it can create or hide the
effect under test.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-STRAT02-AVOCET-20260806"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


SIGMA_BETA = 0.02          # fixed design constant; divides every cell of both sides


def draw_panel(rng, n, p0, u):
    """Genotypes for `n` individuals with an ancestry gradient at every SNP.

    The axis is standardized in every panel.  What distinguishes the target
    panel is its LOADING vector `u`, not the axis: see the discarded design in
    the module docstring for why the axis's scale is observationally inert here.
    """
    a = rng.normal(0, 1.0, n)
    p = np.clip(p0[None, :] + np.outer(a, u), 0.01, 0.99)
    # Two Bernoulli draws rather than `rng.binomial(2, p)` on an n-by-L array of
    # per-cell probabilities: same distribution, and it is what brought a run
    # from over ten minutes to under two. Nothing here needs a count above 2.
    g = ((rng.random(p.shape) < p).astype(np.float64)
         + (rng.random(p.shape) < p).astype(np.float64))
    return a, g


def tilt(rng, u, rho, scale):
    """A loading vector at cosine `rho` to `u`, at `scale` times its length.

    TWO LEVERS, AND THEY DO DIFFERENT WORK.  `rho` walks the Cauchy-Schwarz
    inequality off its equality case, so it tests whether the body is a bound or
    an identity.  `scale` shrinks the target's gradient WITHOUT turning it,
    which keeps the inequality tight -- so the body still predicts an equality
    -- while separating `H'` from `L*Sbar` by `scale^2`.  That separation is
    what gives the design power against the rivals that agree with the body
    whenever the two susceptibilities coincide, and in the first run of this
    battery it was missing: the arithmetic mean and the residual susceptibility
    alone both came back MATCH on an arm where `H' = L*Sbar` made all three the
    same number.

    It is also the honest picture of what correcting on principal components
    does.  It removes a component of the ancestry gradient and leaves the rest
    pointing where it did; it does not rotate the gradient into a new direction,
    and it does not (see the discarded design above) rescale the axis.
    """
    v = u if rho >= 1.0 else (
        rho * u + math.sqrt(1.0 - rho ** 2)
        * rng.normal(0, float(np.std(u)), len(u)))
    return scale * v


def susceptibility(a, g, idx):
    """`sum_l Cor(a, g_l)^2` over the ascertained set `idx`.

    Zero-variance columns contribute zero rather than a NaN: a monomorphic draw
    carries no ancestry information, and propagating a NaN would silently void
    the whole cell instead of the one variant.
    """
    if len(idx) == 0:
        return 0.0
    gc = g[:, idx] - g[:, idx].mean(0)
    ac = a - a.mean()
    sd = gc.std(0)
    ok = sd > 0
    r = np.zeros(len(idx))
    r[ok] = (gc[:, ok] * ac[:, None]).mean(0) / (sd[ok] * ac.std())
    return float(np.sum(r ** 2))


def marginal_gwas(g, y):
    """Per-variant marginal slope and z, on raw dosage."""
    gc = g - g.mean(0)
    yc = y - y.mean()
    var = (gc * gc).mean(0)
    var = np.where(var <= 0, np.inf, var)
    beta = (gc * yc[:, None]).mean(0) / var
    se = np.sqrt(float(yc.var()) / (len(y) * var))
    return beta, beta / se


def one_rep(rng, n_gwas, n_target, n_ref, L, c, thresh, sigma_u, rho, scale,
            causal_beta=None):
    """One cell replicate.

    Returns `(bias, H, Hprime, n_ascertained, causal_ratio)`, where `bias` is the
    standardized slope of the score on the target's ancestry axis and `H`,
    `Hprime` are measured on panels the oracle never touches.
    """
    p0 = rng.uniform(0.15, 0.5, L)
    u = rng.normal(0, sigma_u, L)
    u_t = tilt(rng, u, rho, scale)

    a, g = draw_panel(rng, n_gwas, p0, u)
    y = c * a + rng.normal(0, 1, n_gwas)
    if causal_beta is not None:
        y = y + (g - g.mean(0)) @ causal_beta
    beta, z = marginal_gwas(g, y)
    picked = np.flatnonzero(np.abs(z) > thresh)

    causal_ratio = None
    if causal_beta is not None:
        j = np.flatnonzero(causal_beta != 0)
        causal_ratio = float(np.mean(beta[j] / causal_beta[j]))

    if len(picked) == 0:
        return 0.0, 0.0, 0.0, 0, causal_ratio

    at, gt = draw_panel(rng, n_target, p0, u_t)
    pgs = gt[:, picked] @ beta[picked]
    slope = float(np.cov(pgs, at)[0, 1] / at.var())

    # The prediction's inputs, on panels DISJOINT from both of the above.
    a_ref, g_ref = draw_panel(rng, n_ref, p0, u)
    at_ref, gt_ref = draw_panel(rng, n_ref, p0, u_t)
    H = susceptibility(a_ref, g_ref, picked)
    Hp = susceptibility(at_ref, gt_ref, picked)

    return slope / SIGMA_BETA, H, Hp, len(picked), causal_ratio


def cell(seed0, reps, c, thresh, sigma_u, rho, scale,
         n_gwas=6000, n_target=6000, n_ref=4000, L=1500):
    """Average a cell over replicates, returning measured and predicted parts."""
    bias, Hs, Hps, hits = [], [], [], []
    for r in range(reps):
        rng = np.random.default_rng(seed0 + 7919 * r)
        b, H, Hp, k, _ = one_rep(rng, n_gwas, n_target, n_ref, L, c, thresh,
                                 sigma_u, rho, scale)
        bias.append(b / c)                 # per unit of confounding
        Hs.append(H)
        Hps.append(Hp)
        hits.append(k)
    return (float(np.mean(bias)),
            float(np.std(bias, ddof=1) / math.sqrt(reps)),
            float(np.mean(Hs)), float(np.mean(Hps)), float(np.mean(hits)))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-STRAT02-AVOCET-20260806")

    # ARM E: aligned. The ascertainment threshold and the loading scale move
    # `L*Sbar` for two independent reasons, so the cells test a functional form
    # and not one number.
    aligned = [
        (0.6, 0.05, 3.0, 1.0, 1.00),
        (0.6, 0.05, 2.5, 1.0, 0.60),
        (0.6, 0.035, 3.0, 1.0, 1.50),
        (0.6, 0.065, 3.5, 1.0, 0.40),
        (0.9, 0.05, 2.5, 1.0, 1.30),
        (0.9, 0.035, 3.5, 1.0, 0.70),
    ]
    # ARM M: the same instrument walked off the equality case.
    misaligned = [
        (0.6, 0.05, 3.0, 0.90, 1.0),
        (0.6, 0.05, 3.0, 0.70, 1.0),
        (0.6, 0.05, 3.0, 0.50, 1.0),
        (0.9, 0.04, 2.5, 0.70, 0.7),
    ]

    def sweep(designs, seed_base, label):
        body, rL, rH, ram, rhp = [], [], [], [], []
        print("\n  %s" % label)
        print("  %-50s %9s %9s %9s %9s" % ("cell", "L*Sbar", "H'", "body",
                                           "measured"))
        for i, (c, sigma_u, thresh, rho, scale) in enumerate(designs):
            mean, sem, H, Hp, hits = cell(seed_base + 1301 * i, 6, c, thresh,
                                          sigma_u, rho, scale)
            lab = ("c=%.2f u=%.3f |z|>%.1f rho=%.2f k=%.2f (%.0f ascertained)"
                   % (c, sigma_u, thresh, rho, scale, hits))
            pred = math.sqrt(H) * math.sqrt(Hp) / SIGMA_BETA
            print("  %-50s %9.3f %9.3f %9.1f %9.1f"
                  % (lab, H, Hp, pred, mean))
            body.append(dict(design=lab, lean=pred, truth=mean, sem=sem))
            rL.append(dict(design=lab, lean=H * math.sqrt(Hp) / SIGMA_BETA,
                           truth=mean, sem=sem))
            rH.append(dict(design=lab, lean=math.sqrt(H) * Hp / SIGMA_BETA,
                           truth=mean, sem=sem))
            ram.append(dict(design=lab, lean=0.5 * (H + Hp) / SIGMA_BETA,
                            truth=mean, sem=sem))
            rhp.append(dict(design=lab, lean=Hp / SIGMA_BETA,
                            truth=mean, sem=sem))
        return body, rL, rH, ram, rhp

    body, rival_L, rival_H, rival_am, rival_hp = sweep(
        aligned, 310_000, "ARM E -- aligned loadings, where the body's "
                          "Cauchy-Schwarz form is an equality")
    bound, _, _, _, _ = sweep(
        misaligned, 720_000, "ARM M -- misaligned loadings, where it is a bound")

    # ---- control: no confounder, a real additive effect of known size ------
    L = 1500
    cb = np.zeros(L)
    cb[:200] = 0.05
    ratios = []
    for r in range(6):
        _, _, _, _, hat = one_rep(np.random.default_rng(90210 + r), 6000, 6000,
                                  2000, L, 0.0, 3.0, 0.05, 1.0, 1.0,
                                  causal_beta=cb)
        ratios.append(hat)
    control = dict(design="no confounder, true additive effects: the mean "
                          "marginal estimate recovers the effect it was given",
                   lean=1.0, truth=float(np.mean(ratios)),
                   sem=float(np.std(ratios, ddof=1) / math.sqrt(len(ratios))))
    print("\n  CONTROL %s: predicted %.4f measured %.4f +/- %.4f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))

    reg = ("confounded null: 1500 candidate variants carrying an ancestry "
           "frequency gradient, 6000 GWAS individuals, 6000 target individuals "
           "and 6000 reference individuals per panel, no variant causal, "
           "phenotype c*a + noise on a standardized ancestry axis. The target "
           "panel carries the ancestry LOADING vector rho*u + sqrt(1-rho^2)*u_perp "
           "against the GWAS panel's u, at the same scale and on the same allele "
           "frequencies, so the residual axis differs in direction rather than in "
           "magnitude; the axis's own variance is observationally inert for this "
           "oracle and misalignment is what separates L*Sbar from H'. "
           "L*Sbar is the sum of squared ancestry "
           "correlations over the ascertained set and H' the same sum in the "
           "target, both measured on reference panels drawn independently of "
           "the GWAS panel that ascertains and of the target panel the oracle "
           "regresses on. The observable is the regression slope of the score "
           "on the target panel's ancestry axis, over sigma_beta and over the "
           "confounding magnitude. Phi = Lambda = 0, where "
           "ascertainmentAmplification is 1: the corpus defines neither "
           "operationally, so that factor is outside this design and is not "
           "folded into the verdict")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="sample")

    record("pgsStratificationRiskCoefficient", "Diagnostic.lean",
           "sqrt(L*Sbar) * sqrt(H') / sigma_beta * ascertainmentAmplification 0 0",
           body, **MODEL)
    record("pgsStratificationRiskCoefficient "
           "[exponent 1 on the GWAS side, competing]", "Diagnostic.lean",
           "(L*Sbar) * sqrt(H') / sigma_beta", rival_L, **MODEL)
    record("pgsStratificationRiskCoefficient "
           "[exponent 1 on the residual side, competing]", "Diagnostic.lean",
           "sqrt(L*Sbar) * H' / sigma_beta", rival_H, **MODEL)
    record("pgsStratificationRiskCoefficient "
           "[arithmetic mean in place of geometric, competing]",
           "Diagnostic.lean", "(L*Sbar + H') / 2 / sigma_beta", rival_am,
           **MODEL)
    record("pgsStratificationRiskCoefficient "
           "[residual susceptibility alone, competing]", "Diagnostic.lean",
           "H' / sigma_beta", rival_hp, **MODEL)
    record("pgsStratificationRiskCoefficient [read as an equality off the "
           "aligned regime]", "Diagnostic.lean",
           "sqrt(L*Sbar) * sqrt(H') / sigma_beta, at rho < 1", bound, **MODEL)

    dump_results("battery_strat02_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-30s %-58s worst %9.2f sems, %8.2f%% rel"
              % (rec["verdict"], rec["name"][:58],
                 w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
