"""Battery mi01: `effectMutualInformation`, against an estimator that does not
assume the Gaussian family.

WHY A NEW BATTERY RATHER THAN A CELL IN AN OLD ONE. `battery_bulk40.py`
`group_h` already tried this and agreed with the body to SIX DECIMAL PLACES in
every cell, 0.00 sems, which is the signature of an algebraic identity and not
of a measurement. It was one: the oracle FIT A CONDITIONAL GAUSSIAN to the
training sample and scored the held-out log-likelihood gain, so the out-of-sample
mean gain reduces to `(m/2)·log(sigma_marginal^2 / sigma_conditional^2)` and both
variance ratios collapse onto the same sample correlation the prediction is
evaluated at. The oracle was the formula wearing an estimator. That is the
`driftVariance` failure mode one level up -- an argument-source failure, where
the quantity fed in came from the same fit the oracle performs.

THE SYMBOLIC FACT THAT MAKES THE DEFINITION TESTABLE. At a fixed correlation the
Gaussian is the maximum-entropy joint, so it is the MINIMUM-mutual-information
one: `-(m/2)·log(1-rho^2)` is a strict LOWER BOUND on the mutual information of
any dependence at that correlation, with equality only under Gaussian
dependence. So the body carries two separable claims and this battery separates
them:

  EQUALITY UNDER GAUSSIAN DEPENDENCE, which is what the docstring asserts. Cells
      A. Measured against a k-nearest-neighbour estimator that knows nothing
      about Gaussians. Competing readings -- the factor `m` instead of `m/2`,
      and `log(1-rho)` instead of `log(1-rho^2)` -- are carried on the same
      cells.

  STRICT INEQUALITY OTHERWISE, which is the regime condition and is what makes
      the check able to FAIL. Cells B put NON-GAUSSIAN dependence at the SAME
      realised correlation and require the measurement to come out strictly
      ABOVE the body. If the body matched there it would be refuted as a claim
      about mutual information, because no single function of `rho` can be the
      mutual information of every dependence at that `rho`.

THE ESTIMATOR is Kraskov-Stogbauer-Grassberger (2004), estimator 1: for each
point, the Chebyshev distance to its k-th neighbour in the joint plane, then the
counts of neighbours within that distance in each margin separately, combined
through digammas. It uses ranks and neighbour counts only -- no density model,
no Gaussian assumption, nothing fitted -- which is the whole point.

Mutual information is additive over independent coordinate pairs, so the
m-dimensional value is `m` times the one-coordinate value; the estimator is used
in two dimensions where it is reliable rather than in 2m.

CONVENTIONS, stated:
  * `rho` is the REALISED Pearson correlation of the drawn pairs, never the
    nominal parameter that generated them. At m = 400 the nominal is off by
    O(1/sqrt(m)) ~ 5%, which is the size of a spurious verdict.
  * the standard error comes from 8 INDEPENDENT blocks, so `sem_source` is
    genuinely "replicates" and a significance claim is a finding rather than a
    lead.
  * `m` scales both the prediction and the measurement identically, so it is not
    under test here; what is under test is the per-coordinate law.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np
from scipy.spatial import cKDTree
from scipy.special import digamma

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-MI01-KITTIWAKE-20260804"
M_COORDS = 40


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def ksg_mi(x, y, k=4):
    """Kraskov-Stogbauer-Grassberger estimator 1, in nats.

    No density model and nothing fitted: the estimate is built from the
    Chebyshev distance to the k-th joint neighbour and the number of points
    within that distance in each margin. A tiny jitter breaks ties, which
    otherwise make the strict margin counts ambiguous.
    """
    n = len(x)
    rng = np.random.default_rng(0)
    x = x + rng.normal(0, 1e-10, n)
    y = y + rng.normal(0, 1e-10, n)
    pts = np.column_stack([x, y])
    tree = cKDTree(pts)
    # k-th neighbour excluding the point itself, in the max-norm
    eps = tree.query(pts, k=k + 1, p=np.inf)[0][:, k]
    xs = np.sort(x)
    ys = np.sort(y)
    # strict counts: points with |x_j - x_i| < eps_i, excluding i itself
    nx = (np.searchsorted(xs, x + eps, side="left")
          - np.searchsorted(xs, x - eps, side="right"))
    ny = (np.searchsorted(ys, y + eps, side="left")
          - np.searchsorted(ys, y - eps, side="right"))
    return float(digamma(k) - np.mean(digamma(nx) + digamma(ny))
                 + digamma(n))


def blocked_mi(x, y, blocks=8, k=4):
    """(mean MI over independent blocks, sem of that mean)."""
    n = len(x) // blocks
    vals = [ksg_mi(x[b * n:(b + 1) * n], y[b * n:(b + 1) * n], k=k)
            for b in range(blocks)]
    v = np.asarray(vals, dtype=float)
    return float(v.mean()), float(v.std(ddof=1) / math.sqrt(blocks))


def gaussian_pair(rng, rho, n):
    x = rng.normal(0, 1, n)
    y = rho * x + math.sqrt(max(1 - rho ** 2, 0.0)) * rng.normal(0, 1, n)
    return x, y


def mixture_pair(rng, a_lo, a_hi, n):
    """Non-Gaussian dependence: the coupling strength is itself random.

    `y = A x + sqrt(1-A^2) z` with `A` drawn from {a_lo, a_hi} with equal
    probability. Each component is Gaussian, the mixture is not, and the
    Pearson correlation is the mean of the two couplings -- so a Gaussian cell
    can be matched to it at the same realised correlation while carrying
    strictly less dependence.
    """
    A = np.where(rng.random(n) < 0.5, a_lo, a_hi)
    x = rng.normal(0, 1, n)
    y = A * x + np.sqrt(np.maximum(1 - A ** 2, 0.0)) * rng.normal(0, 1, n)
    return x, y


def body(m, rho):
    return -(m / 2.0) * math.log(max(1 - rho ** 2, 1e-300))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-MI01-KITTIWAKE-20260804")
    rng = np.random.default_rng(90210)
    n = 200000
    m = M_COORDS

    # --- calibration of the estimator itself, before it is used as an oracle --
    print("\n=== estimator calibration: KSG against the Gaussian closed form")
    control = None
    for rho in (0.3, 0.5, 0.7, 0.9):
        x, y = gaussian_pair(rng, rho, n)
        rho_hat = float(np.corrcoef(x, y)[0, 1])
        mi, sem = blocked_mi(x, y)
        exact = -0.5 * math.log(1 - rho_hat ** 2)
        print("  rho=%.1f (realised %.4f)  KSG %.5f ± %.5f   exact %.5f   "
              "off %+.2f%%" % (rho, rho_hat, mi, sem, exact,
                               100 * (mi / exact - 1)))
        if abs(rho - 0.5) < 1e-9:
            control = dict(
                design="Gaussian rho=0.50 [KSG against the closed form "
                       "-0.5*log(1-rho^2), one coordinate]",
                lean=exact, truth=mi, sem=sem)

    # --- A. equality under Gaussian dependence ------------------------------
    print("\n=== A. the body against a model-free estimator, Gaussian cells")
    cells, c_double, c_nosq = [], [], []
    for rho in (0.3, 0.5, 0.7, 0.9):
        x, y = gaussian_pair(rng, rho, n)
        rho_hat = float(np.corrcoef(x, y)[0, 1])
        mi, sem = blocked_mi(x, y)
        lab = "Gaussian rho=%.1f (realised %.4f)" % (rho, rho_hat)
        print("  %-38s KSG*m = %.4f ± %.4f | body %.4f"
              % (lab, m * mi, m * sem, body(m, rho_hat)))
        cells.append(dict(design=lab, lean=body(m, rho_hat), truth=m * mi,
                          sem=m * sem))
        c_double.append(dict(design=lab, lean=2 * body(m, rho_hat),
                             truth=m * mi, sem=m * sem))
        c_nosq.append(dict(design=lab,
                           lean=-(m / 2.0) * math.log(max(1 - rho_hat, 1e-300)),
                           truth=m * mi, sem=m * sem))
    reg_a = ("m = %d independent coordinate pairs with Gaussian dependence, "
             "2e5 draws per coordinate; mutual information is additive over "
             "independent pairs so the estimate is m times a two-dimensional "
             "Kraskov-Stogbauer-Grassberger estimate, which uses neighbour "
             "counts only and assumes no density model. rho is the REALISED "
             "Pearson correlation of the drawn pairs. The standard error is "
             "over 8 independent blocks" % m)
    record("effectMutualInformation", "MultiAncestryTheory.lean",
           "-(m/2) * log(1 - rho^2)", cells, regime=reg_a, control=control,
           argument_source="sample", realised_inputs=True)
    record("effectMutualInformation [factor m not m/2, competing]",
           "MultiAncestryTheory.lean", "-m * log(1 - rho^2)", c_double,
           regime=reg_a, control=control, argument_source="sample",
           realised_inputs=True)
    record("effectMutualInformation [rho not squared, competing]",
           "MultiAncestryTheory.lean", "-(m/2) * log(1 - rho)", c_nosq,
           regime=reg_a, control=control, argument_source="sample",
           realised_inputs=True)

    # --- B. strict inequality off the Gaussian family -----------------------
    print("\n=== B. the same body at the same realised rho, NON-Gaussian")
    cells_b = []
    designs = ((0.10, 0.90), (0.45, 0.95), (-0.20, 0.80), (-0.60, 0.60))
    for a_lo, a_hi in designs:
        x, y = mixture_pair(rng, a_lo, a_hi, n)
        rho_hat = float(np.corrcoef(x, y)[0, 1])
        mi, sem = blocked_mi(x, y)
        lab = ("mixture A in {%+.2f, %+.2f} (realised rho %.4f)"
               % (a_lo, a_hi, rho_hat))
        print("  %-46s KSG*m = %.4f ± %.4f | body %.4f | excess %+.1f%%"
              % (lab, m * mi, m * sem, body(m, rho_hat),
                 100 * (m * mi / max(body(m, rho_hat), 1e-12) - 1)))
        cells_b.append(dict(design=lab, lean=body(m, rho_hat), truth=m * mi,
                            sem=m * sem))
    reg_b = ("the same estimator and the same m, but the coupling strength is "
             "itself random -- y = A x + sqrt(1-A^2) z with A drawn from two "
             "values -- so each component is Gaussian and the mixture is not, "
             "while the Pearson correlation is the mean of the two couplings. "
             "The Gaussian is the maximum-entropy joint at fixed correlation "
             "and therefore the minimum-mutual-information one, so the body is "
             "a strict LOWER BOUND here and the measurement must exceed it. "
             "The last cell has A symmetric about zero: the realised "
             "correlation is ~0 and the body predicts NO information, while "
             "the dependence is total")
    record("effectMutualInformation [non-Gaussian dependence at the same "
           "realised rho: the body is a strict lower bound]",
           "MultiAncestryTheory.lean", "-(m/2) * log(1 - rho^2)", cells_b,
           regime=reg_b, control=control, argument_source="sample",
           realised_inputs=True)

    dump_results("battery_mi01_results.json")
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-24s %-64s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:64], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
