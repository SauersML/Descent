"""What does battery_bulk7's gwasHeritability design actually measure, and what
is its error bar?

THE ROW. `gwasHeritability = h2_true * avg_r2_tag`, recorded at 7.5 sems and held
as LEAD for want of a positive control. The design draws m = 400 causal variants,
gives each a tag correlated at rho, fits OLS on half of n = 120000 individuals and
scores the predictor out of sample.

TWO THINGS TO SETTLE, IN THIS ORDER.

1. THE BAR. The battery runs ONE draw per cell and asserts
   `sem = captured * sqrt(4/h)`. There are no replicates behind it, so "7.5 sems"
   is 7.5 times a formula. This runs REPS independent draws per cell and reports
   the block sem beside the asserted one.

2. THE ESTIMAND. The body is the POPULATION optimum. The design scores a FITTED
   predictor, and a fitted predictor is attenuated out of sample by its own
   estimation noise, which is a property of the design and not of the body.
   Derived from the design: the population coefficients are `beta* = rho*beta`
   with `Var(tag) = 1` and tags independent, so `R2_pop = ||beta*||^2 / Var(y)`.
   OLS on h samples has `Cov(coef) ~ sigma2/h * I` with
   `sigma2 = (1 - R2_pop) Var(y)`, so out of sample

       E[captured] ~ R2_pop / (1 + m (1 - R2_pop) / (h R2_pop))

   That is the third column. If the measurement tracks it rather than the body,
   the shortfall is the design's estimation noise and the row is bad
   correspondence; if it tracks neither, something else is wrong and this says so
   rather than guessing.

No verdict is emitted. This attributes a disagreement; it does not score a body.
"""
import math

import numpy as np

DESIGNS = ((0.5, 0.9), (0.5, 0.6), (0.8, 0.8))
N, M, REPS = 120000, 400, 8


def one_draw(h2, rho, rng):
    causal = rng.normal(0, 1, (N, M))
    tag = rho * causal + math.sqrt(1 - rho ** 2) * rng.normal(0, 1, (N, M))
    beta = rng.normal(0, math.sqrt(h2 / M), M)
    realised_h2 = float((beta ** 2).sum())
    y = causal @ beta + rng.normal(0, math.sqrt(1 - h2), N)
    h = N // 2
    A1 = tag[:h] - tag[:h].mean(0)
    y1 = y[:h] - y[:h].mean()
    coef, *_ = np.linalg.lstsq(A1, y1, rcond=None)
    A2 = tag[h:] - tag[h:].mean(0)
    pred = A2 @ coef
    y2 = y[h:] - y[h:].mean()
    captured = float(np.cov(pred, y2)[0, 1] ** 2
                     / (np.var(pred) * np.var(y2)) * np.var(y2) / np.var(y))
    return realised_h2, captured, float(np.var(y))


def main():
    h = N // 2
    print("%-16s %11s %11s %11s %11s %11s"
          % ("cell", "measured", "body", "design", "sem(reps)", "sem(asserted)"))
    for h2, rho in DESIGNS:
        rng = np.random.default_rng(16001)
        caps, bodies, designs = [], [], []
        for _ in range(REPS):
            rh2, cap, vy = one_draw(h2, rho, rng)
            r2pop = rh2 * rho ** 2 / vy
            caps.append(cap)
            bodies.append(rh2 * rho ** 2)
            designs.append(r2pop / (1.0 + M * (1.0 - r2pop) / (h * r2pop)))
        cap = float(np.mean(caps))
        sem = float(np.std(caps, ddof=1) / math.sqrt(REPS))
        body = float(np.mean(bodies))
        des = float(np.mean(designs))
        print("%-16s %11.6f %11.6f %11.6f %11.6f %11.6f"
              % ("h2=%.1f rho=%.1f" % (h2, rho), cap, body, des, sem,
                 cap * math.sqrt(4.0 / h)))
        print("%-16s %11s %11.2f %11.2f  (on the block sem)"
              % ("", "sems off:", abs(cap - body) / sem, abs(cap - des) / sem))


if __name__ == "__main__":
    main()
