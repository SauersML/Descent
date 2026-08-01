"""Round 6.

  PowerAnalysis.lean:483    r2ScalingModel n C = n / (n + C)
  HaplotypeTheory.lean:36   expectedDistinctHaplotypes k n
  HaplotypeTheory.lean:398  phaseAttenuation s = (1 - 2*s)^2
  SampleOverlapBias.lean:208 kinshipInflation r2 K h2_family = r2 + K*h2_family
  StratificationConfounding.lean:436 pgsAttenuationFactor r2 = sqrt r2
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402


def lean_r2ScalingModel(n, C):
    return n / (n + C)


def lean_phaseAttenuation(s):
    return (1 - 2 * s) ** 2


def lean_kinshipInflation(r2, K, h2_family):
    return r2 + K * h2_family


def check_r2_scaling(args):
    """Out-of-sample PGS R^2 vs training n, at fixed h2 and marker count."""
    n_train, n_test, n_snp, h2, reps, seed = args
    rng = np.random.default_rng(seed)
    vals = []
    for _ in range(reps):
        beta = rng.standard_normal(n_snp)
        X = rng.standard_normal((n_train, n_snp))
        g = X @ beta
        g /= g.std()
        y = np.sqrt(h2) * g + np.sqrt(1 - h2) * rng.standard_normal(n_train)
        y -= y.mean()
        bhat = (X.T @ y) / n_train           # marginal effect estimates
        Xt = rng.standard_normal((n_test, n_snp))
        gt = Xt @ beta
        gt /= np.sqrt(n_snp)
        yt = np.sqrt(h2) * (Xt @ beta) / np.sqrt(n_snp) \
            + np.sqrt(1 - h2) * rng.standard_normal(n_test)
        s = Xt @ bhat
        vals.append(float(np.corrcoef(s, yt)[0, 1] ** 2))
    return dict(check="r2Scaling", n_train=n_train, n_snp=n_snp, h2=h2,
                r2_out=float(np.mean(vals)), sd=float(np.std(vals)))


def check_distinct_haplotypes(args):
    """E[number of distinct haplotypes] for n draws over k equally likely types."""
    k, n, reps, seed = args
    rng = np.random.default_rng(seed)
    counts = []
    for _ in range(reps):
        draws = rng.integers(0, k, size=n)
        counts.append(len(np.unique(draws)))
    exact = k * (1 - (1 - 1 / k) ** n)      # standard occupancy expectation
    return dict(check="distinctHaplotypes", k=k, n=n,
                sim=float(np.mean(counts)), occupancy_exact=float(exact))


def check_phase_attenuation(args):
    """Regression attenuation when a fraction s of phase calls are swapped."""
    s, n, reps, seed = args
    rng = np.random.default_rng(seed)
    out = []
    for _ in range(reps):
        # true haplotype-level predictor h in {-1, +1}; observed version has a
        # fraction s of calls flipped
        h = rng.choice([-1.0, 1.0], size=n)
        y = h + rng.normal(0, 1.0, size=n)
        flip = rng.random(n) < s
        hobs = h * np.where(flip, -1.0, 1.0)
        b_true = float(np.cov(h, y)[0, 1] / np.var(h))
        b_obs = float(np.cov(hobs, y)[0, 1] / np.var(hobs))
        out.append(b_obs / b_true)
    ratio = float(np.mean(out))
    return dict(check="phaseAttenuation", s=s, sim_beta_ratio=ratio,
                sim_r2_ratio=ratio**2, lean=lean_phaseAttenuation(s))


def main():
    jobs = []
    for n_train in (500, 1000, 2000, 5000, 10000, 20000, 50000):
        jobs.append((check_r2_scaling, (n_train, 4000, 500, 0.5, 8, 31 + n_train)))
    for k in (10, 50, 200):
        for n in (20, 100, 500):
            jobs.append((check_distinct_haplotypes, (k, n, 4000, 7 + k + n)))
    for s in (0.0, 0.05, 0.1, 0.2, 0.3, 0.5):
        jobs.append((check_phase_attenuation, (s, 200000, 20, 99 + int(s * 100))))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "20"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "b6.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()
