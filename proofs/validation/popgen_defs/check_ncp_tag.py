"""Does discoveryNCP use the tag's or the causal variant's genotype variance?

  GeneticArchitectureDiscovery.lean:51
      discoveryNCP n beta maf ld = n * beta^2 * ld^2 * (2*maf*(1-maf))
  with tagGenotypeVariance documented as the TAG's genotype variance.

Theory: the tag's marginal effect is beta_tag = beta * r * sigma_c / sigma_t, so
the noncentrality at the tag is

    n * beta_tag^2 * sigma_t^2 / sigma_e^2 = n * beta^2 * r^2 * sigma_c^2

i.e. it carries the CAUSAL variant's genotype variance; the tag's variance
cancels.  The two agree only when the tag and the causal variant have the same
MAF, so this simulates them at deliberately different MAFs.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402


def lean_discoveryNCP(n, beta, maf_tag, ld):
    return n * beta**2 * ld**2 * (2 * maf_tag * (1 - maf_tag))


def theory_discoveryNCP(n, beta, maf_causal, ld):
    return n * beta**2 * ld**2 * (2 * maf_causal * (1 - maf_causal))


def one(args):
    n_dip, p_c, p_t, r_target, beta, reps, seed = args
    rng = np.random.default_rng(seed)
    # haplotype frequencies for the (causal, tag) pair with correlation r
    D = r_target * np.sqrt(p_c * (1 - p_c) * p_t * (1 - p_t))
    f11 = p_c * p_t + D
    f10 = p_c * (1 - p_t) - D
    f01 = (1 - p_c) * p_t - D
    f00 = (1 - p_c) * (1 - p_t) + D
    f = np.array([f11, f10, f01, f00])
    if np.any(f < -1e-12):
        return None
    f = np.clip(f, 0, None)
    f /= f.sum()

    chi2s = []
    r2s = []
    for _ in range(reps):
        idx = rng.choice(4, size=2 * n_dip, p=f)
        hc = np.isin(idx, [0, 1]).astype(float)
        ht = np.isin(idx, [0, 2]).astype(float)
        gc = hc[0::2] + hc[1::2]
        gt = ht[0::2] + ht[1::2]
        y = beta * gc + rng.standard_normal(n_dip)
        gt_c = gt - gt.mean()
        y_c = y - y.mean()
        sxx = (gt_c * gt_c).sum()
        if sxx <= 0:
            continue
        b = (gt_c * y_c).sum() / sxx
        resid = y_c - b * gt_c
        s2 = (resid**2).sum() / (n_dip - 2)
        chi2s.append(b**2 / (s2 / sxx))
        r2s.append(np.corrcoef(gc, gt)[0, 1] ** 2)

    obs_ncp = float(np.mean(chi2s) - 1)
    r2_hat = float(np.mean(r2s))
    ld = float(np.sqrt(r2_hat))
    return dict(n=n_dip, p_causal=p_c, p_tag=p_t, r=ld, beta=beta,
                obs_ncp=obs_ncp,
                lean=lean_discoveryNCP(n_dip, beta, p_t, ld),
                theory=theory_discoveryNCP(n_dip, beta, p_c, ld))


def main():
    jobs = []
    # causal common, tag rarer, and the reverse
    for p_c, p_t in [(0.5, 0.25), (0.5, 0.35), (0.25, 0.5), (0.35, 0.5), (0.4, 0.4)]:
        jobs.append((4000, p_c, p_t, 0.5, 0.15, 3000, 21 + int(p_c * 100) + int(p_t * 10)))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "8"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    out = [o for o in out if o]
    with open(sys.argv[1] if len(sys.argv) > 1 else "ncptag.json", "w") as fh:
        json.dump(out, fh)

    print("NCP at a tag SNP: does it carry the tag's or the causal variance?\n")
    print(f"{'p_causal':>9} {'p_tag':>7} {'r':>6} {'observed NCP':>13} "
          f"{'lean (tag var)':>15} {'theory (causal var)':>20}")
    for r in out:
        print(f"{r['p_causal']:9.2f} {r['p_tag']:7.2f} {r['r']:6.3f} "
              f"{r['obs_ncp']:13.4f} {r['lean']:15.4f} {r['theory']:20.4f}")


if __name__ == "__main__":
    main()
