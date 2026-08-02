"""Var_Delta_Mu V_A fst = 2 * fst * V_A      PortabilityDrift.lean:276
   Expected_Abs_Shift V_A fS fT = sqrt(Var_Delta_Mu V_A (fS+fT)) * sqrt(2/pi)

This is the core drift model of PortabilityDrift: the variance of the
between-population difference in mean PGS, induced by allele-frequency drift at
fixed effect sizes.

Analytically, with V_A = sum beta_i^2 * 2 p_i (1-p_i) and one branch drifting by
fst,  Var(delta mu) = sum 4 beta_i^2 * fst * p(1-p) = 2 * fst * V_A, which is
the definition.  For two independently drifting branches the drift variances add,
which is why Expected_Abs_Shift passes fS + fT.

Ground truth: draw ancestral frequencies, drift each branch under the
Balding-Nichols model with the stated fst, and measure the variance of the mean
PGS difference across many independent genome replicates.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402


def one(args):
    M, fstS, fstT, reps, seed = args
    rng = np.random.default_rng(seed)
    p = rng.uniform(0.05, 0.95, size=M)
    beta = rng.standard_normal(M)
    V_A = float(np.sum(beta**2 * 2 * p * (1 - p)))

    deltas = np.empty(reps)
    for r in range(reps):
        # Balding-Nichols drift on each branch, independently
        aS = p * (1 - fstS) / fstS
        bS = (1 - p) * (1 - fstS) / fstS
        pS = rng.beta(aS, bS)
        aT = p * (1 - fstT) / fstT
        bT = (1 - p) * (1 - fstT) / fstT
        pT = rng.beta(aT, bT)
        # mean PGS in each population, at FIXED effect sizes
        muS = float(np.sum(beta * 2 * pS))
        muT = float(np.sum(beta * 2 * pT))
        deltas[r] = muT - muS

    obs_var = float(deltas.var())
    obs_absmean = float(np.abs(deltas).mean())
    lean_var_onebranch = 2 * fstS * V_A
    lean_var_two = 2 * (fstS + fstT) * V_A
    lean_abs = np.sqrt(lean_var_two) * np.sqrt(2 / np.pi)
    return dict(M=M, fstS=fstS, fstT=fstT, V_A=V_A,
                obs_var=obs_var, lean_var_two=lean_var_two,
                lean_var_onebranch=lean_var_onebranch,
                obs_absmean=obs_absmean, lean_abs=lean_abs)


def main():
    jobs = []
    for M in (2000,):
        for fstS, fstT in [(0.01, 0.01), (0.05, 0.05), (0.1, 0.1),
                           (0.02, 0.08), (0.15, 0.05)]:
            jobs.append((M, fstS, fstT, 4000, 11 + int(fstS * 1000) + int(fstT * 100)))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "10"))) as ex:
        out = [f.result() for f in [ex.submit(one, a) for a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "vdm.json", "w") as fh:
        json.dump(out, fh)

    print("=== Var_Delta_Mu: variance of the between-population mean PGS shift ===")
    print(f"{'fstS':>6} {'fstT':>6} {'V_A':>10} {'obs Var':>12} "
          f"{'lean 2(fS+fT)V_A':>18} {'err%':>7}")
    for r in out:
        print(f"{r['fstS']:6.2f} {r['fstT']:6.2f} {r['V_A']:10.1f} "
              f"{r['obs_var']:12.1f} {r['lean_var_two']:18.1f} "
              f"{100*(r['lean_var_two']-r['obs_var'])/r['obs_var']:7.1f}")

    print("\n=== Expected_Abs_Shift = sqrt(Var) * sqrt(2/pi) ===")
    print(f"{'fstS':>6} {'fstT':>6} {'obs E|shift|':>13} {'lean':>10} {'err%':>7}")
    for r in out:
        print(f"{r['fstS']:6.2f} {r['fstT']:6.2f} {r['obs_absmean']:13.2f} "
              f"{r['lean_abs']:10.2f} "
              f"{100*(r['lean_abs']-r['obs_absmean'])/r['obs_absmean']:7.1f}")


if __name__ == "__main__":
    main()
