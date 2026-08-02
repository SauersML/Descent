"""Drive the SLiM stabilizing-selection model over a parameter grid.

Tests `equilibriumEffectVariance v_mutation s = v_mutation / s`
(SelectionArchitecture.lean), which asserts the equilibrium genetic variance is
LINEAR in the mutational variance.

V_m is proportional to MU and to ALPHA^2, so sweeping MU and ALPHA separately
tells us the true scaling exponents:
    V_g ~ MU^a * ALPHA^b
The Lean form (V_g proportional to V_m) requires a = 1 and b = 2.
House-of-cards predicts a = 1, b = 0.  Lande's Gaussian predicts a = 1/2, b = 1.
"""
from __future__ import annotations

import itertools
import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

import numpy as np

SLIM = os.environ.get("SLIM", "/scratch.global/sauer354/slim/build/slim")
MODEL = os.environ.get("MODEL", "stabilizing.slim")


def run_one(args):
    mu, alpha, vs, N, L, gens, seed = args
    cmd = [SLIM, "-s", str(seed),
           "-d", f"MU={mu}", "-d", f"ALPHA={alpha}", "-d", f"VS={vs}",
           "-d", f"N={N}", "-d", f"L={L}", "-d", f"GENS={gens}", MODEL]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True,
                             timeout=1800).stdout
    except subprocess.TimeoutExpired:
        return None
    m = re.search(r"RESULT (\S+) (\S+) (\S+) (\S+) (\S+) (\S+) (\S+)", out)
    if not m:
        return None
    return dict(mu=float(m.group(1)), alpha=float(m.group(2)),
                vs=float(m.group(3)), N=int(float(m.group(4))),
                vm=float(m.group(5)), vg=float(m.group(6)),
                n_mut=int(float(m.group(7))), seed=seed)


def main():
    N = int(os.environ.get("N", "500"))
    L = int(os.environ.get("L", "2000"))
    gens = int(os.environ.get("GENS", "5000"))
    reps = int(os.environ.get("REPS", "3"))

    mus = [1e-6, 2e-6, 4e-6, 8e-6]
    alphas = [0.05, 0.1, 0.2]
    vss = [1.0, 5.0]

    jobs = []
    for mu, alpha, vs in itertools.product(mus, alphas, vss):
        for r in range(reps):
            jobs.append((mu, alpha, vs, N, L, gens, 1000 + r * 7919
                         + int(mu * 1e8) + int(alpha * 100) + int(vs)))

    with ThreadPoolExecutor(max_workers=int(os.environ.get("NPROC", "24"))) as ex:
        out = [r for r in ex.map(run_one, jobs) if r]

    with open(sys.argv[1] if len(sys.argv) > 1 else "slim.json", "w") as fh:
        json.dump(out, fh)
    if not out:
        print("no SLiM results")
        return

    from collections import defaultdict
    g = defaultdict(list)
    for r in out:
        g[(r["mu"], r["alpha"], r["vs"])].append(r)

    print(f"{len(out)} SLiM runs, N={N}, L={L}, {gens} generations\n")
    print(f"{'MU':>9} {'ALPHA':>6} {'VS':>5} {'V_m':>10} {'V_g obs':>10} "
          f"{'V_g/V_m':>9} {'lean V_m/s':>11}")
    for k in sorted(g):
        rows = g[k]
        vm = np.mean([r["vm"] for r in rows])
        vg = np.mean([r["vg"] for r in rows])
        # the Lean 's' is the strength of stabilizing selection; with fitness
        # exp(-P^2/(2 VS)) the natural scale is s = 1/VS
        lean = vm * k[2]
        print(f"{k[0]:9.1e} {k[1]:6.2f} {k[2]:5.1f} {vm:10.3e} {vg:10.3e} "
              f"{vg/vm:9.2f} {lean:11.3e}")

    # fit log V_g = a log MU + b log ALPHA + c log VS + const
    X, y = [], []
    for r in out:
        X.append([np.log(r["mu"]), np.log(r["alpha"]), np.log(r["vs"]), 1.0])
        y.append(np.log(r["vg"]))
    coef, *_ = np.linalg.lstsq(np.array(X), np.array(y), rcond=None)
    print(f"\nfitted scaling  V_g ~ MU^{coef[0]:.3f} * ALPHA^{coef[1]:.3f} "
          f"* VS^{coef[2]:.3f}")
    print("  Lean V_m/s  requires   MU^1.000 * ALPHA^2.000 * VS^1.000")
    print("  house-of-cards         MU^1.000 * ALPHA^0.000 * VS^1.000")
    print("  Lande Gaussian         MU^0.500 * ALPHA^1.000 * VS^0.500")


if __name__ == "__main__":
    main()
