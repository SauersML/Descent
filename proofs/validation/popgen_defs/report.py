"""Tabulate check_defs.py output: Lean definition vs simulated ground truth."""
from __future__ import annotations

import json
import sys
from collections import defaultdict

import numpy as np


def agg(rows, keys, cols):
    g = defaultdict(list)
    for r in rows:
        g[tuple(r[k] for k in keys)].append(r)
    out = []
    for k in sorted(g):
        rec = dict(zip(keys, k))
        for c in cols:
            vals = [r[c] for r in g[k] if r[c] == r[c]]
            rec[c] = float(np.mean(vals)) if vals else float("nan")
        out.append(rec)
    return out


def main(path):
    recs = json.load(open(path))
    by = defaultdict(list)
    for r in recs:
        by[r["check"]].append(r)

    print("=" * 78)
    print("CHECK 1  split Fst:  coalFst t/(t+2Ne)   vs   fstFromDrift 1-(1-1/2Ne)^t")
    print("=" * 78)
    print(f"{'Ne':>6} {'t':>6} {'sim':>9} {'coalFst':>9} {'err%':>7} "
          f"{'fstDrift':>9} {'err%':>7}")
    for r in agg(by["split_fst"], ["Ne", "t"], ["sim", "lean_coalFst", "lean_fstFromDrift"]):
        e1 = 100 * (r["lean_coalFst"] - r["sim"]) / r["sim"]
        e2 = 100 * (r["lean_fstFromDrift"] - r["sim"]) / r["sim"]
        print(f"{r['Ne']:6.0f} {r['t']:6.0f} {r['sim']:9.5f} "
              f"{r['lean_coalFst']:9.5f} {e1:7.1f} {r['lean_fstFromDrift']:9.5f} {e2:7.1f}")

    print("\n" + "=" * 78)
    print("CHECK 2  island model:  islandModelFst = 1/(1+4*Ne*m)")
    print("=" * 78)
    print(f"{'demes':>6} {'Nm':>6} {'sim':>9} {'lean':>9} {'err%':>8} {'sim/lean':>9}")
    for r in agg(by["island_fst"], ["ndemes", "Nm"], ["sim", "lean"]):
        e = 100 * (r["lean"] - r["sim"]) / r["sim"]
        print(f"{r['ndemes']:6.0f} {r['Nm']:6.2f} {r['sim']:9.5f} {r['lean']:9.5f} "
              f"{e:8.1f} {r['sim']/r['lean']:9.3f}")

    print("\n" + "=" * 78)
    print("CHECK 3  singleton proportion:  1 - log N0 / log N1")
    print("=" * 78)
    print(f"{'N0':>8} {'N1':>9} {'nsamp':>6} {'sim':>8} {'lean':>8} "
          f"{'const-size theory':>18}")
    for r in agg(by["singletons"], ["N0", "N1", "nsamp"],
                 ["sim", "lean", "neutral_constant_size"]):
        print(f"{r['N0']:8.0f} {r['N1']:9.0f} {r['nsamp']:6.0f} {r['sim']:8.4f} "
              f"{r['lean']:8.4f} {r['neutral_constant_size']:18.4f}")

    print("\n" + "=" * 78)
    print("CHECK 4  LD decay:  ldAfterGenerations = D0*((1-r)(1-1/2Ne))^t")
    print("=" * 78)
    print(f"{'N':>6} {'r':>7} {'t':>5} {'E[D]/D0':>9} {'E[D^2]/D0^2':>12} "
          f"{'lean':>9} {'(1-r)^t':>9}")
    for r in agg(by["ld_decay"], ["N", "r", "t"],
                 ["sim_ED_ratio", "sim_ED2_ratio",
                  "lean_ldAfterGenerations_ratio", "pure_recombination"]):
        print(f"{r['N']:6.0f} {r['r']:7.4f} {r['t']:5.0f} {r['sim_ED_ratio']:9.4f} "
              f"{r['sim_ED2_ratio']:12.4f} {r['lean_ldAfterGenerations_ratio']:9.4f} "
              f"{r['pure_recombination']:9.4f}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "defs.json")
