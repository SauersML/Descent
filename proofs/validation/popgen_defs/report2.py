"""Tabulate check_defs2.py output."""
from __future__ import annotations

import json
import sys
from collections import defaultdict

import numpy as np


def main(path):
    recs = json.load(open(path))
    by = defaultdict(list)
    for r in recs:
        by[r["check"]].append(r)

    print("=" * 76)
    print("split Fst (branch-mode):  coalFst t/(t+2Ne)  vs  fstFromDrift")
    print("=" * 76)
    print(f"{'Ne':>6} {'t':>6} {'sim':>9} {'coalFst':>9} {'err%':>7} "
          f"{'fstDrift':>9} {'err%':>7}")
    for r in sorted(by["split_fst"], key=lambda r: (r["Ne"], r["t"])):
        e1 = 100 * (r["lean_coalFst"] - r["sim"]) / r["sim"]
        e2 = 100 * (r["lean_fstFromDrift"] - r["sim"]) / r["sim"]
        print(f"{r['Ne']:6.0f} {r['t']:6.0f} {r['sim']:9.5f} {r['lean_coalFst']:9.5f} "
              f"{e1:7.1f} {r['lean_fstFromDrift']:9.5f} {e2:7.1f}")

    print("\n" + "=" * 76)
    print("island model (total immigration held fixed):  1/(1+4*Ne*m)")
    print("=" * 76)
    print(f"{'demes':>6} {'Nm':>6} {'sim':>9} {'lean':>9} {'err%':>8} "
          f"{'finite-deme':>12} {'err%':>8}")
    for r in sorted(by["island_fst"], key=lambda r: (r["ndemes"], r["Nm"])):
        e1 = 100 * (r["lean"] - r["sim"]) / r["sim"]
        e2 = 100 * (r["finite_deme_theory"] - r["sim"]) / r["sim"]
        print(f"{r['ndemes']:6.0f} {r['Nm']:6.2f} {r['sim']:9.5f} {r['lean']:9.5f} "
              f"{e1:8.1f} {r['finite_deme_theory']:12.5f} {e2:8.1f}")

    print("\n" + "=" * 76)
    print("admixedFst:  Fst(ADM, A) =? (1-alpha)^2 * Fst(A, B)")
    print("=" * 76)
    print(f"{'alpha':>6} {'g':>5} {'Fst(A,B)':>10} {'Fst(ADM,A)':>11} "
          f"{'lean':>10} {'err%':>8}")
    for r in sorted(by["admixture"], key=lambda r: (r["alpha"], r["g"])):
        e = 100 * (r["lean_admixedFst_vs_A"] - r["fst_ADM_A"]) / r["fst_ADM_A"]
        print(f"{r['alpha']:6.2f} {r['g']:5.0f} {r['fst_AB']:10.5f} "
              f"{r['fst_ADM_A']:11.5f} {r['lean_admixedFst_vs_A']:10.5f} {e:8.1f}")

    print("\n" + "=" * 76)
    print("amEquilibriumVariance:  V_A(eq)/V_A(0) =? 1/(1 - r*h2)")
    print("=" * 76)
    print(f"{'r_tgt':>6} {'r_real':>7} {'h2':>5} {'obs ratio':>10} "
          f"{'lean':>9} {'err%':>8}")
    for r in sorted(by["assortative_mating"], key=lambda r: (r["r_target"], r["h2"])):
        e = 100 * (r["lean_ratio"] - r["ratio_obs"]) / r["ratio_obs"]
        print(f"{r['r_target']:6.2f} {r['r_realized']:7.3f} {r['h2']:5.2f} "
              f"{r['ratio_obs']:10.4f} {r['lean_ratio']:9.4f} {e:8.1f}")
    for r in sorted(by["assortative_mating"], key=lambda r: (r["r_target"], r["h2"]))[:2]:
        print(f"   trajectory r={r['r_target']} h2={r['h2']} (every 5 gens): "
              + " ".join(f"{v/r['V_A0']:.3f}" for v in r["traj"]))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "defs2.json")
