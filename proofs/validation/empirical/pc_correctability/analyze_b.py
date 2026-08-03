"""Compare Experiment B (msprime, real LD) against the PCCorrectability model.

The Lean threshold model takes `M` = effectively independent markers as an input
and does not supply the bridge from a dependent genotype matrix.  Here we ask
which marker count makes the model true:

    M_raw  - SNPs actually used
    M_thin - SNPs thinned to one per 20 kb
    M_eff  - moment-matched from the noise bulk, where Var(bulk) = n / M

using the empirically corrected spike constant KAPPA = 4 from Experiment A.
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict

import numpy as np

KAPPA = 4.0


def jp_overlap(s, c):
    return 0.0 if s <= np.sqrt(c) else (1 - c / s**2) / (1 + c / s)


def main(path):
    recs = json.load(open(path))
    g = defaultdict(list)
    for r in recs:
        g[r["split_gens"]].append(r)

    print("Experiment B: two-deme coalescent, n=%d, %s Mb, %d SNPs\n"
          % (recs[0]["n"], recs[0]["length"] / 1e6, recs[0]["full"]["M"]))
    print(f"{'split':>6} {'Fst':>9} {'M_raw':>7} {'M_eff':>7} {'ratio':>6} "
          f"{'ov_obs':>8} {'pred(M_raw)':>12} {'pred(M_eff)':>12} {'ov_thin':>8}")
    for split in sorted(g):
        rows = g[split]
        n = rows[0]["n"]
        e = rows[0]["eff_size"]
        F = float(np.mean([r["fst_hat"] for r in rows]))
        s = KAPPA * F * e
        M_raw = float(np.mean([r["full"]["M"] for r in rows]))
        M_eff = float(np.mean([r["full"]["M_eff"] for r in rows]))
        ov = float(np.mean([r["full"]["overlap_pc1"] for r in rows]))
        ov_t = float(np.mean([r["thinned"]["overlap_pc1"] for r in rows]))
        print(f"{split:6d} {F:9.5f} {M_raw:7.0f} {M_eff:7.0f} {M_raw/M_eff:6.1f} "
              f"{ov:8.4f} {jp_overlap(s, n/M_raw):12.4f} "
              f"{jp_overlap(s, n/M_eff):12.4f} {ov_t:8.4f}")

    # scoreboard: which marker count reproduces the observed overlap?
    err_raw, err_eff = [], []
    for r in recs:
        n, e = r["n"], r["eff_size"]
        s = KAPPA * r["fst_hat"] * e
        err_raw.append(jp_overlap(s, n / r["full"]["M"]) - r["full"]["overlap_pc1"])
        err_eff.append(jp_overlap(s, n / r["full"]["M_eff"]) - r["full"]["overlap_pc1"])
    print(f"\nmean |error| using M_raw: {np.mean(np.abs(err_raw)):.4f} "
          f"(bias {np.mean(err_raw):+.4f})")
    print(f"mean |error| using M_eff: {np.mean(np.abs(err_eff)):.4f} "
          f"(bias {np.mean(err_eff):+.4f})")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "expB.json")
