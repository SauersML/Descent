"""Compare Experiment A output against the PCCorrectability definitions.

For each replicate we know n, M, the realized Hudson Fst, and the subgroup size.
The Lean model predicts

    s = demographicSpike = KAPPA * F * m (n - m) / n     with KAPPA = 2
    edge = bbpProxyThreshold = sqrt(n / M)               (BBP: detect iff s > edge)
    overlap^2 = (1 - c/s^2) / (1 + c/s)                  c = n / M

We invert the BBP eigenvalue law lam1 = (1+s)(1+c/s) to recover an observed
spike per replicate, and report the implied KAPPA.
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict

import numpy as np


def spike_from_eigenvalue(lam, c):
    """Invert lam = (1+s)(1+c/s) for the larger root; nan below the edge."""
    b = lam - 1 - c
    disc = b * b - 4 * c
    if disc <= 0:
        return np.nan
    return (b + np.sqrt(disc)) / 2


def jp_overlap(s, c):
    if s <= np.sqrt(c):
        return 0.0
    return (1 - c / s**2) / (1 + c / s)


def main(path):
    recs = json.load(open(path))
    by = defaultdict(list)
    for r in recs:
        by[r["slice"]].append(r)

    for sl in ("theta", "bign"):
        rows = by.get(sl)
        if not rows:
            continue
        print(f"\n=== slice {sl}: threshold sweep (Lean claims edge at theta = M F^2 n = 4) ===")
        print(f"{'theta':>7} {'n':>5} {'overlap_obs':>12} {'pred K=2':>9} {'pred K=4':>9} "
              f"{'lam1':>7} {'edge':>6} {'K_hat':>7}")
        groups = defaultdict(list)
        for r in rows:
            th = round(r["M"] * r["F"] ** 2 * r["n"], 3)
            groups[th].append(r)
        for th in sorted(groups):
            g = groups[th]
            n = g[0]["n"]
            c = n / g[0]["M"]
            e = g[0]["eff_size"]
            F = float(np.mean([r["fst_hat"] for r in g]))
            ov = float(np.mean([r["overlap_pc1"] for r in g]))
            lam = float(np.mean([r["lam1"] for r in g]))
            p2 = jp_overlap(2 * F * e, c)
            p4 = jp_overlap(4 * F * e, c)
            s_hat = spike_from_eigenvalue(lam, c)
            k_hat = s_hat / (F * e) if np.isfinite(s_hat) else np.nan
            print(f"{th:7.2f} {n:5d} {ov:12.4f} {p2:9.4f} {p4:9.4f} "
                  f"{lam:7.3f} {(1+np.sqrt(c))**2:6.3f} {k_hat:7.3f}")
        # kappa estimated only well above the edge, where the inversion is stable
        ks = []
        for r in rows:
            c = r["n"] / r["M"]
            th = r["M"] * r["F"] ** 2 * r["n"]
            if th < 8:
                continue
            s_hat = spike_from_eigenvalue(r["lam1"], c)
            if np.isfinite(s_hat):
                ks.append(s_hat / (r["fst_hat"] * r["eff_size"]))
        if ks:
            print(f"  KAPPA from eigenvalue inversion (theta>=8): "
                  f"{np.mean(ks):.4f} +/- {np.std(ks)/np.sqrt(len(ks)):.4f}  (n={len(ks)})")

    if by.get("collapse"):
        print("\n=== slice collapse: does only the product M F^2 n matter? ===")
        print(f"{'theta':>7} {'M':>7} {'overlap_obs':>12} {'pred K=4':>9}")
        g = defaultdict(list)
        for r in by["collapse"]:
            g[(round(r["M"] * r["F"] ** 2 * r["n"], 2), r["M"])].append(r)
        for key in sorted(g):
            rows = g[key]
            c = rows[0]["n"] / rows[0]["M"]
            F = float(np.mean([r["fst_hat"] for r in rows]))
            ov = float(np.mean([r["overlap_pc1"] for r in rows]))
            print(f"{key[0]:7.2f} {key[1]:7d} {ov:12.4f} "
                  f"{jp_overlap(4*F*rows[0]['eff_size'], c):9.4f}")

    if by.get("unbalanced"):
        print("\n=== slice unbalanced: spike proportional to m(n-m)/n, max at m=n/2 ===")
        print(f"{'m':>5} {'eff_size':>9} {'overlap_obs':>12} {'pred K=4':>9} {'s_hat/F':>9}")
        g = defaultdict(list)
        for r in by["unbalanced"]:
            g[r["m"]].append(r)
        for m in sorted(g):
            rows = g[m]
            c = rows[0]["n"] / rows[0]["M"]
            e = rows[0]["eff_size"]
            F = float(np.mean([r["fst_hat"] for r in rows]))
            ov = float(np.mean([r["overlap_pc1"] for r in rows]))
            lam = float(np.mean([r["lam1"] for r in rows]))
            s_hat = spike_from_eigenvalue(lam, c)
            print(f"{m:5d} {e:9.1f} {ov:12.4f} {jp_overlap(4*F*e, c):9.4f} "
                  f"{(s_hat/F if np.isfinite(s_hat) else np.nan):9.1f}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "expA.json")
