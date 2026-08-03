#!/usr/bin/env python3
"""Summarise block_count_results.json.

Two ratios carry the verdict.

  R_pred  = deviation(m = B*L markers, corr length L) / deviation(B independent
            markers).  The block reduction predicts 1.

  R_infl  = deviation(m = B*L markers, corr length L) / deviation(m independent
            markers).  The Lean file's `berry_esseen_block_bound_eq` predicts
            sqrt(L) for the skew (Berry-Esseen) functional and L for the excess
            kurtosis.
"""
import json
import math
import os
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "block_count_results.json"
D = json.load(open(path))
R = D["results"]


def sel(**kw):
    out = [r for r in R if all(r[k] == v for k, v in kw.items())]
    return sorted(out, key=lambda r: (r["L"], r["B"]))


def f(x, n=3):
    return "  n/a " if x is None else f"{x:{n+4}.{n}f}"


print("=" * 92)
print("META", D["meta"])
print("CALIBRATION (negative-control loadings, matched to copy-arm inflation)")
for k, v in D["calibration"].items():
    print("   ", k, v)

print("\n" + "=" * 92)
print("POSITIVE CONTROL 1 -- L=1 must reproduce the independent panel exactly")
print(f"{'wmode':7} {'arm':12} {'B':>5} {'skew':>9} {'exact':>9} {'R_pred':>8} "
      f"{'+-':>7} {'ks':>8} {'infl':>7}")
for wmode in D["meta"]["wmodes"]:
    for arm in ("indep", "blockconst", "copy"):
        for r in sel(wmode=wmode, arm=arm, L=1):
            print(f"{wmode:7} {arm:12} {r['B']:5d} {f(r['meas']['skew'],4)} "
                  f"{f(r['ref_block']['skew'],4)} {f(r['R_pred_skew'])} "
                  f"{f(r.get('R_pred_skew_se'))} {f(r['meas']['ks'],4)} "
                  f"{f(r['var_inflation'],2)}")

for stat, law in (("skew", "sqrt(L)"), ("exkurt", "L")):
    print("\n" + "=" * 92)
    print(f"MAIN TEST -- functional: {stat}   (R_pred should be 1; "
          f"R_infl should be {law})")
    print(f"{'wmode':7} {'arm':12} {'B':>5} {'L':>4} {'m':>7} {'infl':>7} "
          f"{'R_pred':>8} {'+-':>7} {'R_infl':>8} {'R_infl/law':>11}")
    for wmode in D["meta"]["wmodes"]:
        for arm in ("blockconst", "copy", "copy_global", "latent"):
            rows = sel(wmode=wmode, arm=arm)
            if not rows:
                continue
            for r in rows:
                law_v = math.sqrt(r["L"]) if stat == "skew" else r["L"]
                ri = r[f"R_infl_{stat}"]
                print(f"{wmode:7} {arm:12} {r['B']:5d} {r['L']:4d} {r['m']:7d} "
                      f"{f(r['var_inflation'],2)} {f(r[f'R_pred_{stat}'])} "
                      f"{f(r.get(f'R_pred_{stat}_se'))} {f(ri)} "
                      f"{f(None if ri is None else ri/law_v)}")
            print()

print("\n" + "=" * 92)
print("KS DISTANCE -- R_pred against a SIMULATED independent panel of B markers")
print(f"{'wmode':7} {'arm':12} {'B':>5} {'L':>4} {'ks(m,L)':>9} {'ks(B,ind)':>10} "
      f"{'R_pred_ks':>10} {'+-':>8}")
for wmode in D["meta"]["wmodes"]:
    for arm in ("blockconst", "copy", "copy_global", "latent"):
        for r in sel(wmode=wmode, arm=arm):
            if "ks_ref_block" not in r:
                continue
            print(f"{wmode:7} {arm:12} {r['B']:5d} {r['L']:4d} "
                  f"{f(r['meas']['ks'],4)} {f(r['ks_ref_block']['ks'],4)} "
                  f"{f(r['R_pred_ks'])} {f(r.get('R_pred_ks_se'))}")
        print()

print("\n" + "=" * 92)
print("CLOSED FORM FOR THE SHORTFALL")
print("""
The block reduction says the score behaves like m/L independent BLOCKS.  It does.
What it does not say is that a block behaves like a MARKER.  For the skew (i.e.
Berry-Esseen) functional the discrepancy is exactly the excursion-shape factor

    kappa = E[bw^3] / E[bw^2]^{3/2}      (bw = the weight a block carries)

  * equal-length equal-weight blocks:  bw == L constant  ->  kappa = 1  (exact)
  * geometric block lengths (renewal / recombination), unit marker weights:
        kappa = E[len^3]/E[len^2]^{3/2}  ->  6/2^{3/2} = 2.1213  as L -> inf
  * equal-length blocks, half-normal marker weights: blocks AVERAGE the weights,
        kappa -> (E w^2)^{3/2}/E|w|^3 = 1/1.5958 = 0.6267
  * both at once: the product.

So the Lean file's "exactly sqrt(L)" is "kappa * sqrt(L)".
""")
print(f"{'L':>4} {'kappa (geometric, closed form)':>32} "
      f"{'measured copy/unit R_pred_skew':>34}")
for L in D["meta"]["Ls"]:
    if L == 1:
        continue
    p = 1.0 / L
    e2 = (2 - p) / p ** 2
    e3 = (p * p - 6 * p + 6) / p ** 3
    got = [round(r["R_pred_skew"], 3)
           for r in sel(arm="copy", wmode="unit", L=L)]
    print(f"{L:4d} {e3 / e2 ** 1.5:32.4f}   {str(got):>32}")
print(f"{'':4} {6 / 2 ** 1.5:32.4f}   (L -> infinity)")

print("\n" + "=" * 92)
print("VERDICT TABLE -- |R_pred_skew - 1| in units of its own standard error")
print("(<2 = consistent with the block reduction; >5 = refuted at that setting)")
print(f"{'wmode':7} {'arm':12} {'B':>5} " +
      " ".join(f"{'L=' + str(L):>9}" for L in D["meta"]["Ls"]))
for wmode in D["meta"]["wmodes"]:
    for arm in ("blockconst", "copy", "copy_global", "latent"):
        for B in D["meta"]["Bs"]:
            rows = sel(wmode=wmode, arm=arm, B=B)
            if not rows:
                continue
            cells = {}
            for r in rows:
                v, se = r["R_pred_skew"], r.get("R_pred_skew_se")
                cells[r["L"]] = ("  n/a" if v is None or not se
                                 else f"{abs(v - 1.0) / se:9.1f}")
            print(f"{wmode:7} {arm:12} {B:5d} " +
                  " ".join(cells.get(L, "      -  ") for L in D["meta"]["Ls"]))
