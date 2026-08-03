#!/usr/bin/env python3
"""Analyse the graded-modulus LP output.

Three questions:
  Q1  Is Delta_K increasing or decreasing in K at fixed scale h?  Monotone at all?
  Q2  Is the claimed shape Delta_K(h) ~ h^{b_K/2} with b_K = Theta(1/K) consistent?
      Fit log Delta_K = const + (b_K/2) log h over the small-h decades and report b_K.
      The claim b_K * K = b_1 is then a testable identity.
  Q3  Does the K-free envelope Theta(1/sqrt(log(1/h))) show up in Delta_0?
      Compare fits of  c/log(1/h)^alpha  for alpha free, against alpha = 1/2 and alpha = 1.
"""

import json
import sys
from collections import defaultdict

import numpy as np


def load(path):
    rows = [r for r in json.load(open(path)) if r.get("ok")]
    by = defaultdict(dict)
    for r in rows:
        by[(r["A"], r["m"])][(r["K"], r["h"])] = r
    return rows, by


def main():
    rows, by = load(sys.argv[1])
    out = {}

    for (A, m), tab in sorted(by.items()):
        Ks = sorted({k for k, _ in tab})
        hs = sorted({h for _, h in tab}, reverse=True)
        print(f"\n=== A={A} m={m} : Delta_K(h) ===")
        print("h".ljust(10) + "".join(f"K={k}".rjust(12) for k in Ks))
        for h in hs:
            line = f"{h:<10.1e}"
            for k in Ks:
                r = tab.get((k, h))
                line += f"{r['delta']:12.6f}" if r else " " * 12
            print(line)

        # monotonicity in K at each h
        print("\nmonotone in K at each h (strictly decreasing?):")
        mono = {}
        for h in hs:
            vals = [tab[(k, h)]["delta"] for k in Ks if (k, h) in tab]
            d = np.diff(vals)
            mono[h] = dict(nonincreasing=bool((d <= 1e-9).all()),
                           strict_steps=int((d < -1e-6).sum()),
                           max_increase=float(d.max()))
            print(f"  h={h:.1e}  nonincreasing={mono[h]['nonincreasing']} "
                  f"strict_decreases={mono[h]['strict_steps']}/{len(d)} "
                  f"max_step_up={mono[h]['max_increase']:+.2e}")

        # Q2: local exponent b_K/2 from log-log slope over the smallest decades
        print("\nfitted exponent b_K (Delta_K ~ h^{b_K/2}), small-h decades:")
        bK = {}
        small = [h for h in hs if h <= 1e-3]
        for k in Ks:
            pts = [(np.log(h), np.log(tab[(k, h)]["delta"]))
                   for h in small if (k, h) in tab and tab[(k, h)]["delta"] > 0]
            if len(pts) < 3:
                continue
            X = np.array([p[0] for p in pts])
            Y = np.array([p[1] for p in pts])
            slope, icpt = np.polyfit(X, Y, 1)
            resid = float(np.max(np.abs(Y - (slope * X + icpt))))
            bK[k] = dict(b=2 * float(slope), maxresid=resid)
            print(f"  K={k}: b_K={2*slope:+.4f}  (max log-resid {resid:.3f})")
        if 1 in bK:
            print("  claim b_K*K = b_1 :", {k: round(v["b"] * k, 4) for k, v in bK.items()},
                  " b_1 =", round(bK[1]["b"], 4))

        # Q3: envelope shape of Delta_0
        pts = [(h, tab[(0, h)]["delta"]) for h in hs if (0, h) in tab]
        H = np.array([np.log(1.0 / p[0]) for p in pts])
        D = np.array([p[1] for p in pts])
        # fit log Delta_0 = log c - alpha log log(1/h)
        alpha, logc = np.polyfit(np.log(H), np.log(D), 1)
        print(f"\nDelta_0 envelope: fit c * log(1/h)^(-alpha) -> alpha={-alpha:.4f}, c={np.exp(logc):.4f}")
        for a, name in ((0.5, "1/sqrt(log(1/h)) [claimed]"), (1.0, "1/log(1/h)")):
            c = float(np.mean(D * H ** a))
            rel = float(np.max(np.abs(D - c * H ** -a) / D))
            print(f"   shape {name}: best c={c:.4f}, max rel error {rel*100:.1f}%")

        out[f"A={A},m={m}"] = dict(mono={f"{k:.1e}": v for k, v in mono.items()},
                                   bK=bK, alpha=float(-alpha))

    if len(sys.argv) > 2:
        json.dump(out, open(sys.argv[2], "w"), indent=1)


if __name__ == "__main__":
    main()
