#!/usr/bin/env python3
"""Analyse the growing-support sweep: A(h) = c sqrt(log(1/h)).

This is the regime the module header names for the K-free envelope ("a deconvolution
construction at scale sqrt(log(1/h))").  Questions:
  * does Delta_0(h) behave like Theta(1/sqrt(log(1/h)))?
  * is the deficit ratio Delta_0/Delta_K polynomial in 1/h at fixed K, as
    gradeGap_lower_bound requires, and does its exponent decay like 1/K?
"""

import json
import sys
from collections import defaultdict

import numpy as np


def main():
    rows = [r for r in json.load(open(sys.argv[1])) if r.get("ok")]
    by = defaultdict(dict)
    for r in rows:
        by[r["c"]][(r["K"], r["h"])] = r
    out = {}

    for c, tab in sorted(by.items()):
        Ks = sorted({k for k, _ in tab})
        hs = sorted({h for _, h in tab}, reverse=True)
        print(f"\n=== A(h) = {c} * sqrt(log(1/h)) ===")
        print("h".ljust(9) + "A".rjust(6) + "".join(f"K={k}".rjust(11) for k in Ks)
              + "  TVcheck")
        for h in hs:
            A = c * np.sqrt(np.log(1 / h))
            line = f"{h:<9.0e}{A:6.2f}"
            tvmax = 0.0
            for k in Ks:
                r = tab.get((k, h))
                if r:
                    line += f"{r['delta']:11.6f}"
                    tvmax = max(tvmax, r["tv_fine"] / h)
                else:
                    line += " " * 11
            print(line + f"  {tvmax:.3f}")
        print("  (TVcheck = max over K of recomputed-TV / budget; >1.05 means the LP's")
        print("   discretised TV understated the true one and the row is not trustworthy)")

        print("\n  deficit ratio Delta_0 / Delta_K:")
        print("  h".ljust(11) + "".join(f"K={k}".rjust(9) for k in Ks[1:]))
        for h in hs:
            line = f"  {h:<9.0e}"
            for k in Ks[1:]:
                if (k, h) in tab and (0, h) in tab:
                    line += f"{tab[(0,h)]['delta']/tab[(k,h)]['delta']:9.4f}"
            print(line)

        # envelope shape of Delta_0
        pts = [(h, tab[(0, h)]["delta"]) for h in hs if (0, h) in tab]
        H = np.array([np.log(1.0 / p[0]) for p in pts])
        D = np.array([p[1] for p in pts])
        alpha, logc = np.polyfit(np.log(H), np.log(D), 1)
        print(f"\n  Delta_0 ~ const * log(1/h)^({alpha:+.4f})   "
              f"[claimed exponent -0.5, fixed-support behaviour -1.0]")
        for a, name in ((0.5, "1/sqrt(log(1/h))"), (1.0, "1/log(1/h)")):
            k = float(np.mean(D * H ** a))
            rel = float(np.max(np.abs(D - k * H ** -a) / D))
            print(f"    shape {name:<18}: best const {k:.4f}, max rel err {rel*100:5.1f}%")

        # exponent of the deficit ratio in h (gradeGap requires b_K/2 > 0, b_K ~ 1/K)
        print("\n  fitted b_K from Delta_0/Delta_K ~ h^{-b_K/2}:")
        bK = {}
        for k in Ks[1:]:
            p = [(np.log(h), np.log(tab[(0, h)]["delta"] / tab[(k, h)]["delta"]))
                 for h in hs if (k, h) in tab and (0, h) in tab]
            X = np.array([q[0] for q in p]); Y = np.array([q[1] for q in p])
            s, _ = np.polyfit(X, Y, 1)
            bK[k] = -2 * float(s)
            print(f"    K={k}: b_K = {-2*s:+.4f}   b_K*K = {-2*s*k:+.4f}")
        print("    (b_order requires b_K*K constant; positive b_K required for the gap)")
        out[str(c)] = dict(alpha=float(alpha), bK=bK)

    if len(sys.argv) > 2:
        json.dump(out, open(sys.argv[2], "w"), indent=1)


if __name__ == "__main__":
    main()
