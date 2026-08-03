"""Exact site-frequency-spectrum expectations with moments.

`singletonProportion (N0 N1) = 1 - log N0 / log N1` was falsified by
simulation: it returns 0 at the no-growth null where the truth is 1/H_{n-1},
takes no sample size, and was 40-70% off.  It has since been removed from the
development.  This supplies the correct quantity analytically, so a replacement
can be stated rather than fitted.

moments integrates the diffusion forward under a demography and returns the
expected SFS directly -- no simulation, no Monte Carlo error.  A coalescent run
that took minutes becomes an exact calculation in milliseconds.
"""
from __future__ import annotations

import json
import sys

import numpy as np
import moments


def singleton_proportion(fs):
    """Fraction of segregating sites that are singletons (folded at n-1)."""
    a = np.asarray(fs)[1:-1]          # drop the fixed bins
    return float(a[0] / a.sum())


def main():
    rows = []
    ns_list = [20, 50, 100, 200]

    # standard neutral model: the analytic answer is 1 / H_{n-1}
    print("=== no growth (standard neutral) ===")
    print(f"{'n':>5} {'moments':>10} {'1/H_(n-1)':>11} {'lean 1-lnN0/lnN1':>18}")
    for n in ns_list:
        fs = moments.Demographics1D.snm([n])
        harmonic = float(np.sum(1.0 / np.arange(1, n)))
        exact = singleton_proportion(fs)
        rows.append(dict(model="snm", n=n, moments=exact,
                         analytic=1 / harmonic, lean=0.0))
        print(f"{n:5d} {exact:10.4f} {1/harmonic:11.4f} {0.0:18.4f}")

    # exponential growth: nu = N1/N0 over T (in units of 2N0 generations)
    print("\n=== exponential growth, T = 0.05 (2N0 units) ===")
    print(f"{'n':>5} {'N1/N0':>8} {'moments':>10} {'lean':>10} {'err%':>8}")
    for n in (50, 200):
        for ratio in (10.0, 100.0, 1000.0):
            T = 0.05
            fs = moments.Demographics1D.growth([ratio, T], [n])
            exact = singleton_proportion(fs)
            lean = 1 - np.log(1.0) / np.log(ratio) if ratio != 1 else 0.0
            # lean uses absolute sizes; with N0 = 1000 this is 1 - ln1000/ln(1000*ratio)
            N0 = 1000.0
            lean = 1 - np.log(N0) / np.log(N0 * ratio)
            rows.append(dict(model="growth", n=n, ratio=ratio, T=T,
                             moments=exact, lean=lean))
            print(f"{n:5d} {ratio:8.0f} {exact:10.4f} {lean:10.4f} "
                  f"{100*(lean-exact)/exact:8.1f}")

    with open(sys.argv[1] if len(sys.argv) > 1 else "sfs.json", "w") as fh:
        json.dump(rows, fh)

    print("\nThe correct no-growth value is 1/H_(n-1): a function of SAMPLE SIZE,")
    print("which the removed definition could not express -- it had no n argument.")


if __name__ == "__main__":
    main()
