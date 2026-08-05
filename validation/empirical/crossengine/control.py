#!/usr/bin/env python3
"""Neutrality control for the cross-engine harness.  GUARD: XSIM_CE_V1

    python control.py --engines msprime,slim,fwdpy11

Where a forward simulator and a coalescent simulator MUST agree, a disagreement
means the harness is broken, not the corpus.  This is the control that tells
those two cases apart, and nothing in `run.py` should be believed unless it
passes.

Quantity: per-site nucleotide diversity at neutral, freely-recombining sites in
a constant-size Wright-Fisher population.  All engines must return 4*N*mu.
Exits nonzero on disagreement.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import engines as eng_mod            # noqa: E402

N, MU, L = 500, 2.5e-5, 2000         # theta = 4*N*mu = 0.05 per site
TOL_SEMS = 4.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--engines", default="msprime,slim,fwdpy11")
    ap.add_argument("--reps", type=int, default=8)
    ap.add_argument("--out", default=str(HERE / "control.json"))
    a = ap.parse_args()

    theta = 4 * N * MU
    print(f"neutrality control: theta = 4*N*mu = {theta:.6g} "
          f"(N={N}, mu={MU}, L={L}, reps={a.reps})")
    ok, rows = True, []
    for e in eng_mod.load(a.engines.split(",")):
        try:
            xs = [e.neutral_diversity(N, MU, L, 1000 + 977 * r)
                  for r in range(a.reps)]
        except Exception as exc:
            print(f"  {e.name:9s} FAILED: {type(exc).__name__}: {exc}")
            ok = False
            continue
        m, sd = sum(xs) / len(xs), eng_mod.sem(xs)
        z = (m - theta) / sd
        agree = bool(abs(z) <= TOL_SEMS)
        ok = ok and agree
        print(f"  {e.name:9s} ({e.kind:10s}) pi = {m:.6g} ± {sd:.3g}   "
              f"({z:+.2f} sems from theta)   {'OK' if agree else 'DISAGREES'}")
        rows.append({"engine": e.name, "kind": e.kind, "version": e.version,
                     "pi": float(m), "sem": float(sd), "theta": theta,
                     "sems_from_theta": float(z), "agrees": bool(agree)})
    with open(a.out, "w") as fh:
        json.dump({"guard": eng_mod.GUARD, "N": N, "mu": MU, "L": L,
                   "theta": theta, "tol_sems": TOL_SEMS,
                   "ok": ok, "rows": rows}, fh, indent=1)
    print("NEUTRALITY CONTROL " + ("OK" if ok else "BROKEN"))
    print("GUARD " + eng_mod.GUARD)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
