"""CLUSTER JOB 3 -- does any tier's verdict depend on the draw?

REPRODUCIBILITY IS NOT STABILITY.  Every tier here samples, and until now every
one of them sampled from a FIXED seed.  That makes their answers reproducible
and says nothing about whether an answer survives drawing different points.
Determinism answers the easy question.

Three tiers had never been tested this way at all:

  range        the escape search draws start points; a `proved` verdict means
               "sampling found no escape and the interval proof closed", and
               only the second half is draw-independent
  invariants   symmetry, scale, monotonicity and the totality scan all draw
               base points
  theorems     points are drawn until enough satisfy the hypotheses

The simulation tier is covered separately by `run_stability.py`, which varies
point-sets within a run; this job varies the MASTER seed across whole runs,
which additionally perturbs the other three.

Any definition whose verdict moves between seeds was never really covered, and
gets withdrawn the same way a flickering simulation spec does.

INVOCATION
    module load python3/3.10.9_anaconda2023.03_libmamba
    cd <repo>/proofs/validation/invariants
    python3 cluster/run_seed_variation.py --seeds 0 11 977 > cluster/out_seeds.txt 2>&1

RUNTIME: roughly the full-tier runtime times the number of seeds.  Start with
three.  Send back `cluster/out_seeds.txt` and `results_seed_variation.json`.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent

# The stages whose verdicts we compare.  Simulation is excluded on purpose:
# `run_stability.py` already varies its point-sets, and including it here would
# conflate two different perturbations.
STAGES = ["check_ranges", "check_invariants", "check_theorems"]


def run_at_seed(seed):
    """Run the sampling tiers at one master seed; return their verdicts."""
    env = dict(os.environ, GNOMON_SEED=str(seed))
    for mod in STAGES:
        r = subprocess.run([sys.executable, f"{mod}.py"], cwd=str(ROOT),
                           env=env, capture_output=True, text=True)
        if r.returncode:
            print(f"  stage {mod} FAILED at seed {seed}:\n{r.stdout[-2000:]}\n"
                  f"{r.stderr[-2000:]}", flush=True)
            return None

    out = {}
    rng = json.loads((ROOT / "results_ranges.json").read_text())
    for k, v in rng.items():
        out[f"range::{k}"] = v.get("verdict")
    inv = json.loads((ROOT / "results_invariants.json").read_text())
    for k, v in inv.items():
        for c in v.get("checks", []):
            out[f"inv::{k}::{c['kind']}"] = c.get("holds")
        # totality findings compared by identity, not just by count
        for c in v.get("checks", []):
            if c["kind"] != "totality":
                continue
            fs = sorted((f["klass"], f["coordinate"], round(f["at"], 6))
                        for f in (c.get("detail") or {}).get("findings", [])
                        if f.get("is_defect"))
            out[f"totality::{k}"] = fs
    thm = json.loads((ROOT / "results_theorems.json").read_text())
    for k, v in thm.get("theorems", {}).items():
        out[f"thm::{k}"] = v.get("status")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=int, nargs="+", default=[0, 11, 977])
    args = ap.parse_args()

    runs = {}
    for sd in args.seeds:
        print(f"\n=== master seed {sd} ===", flush=True)
        r = run_at_seed(sd)
        if r is None:
            return 1
        runs[sd] = r
        print(f"  {len(r)} verdicts recorded", flush=True)

    base = runs[args.seeds[0]]
    common = set(base)
    for sd in args.seeds[1:]:
        common &= set(runs[sd])

    moved = {}
    for k in sorted(common):
        vals = {sd: runs[sd][k] for sd in args.seeds}
        if len({json.dumps(v, sort_keys=True) for v in vals.values()}) > 1:
            moved[k] = vals

    (ROOT / "results_seed_variation.json").write_text(json.dumps(
        dict(seeds=args.seeds, n_compared=len(common), moved=moved), indent=1))

    print(f"\n{len(common)} verdicts compared across {len(args.seeds)} master "
          f"seeds")
    print(f"{len(moved)} DEPEND ON THE DRAW\n")
    if not moved:
        print("No verdict moved. Every tier's answer is draw-independent on "
              "this corpus, which is what had never been established.")
    else:
        print("These were never really covered -- withdraw them:")
        by_tier = {}
        for k in moved:
            by_tier.setdefault(k.split("::")[0], []).append(k)
        for tier, ks in sorted(by_tier.items()):
            print(f"  {tier}: {len(ks)}")
            for k in ks[:20]:
                print(f"      {k}  {moved[k]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
