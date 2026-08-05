"""CLUSTER JOB 1 (PRIORITY) -- seed-stability sweep of every simulation spec.

WHY THIS RUNS FIRST.  This tier's point-set seed was `hash(name) % 10000`, and
Python salts string hashing per process, so its verdicts were not reproducible
between runs.  Every external verdict it has issued is therefore of unknown
reproducibility.  Fixing the seed does not fix that -- it makes the answer
stable, not correct.  Only running each spec against several INDEPENDENT
point-sets and withdrawing any that flips converts a stable number into a real
one.

A local eight-seed sweep found 2 of 20 specs agreeing on only 4/8 and 5/8 while
being reported as agreeing.  This job re-establishes that on the cluster, at
higher replication, after the fix.

INVOCATION
    module load python3/3.10.9_anaconda2023.03_libmamba
    cd <repo>/validation/invariants
    python3 cluster/run_stability.py --seeds 8 > cluster/out_stability.txt 2>&1

EXPECTED RUNTIME: a few minutes.  Pure numpy, single process, no threads
beyond numpy's own.  Memory stays under a few hundred MB: the largest array is
one simulated haplotype pool (1.5e6 int8).

WHAT TO SEND BACK: `cluster/out_stability.txt` and
`results_simulation_stability.json`.

READS   sim_engines.py, check_simulation.py, defs.json
WRITES  results_simulation_stability.json (and stdout)
        Does NOT overwrite results_simulation.json.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


def _revision():
    """The revision every number in this run belongs to.

    A private clone that never pulls diverges silently and starts testing a
    revision nobody else has -- the failure mode that makes two agents'
    numbers incomparable without either noticing. So the revision is recorded
    WITH the numbers rather than assumed, and the caller is expected to pull
    before invoking.
    """
    import subprocess
    try:
        r = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                           cwd=str(HERE), capture_output=True, text=True)
        d = subprocess.run(["git", "status", "--porcelain"],
                           cwd=str(HERE), capture_output=True, text=True)
        rev = r.stdout.strip() or "unknown"
        return rev + ("+dirty" if d.stdout.strip() else "")
    except Exception:
        return "unknown"
sys.path.insert(0, str(HERE.parent))

import check_simulation as CS  # noqa: E402
import compile_defs as C  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=int, default=8,
                    help="independent point-sets per spec")
    ap.add_argument("--only-index", type=int, default=None,
                    help="run ONE spec by index, for a SLURM job array")
    ap.add_argument("--json-out", default=None,
                    help="write results here instead of the default path")
    args = ap.parse_args()

    defs = C.load_defs()
    cs, _, _ = C.compile_all(defs)

    out, flaky = {}, []
    rev = _revision()
    print(f"seed-stability sweep: {len(CS.SPECS)} specs x {args.seeds} "
          f"independent point-sets\ncorpus revision: {rev}\n")
    print(f"{'definition':56s} {'agree':>7s} {'worst excess':>13s}")
    specs = list(CS.SPECS)
    if args.only_index is not None:
        if not 0 <= args.only_index < len(specs):
            print(f"index {args.only_index} out of range for {len(specs)} specs")
            return 2
        specs = [specs[args.only_index]]
    for sp in specs:
        k = sp["name"]
        if k not in cs:
            out[k] = dict(status="not-compiled")
            print(f"{k:56s} {'--':>7s}   not compiled")
            continue
        excess = []
        for sd in range(args.seeds):
            pts = CS._grid(sp["domain"], sp["reps"], seed=9000 + sd * 131)
            orc = CS.oracle_values(sp, pts)
            _, w = CS.compare(cs[k].fn, sp, pts, orc)
            excess.append(w)
        agree = sum(1 for w in excess if w <= 1.0)
        stable = agree == args.seeds
        if not stable:
            flaky.append(k)
        out[k] = dict(status="stable" if stable else "FLICKERS",
                      seeds_tried=args.seeds, seeds_agreeing=agree,
                      excess=[round(w, 4) for w in excess],
                      oracle=sp["note"], tolerance=sp["tol"])
        mark = "" if stable else "   <-- FLICKERS, withdraw"
        print(f"{k:56s} {agree:3d}/{args.seeds:<3d} {max(excess):13.3f}{mark}")

    dest = (pathlib.Path(args.json_out) if args.json_out
            else HERE.parent / "results_simulation_stability.json")
    dest.write_text(json.dumps(
        dict(revision=rev, seeds=args.seeds, specs=out,
             only_index=args.only_index), indent=1))
    print(f"\n{len(CS.SPECS) - len(flaky)} stable, {len(flaky)} flicker")
    if flaky:
        print("WITHDRAW these -- their verdicts depend on the draw:")
        for k in flaky:
            print(f"  {k}  agrees {out[k]['seeds_agreeing']}/{args.seeds}")
    else:
        print("Every spec agrees on every point-set.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
