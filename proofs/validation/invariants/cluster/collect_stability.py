"""Merge per-spec stability results from a SLURM job array.

The array writes one JSON per spec so a dead node loses one spec rather than
the whole sweep. This merges them — and, more importantly, NAMES THE GAPS.

A merge that silently skips missing files would report "every spec that ran
was stable", which is the shape of claim this whole tier exists to refuse. A
spec whose task died is not a stable spec and is not an unstable one; it is a
spec with no result, and it has to be visible as that.

    python3 cluster/collect_stability.py [--dir <path>] [--expect 39]
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
DEFAULT_DIR = pathlib.Path(
    "/projects/standard/hsiehph/sauer354/inv_stability")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=str(DEFAULT_DIR))
    ap.add_argument("--expect", type=int, default=None,
                    help="number of array tasks submitted")
    ap.add_argument("--out", default=str(
        HERE.parent / "results_simulation_stability.json"))
    args = ap.parse_args()

    d = pathlib.Path(args.dir)
    if not d.exists():
        print(f"no such directory: {d}")
        return 2

    merged, revisions, missing, failed = {}, set(), [], []
    expect = args.expect
    if expect is None:
        outs = sorted(d.glob("spec_*.out"))
        expect = len(outs) or 0

    for i in range(expect):
        j = d / f"spec_{i}.json"
        o = d / f"spec_{i}.out"
        if not j.exists():
            why = "task produced no JSON"
            if o.exists():
                tail = [ln for ln in o.read_text(errors="ignore").splitlines()
                        if ln.strip()][-3:]
                why = " | ".join(tail)[:220] or why
            (failed if o.exists() else missing).append((i, why))
            continue
        try:
            blob = json.loads(j.read_text())
        except Exception as e:
            failed.append((i, f"unreadable JSON: {e}"))
            continue
        if blob.get("revision"):
            revisions.add(blob["revision"])
        merged.update(blob.get("specs", {}))

    flaky = {k: v for k, v in merged.items() if v.get("status") == "FLICKERS"}
    stable = {k: v for k, v in merged.items() if v.get("status") == "stable"}

    result = dict(
        revisions=sorted(revisions),
        tasks_expected=expect,
        tasks_with_results=len(merged),
        tasks_failed=[dict(index=i, reason=w) for i, w in failed],
        tasks_missing=[dict(index=i, reason=w) for i, w in missing],
        stable=sorted(stable),
        flickers={k: dict(seeds_agreeing=v.get("seeds_agreeing"),
                          seeds_tried=v.get("seeds_tried"),
                          excess=v.get("excess"))
                  for k, v in flaky.items()},
        specs=merged,
    )
    pathlib.Path(args.out).write_text(json.dumps(result, indent=1))

    print(f"revision(s): {sorted(revisions) or 'unknown'}")
    if len(revisions) > 1:
        print("  WARNING: tasks ran against DIFFERENT revisions. These results "
              "do not share an axis and must not be merged into one number.")
    print(f"expected {expect} specs, have results for {len(merged)}")
    print(f"  stable   {len(stable)}")
    print(f"  FLICKERS {len(flaky)}")
    for k, v in flaky.items():
        print(f"      {k}: agrees {v.get('seeds_agreeing')}/"
              f"{v.get('seeds_tried')}  -- WITHDRAW")
    if failed or missing:
        print(f"  NO RESULT {len(failed) + len(missing)} -- these are neither "
              "stable nor unstable, they are unmeasured:")
        for i, w in (failed + missing)[:20]:
            print(f"      spec {i}: {w}")
        print("  The sweep is INCOMPLETE. Any coverage claim resting on an "
              "unmeasured spec is unsupported.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
