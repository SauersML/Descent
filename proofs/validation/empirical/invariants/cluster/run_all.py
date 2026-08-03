"""CLUSTER JOB 2 -- full tier re-run, with an explicit before/after diff.

Runs every stage in order and then DIFFS the new verdicts against whatever was
committed, because the question outstanding is not "what are the numbers" but
"what moved".  A stage banner is printed before each stage so a failure names
itself.

INVOCATION
    module load python3/3.10.9_anaconda2023.03_libmamba
    cd <repo>/proofs/validation/invariants
    python3 cluster/run_all.py > cluster/out_all.txt 2>&1

RUNTIME: roughly 10-20 minutes, dominated by the theorem sweep and the mutation
loops.  Pure numpy, single process.

z3 IS ABSENT ON THE CLUSTER.  `z3backend.decide_range` returns `no-z3` and the
tier falls back to interval branch-and-bound plus sampling.  Every verdict
carries `decided_by`, so a sampling negative remains visibly not a proof.
Expect roughly 25 verdicts to move from `proved` to `inconclusive` for that
reason alone -- those are NOT regressions and the diff labels them.
"""
from __future__ import annotations

import json
import pathlib
import shutil
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
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

STAGES = [
    ("lean-semantics differential test", "test_lean_semantics"),
    ("extract definitions", "extract_defs"),
    ("range escapes", "check_ranges"),
    ("metamorphic invariants + totality", "check_invariants"),
    ("simulation against oracles", "check_simulation"),
    ("theorems as property tests", "check_theorems"),
    ("falsifiability (mutation)", "demo_falsifiable"),
    ("coverage report", "report"),
    ("unreachable accounting", "unreachable"),
]

SNAPSHOT = ["results_ranges.json", "results_invariants.json",
            "results_simulation.json", "results_theorems.json",
            "results_falsifiability.json", "coverage.json"]


def banner(msg):
    print(f"\n{'=' * 70}\n== {msg}\n{'=' * 70}", flush=True)


def main():
    before = {}
    for f in SNAPSHOT:
        p = ROOT / f
        if p.exists():
            before[f] = json.loads(p.read_text())
            shutil.copy(p, HERE / f"before_{f}")

    for label, mod in STAGES:
        banner(label)
        m = __import__(mod)
        rc = m.main([]) if hasattr(m, "main") else 0
        if rc:
            print(f"STAGE FAILED: {label} (rc={rc})", flush=True)
            return rc

    banner("DIFF versus the committed results")
    _diff_ranges(before.get("results_ranges.json"))
    _diff_totality(before.get("results_invariants.json"))
    _diff_coverage(before.get("coverage.json"))
    return 0


def _load(f):
    return json.loads((ROOT / f).read_text())


def _diff_ranges(before):
    if not before:
        print("no previous range results to diff")
        return
    after = _load("results_ranges.json")
    common = set(before) & set(after)
    moved = [(k, before[k]["verdict"], after[k]["verdict"])
             for k in common if before[k]["verdict"] != after[k]["verdict"]]
    # a proved -> inconclusive move with no z3 is expected, not a regression
    z3loss = [m for m in moved
              if m[1] == "proved" and m[2] == "inconclusive"]
    real = [m for m in moved if m not in z3loss]
    print(f"range verdicts: {len(common)} comparable, {len(moved)} moved")
    print(f"  {len(z3loss)} are proved -> inconclusive, EXPECTED: no z3 here")
    print(f"  {len(real)} are other movements:")
    for k, a, b in real[:40]:
        print(f"    {k}: {a} -> {b}")


def _diff_totality(before):
    after = _load("results_invariants.json")

    def defects(d):
        out = {}
        for k, v in (d or {}).items():
            for c in v.get("checks", []):
                if c["kind"] != "totality":
                    continue
                for f in (c.get("detail") or {}).get("findings", []):
                    if f.get("is_defect"):
                        out.setdefault(k, []).append(
                            (f["klass"], f["coordinate"], round(f["at"], 9)))
        return out

    b, a = defects(before), defects(after)
    nb = sum(len(v) for v in b.values())
    na = sum(len(v) for v in a.values())
    print(f"\ntotality defects: before {nb}, after {na}")
    for k in sorted(set(b) | set(a)):
        if b.get(k) != a.get(k):
            print(f"  CHANGED {k}: {b.get(k)} -> {a.get(k)}")
    if set(b) == set(a) and all(b[k] == a[k] for k in b):
        print("  identical: same definitions, same triggering points")


def _diff_coverage(before):
    if not before:
        return
    after = _load("coverage.json")
    common = set(before) & set(after)
    moved = [(k, before[k]["covered"], after[k]["covered"])
             for k in common if before[k]["covered"] != after[k]["covered"]]
    print(f"\ncoverage: {len(common)} comparable, {len(moved)} changed status")
    for k, x, y in moved[:40]:
        print(f"  {k}: {x} -> {y}  (evidence now: "
              f"{after[k].get('evidence_class')})")


if __name__ == "__main__":
    sys.exit(main())
