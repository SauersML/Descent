"""Differential test of Lean's totality conventions against a second implementation.

Every verdict this checker emits rests on the transcribed body computing what
Lean computes.  Mathlib totalises partial operations, and the conventions are
easy to get subtly wrong in a way no test of the CHECKER would catch -- an
earlier version of `backends.py` returned 0 for `Real.log` of every nonpositive
argument, where Mathlib defines `log` through `|x|` and so `log (-2) = log 2`.
That error would silently change which definitions look defective.

Two independently written implementations agreeing is the only real evidence
either is right, so this compares `backends.FloatBackend` against the `extract`
agent's `lean_rt`, which was written separately from a separate reading of
Mathlib.

Exit code is non-zero on any disagreement.  Run it before trusting a report:

    python test_lean_semantics.py
"""
from __future__ import annotations

import math
import pathlib
import random
import sys

import backends

EXTRACT = pathlib.Path(__file__).resolve().parents[1] / "extract"


def load_reference():
    sys.path.insert(0, str(EXTRACT))
    try:
        import lean_rt
    except Exception as e:
        return None, f"reference implementation unavailable: {e}"
    return lean_rt, None


def _overflow_pair(x, y):
    """Is this a double-precision overflow rather than a semantic difference?

    `(1e-300) ** -2` is 1e600, a perfectly ordinary real that Lean has no
    trouble with and a float cannot hold.  One implementation returns `inf`
    and the other raises; neither is Mathlib's answer, and the difference says
    nothing about the totality conventions this test exists to check.  Counted
    and reported, not failed on.
    """
    xs = x if isinstance(x, str) else ("inf" if math.isinf(x) else None)
    ys = y if isinstance(y, str) else ("inf" if math.isinf(y) else None)
    if xs is None and ys is None:
        return False
    tokens = {t for t in (xs, ys) if t is not None}
    return tokens <= {"inf", "raise:OverflowError"}


def main():
    ref, err = load_reference()
    if ref is None:
        # This test is a trust-boundary gate: without the independent runtime
        # there was no comparison, so success would turn an unverified result
        # into a false green in `cluster/run_all.py` and CI.
        print(f"SKIPPED - {err}")
        print("The totality conventions in backends.py are then UNVERIFIED.")
        return 2

    pairs = [
        ("Real.log", backends.FLOAT.log, ref.rlog, 1),
        ("Real.sqrt", backends.FLOAT.sqrt, ref.rsqrt, 1),
        ("_ / _", backends.FLOAT.div, ref.rdiv, 2),
        ("Real.rpow", backends.FLOAT.rpow, ref.lpow, 2),
    ]
    rng = random.Random(20240801)
    bad, total, overflow = [], 0, 0
    # deliberately include the exact junk points, not just random reals
    specials = [0.0, -0.0, 1.0, -1.0, 1e-300, -1e-300, 2.0, -2.0]
    for _ in range(4000):
        a = rng.choice(specials + [rng.uniform(-50, 50)])
        b = rng.choice(specials + [rng.uniform(-5, 5)])
        for name, mine, theirs, arity in pairs:
            args = (a,) if arity == 1 else (a, b)
            total += 1
            try:
                x = mine(*args)
            except Exception as e:
                x = f"raise:{type(e).__name__}"
            try:
                y = theirs(*args)
            except Exception as e:
                y = f"raise:{type(e).__name__}"
            if _overflow_pair(x, y):
                overflow += 1
                continue
            if isinstance(x, str) or isinstance(y, str):
                if x != y:
                    bad.append((name, args, x, y))
                continue
            if math.isnan(x) and math.isnan(y):
                continue
            if not (abs(x - y) <= 1e-9 * max(1.0, abs(x), abs(y))):
                bad.append((name, args, x, y))

    print(f"{total} comparisons across {len(pairs)} primitives")
    if overflow:
        print(f"{overflow} skipped as double-precision overflow (not a "
              "semantic difference)")
    if bad:
        print(f"FAILED - {len(bad)} disagreements with the reference:")
        for name, args, x, y in bad[:15]:
            print(f"  {name}{args}: backends={x!r} lean_rt={y!r}")
        print("\nThe two implementations of Mathlib's totality conventions "
              "disagree.\nEvery verdict in results_*.json is suspect until "
              "this is resolved.")
        return 1
    print("PASSED - 0 semantic disagreements. The totality conventions in "
          "backends.py\nagree with an independently written implementation, "
          "including at the junk points.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
