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

    BOTH sides must be in that class.  This used to collect tokens only from
    the sides that had one -- a FINITE side contributed nothing -- so `inf`
    against an ordinary finite answer gave `{"inf"}`, satisfied the subset
    test, and was skipped.  Measured: with `backends.FLOAT.log` returning `inf`
    for every argument, all 4000 log comparisons were reclassified as overflows
    and the gate printed "PASSED - 0 semantic disagreements" and returned 0.
    One side finite and the other infinite is the disagreement, not the excuse
    for it.
    """
    def token(v):
        if isinstance(v, str):
            return v
        return "inf" if math.isinf(v) else None

    xs, ys = token(x), token(y)
    if xs is None or ys is None:
        return False
    return {xs, ys} <= {"inf", "raise:OverflowError"}


# Every comparison this gate skips is a comparison it did not make, and the
# skips are the only route by which it can report "0 disagreements" while
# looking at nothing.  A primitive must be genuinely compared at a large
# fraction of its 4000 points.  Not a ratchet: the grid is fixed and
# deterministic, and the clean tree skips well under one percent of any
# primitive, so this is a structural floor rather than a record of today's
# count.
MIN_COMPARED_FRACTION = 0.5


def compare(pairs, n=4000):
    """Run the grid over (name, mine, theirs, arity) tuples.

    Returns (disagreements, total, per-primitive {name: [compared, skipped]}).
    Factored out of `main` so the calibration below can drive it with a
    deliberately wrong backend -- a gate whose only possible input is the
    implementation it is checking can only ever be exercised where that
    implementation happens to be right.
    """
    rng = random.Random(20240801)
    bad, total = [], 0
    tally = {name: [0, 0] for name, _m, _t, _a in pairs}
    # deliberately include the exact junk points, not just random reals
    specials = [0.0, -0.0, 1.0, -1.0, 1e-300, -1e-300, 2.0, -2.0]
    for _ in range(n):
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
                tally[name][1] += 1
                continue
            tally[name][0] += 1
            if isinstance(x, str) or isinstance(y, str):
                if x != y:
                    bad.append((name, args, x, y))
                continue
            if math.isnan(x) and math.isnan(y):
                continue
            # An infinity that reached here is NOT excused as an overflow: the
            # other side was finite, or the two are opposite infinities. The
            # relative test below cannot see it -- `max(1.0, inf, 0.693)` is
            # `inf`, `1e-9 * inf` is `inf`, and `abs(inf - 0.693) <= inf` is
            # True, so an infinite answer "agreed" with every finite one. That
            # is the second half of the same hole: with FLOAT.log returning inf
            # everywhere, the excuse caught most of the grid and this test
            # caught the rest.
            if math.isinf(x) or math.isinf(y):
                if not (math.isinf(x) and math.isinf(y)
                        and math.copysign(1.0, x) == math.copysign(1.0, y)):
                    bad.append((name, args, x, y))
                continue
            if not (abs(x - y) <= 1e-9 * max(1.0, abs(x), abs(y))):
                bad.append((name, args, x, y))
    return bad, total, tally


def calibrate(pairs):
    """Both directions, before the verdict is read.

    This gate had no calibration and one escape hatch, and the hatch was wide
    enough to swallow the gate: `inf` on one side against a finite answer on
    the other was classified as a double-precision overflow, so a backend
    returning `inf` for every `Real.log` passed with "0 semantic
    disagreements".  Each plant below is a one-place change to ONE primitive.
    Returns a list of failures.
    """
    fails = []
    by_name = {name: (mine, theirs, arity) for name, mine, theirs, arity in pairs}

    def with_plant(name, fn):
        out = []
        for n, mine, theirs, arity in pairs:
            out.append((n, fn if n == name else mine, theirs, arity))
        return out

    plants = [
        ("Real.log returns inf everywhere",
         "Real.log", lambda *a: float("inf")),
        ("Real.sqrt returns inf everywhere",
         "Real.sqrt", lambda *a: float("inf")),
        ("Real.log off by a constant",
         "Real.log", lambda x: by_name["Real.log"][0](x) + 1e-3),
        ("division raises instead of totalising x/0 = 0",
         "_ / _", lambda x, y: x / y),
        ("Real.sqrt of a negative returns NaN instead of 0",
         "Real.sqrt", lambda x: math.sqrt(x) if x >= 0 else float("nan")),
    ]
    for label, name, fn in plants:
        bad, _total, _tally = compare(with_plant(name, fn), n=400)
        if not bad:
            fails.append(f"PLANTED DEFECT NOT CAUGHT: {label}")
        elif any(b[0] != name for b in bad):
            fails.append(
                f"the plant in {name} was also reported against "
                f"{sorted({b[0] for b in bad if b[0] != name})}; the gate "
                f"cannot localise which primitive disagrees")

    # NEGATIVE: the overflow excuse must survive, or every genuine 1e600 shows
    # up as a finding and this gate becomes noise.
    if not _overflow_pair(float("inf"), "raise:OverflowError"):
        fails.append("a genuine double-precision overflow pair (inf against "
                     "OverflowError) is no longer excused")
    if not _overflow_pair(float("inf"), float("inf")):
        fails.append("inf on both sides is no longer excused")
    if _overflow_pair(float("inf"), 0.693):
        fails.append("inf against a FINITE answer is still excused as an "
                     "overflow; that is the hole this calibration exists for")
    if _overflow_pair("raise:OverflowError", 0.0):
        fails.append("an OverflowError against a finite answer is still "
                     "excused as an overflow")

    # NEGATIVE: the unperturbed backends must be silent, or nothing above is
    # evidence about anything.
    bad, _total, _tally = compare(pairs, n=400)
    if bad:
        fails.append(f"the unperturbed backends disagree at {len(bad)} points, "
                     f"so the plants above prove nothing: {bad[:2]}")
    return fails


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

    calib = calibrate(pairs)
    if calib:
        print(f"CALIBRATION FAILED - {len(calib)}:")
        for line in calib:
            print(f"  {line}")
        print("\nThe detector is not asserted in both directions, so its "
              "silence below is not evidence.")
        return 1
    print(f"calibration: {5} planted defects each caught and localised, the "
          f"overflow excuse holds for inf-vs-inf and inf-vs-OverflowError and "
          f"no longer swallows inf-vs-finite, unperturbed backends silent.")

    bad, total, tally = compare(pairs)

    print(f"{total} comparisons across {len(pairs)} primitives")
    overflow = sum(skipped for _c, skipped in tally.values())
    if overflow:
        print(f"{overflow} skipped as double-precision overflow (not a "
              "semantic difference)")
    # A primitive that was skipped away is a primitive this run did not check.
    starved = [(name, compared, skipped) for name, (compared, skipped)
               in sorted(tally.items())
               if compared < MIN_COMPARED_FRACTION * (compared + skipped)]
    if starved:
        print("FAILED - a primitive was excused rather than compared:")
        for name, compared, skipped in starved:
            print(f"  {name}: {compared} compared, {skipped} skipped as "
                  f"overflow. A run that skips most of a primitive's grid "
                  f"reports agreement it never observed.")
        return 1
    if bad:
        print(f"FAILED - {len(bad)} disagreements with the reference:")
        for name, args, x, y in bad[:15]:
            print(f"  {name}{args}: backends={x!r} lean_rt={y!r}")
        print("\nThe two implementations of Mathlib's totality conventions "
              "disagree.\nEvery verdict in results_*.json is suspect until "
              "this is resolved.")
        return 1
    for name, (compared, skipped) in sorted(tally.items()):
        print(f"  {name:<10} {compared} compared, {skipped} skipped")
    print("PASSED - 0 semantic disagreements. The totality conventions in "
          "backends.py\nagree with an independently written implementation, "
          "including at the junk points.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
