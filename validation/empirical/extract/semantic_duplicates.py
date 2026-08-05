"""Definitions that compute the SAME FUNCTION under different bodies.

`validation/code/architecture.py`'s `gate_duplicate_bodies` keys on
alpha-normalised body TEXT, so it catches `1 - a/b` against `1 - x/y` and misses
anything that differs by algebraic rearrangement. It reported zero while
`fstMigDriftNext` -- `(1 - 2m - 1/(2Ne)) * F + 1/(2Ne)` -- and `ibdFlowStep` --
`F + (1-F)/(2Ne) - 2*rate*F` -- were the same affine map in two modules. Nothing
alpha-normalises those to one string; only expanding does.

So this asks a different question. Two definitions with the same explicit real
arity are evaluated at one shared batch of random points, and a collision is
reported when every value agrees. That is evidence, not proof: agreement on 200
points is not agreement everywhere, and the pair still has to be read. It is the
same standard the corpus already applies to its simulation batteries, and it is
why the output says CANDIDATE.

WHY THIS IS NOT A GATE. A shared function is not automatically a defect. The
corpus keeps `genotypeVarianceHWE` and `hweHeterozygosity` apart deliberately --
one a variance of a 0/1/2 dosage, the other a heterozygote probability, equal
under Hardy-Weinberg and not the same quantity -- and conflating them with the
allelic variance is the factor-of-four error the corpus has already paid for
once. What this produces is a reading list: pairs that agree numerically and
have no theorem saying so.

    python3 validation/empirical/extract/semantic_duplicates.py [--points N]
"""
from __future__ import annotations

import argparse
import collections
import re
import math
import random
import sys
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                       # noqa: E402


def scalar_arity(entry) -> int | None:
    """Number of explicit arguments, if every one of them is a plain real.

    A definition taking a structure, a vector or a function is skipped: those
    need an inhabitant to evaluate, inhabitants are drawn per-definition, and two
    definitions handed DIFFERENT random structures would disagree for a reason
    that has nothing to do with the maps they compute.
    """
    args = [a for a in entry.get("args", []) if not a.get("implicit")]
    if not args:
        return None
    n = 0
    for a in args:
        if a.get("type", "").strip() not in ("ℝ", "ℝ"):
            return None
        n += len(a.get("names", []))
    return n


def fingerprint(fn, arity, points):
    """Values at a shared batch, or None if the definition will not evaluate."""
    out = []
    for pt in points[arity]:
        try:
            v = fn(*pt)
        except Exception:                                        # noqa: BLE001
            return None
        if not isinstance(v, (int, float)) or isinstance(v, bool):
            return None
        if not math.isfinite(v):
            # A junk value IS part of the function and is kept, but NaN cannot be
            # compared for equality and would make a pair look distinct for a
            # reason that is an artefact of the encoding.
            return None
        out.append(v)
    return tuple(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--points", type=int, default=200)
    args = ap.parse_args()

    rng = random.Random(20260805)
    # One shared batch per arity, so two definitions are compared at IDENTICAL
    # inputs. Points avoid 0 and 1: every ratio-shaped body in this corpus is
    # pinned at those, so including them makes unrelated definitions collide.
    points = {n: [tuple(rng.uniform(0.07, 0.93) for _ in range(n))
                  for _ in range(args.points)]
              for n in range(1, 7)}

    table = api.definition_table()
    groups: dict = collections.defaultdict(list)
    evaluated = skipped = 0
    for fq in sorted(table):
        try:
            entry = api.definition(fq)
        except Exception:                                        # noqa: BLE001
            continue
        arity = scalar_arity(entry)
        if arity is None or arity > 6:
            skipped += 1
            continue
        try:
            fn, _ = api.callable_for(fq)
        except Exception:                                        # noqa: BLE001
            skipped += 1
            continue
        fp = fingerprint(fn, arity, points)
        if fp is None:
            skipped += 1
            continue
        evaluated += 1
        groups[(arity, fp)].append(fq)

    collisions = {k: v for k, v in groups.items() if len(v) > 1}
    print(f"evaluated {evaluated} scalar definitions at {args.points} shared "
          f"points ({skipped} skipped: non-scalar arguments, no executable "
          f"form, or a non-finite value)")
    print(f"groups agreeing at every point: {len(collisions)}\n")

    # A KERNEL AND ITS WRAPPERS MUST AGREE, and that is the repaired state rather
    # than the defect -- `oddsLike`, `coalFst` and `qst` collide because the last
    # two CALL the first, which is exactly what the Core layer is for. Excluded
    # here for the same reason `gate_duplicate_bodies` excludes delegations: a
    # detector that flags the fix it exists to encourage cannot be read.
    interesting = []
    for (arity, _), names in collisions.items():
        bodies = {}
        for n in names:
            try:
                bodies[n] = api.definition(n).get("body", "")
            except Exception:                                    # noqa: BLE001
                bodies[n] = ""
        shorts = {n.rsplit(".", 1)[-1] for n in names}
        kernels = [set(re.findall(r'Descent\.Core\.(\w+)', b)) | (shorts & set(re.findall(r'\b(\w+)\b', b)))
                   for b in bodies.values()]
        # every member routing through one shared name is the repaired shape
        if kernels and set.intersection(*kernels):
            continue
        interesting.append((arity, sorted(shorts)))

    print(f"of those, groups NOT sharing a kernel or calling one another: "
          f"{len(interesting)}\n")
    for arity, shorts in sorted(interesting, key=lambda kv: -len(kv[1])):
        print(f"  arity {arity}: {', '.join(shorts)}")
    if collisions:
        print("\nCANDIDATES, not defects. Agreement at 200 points is evidence "
              "that two bodies compute one function; whether they name one "
              "QUANTITY is a question about what they mean, and the corpus "
              "keeps several numerically-equal pairs apart on purpose.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
