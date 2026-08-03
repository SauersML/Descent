"""An INDEPENDENT second path for the vector- and matrix-valued definitions.

    python3 validation/extract/xcheck_vector.py       # exits non-zero on any disagreement

WHY THIS EXISTS, AND WHY IT IS NOT REDUNDANT WITH coverage_v2.py.

Four definitions -- cumulativeDrift, heterozygosityLossVariableNe, harmonicMeanNe,
ldMismatchFrobenius -- take vector or matrix arguments, and for a long time
exactly ONE translator could reach them.  Everything downstream of that
translator agreed with it by construction, so if it were wrong about them,
nothing in this project would have said so.  The mutation gate cannot help: it
asks whether a check notices a perturbed body, and it runs that check through
the same translator.  A translator bug is invisible to it.

THIS IS NOT HYPOTHETICAL.  While the extractor was being extended, a regex tore
`(Fin p)` into `(Fin` and `p)`, which silently turned elementwise arithmetic off,
so `Sig_S - Sig_T` in `ldMismatchFrobenius` became a Python list subtraction.
It surfaced as a TypeError only because lists happen to refuse subtraction --
with friendlier shapes it would have returned a NUMBER, and a wrong number that
validates is the worst output this project can produce.  This script is what
caught it.

The references below are transcribed BY HAND from the Lean source text, using
numpy, in a deliberately different style from the extractor's output.  The Lean
text each one claims to implement is PRINTED when the script runs, so the
transcription can be audited against the corpus rather than trusted.  If the
Lean changes, the printed text changes and the transcription must be revisited:
that is the intended maintenance burden, and it is the price of having a second
path at all.
"""
from __future__ import annotations

import json
import math
import pathlib
import random
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                       # noqa: E402

# The Lean each reference below implements, printed for audit.
QUOTED = ["cumulativeDrift", "heterozygosityLossVariableNe", "harmonicMeanNe",
          "ldMismatchFrobenius", "frobeniusNormSq"]


# Lean: cumulativeDrift {T} (Ne : Fin T -> R) : R := sum i, 1 / (2 * Ne i)
# Mathlib totality: x / 0 = 0, so a zero entry contributes nothing.
def ref_cumulativeDrift(Ne):
    return float(np.sum([1.0 / (2.0 * x) if x != 0 else 0.0 for x in Ne]))


# Lean: heterozygosityLossVariableNe (Ne) : R := 1 - Real.exp (-(cumulativeDrift Ne))
def ref_heterozygosityLossVariableNe(Ne):
    return 1.0 - math.exp(-ref_cumulativeDrift(Ne))


# Lean: harmonicMeanNe {T} (Ne : Fin T -> R) : R := (T : R) / sum i, (1 / Ne i)
def ref_harmonicMeanNe(Ne):
    s = float(np.sum([1.0 / x if x != 0 else 0.0 for x in Ne]))
    return 0.0 if s == 0 else len(Ne) / s


# Lean: frobeniusNormSq (A) := sum i : Fin t, sum j : Fin t, (A i j) ^ 2
def ref_frobeniusNormSq(M):
    A = np.asarray(M, dtype=float)
    return float(np.sum(A * A))


# Lean: ldMismatchFrobenius (Sig_S Sig_T) := frobeniusNormSq (Sig_S - Sig_T)
def ref_ldMismatchFrobenius(S, T):
    return ref_frobeniusNormSq(np.asarray(S, float) - np.asarray(T, float))


# Values known WITHOUT running either path.  A random-point comparison shows the
# two agree; these show they agree on the right answer.
CONTROLS = [
    ("Calibrator.cumulativeDrift", ([1.0, 1.0, 1.0],), 1.5),        # 3 * 1/2
    ("Calibrator.cumulativeDrift", ([0.5],), 1.0),                  # 1/(2*0.5)
    ("Calibrator.heterozygosityLossVariableNe", ([1.0, 1.0, 1.0],), 1.0 - math.exp(-1.5)),
    ("Calibrator.harmonicMeanNe", ([1.0, 2.0, 4.0],), 3.0 / 1.75),
    ("Calibrator.harmonicMeanNe", ([5.0, 5.0],), 5.0),   # HM of equals is equal
    ("Calibrator.ldMismatchFrobenius",
     ([[1.0, 0.0], [0.0, 1.0]], [[0.0, 0.0], [0.0, 0.0]]), 2.0),    # ||I2||^2
    ("Calibrator.ldMismatchFrobenius",
     ([[1.0, 2.0], [3.0, 4.0]], [[1.0, 2.0], [3.0, 4.0]]), 0.0),    # identical
    ("Calibrator.ldMismatchFrobenius",
     ([[2.0, 3.0], [4.0, 5.0]], [[1.0, 2.0], [3.0, 4.0]]), 4.0),    # all-ones diff
]

PAIRS = [
    ("Calibrator.cumulativeDrift", ref_cumulativeDrift, "vec"),
    ("Calibrator.heterozygosityLossVariableNe", ref_heterozygosityLossVariableNe, "vec"),
    ("Calibrator.harmonicMeanNe", ref_harmonicMeanNe, "vec"),
    ("Calibrator.ldMismatchFrobenius", ref_ldMismatchFrobenius, "matpair"),
]

TOL = 1e-12
N_RANDOM = 200


def main():
    api.refresh()
    api.require_fresh()
    blob = json.loads((HERE / "defs.json").read_text())
    by_short = {}
    for d in blob["definitions"]:
        by_short.setdefault(d["short"], d)
    print("the Lean these references claim to implement:")
    for s in QUOTED:
        d = by_short.get(s)
        print(f"  {d['name'] if d else s} : {d['ret_type'] if d else '?'}  :=  "
              f"{' '.join(d['body'].split()) if d else 'NOT IN THE CORPUS'}")
    print()

    bad = []
    for name, args, want in CONTROLS:
        fn, _ = api.callable_for(name)
        got = fn(*args)
        if abs(got - want) > TOL * max(1.0, abs(want)):
            bad.append(f"CONTROL {name}{args}: got {got!r}, want {want!r}")
        else:
            print(f"  ok  control {name.split('.')[-1]} -> {got!r}")

    rng = random.Random(4242)
    worst = {}
    for _ in range(N_RANDOM):
        n = rng.randint(1, 7)
        for name, ref, shape in PAIRS:
            if shape == "vec":
                args = ([rng.uniform(0.05, 50.0) for _ in range(n)],)
            else:
                args = tuple([[rng.uniform(-3, 3) for _ in range(n)]
                              for _ in range(n)] for _ in range(2))
            fn, _ = api.callable_for(name)
            got, want = fn(*args), ref(*args)
            rel = abs(got - want) / max(1.0, abs(want))
            worst[name] = max(worst.get(name, 0.0), rel)
            if rel > TOL:
                bad.append(f"{name}: extractor {got!r} vs reference {want!r} "
                           f"at {args!r}")
    print(f"\nworst relative disagreement over {N_RANDOM} random points each:")
    for k, v in sorted(worst.items()):
        print(f"  {k:45s} {v:.3e}")

    if bad:
        print(f"\n{len(bad)} DISAGREEMENT(S) -- one of the two paths is wrong:")
        for b in bad[:20]:
            print("  " + b)
        return 1
    print("\nboth paths agree on every point and every control.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
