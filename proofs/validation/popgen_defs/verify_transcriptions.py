"""Check every hand transcription in check_defs.py against the actual Lean.

    /projects/standard/hsiehph/sauer354/popgen_venv/bin/python verify_transcriptions.py

WHY THIS EXISTS.  check_defs.py compares simulation against Lean definitions
that were transcribed INTO PYTHON BY HAND, with the Lean source quoted in each
docstring.  Nothing checked those transcriptions, and the quoted line numbers
were the only link back to the corpus.  Both rot:

  * `lean_ldHalfLife` was `2 * Ne * Real.log 2` taking one argument.  The corpus
    now says `Real.log 2 / (-Real.log (ldRetentionPerGen r Ne))` and takes two.
    The transcription was not exercised by any check, so even the arity change
    raised nothing -- it simply sat there being wrong.
  * `lean_fstFromDrift`, `lean_islandModelFst` and `lean_singletonProportion`
    name definitions that NO LONGER EXIST in the corpus.  Three of the four
    original checks were therefore grading simulation against formulas the
    development had removed, and still printed a full table of error
    percentages.

A stale transcription is worse than a missing one: it produces a number, the
report prints it next to a simulation, and a reader takes the agreement or the
disagreement as evidence about the corpus.  It is evidence about a formula
nobody has read in months.

The extractor (validation/extract) already parses every Lean body into a
callable.  That is an INDEPENDENT second path to the same formula, so the two
can be compared point by point.  Disagreement means one of them is wrong and a
human has to look; it never picks a winner.
"""
from __future__ import annotations

import pathlib
import random
import sys

HERE = pathlib.Path(__file__).resolve().parent
EXTRACT = HERE.parent / "extract"
sys.path.insert(0, str(EXTRACT))
sys.path.insert(0, str(HERE))

import check_defs                                                # noqa: E402
import api                                                       # noqa: E402

# Positive arguments keep every quoted formula inside its intended domain: these
# are rates, counts and frequencies, and comparing two transcriptions of the
# same formula outside its domain compares two junk conventions, not the bodies.
DOMAIN = {
    "t": (1.0, 200.0), "Ne": (10.0, 5000.0), "k": (5.0, 500.0),
    "r": (0.0, 0.2), "c": (0.0, 0.2), "D0": (0.01, 0.25), "D₀": (0.01, 0.25),
    "theta": (0.001, 2.0), "θ": (0.001, 2.0), "alpha": (0.0, 0.9),
    "α": (0.0, 0.9), "fst_AB": (0.0, 0.5),
    "p1": (0.02, 0.98), "p2": (0.02, 0.98), "p₁": (0.02, 0.98), "p₂": (0.02, 0.98),
}
DEFAULT = (0.05, 0.95)
TOL = 1e-9
N = 200


def main() -> int:
    api.refresh()
    # NAME EVERY INPUT.  A run that does not print which files it read has to be
    # trusted; one that does can be checked.  This script exists because a
    # harness was comparing simulation against definitions that no longer
    # existed, and the report gave no way to see that from its output.
    st = api.stamp()
    print(f"transcriptions : {pathlib.Path(check_defs.__file__).resolve()}")
    print(f"extracted table: {(EXTRACT / 'defs.json').resolve()}")
    print(f"corpus         : {st['source_digest_on_disk']} over "
          f"{st['source_files']} files, {st['n_definitions']} definitions")
    print(f"table current  : {st['table_is_current']}\n")
    rng = random.Random(20260803)
    bad, gone, ok = [], [], []

    for pyname, leanname in sorted(check_defs.TRANSCRIBED_FROM.items()):
        fn = getattr(check_defs, pyname, None)
        if fn is None:
            bad.append(f"{pyname}: not defined in check_defs.py")
            continue
        try:
            lean_fn, argnames = api.callable_for(leanname)
        except Exception as e:                                   # noqa: BLE001
            gone.append(f"{pyname} -> {leanname}: {type(e).__name__}: "
                        f"{str(e)[:90]}")
            continue
        worst, worst_pt = 0.0, None
        err = None
        for _ in range(N):
            pt = [rng.uniform(*DOMAIN.get(a, DEFAULT)) for a in argnames]
            try:
                a = float(lean_fn(*pt))
                b = float(fn(*pt))
            except TypeError as e:
                err = (f"ARITY/TYPE MISMATCH: the Lean takes {argnames}, the "
                       f"transcription refused them ({e})")
                break
            except Exception as e:                               # noqa: BLE001
                err = f"{type(e).__name__}: {e}"
                break
            rel = abs(a - b) / max(1.0, abs(a))
            if rel > worst:
                worst, worst_pt = rel, (pt, a, b)
        if err:
            bad.append(f"{pyname} -> {leanname}: {err}")
        elif worst > TOL:
            pt, a, b = worst_pt
            bad.append(f"{pyname} -> {leanname}: DISAGREE by {worst:.3e}; at "
                       f"{dict(zip(argnames, [round(x, 6) for x in pt]))} the "
                       f"Lean gives {a!r} and the transcription {b!r}")
        else:
            ok.append(f"{pyname:32s} == {leanname:42s} (worst {worst:.1e} over "
                      f"{N} points, args {argnames})")

    print("=" * 78)
    print("TRANSCRIPTIONS THAT MATCH THE LEAN")
    print("=" * 78)
    for line in ok:
        print("  ok  " + line)

    if check_defs.RETIRED_TRANSCRIPTIONS:
        print("\n" + "=" * 78)
        print("TRANSCRIPTIONS OF DEFINITIONS THE CORPUS NO LONGER HAS")
        print("=" * 78)
        print("  Each of these was comparing simulation against a formula the")
        print("  development has removed, while printing a full error table.")
        for k, v in sorted(check_defs.RETIRED_TRANSCRIPTIONS.items()):
            print(f"  RETIRED  {k:28s} {v}")

    if gone:
        print("\n" + "=" * 78)
        print("NAMED LEAN DEFINITION COULD NOT BE RESOLVED")
        print("=" * 78)
        for line in gone:
            print("  GONE  " + line)

    print("\n" + "=" * 78)
    print("EXPLICIT GAPS: asked for, no check written")
    print("=" * 78)
    for k, v in sorted(check_defs.GAPS.items()):
        print(f"  GAP  {k}\n         {v}")

    if bad:
        print("\n" + "=" * 78)
        print(f"{len(bad)} TRANSCRIPTION(S) DISAGREE WITH THE CORPUS")
        print("=" * 78)
        for line in bad:
            print("  BAD  " + line)
        return 1
    print(f"\nall {len(ok)} live transcriptions agree with the extracted Lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
