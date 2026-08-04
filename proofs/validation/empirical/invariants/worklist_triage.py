"""Split the work list by WHOSE problem each entry is.

WHY

`unreachable.py` says a definition is not covered and gives a reason. For the
`no-derivable-check` entries the reason reads

    no theorem's conclusion mentions it, so the corpus states no property of it

and the obvious response is to write a theorem. Four times in one session that
response produced a DUPLICATE: `fstTransientAt_zero`, `expanderAgreementFloor_pos`,
`gaussianJetVariance_pos` and `ageDependentSignalShape_at_peak` all already
existed. Every one of those was on the list because this checker could not read
the theorem, not because the corpus lacked it -- nullary constants were refused
outright, structure binders were filed as hypotheses, one-line term-mode proofs
were left unparsed.

Writing Lean for that group is wasted work, and worse, it hides the tooling bug
behind a second theorem that happens to be readable.

WHAT THIS DOES

For every uncovered definition, look for theorems whose conclusion mentions it
and report what `check_theorems` decided about each:

  checker-rejected   a theorem mentions the definition and was NOT evaluated.
                     The reason is printed. This is a tooling fix, and one fix
                     usually clears many definitions at once.
  checker-blind      a theorem mentions it, evaluated, held, and discriminated
                     nothing. This is a real corpus gap: the statement is an
                     invariance, a vanishing criterion or a one-sided bound that
                     a wrong body also satisfies, and it needs a pinning theorem.
  unstated           nothing mentions it. Only this group needs a theorem
                     written from scratch.

EIGHT WAYS A DEFINITION LOOKS COVERED AND IS NOT

The `checker-blind` group is the interesting one, and across roughly eighty
repairs it has come in eight shapes.  Each is a theorem that holds, that a reader
would take as verification, and that a whole family of wrong bodies also
satisfies.  Listed with what each fixes and what it leaves free:

  restatement (`rfl`)        nothing at all; true of every body by construction
  one-sided surd bound       a sign; not the sign-flipped constant, which usually
                             lands on the same side of zero
  invariance / symmetry      the structure; not the constant.  Twice a ratio is
                             still unit-invariant, twice a distance still
                             symmetric with the same vanishing criterion
  vanishing criterion        where it is zero; not the slope through that zero
  growth or decay rate       the direction; not the rate.  A decay theorem holds
                             for EVERY decreasing function, so it constrains no
                             exponent -- the most common case in this corpus, and
                             the one where the docstring most often claims a rate
  monotone cluster           the direction across several related quantities; no
                             scale for any of them
  cross-identity             the two definitions JOINTLY and neither alone.  If
                             both carry the same wrong factor it cancels and the
                             identity survives untouched
  fixed-point / recurrence   invariant under exactly the rescaling it should
                             exclude: the equilibrium of `c * f` is a fixed point
                             of the recurrence for every `c`, since `c` appears
                             on both sides

The repair is the same in all eight: EVALUATE AT THE ARGUMENT WHERE THE WRONG
BODIES DISAGREE.  Usually a fixed point, an interior maximum, an endpoint of the
parameter range, or a reference value at which one term drops out.  Multiplying a
denominator back is the same move for ratios.

A corollary worth stating separately: constraints on DERIVED quantities do not
reach the base.  `dosageTransportBias` and `haplotypeTransportBias` are both
differences of `averagePhaseInteraction`, and bounding both differences leaves the
interpolation they are built from unpinned.

Run after check_theorems.py:

    python3 worklist_triage.py            # counts
    python3 worklist_triage.py --list     # every entry, grouped
"""

from __future__ import annotations

import collections
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


def load(name: str):
    p = HERE / name
    return json.loads(p.read_text(encoding="utf-8")) if p.exists() else {}


def triage() -> dict:
    cov = load("coverage.json")
    unreach = load("unreachable.json")
    res = load("results_theorems.json")
    theorems = res.get("theorems", {}) if isinstance(res, dict) else {}

    # definition short name -> theorems whose conclusion mentions it
    mentions: dict[str, list] = collections.defaultdict(list)
    for tname, t in theorems.items():
        for d in t.get("mentions", []) or []:
            mentions[d].append((tname, t))

    out: dict[str, list] = {"checker-rejected": [], "checker-blind": [], "unstated": []}
    for key, info in sorted(unreach.items()):
        if cov.get(key, {}).get("covered"):
            continue
        if info.get("stage") != "no-derivable-check":
            continue
        short = key.rsplit(".", 1)[-1]
        hits = mentions.get(short, [])
        if not hits:
            out["unstated"].append((key, ""))
            continue
        rejected = [(n, t) for n, t in hits if t.get("status") != "holds"]
        if rejected:
            n, t = rejected[0]
            out["checker-rejected"].append(
                (key, f"{n}: {t.get('status')} -- {str(t.get('reason'))[:70]}"))
        else:
            n, _ = hits[0]
            out["checker-blind"].append((key, f"{n} holds but discriminates nothing"))
    return out


def main(argv: list[str]) -> int:
    groups = triage()
    if not any(groups.values()):
        print("nothing to triage: run check_theorems.py and report.py first",
              file=sys.stderr)
        return 2
    for name in ("checker-rejected", "checker-blind", "unstated"):
        rows = groups[name]
        print(f"{name:18s} {len(rows)}")
    print()
    print("checker-rejected is a TOOLING fix and clears many at once.")
    print("checker-blind needs a pinning theorem: the existing one is an")
    print("invariance a wrong body also satisfies.")
    print("unstated is the only group needing a theorem written from scratch.")
    if "--list" in argv:
        for name in ("checker-rejected", "checker-blind", "unstated"):
            print()
            print(f"== {name}")
            for key, why in groups[name]:
                print(f"  {key}")
                if why:
                    print(f"      {why}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
