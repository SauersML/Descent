"""Which range checks CAN fail, and which are certifying arithmetic?

A range check on a body that cannot leave its bound certifies the arithmetic
rather than the definition.  `liabilitySensitivity` was the first visible case:
its bound is `Phi`'s codomain, so the check passed on the strength of `Phi`
rather than of the body.  This asks, for every name-graded definition, whether
a violating input EXISTS.

    LIVE          a concrete violating point exists inside the admissible box.
                  The check can fail; it is real coverage.
    BOX-VACUOUS   no violation in the box, but a concrete one exists outside.
                  A BOX-INFERENCE problem, and fixable by widening the box.
    INTRINSIC     containment proved even on a widened box.  A HARD CEILING:
                  the body cannot violate its bound, so grading it proves
                  nothing about the definition and range-checking can never
                  cover it.
    INCONCLUSIVE  neither a witness nor a proof.  Reported, never counted.

BOX-VACUOUS and INTRINSIC are kept apart on purpose.  One is a bug in our box
inference and one is a limit of the method; a single number answering neither
would be worse than two honest ones.

=== THE CONTROL IS WIRED PER DEFINITION, NOT ONCE ===

The refutation arm is `maximize`, which is sound only in the direction of
finding: failing to find a witness is not proof that none exists.  So for every
definition we first ask the refuter to violate an ABSURD bound, [0.499,
0.5001], which essentially no real quantity satisfies.  If the refuter cannot
even do that, IT CANNOT FIRE FOR THIS DEFINITION, and the definition's verdict
is REFUTER-BLIND rather than "cannot violate".

This is not decoration.  On 2026-08-02 a sweep reported 0 of 137 definitions as
able to violate their bound -- a spectacular-looking result, and entirely an
artefact of branching on a `prove_contained` verdict that is unreachable.  A
global version of this control caught it at 0 of 120.  Wiring it per definition
makes the same mistake impossible to make quietly: a blind refuter can no
longer be averaged in with genuine containment.
"""
from __future__ import annotations

import json
import pathlib
import sys

import compile_defs as C
import seeds
from backends import FLOAT, INTERVAL
from check_ranges import _viol
from search import maximize, prove_contained
from semantics import admissible_box, required_range

HERE = pathlib.Path(__file__).resolve().parent

# A bound essentially nothing satisfies.  Used only to ask whether the refuter
# is capable of reporting anything at all for this definition.
ABSURD_LO, ABSURD_HI = 0.499, 0.5001

# "Widened box": wide enough that a body which still cannot escape here is
# constrained by its own arithmetic rather than by our parameter ranges.
WIDE_LO, WIDE_HI = -1e6, 1e6

BUDGET = 4000


def _wide(names):
    # `scale` picks the sampling measure and `maximize` requires it; omitting
    # it raised KeyError on every definition, which the driver swallowed into
    # a uniform ERROR verdict.  "lin" is right for a symmetric widened box.
    return {n: {"lo": WIDE_LO, "hi": WIDE_HI, "scale": "lin",
                "source": "widened"} for n in names}


def find_witness(c, box, names, lo, hi, seed):
    """Search for a concrete point where c leaves [lo, hi].

    Returns (witness_dict, value) or (None, None).  A refutation ALWAYS carries
    its point: a refutation without one is the same class of claim as a witness
    theorem sitting outside the slice it certifies.
    """
    def f(*xs):
        return _viol(c(FLOAT, *xs), lo, hi)

    best, x = maximize(f, box, names, budget=BUDGET, seed=seed)
    if x is None or not (best > 0):
        return None, None
    return dict(zip(names, x)), c(FLOAT, *x)


def classify(c, seed):
    d = c.d
    rng = required_range(d)
    if rng is None:
        return None
    lo, hi, why = rng
    names = c.names
    if not names:
        return None
    box, _unguarded = admissible_box(d)

    # CONTROL FIRST.  If the refuter cannot violate an absurd bound, nothing it
    # fails to find below is evidence of anything.
    ctrl_box, _ = find_witness(c, box, names, ABSURD_LO, ABSURD_HI, seed)
    ctrl_wide, _ = find_witness(c, _wide(names), names, ABSURD_LO, ABSURD_HI, seed)
    refuter_live = ctrl_box is not None or ctrl_wide is not None

    rec = dict(name=d["name"], module=d["module"], lo=lo, hi=hi, why=why,
               refuter_control=bool(refuter_live))

    w, val = find_witness(c, box, names, lo, hi, seed)
    if w is not None:
        return {**rec, "verdict": "LIVE", "witness": w, "value": val}

    if not refuter_live:
        return {**rec, "verdict": "REFUTER-BLIND"}

    fiv = lambda *xs: c(INTERVAL, *xs)
    v_box, _worst, _used = prove_contained(fiv, box, names, lo, hi)
    if v_box != "proved":
        return {**rec, "verdict": "INCONCLUSIVE", "detail": "no witness in box, "
                "and interval arithmetic could not prove containment either"}

    w2, val2 = find_witness(c, _wide(names), names, lo, hi, seed)
    if w2 is not None:
        return {**rec, "verdict": "BOX-VACUOUS", "witness": w2, "value": val2}

    v_wide, _w3, _u3 = prove_contained(fiv, _wide(names), names, lo, hi)
    if v_wide == "proved":
        return {**rec, "verdict": "INTRINSIC"}
    return {**rec, "verdict": "INCONCLUSIVE",
            "detail": "contained in box, no witness outside it, but containment "
                      "on the widened box is unproved"}


def main(argv):
    defs = C.load_defs()                      # freshness-guarded on purpose
    cs, _why_not, _ = C.compile_all(defs)
    seed = seeds.sub("range", 0)

    rows = []
    for k in sorted(cs):
        try:
            r = classify(cs[k], seed)
        except Exception as e:
            r = dict(name=cs[k].d["name"], module=cs[k].d["module"],
                     verdict="ERROR", detail=f"{type(e).__name__}: {e}")
        if r is not None:
            rows.append(r)

    tally = {}
    for r in rows:
        tally[r["verdict"]] = tally.get(r["verdict"], 0) + 1
    total = len(rows)
    print(f"name-graded definitions with inputs: {total}\n")
    for v, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {n:5d}  {v:14s} ({100.0 * n / total:.1f}%)")

    # NO DEFAULT HERE.  `.get(..., True)` counted rows that never reached the
    # control -- every ERROR row -- as "control passed", so a run in which
    # 100% of definitions crashed still printed "BLIND on 0/137".  A summary
    # line that reads reassuring when nothing ran is the failure this whole
    # file is about.
    blind = sum(1 for r in rows if r.get("refuter_control") is False)
    no_control = sum(1 for r in rows if "refuter_control" not in r)
    print(f"\nrefuter control: BLIND on {blind}/{total} definitions "
          f"({100.0 * blind / total:.1f}%)")
    print(f"refuter control: NEVER REACHED on {no_control}/{total} "
          f"(errored before the control ran)")
    print("a definition whose refuter is blind is NEVER counted as "
          "'cannot violate'.")
    if no_control:
        print("REFUSING to summarise: rows that never reached the control "
              "cannot be distinguished from rows that passed it.")

    for want in ("INTRINSIC", "BOX-VACUOUS"):
        sel = [r for r in rows if r["verdict"] == want]
        print(f"\n{want} ({len(sel)}):")
        for r in sel:
            extra = ""
            if "witness" in r:
                extra = "  witness " + ", ".join(
                    f"{k}={v:.6g}" for k, v in r["witness"].items())
            print(f"   {r['module']}.{r['name']}  [{r['lo']}, {r['hi']}]{extra}")

    out = HERE / "results_vacuity.json"
    out.write_text(json.dumps(rows, indent=1, default=str))
    print(f"\n-> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
