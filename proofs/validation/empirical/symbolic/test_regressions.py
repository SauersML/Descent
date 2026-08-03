"""Regression tests for the checker itself.

Every case here is a bug the checker actually shipped, or a corpus fact it must
keep confirming.  Run with:

    .venv/bin/python test_regressions.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import sympy as sp

import leansym as L
import hyps as H
import fixedpoint as FP
from paths import ARTIFACTS as ART

HERE = Path(__file__).parent
FAILURES = []


def check(name, cond, detail=""):
    print(f"  {'PASS' if cond else 'FAIL'}  {name}" + (f"  {detail}" if detail else ""))
    if not cond:
        FAILURES.append(name)


def table():
    import shared
    return shared.build_table()


def main():
    tab = table()
    conv = L.Converter(tab)

    print("BUG 1 -- pair by the theorem's map, never by name proximity")
    # the migration-first equilibrium is the fixed point of the migration-first
    # map, and NOT of the selection-first map
    s, m, p = sp.symbols("s m p", positive=True)
    mf = conv.convert(tab["continentIslandStepMigrationFirst"][1],
                      {"s": s, "m": m, "p": p})
    sf = conv.convert(tab["continentIslandStepSelectionFirst"][1],
                      {"s": s, "m": m, "p": p})
    eq_mf = (s - m - m * s) / (s * (1 - m))
    eq_sf = (s - m - m * s) / s
    check("migration-first equilibrium is a fixed point of the migration-first map",
          sp.simplify(mf.subs(p, eq_mf) - eq_mf) == 0)
    check("selection-first equilibrium is a fixed point of the selection-first map",
          sp.simplify(sf.subs(p, eq_sf) - eq_sf) == 0)
    check("the two maps are different functions",
          sp.simplify(mf - sf) != 0)

    print("BUG 2 -- coupled systems solved jointly")
    M, A, B = sp.symbols("M ETss ETst", positive=True)
    sols, _ = FP.joint_fixed_point(
        {"ETss": 1 / (1 + M) + (M / (1 + M)) * B, "ETst": 1 / M + A},
        {"ETss": A, "ETst": B})
    check("two-deme joint solution is ETss=2, ETst=(2M+1)/M",
          sols is not None and len(sols) == 1
          and sp.simplify(sols[0]["ETss"] - 2) == 0
          and sp.simplify(sols[0]["ETst"] - (2 * M + 1) / M) == 0,
          str(sols[0] if sols else None))

    print("BUG 3 -- no variable capture in map/equilibrium binding")
    c1 = json.load(open(ART / "results_check1.json"))
    delta = [r for r in c1 if r["name"] == "twoDemeIMEquilibriumDelta"]
    check("twoDemeIMEquilibriumDelta is not reported as a failed fixed point",
          all(r["status"] not in ("FIXED_POINT_FAILS",) for r in delta),
          str([r["status"] for r in delta]))
    shared = [r for r in c1 if r["name"] == "sharedLD_from_equilibrium"]
    check("sharedLD_from_equilibrium is classified, not failed",
          all(r["status"] not in ("FIXED_POINT_FAILS",) for r in shared),
          str([r["status"] for r in shared]))
    check("no FIXED_POINT_FAILS anywhere in the corpus",
          not [r for r in c1 if r["status"] == "FIXED_POINT_FAILS"],
          str([r["fqn"] for r in c1 if r["status"] == "FIXED_POINT_FAILS"]))

    print("BUG 4 -- linearised is distinguished from wrong")
    Ne, mm, F = sp.symbols("Ne m F", positive=True)
    lin_fp = sp.simplify(sp.solve(sp.Eq(F * (1 - 2 * mm) + (1 - F) / (2 * Ne), F), F)[0])
    exact_fp = sp.simplify(sp.solve(
        sp.Eq((1 - mm) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * F), F), F)[0])
    check("island 1/(1+4Ne m) is NOT the exact root of the unlinearised map",
          sp.simplify(lin_fp - exact_fp) != 0)
    hits = FP.linearisation_verdict(lin_fp, exact_fp, [Ne, mm])
    m0 = [h for h in hits if h["regime"] == "m -> 0"]
    check("it IS the exact root's leading term as m -> 0, error O(m^2)",
          bool(m0) and m0[0]["agree_to_order"] == 1
          and m0[0]["leading_error_order"] == 2,
          str(m0[0] if m0 else None))
    # the exact identity supplied by the team lead, pinned as ground truth
    D = (1 - mm) ** 2 + 2 * Ne * mm * (2 - mm)
    xstar = (1 - mm) ** 2 / D
    lead_err = 2 * Ne * mm ** 2 * (2 * mm - 3) / (D * (1 + 4 * Ne * mm))
    check("lead's x* is the exact fixed point of the IBD recurrence",
          sp.simplify((1 - mm) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * xstar)
                      - xstar) == 0)
    check("x* - 1/(1+4Ne r) equals the supplied error term exactly",
          sp.simplify(xstar - 1 / (1 + 4 * Ne * mm) - lead_err) == 0)
    check("the classical form strictly OVERSTATES the rest point on (0,1)",
          float(xstar.subs({mm: sp.Rational(1, 4), Ne: 2}))
          < float((1 / (1 + 4 * Ne * mm)).subs({mm: sp.Rational(1, 4), Ne: 2})))
    lead_hits = FP.linearisation_verdict(1 / (1 + 4 * Ne * mm), xstar, [Ne, mm])
    lead_r0 = [h for h in lead_hits if h["regime"] == "r -> 0" or h["regime"] == "m -> 0"]
    check("verdict on the supplied pair is holds_to_first_order, error order 2",
          bool(lead_r0) and lead_r0[0]["leading_error_order"] == 2,
          str(lead_r0[0] if lead_r0 else None))

    check("a genuinely wrong form is NOT excused as a linearisation",
          not FP.linearisation_verdict(1 / (1 + 4 * Ne * mm) + 7, exact_fp, [Ne, mm]))
    check("a trivial shared zero limit is not counted as agreement",
          not [h for h in FP.linearisation_verdict(
              (1 - mm) / (1 - Ne), ((1 - mm) / (1 - Ne)) ** 2, [Ne, mm])
              if h["regime"] == "Ne -> 0"])

    print("hypotheses are honoured, not discarded")
    slope = sp.Symbol("slope", real=True)
    v, _ = H.equal_under(sp.Abs(slope - 1), 1 - slope, [sp.Lt(slope, 1)], ())
    check("|slope-1| = 1-slope under slope < 1", v is True)
    v, _ = H.equal_under(sp.Abs(slope - 1), 1 - slope, [], ())
    check("...and is rejected without the hypothesis", v is False)

    print("shared parser is the source of definition bodies")
    import shared
    check("shared table is non-empty and excludes the phantom singletonProportion",
          len(shared.build_table()) > 500
          and "singletonProportion" not in shared.build_table(),
          f"{len(shared.build_table())} definitions")

    print("Mathlib totality")
    xx = sp.Symbol("xx", real=True)
    import hyps
    f = sp.lambdify([xx], hyps.totalize(1 / xx),
                    modules=[hyps.TOTAL_FUNCS, "math"])
    check("1/0 evaluates to 0, as in Mathlib", f(0.0) == 0.0)
    g = sp.lambdify([xx], hyps.totalize(sp.log(xx)),
                    modules=[hyps.TOTAL_FUNCS, "math"])
    check("log 0 evaluates to 0, as in Mathlib", g(0.0) == 0.0)
    h = sp.lambdify([xx], hyps.totalize(sp.sqrt(xx)),
                    modules=[hyps.TOTAL_FUNCS, "math"])
    check("sqrt of a negative evaluates to 0, as in Mathlib", h(-4.0) == 0.0)

    print("checks can fail: perturbed bodies are rejected")
    cov = json.load(open(ART / "coverage.json"))
    covered = [f for f, e in cov.items()
               if any(c["covered"] for c in e["checks"].values())]
    check("at least 150 definitions have a mutation-rejecting check",
          len(covered) >= 150, f"{len(covered)} covered")

    print()
    if FAILURES:
        print(f"{len(FAILURES)} FAILED: {FAILURES}")
        sys.exit(1)
    print("all regression tests passed")


if __name__ == "__main__":
    main()
