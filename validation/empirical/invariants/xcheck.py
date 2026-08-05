"""Cross-check the vacuity verdict against the mutation gate.

=== THE DISTINCTION THIS FILE EXISTS TO PRESERVE ===

    vacuity.py asks:        can the TRUE body violate its bound?
    the mutation gate asks: can the check reject a WRONG body?

THESE ARE NOT THE SAME QUESTION, and on 2026-08-02 both the author of this file
and the agent reviewing it treated them as one.  The wrong inference is
seductive and reads as obvious: "a definition whose range check cannot fail
should be exactly one whose mutants all survive".  It is false.

A check that ACCEPTS THE TRUE BODY and REJECTS MUTATED ONES IS A WORKING CHECK
-- that is what discrimination means.  "The true body cannot violate its own
bound" is what you expect of a CORRECT DEFINITION, not evidence that the check
is empty.  A check is vacuous only if it accepts EVERY body, and only the
mutation gate measures that.

The cost of the conflation, measured: it produced a headline claiming ten AUC
definitions were counted as coverage while unable to fail.  Running this
cross-check refuted it 11 times out of 13 -- those definitions reject mutants
freely.  The genuinely vacuous set was TWO, confirmed by two independent
methods instead of asserted by one.  A stronger claim about a smaller set.

    LIVE + mutants caught          -> both instruments agree the check works
    INTRINSIC + no mutant caught   -> genuinely vacuous, and now double-sourced
    INTRINSIC + mutants caught     -> the check discriminates anyway; the
                                      vacuity verdict says nothing about
                                      coverage, which is the whole lesson above

=== WHY THE UNSCORABLE GUARD IS NOT OPTIONAL ===

The first version of this script printed `agree=71, disagree=41` HAVING
COMPILED NOT ONE MUTANT: it passed an empty namespace to `compile_mutant` (so
every mutant raised), and iterated `mutants()` as if it yielded bare bodies
when it yields (tag, body) pairs.  Every mutant silently failed, `caught`
stayed 0 everywhere, and "0 caught" was then scored as agreement with "cannot
fail".  All 71 agreements were the tautology 0 == 0.

That was the tenth instrument in one day to return a credible number while
measuring nothing.  So a row with zero compiled mutants is UNSCORABLE here,
never scored, and `--selftest` DEMONSTRATES the refusal firing rather than
asserting it -- a guard nobody has watched fire is a guard nobody should trust.

Run:  python xcheck.py            cross-check against results_vacuity.json
      python xcheck.py --selftest exercise the refusal path, exit nonzero on
                                  failure
"""
from __future__ import annotations

import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
REJECT = {"escape", "escape-unguarded", "escape-outside-theorem"}


def score(rows):
    """rows: [(name, vacuity_verdict, n_tried, n_caught)] -> (summary, detail).

    Pure, so the refusal path can be exercised without compiling anything.
    """
    agree = disagree = unscorable = 0
    detail = []
    for name, v, tried, caught in rows:
        if tried == 0:
            unscorable += 1
            detail.append((name, v, 0, 0, "UNSCORABLE"))
            continue
        predicted = (v == "LIVE")          # LIVE predicts the gate catches one
        observed = caught > 0
        ok = (predicted == observed)
        agree += ok
        disagree += (not ok)
        detail.append((name, v, tried, caught, "AGREE" if ok else "DISAGREE"))
    return dict(scored=agree + disagree, agree=agree, disagree=disagree,
                unscorable=unscorable), detail


def selftest():
    """Show the refusal firing, and show the scorer working when it should."""
    ok = True

    # (1) Every row unscorable -> refuse, and score nothing.
    s, d = score([("a", "INTRINSIC", 0, 0), ("b", "LIVE", 0, 0)])
    if not (s["scored"] == 0 and s["unscorable"] == 2
            and all(r[4] == "UNSCORABLE" for r in d)):
        print("FAIL: zero-mutant rows were scored instead of refused"); ok = False
    else:
        print("pass: 2 zero-mutant rows -> UNSCORABLE, scored=0 (refusal fires)")

    # (2) The old bug, replayed: had these been scored, 0==0 would have made
    #     the INTRINSIC row 'agree'. Assert it does NOT.
    _s2, d2 = score([("intrinsic_no_mutants", "INTRINSIC", 0, 0)])
    if d2[0][4] == "AGREE":
        print("FAIL: reproduced the 0 == 0 tautology"); ok = False
    else:
        print("pass: INTRINSIC with 0 mutants is not scored as AGREE")

    # (3) POSITIVE CONTROL on the scorer: with real counts it must still
    #     discriminate, or the refusal above would be the only thing it does.
    s3, d3 = score([("live_caught", "LIVE", 5, 2),
                    ("live_missed", "LIVE", 5, 0),
                    ("intr_clean", "INTRINSIC", 5, 0),
                    ("intr_caught", "INTRINSIC", 5, 3)])
    want = ["AGREE", "DISAGREE", "AGREE", "DISAGREE"]
    if [r[4] for r in d3] != want or s3["scored"] != 4:
        print(f"FAIL: scorer verdicts {[r[4] for r in d3]} != {want}"); ok = False
    else:
        print("pass: scorer separates AGREE/DISAGREE on real counts")

    print("SELFTEST", "OK" if ok else "FAILED")
    return 0 if ok else 1


def main(argv):
    if "--selftest" in argv:
        return selftest()

    import backends
    import compile_defs as C
    from check_ranges import check_one as range_check
    from demo_falsifiable import arg_swap_mutants, compile_mutant

    vac = HERE / "results_vacuity.json"
    rows_in = {r["name"]: r for r in json.loads(vac.read_text())}
    defs = C.load_defs()
    cs, _why, text = C.compile_all(defs)
    ns = {"backends": backends}
    exec(compile(text, "<corpus>", "exec"), ns)   # the REAL namespace
    by_name = {c.d["name"]: c for c in cs.values()}

    # INCONCLUSIVE is included deliberately: interval arithmetic failing to
    # decide a definition says nothing about whether the check discriminates,
    # and the gate can often score it directly.
    want = ("INTRINSIC", "BOX-VACUOUS", "LIVE", "INCONCLUSIVE")
    measured = []
    for name, r in sorted(rows_in.items()):
        if r["verdict"] not in want:
            continue
        c = by_name.get(name)
        if c is None:
            continue
        d = c.d
        muts = C.mutants(d.get("body") or "") + arg_swap_mutants(d)
        tried = caught = 0
        for _tag, body in muts:
            try:
                mc = compile_mutant(defs, ns, d, body)
                mc(backends.FLOAT, *[0.3] * len(c.names))
            except Exception:
                continue
            tried += 1
            try:
                mr = range_check(mc, defs, budget=1200, bnb=300, use_z3=False)
            except Exception:
                continue
            if mr.get("verdict") in REJECT:
                caught += 1
        measured.append((name, r["verdict"], tried, caught))

    summary, detail = score(measured)

    print(f"{'definition':46s} {'vacuity':13s} {'muts':>5s} {'caught':>7s}  verdict")
    for n, v, t, ca, s in detail:
        print(f"{n[:46]:46s} {v:13s} {t:5d} {ca:7d}  {s}")

    print(f"\nscored={summary['scored']}  agree={summary['agree']}  "
          f"disagree={summary['disagree']}  "
          f"UNSCORABLE(0 mutants compiled)={summary['unscorable']}")

    # Per-category, counted by EXACT verdict.  `grep -c AGREE` does not work
    # here: it also matches DISAGREE, and reading the table that way overstates
    # agreement by exactly the disagreement count.  Same silent-truncation
    # class as `grep -o` eating a trailing subscript from a lemma name -- a
    # measurement that quietly answers a broader question than the one asked.
    print("\nby category (exact match, not substring):")
    for cat in want:
        rs = [r for r in detail if r[1] == cat]
        a = sum(1 for r in rs if r[4] == "AGREE")
        dis = sum(1 for r in rs if r[4] == "DISAGREE")
        un = sum(1 for r in rs if r[4] == "UNSCORABLE")
        if rs:
            print(f"  {cat:13s} rows={len(rs):4d} agree={a:4d} "
                  f"disagree={dis:4d} unscorable={un:4d}")

    # The two-instrument agreement that actually establishes vacuity.
    both = [r for r in detail
            if r[1] in ("INTRINSIC", "BOX-VACUOUS") and r[4] == "AGREE"
            and r[2] > 0]
    print(f"\nVACUOUS BY BOTH INSTRUMENTS ({len(both)}) -- cannot violate on "
          f"admissible input AND rejects no mutant:")
    for n, v, t, ca, _s in both:
        print(f"   {n}  [{v}]  {t} mutants tried, 0 caught")

    (HERE / "results_xcheck.json").write_text(
        json.dumps(dict(summary=summary,
                        detail=[dict(name=n, vacuity=v, tried=t, caught=c,
                                     verdict=s) for n, v, t, c, s in detail]),
                   indent=1))
    if summary["scored"] == 0:
        print("\nREFUSING TO REPORT AGREEMENT: not one mutant compiled, so "
              "every 'caught=0' is a tautology rather than a measurement.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
