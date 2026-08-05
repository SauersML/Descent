"""Attack the hand-translated statements in `statements.py` with z3.

    python3 run_statements.py            # calibration + corpus, exits nonzero on regression

STATUS: DIAGNOSTIC.  Not wired into prover.yml as a gate, because it needs z3
(see the "WHAT IS NOT WIRED UP" note in .github/workflows/prover.yml, bucket 3)
and because an SMT query has no reproducible time bound on every machine.  It
is deterministic in verdict and takes well under a second on the pinned set, so
promoting it later is a matter of accepting the dependency, not of fixing
flakiness.

WHAT IT DOES.  For each statement it runs two probes:

    VACUITY      hypotheses alone.  UNSAT => the hypotheses contradict each
                 other => the theorem is vacuous and proves nothing.
    COUNTEREXAMPLE   hypotheses AND the negated conclusion.  SAT => a model is
                 a machine-checked counterexample.

TIMEOUTS ARE NOT CLEAN.  `unknown` from z3 is reported as UNKNOWN and is
treated as a failure of the run, never folded into "no counterexample found".
The precedent this avoids is `invariants/check_ranges.py`, which prints its
findings and exits 0 whatever it finds, so as a gate it catches nothing but its
own crashes.

WHAT UNSAT DOES AND DOES NOT MEAN.  UNSAT over the reals is strong evidence and
not a proof of the Lean statement: Lean quantifies over structures, carries
`x/0 = 0`, and may range over types this encoding flattens to `Real`.  The
direction that is sound is the other one -- a SAT model is a genuine
counterexample, and that asymmetry is why only SAT and UNKNOWN are ever
escalated here.
"""
from __future__ import annotations

import sys

try:
    from z3 import Solver, Real, Not, sat, unsat, unknown
except ImportError:                                        # pragma: no cover
    print("z3 is not installed; this is a DIAGNOSTIC check, so that is not a "
          "failure. Install with: pip install z3-solver")
    raise SystemExit(0)

import statements as S

TIMEOUT_MS = 5000


def _vars(st):
    return {n: Real(n) for n in st.vars}


def probe(st) -> tuple[str, dict | None]:
    """Returns (verdict, model) with verdict in HOLDS | FALSE | VACUOUS | UNKNOWN."""
    v = _vars(st)

    sv = Solver()
    sv.set("timeout", TIMEOUT_MS)
    for h in st.hyps:
        sv.add(h(v))
    r = sv.check()
    if r == unknown:
        return "UNKNOWN", None
    if r == unsat:
        return "VACUOUS", None

    sc = Solver()
    sc.set("timeout", TIMEOUT_MS)
    for h in st.hyps:
        sc.add(h(v))
    sc.add(Not(st.concl(v)))
    r = sc.check()
    if r == unknown:
        return "UNKNOWN", None
    if r == sat:
        m = sc.model()
        return "FALSE", {str(d): str(m[d]) for d in m.decls()}
    return "HOLDS", None


def main() -> int:
    rows, bad = [], []
    for st in S.STATEMENTS:
        got, model = probe(st)
        ok = (got == st.verdict)
        rows.append((st.key, st.verdict, got, ok, model))
        if not ok:
            bad.append((st, got, model))

    width = max(len(r[0]) for r in rows)
    print(f"{'statement':<{width}}  {'expect':<8} {'got':<8} ")
    print("-" * (width + 20))
    for key, want, got, ok, model in rows:
        print(f"{key:<{width}}  {want:<8} {got:<8} {'' if ok else '  <== MISMATCH'}")
        if model and got == "FALSE":
            print(f"{'':<{width}}  witness: {model}")

    n_calib = sum(1 for s in S.STATEMENTS if not s.fqn)
    print(f"\n{len(S.STATEMENTS)} statements ({n_calib} calibration, "
          f"{len(S.STATEMENTS) - n_calib} from the corpus)")

    if bad:
        print("\nREGRESSIONS -- a statement stopped producing its pinned verdict:")
        for st, got, model in bad:
            print(f"  * {st.key}: expected {st.verdict}, got {got}")
            if st.fqn:
                print(f"    declaration: {st.fqn}")
            if got == "UNKNOWN":
                print("    z3 returned unknown (timeout or incompleteness). "
                      "This is NOT a clean result and is never reported as one.")
            if st.verdict == "FALSE" and got == "HOLDS":
                print("    A statement pinned FALSE now verifies. Either the "
                      "encoding broke or a hypothesis was added that rules the "
                      "witness out. Both are regressions.")
            print(f"    {st.note}")
        return 1

    print("all statements produced their pinned verdicts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
