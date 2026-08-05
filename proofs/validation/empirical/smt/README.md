# SMT attacks on theorem STATEMENTS

The rest of `empirical/` tests what definitions **compute**. This directory
tests what theorems **say**.

    python3 sweep.py selftest      # calibration, both directions
    python3 sweep.py scan          # corpus sweep for vacuous / tautological statements
    python3 run_statements.py      # the hand-translated statement corpus

Needs `z3-solver`. **Status: DIAGNOSTIC** — not gated in `prover.yml`; see the
"WHAT IS NOT WIRED UP" note there for the reason and for what promoting it
would take.

## The finding that shaped this directory

The corpus has **no `sorry` and no custom `axiom`**. Every statement in it is
kernel-checked, so no statement can be false and counterexample search against
statements has nothing to find. Measured 2026-08-04:

| probe | result |
|---|---|
| vacuous statements | **0** of 1861 checkable hypothesis-carrying theorems |
| tautological conclusions | **0** of 1065 checkable |

That is a real result about the corpus, not a failed search — but only because
`sweep.py selftest` asserts both directions. A detector reporting zero is
otherwise indistinguishable from a blind one.

The defects that survive a valid proof are **definitions that are true-but-wrong**:
a def encoding a direction, an inverse, or a ratio, written the wrong way round.
Nothing is false — the theorems are all true *about the wrong function*. That
class is caught by the exact-arithmetic round trips in
`../differential/checks.py`, not here.

## Why UNSAT-only reporting is what makes the sweep sound

There is no verified Lean→SMT translator here and there will not be one. Instead
every untranslatable construct becomes something **strictly more permissive**:
unknown definitions become uninterpreted real functions, unparseable hypotheses
are *dropped*, unknown subterms become fresh unconstrained reals. Relaxing
hypotheses only enlarges the model set, so

* hypotheses alone UNSAT ⇒ genuinely **vacuous**,
* negated conclusion UNSAT with no hypotheses ⇒ genuinely **tautological**,
* `H₋ᵢ ∧ ¬hᵢ` UNSAT ⇒ `hᵢ` genuinely **redundant**.

`SAT` carries **no** information under this encoding and is never reported.

## Limitations, stated because they are easy to over-read

* **UNSAT is not a proof of the Lean statement.** Lean quantifies over
  structures, carries `x / 0 = 0`, and ranges over types this encoding flattens
  to `Real`. The sound direction is the other one: a SAT model on a *hand*
  translation (`statements.py`) is a genuine counterexample.
* **The sweep cannot tell you a statement is fine**, only that it failed to
  prove it degenerate.
* **The redundancy probe removes one hypothesis at a time.** Hypotheses that
  are each individually redundant are frequently not *jointly* redundant, so
  this output does **not** license removing several at once. The sound way to
  drop premises is to scan the kernel-accepted proof term for binders that do
  not occur in it — and even that is only valid against the statement it was
  computed on. A correct trim and a correct inversion, applied concurrently to
  `am_correction_increases_portability`, combined into a false theorem for
  exactly that reason.
* **A timeout is not a clean result.** `unknown` is reported as UNKNOWN and
  fails the run.

## Files

| file | what it is |
|---|---|
| `statements.py` | hand-translated statements, each carrying its `fqn`, its expected verdict, and its witness if false. Anchored to declaration names, never line numbers. |
| `run_statements.py` | runs them; exits nonzero when any pinned verdict changes |
| `sweep.py` | corpus-wide vacuity / tautology sweep, plus its own calibration |
| `leansmt.py` | the deliberately-over-permissive Lean-subset translator |

`statements.py` pins known-**false** statements as expected-false on purpose. If
one starts verifying, either the encoding broke or somebody added a hypothesis
that quietly rules the witness out — both are regressions, which is why they are
pinned rather than deleted.
