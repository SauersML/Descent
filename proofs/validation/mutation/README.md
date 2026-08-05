# Proof mutation: the delete-and-rebuild half of the unused-hypothesis scan

`proofs/validation/code/Check.lean` gates on hypotheses that occur nowhere in a
theorem's kernel-accepted proof term. That check is exact and free, and it is
**blind to tactic proofs**: `omega`, `linarith`, `simp_all`, `aesop`, `decide`,
`positivity`, `field_simp`, `tauto` and `grind` splice every hypothesis in scope
into the certificate they emit, so a hypothesis they did not need still occurs
in the term.

This directory closes that direction the only way it can be closed — by removing
the binder and rebuilding. That is far too slow to gate (it re-elaborates
thousands of tactic proofs), so it is an instrument you run, not a check that
runs itself.

## Invocation

From the repository root, on a machine with a built corpus:

    bash proofs/validation/mutation/run.sh one    # one mutant per Prop binder
    bash proofs/validation/mutation/run.sh all    # one mutant per theorem, all binders dropped

`JOBS=24` caps parallelism. Each mode emits one probe module per source module,
elaborates them in parallel, scores them, and deletes the probes. Runtime is
roughly one corpus rebuild.

## What a result means, and what it does not

A mutant that **compiles** is a kernel-checked proof that the theorem holds
without that binder. A mutant that **fails** proves nothing — the tactic may
simply have taken a different route with the hypothesis present, or the example
may have failed to resolve a name. Both counts are therefore **lower bounds**,
with no false-positive direction.

**`one` and `all` are not interchangeable, and this is the important caveat.**
This instrument is *derivability*-based: a mutant compiles when the tactic can
re-derive the dropped hypothesis from the survivors. So hypotheses that are each
individually droppable are frequently **not** jointly droppable, and a report
from `one` licenses removing exactly one binder — never two. (The scan in
`Check.lean` is different and carries no such hazard: a binder absent from the
accepted proof term is absent from an object that still type-checks, so any
number of them may go at once.) `all` is the mode that answers the joint
question, and it has to be run to answer it.

## Calibration, and the three ways this instrument was wrong before it was right

Five probes are planted in **every** probe module. Any file failing one is
scored VOID and excluded, and `score.py` prints each axis with the value it must
have.

| probe | must | catches |
|---|---|---|
| `CALIB-DROPPABLE` | compile | scoring that never reports a success |
| `CALIB-NEEDED` | fail | scoring that reports everything as success |
| `CALIB-FRESH` | fail | a stale log |
| `CALIB-TAIL` | fail | message-cap truncation |
| `CALIB-AUTOIMPLICIT` | fail | `autoImplicit` silently back on |

Each of the last three exists because of a defect that produced a wrong number
first. They are recorded because the failure mode is more instructive than the
result:

1. **An anchored error regex.** Lake writes `error: <path>:l:c:`; a direct
   `lake env lean` writes `<path>:l:c: error:`. A `^<path>` anchor matched
   neither, no error was ever found, and the first vacuity run reported **every**
   theorem as defective. Caught by `CALIB-NEEDED`.
2. **The message cap.** Lean stops after `maxErrors` (default 100) per file and
   says so on line 0. Verdicts are span-based — "no error inside this mutant's
   span" means "it compiled" — so every mutant past the 100th error was scored
   as compiling. 24 of 101 files were truncated, and the one-at-a-time count read
   **901** instead of 34. The calibration at the time did not catch it *because
   all three probes sat at the top of every file, where truncation cannot reach*.
   A calibration placed where the failure mode cannot occur certifies nothing.
   Hence `CALIB-TAIL`, at the end of the file. Note that `set_option maxErrors`
   **inside** the file does not work: the limit is read from the initial options,
   before the file's commands run, so it must be a command-line `-D`.
3. **`autoImplicit`.** Moving from `lake build` to `lake env lean` to lift the
   cap dropped the library's `leanOptions`, turning `autoImplicit` back on — so a
   dropped binder came back as a fresh implicit variable and the mutant compiled
   vacuously. The count read 46 instead of 34, and included a theorem with no
   Prop binder at all. Hence `-DautoImplicit=false` and `CALIB-AUTOIMPLICIT`.

Every one of the three was found by disbelieving a specific surprising hit and
going to look at the probe, not by the calibration that existed at the time. The
calibration is what makes the *next* run trustworthy.

## Result at the time of writing

Against the corpus at `9074b70d`, with all five axes passing and zero VOID files:

    one:  MUTANTS 3228   DROPPABLE 34
    all:  MUTANTS 1300   UNCONDITIONAL 11

**None of the 11 is a hollow statement, and none should have its hypotheses
deleted.** Every one is a divisor guard (`≠ 0`, `0 <`) or a natural-subtraction
guard, and the identity survives dropping it only because Lean's `x / 0 = 0` and
truncated `ℕ` subtraction make both sides degenerate the same way off-domain.
`max_reciprocal_half_eq_two_div` is typical: at `total = 0` the left side is
`max (1/0) (1/0) = 0` and the right side is `2/0 = 0`, so the equation holds for
a reason that has nothing to do with what it says. Deleting these guards would
quietly extend each statement across the junk point that `Check.lean`'s JUNK
scan exists to flag — the reverse of an improvement.

So the honest reading of "all hypotheses droppable" is much weaker than it
sounds in a total type theory, and this instrument's own headline number is the
example. Treat a hit as a question ("why is this true off-domain?"), not as a
finding.
