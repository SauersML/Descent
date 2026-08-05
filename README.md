# Descent

A Lean 4 formalization of genetics, with a simulation harness that tests every
formula the corpus states against measurement.

The mathematics lives in `Descent/`. Everything in `validation/` exists to
attack it — because a proof assistant checks that a proof follows from a
statement, and nothing in it checks that the statement says what you meant.
Most of the defects found here were true theorems about the wrong quantity.

## Layout

| Path | What it is |
| --- | --- |
| `Descent.lean` | The root module. Every corpus module must be reachable from it, or `lake build` cannot validate it. |
| `Descent/` | The corpus: ~110 modules, one namespace, `autoImplicit` off. |
| `validation/code/` | Source-text and elaborated-environment guards over the corpus. |
| `validation/empirical/` | Simulations that evaluate the corpus's definitions numerically and compare them against independent implementations. |
| `validation/mutation/` | Mutation testing: drops hypotheses and checks the theorem stops compiling. |
| `validation/Shared/` | The generated-declaration filter and results writer the detectors share. |

`ValidationShared` is a separate Lake library on purpose. The detectors
`import Descent`, so anything they import has to build *before* the corpus
does; and a proof module must not be able to import its own auditor, which
putting these under the `Descent` root would permit.

## Building

```sh
lake exe cache get          # Mathlib oleans; do not build Mathlib yourself
lake build Descent ValidationShared
```

Naming only `Descent` leaves the shared oleans unbuilt and every detector step
fails on an unknown module.

## The rule the validation tier is built on

**A detector that reports nothing is indistinguishable from a broken
detector.** So no guard's silence counts as evidence until it has been asserted
in both directions: every planted defect caught, and no finding on clean
mathematics. That is why `test_check.py` runs before `check.py`,
`test_metamorphic.py` before `run.py`, and `test_battery_gate.py` before the
differential battery. A calibration also certifies only the region it occupies,
which is why several probes are planted at the *tail* of their real inputs —
truncation and early loop exits cannot be caught from the head.

Every guard budget is `0`. Budgets are not pinned to the current count to make
a check pass; a budget that tracks reality measures nothing.

Where a result is not proved, the corpus says `sorry`. A visible admission is
worth more than a weakened, conditional, or laundered statement that
technically compiles.

## What this repository does not check

The corpus was extracted from [gnomon](https://github.com/SauersML/gnomon),
where it was proved against a shipped Rust scoring implementation. Three CI
steps did that checking — a corpus/implementation correspondence table, its
calibration, and a cargo differential evaluating every mapped definition
against the real code — and all three read Rust that lives in gnomon.

They did not come along, and **until they run in gnomon against this corpus as
a dependency, nothing checks that the theorems here describe code that ships.**
That is a real gap, stated here rather than left to be discovered. Vendoring a
frozen copy of the Rust was the alternative and is worse: the table is anchored
on content hashes, so a copy that stops tracking gnomon stays green while
checking an implementation nobody ships.

## History

The commit history predates this repository. It was extracted from gnomon with
authors and timestamps intact, and begins in February 2026 — the corpus was
`Calibrator` under `proofs/` for most of that time, so older commits refer to
it by that name.

## License

Apache 2.0. See [LICENSE](LICENSE).
