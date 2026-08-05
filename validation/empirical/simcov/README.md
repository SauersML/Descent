# simcov — the simulation-coverage harness and its verdict ledger

**This directory is the source of truth.** The working copy on the cluster is a
checkout of it, not the other way round. Everything a verdict rests on — the
battery that produced it, the result file it produced, the ledger record the
guard reads — is committed here.

## What is gated, and what deliberately is not

`.github/workflows/prover.yml` documents why Monte-Carlo suites are not required
checks: a statistical verdict carries a false-failure rate, and a randomly
failing required check is a check people learn to ignore. **The batteries stay
ungated.** What is gated is the LEDGER — `check.py --only ledger` — which reads
committed records and corpus source text, needs no simulator, no numpy and no
network, and runs in well under a second.

That is the valuable half. The failure modes this project actually hit are all
bookkeeping:

* batteries ran ahead of the docstrings, so definitions carried a real verdict
  and still read `Empirical status: UNTESTED`;
* docstrings ran ahead of the batteries, so definitions read VALIDATED off a
  MATCH that no competing formula was ever run against;
* a docstring cited a battery whose results were never committed, or whose
  source had been edited since the run.

None of those needs a simulation to detect. All of them need the records to be
committed and schema'd.

## The competitor gate is structural

An oracle algebraically pinned to the body under test cannot reject a competing
formula, so agreement with it is arithmetic, not evidence. `driftVariance`,
`haplotypeHomozygosity` and `multiTraitEffectiveSampleSize` were each banked as
validations that way.

`ledger.py` therefore applies the gate **at emit time**: a corpus row that agrees
with its oracle while no competing formula was rejected on the same cells is
recorded as `UNINFORMATIVE`, never as `MATCH`. A battery author cannot forget it,
and the rule applies retroactively to every result file already on disk. Of the
MATCHes in the corpus's history, most are uninformative under this rule; that
number is printed by `ledger.py` and by the guard, and it is the honest state of
the evidence rather than a regression.

Roles are decided on the **transcribed formula**, not on the bracket tag: a row
is a corpus row if its name is bare, or if it is tagged but transcribes the same
`source` as a bare row (a regime split). There are 118 distinct tags and no
grammar, so tag-parsing is guesswork — and a tagged row with no bare sibling used
to be filed as a corpus row, which is how `calibratedBrier` and
`islandFstFiniteDemes` came to carry falsifications that were really their
competitors' verdicts.

## Freshness is a field, not a habit

Two independent routes, because the self-reported one only exists for batteries
written after the requirement:

* **self-reported** — a battery prints `FRESHNESS=OK` only when its own source
  carries a token that exists nowhere else, so its log is evidence about *which*
  source produced the numbers;
* **mtime** — if the results file is older than the battery source, the numbers
  came from a source that no longer exists. Computable for every battery ever
  written, needs no re-run.

STALE beats OK: a battery whose source was edited since the run is stale however
cheerfully its old log reported otherwise. A docstring may not cite a stale
battery.

## Files

| file | what it is |
|---|---|
| `battery_*.py` | the batteries. Ungated; run them on a cluster. |
| `battery_*_results.json` | their output, committed. |
| `battery_core.py`, `simlib.py` | the `record()` entry point and the simulation helpers. |
| `verdict.py` | the verdict gates: self-test, generative self-test, no power, degenerate oracle, missing control, weak error bar. |
| `inventory.py` | the coverage denominator. Transcribes `check.py`'s own empirical-claim screen on purpose — a denominator that disagrees with the guard's is a number nobody can check. |
| `ledger.py` | emits `ledger.json` from the result files, applying the competitor gate and freshness. |
| `ledger.json` | **generated and committed.** Regenerate with `python3 ledger.py <results-dir>`. |
| `adjudications.json` | **hand-written.** One entry per definition carrying contradictory verdicts, naming the authoritative battery and the defect in the other design. Regenerating the ledger never discards it. |
| `crossref.py` | cross-references result files against `inventory.json`; diagnostic. |
| `identity_probe.py` | **not an identity detector, despite the name.** See below. |

## `identity_probe.py` does not do what its name says

It separates a **biased approximation** from **exact agreement**, by rerunning a
cell at `N` and `16N` and reading whether `z = |lean-truth|/sem` grows. A real
bias makes `z` grow; an identity keeps `z` at O(1) forever. But an exact law with
truly zero bias behaves identically to an identity under that test, and the probe
reports that case as INCONCLUSIVE.

So it can say "this disagreement is real even though it looks small". It cannot
say "this agreement is an identity". Its 4/4 calibration is a calibration of the
bias/no-bias split, not of identity detection. **Never use it to clear a MATCH.**
The thing that clears a MATCH is a rejected competitor, which is what the ledger
gate enforces.

## Coverage is over what is OWED, not over what is screened

`inventory.py` prints three numbers and the third is the one that means
something. `validation/conventions.json` defines the closed vocabulary, and it
says of three of its terms that no measurement is claimed or needed:

| term | what it says |
|---|---|
| `DERIVED` | Follows from other results in the corpus. |
| `VACUOUS` | The measurement was an algebraic identity. |
| `ASSERTED` | An input taken from external literature. |

A denominator counting those as debt reports the corpus as less covered than it
is. **The exclusion is not free.** A `DERIVED` marker that names nothing it
follows from is an assertion, not a derivation, so the scan requires a
backticked identifier in the status paragraph and keeps the rest in the
denominator. Five markers failed that on the first run and each was either
substantiated or reclassified.

Two parsing faults were fixed at the same time: `CONVENTION PINNED` is a
two-word head and was being read as the bare state word `CONVENTION`, and the
head rule never reached the vocabulary branch for any two-word term whose first
word is also a state word.

## Outstanding, and not this harness's to close

`Descent/Core/` and `Descent/Coalescent/` were created after this scan was last
run and their declarations carry no per-declaration `Empirical status:` marker.
`Core/Fst.lean` states one at MODULE level -- "None. The bodies here are
algebra" -- which is the right verdict and which neither this scan nor
`check.py`'s `ident` guard can see, because both anchor on the docstring
immediately above a `def`. Fifteen declarations are in that state. They are the
whole of the remaining coverage debt.

## Regenerating

```
python3 validation/empirical/simcov/ledger.py <dir-with-results> \
    -o validation/empirical/simcov/ledger.json
python3 validation/code/check.py --only ledger
python3 validation/code/test_ledger.py     # calibration, both directions
```

`test_ledger.py` plants a wrong formula, an uncompeted identity, a hand-edited
ledger, a dangling citation, a stale citation and a clean corpus, and asserts
that the first five are caught and the last produces nothing. A guard with no
calibration is a guard nobody can quote.
