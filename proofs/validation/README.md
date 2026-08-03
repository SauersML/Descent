# Validation

This directory holds the instruments. A Lean proof says a formula follows from
its assumptions. Nothing in Lean says the assumptions describe a real
population, so every formula that claims to describe one needs a simulation
that could contradict it.

## Regenerate the extraction tables before you run anything

Seven files under `extract/` are generated from the Lean sources and are not
tracked:

    defs.json  classes.json  reconcile.json  regime.json
    ceiling.json  coverage.json  lean_defs.py

They are untracked on purpose. A committed cache that drifts against its source
is not a cache, it is a second source of truth that disagrees with the first,
and this one had drifted by six figures of changed lines before anyone noticed.

Regenerate them in whichever tree you are about to run, from a corpus that
builds:

    python3 proofs/validation/extract/emit.py

Consumers fail loudly rather than reading a stale table. If a script stops with
`defs.json missing`, that is the design working. Run `emit.py` and try again.

## What a result file must carry

Use `simprov.py`. Every output records the git revision, whether the working
tree was clean, a timestamp, the seed and the replicate count.

A result that cannot name the revision it describes is a number, not a
measurement. Two claims on the public page survived for months because their
only record was a commit message, and one of those messages named three
declarations that did not exist in the tree it described.

Report a standard error with every estimate, and write one record per replicate
rather than per-cell aggregates alone. Aggregates hide scatter. One portability
condition returned 0.343, 0.370 and 0.639, so its three-replicate mean carried
a scatter as large as the effect it claimed to measure.

## Every simulator needs a control

A simulator with no control cannot separate a real agreement from a broken
harness. Follow `fold_search`, which records a fold both present and excluded,
or `fam_selection` and `fam_ascertainment`, which carry their own.

This matters more here than the general argument suggests. Several instruments
in this repository returned credible numbers while measuring nothing, and none
was caught by reading it. Each fell to a deliberate falsification, to a second
instrument that disagreed, or to a number that could not be true.

## Compare, do not overwrite

Some families already carry a stored result from an earlier run. Write a fresh
run somewhere else and diff it. Agreement raises confidence in both. A
disagreement is a finding, and it needs both numbers and both revisions.

Overwriting destroys the only cross-check available, and a stored result whose
script no longer runs is exactly the case where the comparison is worth most.

## Coverage counts three different things

`differential/cluster/families.py` counts model families. The filesystem counts
scripts. The two disagree because the mapping runs many-to-many in both
directions: one script serves three families, another serves two, and one
family is served by two scripts together. Neither number means anything unless
you say which unit it counts.

The number to drive down first is families with no simulator, because a family
with none is a blind spot with many statements behind it and it is invisible in
any per-definition percentage. The number to drive down second is statements
belonging to no family at all: nobody has yet said what generative process
those are claims about.

## Do not run these on a login node

The compute is shared. Submit to a partition, keep the core count modest, and
say in the result which revision and which node produced it.

## Verify your own tooling, and make the verification able to fail

A verification step that cannot fail loudly will eventually certify the wrong
thing. Four separate failures in one day shared this shape, and the sharpest was
not in the corpus at all but in the wrapper used to measure it.

`scripts/cluster-lean-build.sh` hardcoded the shared checkout, so measuring a
clean clone meant rewriting one line with `sed`. Then the script gained
`GNOMON_REPO` support and the rewritten line stopped existing. The `sed` matched
nothing, exited 0, and produced a byte-identical copy of the script. Running
that copy would have built the STALE SHARED CHECKOUT and reported it as the
corpus at a revision it had never seen: a plausible number, precise-looking, and
about the wrong tree. It was caught only because the diff between original and
rewritten script was printed and required to be non-empty.

The rule: after transforming a file, assert that the transformation changed
something. `sed`, `grep -v`, a filter, a patch applied with fuzz -- each exits 0
on a no-op. Print the diff, count the lines, check the marker; anything that
turns silence into an error.

The same shape, three more times the same day:

  * A build verified with `lake build Calibrator.QuadraticShift` broke the root
    module. Building a leaf never elaborates the root, so the build that was run
    could not have exercised the edit that broke it. Name the target that
    actually contains the change; for a root or import change, that is the root.
  * A 25-second probe harness collected stderr only. A family that reports a
    failed check on STDOUT and exits nonzero was recorded as crashing. Capture
    both streams: for some scripts a nonzero exit is a measurement outcome, not
    an error.
  * A guard's real finding sat at the bottom of a long advisory list and went
    unread for hours. A finding that is not surfaced is functionally invisible;
    lead with the verdict, not the log.
