# Detector results

Three files here, and each one is the ONLY result its detector has ever
produced. Nothing has superseded them.

    axioms.prev.txt      AxiomScan, captured stdout
    inflation.prev.json  Inflation
    rfl.prev.json        RflScan

## Read the .prev suffix as "compare the next run against this", not as "stale"

The suffix marks these as the baseline a fresh run gets diffed against. It does
not mean a newer result exists. At the time of writing no rescan has run, so
these three are the whole of what is known.

## What each one is worth, and what it is not

`axioms.prev.txt` is captured stdout, not a file the detector wrote. AxiomScan
emits no JSON. Its header carries a correction that matters more than its
numbers: `lake env lean` does not build, so the scan elaborated against object
files from an earlier revision than the source tree it was stamped with. Its
zero admitted proofs is true of the revision it compiled and false of the
revision it names. Source inspection of the current tree finds eight, and the
header names all eight by declaration.

A rescan must report exactly eight. Anything else is itself the finding and
outranks whatever else that run reports.

`inflation.prev.json` and `rfl.prev.json` were written by their detectors and
carry a revision, a run time and a working-tree state. Read `workingTreeClean`
before quoting either. When it is false, read the path list beside it: dirty
scratch files mean the numbers still describe that revision's tracked content,
and a dirty tracked source means they do not.

## AxiomScan uses a different filter from the other two

The other two share `Shared/DeclFilter.lean`. AxiomScan still carries its own
private copy, because the file was held by another session when the three were
unified. Its declaration count is therefore not directly comparable with theirs.

## The scope question is settled

The root imports 93 of 115 modules directly, and every one of the 115 is
reachable through the transitive closure. A direct-import count is not a
closure. No module is outside the reach of these detectors.
