# Regenerating the coverage number

## Why this file exists

`report.py` reads artifacts that other stages write. Those artifacts are not in git, and
`compile_defs.check_fresh` refuses to count a result whose definition table has changed
underneath it — correctly, because a coverage figure computed against a stale table is worse
than no figure.

The failure mode this produces is silent and was observed: in a clean checkout, or after any
rename in `proofs/Calibrator`, `report.py` prints

```
covered BY THIS CHECKER .................. 0  (0.0%)
residue by stage:
   1391  no-derivable-check
```

Nothing is wrong with the corpus when it says that. The stages simply have not been run in
order. Reading that `0` as a corpus property is the mistake, and the number is quoted in enough
places that the mistake is easy to make.

## The order

Run all four from this directory. Each writes what the next one reads.

```
python3 extract_defs.py     # proofs/Calibrator -> defs.json
python3 compile_defs.py     # defs.json -> callables, per backend
python3 check_theorems.py   # the corpus's own theorems as discriminating checks
python3 check_ranges.py     # declared ranges and their escapes
python3 report.py           # the coverage figure
```

`check_invariants.py` (metamorphic invariants and the junk-branch scan) and
`check_simulation.py` (external reference) are independent of the coverage figure and can be run
at any point after `compile_defs.py`. The junk-branch scan is the one that finds a division by a
quantity that reaches zero through a chain of definitions — a text search cannot, because it
would have to unfold the chain.

## What the figure meant on 2026-08-03

```
definitions in proofs/Calibrator ......... 1391
covered BY THIS CHECKER .................. 368  (26.5%)
not reached by THIS CHECKER .............. 1023
residue by stage:  922 transpile, 101 no-derivable-check
```

`unreachable.py` splits the 1023 into `907 corpus` and `116 checker`, and that split is the part
worth reading. **The uncovered majority is not a checker deficiency.** A definition is
corpus-unreachable when nothing states a property about it and its name denotes no simulatable
quantity — which is what most of the abstract material is, and no numeric tier will ever reach
it. Raising 26.5% by attacking the 907 is not available.

The 49 definitions that are transpilable *and* checker-limited are the live work list, and
`unreachable.py` prints them by name. Those are the ones where a check could be derived and is
not.

## The rule this encodes

A coverage number is a joint property of the corpus and the tool, never of the corpus alone.
Quoting it without saying which tool, at which freshness, is how `0.0%` and `26.5%` both get
attributed to the same corpus on the same day.
