# Raw cluster run output

Captured verbatim. Nothing here is summarised, and nothing here should be read
as a finished result unless its own header says the run completed.

## `out_stability_partial.txt` — INCOMPLETE, RUN STILL IN FLIGHT

Seed-stability sweep, 39 specs x 8 independent point-sets. **3 of 39 specs
done at the time of capture.** Pushed mid-run under a save order, with its
incompleteness named rather than waiting for a clean number.

What it says so far: the three specs reported agree on 8 of 8 point-sets. That
is three data points and it establishes nothing about the other 36. In
particular it does NOT yet re-establish the two admixture-LD specs that were
found flickering at 4/8 and 5/8 before the standard-error fix — those are
later in the list.

Why it is slow: the Wright-Fisher specs use 40,000 replicates over a couple of
hundred generations and take roughly eight minutes each. That is real waste and
the fix is the replicate count, but only AFTER this run lands. Changing the
sampler during a sampling-stability test is the one change that would
invalidate the result.

**Until this completes, every external-reference verdict this tier has issued
is of unknown reproducibility.** That is the consequence of the `hash()`
seeding bug found earlier, and this sweep is what discharges it.

## `out_theorems_equalsfix.txt` — COMPLETE

Theorem tier after adding `=` to the tokeniser's operator set. The tier had
never parsed a Lean equality, because bare `=` was absent from the operator
alternation while `==` and the unicode comparisons were present.

    statements parsed              2248
    usable                          427  ->  680
    hold numerically                426  ->  679
    disagree with the checker         0  ->    1
    definitions discriminated       221  ->  319

The single disagreement was a double-precision overflow in an identity that is
exact over the reals, not a semantic failure, and is fixed separately — a
comparison on a non-finite value now returns undecided in both theorem
backends. A rerun measuring that is in flight and is not captured here.

The +98 discriminated definitions are **internal consistency**, not
validation. Lean admits no false theorem, so this discovers nothing; it
establishes that a wrong body would have been caught, and moves those
definitions out of "nothing in the corpus states a property of this".
