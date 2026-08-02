# Range and invariant checks over `proofs/Calibrator`

Bulk validation that runs in seconds and needs no simulation. Two families:

**Range escapes.** A definition whose name forces a range — a probability in
`[0,1]`, a correlation in `[-1,1]`, an F_ST in `[0,1]`, a variance nonnegative —
is searched over its admissible box for a point where the transcribed body
leaves that range.

**Metamorphic invariants.** Relations between the value at one input and the
value at another, so no reference value is needed: symmetry under swapping two
populations, invariance under rescaling every second moment together, limits,
absorbing boundaries, asserted monotonicity, and continuity at the endpoints of
the box.

Nothing here runs Lean. Bodies are transcribed by a narrow transpiler
(`transpile.py`) that accepts the arithmetic fragment and **raises rather than
guesses** on anything else; what it rejects is reported, not skipped.

## Running

```
python extract_defs.py       # -> defs.json          (973 definitions)
python check_ranges.py       # -> results_ranges.json
python check_invariants.py   # -> results_invariants.json
python demo_falsifiable.py   # -> results_falsifiability.json
python report.py --findings  # -> coverage.json + the ranked defect list
```

Requires Python 3.11+ and nothing else. `z3` is optional and currently unused;
see *Method and its limits* below for what that costs.

## What "covered" means here

A definition is `covered: true` in `coverage.json` **only** if a check on it has
been demonstrated to be able to fail — either

* the check already rejects the body as written, so the body is its own
  counterexample, or
* a named mutant of the body (`const-off-by-one`, `negate`, `drop-max-guard`,
  `swap-args(p₁,p₂)`, …) is rejected, and that mutant is recorded in
  `falsifiability_evidence`.

Definitions whose checks survive every mutant are reported as **not covered**,
with the surviving mutants listed. A check that cannot fail covers nothing, and
counting it would convert an unknown into a false known.

## Verdicts

| verdict | meaning |
| --- | --- |
| `escape` | a concrete input point leaves the required range, and every coordinate of it is pinned by a theorem hypothesis or an unambiguous parameter name |
| `escape-unguarded` | same, but the witness needs a coordinate whose admissible values could not be determined — a weaker claim, never pooled with the above |
| `proved` | interval branch-and-bound covered the whole box. A proof, not a sample |
| `guarded-by-side-condition` | no escape inside the relational hypotheses the author stated in adjacent theorems; the range is **not** implied by the definition alone |
| `inconclusive` | search found nothing and the interval proof did not close. **Not** a pass |
| `no-range` | the name and docstring commit the definition to no particular range |
| `not-transpiled` | outside the arithmetic fragment; the reason is recorded |

## Where the admissible box comes from

In priority order, recorded per coordinate in `box_provenance`:

1. **Theorem hypotheses.** Numeric bounds (`0 < Ne`, `m ≤ 1`) become box edges;
   *relational* ones (`H_S ≤ H_T`, `D_sq ≤ var_tag * var_causal`,
   `total = between + within`) become side constraints on the search. Theorems
   rename arguments freely, so the application site is read to map theorem-local
   names back onto the definition's own parameters.
2. **The meaning of the parameter name.** `h2_true` is a heritability,
   `fstTarget` is an F_ST, `v_noise_s` is a variance.
3. **Nothing.** Then the definition is *unguarded* in that coordinate and it is
   reported as such. No box is invented to make a definition pass.

## Method and its limits

Read these before trusting a negative result.

* **A negative from the witness search is not a proof.** Sampling plus pattern
  search can miss a thin escape. Only `proved` (interval branch-and-bound) is a
  proof of containment, and it closes for 62 of the definitions it is tried on.
  Everything else that found nothing is `inconclusive`, deliberately.
* **z3 is not wired in.** The polynomial/rational fragment is decidable and an
  SMT backend would turn many `inconclusive` verdicts into decisions.
  `backends.py` is written against an abstract backend for exactly this reason;
  the Z3 backend is the obvious next increment.
* **Lean's junk values are reproduced, not repaired**: `x / 0 = 0`,
  `Real.sqrt x = 0` for `x < 0`, `Real.log x = 0` for `x ≤ 0`. Testing what is
  written is the whole point, and one finding here exists only because of them.
* **Range inference is heuristic.** It reads names. `xFromY` returns an *x*;
  `scaled…Rate` is a compound parameter and not a probability; a calibration
  *slope* above one is under-dispersion rather than an error; a matrix *trace*
  is not a rate. Those exclusions are in `semantics.RANGE_VETO` and each was
  added after a false positive, not before.
* **`escape-unguarded` findings are weaker than they look.** The witness may use
  a physically unreachable value for a coordinate whose meaning the name did not
  reveal. They are separated from `escape` for that reason and should be triaged
  by someone who knows what the parameter means.
* **The `continuity` check is broad but weak.** It applies to 637 coordinates
  and almost no mutation breaks it, so on its own it does not make a definition
  covered — and `demo_falsifiable.py` does not let it.
