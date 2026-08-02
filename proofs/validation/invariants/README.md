# Range and invariant checks over `proofs/Calibrator`

Bulk validation that runs in seconds and needs no simulation. Two families:

**Range escapes.** A definition whose name forces a range — a probability in
`[0,1]`, a correlation in `[-1,1]`, an F_ST in `[0,1]`, a variance nonnegative —
is searched over its admissible box for a point where the transcribed body
leaves that range.

**Metamorphic invariants.** Relations between the value at one input and the
value at another, so no reference value is needed: symmetry under swapping two
populations, invariance under rescaling every second moment together, limits,
absorbing boundaries, asserted monotonicity, continuity at the endpoints of the
box, and **totality artifacts**.

## The totality contract, in two clauses

Mathlib totalises partial operations: `x / 0 = 0`, `x⁻¹ = 0` at 0,
`Real.log 0 = 0`, `Real.log x = Real.log |x|`, `Real.sqrt x = 0` for `x < 0`.

1. A checking **tool** must not raise, or flag, merely because Lean returns 0
   where mathematics would be undefined. Doing so manufactures defects that do
   not exist. `backends.py` reproduces every one of these conventions, and is
   differential-tested against `extract/lean_rt.py` on 16000 random arguments.

2. Totality explains why the expression does not error. It does **not** make
   the resulting value defensible. Where the point is attainable inside the
   definition's own admissible box, and the modelled quantity has a defined
   limit there, and the junk value differs from that limit, the definition
   returns a **wrong value inside its domain** — silently, at exactly the
   endpoint people care about, and no type error will ever reveal it. That is a
   defect, and a more serious one than an unbounded range: an unbounded range
   is usually a missing hypothesis; this is a wrong answer.

The distinguishing question is whether the limit exists and differs from what
totality returns. `totality.py` decides it by instrumenting the backend to
record every divisor and every `log`/`sqrt` argument, finding where a guard
changes sign along a coordinate, and bisecting onto the exact junk point —
sampling essentially never lands on one, since they are a measure-zero set.

Of 275 definitions scanned, 16 have an attainable junk point. In 15 the limit
is infinite, so the quantity is genuinely undefined there and the junk value is
a modelling choice; those are reported separately and are **not** called
defects. One has a finite limit and is a defect:
`equalVarianceGaussianAUCFromExplainedR2` returns 0.5 — chance discrimination —
at `r2 = 1`, where the AUC tends to 1.

Nothing here runs Lean. Bodies are transcribed by a narrow transpiler
(`transpile.py`) that accepts the arithmetic fragment and **raises rather than
guesses** on anything else; what it rejects is reported, not skipped.

## Running

```
python extract_defs.py       # -> defs.json          (991 definitions)
python check_ranges.py       # -> results_ranges.json
python check_invariants.py   # -> results_invariants.json
python demo_falsifiable.py   # -> results_falsifiability.json
python report.py --findings  # -> coverage.json + the ranked defect list
```

Requires Python 3.11+ and nothing else. `z3` is optional: install it
(`pip install z3-solver`) and range containment is DECIDED for the
polynomial/rational fragment instead of sampled. Without it the checker still
runs; verdicts that would have been decided stay `inconclusive`.

Every verdict records `decided_by`, because a sampling negative is not a proof
and an SMT negative is, and anyone reading the results needs to know which one
they are holding:

| `decided_by` | strength |
| --- | --- |
| `z3 (UNSAT over the whole box)` | proof — no point of the box escapes |
| `interval-branch-and-bound` | proof — sound outward-rounded enclosure |
| `z3 (SAT, model is the witness)` | proof of existence; the witness is exact |
| `sampling + pattern search` | a witness, when it finds one. Finding nothing proves nothing |

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
| `escape-outside-theorem` | escapes, but only where the hypotheses of a theorem that proves that bound are violated. The range does hold where the author proved it; the finding is that the definition itself does not carry the condition. A lead, not a defect |
| `contradicts-theorem` | escapes at a point that satisfies the hypotheses of a theorem proving that bound. Lean has no `sorry`s, so this indicates an error in **this checker**, and it is never reported as a corpus defect |
| `inconclusive` | search found nothing and the interval proof did not close. **Not** a pass |
| `no-range` | the name and docstring commit the definition to no particular range |
| `not-transpiled` | outside the arithmetic fragment; the reason is recorded |

## Where the admissible box comes from

In priority order, recorded per coordinate in `box_provenance`:

1. **Theorem hypotheses.** Numeric bounds (`0 < Ne`, `m ≤ 1`) become box edges.
   Theorems rename arguments freely, so the application site is read to map
   theorem-local names back onto the definition's own parameters.

   Theorem hypotheses are **never** used to shrink the searched region. They
   are applied afterwards, to classify a witness, for three reasons learned the
   hard way:

   * hypotheses must be grouped **by theorem** and never conjoined across
     theorems — the union is not a domain. `coalFst` carries `100 * Ne < t`
     from one asymptotic lemma, and conjoining it excludes every sensible F_ST
     evaluation, so the definition passes vacuously.
   * a theorem's guard must use **all** of that theorem's hypotheses. Splitting
     them between the box and the guard left guards incomplete and reported
     `neiFst` as broken at `H_S > H_T`, which `nei_fst_in_unit` excludes.
   * a guard only excuses an escape on the **side it bounds**.
     `steppingStoneFst_nonneg` proves `0 ≤ f`; a witness of 10000 satisfies both
     its hypotheses and its conclusion and says nothing about the escape above 1.
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
* **z3 does not model transcendentals.** `exp`, `log`, `Real.rpow` and `Phi`
  have no decidable theory here, and axiomatising them would yield verdicts
  that look like proofs and are not. Definitions using them are reported
  `unsupported` by the solver and fall back to sampling.
* **`Phi` is a numeric stand-in.** The `extract` agent's `Phi` is an erf form,
  mathematically equal to the corpus's measure-theoretic
  `ProbabilityTheory.cdf (gaussianReal 0 1)` but not derived from it; 23
  definitions depend on it. This checker never routes a verdict through it: the
  AUC finding below is about the ARGUMENT `r2 / (2 * (1 - r2))` jumping from a
  limit of `+inf` to a junk value of `0`, which any monotone `Phi` maps to a
  wrong answer. The finding does not depend on how `Phi` is implemented.
* **Lean's junk values are reproduced, not repaired**: `x / 0 = 0`,
  `x⁻¹ = 0` at 0, `Real.sqrt x = 0` for `x < 0`, `Real.log 0 = 0` and
  `Real.log x = Real.log |x|`, and `Real.rpow` on a negative base via the
  complex branch. Testing what is written is the whole point, and one finding
  here exists only because of them. `backends.FloatBackend` agrees with
  `extract/lean_rt.py` on 16000 randomised comparisons of these primitives;
  that differential test is the only reason to believe either is right.
* **The required range here is name-implied, not theorem-proved.** Violating a
  bound a theorem proves would be a defect; violating one only implied by a
  name is a **lead**. `results_ranges.json` records both — `range_source` for
  the implied one and `proved_bound` / `bounding_theorems` for the proved one —
  and they are never merged.
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
