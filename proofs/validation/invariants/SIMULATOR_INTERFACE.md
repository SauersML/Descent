# Shared simulation oracle — interface, announced before it is built

**Status: PROPOSED. Comment before it is finished.** This is published ahead of
the implementation on purpose. Four agents independently wrote four Lean
parsers this session and reconciling them cost real time and turned up 76
disagreements, one of which silently replaced a declaration with a namesake.
The simulator is the next thing with that shape, so the interface is being
agreed first and built once.

## What it is

A bank of oracles that compute a named quantity by SIMULATION, from first
principles — draw individuals, draw genotypes, run generations, measure — so a
definition can be compared against something other than its own stated
properties. It is the only tier in this project that produces **external**
evidence; everything else establishes internal consistency.

Pure numpy. No scipy, msprime or tskit in this environment.

## Entry point

```python
import sys; sys.path.insert(0, "/Users/user/gnomon/proofs/validation/invariants")
import sim_api

sim_api.oracles()                    # {oracle_id: OracleSpec}
sim_api.oracle("hwe_genotype_variance")
sim_api.evaluate(oracle_id, args, seeds=2)   # -> Estimate
sim_api.compare(oracle_id, callable_, points)  # -> Comparison
sim_api.stamp()                      # provenance: engine versions, git sha
```

### `Estimate`

Never a bare float. A simulated value without its own noise is not usable as a
reference, and treating it as exact is how a Monte Carlo wobble gets reported
as a defect.

```python
Estimate(value=0.4199, se=0.0009, n_draws=400_000, seeds=(0, 1),
         engine="hwe", undefined=False)
```

`se` is measured by running the oracle under two seeds and taking the spread,
not derived analytically. `undefined=True` means the quantity has no value at
that point (the oracle refuses rather than returning a number).

### `Comparison`

```python
Comparison(agrees=True, worst_excess=0.065, worst_point={...},
           allowed="max(rel_tol * |ref|, 3 * se)", rows=[...])
```

`worst_excess` is the gap divided by what is allowed, so `<= 1` means agreement
and the number is comparable across specs with different tolerances.

## Rules for anyone adding an oracle

1. **Simulate the quantity the NAME refers to.** An oracle derived by
   rearranging the Lean formula tests nothing. If a closed form is used, state
   the textbook source in the docstring and cross-check it against a sampler at
   a control point in the same run.
2. **Every oracle ships a negative control.** A deliberately wrong variant —
   half the true value, the right shape at the wrong parameter — must be
   REJECTED by the comparison, and the rejection factor is recorded. Without
   this, "no disagreement found" is indistinguishable from a blind test. The
   existing controls reject at 8x to 25x.
3. **Return `undefined`, never a guess**, where the quantity does not exist.
4. **Declare the regime.** If the oracle is only valid for many demes, or weak
   selection, or large samples, that goes in `OracleSpec.regime` and is carried
   into every result.

## Results contract

Keyed by **fully-qualified definition name** — never a bare short name. 22
short names in this corpus map to more than one definition, and one of them
silently mis-bound in another tier's translator.

```json
{"Calibrator.CovarianceStructure.ldCorrelationSq": {
   "oracle": "ld_correlation_sq",
   "verdict": "agrees" | "disagrees" | "undefined-here" | "no-oracle",
   "worst_excess": 0.08,
   "evidence_class": "external-reference",
   "mutants_rejected": 6, "mutants_tried": 6,
   "regime": "linkage equilibrium within each source population"}}
```

`evidence_class` is always `external-reference` from this module. It is the
vocabulary the `extract` agent's consumer already reads, and it is the only
value in this project that should count toward model validation.

`mutants_rejected` / `mutants_tried` are BOTH reported. "At least one mutant
was rejected" and "most nearby wrong bodies are rejected" are different claims
and pooling them overstates the evidence.

## Join key — OPEN QUESTION, needs `extract`

Consumers must map a definition to an oracle. Three candidate keys all fail
today: short names collide (22 of them); `(file, short)` still collides because
a namespaced definition and a bare one in the same file share a `short`; and
`(file, line)` breaks because tables are extracted from different revisions of
a corpus several agents are editing — 93 of 403 of my callables had no row at
their file:line against a table generated minutes earlier.

Proposal: the fully-qualified name as `extract` emits it, with `body_checksum`
as a corroborating field — if names join but checksums differ, the consumer is
told the two sides are looking at different revisions rather than proceeding.
**Not settled. Do not build a join against this document until it is.**

## What this will and will not cover

Reaches: Wright-Fisher drift, Hardy-Weinberg genotype and variance components,
two-locus LD with recombination, admixture, Gaussian and Bernoulli risk,
screening and waiting times, and — once the GWAS pipeline lands — discovery
power, portability, and sample-overlap quantities.

Does not reach: anything whose signature is not a real-valued function of real
arguments (matrices, measures, `Prop`), and any quantity whose name does not
identify something simulatable. Those stay on the UNREACHABLE list with a
reason rather than being quietly omitted.
