# Simulation checks of Calibrator population-genetics definitions

`proofs/Calibrator` contains ~1500 theorems and no `sorry`s, so no theorem in it
can be false. A wrong *result* can therefore enter only through a definition
whose name claims a population-genetic meaning that its formula does not have.
Downstream theorems are then machine-checked and still misleading — this is
exactly how the factor-of-two in `demographicSpike` survived review.

These scripts transcribe each Lean definition literally (the Lean file and line
are quoted in each Python docstring) and compare it against a simulation of the
quantity the *name* refers to. Ground truth is msprime for coalescent
quantities and exact vectorized Wright-Fisher forward simulation for the
two-locus LD and assortative-mating quantities.

## Running

```
NPROC=24 python3 check_defs.py  all defs.json   && python3 report.py  defs.json
NPROC=24 python3 check_defs2.py all defs2.json  && python3 report2.py defs2.json
```

Round 1 is ~1 minute on 24 cores; round 2 is a few minutes (branch-mode
statistics over 20 Mb).

## Findings

| Definition | Source | Verdict |
| --- | --- | --- |
| `ldRetentionPerGen`, `ldAfterGenerations` | `LDDecayTheory.lean:38,67` | **Validated.** `(1-r)(1-1/2Ne)` tracks `E[D]/D₀` to 3–4 digits over N ∈ {500, 2000}, r ∈ {0, 10⁻³, 10⁻²}, t ≤ 100. It describes `E[D]`, not `E[D²]`, which decays about twice as fast. |
| `singletonProportion` | `DemographicHistory.lean:289` | **Falsified.** See below. |
| `demographicSpike` | `PCCorrectability/Threshold.lean` | **Falsified and fixed** (constant 2 → 4); see `../pc_correctability/`. |

### `singletonProportion` is wrong

`1 - log N₀ / log N₁` fails in three independent ways:

1. **Wrong at the null.** With no growth (`N₀ = N₁`) it returns exactly 0, but a
   constant-size neutral population has singleton proportion `1/H_{n-1}`:
   simulation gives 0.187 (n=50) and 0.140 (n=200), matching the neutral
   prediction 0.193 / 0.152. The harness reproduces standard theory at the
   null, so the disagreement is in the definition.
2. **No sample-size dependence.** The singleton proportion depends strongly on
   sample size (0.427 vs 0.368 at N₁=10⁴; 0.693 vs 0.745 at N₁=10⁶), but the
   formula cannot express that — it has no `n` argument.
3. **Numerically off throughout**: 0.25 vs 0.43, 0.40 vs 0.61, 0.50 vs 0.69.

Any theorem quantifying expansion through this definition inherits the error.

## Harness caveats found the hard way

Round 1's island-model check was **invalid**: it set msprime's *pairwise*
migration rate, so total immigration per deme scaled with the number of demes
and produced a spurious deme-count trend. `check_defs2.py` holds total
immigration fixed. Round 1's split-Fst check used site statistics from a single
2 Mb region at 2 replicates and was too noisy to call; round 2 uses tskit
branch-mode divergence, which averages over mutational noise analytically.
