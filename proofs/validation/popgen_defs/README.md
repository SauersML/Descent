# Simulation checks of Calibrator definitions

`proofs/Calibrator` contains ~1500 theorems and no `sorry`s, so no theorem in it
can be false. A wrong *result* can therefore enter only through a definition
whose name claims a meaning that its formula does not have. Downstream theorems
are then machine-checked and still misleading — this is how the factor-of-two in
`demographicSpike` survived review.

These scripts transcribe each Lean definition literally (the Lean file and line
are quoted in each Python docstring) and compare it against a simulation of the
quantity the *name* refers to.

## Ground truth used

| Tool | Used for |
| --- | --- |
| msprime | coalescent quantities: F_ST, island/stepping-stone models, admixture, singleton spectra |
| tskit branch-mode statistics | divergence/diversity without mutational noise |
| exact vectorized Wright–Fisher (this repo) | two-locus LD, assortative mating — forward-time phenomena the coalescent cannot represent |
| exact numerical integration | truncated-normal and liability-threshold quantities |
| Monte Carlo (10⁶–10⁷ draws) | cross-checks on every closed form above |

A definition is only reported as falsified when the harness reproduces standard
theory at a null or control point in the same run.

## Falsified

| Definition | Source | Error |
| --- | --- | --- |
| `demographicSpike` | `PCCorrectability/Threshold.lean` | constant 2 should be 4; sharp threshold is `MF²n > 1`, not `> 4` (fixed) |
| `singletonProportion` | `DemographicHistory.lean:289` | returns 0 at the no-growth null where truth is `1/H_{n-1}`; no sample-size argument; 40–70% off |
| `truncationBias` | `PowerAnalysis.lean:215` | ~2×10⁵ too small at genome-wide significance; *increases* in β/SE where the true bias decreases; quoted one-sided formula contradicts the two-sided `isSelected` |
| `winnersCurseInflation` | `PowerAnalysis.lean:389` | no threshold parameter; −73% to +23%, sign-flipping |
| `approxPower` | `PowerAnalysis.lean:74` | no α; 99.3% vs 1.1% true power at GWAS significance |
| `amInflationFactor` | `StratificationConfounding.lean:138` | `1/(1−r)` overstates by up to +82%; no h² argument though the truth depends strongly on h² |
| `fstFromDrift` | `PopulationGeneticsFoundations.lean:283` | documented as split F_ST but is within-population heterozygosity loss; +15–28% biased upward in 11/12 cells |
| `liabilityAUCFromSNR`, `liabilityAUCFromVariances`, `liabilityAUCFromExplainedR2` | `PortabilityDrift.lean:2544,2548,2578` | documented "Exact"; no prevalence argument; −3% to −26% |
| `admixedFst` | `DemographicHistory.lean:173` | `(1−α)²` scaling ignores that F_ST is a ratio; −2% to −91%, worst at high α |
| `partialOverlapR2` | `SampleOverlapBias.lean:54` | spurious `/n_gwas` makes overlap inflation ~2000× too small; truth is `(1−f)R²_out + f·R²_in` |
| `bottleneckLDAmplification` | `LDDecayTheory.lean:192` | no recombination rate; rises to 1 instead of saturating at `1/(1+4Nc)`; up to 3.3× too high |

## Validated

| Definition | Agreement |
| --- | --- |
| `ldRetentionPerGen`, `ldAfterGenerations` | 3–4 digits vs `E[D]/D₀` (describes `E[D]`, not `E[D²]`) |
| `r2EstimatorVariance` | 0.99–1.01 of Monte Carlo variance for n ≥ 1000 |
| `noncentralityParam` | 0.99–1.01 vs mean Wald χ² from simulated genotype regressions |
| `amEquilibriumVariance` | −5%…+1% across r ∈ [0.1,0.5], h² ∈ [0.2,0.8] |
| `coalFst` | unbiased; errors scatter both signs within a few SE |
| `admixtureLD` | ≤0.2% |
| `Expected_Abs_Shift` | ≤0.1% (correct half-normal mean) |

## Recurring defect: the missing parameter

Six of the eleven falsified definitions fail the same way — the quantity depends
on a parameter the definition does not take, so no choice of constants can
repair them:

* `approxPower` — no significance threshold α
* `winnersCurseInflation` — no selection threshold
* `liabilityAUCFrom*` — no prevalence
* `singletonProportion` — no sample size
* `amInflationFactor` — no heritability
* `bottleneckLDAmplification` — no recombination rate

A cheap mechanical screen for the rest of the development: for each definition,
ask which arguments the named quantity is known to depend on, and flag any that
are absent from the signature. That is a static check — it needs no simulation.

## Harness caveats found the hard way

* Round 1's island-model check was **invalid**: it set msprime's *pairwise*
  migration rate, so total immigration scaled with deme count and produced a
  spurious deme-count trend. `check_defs2.py` holds total immigration fixed.
* Round 1's split-F_ST check used site statistics from one 2 Mb region at 2
  replicates — too noisy to call. Round 4a uses branch-mode statistics with 6
  replicates and reports standard errors.
* The first portability run measured source R² *in the GWAS sample itself*, so
  the "portability ratio" confounded overfitting with portability.
  `check_portability.py` now holds out half the source population.
* `demoSteppingStoneFst` looked 30–123% wrong, but σ² is a free dispersal
  parameter that was fixed to 1 arbitrarily. **Not reported as a finding.**
