# Empirical-status triage: the 38 definitions check 3b reported

This file exists for whoever is applying `Empirical status:` markers. It is a
per-definition verdict on the 38 definitions that check 3b of
`proofs/validation/code/check.py` reported as making an empirical claim with no
status marker.

**All 38 have since been marked, nearly all `UNTESTED`.** So this is no longer a
to-do list. It is a list of which of those markers are right and which should be
taken back off, because roughly ten of them record a claim the definition does not
make.

## Why a wrong marker is not a harmless marker

`Empirical status: UNTESTED` on a definition that makes no empirical claim is not a
neutral act of bookkeeping. It asserts that the declaration is a claim about an
observable which nobody has yet checked, and it puts that declaration into the
enumerable set of things someone is expected to go and test. A permutation on
`Fin 3` and a closed ball in `ℝ^q` are not awaiting measurement. Marking them
inflates the corpus's own count of outstanding empirical debt with entries that can
never be discharged, which is the same disease as a budget nobody can reach: the
list stops being read.

The rule this file applies: mark it if a wrong number in the body would be a wrong
statement **about the world**. Do not mark it if a wrong number would be a wrong
statement about mathematics.

## Part 1: the ten that should NOT carry a marker

### 1a. Four caught by a regex bug that has since been fixed

These four were never about linkage disequilibrium. Check 3b's `DOMAIN` pattern
was compiled with `re.I`, which defeated the case discrimination in its own
`ld[A-Z_]` branch and reduced it to "an `l` followed by a `d`, anywhere in the
name". Every one of these is a mid-word accident:

| Definition | The letters that matched |
|---|---|
| `Condensation.criticalDegree` | critica**LDE**gree |
| `FoldedSpectrum.totalDiploidCovarianceMomentInformation` | tota**LDI**ploid |
| `GenerativePortabilityLaw.historySpectralDistanceSq` | spectra**LDI**stance |
| `ScoreDistribution.residualDiscreteness` | residua**LDI**screteness |

The pattern is now `^ld|(?:^|[a-z0-9])LD(?=[A-Z_]|$)`, matching `LD` as a word, and
none of these four matches it. `criticalDegree` is a percolation threshold
`log N / c`; `historySpectralDistanceSq` is a squared distance in a kernel space.
Their markers should come off unless someone can say what observable each predicts.

### 1b. `effect` in its ordinary causal sense

`effect` is in the domain list because of allele effect sizes. These uses are
structural-causal-model vocabulary over abstract fields, and the enclosing modules
are rigidity witnesses, not genetics:

- `BundleRigidity/LinearSCM.totalEffect`, `.directEffect`, `.indirectEffect` —
  differences of the SCM's own `yUnder` / `yUnderXM` / `mUnder` fields. `totalEffect
  x x' nM nY = S.yUnder x' nM nY - S.yUnder x nM nY` is the definition of an
  intervention contrast, not a measured quantity.
- `CausalInference.effectShare` — `indirect_effect / total_effect`, a ratio of two
  arguments.
- `PolygenicArchitecture.boundedEffectCarrier` — `Metric.closedBall 0 |B|`, a set.
- `PolygenicArchitecture.effects` — the carrier set of a certificate problem.

A wrong body in any of these is a wrong statement about arithmetic.

### 1c. Three more where the domain word is a different word

- `CirculationDefect.driftGeneratorForm` — `drift` here is the drift term of a
  diffusion generator, not genetic drift. The body is
  `s * (x^2 + y^2) + circulationQuadraticForm a x y`, a quadratic form.
- `FoldedSpectrum.genotypeFlip3` — the permutation `![2, 1, 0]` on `Fin 3`. It is
  reindexing, and `genotypeFlip3_involutive` is the only thing said about it.
- `BlindnessRegistry.averageEffect_blind_to_dominance` — a `def` producing a
  `ProbeBlindness` witness. It is a proof object, not a quantity.

### 1d. Two caught by the ploidy screen on something that is not a frequency

`BundleRigidity/TwoAtom.mOne` and `.mTwo` are `|1 - 2p| / p` and `|1 - 2p| / (1-p)`,
where `p` is the weight of one atom of a two-point distribution. The `2 * p` trips
the convention screen, but the guard's own comment already excludes exactly this:
"The 2 in a Gaussian density or in a quadratic expansion is not a ploidy
convention, and tying it to `ploidy` would be wrong." Tying these to `ploidy` would
assert that a mixture weight is an allele frequency.

## Part 2: the ~28 that genuinely should carry a marker

These are claims about observables, and `UNTESTED` is the right marker for any of
them with no measurement recorded.

**Population-genetic rates and equilibria** — `DGP.scaledMutationRate` (`4 Ne μ`),
`DGP.scaledMigrationRate` (`4 Ne m`), `DGP.fstMutationDriftEquilibrium`
(`1/(1+θ)`), `DGP.hetDecayFromScaled`, `DGP.fstDriftMigration`,
`PopulationGeneticsFoundations.steppingStoneCharacteristicLength`,
`SerialFounderChain.serialFounderWithinTime`, `.serialFounderCeilingFst`,
`DirichletTransfer.driftHorizon`.

**F_ST estimator spikes** — `Conventions.neiContrastSpike`,
`Conventions.hudsonBbpSpike`. Both are estimator behaviour under a demographic
design and both are falsifiable by simulation.

**The liability-threshold family** — `PortabilityDrift.liabilityThreshold`,
`.liabilityCaseMean`, `.liabilityControlMean`, `.liabilityCaseVariance`,
`.liabilityControlVariance`. These are the classical Falconer quantities; each is a
prediction about a real case/control distribution.

**Falconer's one-locus model** — `BlindnessRegistry.averageEffect`
(`a + d(1 - 2p)`), `.genotypicValue`. Note both currently have **no docstring at
all**, so a marker means adding one.

**LD and score structure** — `ScoreDistribution.effectiveBlockCount`,
`FoldedSpectrum.InLinkageEquilibrium`, `PortabilityDrift.totalEffect`,
`GenerativePortabilityLaw` and `FoldedSpectrum` entries not listed in Part 1.

## Part 3: `neutralAFBenchmark`, and a correction

I flagged `PortabilityDrift.targetLiabilityAUCFromNeutralAFBenchmark` and
`.neutralAFBenchmarkLiabilityMetricProfile` as needing something stronger than a
bare `UNTESTED`, on the grounds that `neutralAFBenchmarkRatio` is recorded as
falsified at nine to fifteen standard errors, and that `UNTESTED` and `FALSIFIED`
are opposite claims so the weaker word would launder the stronger fact.

**That reasoning is right in general and does not apply to these two.** Reading them
properly: `neutralAFBenchmarkRatio` was **deleted** (`PortabilityDrift.lean:2881`,
with its five theorems), and these two definitions are the **repairs** that replaced
the falsified route, not inheritors of it. `targetLiabilityAUCFromNeutralAFBenchmark`
routes through `presentDayR2` and makes prevalence `K` a required argument precisely
because the failure it replaces was that no prevalence was ever named. Their
docstrings cite the predecessor's measured `-0.068` AUC bias as the thing they fix.

A bare `UNTESTED` is therefore honest for both: they are new formulas, and being new
is why nothing has measured them.

The general rule still stands and is worth stating for whoever marks the next batch:
**never write `UNTESTED` on a definition whose predecessor's defect it still
carries.** `UNTESTED` means nobody looked. `FALSIFIED` means somebody looked and it
failed. Substituting the first for the second converts a known defect into an open
question, and it does so in the one place a reader goes to find out which is which.

## Part 4: what to do

1. Remove the markers from the ten in Part 1, or replace them with a one-line note
   saying why the definition is not an empirical claim.
2. Leave Part 2 as `UNTESTED`.
3. Check any marker added in this sweep against check 3d-bis. Marking a definition
   `UNTESTED` whose docstring already says "exact" or "precisely" creates an
   overclaim violation out of two edits that were each defensible alone. That
   happened once already during this sweep, on
   `steppingStoneCharacteristicLength`, and was corrected to `MEASURED`.
