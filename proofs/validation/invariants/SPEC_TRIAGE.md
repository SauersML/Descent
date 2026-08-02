# Triage of the 64 checker-limited definitions

These are the definitions this tier transpiles and evaluates but cannot
discriminate: no name-implied range, no derivable invariant, no theorem
constraining them, and until now no simulation spec. They read as
`covered: false` with a stated reason — the tier reports its own incapacity
rather than hiding it — and the task is to remove that incapacity or to say
precisely why it cannot be removed.

**Two different claims can put a definition in the parked class, and they are
not interchangeable:**

| claim | about | what would falsify it |
| --- | --- | --- |
| *no non-circular oracle exists* | the corpus | a consumer whose observable behaviour depends on this quantity, making the COMPOSITION testable even when the definition is not |
| *I could not construct one* | my afternoon | somebody constructing one |

Every parked entry below states which claim it is. A circular oracle is worse
than an absent one, because it produces a number.

## A. Simulation spec written (13)

Independent oracles, in `sim_engines.py`, registered in `check_simulation.py`.
None of these restates the Lean body: each simulates the named quantity from
first principles and is compared against the sampler's own noise.

`fisherAverageEffect` (least-squares slope of genotypic value on dosage, which
is the definition of an average effect), `olsEffectEstimationVariance`
(variance across replicate refits), `r2FromMSE`, `expectedDistinctHaplotypes`
(occupancy, counted), `freqCorrFromFst` (correlation across loci after a
simulated split), `targetHetFromFst`, `mutationSelectionStepRare`,
`mutationSelectionStepRecessive` (both counted from explicit diploid genotypes
under viability selection then mutation), `twoDemeIMEquilibriumETss`,
`twoDemeIMEquilibriumETst` (exact two-lineage structured coalescent),
`optimumOUVariance` (SDE integrated forward), plus `hweGenotypeVariance` and
`hudsonFst` from the same batch.

## B. Simulatable, spec not yet written (11)

Claim: *my afternoon*, explicitly. Each has an obvious non-circular oracle and
I have not built it yet.

| definition | oracle |
| --- | --- |
| `driftLDCreationRate` | per-generation identity-by-descent rate, counted in a Wright-Fisher run |
| `driftLDStep`, `ibdRecurrenceStep`, `ibdFlowStep` | two-locus WF with recombination; measure the step |
| `stationaryLDEntry` | LD by separation in a simulated stationary chain |
| `ldPrecisionTrace` | trace of the inverse of a simulated first-order LD covariance |
| `pgsVarianceFromHet` | variance of a simulated score from simulated genotypes |
| `brierRegretPoint`, `logLossRegretPoint` | both risks are already simulated by existing engines; the regret is their difference at simulated points |
| `Expected_Abs_Shift`, `expectedSqMeanPGSDiff_pureSplit` | mean absolute / squared PGS-mean difference between two simulated diverged populations |

## C. Decidable without simulation (4)

Extract's observation, taken: **sampling is what you do when you cannot solve,
not a more honest version of solving.** These are exactly decidable and
sampling them would be the grid-search mistake again.

`gaussianJetVariance` (a closed constant, `π²/2 − 4`), `criticalDegree`,
`nonsmoothSummaryRisk`, `bbpProxyThreshold` — all elementary functions whose
claimed properties are algebraic identities, better settled by the solver than
by a sampler.

## D. Parked — CORPUS-LEVEL claim (28)

Claim: *no non-circular oracle exists*, because the name introduces an
abbreviation and has no referent independent of the formula. Measuring
`costEffectiveness` means dividing improvement by cost; there is no experiment
that could disagree.

`costEffectiveness`, `apparent_portability_loss`, `true_portability_loss`,
`total_portability_loss`, `incrementalR2`, `thresholdStandardizedCoordinate`,
`prevalenceLogit`, `ldOverlapFromSharedLD` (an explicit identity),
`expectedLinearEffectEstimate`, `deployedTransferTargetR2`,
`pcaSignalLossPenalty`, `coalescentTau` (a unit convention),
`informationCrossoverTime`, `globalAncestryAveragedEffect`,
`exactCalibratedBrierRiskFromR2`, `targetPGSVariance`, `absorptionInformation`,
`expectedEffectMultiplier`, `gradeCertifiedRisk`, `hweMellinJetVariance`,
`ldsrExpectedBetaSq`, `pgsStratificationRiskCoefficient`,
`haplotypePhasePredictionError`, `haplotypeTransportBias`,
`ageDependentSignalVariance`, `fisherTraceMSELowerBound`,
`requiredEffectiveSampleSizeForTraceMSE`, `recalibrationTraceMSELowerBound`.

**THE FALSIFIER, stated because the claim is about the corpus and must be
refutable:** each of these becomes testable the moment a definition or theorem
CONSUMES it in a context where the composed quantity is measurable. If
`coalescentTau` feeds a coalescent probability, the probability is simulatable
and the convention is then under test even though the conversion alone is not.
So this class is not closed — it shrinks whenever the corpus grows a consumer,
and the honest form of the claim is *no oracle exists for this definition in
isolation*, not *this definition can never be wrong*.

I have not yet run that consumer search. It is mechanical — the dependents are
already in the table — and it is the next thing I would do on this class rather
than writing oracles for them.

## E. Composite of already-covered parts (8)

`brierRegretRatio`, `logLossRegretRatio`, `targetExactCalibratedBrierRisk`,
`signalRetentionMigrationDrift`, `optimalFineTuningMSE`,
`scratchVsFineTuningCriticalSampleSize`, `ldBlockPruningDeficit`,
`expectedSqMeanPGSDiff_IMEquilibrium`, `twoLocusIBDCovariance`.

Claim: *my afternoon*. Each is a ratio or composition of quantities that either
already have oracles or are in class B. Once the parts are covered these follow
by composing the same simulations, and a wrong composition is detectable even
when each part is right — so they are worth doing, and after B rather than
before.

## What this changes about the residue

The 64 do not collapse to one number. 13 are done, 11+8 are work I have
declined to pretend is impossible, 4 want a solver rather than a sampler, and
28 rest on a corpus-level claim with a named and mechanical falsifier that I
have not yet run.

The number I would not want quoted is "64 need simulation". Roughly half do.
