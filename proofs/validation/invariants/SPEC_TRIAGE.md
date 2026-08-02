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

## D. Parked — CORPUS-LEVEL claim (was 28, now 0) — **CLAIM REFUTED**

**I ran the consumer search within the hour of writing this section, and it
refutes the claim for every definition in it.** Recorded rather than quietly
edited, because the claim was stated as being about the corpus and a claim
about the corpus has to be allowed to lose.

    11 of 27  have a downstream CONSUMER, so the composition is testable
              exactly as the falsifier said it would be
    16 of 27  have no consumer but DO have theorems mentioning them — which
              my theorem tier failed to evaluate
     0 of 27  are genuinely isolated

Consumers found: `coalescentTau` feeds `fstFromGenerations` and
`PureSplitModel.tau`; `prevalenceLogit` feeds `prevalenceCITLShift`;
`thresholdStandardizedCoordinate` feeds `benchmarkHighScoreRate`;
`hweMellinJetVariance` feeds three; `pgsStratificationRiskCoefficient` feeds
two; and six more. Every one of those composites is a measurable quantity, so
the convention underneath is under test even though the conversion alone is
not — which is precisely what I said would have to exist for the claim to be
wrong.

The other 16 are a different and more embarrassing finding: they all have
theorems about them, and my theorem tier did not use those theorems. That is a
gap in my evaluator — untranspilable conclusions, or hypotheses that admitted
no sampled point — not a property of the corpus. It is the same shape as the
`Finset` sums that looked unmeasurable until somebody wrote forty lines of
evaluator.

So the honest count for this class is ZERO corpus-level parks. What I had was
27 claims about my afternoon wearing a claim about the corpus.

### The original section, kept for the record (28)

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

The 64 do not collapse to one number, and after the consumer search they do
not collapse to my first answer either:

    13  simulation spec written
    11  simulatable, spec not yet written
     4  decidable, want a solver rather than a sampler
    11  testable IN COMPOSITION via a downstream consumer
    16  have theorems my own theorem tier could not evaluate
     8  compositions of the above
     0  genuinely beyond reach

Nothing here is unreachable. Every one of the 64 is work, and the only honest
label for the whole set is "not done yet".

**The methodological point costs me the section above and is worth more than
it.** A claim about the corpus must be refutable, and mine was refuted within
the hour by a search I had already described. The version of this mistake that
would have survived is the one where the falsifier is named but never run —
naming it is what makes the claim look rigorous, and running it is the only
thing that makes it a claim at all. Stating a falsifier and not executing it is
the same failure as a check that cannot fail, one level up.
