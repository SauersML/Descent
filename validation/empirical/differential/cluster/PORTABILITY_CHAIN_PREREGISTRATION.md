# Portability-chain correspondence and blind preregistration

Status: mathematics authored; blind battery preregistered; no simulation in this document has
been run or scored. The Lean declarations are general. The sample sizes and CSV details below
are one correspondence instance and are not parameters embedded in those laws.

## Complete metric correspondence

| Reported column | Corpus declaration | Exact estimator form | Committed-source quotation or pin |
|---|---|---|---|
| finite-sample F | `Core.bhatiaHudsonRatioOfSums` | sum of sample-corrected Hudson numerators divided by sum of between-population denominators | `refs.py`: “Hudson's ratio-of-averages estimator at finite haploid sample size.” |
| `r2_true` / `liability_r2` | `DemeScoreLaw.r2True` | `Cov(S,Y)^2/(Var(S) Var(Y))` | `fam_serial_founder.py` reads `metric == "liability_r2"` keyed by demography, phenotype, method, and seed. |
| calibration slope | `DemeScoreLaw.calibrationSlope` | `Cov(S,Y)/Var(S)` | `calibration_binary.csv`; the same per-run key is used. |
| CITL/intercept | `phenotypeCITL` | `logit(K_observed)-logit(K_predicted)` | `fam_serial_founder.py`: the generator solves one intercept per phenotype and splits every deme 50/50. |
| probit risk spread | `DemeScoreLaw.probitRiskSpreadRatio` | `sqrt(R2/(1-R2))` | Same two per-deme score moments as slope. |
| Spearman | `DemeScoreLaw.spearman` | `6/pi asin(Pearson/2)` under the Gaussian chart | Within-deme metric; no population pooling. |
| MAE | `DemeScoreLaw.mae` | `sqrt(2/pi) sqrt(Var(linear error))` | Within-deme Gaussian error chart. |
| tail RMSE | `DemeScoreLaw.topDecileRMSE` | conditional Gaussian second-moment RMSE above the declared boundary | Boundary supplied to the law rather than estimated inside it. |
| top-tail risk ratio | `DemeScoreLaw.topDecileRiskRatio` | tail mean of liability risk divided by deme prevalence | Tail and prevalence are evaluated in the same deme. |
| OR per SD | `DemeScoreLaw.orPerSD` | liability-model odds ratio for one score standard deviation | Routes through the existing validated liability chart. |
| Brier score / BSS | `DemeScoreLaw.brier` plus an explicit reference Brier | BSS is `1-Brier(model)/Brier(reference)` | `fam_serial_founder.py`: “Brier = MSE(p,p_true) + E[p_true(1-p_true)]” within a run. |
| within-deme AUC | `DemeScoreLaw.withinAUC` | liability-threshold AUC at that deme's `R2` and prevalence | `accuracy_binary.csv`, `metric == "auc"`. |
| pooled AUC | `DemeMixture.pooledAUC` | `sum_i sum_j P(i|case)P(j|control)P(S_i^+>S_j^-)` | Diagonal terms are within-deme AUC; off-diagonal terms compare different deme laws. |
| Harrell C | `administrativeHarrellC` | concordant comparable-pair mass divided by comparable-pair mass | Administrative horizon and hazard model are explicit inputs; absent comparable pairs remain an informative zero branch. |

The demography column is part of the inference key. The committed reader constructs keys as
`(r["dem"], r["pheno"], r["method"], int(r["seed"]), r["metric"])`; dropping `dem` merges
different data-generating laws and is a correspondence error.

The study instance has 125 held-out diploid individuals per nontraining deme, hence 250
haplotypes per allele-frequency cell, and ten seeds per demography/phenotype inference cell.
`fam_auc_demography_split.py` quotes the resulting test partitions as `2500 + 9*125` and
`2500 + 35*125`. These numbers belong here, not in the general Lean types.

Serial distance-quintile rows are mixture strata. They must be represented by
`Program.PopulationRow.mixture` with their actual deme weights and evaluated as a weighted
functional. They are not atomic deme rows and may not be assigned the midpoint deme's law.
The primary generator/sidecar containing the quintile weights is absent from this checkout;
that missing correspondence input is recorded as a blocker, not replaced by equal weights.

## Migration components and estimator gate

`PopGen.TwoDemeMigrationComponents` separates directional backward rates, their symmetric
midpoint, total lineage-mixing rate, signed imbalance, diploid-scaled total, and finite-deme
correction. Relabelling preserves total flow and negates imbalance. Arbitrary migration
matrices can instantiate the same decomposition pairwise.

The finite-sample F gate owns `Core.bhatiaHudsonRatioOfSums`. Its required rivals are:

- parametric Hudson F (sample corrections deleted);
- mean of per-locus Hudson ratios;
- Nei G_ST ratio of averages;
- Weir-Cockerham theta.

No rival is a fallback. A mismatch is `bad-correspondence` unless the exact constructor's
algebra is wrong, in which case it is `bad-math`.

## Blind gap-list re-derivation

| Gap | Law → fresh observable | Analytic limits checked before data | Predeclared rivals | Informative zero |
|---|---|---|---|---|
| A1 | joint present-day count law → source/target JSFS, fixation, conditional erosion | no migration; coincident demes; probabilities sum to one | scalar retention; independent marginal spectra | zero conditional denominator is reported as undefined branch |
| A2 | finite two-locus stationary system → cross-deme `D1D2` family over recombination and migration | zero recombination; panmictic equality; determinant nonzero | fitted exponential retention; one-locus substitution | zero Cramer numerator is retained |
| A3/A4 | typed demographic primitives → arbitrary serial, grid, and many-deme instances | pair relabelling; train=target; aggregation invariance | one scalar F for all primitives | absent spectrum cell stays zero |
| B | realised GWAS sampling law, then clump and threshold → winning threshold and retained effect mass | zero estimation noise; no conflicts; one threshold | select using mean p-values; independent-locus clumping | empty retained set is a prediction |
| C/D | per-deme score moments → R2, slope, risk spread, errors, CITL, phenotype ladder | identical deme; clean rung CITL zero; common rung slope | pooled retention; entered target prevalence for emergent rung | correct R2 with wrong slope rejects the joint law |
| E1/E2 | deme laws and mixture weights → within and pooled AUC | one deme; identical deme laws; weights sum to one | unweighted mean of within-deme AUCs | zero off-diagonal mean shift remains diagnostic |
| E3 | administrative PH law → Harrell C | horizon zero; common score shift with reciprocal baseline change | uncensored AUC; prevalence-threshold AUC | no comparable pairs is not imputed as 0.5 |
| F | typed correspondence → every exported comparison column | ploidy cell identity; replicate-key uniqueness | wrong F conventions; demography-pooled key; atomicized mixture | missing source cell remains missing |

## Preregistered blind battery

Fresh simulations must be generated only after the declarations and this table are frozen.
The battery contains a held-out two-deme isolation-with-migration history, a held-out serial
founder history, and a held-out spatial split. Parameter values, seeds, and tolerances are
chosen by a party blind to outcomes. The inference unit is a fresh seed within a declared
demography/phenotype cell; seeds are never rows of one pooled fit.

Acceptance requires simultaneous predeclared error bounds for all observables in the gap
table and rejection of every named rival. A zero prediction is evaluated with its sampling
uncertainty. No result may be labelled validated merely because the preferred law was not
rejected.

## Ordered doctrine and ledger

Every law moves through: literature → symbolic derivation → general Lean body with constraints
carried by types → analytic-limit self-check → blind-battery preregistration → one fresh blind
battery → ledger. Simulation output is not used to repair a formula iteratively.

Current ledger state:

| Layer | State | Last completed stage |
|---|---|---|
| A1–A4 | derived | analytic self-check authored |
| B1–B2 | derived | analytic self-check authored |
| C1–C3 | derived | analytic self-check authored |
| D1–D3 | derived | analytic self-check authored |
| E1–E3 | derived | analytic self-check authored |
| F1–F3 | preregistered | blind battery preregistered |

Misses are filed only as `bad-assumption`, `bad-math`, or `bad-correspondence`. Repairs must
have been mandatory from the preregistration or be deferred to a separately preregistered
battery. This document records no empirical verdict.
