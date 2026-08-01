import Calibrator.PopulationGeneticsFoundations
import Calibrator.DemographicHistory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.PCCorrectability.Threshold
import Calibrator.Identification
import Calibrator.AssortativeMatingPGS
import Calibrator.CovarianceStructure
import Calibrator.AncestrySpecificPower
import Calibrator.GeneticArchitectureDiscovery
import Calibrator.LongitudinalPortability
import Calibrator.LDDecayTheory
import Calibrator.MetricSpecificPortability
import Calibrator.PhenomeWidePortability
import Calibrator.ScoreDistribution
import Calibrator.EpistasisAndNonAdditivity
import Calibrator.VarianceComponents
import Calibrator.PowerAnalysis
import Calibrator.SelectionArchitecture
import Calibrator.PolygenicAdaptation
import Calibrator.AncestryCalibration
import Calibrator.PortabilityBounds
import Calibrator.PortabilityDrift
import Calibrator.StratificationConfounding

namespace Calibrator

/-!
# Identifications: making a named quantity carry its obligation

A Lean `def` cannot be wrong internally, so the entire risk of this
development sits in one place: a definition whose *name* claims a
population-genetic meaning that its *formula* does not have. Every theorem
downstream is then machine-checked and misleading. Two instances have now been
found by simulation rather than by proof.

`demographicSpike` carried the wrong constant, `2 F m_eff` where the data give
`3.9920 ± 0.0045`. A cross-check between two independently written formulas
would have caught it, and `four_hudsonFst_eq_standardizedContrastVariance`
below is that cross-check.

`singletonProportion N₀ N₁ = 1 - log N₀ / log N₁` was worse, and no
cross-check of that kind could have caught it. It returns `0` at the null
where the truth is `0.187`, and it takes no sample size at all although the
observable moves from `0.427` to `0.368` when `n` goes from 50 to 200. The
signature cannot express the quantity. That is a type error, not an arithmetic
one, and it is invisible to any argument that only compares formulas to other
formulas.

The two failures therefore need two different mechanisms.

* Against a wrong constant: over-determination. Derive the quantity from a
  primitive so the constant is forced, and relate independently written
  formulas so that drift between them fails to compile. That is this file.

* Against a wrong signature: an obligation attached to the name. A named
  empirical quantity must be introduced together with the observable it claims
  to be, and a proof that the two agree. Then a formula that cannot depend on
  `n` cannot be offered as an observable that does. That is `Identification`
  in `Calibrator.Identification`.
-/

section Ploidy

/-- Number of homologous copies per locus. Every non-exponent factor of two in
this development traces to this constant, and every factor of four to twice
it. The corpus currently restates the convention inline at ninety-nine
definition sites: seventy-eight carrying a two and twenty-one a four. The
theorems in this section tie the independently written ones back here, so that
drift between them is a compile error rather than a silent disagreement. -/
noncomputable def ploidy : ℝ := 2

/-- Genotype variance at a locus in Hardy-Weinberg proportions, for dosage
coded `0, 1, …, ploidy`.

    Empirical status: UNTESTED. -/
noncomputable def hweGenotypeVariance (p : ℝ) : ℝ := ploidy * p * (1 - p)

/-- Coalescent time scale: time measured in units of `ploidy · Nₑ`
generations. -/
noncomputable def coalescentTimeScale (Ne : ℝ) : ℝ := ploidy * Ne

@[simp] theorem coalescentTimeScale_eq (Ne : ℝ) :
    coalescentTimeScale Ne = 2 * Ne := by
  unfold coalescentTimeScale ploidy; ring

/-- **Cross-check: the scaled mutation rate in `PopulationGeneticsFoundations`
is twice the coalescent time scale times the mutation rate**, rather than an
independently chosen `4`. -/
theorem scaledMutationRate_eq_ploidy_form (Ne mu : ℝ) :
    scaledMutationRate Ne mu = 2 * ploidy * Ne * mu := by
  unfold scaledMutationRate ploidy; ring

/-- **Cross-check: the scaled migration rate in `PortabilityDrift` uses the
same convention.** These two were written in different files, each spelling
out its own `4`. -/
theorem scaledMigrationRate_eq_ploidy_form (Ne m : ℝ) :
    scaledMigrationRate Ne m = 2 * ploidy * Ne * m := by
  unfold scaledMigrationRate ploidy; ring

/-- **Cross-check: the drift `F_ST` uses the coalescent time scale**, so the
`2 Nₑ` inside it is the same `ploidy · Nₑ` and not a separate choice. -/
theorem fstFromDrift_uses_coalescentTimeScale (t : ℕ) (Ne : ℝ) :
    heterozygosityLossFromDrift t Ne = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold heterozygosityLossFromDrift; rw [coalescentTimeScale_eq]

end Ploidy

section Differentiation

/-- Mean allele frequency across two subgroups of equal weight.

    Empirical status: UNTESTED. -/
noncomputable def meanAlleleFreq (p₁ p₂ : ℝ) : ℝ := (p₁ + p₂) / 2

/-- **Hudson's `F_ST` for two subgroups**, as one minus the ratio of mean
within-subgroup heterozygosity to total heterozygosity. Restored as a
definition so that `F` denotes a quantity rather than a name; it had been
deleted as unreferenced, which is precisely why `F` in the spike was free to
mean anything. -/
noncomputable def hudsonFst (p₁ p₂ : ℝ) : ℝ :=
  1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) /
    (ploidy * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

/-- Between-subgroup allele-frequency variance for an equal-weight split. -/
noncomputable def betweenSubgroupVariance (p₁ p₂ : ℝ) : ℝ := (p₁ - p₂) ^ 2 / 4

/-- **Cross-check: the heterozygosity form and the variance form of `F_ST`
agree.** The corpus contained both shapes and never related them. -/
theorem hudsonFst_eq_varianceRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    hudsonFst p₁ p₂ =
      betweenSubgroupVariance p₁ p₂ /
        (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  have h1 : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul h
  have h2 : (1 - meanAlleleFreq p₁ p₂) ≠ 0 := right_ne_zero_of_mul h
  unfold hudsonFst betweenSubgroupVariance ploidy
  field_simp
  unfold meanAlleleFreq
  ring

/-- **Cross-check: `simpleFst`, written separately in
`PopulationGeneticsFoundations`, is the same quantity.** -/
theorem simpleFst_eq_hudsonFst (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    simpleFst p₁ p₂ = hudsonFst p₁ p₂ := by
  rw [hudsonFst_eq_varianceRatio p₁ p₂ h]
  change (p₁ - p₂) ^ 2 /
      (4 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) =
    ((p₁ - p₂) ^ 2 / 4) /
      (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))
  field_simp [h]

/-- **The spike constant is forced, not chosen.**

Four times Hudson `F_ST` is exactly the variance of the standardized subgroup
contrast. Writing `2` in `demographicSpike` asserts that twice `F_ST` equals
that variance, which this theorem refutes, so the old constant is now
unprovable rather than merely differently calibrated. Simulation recovers
`3.9920 ± 0.0045` with `F` measured as Hudson `F_ST`, agreeing with the
derived value. -/
theorem four_hudsonFst_eq_standardizedContrastVariance (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    4 * hudsonFst p₁ p₂ =
      (p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  rw [hudsonFst_eq_varianceRatio p₁ p₂ h]
  unfold betweenSubgroupVariance
  field_simp

/-- **The spike written without any free constant.** With `F` pinned to Hudson
`F_ST`, the rank-one signal is the contrast variance times the effective
subgroup size, and no numeral appears on the right. -/
theorem demographicSpike_eq_contrastVariance_mul_effectiveSize
    (n m p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    demographicSpike n (hudsonFst p₁ p₂) m =
      ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
        effectiveSubgroupSize n m := by
  unfold demographicSpike
  rw [← four_hudsonFst_eq_standardizedContrastVariance p₁ p₂ h]

/-- **The spike, as an identification rather than a definition.**

This is the mechanism of `Calibrator.Identification` applied to the quantity
that motivated it. `formula` is what the calculator computes, `observable` is
the standardized contrast variance times the effective subgroup size, defined
without reference to the formula, and `derivation` is discharged. The old
constant cannot be substituted here, because the resulting field would not
typecheck.

    Empirical status: UNTESTED. -/
noncomputable def spikeIdentification (n m p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    Identification ℝ where
  formula := demographicSpike n (hudsonFst p₁ p₂) m
  observable :=
    ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
      effectiveSubgroupSize n m
  derivation := demographicSpike_eq_contrastVariance_mul_effectiveSize n m p₁ p₂ h
  evidence := Evidence.derived

end Differentiation

section EquilibriumAgreements

/-- **Cross-check: the island-model `F_ST` in `DemographicHistory` and the
architecture-level `equilibriumFst` in `AncestrySpecificArchitecture` are the
same function.** They were written in separate files, each spelling out its own
factor of four. -/
theorem equilibriumFst_eq_demoIslandModelFst (Ne m : ℝ) :
    equilibriumFst m Ne = demoIslandModelFst Ne m := by
  unfold equilibriumFst demoIslandModelFst; ring_nf

/-- **Cross-check: the two assortative-mating inflation claims agree only at
full heritability.**

`StratificationConfounding` carried `amInflationFactor r = 1/(1 - r)` and
`AssortativeMatingPGS` carries `amEquilibriumVariance V_A r h² = V_A/(1 - r h²)`
for the same quantity, and no theorem related them. Forward simulation with
the spousal correlation measured rather than assumed puts the second within
-5% to +1% and the first between +3% and +82% high, so the first is deleted.
This theorem records why the disagreement was invisible: the two coincide
exactly when `h² = 1`, which is the only case anyone would have checked by
inspection, and diverge with `h²` everywhere else. Assortative mating is a
forward-time phenomenon, so no coalescent simulation could have separated
them. -/
theorem amEquilibriumVariance_at_full_heritability (V_A r : ℝ) :
    amEquilibriumVariance V_A r 1 = V_A / (1 - r) := by
  unfold amEquilibriumVariance
  ring_nf

/-- **Cross-check spanning the mating and drift modules: assortative mating and
drift act multiplicatively on the additive variance.**

`amEquilibriumVariance` inflates by `1/(1 - r h²)` and `presentDayPGSVariance`
deflates by `(1 - F_ST)`, and composing them gives the product. Stated because
the two modules described the same variance and were never related, which is
the condition under which a falsified companion of `amEquilibriumVariance`
survived. -/
theorem amEquilibrium_then_drift (V_A r h2 fst : ℝ) :
    presentDayPGSVariance (amEquilibriumVariance V_A r h2) fst =
      (1 - fst) * (V_A / (1 - r * h2)) := by
  unfold presentDayPGSVariance amEquilibriumVariance
  ring

/-! ### Tying the inlined genotype-variance restatements back to `ploidy`

Five definitions across five modules spell out `2 p (1 - p)` independently.
Each is Hardy-Weinberg genotype variance, and none was related to any other,
so a change to the ploidy convention in one would have left the others
silently disagreeing. These theorems make that disagreement a failed proof. -/

theorem allelicVariance_eq_hwe (p : ℝ) :
    allelicVariance p = hweGenotypeVariance p := by
  unfold allelicVariance hweGenotypeVariance ploidy; ring

theorem heterozygosity_eq_hwe (p : ℝ) :
    heterozygosity p = hweGenotypeVariance p := by
  unfold heterozygosity hweGenotypeVariance ploidy; ring

theorem genotypeVarianceHWE_eq_hwe (p : ℝ) :
    genotypeVarianceHWE p = hweGenotypeVariance p := by
  unfold genotypeVarianceHWE hweGenotypeVariance ploidy; ring

theorem ancestryHeterozygosity_eq_hwe (p : ℝ) :
    ancestryHeterozygosity p = hweGenotypeVariance p := by
  unfold ancestryHeterozygosity hweGenotypeVariance ploidy; ring

theorem tagGenotypeVariance_eq_hwe (maf : ℝ) :
    tagGenotypeVariance maf = hweGenotypeVariance maf := by
  unfold tagGenotypeVariance hweGenotypeVariance ploidy; ring

/-! ### Tying the inlined island-model restatements back to the scaled rate

Five definitions across five modules spell out `1 / (1 + 4 Nₑ m)`. Each is the
migration-drift equilibrium at the scaled migration rate. -/

theorem fstMigrationDriftEquilibrium_eq_scaled (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m =
      fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

theorem islandModelFst_eq_scaled (Ne m : ℝ) :
    islandModelFst Ne m =
      fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold islandModelFst fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

theorem equilibriumFst_eq_scaled (Ne m : ℝ) :
    equilibriumFst m Ne =
      fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold equilibriumFst fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### Per-generation drift rate, written out in three modules

`1 / (2 Nₑ)` appears independently in `LongitudinalPortability`,
`DemographicHistory` and `LDDecayTheory` under three names. It is the
reciprocal of the coalescent time scale in each. -/

theorem longitudinalDriftDecayRate_eq_inv_timeScale (Ne : ℝ) :
    longitudinalDriftDecayRate Ne = 1 / coalescentTimeScale Ne := by
  unfold longitudinalDriftDecayRate; rw [coalescentTimeScale_eq]

theorem driftLDCreationRate_eq_inv_timeScale (Ne : ℝ) :
    driftLDCreationRate Ne = 1 / coalescentTimeScale Ne := by
  unfold driftLDCreationRate; rw [coalescentTimeScale_eq]

theorem ldDecayRatePerGen_eq_inv_timeScale (Ne : ℝ) :
    ldDecayRatePerGen Ne = 1 / coalescentTimeScale Ne := by
  unfold ldDecayRatePerGen; rw [coalescentTimeScale_eq]

/-! ### The coalescent `F_ST` map, written out twice

`DemographicHistory.fstFromCoalescenceTime` and
`PopulationGeneticsFoundations.coalFst` are the same function. `coalFst` is
the one simulation validated as split `F_ST`, being unbiased against
branch-mode divergence where the drift formula was biased upward by up to 28
percent, so relating them transfers that evidence. -/

theorem fstFromCoalescenceTime_eq_coalFst (T Ne : ℝ) :
    fstFromCoalescenceTime T Ne = coalFst T Ne := by
  unfold fstFromCoalescenceTime coalFst; ring_nf

/-! ### The harmonic mean, written out twice

`MetricSpecificPortability.f1ScoreMetric` and `OpenQuestions.f1Score` are the
same expression under two names in two modules, with no theorem relating
them. -/

theorem f1ScoreMetric_eq_f1Score (precision sens : ℝ) :
    f1ScoreMetric precision sens = f1Score precision sens := by
  unfold f1ScoreMetric f1Score; ring_nf

/-! ### Three more quantities written out in two modules each

Each pair below is the same expression under two names in two files, with no
theorem relating them. These are the configurations in which a divergence goes
unnoticed, which is how `amInflationFactor` and `fstFromDrift` survived. -/

theorem effectiveSymmetricMigration_eq_effectiveMigration (m₁₂ m₂₁ : ℝ) :
    effectiveSymmetricMigration m₁₂ m₂₁ = effectiveMigration m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration effectiveMigration; ring_nf

/-- The AUC map of the equal-variance Gaussian model appears in `DGP` under a
name that does not mention a model at all. Both were falsified as
liability-threshold AUCs and both are exact for the equal-variance model, so
they must agree. -/
theorem equalVarianceGaussianAUCFromVariances_eq_aucFromSignalVariance
    (vSignal vNoise : ℝ) :
    equalVarianceGaussianAUCFromVariances vSignal vNoise =
      gaussianAUCFromSignalVariance vSignal vNoise := by
  unfold equalVarianceGaussianAUCFromVariances gaussianAUCFromSignalVariance; ring_nf

/-- Wright's compounding identity: one minus the product of retentions. It is
written once for the two branches of a split and once for the two levels of
the `F`-statistic hierarchy. -/
theorem pairwiseFstFromBranches_eq_wrightFIT (a b : ℝ) :
    pairwiseFstFromBranches a b = wrightFIT a b := by
  unfold pairwiseFstFromBranches wrightFIT; ring_nf

/-! ### The per-generation retention factor, written out in four modules

`1 - 1/(2 Nₑ)` is the probability that two lineages fail to coalesce in one
generation. It is spelled out independently in `PhenomeWidePortability`,
`LDDecayTheory`, `PopulationGeneticsFoundations` and `PortabilityDrift`. -/

theorem neutralDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) :
    neutralDriftFactor Ne t = (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold neutralDriftFactor; rw [coalescentTimeScale_eq]

theorem ldRetainedFraction_uses_timeScale (Ne : ℝ) (t : ℕ) :
    ldRetainedFraction Ne t = (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold ldRetainedFraction; rw [coalescentTimeScale_eq]

theorem fstDerived_uses_timeScale (Ne : ℝ) (t : ℕ) :
    fstDerived Ne t = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold fstDerived; rw [coalescentTimeScale_eq]

theorem wrightFisherDriftRetention_uses_timeScale (N : ℕ) (t : ℕ) :
    wrightFisherDriftRetention N t
      = (1 - 1 / coalescentTimeScale (N : ℝ)) ^ t := by
  unfold wrightFisherDriftRetention; rw [coalescentTimeScale_eq]

/-! ### The coalescent time coordinate, written out twice

`t / (2 Nₑ)` is time in coalescent units, in `PortabilityDrift` and in `DGP`. -/

theorem coalescentTau_uses_timeScale (t Ne : ℝ) :
    coalescentTau t Ne = t / coalescentTimeScale Ne := by
  unfold coalescentTau; rw [coalescentTimeScale_eq]

/-! ### The scaled rates, written out on three parameter records

`θ = 4 Nₑ μ` and `M = 4 Nₑ m` appear as fields of
`GenerationalPopGenParameters` in `PortabilityDrift` and of
`EvolutionaryParameters` in `DGP`, each spelling out its own four. -/

theorem GenerationalPopGenParameters_theta_eq_ploidy_form
    (g : GenerationalPopGenParameters) :
    GenerationalPopGenParameters.theta g = 2 * ploidy * g.Ne * g.μ := by
  unfold GenerationalPopGenParameters.theta ploidy; ring

theorem GenerationalPopGenParameters_bigM_eq_ploidy_form
    (g : GenerationalPopGenParameters) :
    GenerationalPopGenParameters.bigM g = 2 * ploidy * g.Ne * g.mig := by
  unfold GenerationalPopGenParameters.bigM ploidy; ring

theorem EvolutionaryParameters_theta_eq_ploidy_form (p : EvolutionaryParameters) :
    EvolutionaryParameters.theta p = 2 * ploidy * p.Ne * p.mu := by
  unfold EvolutionaryParameters.theta ploidy; ring

theorem EvolutionaryParameters_bigM_eq_ploidy_form (p : EvolutionaryParameters) :
    EvolutionaryParameters.bigM p = 2 * ploidy * p.Ne * p.mig := by
  unfold EvolutionaryParameters.bigM ploidy; ring

/-- **The between-population variance of the mean breeding value is
`ploidy · F_ST · V_A`.**

Two independently drifting populations each contribute `F_ST V_A`, so the
variance of their difference carries the ploidy factor. Writing `2` here is
the same convention as everywhere else and is now tied to it. -/
theorem Var_Delta_Mu_eq_ploidy_form (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = ploidy * fst * V_A := by
  unfold Var_Delta_Mu ploidy; ring

/-! ### Genotype variance inside sums and products

Eight further definitions carry `2 p (1 - p)` as a factor rather than as their
whole body: score means and variances, Fisher's average effect, dominance and
additive variance, two noncentrality parameters, and a pairwise epistatic
variance. Each is now written against `hweGenotypeVariance`. -/

theorem pgsVariance_uses_hwe {m : ℕ} (β p : Fin m → ℝ) :
    pgsVariance β p = ∑ i, β i ^ 2 * hweGenotypeVariance (p i) := by
  unfold pgsVariance hweGenotypeVariance ploidy; ring_nf

theorem dominanceVariance_uses_hwe {m : ℕ} (p d : Fin m → ℝ) :
    dominanceVariance p d = ∑ i, (hweGenotypeVariance (p i) * d i) ^ 2 := by
  unfold dominanceVariance hweGenotypeVariance ploidy; ring_nf

theorem additiveVariance_uses_hwe {m : ℕ} (p α : Fin m → ℝ) :
    additiveVariance p α = ∑ i, hweGenotypeVariance (p i) * (α i) ^ 2 := by
  unfold additiveVariance hweGenotypeVariance ploidy; ring_nf

theorem noncentralityParam_uses_hwe (n : ℕ) (beta p : ℝ) :
    noncentralityParam n beta p = n * beta ^ 2 * hweGenotypeVariance p := by
  unfold noncentralityParam hweGenotypeVariance ploidy; ring_nf

theorem gwasNCP_uses_hwe (n : ℕ) (β p : ℝ) :
    gwasNCP n β p = n * β ^ 2 * hweGenotypeVariance p := by
  unfold gwasNCP hweGenotypeVariance ploidy; ring_nf

theorem effectiveSampleSize_uses_hwe (n : ℕ) (p r2_ld : ℝ) :
    effectiveSampleSize n p r2_ld = n * hweGenotypeVariance p * r2_ld := by
  unfold effectiveSampleSize hweGenotypeVariance ploidy; ring_nf

theorem epistaticVariancePairwise_uses_hwe (γ p₁ p₂ : ℝ) :
    epistaticVariancePairwise γ p₁ p₂ =
      γ ^ 2 * hweGenotypeVariance p₁ * hweGenotypeVariance p₂ := by
  unfold epistaticVariancePairwise hweGenotypeVariance ploidy; ring_nf

/-- The between-population drift variance of the score, carrying the same
ploidy factor as `Var_Delta_Mu`. -/
theorem expectedPGSDiffVariance_eq_ploidy_form (V_A fst : ℝ) :
    expectedPGSDiffVariance V_A fst = ploidy * fst * V_A := by
  unfold expectedPGSDiffVariance ploidy; ring

/-! ### The remaining singletons

Each of these uses the ploidy convention once, with no sibling to disagree
with, so only a derivation from `ploidy` ties them down. -/

theorem ldHalfLife_uses_timeScale (Ne : ℝ) :
    ldHalfLife Ne = coalescentTimeScale Ne * Real.log 2 := by
  unfold ldHalfLife; rw [coalescentTimeScale_eq]

theorem steppingStoneCharacteristicLength_uses_timeScale (Ne m : ℝ) :
    steppingStoneCharacteristicLength Ne m
      = Real.sqrt (coalescentTimeScale Ne * m) := by
  unfold steppingStoneCharacteristicLength; rw [coalescentTimeScale_eq]

theorem cumulativeDrift_uses_timeScale {T : ℕ} (Ne : Fin T → ℝ) :
    cumulativeDrift Ne = ∑ i, 1 / coalescentTimeScale (Ne i) := by
  unfold cumulativeDrift
  simp only [coalescentTimeScale_eq]

theorem ldRetentionPerGen_uses_timeScale (r Ne : ℝ) :
    ldRetentionPerGen r Ne = (1 - r) * (1 - 1 / coalescentTimeScale Ne) := by
  unfold ldRetentionPerGen; rw [coalescentTimeScale_eq]

theorem hetDecayFactor_uses_timeScale (Ne θ : ℝ) :
    hetDecayFactor Ne θ
      = (1 - 1 / coalescentTimeScale Ne) * (1 - θ / coalescentTimeScale Ne) := by
  unfold hetDecayFactor; rw [coalescentTimeScale_eq]

theorem asymmetricFst_eq_scaled (Ne m_into : ℝ) :
    asymmetricFst Ne m_into
      = fstMutationDriftEquilibrium (scaledMigrationRate Ne m_into) := by
  unfold asymmetricFst fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

theorem fstMigDriftEquil_eq_scaled (Ne m : ℝ) :
    fstMigDriftEquil Ne m
      = fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold fstMigDriftEquil fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

theorem fstMigrationMutationEquilibrium_eq_scaled (Ne m μ : ℝ) :
    fstMigrationMutationEquilibrium Ne m μ
      = 1 / (1 + scaledMigrationRate Ne m + scaledMutationRate Ne μ) := by
  unfold fstMigrationMutationEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold ploidy; ring_nf

theorem expectedFreqDiffSq_uses_hwe (fst p0 : ℝ) :
    expectedFreqDiffSq fst p0 = fst * hweGenotypeVariance p0 := by
  unfold expectedFreqDiffSq hweGenotypeVariance ploidy; ring

theorem pgsMean_uses_ploidy {m : ℕ} (β p : Fin m → ℝ) :
    pgsMean β p = ∑ i, β i * (ploidy * p i) := by
  unfold pgsMean ploidy; ring_nf

theorem fisherAverageEffect_uses_ploidy (a d p : ℝ) :
    fisherAverageEffect a d p = a + d * (1 - ploidy * p) := by
  unfold fisherAverageEffect ploidy; ring

theorem neutralPortability_uses_ploidy (r2_0 fst : ℝ) :
    neutralPortability r2_0 fst = r2_0 * (1 - ploidy * fst) := by
  unfold neutralPortability ploidy; ring

end EquilibriumAgreements

end Calibrator
