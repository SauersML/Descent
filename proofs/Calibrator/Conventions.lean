import Calibrator.PopulationGeneticsFoundations
import Calibrator.ImitationRigidity
import Calibrator.DemographicHistory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.PCCorrectability.Threshold
import Calibrator.Identification
import Calibrator.AssortativeMatingPGS
import Calibrator.CovarianceStructure
import Calibrator.AncestrySpecificPower
import Calibrator.GeneticArchitectureDiscovery
import Calibrator.LongitudinalPortability
import Calibrator.ImputationPortability
import Calibrator.SimulationValidation
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
import Calibrator.CovarianceStructure
import Calibrator.HaplotypeTheory
import Calibrator.LongitudinalPortability
import Calibrator.ImputationPortability
import Calibrator.SimulationValidation
import Calibrator.PortabilityDrift
import Calibrator.StratificationConfounding
import Calibrator.PolygenicArchitecture
import Calibrator.TransferLearningPGS

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

/-- **Cross-check: the within-deme coalescence time carries the same two.**
`PortabilityDrift.twoDemeIMEquilibriumETss` is `2` in units of `Nₑ`
generations, and that two is the ploidy: `E[T_within] = ploidy · Nₑ`
generations is `coalescentTimeScale`, which is `2 Nₑ`. Writing the constant
without saying so left a bare numeral in an equilibrium; this theorem says
which two it is. -/
theorem twoDemeIMEquilibriumETss_eq_ploidy (M : ℝ) :
    twoDemeIMEquilibriumETss M = ploidy := by
  unfold twoDemeIMEquilibriumETss ploidy; ring

end Ploidy

section Differentiation

/-- Mean allele frequency across two subgroups of equal weight.

    Empirical status: UNTESTED. -/
noncomputable def meanAlleleFreq (p₁ p₂ : ℝ) : ℝ := (p₁ + p₂) / 2

/-! ### The arithmetic mean of two, shared with the migration rates

`meanAlleleFreq` averages two subgroup allele frequencies;
`PopulationGeneticsFoundations.effectiveMigration` and
`PortabilityDrift.effectiveSymmetricMigration` average two directional
migration rates. Three different quantities, one map, and an equal-weight
convention that has to be the same equal-weight convention in all three or the
`F_ST` these feed disagrees with itself. -/

theorem effectiveMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    effectiveMigration m₁₂ m₂₁ = meanAlleleFreq m₁₂ m₂₁ := by
  unfold effectiveMigration meanAlleleFreq; ring

theorem effectiveSymmetricMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    effectiveSymmetricMigration m₁₂ m₂₁ = meanAlleleFreq m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration meanAlleleFreq; ring

/-- **Hudson's `F_ST` for two subgroups**, as one minus the ratio of mean
within-subgroup heterozygosity to total heterozygosity. Restored as a
definition so that `F` denotes a quantity rather than a name; it had been
deleted as unreferenced, which is the reason `F` in the spike was free to mean
anything.

    Empirical status: UNTESTED. Simulation recovers the spike constant against
    `F` measured this way (see `four_hudsonFst_eq_standardizedContrastVariance`
    below), but the estimator itself has not been checked against a simulated
    `F_ST`. -/
noncomputable def hudsonFst (p₁ p₂ : ℝ) : ℝ :=
  1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) /
    (ploidy * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

/-- Between-subgroup allele-frequency variance for an equal-weight split. -/
noncomputable def betweenSubgroupVariance (p₁ p₂ : ℝ) : ℝ := (p₁ - p₂) ^ 2 / 4

/-- **Cross-check: the fair two-point variance in `ImitationRigidity` is the
between-subgroup variance.** Both are `(a - b)² / 4`: the variance of a
two-point law with equal weights. One is used as a nonconcentration witness for
a resolvent and the other as the numerator of `F_ST`, and neither file knew the
other existed. -/
theorem fairTwoPointVariance_eq_betweenSubgroupVariance (a b : ℝ) :
    fairTwoPointVariance a b = betweenSubgroupVariance a b := by
  unfold fairTwoPointVariance betweenSubgroupVariance; ring

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

/-! **The island-model `F_ST` is now one definition.** It used to be written out
independently in several modules — `DemographicHistory.demoIslandModelFst`,
`PopulationGeneticsFoundations.islandModelFst`, `AncestrySpecificArchitecture.equilibriumFst`
and `PortabilityDrift.fstMigrationDriftEquilibrium` — each spelling out its own factor of
four, and this file carried a cross-check theorem per pair to keep them in step. The copies
are gone in favour of the single `fstMigrationDriftEquilibrium`, so the cross-checks have
nothing left to relate.

`equilibriumFst` is worth recording as a hazard: it took its arguments in the opposite
order to the other two, so the same call spelled the same way meant different things
depending on which copy was in scope. -/

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
  unfold presentDayPGSVariance pgsVarianceFromHet amEquilibriumVariance
  ring

/-! ### Tying the inlined genotype-variance restatements back to `ploidy`

Five definitions across five modules used to spell out `2 p (1 - p)`
independently, and none was related to any other, so a change to the ploidy
convention in one would have left the others silently disagreeing. Four of the
five are gone: `CovarianceStructure.genotypeVarianceAtLocus`,
`GeneticArchitectureDiscovery.tagGenotypeVariance` and
`StratificationConfounding.heterozygosity` were deleted and their references
repointed, and `AncestrySpecificPower.ancestryHeterozygosity` was renamed
`hweHeterozygosity`. What survives is one genotype variance and one
heterozygote frequency, both in `AncestrySpecificPower`, related there by
`hweHeterozygosity_eq_genotypeVarianceHWE`. These two theorems tie that pair
back to `ploidy`, so the convention still has exactly one place to change. -/

theorem genotypeVarianceHWE_eq_hwe (p : ℝ) :
    genotypeVarianceHWE p = hweGenotypeVariance p := by
  unfold genotypeVarianceHWE hweGenotypeVariance ploidy; ring

theorem hweHeterozygosity_eq_hwe (p : ℝ) :
    hweHeterozygosity p = hweGenotypeVariance p := by
  unfold hweHeterozygosity hweGenotypeVariance ploidy; ring

/-! ### Tying the island-model equilibrium back to the scaled rate

`1 / (1 + 4 Nₑ m)` used to be spelled out by several definitions across several modules,
and this section carried one bridge theorem per copy — three of them with identical
statements and identical proofs. There is now a single definition, so there is a single
bridge: it is the migration-drift equilibrium at the scaled migration rate. -/

theorem fstMigrationDriftEquilibrium_eq_scaled (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m =
      fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### Per-generation drift rate, written out in three modules

`1 / (2 Nₑ)` appears independently in `LongitudinalPortability`,
`DemographicHistory` and `LDDecayTheory` under three names. It is the
reciprocal of the coalescent time scale in each. -/

theorem driftLDCreationRate_eq_inv_timeScale (Ne : ℝ) :
    driftLDCreationRate Ne = 1 / coalescentTimeScale Ne := by
  unfold driftLDCreationRate; rw [coalescentTimeScale_eq]

theorem ldDecayRatePerGen_eq_inv_timeScale (Ne : ℝ) :
    ldDecayRatePerGen Ne = 1 / coalescentTimeScale Ne := by
  unfold ldDecayRatePerGen; rw [coalescentTimeScale_eq]

/-- **Cross-check: the `2 Nₑ` inside `coalFst` is the coalescent time scale.**
`coalFst t Ne = t / (t + 2 Nₑ)` is `t / (t + E[T_within])`, and `E[T_within]`
is `ploidy · Nₑ` generations. Writing the two inline left the constant free;
this states which two it is. -/
theorem coalFst_uses_coalescentTimeScale (t Ne : ℝ) :
    coalFst t Ne = t / (t + coalescentTimeScale Ne) := by
  unfold coalFst; rw [coalescentTimeScale_eq]

/-! ### The coalescent `F_ST` map, no longer written out twice

`DemographicHistory.fstFromCoalescenceTime` and
`PopulationGeneticsFoundations.coalFst` were the same function under two names.
`coalFst` is the one simulation validated as split `F_ST`, being unbiased
against branch-mode divergence where the drift formula was biased upward by up
to 28 percent, so it is the survivor; `fstFromCoalescenceTime` has been deleted
and its uses in `DemographicHistory` now call `coalFst` directly. -/

/-! ### The harmonic mean, no longer written out twice

`MetricSpecificPortability.f1ScoreMetric` and `OpenQuestions.f1Score` were the
same expression under two names in two modules, with no theorem relating them.
`f1ScoreMetric` has been deleted and `MetricSpecificPortability` now calls
`f1Score`. -/

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
      TransportedMetrics.gaussianAUCFromSignalVariance vSignal vNoise := by
  unfold equalVarianceGaussianAUCFromVariances
    TransportedMetrics.gaussianAUCFromSignalVariance
  ring_nf

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

/-! ### The last entangled uses

These carry the convention inside a larger expression. A relation still ties
them down; no definition needs rewriting. -/

theorem selectedDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) (s_correction : ℝ) :
    selectedDriftFactor Ne t s_correction
      = (1 - 1 / coalescentTimeScale Ne + s_correction) ^ t := by
  unfold selectedDriftFactor; rw [coalescentTimeScale_eq]

theorem SplitMigrationModel_scaledMigration_eq_ploidy_form
    (m : SplitMigrationModel) :
    SplitMigrationModel.scaledMigration m = 2 * ploidy * m.Ne * m.mig := by
  unfold SplitMigrationModel.scaledMigration ploidy; ring

theorem fstMigDriftNext_uses_timeScale (Ne m Fst : ℝ) :
    fstMigDriftNext Ne m Fst
      = (1 - 2 * m - 1 / coalescentTimeScale Ne) * Fst
        + 1 / coalescentTimeScale Ne := by
  unfold fstMigDriftNext; rw [coalescentTimeScale_eq]

theorem stabilizingPortability_uses_ploidy (r2_0 fst strength : ℝ) :
    stabilizingPortability r2_0 fst strength
      = r2_0 * (1 - ploidy * fst) * Real.exp (-strength * fst) := by
  unfold stabilizingPortability ploidy; ring_nf

theorem ibdFst_eq_ploidy_form (d N sigma_sq : ℝ) :
    ibdFst d N sigma_sq = d / (2 * ploidy * N * sigma_sq + d) := by
  unfold ibdFst ploidy; ring_nf

theorem EvolutionaryParameters_tau_uses_timeScale (p : EvolutionaryParameters) :
    EvolutionaryParameters.tau p = p.t_div / coalescentTimeScale p.Ne := by
  unfold EvolutionaryParameters.tau; rw [coalescentTimeScale_eq]

theorem sharedLDRetention_uses_ploidy (p : EvolutionaryParameters) :
    sharedLDRetention p = Real.exp (-ploidy * p.recomb * p.t_div) := by
  unfold sharedLDRetention ploidy; ring_nf

theorem demoSteppingStoneFst_eq_scaled (d Ne m σ_sq : ℝ) :
    demoSteppingStoneFst d Ne m σ_sq
      = d / (d + scaledMigrationRate Ne m * σ_sq) := by
  unfold demoSteppingStoneFst
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### The last seven

Each carries the convention in its own shape: inside a `let`, in a recursion
step, or under two nested decay factors. A relation reaches all of them. -/

theorem tauAt_uses_timeScale (g : GenerationalPopGenParameters) (t : ℕ) :
    GenerationalPopGenParameters.tauAt g t
      = (t : ℝ) / coalescentTimeScale g.Ne := by
  unfold GenerationalPopGenParameters.tauAt; rw [coalescentTimeScale_eq]

theorem diversifyingPortability_uses_ploidy (r2_0 fst lam_turn : ℝ) :
    diversifyingPortability r2_0 fst lam_turn
      = r2_0 * (1 - ploidy * fst) * (Real.exp (-lam_turn * fst)) ^ 2 := by
  unfold diversifyingPortability ploidy; ring_nf

theorem alleleFreqDivergenceRate_eq_scaled (Ne mu m_rate : ℝ) :
    alleleFreqDivergenceRate Ne mu m_rate
      = 1 / (coalescentTimeScale Ne *
          (1 + scaledMutationRate Ne mu + scaledMigrationRate Ne m_rate)) := by
  unfold alleleFreqDivergenceRate
  rw [coalescentTimeScale_eq, scaledMutationRate_eq_ploidy_form,
    scaledMigrationRate_eq_ploidy_form]
  unfold ploidy; ring_nf

theorem excessLDAfterBottleneck_uses_timeScale (N_b N_r : ℝ) (t_b t_r : ℕ) :
    excessLDAfterBottleneck N_b N_r t_b t_r
      = (1 - (1 - 1 / coalescentTimeScale N_b) ^ t_b)
        * (1 - 1 / coalescentTimeScale N_r) ^ t_r := by
  unfold excessLDAfterBottleneck; rw [coalescentTimeScale_eq, coalescentTimeScale_eq]

theorem fstMutationDriftTransient_uses_timeScale (θ t Ne : ℝ) :
    fstMutationDriftTransient θ t Ne
      = fstMutationDriftEquilibrium θ *
          (1 - Real.exp (-(1 + θ) * t / coalescentTimeScale Ne)) := by
  unfold fstMutationDriftTransient; rw [coalescentTimeScale_eq]

theorem MutationDriftModelAssumptions_fstTransient_uses_timeScale
    (m : MutationDriftModelAssumptions) :
    MutationDriftModelAssumptions.fstTransient m
      = m.fstEquilibrium *
          (1 - Real.exp (-(1 + m.theta) * m.t / coalescentTimeScale m.Ne)) := by
  unfold MutationDriftModelAssumptions.fstTransient
  rw [coalescentTimeScale_eq]

theorem hetMutationDriftRecurrence_step_uses_timeScale
    (Ne mu H₀ : ℝ) (t : ℕ) :
    hetMutationDriftRecurrence Ne mu H₀ (t + 1)
      = (1 - 1 / coalescentTimeScale Ne) * hetMutationDriftRecurrence Ne mu H₀ t
        + ploidy * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t) := by
  change
    (1 - 1 / (2 * Ne)) * hetMutationDriftRecurrence Ne mu H₀ t +
        2 * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t) = _
  rw [coalescentTimeScale_eq]
  unfold ploidy
  rfl

/-- Equilibrium heterozygosity under mutation-drift balance, `θ/(1 + θ)`,
written out with its own four. This is the last inline restatement of the
ploidy convention in the development. -/
theorem hetEquilibrium_eq_scaled (Ne mu : ℝ) :
    hetEquilibrium Ne mu
      = scaledMutationRate Ne mu / (1 + scaledMutationRate Ne mu) := by
  unfold hetEquilibrium
  rw [scaledMutationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### Shared primitives

Several groups of definitions across the development are the same map applied
to different quantities. Left unrelated, each is free to drift from the others;
naming the map once and relating them makes a divergence a failed proof. This
is the same device as `ploidy`, applied to structure rather than to a
constant. -/

/-- Convex combination, `α x + (1 - α) y`. -/
noncomputable def convexMix (α x y : ℝ) : ℝ := α * x + (1 - α) * y

theorem spikeAndSlabVariance_eq_convexMix (pi sl sm : ℝ) :
    spikeAndSlabVariance pi sl sm = convexMix pi sl sm := by
  unfold spikeAndSlabVariance convexMix; ring

theorem admixedAlleleFreq_eq_convexMix (α p_A p_B : ℝ) :
    admixedAlleleFreq α p_A p_B = convexMix α p_A p_B := by
  unfold admixedAlleleFreq convexMix; ring

theorem averagePhaseInteraction_eq_convexMix (freq_cis i_cis i_trans : ℝ) :
    averagePhaseInteraction freq_cis i_cis i_trans = convexMix freq_cis i_cis i_trans := by
  unfold averagePhaseInteraction convexMix; ring

theorem ancestrySpecificEffect_eq_convexMix (b1 b2 alpha : ℝ) :
    ancestrySpecificEffect b1 b2 alpha = convexMix alpha b1 b2 := by
  unfold ancestrySpecificEffect convexMix; ring

/-- Geometric decay, `(1 - r)^t`: LD across generations, recombination
survival along a genealogy, and admixture-LD decay are one map. -/
noncomputable def geometricDecay (r : ℝ) (t : ℕ) : ℝ := (1 - r) ^ t

theorem ldDecayPerGeneration_eq_geometricDecay (r : ℝ) (t : ℕ) :
    ldDecayPerGeneration r t = geometricDecay r t := by
  unfold ldDecayPerGeneration geometricDecay; ring_nf

theorem admixtureLDDecay_eq_geometricDecay (r : ℝ) (t : ℕ) :
    admixtureLDDecay r t = geometricDecay r t := by
  unfold admixtureLDDecay geometricDecay; ring_nf

theorem discreteRecombinationSurvival_eq_geometricDecay (r : ℝ) (t : ℕ) :
    discreteRecombinationSurvival r t = geometricDecay r t := by
  unfold discreteRecombinationSurvival geometricDecay; ring_nf

/-- One minus a ratio, `1 - a / b`: `F_ST` from a heterozygosity ratio, `F_ST`
from coalescence times, `R²` from a mean squared error, and residual efficacy
are one map. -/
noncomputable def oneMinusRatio (a b : ℝ) : ℝ := 1 - a / b

theorem fstFromHetRatio_eq_oneMinusRatio (H H₀ : ℝ) :
    fstFromHetRatio H H₀ = oneMinusRatio H H₀ := by
  unfold fstFromHetRatio oneMinusRatio; ring_nf

theorem hudsonFstFromCoalescenceTimes_eq_oneMinusRatio (ETss ETst : ℝ) :
    hudsonFstFromCoalescenceTimes ETss ETst = oneMinusRatio ETss ETst := by
  unfold hudsonFstFromCoalescenceTimes oneMinusRatio; ring_nf

/-- The PC-correction efficacy is the same `1 - a/b` map: what is corrected
away is one minus the fraction of the ancestry axis that survives correction,
exactly as `F_ST` is one minus the fraction of heterozygosity that survives
subdivision. The two are different quantities and must not drift into different
shapes. -/
theorem pcTargetAxisEfficacy_eq_oneMinusRatio (H Hres : ℝ) :
    pcTargetAxisEfficacy H Hres = oneMinusRatio Hres H := by
  unfold pcTargetAxisEfficacy oneMinusRatio; ring_nf

theorem r2FromMSE_eq_oneMinusRatio (mse varY : ℝ) :
    r2FromMSE mse varY = oneMinusRatio mse varY := by
  unfold r2FromMSE oneMinusRatio; ring_nf

/-! ### Retention and ratio maps

Three further groups are one map under several names. -/

/-- Retained fraction, `(1 - loss) · total`: the ascertainment-loss survivor,
the neutral portability ratio and the present-day PGS variance are one map. -/
noncomputable def retainedFraction (loss total : ℝ) : ℝ := (1 - loss) * total

theorem ascertainment_loss_eq_retainedFraction (coverage v_causal : ℝ) :
    ascertainment_loss coverage v_causal = retainedFraction coverage v_causal := by
  unfold ascertainment_loss retainedFraction; ring

theorem neutralPortabilityRatioLD_eq_retainedFraction (fst ld : ℝ) :
    neutralPortabilityRatioLD fst ld = retainedFraction fst ld := by
  unfold neutralPortabilityRatioLD retainedFraction; ring

theorem presentDayPGSVariance_eq_retainedFraction (V_A fst : ℝ) :
    presentDayPGSVariance V_A fst = retainedFraction fst V_A := by
  unfold presentDayPGSVariance pgsVarianceFromHet retainedFraction; ring

/-- Squared covariance over the product of variances: the transport-moment
explained `R²` and the PGS `R²` are one map. -/
theorem explainedR2FromTransportMoments_eq_pgsR2 (cov vs vy : ℝ) :
    explainedR2FromTransportMoments cov vs vy = pgsR2 cov vs vy := by
  unfold explainedR2FromTransportMoments pgsR2; ring_nf

/-! The two portability ratios were the same quotient of transported metrics,
written once in `SimulationValidation` and once in
`GeneticArchitectureDiscovery`. `sourceTargetPortabilityRatio` has been deleted
and `GeneticArchitectureDiscovery` now calls `mechanisticPortabilityRatio`. -/

end EquilibriumAgreements

end Calibrator
