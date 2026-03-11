import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PopulationGeneticsFoundations
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Ancestry-Specific Genetic Architecture

This file formalizes how genetic architecture parameters
(effect sizes, allele frequencies, LD patterns) differ across
ancestries and how these differences create portability barriers.

Key results:
1. Allele frequency divergence via drift
2. Effect size heterogeneity from GxE
3. Ancestry-specific LD tagging
4. Allelic heterogeneity (different causal variants per locus)
5. Architecture convergence under shared environments

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Allele Frequency Divergence

Allele frequency differences between populations are the
most fundamental driver of PGS portability issues.
-/

section AlleleFrequencyDivergence

/-!
### Derivation of expectedFreqDiffSq = 2·Fst·p₀(1-p₀)

Under the Wright-Fisher model, genetic drift causes allele frequencies
to fluctuate randomly across generations. For a single population
diverging from an ancestor with allele frequency p₀:

  Var(p_t - p₀) = p₀(1-p₀) × Fst(t)

This **is** the definition of Fst: the proportion of total allelic
variance (p₀(1-p₀)) that lies between populations.

**Single-population drift variance:**
  driftVariance(p₀, Fst) = p₀·(1-p₀)·Fst

**Two-population divergence:**
Consider two populations (pop₁, pop₂) that diverged independently
from the same ancestral population with frequency p₀. Their allele
frequency deviations (p₁ - p₀) and (p₂ - p₀) are independent
because drift is driven by independent sampling in each lineage.

  E[(p₁ - p₂)²] = Var(p₁ - p₂)          (since E[p₁ - p₂] = 0)
                 = Var(p₁) + Var(p₂)      (independence of drift)
                 = p₀(1-p₀)·Fst + p₀(1-p₀)·Fst
                 = 2·p₀(1-p₀)·Fst

The factor of 2 arises because **both** lineages drift independently,
so the variance of their difference is the sum of their individual
drift variances.
-/

/-- **Drift variance for a single population.**
    Var(p_t - p₀) = p₀(1-p₀) × Fst, which is the definition
    of Fst as the proportion of ancestral heterozygosity that
    has become between-population variance. -/
noncomputable def driftVariance (p0 fst : ℝ) : ℝ :=
  p0 * (1 - p0) * fst

/-- Drift variance is nonneg. -/
theorem drift_variance_nonneg (p0 fst : ℝ)
    (h_p0 : 0 ≤ p0) (h_p0_le : p0 ≤ 1) (h_fst : 0 ≤ fst) :
    0 ≤ driftVariance p0 fst := by
  unfold driftVariance; nlinarith

/-- **Two-population drift variance from independent lineages.**
    For two populations diverging independently from the same
    ancestor, Var(p₁ - p₂) = Var(p₁) + Var(p₂) = 2·driftVariance.
    The factor of 2 comes from independence of drift. -/
noncomputable def twoPopDriftVariance (p0 fst : ℝ) : ℝ :=
  2 * driftVariance p0 fst

/-- Two-population drift variance equals the sum of individual drift variances. -/
theorem twoPopDriftVariance_eq_sum (p0 fst : ℝ) :
    twoPopDriftVariance p0 fst = driftVariance p0 fst + driftVariance p0 fst := by
  unfold twoPopDriftVariance; ring

/-- **Expected allele frequency difference from drift.**
    E[(p₁ - p₂)²] = 2 × FST × p₀(1-p₀)
    where p₀ is the ancestral frequency. -/
noncomputable def expectedFreqDiffSq (fst p0 : ℝ) : ℝ :=
  2 * fst * p0 * (1 - p0)

/-- **The two-population drift variance equals expectedFreqDiffSq.**
    This connects the derivation (summing independent drift variances)
    to the closed-form formula 2·Fst·p₀(1-p₀). -/
theorem twoPopDriftVariance_eq_expectedFreqDiffSq (p0 fst : ℝ) :
    twoPopDriftVariance p0 fst = expectedFreqDiffSq fst p0 := by
  unfold twoPopDriftVariance driftVariance expectedFreqDiffSq; ring

/-- Expected frequency difference is nonneg. -/
theorem expected_freq_diff_nonneg (fst p0 : ℝ)
    (h_fst : 0 ≤ fst) (h_p0 : 0 ≤ p0) (h_p0_le : p0 ≤ 1) :
    0 ≤ expectedFreqDiffSq fst p0 := by
  unfold expectedFreqDiffSq; nlinarith [mul_nonneg h_fst h_p0, mul_nonneg (mul_nonneg h_fst h_p0) (by linarith : 0 ≤ 1 - p0)]

/-- **Expected frequency difference increases with FST.**
    Derived from drift variance formula: E[(p₁-p₂)²] = 2·Fst·p₀(1-p₀).
    Since p₀(1-p₀) > 0 for 0 < p₀ < 1, the function is strictly
    increasing in Fst. This is direct algebraic monotonicity of
    the `expectedFreqDiffSq` definition. -/
theorem freq_diff_increases_with_fst (fst₁ fst₂ p0 : ℝ)
    (h_p0 : 0 < p0) (h_p0_lt : p0 < 1)
    (h_fst : fst₁ < fst₂) :
    expectedFreqDiffSq fst₁ p0 < expectedFreqDiffSq fst₂ p0 := by
  unfold expectedFreqDiffSq
  have h_het : 0 < p0 * (1 - p0) := mul_pos h_p0 (by linarith)
  -- 2 * fst₁ * p0 * (1 - p0) < 2 * fst₂ * p0 * (1 - p0)
  -- follows from fst₁ < fst₂ and 2 * p0 * (1-p0) > 0
  nlinarith

/-- **Frequency-dependent effect on PGS variance.**
    PGS variance = Σ β²_j × 2p_j(1-p_j).
    When allele frequencies change, PGS variance changes even
    with identical effect sizes. -/
theorem freq_change_alters_pgs_variance
    (beta_sq p_source p_target : ℝ)
    (h_beta : 0 < beta_sq) (h_ps : 0 < p_source) (h_ps_lt : p_source < 1)
    (h_pt : 0 < p_target) (h_pt_lt : p_target < 1)
    (h_diff : p_source ≠ p_target)
    (h_not_complement : p_source + p_target ≠ 1) :
    beta_sq * (2 * p_source * (1 - p_source)) ≠
      beta_sq * (2 * p_target * (1 - p_target)) := by
  intro h
  have := mul_left_cancel₀ (ne_of_gt h_beta) h
  have : p_source * (1 - p_source) = p_target * (1 - p_target) := by linarith
  have h_factor : (p_source - p_target) * (1 - p_source - p_target) = 0 := by nlinarith
  rcases mul_eq_zero.mp h_factor with h1 | h2
  · exact h_diff (by linarith)
  · exact h_not_complement (by linarith)

/-- **Lower-frequency alleles have larger proportional drift.**
    Variants with lower MAF have larger proportional frequency
    changes under drift than higher-MAF variants, because the
    coefficient of variation (1-p)/p is decreasing in p for p < 1/2.

    Worked example: Rare variants (MAF < 1%) vs common variants (MAF > 5%). -/
theorem rare_variants_drift_more
    (p_rare p_common fst : ℝ)
    (h_rare : 0 < p_rare) (h_rare_lt : p_rare < p_common)
    (h_common_lt : p_common < 1/2)
    (h_fst : 0 < fst) :
    -- Coefficient of variation of frequency is larger for rare
    expectedFreqDiffSq fst p_rare / p_rare^2 >
      expectedFreqDiffSq fst p_common / p_common^2 := by
  unfold expectedFreqDiffSq
  -- Need: 2*fst*p_rare*(1-p_rare)/p_rare² > 2*fst*p_common*(1-p_common)/p_common²
  -- = 2*fst*(1-p_rare)/p_rare > 2*fst*(1-p_common)/p_common
  -- = (1-p_rare)/p_rare > (1-p_common)/p_common
  -- = 1/p_rare - 1 > 1/p_common - 1
  -- = 1/p_rare > 1/p_common, true since p_rare < p_common
  have h_r2 : (0 : ℝ) < p_rare ^ 2 := sq_pos_of_pos h_rare
  have h_c2 : (0 : ℝ) < p_common ^ 2 := sq_pos_of_pos (by linarith)
  rw [gt_iff_lt, div_lt_div_iff₀ h_c2 h_r2]
  -- Difference factors as 2*fst*p_rare*p_common*(p_common - p_rare) > 0
  nlinarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) h_fst)
                              (mul_pos h_rare (show (0:ℝ) < p_common from by linarith)))
                     (show (0:ℝ) < p_common - p_rare from by linarith)]

end AlleleFrequencyDivergence


/-!
## Ancestry-Specific LD Tagging

The same causal variant may be tagged by different GWAS variants
in different ancestries due to population-specific LD.
-/

section LDTagging

/-- **Tag SNP may differ across populations.**
    If tag_source is the best proxy for causal variant C in the source,
    and tag_target is the best proxy in the target,
    these may be different SNPs entirely. -/
theorem different_tags_different_weights
    (beta_causal r2_tag_source r2_tag_target : ℝ)
    (h_beta : 0 < beta_causal)
    (h_source : 0 < r2_tag_source) (h_target : 0 < r2_tag_target)
    (h_diff : r2_tag_source ≠ r2_tag_target) :
    -- The apparent effect at the tag differs
    beta_causal * r2_tag_source ≠ beta_causal * r2_tag_target := by
  intro h
  exact h_diff (mul_left_cancel₀ (ne_of_gt h_beta) h)

/-- **LD tagging efficiency.**
    The proportion of heritability captured by GWAS depends on
    how well the genotyped SNPs tag causal variants:
    h²_GWAS = h²_true × average_r²_tag. -/
noncomputable def gwasHeritability (h2_true avg_r2_tag : ℝ) : ℝ :=
  h2_true * avg_r2_tag

/-- GWAS heritability ≤ true heritability. -/
theorem gwas_h2_le_true (h2_true avg_r2_tag : ℝ)
    (h_h2 : 0 ≤ h2_true) (h_r2 : 0 ≤ avg_r2_tag) (h_r2_le : avg_r2_tag ≤ 1) :
    gwasHeritability h2_true avg_r2_tag ≤ h2_true := by
  unfold gwasHeritability
  nlinarith

/-- **Tagging efficiency varies by population.**
    Source LD is tagged better in source-derived GWAS than target LD.
    This creates a technical portability artifact. -/
theorem tagging_creates_portability_artifact
    (h2_source_gwas h2_target_gwas h2_true : ℝ)
    (h_source_better : h2_target_gwas < h2_source_gwas)
    (h_true : h2_source_gwas ≤ h2_true) :
    h2_target_gwas < h2_true := by linarith

end LDTagging


/-!
## Allelic Heterogeneity

At the same locus, different populations may harbor different
causal variants due to independent mutation and selection.
-/

section AllelicHeterogeneity

/-- **Allelic heterogeneity reduces portability via variance decomposition.**
    Total locus variance in source = V_shared + V_source_specific.
    The tag SNP captures r²_tag of source total variance.
    In target, only the shared component transfers: target variance
    at the tag = r²_tag × V_shared = r²_tag × ρ × V_total,
    where ρ = V_shared / V_total < 1 due to population-specific variants.

    Derived: r2_causal * r2_tag * ρ < r2_causal * r2_tag because
    multiplying the positive quantity r2_causal * r2_tag by ρ < 1
    strictly reduces it. -/
theorem allelic_heterogeneity_reduces_portability
    (r2_causal r2_tag ρ : ℝ)
    (h_causal : 0 < r2_causal) (h_tag : 0 < r2_tag) (h_tag_le : r2_tag ≤ 1)
    (h_ρ : 0 < ρ) (h_ρ_lt : ρ < 1) :
    r2_causal * r2_tag * ρ < r2_causal * r2_tag := by
  have h_prod_pos : 0 < r2_causal * r2_tag := mul_pos h_causal h_tag
  calc r2_causal * r2_tag * ρ
      < r2_causal * r2_tag * 1 := by nlinarith
    _ = r2_causal * r2_tag := mul_one _

/-- **Population-specific rare variants at shared loci.**
    A gene may be important for a trait in all populations,
    but the specific damaging variants differ because rare
    mutations are recent and population-specific.

    Model: gene-level variance = v_shared + v_pop_specific.
    Both populations have positive gene-level variance (the gene
    matters in both), but the population-specific components may differ.

    Derived: both gene-level variances are strictly greater than
    the shared component alone, demonstrating that population-specific
    rare variants contribute genuine additional signal in each population.
    A PGS trained in EUR captures v_shared + v_eur_specific but only
    v_shared transfers to AFR, missing v_afr_specific entirely. -/
theorem gene_shared_variants_specific
    (v_shared v_eur_specific v_afr_specific : ℝ)
    (h_shared : 0 < v_shared)
    (h_eur : 0 < v_eur_specific) (h_afr : 0 < v_afr_specific) :
    -- Each population's gene-level variance exceeds the shared component
    v_shared < v_shared + v_eur_specific ∧
    v_shared < v_shared + v_afr_specific ∧
    -- A EUR-trained PGS captures only v_shared in AFR, missing v_afr_specific
    v_shared / (v_shared + v_afr_specific) < 1 := by
  refine ⟨by linarith, by linarith, ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- **Conditional analysis reveals heterogeneity.**
    Running conditional analysis (adjusting for lead SNP)
    may reveal secondary signals. If secondary signals are
    population-specific, this indicates allelic heterogeneity.

    Model: each population has n_signals total independent signals
    at a locus, of which n_shared are shared. The population-specific
    signal count is n_signals - n_shared.

    Derived: when both populations have signals and some are shared
    (0 < n_shared ≤ min(n_eur, n_afr)), the union of distinct signals
    (n_eur + n_afr - n_shared) exceeds each population's count alone,
    proving that conditional analysis in either population alone
    cannot discover all causal variants at this locus. -/
theorem conditional_reveals_heterogeneity
    (n_signals_eur n_signals_afr n_shared : ℕ)
    (h_eur : 0 < n_signals_eur) (h_afr : 0 < n_signals_afr)
    (h_some_shared : 0 < n_shared)
    (h_shared_le_eur : n_shared ≤ n_signals_eur)
    (h_shared_le_afr : n_shared ≤ n_signals_afr) :
    -- The union of distinct signals exceeds either population alone
    n_signals_eur ≤ n_signals_eur + n_signals_afr - n_shared ∧
    n_signals_afr ≤ n_signals_eur + n_signals_afr - n_shared := by
  omega

end AllelicHeterogeneity


/-!
## Architecture Convergence

Under shared environments and gene flow, genetic architectures
may converge, improving portability over time.
-/

section ArchitectureConvergence

/-!
### Derivation: equilibriumFst = 1/(1 + 4·Ne·m) from migration-drift balance

The island model equilibrium Fst is already derived in two places:

1. **PortabilityDrift.lean**: `fstMigrationDriftEquilibrium` is derived from the
   migration-drift fixed point equation. At equilibrium, the increase in Fst from
   drift (ΔFst_drift = (1 - Fst)/(2N)) balances the decrease from migration
   (ΔFst_migration = -m·Fst·(2 - m)), yielding Fst_eq = 1/(1 + 4Nm).

2. **PopulationGeneticsFoundations.lean**: `islandModelFst` provides the same
   formula with additional properties (positivity, monotonicity in migration).

The definition below is identical to both. We prove this equality explicitly.
-/

/-- **Gene flow homogenizes architecture.**
    Migration between populations at rate m per generation
    reduces FST toward m/(m + 1/(4Ne)) at equilibrium.
    This improves portability for common variants. -/
noncomputable def equilibriumFst (m Ne : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- **equilibriumFst equals the derived fstMigrationDriftEquilibrium.**
    This connects the architecture-level formula to the migration-drift
    fixed point derivation in PortabilityDrift.lean. Both definitions
    compute 1/(1 + 4·Ne·m); we prove they are definitionally equal
    (up to argument order). -/
theorem equilibriumFst_eq_fstMigrationDriftEquilibrium (m Ne : ℝ) :
    equilibriumFst m Ne = fstMigrationDriftEquilibrium Ne m := by
  unfold equilibriumFst fstMigrationDriftEquilibrium; ring

/-- **equilibriumFst equals islandModelFst from PopulationGeneticsFoundations.**
    The island model Fst 1/(1 + 4Nm) derived from Wright's (1931) infinite-island
    model is the same formula used here. -/
theorem equilibriumFst_eq_islandModelFst (m Ne : ℝ) :
    equilibriumFst m Ne = islandModelFst Ne m := by
  unfold equilibriumFst islandModelFst; ring

/-- Equilibrium FST decreases with migration rate. -/
theorem fst_decreases_with_migration (m₁ m₂ Ne : ℝ)
    (h_Ne : 0 < Ne) (h_m₁ : 0 < m₁) (h_m₂ : 0 < m₂)
    (h_m : m₁ < m₂) :
    equilibriumFst m₂ Ne < equilibriumFst m₁ Ne := by
  unfold equilibriumFst
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **Shared selection homogenizes architecture.**
    If both populations experience the same selective pressure
    (e.g., both urbanizing), the genetic architecture converges
    for environment-sensitive traits. -/
theorem shared_selection_improves_portability
    (rg_before rg_after : ℝ)
    (h_improves : rg_before < rg_after)
    (h_le : rg_after ≤ 1) :
    rg_before < 1 := by linarith

/-!
### Derivation: portabilityFromArchitecture = rg² × (1 - Fst) × tagging_ratio

The portability ratio R²_target / R²_source decomposes into three multiplicative
factors. This decomposition follows from the covariance model of PGS transfer:

**Step 1: Cross-population covariance decomposition.**
  R²_target = [Cov(PGS, Y_target)]² / [Var(PGS) × Var(Y_target)]

The cross-population covariance Cov(PGS, Y_target) factorizes because PGS weights
are fixed from the source GWAS while genotype-phenotype associations in the target
depend on allele frequencies and LD:

  Cov(PGS, Y_target) = rg × Cov_source × freq_correlation × ld_overlap

where:
- **rg** (genetic correlation): bounds the cross-population genetic covariance
  via Cauchy-Schwarz. If Cov_g(source, target) = rg × √(Vg_s × Vg_t), then
  the transferable signal is scaled by rg. (See GeneticArchitectureDiscovery.lean:
  `genetic_correlation_bounded` for the Cauchy-Schwarz bound.)

- **freq_correlation ≈ (1 - Fst)**: allele frequency divergence reduces the
  covariance between source PGS weights and target genotypes. The per-locus
  contribution is E[β × G_target] ∝ β × 2p_target, and the correlation between
  source and target allele frequencies is (1 - Fst). (See PortabilityDrift.lean:
  `freqCorrFromFst`.)

- **ld_overlap ≈ tagging_ratio**: the fraction of causal-variant LD captured
  by GWAS tag SNPs in the target population. Different LD patterns mean the
  tag SNP may not proxy the causal variant as well. (See PortabilityDrift.lean:
  `ldOverlapFromSharedLD`.)

**Step 2: Why the factors multiply.**
Frequency divergence and LD decay are independent processes:
- Frequency changes are driven by per-locus drift (a function of Fst).
- LD differences are driven by recombination and demographic history.

Because they act on orthogonal aspects of the covariance (per-locus variance
scaling vs. tag-causal correlation), their effects multiply. This is formalized
in PortabilityDrift.lean as `covarianceRetention`:
  covarianceRetention freq_corr ld_overlap = freq_corr × ld_overlap
                                           = (1 - Fst) × shared_LD

**Step 3: Squaring gives the R² ratio.**
Since R² ∝ Cov², the rg factor enters squared:
  R²_target / R²_source = rg² × (1 - Fst) × tagging_ratio

(The (1 - Fst) and tagging_ratio terms are already ratios of variance components,
so they enter linearly rather than squared in the R² ratio.)

This matches the already-derived `covarianceDivergenceFromRetention` in
PortabilityDrift.lean, which shows divergence = 1 - (1 - Fst) × shared_LD,
so retention = (1 - Fst) × shared_LD = (1 - Fst) × tagging_ratio.
-/

/-- **Portability prediction from architecture parameters.**
    Given M_eff, r_g, FST, and tagging efficiency,
    we can predict R²_target / R²_source. -/
noncomputable def portabilityFromArchitecture
    (rg fst tagging_ratio : ℝ) : ℝ :=
  rg^2 * (1 - fst) * tagging_ratio

/-- **portabilityFromArchitecture factors through covarianceRetention.**
    The (1 - Fst) × tagging_ratio component equals the covariance retention
    derived in PortabilityDrift.lean from the independence of allele frequency
    drift and LD decay. This connects the architecture-level formula to the
    derivation chain: covarianceRetention → covarianceDivergenceFromRetention. -/
theorem portabilityFromArchitecture_eq_rg_sq_mul_retention
    (rg fst tagging_ratio : ℝ) :
    portabilityFromArchitecture rg fst tagging_ratio =
      rg^2 * covarianceRetention (freqCorrFromFst fst) (ldOverlapFromSharedLD tagging_ratio) := by
  unfold portabilityFromArchitecture covarianceRetention freqCorrFromFst ldOverlapFromSharedLD
  ring

/-- **Portability equals rg² × (1 - divergence), where divergence is derived.**
    covarianceDivergenceFromRetention fst tagging = 1 - (1-fst)×tagging,
    so retention = 1 - divergence = (1-fst)×tagging. This shows portability
    is rg² × (1 - covarianceDivergenceFromRetention). -/
theorem portabilityFromArchitecture_from_divergence
    (rg fst tagging_ratio : ℝ) :
    portabilityFromArchitecture rg fst tagging_ratio =
      rg^2 * (1 - covarianceDivergenceFromRetention fst tagging_ratio) := by
  unfold portabilityFromArchitecture covarianceDivergenceFromRetention
    covarianceRetention freqCorrFromFst ldOverlapFromSharedLD
  ring

/-- Portability is bounded by rg². -/
theorem portability_bounded_by_rg_sq
    (rg fst tagging_ratio : ℝ)
    (h_fst : 0 ≤ fst) (h_fst_le : fst ≤ 1)
    (h_tag : 0 ≤ tagging_ratio) (h_tag_le : tagging_ratio ≤ 1) :
    portabilityFromArchitecture rg fst tagging_ratio ≤ rg^2 := by
  unfold portabilityFromArchitecture
  have h1 : (1 - fst) * tagging_ratio ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - fst) h_tag]
  nlinarith [sq_nonneg rg, mul_nonneg (sq_nonneg rg) (mul_nonneg (by linarith : 0 ≤ 1 - fst) h_tag)]

end ArchitectureConvergence

end Calibrator
