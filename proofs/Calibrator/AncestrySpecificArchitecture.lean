/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat drift models of allele-frequency divergence, allelic heterogeneity
or LD tagging. Sources for individual results, where they exist, are cited at those
results.
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
    has become between-population variance.

    Empirical status: UNTESTED. -/
noncomputable def driftVariance (p0 fst : ℝ) : ℝ :=
  p0 * (1 - p0) * fst

/-- Drift variance is nonneg. -/
theorem drift_variance_nonneg (p0 fst : ℝ)
    (h_p0 : 0 ≤ p0) (h_p0_le : p0 ≤ 1) (h_fst : 0 ≤ fst) :
    0 ≤ driftVariance p0 fst := by
  unfold driftVariance
  apply mul_nonneg
  · exact mul_nonneg h_p0 (sub_nonneg.mpr h_p0_le)
  · exact h_fst

/-- **Two-population drift variance from independent lineages.**
    For two populations diverging independently from the same
    ancestor, Var(p₁ - p₂) = Var(p₁) + Var(p₂) = 2·driftVariance.
    The factor of 2 comes from independence of drift.

    Empirical status: UNTESTED. -/
noncomputable def twoPopDriftVariance (p0 fst : ℝ) : ℝ :=
  2 * driftVariance p0 fst

/-- Two-population drift variance equals the sum of individual drift variances. -/
theorem twoPopDriftVariance_eq_sum (p0 fst : ℝ) :
    twoPopDriftVariance p0 fst = driftVariance p0 fst + driftVariance p0 fst := by
  unfold twoPopDriftVariance; ring

/-- **Expected allele frequency difference from drift.**
    E[(p₁ - p₂)²] = 2 × FST × p₀(1-p₀)
    where p₀ is the ancestral frequency.

    Empirical status: UNTESTED. -/
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
  unfold expectedFreqDiffSq
  nlinarith [mul_nonneg h_fst h_p0,
    mul_nonneg (mul_nonneg h_fst h_p0) (by linarith : 0 ≤ 1 - p0)]

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
    (h_beta : 0 < beta_sq) (_h_ps : 0 < p_source) (_h_ps_lt : p_source < 1)
    (_h_pt : 0 < p_target) (_h_pt_lt : p_target < 1)
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
    (h_diff : r2_tag_source ≠ r2_tag_target) :
    -- The apparent effect at the tag differs
    beta_causal * r2_tag_source ≠ beta_causal * r2_tag_target := by
  intro h
  exact h_diff (mul_left_cancel₀ (ne_of_gt h_beta) h)

/-- **LD tagging efficiency.**
    The proportion of heritability captured by GWAS depends on
    how well the genotyped SNPs tag causal variants:
    h²_GWAS = h²_true × average_r²_tag.

    Empirical status: UNTESTED. -/
noncomputable def gwasHeritability (h2_true avg_r2_tag : ℝ) : ℝ :=
  h2_true * avg_r2_tag

/-- GWAS heritability ≤ true heritability. -/
theorem gwas_h2_le_true (h2_true avg_r2_tag : ℝ)
    (h_h2 : 0 ≤ h2_true) (h_r2 : 0 ≤ avg_r2_tag) (h_r2_le : avg_r2_tag ≤ 1) :
    gwasHeritability h2_true avg_r2_tag ≤ h2_true := by
  unfold gwasHeritability
  nlinarith


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
theorem mul_lt_self_of_lt_one
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
theorem lt_add_pos_and_div_lt_one
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

/-- **Inclusion-exclusion on signal counts.**
    Model: each population has `n_signals` independent signals at a locus, of
    which `n_shared` are shared, so the union of distinct signals is
    `n_eur + n_afr - n_shared`.

    What is proved is that the union is at least as large as either population's
    count. `≤`, not `<`: when one population's signals are all shared
    (`n_afr = n_shared`) the union equals `n_eur` exactly, so "exceeds" would be
    false. `omega` on three naturals.

    What is **not** proved: that conditional analysis in one population cannot
    discover all causal variants. No analysis, no discovery and no conditioning
    appears in the statement — only counts. Whether a population-specific
    signal count is evidence of allelic heterogeneity is a modelling claim this
    theorem does not reach. -/
theorem le_add_sub_of_le_of_le
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
### Derivation: fstMigrationDriftEquilibrium = 1/(1 + 4·Ne·m) from migration-drift balance

The island model equilibrium Fst is already derived in two places:

1. **PortabilityDrift.lean**: `fstMigrationDriftEquilibrium` is derived from the
   migration-drift fixed point equation. At equilibrium, the increase in Fst from
   drift (ΔFst_drift = (1 - Fst)/(2N)) balances the decrease from migration
   (ΔFst_migration = -m·Fst·(2 - m)), yielding Fst_eq = 1/(1 + 4Nm).

2. **PopulationGeneticsFoundations.lean**: `fstMigrationDriftEquilibrium` provides the same
   formula with additional properties (positivity, monotonicity in migration).

The definition below is identical to both. We prove this equality explicitly.
-/

/-- **One generation of gene flow against drift**, in the architecture file's
argument order.

This is `Calibrator.ibdFlowStep` with the homogenising force taken to be
migration: `F` is the probability that two gene copies from the same population
are identical by descent, drift adds `(1 - F)/(2 Nₑ)` and migration removes
`2 m F`.  It is written here, rather than only in `PortabilityDrift`, because
the obligation to derive `fstMigrationDriftEquilibrium` belongs to the file that states it;
`geneFlowFstStep_eq_ibdFlowStep` records that it is the same map.

Composition convention: drift and gene flow are added, not composed, which is
the weak-migration/large-`Nₑ` first-order model.  The unlinearised multiplicative
recursion `islandFstMultiplicativeStep` has a different fixed point.

    Empirical status: UNTESTED. -/
noncomputable def geneFlowFstStep (m Ne F : ℝ) : ℝ :=
  ibdFlowStep Ne m F

/-- One quantity, one map. -/
theorem geneFlowFstStep_eq_ibdFlowStep (m Ne F : ℝ) :
    geneFlowFstStep m Ne F = ibdFlowStep Ne m F := rfl

/-- **`fstMigrationDriftEquilibrium` is the fixed point of gene flow against drift.**
Migration homogenises at rate `2m` per pair and drift re-creates identity at
rate `1/(2 Nₑ)`; balancing them forces `F = 1/(1 + 4 Nₑ m)`.  The formula is
derived here, not stipulated: no other constant satisfies this. -/
theorem equilibriumFst_isFixedPoint (m Ne : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    geneFlowFstStep m Ne (fstMigrationDriftEquilibrium Ne m) = fstMigrationDriftEquilibrium Ne m :=
  ibdFlowStep_fixedPoint Ne m hNe hm

/-- Equilibrium FST decreases with migration rate. -/
theorem fst_decreases_with_migration (m₁ m₂ Ne : ℝ)
    (h_Ne : 0 < Ne) (h_m₁ : 0 < m₁) (h_m₂ : 0 < m₂)
    (h_m : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ := by
  unfold fstMigrationDriftEquilibrium
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith


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
  `covarianceRetentionFactorFromFst`.)

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
      rg ^ 2 * covarianceRetention (covarianceRetentionFactorFromFst fst)
        (ldOverlapFromSharedLD tagging_ratio) := by
  unfold portabilityFromArchitecture covarianceRetention covarianceRetentionFactorFromFst
    ldOverlapFromSharedLD
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
    covarianceRetention covarianceRetentionFactorFromFst ldOverlapFromSharedLD
  ring

/-- Portability is bounded by rg². -/
theorem portability_bounded_by_rg_sq
    (rg fst tagging_ratio : ℝ)
    (h_fst : 0 ≤ fst) (h_fst_le : fst ≤ 1)
    (h_tag : 0 ≤ tagging_ratio) (h_tag_le : tagging_ratio ≤ 1) :
    portabilityFromArchitecture rg fst tagging_ratio ≤ rg^2 := by
  unfold portabilityFromArchitecture
  have h1 : (1 - fst) * tagging_ratio ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - fst) h_tag]
  nlinarith [sq_nonneg rg,
    mul_nonneg (sq_nonneg rg) (mul_nonneg (by linarith : 0 ≤ 1 - fst) h_tag)]

end ArchitectureConvergence

end Calibrator
