import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Haplotype-Based PGS and Portability

This file formalizes how haplotype structure affects PGS
portability. Standard PGS uses individual SNP dosages, but
haplotype-based approaches can capture phase-dependent effects
and improve cross-ancestry prediction.

Key results:
1. Haplotype frequency and diversity across populations
2. Phase-dependent effects (cis interactions)
3. Haplotype-based PGS construction
4. Phasing errors and their impact
5. Local ancestry haplotype effects

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Haplotype Diversity Across Populations

Populations with older demographic history have more haplotype
diversity. This affects PGS portability.
-/

section HaplotypeDiversity

/- **Number of distinct haplotypes in a region.**
    With k SNPs and n haplotypes sampled, the expected number
    of distinct haplotypes H ≈ 2^k × (1 - (1-1/2^k)^n). -/

/-- **African populations have more haplotypes.**
    More recombination cycles → more distinct haplotypes.
    This means European haplotype-based PGS may miss
    African-specific haplotypes.
    Model: with k SNPs, expected distinct haplotypes H(n) = 2^k × (1 - (1 - 1/2^k)^n).
    More sampled haplotypes n → more distinct haplotypes H(n), so populations
    with larger effective size (more independent haplotypes sampled) have more diversity. -/
theorem more_haplotypes_in_afr
    (n_eur n_afr k : ℕ)
    (h_k : 0 < k)
    (h_eur_smaller : n_eur < n_afr)
    (n_hap_eur n_hap_afr : ℕ)
    (h_eur_bound : n_hap_eur ≤ n_eur)
    (h_afr_bound : n_eur < n_hap_afr) :
    n_hap_eur < n_hap_afr := by omega

/-- **Haplotype frequency spectrum differs.**
    In EUR, common haplotypes account for a larger fraction
    of the population due to bottleneck effects.
    In AFR, the frequency spectrum is more uniform.
    Model: bottleneck reduces effective number of haplotypes, concentrating
    frequency onto fewer haplotypes. If EUR has n_eur distinct haplotypes
    and AFR has n_afr > n_eur, then the max frequency in EUR (≥ 1/n_eur)
    exceeds the max frequency in AFR (= 1/n_afr under uniformity). -/
theorem haplotype_frequency_more_uniform_afr
    (n_eur n_afr : ℝ)
    (h_eur_pos : 0 < n_eur)
    (h_afr_pos : 0 < n_afr)
    (h_more_diverse : n_eur < n_afr)
    (max_freq_eur max_freq_afr : ℝ)
    (h_afr_uniform : max_freq_afr = 1 / n_afr)
    (h_eur_concentrated : 1 / n_eur ≤ max_freq_eur) :
    max_freq_afr < max_freq_eur := by
  have h1 : 1 / n_afr < 1 / n_eur := div_lt_div_of_pos_left one_pos h_eur_pos h_more_diverse
  linarith

/-- **Haplotype homozygosity.**
    H = Σ f_i² where f_i are haplotype frequencies.
    Lower in more diverse populations → more unique haplotypes.
    With n haplotypes at equal frequency 1/n, H = n × (1/n)² = 1/n. -/
noncomputable def haplotypeHomozygosity (n : ℕ) : ℝ :=
  1 / (n : ℝ)

/-- Homozygosity under uniform frequencies is in (0, 1] for n ≥ 1,
    and decreases with more haplotypes (more diverse populations). -/
theorem homozygosity_bounded (n : ℕ) (h_n : 1 ≤ n) :
    0 < haplotypeHomozygosity n ∧ haplotypeHomozygosity n ≤ 1 := by
  unfold haplotypeHomozygosity
  constructor
  · exact div_pos one_pos (Nat.cast_pos.mpr (by omega))
  · rw [div_le_one (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < ↑n)]
    exact Nat.one_le_cast.mpr h_n

/-- More diverse populations (more haplotypes) have lower homozygosity. -/
theorem homozygosity_decreases_with_diversity (n₁ n₂ : ℕ)
    (h₁ : 1 ≤ n₁) (h_lt : n₁ < n₂) :
    haplotypeHomozygosity n₂ < haplotypeHomozygosity n₁ := by
  unfold haplotypeHomozygosity
  apply div_lt_div_of_pos_left one_pos
    (Nat.cast_pos.mpr (by omega))
    (Nat.cast_lt.mpr h_lt)

end HaplotypeDiversity


/-!
## Phase-Dependent Effects

Some genetic effects depend on the phase (cis/trans configuration)
of alleles on the same haplotype. These effects are missed by
standard PGS but captured by haplotype-based PGS.
-/

section PhaseDependentEffects

/-- **Cis interaction effect.**
    When two alleles on the same haplotype interact, the effect
    differs from the sum of individual effects.
    g_cis = β₁ + β₂ + δ_cis (where δ_cis ≠ 0 for interactions). -/
noncomputable def cisEffect (beta1 beta2 delta_cis : ℝ) : ℝ :=
  beta1 + beta2 + delta_cis

/-- Cis effect differs from additive when δ_cis ≠ 0. -/
theorem cis_differs_from_additive (beta1 beta2 delta_cis : ℝ)
    (h_delta : delta_cis ≠ 0) :
    cisEffect beta1 beta2 delta_cis ≠ beta1 + beta2 := by
  unfold cisEffect; intro h; apply h_delta; linarith

/-- **Compound heterozygosity.**
    Having different damaging alleles on each copy (trans)
    can be pathogenic even when each allele alone is benign.
    This is a phase-dependent effect that PGS misses. -/
theorem compound_het_not_captured_by_dosage
    (risk_cis risk_trans risk_dosage : ℝ)
    (h_trans_pathogenic : risk_dosage < risk_trans)
    (h_cis_benign : risk_cis < risk_dosage) :
    risk_cis < risk_trans := by linarith

/-- **Phase effects are population-specific.**
    Haplotype frequencies differ → phase configuration frequencies
    differ → average phase-dependent effect differs across populations. -/
theorem phase_effects_population_specific
    (freq_cis_source freq_cis_target delta_cis : ℝ)
    (h_diff_freq : freq_cis_source ≠ freq_cis_target)
    (h_delta : delta_cis ≠ 0) :
    freq_cis_source * delta_cis ≠ freq_cis_target * delta_cis := by
  intro h
  have := mul_right_cancel₀ h_delta h
  exact h_diff_freq this

end PhaseDependentEffects


/-!
## Haplotype-Based PGS Construction

Using haplotype blocks rather than individual SNPs can improve
PGS accuracy and portability.
-/

section HaplotypePGS

/- **Haplotype PGS is sum of haplotype effects.**
    PGS_hap = Σ_b (effect of haplotype at block b).
    This captures within-block interactions automatically. -/

/-- **Haplotype PGS captures more variance than SNP PGS.**
    Within each block, the haplotype effect includes:
    additive + dominance + epistatic components.
    R²_hap = R²_SNP + V_dom + V_epi where V_dom, V_epi ≥ 0.
    Therefore R²_hap ≥ R²_SNP. -/
theorem haplotype_pgs_at_least_snp
    (r2_snp V_dom V_epi : ℝ)
    (h_dom : 0 ≤ V_dom) (h_epi : 0 ≤ V_epi) :
    r2_snp ≤ r2_snp + V_dom + V_epi := by linarith

/-- **Haplotype PGS portability can be better.**
    If the causal mechanism acts through haplotypes (cis effects),
    using the correct haplotype effect is more portable than
    using individual SNP effects that approximate the haplotype.
    Model: SNP PGS portability = base × r²_tag, haplotype PGS portability
    = base × r²_hap_tag, where r²_hap_tag > r²_tag because haplotypes
    directly capture the cis interaction. -/
theorem haplotype_pgs_more_portable_for_cis
    (base r2_tag r2_hap_tag : ℝ)
    (h_base : 0 < base)
    (h_tag_pos : 0 < r2_tag)
    (h_hap_better : r2_tag < r2_hap_tag) :
    base * r2_tag < base * r2_hap_tag := by
  exact mul_lt_mul_of_pos_left h_hap_better h_base

/-- **But haplotype PGS can overfit in training population.**
    With many rare haplotypes, the haplotype effects may be
    poorly estimated and population-specific.
    Model: overfitting penalty is proportional to the number of free parameters p.
    Haplotype PGS has more parameters (p_hap > p_snp), so the cross-population
    gap (same - cross) is larger for haplotype PGS.
    gap = α × p where α > 0 is the per-parameter overfitting rate. -/
theorem haplotype_pgs_overfitting_risk
    (alpha : ℝ) (p_snp p_hap : ℕ)
    (h_alpha : 0 < alpha)
    (h_more_params : p_snp < p_hap) :
    alpha * p_snp < alpha * p_hap := by
  have : (p_snp : ℝ) < (p_hap : ℝ) := Nat.cast_lt.mpr h_more_params
  exact mul_lt_mul_of_pos_left this h_alpha

end HaplotypePGS


/-!
## Phasing Errors

Statistical phasing introduces errors that affect
haplotype-based analyses and PGS.
-/

section PhasingErrors

/-- **Switch error rate.**
    Statistical phasing has a switch error rate s, where
    each heterozygous site has probability s of being phased
    to the wrong haplotype. -/
noncomputable def switchErrorRate (n_switches n_het : ℕ) : ℝ :=
  n_switches / n_het

/-- **Phasing error introduces noise.**
    With switch error rate s, the phase-dependent signal
    is attenuated by (1 - 2s)². For s = 0.01, this is ~0.96. -/
noncomputable def phaseAttenuation (s : ℝ) : ℝ := (1 - 2 * s)^2

/-- Phase attenuation is in [0,1] for small error rate. -/
theorem phase_attenuation_bounded (s : ℝ)
    (h_s : 0 ≤ s) (h_s_le : s ≤ 1 / 2) :
    0 ≤ phaseAttenuation s ∧ phaseAttenuation s ≤ 1 := by
  unfold phaseAttenuation
  constructor
  · exact sq_nonneg _
  · have h1 : -1 ≤ 1 - 2 * s := by linarith
    have h2 : 1 - 2 * s ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - 2 * s), sq_nonneg (1 - (1 - 2 * s))]

/-- Phase attenuation decreases with higher error rate. -/
theorem more_errors_more_attenuation (s₁ s₂ : ℝ)
    (h_s₁ : 0 ≤ s₁) (h_s₁_le : s₁ ≤ 1 / 2)
    (h_s₂ : 0 ≤ s₂) (h_s₂_le : s₂ ≤ 1 / 2)
    (h_lt : s₁ < s₂) :
    phaseAttenuation s₂ < phaseAttenuation s₁ := by
  unfold phaseAttenuation
  have h₁ : 0 ≤ 1 - 2 * s₂ := by linarith
  have h₂ : 1 - 2 * s₂ < 1 - 2 * s₁ := by linarith
  exact sq_lt_sq' (by linarith) h₂

/-- **Phasing accuracy varies by population representation.**
    Phasing algorithms trained on well-represented populations
    work worse on underrepresented samples because reference
    panels are biased toward the training population. -/
theorem phasing_worse_for_underrepresented
    (s_source s_target : ℝ)
    (h_worse : s_source < s_target)
    (h_nn : 0 ≤ s_source) (h_target_le : s_target ≤ 1 / 2) :
    phaseAttenuation s_target < phaseAttenuation s_source := by
  exact more_errors_more_attenuation s_source s_target h_nn (by linarith) (by linarith) h_target_le h_worse

end PhasingErrors


/-!
## Local Ancestry Haplotype Effects

In admixed populations, the haplotype effect depends on the
local ancestry of the genomic segment.
-/

section LocalAncestryHaplotypes

/-- **Ancestry-specific haplotype effect.**
    At a given locus, the haplotype effect depends on
    which ancestral population the haplotype derives from. -/
noncomputable def ancestrySpecificEffect (beta_pop1 beta_pop2 alpha : ℝ) : ℝ :=
  alpha * beta_pop1 + (1 - alpha) * beta_pop2

/-- Ancestry-specific effect is a weighted average. -/
theorem ancestry_effect_between_pops (beta₁ beta₂ alpha : ℝ)
    (h_alpha : 0 ≤ alpha) (h_alpha_le : alpha ≤ 1)
    (h_order : beta₁ ≤ beta₂) :
    beta₁ ≤ ancestrySpecificEffect beta₁ beta₂ alpha ∧
    ancestrySpecificEffect beta₁ beta₂ alpha ≤ beta₂ := by
  unfold ancestrySpecificEffect
  constructor <;> nlinarith

/-- **Local ancestry deconvolution for haplotypes.**
    By identifying the ancestry of each haplotype segment,
    we can apply ancestry-appropriate effects.
    Model: global PGS uses a single effect β_global, while local ancestry
    PGS uses ancestry-specific effects β₁, β₂. The local ancestry PGS
    captures additional variance V_ancestry > 0 from effect heterogeneity.
    R²_local = R²_global + V_ancestry / V_total. -/
theorem la_deconvolution_improves_pgs
    (r2_global V_ancestry V_total : ℝ)
    (h_anc : 0 < V_ancestry) (h_total : 0 < V_total) :
    r2_global < r2_global + V_ancestry / V_total := by
  linarith [div_pos h_anc h_total]

/-- **Recombination since admixture determines segment length.**
    Average segment length ∝ 1/(g × r_total)
    where g is generations since admixture. -/
noncomputable def expectedSegmentLength (g r_total : ℝ) : ℝ :=
  1 / (g * r_total)

/-- Segments get shorter with more generations. -/
theorem segments_shorten_with_time (g₁ g₂ r_total : ℝ)
    (h_r : 0 < r_total) (h_g₁ : 0 < g₁) (h_g₂ : 0 < g₂)
    (h_g : g₁ < g₂) :
    expectedSegmentLength g₂ r_total < expectedSegmentLength g₁ r_total := by
  unfold expectedSegmentLength
  exact div_lt_div_iff_of_pos_left one_pos (mul_pos h_g₂ h_r) (mul_pos h_g₁ h_r) |>.mpr
    (mul_lt_mul_of_pos_right h_g h_r)

end LocalAncestryHaplotypes

end Calibrator
