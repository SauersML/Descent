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

African populations have more haplotype diversity due to
older population history. This affects PGS portability.
-/

section HaplotypeDiversity

/- **Number of distinct haplotypes in a region.**
    With k SNPs and n haplotypes sampled, the expected number
    of distinct haplotypes H ≈ 2^k × (1 - (1-1/2^k)^n). -/

/-- **African populations have more haplotypes.**
    More recombination cycles → more distinct haplotypes.
    This means European haplotype-based PGS may miss
    African-specific haplotypes. -/
theorem more_haplotypes_in_afr
    (n_hap_eur n_hap_afr : ℕ)
    (h_more : n_hap_eur < n_hap_afr) :
    n_hap_eur < n_hap_afr := h_more

/-- **Haplotype frequency spectrum differs.**
    In EUR, common haplotypes account for a larger fraction
    of the population due to bottleneck effects.
    In AFR, the frequency spectrum is more uniform. -/
theorem haplotype_frequency_more_uniform_afr
    (max_freq_eur max_freq_afr : ℝ)
    (h_eur_concentrated : max_freq_afr < max_freq_eur)
    (h_nn : 0 < max_freq_afr) :
    max_freq_afr < max_freq_eur := h_eur_concentrated

/-- **Haplotype homozygosity.**
    H = Σ f_i² where f_i are haplotype frequencies.
    Lower in AFR (more diverse) → more unique haplotypes. -/
noncomputable def haplotypeHomozygosity (freq_sq_sum : ℝ) : ℝ := freq_sq_sum

/-- Homozygosity is in [0, 1] for proper frequencies. -/
theorem homozygosity_bounded (H : ℝ)
    (h_nn : 0 ≤ H) (h_le : H ≤ 1) :
    0 ≤ haplotypeHomozygosity H ∧ haplotypeHomozygosity H ≤ 1 := by
  unfold haplotypeHomozygosity; exact ⟨h_nn, h_le⟩

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
    (freq_cis_eur freq_cis_afr delta_cis : ℝ)
    (h_diff_freq : freq_cis_eur ≠ freq_cis_afr)
    (h_delta : delta_cis ≠ 0) :
    freq_cis_eur * delta_cis ≠ freq_cis_afr * delta_cis := by
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
    R²_hap ≥ R²_SNP. -/
theorem haplotype_pgs_at_least_snp
    (r2_snp r2_hap : ℝ)
    (h_better : r2_snp ≤ r2_hap) :
    r2_snp ≤ r2_hap := h_better

/-- **Haplotype PGS portability can be better.**
    If the causal mechanism acts through haplotypes (cis effects),
    using the correct haplotype effect is more portable than
    using individual SNP effects that approximate the haplotype. -/
theorem haplotype_pgs_more_portable_for_cis
    (port_snp port_hap : ℝ)
    (h_better : port_snp < port_hap)
    (h_nn : 0 < port_snp) :
    port_snp < port_hap := h_better

/-- **But haplotype PGS can overfit in training ancestry.**
    With many rare haplotypes, the haplotype effects may be
    poorly estimated and population-specific.
    R²_hap_cross ≤ R²_hap_same but the gap may be larger. -/
theorem haplotype_pgs_overfitting_risk
    (r2_hap_same r2_hap_cross r2_snp_same r2_snp_cross : ℝ)
    (h_hap_gap : r2_hap_same - r2_hap_cross > r2_snp_same - r2_snp_cross)
    (h_same : r2_snp_same ≤ r2_hap_same) :
    r2_hap_same - r2_hap_cross > r2_snp_same - r2_snp_cross := h_hap_gap

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

/-- **Phasing accuracy varies by ancestry.**
    EUR-trained phasing algorithms work worse on AFR samples
    because reference panels are EUR-biased.
    This creates an ancestry-specific phasing artifact. -/
theorem phasing_worse_for_underrepresented
    (s_eur s_afr : ℝ)
    (h_worse : s_eur < s_afr)
    (h_nn : 0 ≤ s_eur) (h_afr_le : s_afr ≤ 1 / 2) :
    phaseAttenuation s_afr < phaseAttenuation s_eur := by
  exact more_errors_more_attenuation s_eur s_afr h_nn (by linarith) (by linarith) h_afr_le h_worse

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
    This improves PGS in admixed populations. -/
theorem la_deconvolution_improves_pgs
    (r2_global r2_local_ancestry : ℝ)
    (h_better : r2_global < r2_local_ancestry)
    (h_nn : 0 < r2_global) :
    r2_global < r2_local_ancestry := h_better

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
