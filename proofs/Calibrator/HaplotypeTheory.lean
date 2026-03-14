import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

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

noncomputable def expectedDistinctHaplotypes (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (1 - (1 - 1 / ((2 : ℝ) ^ k)) ^ n)

/-- The occupancy-model expectation is strictly increasing in the number of sampled haplotypes
    whenever at least two haplotypes are possible in the region (`k > 0`). -/
theorem expectedDistinctHaplotypes_strictMono
    (k : ℕ) (h_k : 0 < k) :
    StrictMono (expectedDistinctHaplotypes k) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  let m : ℝ := (2 : ℝ) ^ k
  have h_m_pos : 0 < m := by
    dsimp [m]
    positivity
  have h_m_gt_one : 1 < m := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_k) with ⟨k', rfl⟩
    dsimp [m]
    have h_one_le_pow : (1 : ℝ) ≤ (2 : ℝ) ^ k' := by
      exact_mod_cast (Nat.one_le_pow k' 2 (by decide : 0 < 2))
    calc
      (1 : ℝ) < 2 := one_lt_two
      _ ≤ 2 * (2 : ℝ) ^ k' := by nlinarith
      _ = (2 : ℝ) ^ (Nat.succ k') := by simp [pow_succ, mul_comm]
  have h_q_pos : 0 < 1 - 1 / m := by
    have h_inv_lt_one : 1 / m < 1 := by
      rw [div_lt_one h_m_pos]
      exact h_m_gt_one
    exact sub_pos.mpr h_inv_lt_one
  have h_step :
      expectedDistinctHaplotypes k (n + 1) =
        expectedDistinctHaplotypes k n + (1 - 1 / m) ^ n := by
    unfold expectedDistinctHaplotypes
    dsimp [m]
    rw [pow_succ]
    field_simp [h_m_pos.ne']
    ring
  have h_increment_pos : 0 < (1 - 1 / m) ^ n := pow_pos h_q_pos n
  calc
    expectedDistinctHaplotypes k n
      < expectedDistinctHaplotypes k n + (1 - 1 / m) ^ n := by linarith
    _ = expectedDistinctHaplotypes k (n + 1) := h_step.symm

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
    (h_eur_smaller : n_eur < n_afr) :
    expectedDistinctHaplotypes k n_eur < expectedDistinctHaplotypes k n_afr := by
  exact expectedDistinctHaplotypes_strictMono k h_k h_eur_smaller

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
noncomputable def haplotypeHomozygosity {α : Type*} [Fintype α] (freq : α → ℝ) : ℝ :=
  ∑ i, freq i ^ 2

/-- For any valid haplotype frequency distribution, homozygosity is in `(0, 1]`. -/
theorem homozygosity_bounded {α : Type*} [Fintype α] (freq : α → ℝ)
    (h_nonneg : ∀ i, 0 ≤ freq i)
    (h_sum : ∑ i, freq i = 1) :
    0 < haplotypeHomozygosity freq ∧ haplotypeHomozygosity freq ≤ 1 := by
  have h_nonneg_total : 0 ≤ haplotypeHomozygosity freq := by
    unfold haplotypeHomozygosity
    exact Fintype.sum_nonneg fun i ↦ sq_nonneg (freq i)
  have h_ne_zero : haplotypeHomozygosity freq ≠ 0 := by
    intro h_zero
    have h_sq_zero : ∀ i, freq i ^ 2 = 0 := by
      have :
          (∑ i, freq i ^ 2) = 0 := by
        simpa [haplotypeHomozygosity] using h_zero
      have h_sq_zero_fun :
          (fun i ↦ freq i ^ 2) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg fun i ↦ sq_nonneg (freq i)).1 this
      intro i
      exact congrFun h_sq_zero_fun i
    have h_freq_zero : ∀ i, freq i = 0 := fun i ↦ sq_eq_zero_iff.mp (h_sq_zero i)
    have h_total_zero : (∑ i, freq i) = 0 := by simp [h_freq_zero]
    linarith
  have h_le_one : haplotypeHomozygosity freq ≤ 1 := by
    unfold haplotypeHomozygosity
    calc
      ∑ i, freq i ^ 2 ≤ (∑ i, freq i) ^ 2 := by
        simpa using
          (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := freq)
            fun i _ ↦ h_nonneg i)
      _ = 1 := by rw [h_sum]; norm_num
  constructor
  · exact lt_of_le_of_ne h_nonneg_total h_ne_zero.symm
  · exact h_le_one

/-- Under uniform frequencies across `n` haplotypes, the general homozygosity formula reduces to
    `1 / n`. -/
theorem uniform_homozygosity_eq_inverse_haplotype_count
    (n : ℕ) (h_n : 1 ≤ n) :
    haplotypeHomozygosity (fun _ : Fin n ↦ 1 / (n : ℝ)) = 1 / (n : ℝ) := by
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.succ_le_iff.mp h_n)
  unfold haplotypeHomozygosity
  calc
    ∑ _ : Fin n, (1 / (n : ℝ)) ^ 2 = (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by simp
    _ = 1 / (n : ℝ) := by
      field_simp [h_n_pos.ne']

/-- In the uniform-frequency special case, more haplotypes imply lower homozygosity. -/
theorem uniform_homozygosity_decreases_with_diversity (n₁ n₂ : ℕ)
    (h₁ : 1 ≤ n₁) (h_lt : n₁ < n₂) :
    haplotypeHomozygosity (fun _ : Fin n₂ ↦ 1 / (n₂ : ℝ)) <
      haplotypeHomozygosity (fun _ : Fin n₁ ↦ 1 / (n₁ : ℝ)) := by
  have h₂ : 1 ≤ n₂ := le_trans h₁ (Nat.le_of_lt h_lt)
  rw [uniform_homozygosity_eq_inverse_haplotype_count n₂ h₂]
  rw [uniform_homozygosity_eq_inverse_haplotype_count n₁ h₁]
  exact div_lt_div_of_pos_left one_pos
    (Nat.cast_pos.mpr (Nat.succ_le_iff.mp h₁))
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
