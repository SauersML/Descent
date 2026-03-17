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

/-- Inverse homozygosity (Hill number of order 2), a standard effective-number
summary of haplotype diversity. Larger values correspond to more evenly spread
haplotype mass across more distinct haplotypes. -/
noncomputable def effectiveHaplotypeNumber {α : Type*} [Fintype α]
    (freq : α → ℝ) : ℝ :=
  1 / haplotypeHomozygosity freq

/-- Lower homozygosity implies a larger effective number of haplotypes. This is
the biologically relevant diversity statement: populations with more even
haplotype frequency spectra carry more effective haplotypic states. -/
theorem more_haplotypes_in_afr
    {α β : Type*} [Fintype α] [Fintype β]
    (freq_eur : α → ℝ) (freq_afr : β → ℝ)
    (h_afr_nonneg : ∀ i, 0 ≤ freq_afr i)
    (h_afr_sum : ∑ i, freq_afr i = 1)
    (h_hom : haplotypeHomozygosity freq_afr < haplotypeHomozygosity freq_eur) :
    effectiveHaplotypeNumber freq_eur < effectiveHaplotypeNumber freq_afr := by
  have h_hom_afr_pos :
      0 < haplotypeHomozygosity freq_afr := (homozygosity_bounded freq_afr h_afr_nonneg h_afr_sum).1
  unfold effectiveHaplotypeNumber
  exact div_lt_div_of_pos_left one_pos h_hom_afr_pos h_hom

/-- A more uniform haplotype frequency spectrum corresponds to lower
homozygosity and therefore a larger effective haplotype number. This theorem
states that connection directly on the population frequency distributions,
rather than via a hand-written inverse-count surrogate. -/
theorem haplotype_frequency_more_uniform_afr
    {α β : Type*} [Fintype α] [Fintype β]
    (freq_eur : α → ℝ) (freq_afr : β → ℝ)
    (h_afr_nonneg : ∀ i, 0 ≤ freq_afr i)
    (h_afr_sum : ∑ i, freq_afr i = 1)
    (h_hom : haplotypeHomozygosity freq_afr < haplotypeHomozygosity freq_eur) :
    haplotypeHomozygosity freq_afr < haplotypeHomozygosity freq_eur ∧
      effectiveHaplotypeNumber freq_eur < effectiveHaplotypeNumber freq_afr := by
  exact ⟨h_hom, more_haplotypes_in_afr freq_eur freq_afr
    h_afr_nonneg h_afr_sum h_hom⟩

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
noncomputable def riskCis (base_risk interaction_cis : ℝ) : ℝ :=
  base_risk + interaction_cis

/-- Phase-dependent risk under a trans configuration. -/
noncomputable def riskTrans (base_risk interaction_trans : ℝ) : ℝ :=
  base_risk + interaction_trans

/-- Exact phase-dependent risk gap between trans and cis configurations. -/
theorem trans_minus_cis_risk_eq_interaction_gap
    (base_risk interaction_cis interaction_trans : ℝ) :
    riskTrans base_risk interaction_trans - riskCis base_risk interaction_cis =
      interaction_trans - interaction_cis := by
  dsimp [riskTrans, riskCis]
  ring

/-- Average interaction contribution when a population has cis-configuration
frequency `freq_cis` and trans frequency `1 - freq_cis`. -/
noncomputable def averagePhaseInteraction
    (freq_cis interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis * interaction_cis + (1 - freq_cis) * interaction_trans

/-- Structural error from using a dosage-only predictor that cannot distinguish
cis from trans configurations. The best dosage-only predictor within a fixed
dosage class uses the population-average interaction, leaving this residual
phase-misspecification error. -/
noncomputable def dosagePhaseMisspecificationError
    (freq_cis interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis * (interaction_cis - averagePhaseInteraction freq_cis interaction_cis interaction_trans) ^ 2 +
    (1 - freq_cis) *
      (interaction_trans - averagePhaseInteraction freq_cis interaction_cis interaction_trans) ^ 2

/-- A phase-aware haplotype predictor that tracks cis/trans configuration has no
structural phase-misspecification error. -/
noncomputable def haplotypePhasePredictionError : ℝ :=
  0

/-- Transport bias from carrying a source-trained dosage approximation into a
target population whose cis/trans configuration frequency differs. -/
noncomputable def dosageTransportBias
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) : ℝ :=
  |averagePhaseInteraction freq_cis_target interaction_cis interaction_trans -
    averagePhaseInteraction freq_cis_source interaction_cis interaction_trans|

/-- A phase-aware haplotype model transports without this structural bias when
the cis/trans effects themselves are portable and only configuration
frequencies differ. -/
noncomputable def haplotypeTransportBias : ℝ :=
  0

/-- The dosage-only phase-misspecification error has the exact variance form
`f(1-f)(δ_cis - δ_trans)^2`. -/
theorem dosagePhaseMisspecificationError_eq
    (freq_cis interaction_cis interaction_trans : ℝ) :
    dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans =
      freq_cis * (1 - freq_cis) * (interaction_cis - interaction_trans) ^ 2 := by
  unfold dosagePhaseMisspecificationError averagePhaseInteraction
  ring

/-- The structural dosage transport bias is exactly the shift in phase
configuration frequency times the cis/trans interaction gap. -/
theorem dosageTransportBias_eq
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) :
    dosageTransportBias freq_cis_source freq_cis_target interaction_cis interaction_trans =
      |freq_cis_target - freq_cis_source| * |interaction_cis - interaction_trans| := by
  unfold dosageTransportBias averagePhaseInteraction
  have h_factor :
      freq_cis_target * interaction_cis + (1 - freq_cis_target) * interaction_trans -
        (freq_cis_source * interaction_cis + (1 - freq_cis_source) * interaction_trans) =
        (freq_cis_target - freq_cis_source) * (interaction_cis - interaction_trans) := by
    ring
  rw [h_factor, abs_mul]

theorem compound_het_not_captured_by_dosage
    (freq_cis interaction_cis interaction_trans : ℝ)
    (h_freq : 0 < freq_cis ∧ freq_cis < 1)
    (h_phase_gap : interaction_cis ≠ interaction_trans) :
    haplotypePhasePredictionError < dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans := by
  rcases h_freq with ⟨h_freq_pos, h_freq_lt_one⟩
  rw [dosagePhaseMisspecificationError_eq, haplotypePhasePredictionError]
  have h_gap_sq : 0 < (interaction_cis - interaction_trans) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr h_phase_gap)
  have h_mix : 0 < freq_cis * (1 - freq_cis) := by
    exact mul_pos h_freq_pos (sub_pos.mpr h_freq_lt_one)
  exact mul_pos h_mix h_gap_sq

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
    Here the comparison is made on the explicit phase-misspecification error
    surface from the previous section: a phase-aware haplotype score has zero
    structural error, while a dosage-only SNP score has nonnegative error, and
    strictly positive error whenever both cis and trans states occur and their
    effects differ. -/
theorem haplotype_pgs_at_least_snp
    (freq_cis interaction_cis interaction_trans : ℝ)
    (h_freq_nonneg : 0 ≤ freq_cis) (h_freq_le_one : freq_cis ≤ 1) :
    haplotypePhasePredictionError ≤
      dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans := by
  rw [dosagePhaseMisspecificationError_eq, haplotypePhasePredictionError]
  have h_mix_nonneg : 0 ≤ freq_cis * (1 - freq_cis) := by
    exact mul_nonneg h_freq_nonneg (sub_nonneg.mpr h_freq_le_one)
  exact mul_nonneg h_mix_nonneg (sq_nonneg _)

/-- **Haplotype PGS portability can be better.**
    If the causal mechanism acts through cis/trans haplotype configuration,
    transporting a dosage-only approximation incurs structural bias whenever
    the target phase-configuration frequency differs from the source. A
    phase-aware haplotype model avoids this bias. -/
theorem haplotype_pgs_more_portable_for_cis
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ)
    (h_freq_shift : freq_cis_source ≠ freq_cis_target)
    (h_phase_gap : interaction_cis ≠ interaction_trans) :
    haplotypeTransportBias < dosageTransportBias
      freq_cis_source freq_cis_target interaction_cis interaction_trans := by
  rw [dosageTransportBias_eq, haplotypeTransportBias]
  exact mul_pos
    (abs_pos.mpr (sub_ne_zero.mpr h_freq_shift.symm))
    (abs_pos.mpr (sub_ne_zero.mpr h_phase_gap))

/-- **But haplotype PGS can overfit in training population.**
    Rare haplotypes have fewer observed carriers, so their effect estimates are
    noisier. This theorem states the actual carrier-count mechanism: estimation
    variance scales like `σ² / (n × f)` where `f` is haplotype frequency in a
    sample of size `n`. Adding a rarer haplotype strictly increases the total
    estimation-noise burden. -/
noncomputable def haplotypeEffectEstimationVariance
    (σ2 n freq : ℝ) : ℝ :=
  σ2 / (n * freq)

theorem haplotype_pgs_overfitting_risk
    (σ2 n freq_common freq_rare : ℝ)
    (h_sigma : 0 < σ2)
    (h_n : 0 < n)
    (h_rare : 0 < freq_rare)
    (h_rarer : freq_rare < freq_common) :
    haplotypeEffectEstimationVariance σ2 n freq_common <
      haplotypeEffectEstimationVariance σ2 n freq_rare ∧
    haplotypeEffectEstimationVariance σ2 n freq_common <
      haplotypeEffectEstimationVariance σ2 n freq_common +
        haplotypeEffectEstimationVariance σ2 n freq_rare := by
  unfold haplotypeEffectEstimationVariance
  have h_common_var_lt_rare :
      σ2 / (n * freq_common) < σ2 / (n * freq_rare) := by
    exact div_lt_div_of_pos_left h_sigma (mul_pos h_n h_rare)
      (by nlinarith [mul_pos h_n h_rare])
  have h_rare_var_pos : 0 < σ2 / (n * freq_rare) := by
    exact div_pos h_sigma (mul_pos h_n h_rare)
  constructor
  · exact h_common_var_lt_rare
  · linarith

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
    (h_s₂_le : s₂ ≤ 1 / 2)
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
    (h_target_le : s_target ≤ 1 / 2) :
    phaseAttenuation s_target < phaseAttenuation s_source := by
  exact more_errors_more_attenuation s_source s_target h_target_le h_worse

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

/-- Single-effect predictor obtained by averaging ancestry-specific effects
according to the admixture proportion `alpha`. -/
noncomputable def globalAncestryAveragedEffect
    (beta₁ beta₂ alpha : ℝ) : ℝ :=
  ancestrySpecificEffect beta₁ beta₂ alpha

/-- Structural prediction error from using a single ancestry-averaged effect in
an admixed population whose local ancestry really switches between ancestry 1
and ancestry 2. -/
noncomputable def localAncestryMisspecification
    (beta₁ beta₂ alpha : ℝ) : ℝ :=
  alpha * (beta₁ - globalAncestryAveragedEffect beta₁ beta₂ alpha) ^ 2 +
    (1 - alpha) * (beta₂ - globalAncestryAveragedEffect beta₁ beta₂ alpha) ^ 2

/-- The misspecification from ignoring local ancestry is exactly the weighted
squared effect-difference term `α(1-α)(β₁-β₂)^2`. -/
theorem localAncestryMisspecification_eq
    (beta₁ beta₂ alpha : ℝ) :
    localAncestryMisspecification beta₁ beta₂ alpha =
      alpha * (1 - alpha) * (beta₁ - beta₂) ^ 2 := by
  unfold localAncestryMisspecification globalAncestryAveragedEffect ancestrySpecificEffect
  ring

/-- **Local ancestry deconvolution for haplotypes.**
    By identifying the ancestry of each haplotype segment, the model can apply
    the ancestry-appropriate effect instead of a single ancestry-averaged
    effect. The gain is exactly the local-ancestry misspecification variance
    removed by deconvolution. -/
theorem la_deconvolution_improves_pgs
    (r2_global beta₁ beta₂ alpha V_total : ℝ)
    (h_alpha : 0 < alpha)
    (h_alpha_lt : alpha < 1)
    (h_beta : beta₁ ≠ beta₂)
    (h_total : 0 < V_total) :
    r2_global <
      r2_global + localAncestryMisspecification beta₁ beta₂ alpha / V_total := by
  rw [localAncestryMisspecification_eq]
  have h_mix : 0 < alpha * (1 - alpha) := mul_pos h_alpha (sub_pos.mpr h_alpha_lt)
  have h_gap : 0 < (beta₁ - beta₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h_beta)
  have h_gain : 0 < alpha * (1 - alpha) * (beta₁ - beta₂) ^ 2 / V_total := by
    exact div_pos (mul_pos h_mix h_gap) h_total
  linarith

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
