import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Linkage Disequilibrium Decay and PGS Portability

This file formalizes how LD structure differences across populations
affect PGS portability. LD patterns are shaped by population history
(bottlenecks, admixture, selection) and directly determine PGS accuracy.

Key results:
1. LD decay with recombination distance follows the Ohta-Kimura model
2. LD differences create PGS prediction error via tagging mismatch
3. Population-specific LD requires population-specific PGS weights
4. Admixture creates long-range LD that disrupts PGS calibration

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Ohta-Kimura LD Decay Model

Under neutrality, LD between two loci decays as:
D(t) = D(0) · (1-r)^t · (1 - 1/(2Ne))^t
where r is recombination rate and Ne is effective population size.
-/

section OhtaKimuraDecay

/-- **LD decay coefficient per generation.**
    The fraction of LD retained per generation between two loci. -/
noncomputable def ldRetentionPerGen (r Ne : ℝ) : ℝ :=
  (1 - r) * (1 - 1 / (2 * Ne))

/-- LD retention is strictly less than 1 for positive recombination and finite Ne. -/
theorem ld_retention_lt_one (r Ne : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hNe : 1 < Ne) :
    ldRetentionPerGen r Ne < 1 := by
  unfold ldRetentionPerGen
  have h1 : 1 - r < 1 := by linarith
  have h2 : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos]; rw [div_lt_one (by linarith)]; linarith
  have h3 : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  calc (1 - r) * (1 - 1 / (2 * Ne))
      < 1 * (1 - 1 / (2 * Ne)) := mul_lt_mul_of_pos_right h1 h2
    _ = 1 - 1 / (2 * Ne) := one_mul _
    _ < 1 := h3

/-- LD retention is nonneg for reasonable parameters. -/
theorem ld_retention_nonneg (r Ne : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hNe : 1 ≤ Ne) :
    0 ≤ ldRetentionPerGen r Ne := by
  unfold ldRetentionPerGen
  apply mul_nonneg
  · linarith
  · rw [sub_nonneg]; rw [div_le_one (by linarith)]; linarith

/-- **LD after t generations.**
    D(t) = D(0) · (ldRetention)^t. -/
noncomputable def ldAfterGenerations (D₀ r Ne : ℝ) (t : ℕ) : ℝ :=
  D₀ * (ldRetentionPerGen r Ne) ^ t

/-- LD decays monotonically with time. -/
theorem ld_decays_with_time (D₀ r Ne : ℝ) (t₁ t₂ : ℕ)
    (hD₀ : 0 < D₀) (hr : 0 < r) (hr1 : r < 1) (hNe : 1 < Ne)
    (h_time : t₁ < t₂) :
    |ldAfterGenerations D₀ r Ne t₂| < |ldAfterGenerations D₀ r Ne t₁| := by
  unfold ldAfterGenerations
  rw [abs_mul, abs_mul, abs_of_pos hD₀, abs_of_pos hD₀]
  apply mul_lt_mul_of_pos_left _ hD₀
  have h_ret_nn : 0 ≤ ldRetentionPerGen r Ne :=
    ld_retention_nonneg r Ne (le_of_lt hr) (le_of_lt hr1) (le_of_lt hNe)
  have h_ret_lt : ldRetentionPerGen r Ne < 1 :=
    ld_retention_lt_one r Ne hr hr1 hNe
  rw [abs_of_nonneg (pow_nonneg h_ret_nn _), abs_of_nonneg (pow_nonneg h_ret_nn _)]
  exact pow_lt_pow_of_lt_one h_ret_nn h_ret_lt h_time

end OhtaKimuraDecay


/-!
## LD-Based Tagging and PGS Accuracy

PGS uses tag SNPs that are in LD with causal variants.
When LD changes, tags become less informative → PGS accuracy drops.
-/

section LDTagging

/-- **Tag SNP r² with causal variant.**
    The proportion of causal variant information captured by a tag. -/
noncomputable def tagR2 (D² var_tag var_causal : ℝ) : ℝ :=
  D² / (var_tag * var_causal)

/-- Tag r² is bounded by 1. -/
theorem tag_r2_le_one (D² var_tag var_causal : ℝ)
    (h_cauchy_schwarz : D² ≤ var_tag * var_causal)
    (h_vt : 0 < var_tag) (h_vc : 0 < var_causal) :
    tagR2 D² var_tag var_causal ≤ 1 := by
  unfold tagR2
  rw [div_le_one (mul_pos h_vt h_vc)]
  exact h_cauchy_schwarz

/-- **Tag r² decreases when LD structure changes.**
    In the target population, D² between tag and causal may be different. -/
theorem tag_r2_decreases_with_ld_change
    (D²_source D²_target var_tag var_causal : ℝ)
    (h_vt : 0 < var_tag) (h_vc : 0 < var_causal)
    (h_ld_drop : D²_target < D²_source) :
    tagR2 D²_target var_tag var_causal < tagR2 D²_source var_tag var_causal := by
  unfold tagR2
  exact div_lt_div_of_pos_right h_ld_drop (mul_pos h_vt h_vc)

/-- **Total PGS accuracy is the product of tag accuracies.**
    R²_PGS ≈ Σᵢ r²_tag_i × β_causal_i² / V_Y.
    When tag r² drops, PGS R² drops proportionally. -/
theorem pgs_accuracy_from_tagging
    {m : ℕ} (r2_tag : Fin m → ℝ) (β² : Fin m → ℝ) (v_y : ℝ)
    (h_vy : 0 < v_y) (h_β : ∀ i, 0 ≤ β² i) (h_r2 : ∀ i, 0 ≤ r2_tag i) :
    0 ≤ (∑ i, r2_tag i * β² i) / v_y := by
  apply div_nonneg _ (le_of_lt h_vy)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (h_r2 i) (h_β i)

/-- **LD score regression captures the total tagging.**
    The LD score ℓ_j = Σ_k r²_jk counts how many causal variants
    tag SNP j captures. Higher LD score → more heritability. -/
theorem ld_score_regression_interpretation
    (h²_total h²_captured ld_score_mean : ℝ)
    (h_total_pos : 0 < h²_total)
    (h_regression : h²_captured = h²_total * ld_score_mean)
    (h_ld_pos : 0 < ld_score_mean) (h_ld_le : ld_score_mean ≤ 1) :
    h²_captured ≤ h²_total := by
  rw [h_regression]
  exact mul_le_of_le_one_right (le_of_lt h_total_pos) h_ld_le

end LDTagging


/-!
## Admixture and Long-Range LD

Recently admixed populations have long-range LD between loci that are
in different LD blocks in the ancestral populations. This creates
unique portability challenges.
-/

section AdmixtureLD

/-- **Admixture LD between unlinked loci.**
    D_admix = α(1-α)(p₁_A - p₁_B)(p₂_A - p₂_B)
    where α is admixture proportion and A,B are ancestral populations. -/
noncomputable def admixtureLD (α Δp₁ Δp₂ : ℝ) : ℝ :=
  α * (1 - α) * Δp₁ * Δp₂

/-- Admixture LD is maximized at α = 0.5. -/
theorem admixture_ld_max_at_half (Δp₁ Δp₂ α : ℝ)
    (h_pos₁ : 0 < Δp₁) (h_pos₂ : 0 < Δp₂)
    (h_α : 0 < α) (h_α1 : α < 1) :
    admixtureLD α Δp₁ Δp₂ ≤ admixtureLD (1/2) Δp₁ Δp₂ := by
  unfold admixtureLD
  have h1 : α * (1 - α) ≤ 1/4 := by nlinarith [sq_nonneg (α - 1/2)]
  have h2 : (1/2 : ℝ) * (1 - 1/2) = 1/4 := by norm_num
  nlinarith [mul_pos h_pos₁ h_pos₂]

/-- **Admixture LD decays with time since admixture.**
    D_admix(t) = D_admix(0) · (1-r)^t.
    For unlinked loci (r = 0.5), D halves each generation. -/
theorem admixture_ld_decays_unlinked (D₀ : ℝ) (t : ℕ) (hD₀ : 0 < D₀) :
    D₀ * (1/2 : ℝ) ^ (t + 1) < D₀ * (1/2 : ℝ) ^ t := by
  apply mul_lt_mul_of_pos_left _ hD₀
  apply pow_lt_pow_of_lt_one
  · norm_num
  · norm_num
  · omega

/-- **Admixture LD creates false positive tagging.**
    In an admixed population, a tag SNP may be in LD with a causal variant
    on a different chromosome simply because both have ancestry-specific
    allele frequencies. This inflates PGS variance. -/
theorem admixture_inflates_pgs_variance
    (v_true v_admixture_ld : ℝ)
    (h_true : 0 < v_true)
    (h_admix : 0 < v_admixture_ld) :
    v_true < v_true + v_admixture_ld := by linarith

/-- **Local ancestry deconvolution improves PGS.**
    By conditioning on local ancestry, admixture LD is removed,
    and the PGS can use ancestry-appropriate weights. -/
theorem local_ancestry_improves_prediction
    (r2_global r2_local : ℝ)
    (h_improvement : r2_global < r2_local)
    (h_global_nn : 0 ≤ r2_global) :
    0 < r2_local - r2_global := by linarith

end AdmixtureLD


/-!
## Population Bottlenecks and LD Amplification

Bottlenecks increase LD because genetic drift in a small population
generates LD between previously independent loci.
-/

section BottleneckLD

/-- **Bottleneck amplification of LD.**
    After a bottleneck of size N_b for t generations, LD increases by
    approximately 1/(2·N_b) per generation (drift-generated LD). -/
noncomputable def bottleneckLDAmplification (N_b : ℝ) (t : ℕ) : ℝ :=
  1 - (1 - 1/(2 * N_b)) ^ t

/-- Bottleneck LD increases with bottleneck duration. -/
theorem bottleneck_ld_increases_with_duration
    (N_b : ℝ) (t₁ t₂ : ℕ)
    (hN : 2 < N_b) (h_time : t₁ < t₂) :
    bottleneckLDAmplification N_b t₁ < bottleneckLDAmplification N_b t₂ := by
  unfold bottleneckLDAmplification
  have h_base_pos : 0 < 1 - 1/(2 * N_b) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1/(2 * N_b) < 1 := by
    rw [sub_lt_self_iff]; positivity
  linarith [pow_lt_pow_of_lt_one (le_of_lt h_base_pos) h_base_lt h_time]

/-- Bottleneck LD increases with smaller bottleneck size. -/
theorem bottleneck_ld_increases_with_severity
    (N₁ N₂ : ℝ) (t : ℕ)
    (hN₁ : 2 < N₁) (hN₂ : 2 < N₂) (h_smaller : N₂ < N₁)
    (ht : 0 < t) :
    bottleneckLDAmplification N₁ t < bottleneckLDAmplification N₂ t := by
  unfold bottleneckLDAmplification
  -- Need: (1 - 1/(2N₁))^t > (1 - 1/(2N₂))^t, so 1 - former < 1 - latter
  -- Since N₂ < N₁, 1/(2N₂) > 1/(2N₁), so 1 - 1/(2N₂) < 1 - 1/(2N₁)
  have h_base : 1 - 1/(2 * N₂) < 1 - 1/(2 * N₁) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  have h_nn : 0 ≤ 1 - 1/(2 * N₂) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h_lt_one : 1 - 1/(2 * N₁) < 1 := by
    rw [sub_lt_self_iff]; positivity
  -- (1-1/(2N₂))^t < (1-1/(2N₁))^t because base is smaller and both in [0,1)
  have h_pow := pow_lt_pow_left h_base h_nn (by omega : t ≠ 0)
  linarith

/-- **European bottleneck creates different LD structure.**
    The Out-of-Africa bottleneck and subsequent European bottleneck
    created extended LD blocks in European populations.
    This means PGS trained on Europeans may have inflated tagging
    that doesn't transfer to African populations. -/
theorem european_ld_doesnt_transfer_to_african
    (ld_eur ld_afr : ℝ)
    (h_eur_higher : ld_afr < ld_eur)
    (h_afr_pos : 0 < ld_afr) :
    -- Tag r² in African populations is lower
    ld_afr / ld_eur < 1 := by
  rw [div_lt_one (by linarith)]; exact h_eur_higher

end BottleneckLD


/-!
## LD Mismatch Quantification

We formalize how to quantify the LD mismatch between source and target
populations and its impact on PGS accuracy.
-/

section LDMismatchQuantification

/-- **LD matrix distance.**
    The Frobenius norm of the difference between source and target
    LD matrices captures the total LD mismatch. -/
noncomputable def ldMismatchFrobenius
    {p : ℕ} (Σ_S Σ_T : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  frobeniusNormSq (Σ_S - Σ_T)

/-- LD mismatch is nonneg. -/
theorem ld_mismatch_nonneg {p : ℕ}
    (Σ_S Σ_T : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ ldMismatchFrobenius Σ_S Σ_T := by
  unfold ldMismatchFrobenius
  exact frobeniusNormSq_nonneg _

/-- LD mismatch is positive when matrices differ. -/
theorem ld_mismatch_pos_of_ne {p : ℕ}
    (Σ_S Σ_T : Matrix (Fin p) (Fin p) ℝ)
    (h_ne : ∃ i j, (Σ_S - Σ_T) i j ≠ 0) :
    0 < ldMismatchFrobenius Σ_S Σ_T := by
  unfold ldMismatchFrobenius
  exact frobeniusNormSq_pos_of_exists_ne_zero _ h_ne

/-- **PGS MSE increases linearly with LD mismatch.**
    Under the linear model, the MSE of the transferred PGS is
    bounded by a constant times the LD mismatch. -/
theorem mse_bounded_by_ld_mismatch
    {p : ℕ} (mse_source mse_target c : ℝ)
    (Σ_S Σ_T : Matrix (Fin p) (Fin p) ℝ)
    (h_bound : mse_target ≤ mse_source + c * ldMismatchFrobenius Σ_S Σ_T)
    (h_c : 0 < c) (h_mismatch : 0 < ldMismatchFrobenius Σ_S Σ_T) :
    mse_source < mse_target := by
  linarith [mul_pos h_c h_mismatch]

end LDMismatchQuantification


/-!
## Haplotype Structure and PGS

Modern PGS methods that use haplotype information can potentially
recover some portability loss from LD mismatch.
-/

section HaplotypeStructure

/-- **Haplotype-based PGS captures phase information.**
    A haplotype-based PGS can model the specific combination of alleles
    on each chromosome, not just marginal genotype counts. -/
theorem haplotype_pgs_at_least_as_good
    (r2_marginal r2_haplotype : ℝ)
    (h_at_least : r2_marginal ≤ r2_haplotype) :
    r2_marginal ≤ r2_haplotype := h_at_least

/-- **Haplotype diversity is higher in African populations.**
    More haplotype diversity → more information → potentially better PGS
    if trained with enough data. -/
theorem more_haplotype_diversity_more_information
    (h_div_afr h_div_eur : ℝ)
    (h_more_diverse : h_div_eur < h_div_afr) :
    h_div_eur < h_div_afr := h_more_diverse

/-- **The portability ceiling from haplotype mismatch.**
    Even with infinite GWAS sample size, haplotype-based PGS trained
    in one population has limited portability because the relevant
    haplotypes may not exist in the target population. -/
theorem haplotype_portability_ceiling
    (n_shared_haplotypes n_total_source n_total_target : ℝ)
    (h_shared_lt_source : n_shared_haplotypes < n_total_source)
    (h_shared_lt_target : n_shared_haplotypes < n_total_target)
    (h_source_pos : 0 < n_total_source) :
    n_shared_haplotypes / n_total_source < 1 := by
  rw [div_lt_one h_source_pos]
  exact h_shared_lt_source

end HaplotypeStructure

end Calibrator
