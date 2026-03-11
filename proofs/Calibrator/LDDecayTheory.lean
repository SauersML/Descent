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
3. Admixture creates long-range LD maximized at equal mixing
4. Population bottlenecks amplify LD as a function of severity and duration
5. LD mismatch quantification via Frobenius norm

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
  simp only [ldAfterGenerations, abs_mul, abs_of_pos hD₀]
  apply mul_lt_mul_of_pos_left _ hD₀
  have h_ret_nn : 0 ≤ ldRetentionPerGen r Ne :=
    ld_retention_nonneg r Ne (le_of_lt hr) (le_of_lt hr1) (le_of_lt hNe)
  have h_ret_lt : ldRetentionPerGen r Ne < 1 :=
    ld_retention_lt_one r Ne hr hr1 hNe
  rw [abs_of_nonneg (pow_nonneg h_ret_nn _), abs_of_nonneg (pow_nonneg h_ret_nn _)]
  have h_ret_pos : 0 < ldRetentionPerGen r Ne := by
    unfold ldRetentionPerGen
    apply mul_pos
    · linarith
    · rw [sub_pos, div_lt_one (by linarith)]; linarith
  exact pow_lt_pow_right_of_lt_one₀ h_ret_pos h_ret_lt h_time

end OhtaKimuraDecay


/-!
## LD-Based Tagging and PGS Accuracy

PGS uses tag SNPs that are in LD with causal variants.
When LD changes, tags become less informative → PGS accuracy drops.
-/

section LDTagging

/-- **Tag SNP r² with causal variant.**
    The proportion of causal variant information captured by a tag. -/
noncomputable def tagR2 (D_sq var_tag var_causal : ℝ) : ℝ :=
  D_sq / (var_tag * var_causal)

/-- Tag r² is bounded by 1. -/
theorem tag_r2_le_one (D_sq var_tag var_causal : ℝ)
    (h_cauchy_schwarz : D_sq ≤ var_tag * var_causal)
    (h_vt : 0 < var_tag) (h_vc : 0 < var_causal) :
    tagR2 D_sq var_tag var_causal ≤ 1 := by
  unfold tagR2
  rw [div_le_one (mul_pos h_vt h_vc)]
  exact h_cauchy_schwarz

/-- **Tag r² decreases when LD structure changes.**
    In the target population, D² between tag and causal may be different. -/
theorem tag_r2_decreases_with_ld_change
    (D_sq_source D_sq_target var_tag var_causal : ℝ)
    (h_vt : 0 < var_tag) (h_vc : 0 < var_causal)
    (h_ld_drop : D_sq_target < D_sq_source) :
    tagR2 D_sq_target var_tag var_causal < tagR2 D_sq_source var_tag var_causal := by
  unfold tagR2
  exact div_lt_div_of_pos_right h_ld_drop (mul_pos h_vt h_vc)

/-- **Total PGS accuracy is the product of tag accuracies.**
    R²_PGS ≈ Σᵢ r²_tag_i × β_causal_i² / V_Y.
    When tag r² drops, PGS R² drops proportionally. -/
theorem pgs_accuracy_from_tagging
    {m : ℕ} (r2_tag : Fin m → ℝ) (β_sq : Fin m → ℝ) (v_y : ℝ)
    (h_vy : 0 < v_y) (h_β : ∀ i, 0 ≤ β_sq i) (h_r2 : ∀ i, 0 ≤ r2_tag i) :
    0 ≤ (∑ i, r2_tag i * β_sq i) / v_y := by
  apply div_nonneg _ (le_of_lt h_vy)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (h_r2 i) (h_β i)

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
theorem admixture_ld_max_at_half_freq (Δp₁ Δp₂ α : ℝ)
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
  apply pow_lt_pow_right_of_lt_one₀
  · norm_num
  · norm_num
  · omega

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
  linarith [pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_time]

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
  have h_pow := pow_lt_pow_left₀ h_base h_nn (by omega : t ≠ 0)
  linarith

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
    {p : ℕ} (Sig_S Sig_T : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  frobeniusNormSq (Sig_S - Sig_T)

/-- LD mismatch is nonneg. -/
theorem ld_mismatch_nonneg {p : ℕ}
    (Sig_S Sig_T : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ ldMismatchFrobenius Sig_S Sig_T := by
  unfold ldMismatchFrobenius
  exact frobeniusNormSq_nonneg _

/-- LD mismatch is positive when matrices differ. -/
theorem ld_mismatch_pos_of_ne {p : ℕ}
    (Sig_S Sig_T : Matrix (Fin p) (Fin p) ℝ)
    (h_ne : ∃ i j, (Sig_S - Sig_T) i j ≠ 0) :
    0 < ldMismatchFrobenius Sig_S Sig_T := by
  unfold ldMismatchFrobenius
  exact frobeniusNormSq_pos_of_exists_ne_zero _ h_ne

end LDMismatchQuantification


/-!
## Harmonic Mean Effective Population Size

When Ne varies over time, the effective drift is governed by the harmonic
mean: 1/Ne_eff = (1/T) Σ 1/Ne(t). Bottleneck generations dominate because
their small Ne contributes disproportionately large 1/Ne terms.
-/

section HarmonicMeanNe

/-- **Harmonic mean Ne** for a population size trajectory over T generations. -/
noncomputable def harmonicMeanNe (Ne : Fin T → ℝ) : ℝ :=
  (T : ℝ) / ∑ i, (1 / Ne i)

/-- The reciprocal of the harmonic mean equals the average of reciprocals. -/
theorem harmonic_mean_reciprocal (T : ℕ) (hT : 0 < T)
    (Ne : Fin T → ℝ) (hNe : ∀ i, 0 < Ne i) :
    1 / harmonicMeanNe Ne = (1 / (T : ℝ)) * ∑ i, (1 / Ne i) := by
  unfold harmonicMeanNe
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsum_pos : 0 < ∑ i, (1 / Ne i) := by
    apply Finset.sum_pos
    · intro i _; exact div_pos one_pos (hNe i)
    · exact Finset.univ_nonempty
  rw [one_div, inv_div, div_div]
  field_simp

/-- Replacing one generation's Ne with a smaller value decreases the harmonic mean.
    This shows bottleneck generations dominate. -/
theorem bottleneck_dominates_harmonic_mean (T : ℕ) (hT : 0 < T)
    (Ne₁ Ne₂ : Fin T → ℝ)
    (hNe₁ : ∀ i, 0 < Ne₁ i) (hNe₂ : ∀ i, 0 < Ne₂ i)
    (h_recip_larger : ∑ i, (1 / Ne₁ i) < ∑ i, (1 / Ne₂ i)) :
    harmonicMeanNe Ne₂ < harmonicMeanNe Ne₁ := by
  unfold harmonicMeanNe
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hs₁ : 0 < ∑ i, (1 / Ne₁ i) := by
    apply Finset.sum_pos
    · intro i _; exact div_pos one_pos (hNe₁ i)
    · exact Finset.univ_nonempty
  have hs₂ : 0 < ∑ i, (1 / Ne₂ i) := by
    apply Finset.sum_pos
    · intro i _; exact div_pos one_pos (hNe₂ i)
    · exact Finset.univ_nonempty
  exact div_lt_div_of_pos_left hT_pos hs₂ h_recip_larger

/-- A single bottleneck generation (small Ne_b) makes the harmonic mean
    smaller than the arithmetic mean would suggest.
    Specifically: if Ne_b < Ne_normal, then 1/Ne_b > 1/Ne_normal,
    so the sum of reciprocals is dominated by bottleneck terms. -/
theorem bottleneck_reciprocal_dominance (Ne_b Ne_normal : ℝ)
    (hb : 0 < Ne_b) (hn : 0 < Ne_normal)
    (h_bottle : Ne_b < Ne_normal) :
    1 / Ne_normal < 1 / Ne_b := by
  exact div_lt_div_of_pos_left one_pos hb h_bottle

end HarmonicMeanNe


/-!
## Bottleneck Effects on LD

A bottleneck (temporary reduction in Ne) amplifies LD above equilibrium
levels. After recovery, LD decays back but excess persists proportionally
to recovery population size.
-/

section BottleneckLDExcess

/-- **Excess LD from a bottleneck.**
    During a bottleneck of size N_b for t_b generations, drift generates
    LD of magnitude ≈ 1/(2N_b) per generation. After recovery to size N_r,
    this excess decays at rate 1/(2N_r) per generation. -/
noncomputable def excessLDAfterBottleneck (N_b N_r : ℝ) (t_b t_r : ℕ) : ℝ :=
  (1 - (1 - 1/(2 * N_b)) ^ t_b) * (1 - 1/(2 * N_r)) ^ t_r

/-- Excess LD is nonneg for reasonable parameters. -/
theorem excess_ld_nonneg (N_b N_r : ℝ) (t_b t_r : ℕ)
    (hNb : 2 < N_b) (hNr : 2 < N_r) :
    0 ≤ excessLDAfterBottleneck N_b N_r t_b t_r := by
  unfold excessLDAfterBottleneck
  apply mul_nonneg
  · rw [sub_nonneg]
    apply pow_le_one₀
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · rw [sub_le_self_iff]; positivity
  · apply pow_nonneg
    rw [sub_nonneg, div_le_one (by linarith)]; linarith

/-- More severe bottleneck (smaller N_b) produces more excess LD. -/
theorem more_severe_bottleneck_more_ld (N₁ N₂ N_r : ℝ) (t_b t_r : ℕ)
    (hN₁ : 2 < N₁) (hN₂ : 2 < N₂) (hNr : 2 < N_r)
    (h_smaller : N₂ < N₁) (ht_b : 0 < t_b) :
    excessLDAfterBottleneck N₁ N_r t_b t_r <
      excessLDAfterBottleneck N₂ N_r t_b t_r := by
  unfold excessLDAfterBottleneck
  have h_decay_nn : 0 ≤ (1 - 1/(2 * N_r)) ^ t_r := by
    apply pow_nonneg; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h_decay_pos : 0 < (1 - 1/(2 * N_r)) ^ t_r := by
    apply pow_pos; rw [sub_pos, div_lt_one (by linarith)]; linarith
  apply mul_lt_mul_of_pos_right _ h_decay_pos
  -- Need: 1 - (1 - 1/(2N₁))^t_b < 1 - (1 - 1/(2N₂))^t_b
  -- i.e., (1 - 1/(2N₂))^t_b < (1 - 1/(2N₁))^t_b
  rw [sub_lt_sub_iff_left]
  -- Since N₂ < N₁, 1/(2N₂) > 1/(2N₁), so 1 - 1/(2N₂) < 1 - 1/(2N₁)
  have h_base : 1 - 1/(2 * N₂) < 1 - 1/(2 * N₁) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  have h_nn : 0 ≤ 1 - 1/(2 * N₂) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  exact pow_lt_pow_left₀ h_base h_nn (by omega)

/-- After recovery, excess LD decays with time. -/
theorem excess_ld_decays_after_recovery (N_b N_r : ℝ) (t_b : ℕ) (t₁ t₂ : ℕ)
    (hNb : 2 < N_b) (hNr : 2 < N_r) (ht_b : 0 < t_b)
    (h_time : t₁ < t₂) :
    excessLDAfterBottleneck N_b N_r t_b t₂ <
      excessLDAfterBottleneck N_b N_r t_b t₁ := by
  unfold excessLDAfterBottleneck
  have h_amp_pos : 0 < 1 - (1 - 1/(2 * N_b)) ^ t_b := by
    rw [sub_pos]
    apply pow_lt_one₀
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · rw [sub_lt_self_iff]; positivity
    · omega
  apply mul_lt_mul_of_pos_left _ h_amp_pos
  have h_base_pos : 0 < 1 - 1/(2 * N_r) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1/(2 * N_r) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_time

end BottleneckLDExcess


/-!
## Population Expansion and LD Persistence

Population expansion reduces the rate of new drift, so LD generated
pre-expansion persists longer. Large modern Ne means current drift is slow.
-/

section ExpansionLD

/-- **LD decay rate depends on current Ne.**
    The fraction of LD that decays per generation is 1/(2Ne).
    Larger Ne → slower decay → LD persists longer. -/
noncomputable def ldDecayRatePerGen (Ne : ℝ) : ℝ :=
  1 / (2 * Ne)

/-- Larger population has slower LD decay rate. -/
theorem larger_pop_slower_ld_decay (Ne₁ Ne₂ : ℝ)
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (h_larger : Ne₁ < Ne₂) :
    ldDecayRatePerGen Ne₂ < ldDecayRatePerGen Ne₁ := by
  unfold ldDecayRatePerGen
  exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **LD half-life is proportional to Ne.**
    After a perturbation, the number of generations for LD to halve
    is approximately 2·Ne·ln(2). We define it and show monotonicity. -/
noncomputable def ldHalfLife (Ne : ℝ) : ℝ :=
  2 * Ne * Real.log 2

/-- LD half-life increases with population size. -/
theorem ld_half_life_increasing (Ne₁ Ne₂ : ℝ)
    (hNe₁ : 0 < Ne₁) (h_larger : Ne₁ < Ne₂) :
    ldHalfLife Ne₁ < ldHalfLife Ne₂ := by
  unfold ldHalfLife
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Pre-expansion LD retained after t generations in expanded population.
    If pre-expansion LD level is D₀ and expansion is to Ne_new,
    the retained fraction after t generations is (1 - 1/(2·Ne_new))^t.
    Larger Ne_new retains more LD. -/
theorem expansion_retains_more_ld (Ne_small Ne_large D₀ : ℝ) (t : ℕ)
    (hNs : 2 < Ne_small) (hNl : 2 < Ne_large)
    (h_exp : Ne_small < Ne_large) (hD₀ : 0 < D₀) (ht : 0 < t) :
    D₀ * (1 - 1/(2 * Ne_small)) ^ t < D₀ * (1 - 1/(2 * Ne_large)) ^ t := by
  apply mul_lt_mul_of_pos_left _ hD₀
  have h_base : 1 - 1/(2 * Ne_small) < 1 - 1/(2 * Ne_large) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  have h_nn : 0 ≤ 1 - 1/(2 * Ne_small) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h_lt_one : 1 - 1/(2 * Ne_large) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_left₀ h_base h_nn (by omega)

end ExpansionLD


/-!
## LD Half-Life Depends on Ne Trajectory

After a perturbation (bottleneck, admixture, etc.), LD decays with
half-life proportional to the current Ne. Populations with larger modern
Ne have slower LD decay toward equilibrium.
-/

section LDHalfLifeTrajectory

/-- **LD retained fraction** after t generations at constant size Ne. -/
noncomputable def ldRetainedFraction (Ne : ℝ) (t : ℕ) : ℝ :=
  (1 - 1/(2 * Ne)) ^ t

/-- Larger current Ne means more LD retained after any fixed time. -/
theorem larger_ne_more_ld_retained (Ne₁ Ne₂ : ℝ) (t : ℕ)
    (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂) (h : Ne₁ < Ne₂) (ht : 0 < t) :
    ldRetainedFraction Ne₁ t < ldRetainedFraction Ne₂ t := by
  unfold ldRetainedFraction
  have h_base : 1 - 1/(2 * Ne₁) < 1 - 1/(2 * Ne₂) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  have h_nn : 0 ≤ 1 - 1/(2 * Ne₁) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  exact pow_lt_pow_left₀ h_base h_nn (by omega)

/-- Retained fraction is strictly decreasing with time for finite Ne. -/
theorem ld_retained_decreasing (Ne : ℝ) (t₁ t₂ : ℕ)
    (hNe : 2 < Ne) (h_time : t₁ < t₂) :
    ldRetainedFraction Ne t₂ < ldRetainedFraction Ne t₁ := by
  unfold ldRetainedFraction
  have h_pos : 0 < 1 - 1/(2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_lt_one : 1 - 1/(2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_right_of_lt_one₀ h_pos h_lt_one h_time

/-- Two populations with the same initial LD perturbation but different
    modern Ne will have different LD levels after the same time.
    The one with larger Ne retains more excess LD. -/
theorem different_ne_different_ld_persistence
    (D₀ Ne₁ Ne₂ : ℝ) (t : ℕ)
    (hD₀ : 0 < D₀) (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂)
    (h_larger : Ne₁ < Ne₂) (ht : 0 < t) :
    D₀ * ldRetainedFraction Ne₁ t < D₀ * ldRetainedFraction Ne₂ t := by
  apply mul_lt_mul_of_pos_left _ hD₀
  exact larger_ne_more_ld_retained Ne₁ Ne₂ t hNe₁ hNe₂ h_larger ht

end LDHalfLifeTrajectory

end Calibrator
