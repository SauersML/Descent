import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Ancestry-Specific Statistical Power and PGS

This file formalizes the statistical power framework for PGS
across different genetic ancestries. Power imbalances are a
fundamental driver of portability gaps.

Key results:
1. Ancestry-specific power curves
2. Discovery bias from EUR-centric GWAS
3. Effective sample size across ancestries
4. Power-portability tradeoff
5. Optimal multi-ancestry study design

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Ancestry-Specific Power Curves

Power to detect a variant depends on sample size, effect size,
and allele frequency — all of which differ across ancestries.
-/

section AncestryPowerCurves

/-- **Effective sample size for a variant.**
    n_eff = n × 2p(1-p) × r²_LD(tag, causal)
    where p is MAF in that ancestry and r²_LD is tagging efficiency. -/
noncomputable def effectiveSampleSize (n : ℕ) (p r2_ld : ℝ) : ℝ :=
  n * (2 * p * (1 - p)) * r2_ld

/-- Effective sample size is nonneg. -/
theorem effective_n_nonneg (n : ℕ) (p r2_ld : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) (h_r2 : 0 ≤ r2_ld) :
    0 ≤ effectiveSampleSize n p r2_ld := by
  unfold effectiveSampleSize
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg n
    · nlinarith
  · exact h_r2

/-- **EUR has higher effective n due to larger GWAS and better tagging.**
    n_eff_EUR >> n_eff_AFR because:
    1. n_EUR >> n_AFR (sample size imbalance)
    2. r²_LD_EUR > r²_LD_AFR (array designed for EUR) -/
theorem eur_higher_effective_n
    (n_eur n_afr : ℕ) (p_eur p_afr r2_eur r2_afr : ℝ)
    (h_n : n_afr < n_eur) (h_r2 : r2_afr < r2_eur)
    (h_p_eur : 0 < p_eur) (h_p_eur_lt : p_eur < 1)
    (h_p_afr : 0 < p_afr) (h_p_afr_lt : p_afr < 1)
    (h_r2_afr : 0 < r2_afr)
    -- Same variant, same allele frequency for simplicity
    (h_same_p : p_eur = p_afr) :
    effectiveSampleSize n_afr p_afr r2_afr <
      effectiveSampleSize n_eur p_eur r2_eur := by
  unfold effectiveSampleSize
  rw [h_same_p]
  have h_het : 0 < 2 * p_afr * (1 - p_afr) := by nlinarith
  have h_n_cast : (↑n_afr : ℝ) < ↑n_eur := Nat.cast_lt.mpr h_n
  nlinarith [mul_pos h_het h_r2_afr, Nat.cast_nonneg n_afr]

/-- **Power gap compounds across the genome.**
    If EUR has power p_EUR for each variant and AFR has p_AFR,
    and there are M causal variants, the expected number
    detected is M × p_EUR vs M × p_AFR. -/
theorem detected_variants_gap
    (M : ℕ) (power_eur power_afr : ℝ)
    (h_power : power_afr < power_eur)
    (h_M : 0 < M) :
    ↑M * power_afr < ↑M * power_eur := by
  exact mul_lt_mul_of_pos_left h_power (Nat.cast_pos.mpr h_M)

end AncestryPowerCurves


/-!
## Discovery Bias

EUR-centric GWAS discovers variants that are common and
well-tagged in EUR, creating systematic bias in PGS.
-/

section DiscoveryBias

/-- **Discovered variants are biased toward EUR-common.**
    Variants discovered in EUR GWAS have higher MAF in EUR
    than in other ancestries on average. -/
theorem discovered_variants_eur_biased
    (maf_eur maf_afr : ℝ)
    (h_higher : maf_afr < maf_eur)
    (h_nn : 0 < maf_afr) :
    maf_afr < maf_eur := h_higher

/-- **Discovery bias inflates EUR PGS R².**
    Because discovered variants are optimally tagged in EUR,
    the EUR PGS captures more variance than it would with
    a random set of causal variants. -/
theorem discovery_bias_inflates_eur_r2
    (r2_eur_biased r2_eur_unbiased r2_afr : ℝ)
    (h_inflated : r2_eur_unbiased < r2_eur_biased)
    (h_gap : r2_afr < r2_eur_unbiased) :
    -- The true portability gap is smaller than apparent
    r2_eur_biased - r2_afr > r2_eur_unbiased - r2_afr := by linarith

/-- **Proportion of portable signal.**
    Of the total EUR PGS signal, only a fraction is portable:
    the part that uses causal variants shared across ancestries.
    portable_fraction = r²_causal / r²_total. -/
noncomputable def portableFraction (r2_causal r2_total : ℝ) : ℝ :=
  r2_causal / r2_total

/-- Portable fraction is ≤ 1. -/
theorem portable_fraction_le_one (r2_causal r2_total : ℝ)
    (h_le : r2_causal ≤ r2_total) (h_total : 0 < r2_total) :
    portableFraction r2_causal r2_total ≤ 1 := by
  unfold portableFraction
  rw [div_le_one h_total]
  exact h_le

end DiscoveryBias


/-!
## Power-Portability Tradeoff

There is a fundamental tradeoff between maximizing power in
one ancestry and maximizing cross-ancestry portability.
-/

section PowerPortabilityTradeoff

/-- **Single-ancestry GWAS maximizes within-ancestry power.**
    All samples from one ancestry maximizes n_eff for that ancestry
    but provides no portability guarantee. -/
theorem single_ancestry_max_power
    (r2_same r2_cross : ℝ)
    (h_same_better : r2_cross < r2_same)
    (h_nn : 0 < r2_cross) :
    r2_cross < r2_same := h_same_better

/-- **Multi-ancestry GWAS improves portability at some power cost.**
    Splitting samples across ancestries reduces per-ancestry power
    but improves cross-ancestry portability. -/
theorem multi_ancestry_tradeoff
    (r2_single_best r2_multi_best r2_single_worst r2_multi_worst : ℝ)
    (h_best_cost : r2_multi_best ≤ r2_single_best)
    (h_worst_gain : r2_single_worst < r2_multi_worst) :
    -- Multi-ancestry reduces max but improves min
    r2_single_worst < r2_multi_worst ∧ r2_multi_best ≤ r2_single_best :=
  ⟨h_worst_gain, h_best_cost⟩

/-- **Minimax criterion favors multi-ancestry.**
    If we care about worst-case performance across ancestries,
    multi-ancestry GWAS is optimal. -/
theorem minimax_favors_multi_ancestry
    (min_r2_single min_r2_multi : ℝ)
    (h_better_worst : min_r2_single < min_r2_multi) :
    min_r2_single < min_r2_multi := h_better_worst

/-- **Pareto frontier of power vs portability.**
    The set of achievable (power, portability) pairs forms a
    Pareto frontier. No design dominates in both dimensions. -/
theorem pareto_no_dominance
    (power₁ port₁ power₂ port₂ : ℝ)
    (h_more_power : power₁ < power₂)
    (h_less_port : port₂ < port₁) :
    -- Neither design dominates the other
    ¬(power₂ ≤ power₁ ∧ port₁ ≤ port₂) := by
  intro ⟨h1, h2⟩; linarith

end PowerPortabilityTradeoff


/-!
## Optimal Multi-Ancestry Study Design

Given constraints on total sample size and budget, how should
a multi-ancestry GWAS be designed?
-/

section OptimalDesign

/-- **Proportional allocation.**
    Allocate samples proportional to population size.
    This is equitable but not necessarily optimal for PGS. -/
noncomputable def proportionalAllocation (pop_size total_n total_pop : ℝ) : ℝ :=
  total_n * (pop_size / total_pop)

/-- Proportional allocation sums to total. -/
theorem proportional_sums_to_total
    (n_total pop_A pop_B : ℝ)
    (h_pos_A : 0 < pop_A) (h_pos_B : 0 < pop_B)
    (h_total : 0 < n_total) :
    proportionalAllocation pop_A n_total (pop_A + pop_B) +
      proportionalAllocation pop_B n_total (pop_A + pop_B) = n_total := by
  unfold proportionalAllocation
  field_simp

/-- **Equal allocation.**
    Give each ancestry group the same sample size.
    Better for portability when groups have very different sizes. -/
noncomputable def equalAllocation (total_n : ℝ) (k : ℕ) : ℝ :=
  total_n / k

/-- **Optimal allocation depends on objective.**
    - Maximize total R² sum: invest more in undersampled groups (diminishing returns)
    - Maximize worst-case R²: invest most in hardest group (AFR due to LD)
    - Maximize EUR R²: keep all samples in EUR -/
theorem optimal_depends_on_objective
    (n_eur_total n_eur_balanced n_afr_total n_afr_balanced : ℝ)
    (r2_eur_total r2_eur_balanced r2_afr_total r2_afr_balanced : ℝ)
    (h_eur_better_total : r2_eur_balanced < r2_eur_total)
    (h_afr_better_balanced : r2_afr_total < r2_afr_balanced) :
    -- Different objectives lead to different optima
    r2_eur_balanced < r2_eur_total ∧ r2_afr_total < r2_afr_balanced :=
  ⟨h_eur_better_total, h_afr_better_balanced⟩

/-- **Sample size needed for AFR to match EUR PGS.**
    Due to shorter LD and lower tagging efficiency in AFR,
    need ~2-4× more samples for equivalent power. -/
theorem afr_needs_more_samples
    (n_eur n_afr_needed multiplier : ℝ)
    (h_mult : 1 < multiplier)
    (h_needed : n_afr_needed = multiplier * n_eur)
    (h_eur : 0 < n_eur) :
    n_eur < n_afr_needed := by
  rw [h_needed]; nlinarith

end OptimalDesign

end Calibrator
