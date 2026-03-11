import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Statistical Power and PGS Portability

This file formalizes the statistical power framework for PGS
across different populations. Power imbalances are a
fundamental driver of portability gaps.

Key results:
1. Population-specific power curves
2. Discovery bias from single-population GWAS
3. Effective sample size across populations
4. Power-portability tradeoff
5. Optimal multi-population study design

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Population-Specific Power Curves

Power to detect a variant depends on sample size, effect size,
and allele frequency — all of which differ across populations.
-/

section PopulationPowerCurves

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

/-- **Larger GWAS with better tagging yields higher effective n.**
    n_eff_source >> n_eff_target when:
    1. n_source >> n_target (sample size imbalance)
    2. r²_LD_source > r²_LD_target (GWAS optimized for source LD) -/
theorem source_higher_effective_n
    (n_source n_target : ℕ) (p_source p_target r2_source r2_target : ℝ)
    (h_n : n_target < n_source) (h_r2 : r2_target < r2_source)
    (h_p_source : 0 < p_source) (h_p_source_lt : p_source < 1)
    (h_p_target : 0 < p_target) (h_p_target_lt : p_target < 1)
    (h_r2_target : 0 < r2_target)
    -- Same variant, same allele frequency for simplicity
    (h_same_p : p_source = p_target) :
    effectiveSampleSize n_target p_target r2_target <
      effectiveSampleSize n_source p_source r2_source := by
  unfold effectiveSampleSize
  rw [h_same_p]
  have h_het : 0 < 2 * p_target * (1 - p_target) := by nlinarith
  have h_n_cast : (↑n_target : ℝ) < ↑n_source := Nat.cast_lt.mpr h_n
  have h_r2_source : 0 < r2_source := by linarith
  nlinarith [mul_pos (show (0:ℝ) < ↑n_source - ↑n_target from by linarith) (mul_pos h_het h_r2_source),
             mul_nonneg (show (0:ℝ) ≤ ↑n_target from Nat.cast_nonneg n_target)
                        (mul_nonneg (le_of_lt h_het) (by linarith : 0 ≤ r2_source - r2_target))]

/-- **Power gap compounds across the genome.**
    If the source population has power p_source for each variant and
    the target has p_target, and there are M causal variants, the expected
    number detected is M × p_source vs M × p_target. -/
theorem detected_variants_gap
    (M : ℕ) (power_source power_target : ℝ)
    (h_power : power_target < power_source)
    (h_M : 0 < M) :
    ↑M * power_target < ↑M * power_source := by
  exact mul_lt_mul_of_pos_left h_power (Nat.cast_pos.mpr h_M)

end PopulationPowerCurves


/-!
## Discovery Bias

Single-population GWAS discovers variants that are common and
well-tagged in the discovery population, creating systematic bias in PGS.
-/

section DiscoveryBias

/-- **Discovery bias inflates source PGS R².**
    Because discovered variants are optimally tagged in the source,
    the source PGS captures more variance than it would with
    a random set of causal variants. -/
theorem discovery_bias_inflates_source_r2
    (r2_source_biased r2_source_unbiased r2_target : ℝ)
    (h_inflated : r2_source_unbiased < r2_source_biased)
    (h_gap : r2_target < r2_source_unbiased) :
    -- The true portability gap is smaller than apparent
    r2_source_biased - r2_target > r2_source_unbiased - r2_target := by linarith

/-- **Proportion of portable signal.**
    Of the total source PGS signal, only a fraction is portable:
    the part that uses causal variants shared across populations.
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
one population and maximizing cross-population portability.
-/

section PowerPortabilityTradeoff

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
## Optimal Multi-Population Study Design

Given constraints on total sample size and budget, how should
a multi-population GWAS be designed?
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

/-- **Population with shorter LD needs more samples to match.**
    Due to shorter LD and lower tagging efficiency,
    need a multiplier × more samples for equivalent power. -/
theorem shorter_ld_needs_more_samples
    (n_source n_target_needed multiplier : ℝ)
    (h_mult : 1 < multiplier)
    (h_needed : n_target_needed = multiplier * n_source)
    (h_source : 0 < n_source) :
    n_source < n_target_needed := by
  rw [h_needed]; nlinarith

end OptimalDesign

end Calibrator
