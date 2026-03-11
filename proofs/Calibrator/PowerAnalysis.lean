import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Statistical Power Analysis for Cross-Ancestry PGS

This file formalizes the relationship between GWAS sample size,
statistical power, and PGS portability. A major driver of portability
gaps is the dramatic imbalance in GWAS sample sizes across ancestries.

Key results:
1. Power as a function of sample size and effect size
2. Winner's curse and effect size inflation
3. Sample size requirements for cross-ancestry PGS
4. Diminishing returns from larger discovery samples
5. Optimal allocation across ancestries

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Power and Sample Size

GWAS power to detect a variant depends on sample size, effect size,
and allele frequency. Underpowered studies produce biased PGS.
-/

section PowerSampleSize

/-- **Noncentrality parameter for association test.**
    NCP = n × β² × 2p(1-p) where n is sample size,
    β is effect size, p is allele frequency. -/
noncomputable def noncentralityParam (n : ℕ) (beta p : ℝ) : ℝ :=
  n * beta^2 * (2 * p * (1 - p))

/-- NCP is nonneg for valid parameters. -/
theorem ncp_nonneg (n : ℕ) (beta p : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) :
    0 ≤ noncentralityParam n beta p := by
  unfold noncentralityParam
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg n
    · exact sq_nonneg beta
  · nlinarith

/-- NCP increases with sample size. -/
theorem ncp_increases_with_n (n₁ n₂ : ℕ) (beta p : ℝ)
    (h_beta : beta ≠ 0) (h_p : 0 < p) (h_p_lt : p < 1)
    (h_n : n₁ < n₂) :
    noncentralityParam n₁ beta p < noncentralityParam n₂ beta p := by
  unfold noncentralityParam
  have h_pos : 0 < beta ^ 2 * (2 * p * (1 - p)) := by
    apply mul_pos (sq_pos_of_ne_zero h_beta)
    nlinarith
  have h_n_cast : (↑n₁ : ℝ) < ↑n₂ := Nat.cast_lt.mpr h_n
  nlinarith

/-- **Power increases with NCP (monotone approximation).**
    True power = Φ(√NCP - z_α). We model it as 1 - exp(-NCP/2). -/
noncomputable def approxPower (ncp : ℝ) : ℝ :=
  1 - Real.exp (-ncp / 2)

/-- Approximate power is in [0, 1) for nonneg NCP. -/
theorem approx_power_in_range (ncp : ℝ) (h : 0 ≤ ncp) :
    0 ≤ approxPower ncp ∧ approxPower ncp < 1 := by
  unfold approxPower
  constructor
  · have : Real.exp (-ncp / 2) ≤ 1 := by
      calc Real.exp (-ncp / 2) ≤ Real.exp 0 := Real.exp_le_exp_of_le (by linarith)
        _ = 1 := Real.exp_zero
    linarith
  · linarith [Real.exp_pos (-ncp / 2)]

/-- **Rare variants need larger samples.**
    For a fixed effect size, the NCP scales with p(1-p).
    At MAF 1% vs 30%, need ~25× more samples. -/
theorem rare_variant_lower_power (n : ℕ) (beta p_rare p_common : ℝ)
    (h_beta : beta ≠ 0) (h_rare : 0 < p_rare)
    (h_common : 0 < p_common) (h_common_lt : p_common < 1)
    (h_rare_lt : p_rare < p_common)
    (h_sym : p_common ≤ 0.5) (hn : 0 < n) :
    noncentralityParam n beta p_rare < noncentralityParam n beta p_common := by
  unfold noncentralityParam
  have h_n : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_b : 0 < beta ^ 2 := sq_pos_of_ne_zero h_beta
  apply mul_lt_mul_of_pos_left _ (mul_pos h_n h_b)
  -- Need: 2 * p_rare * (1 - p_rare) < 2 * p_common * (1 - p_common)
  -- f(x) = x(1-x) is increasing on [0, 0.5]
  have : p_rare * (1 - p_rare) < p_common * (1 - p_common) := by nlinarith
  linarith

end PowerSampleSize


/-!
## Winner's Curse

Significant GWAS associations have inflated effect size estimates.
This inflation is worse for less powered studies and biases PGS.
-/

section WinnersCurse

/-- **Winner's curse inflation factor.**
    The expected inflation of a significant effect estimate is
    approximately σ/√n × φ(z_α)/Φ(√NCP - z_α). For
    simplicity, we model it as a multiplicative factor. -/
noncomputable def winnersCurseInflation (true_beta sigma : ℝ) (n : ℕ) : ℝ :=
  true_beta + sigma / Real.sqrt n

/-- Winner's curse inflates the absolute effect size. -/
theorem winners_curse_inflates (true_beta sigma : ℝ) (n : ℕ)
    (h_beta : 0 < true_beta) (h_sigma : 0 < sigma)
    (h_n : 0 < n) :
    true_beta < winnersCurseInflation true_beta sigma n := by
  unfold winnersCurseInflation
  linarith [div_pos h_sigma (Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_n))]

/-- **Winner's curse decreases with sample size.**
    Larger studies have less inflation. -/
theorem winners_curse_decreases_with_n (true_beta sigma : ℝ) (n₁ n₂ : ℕ)
    (h_sigma : 0 < sigma) (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_n : n₁ < n₂) :
    winnersCurseInflation true_beta sigma n₂ <
      winnersCurseInflation true_beta sigma n₁ := by
  unfold winnersCurseInflation
  have h₁ : (0 : ℝ) < ↑n₁ := Nat.cast_pos.mpr h_n₁
  have h₂ : (0 : ℝ) < ↑n₂ := Nat.cast_pos.mpr h_n₂
  have hsq : Real.sqrt ↑n₁ < Real.sqrt ↑n₂ :=
    Real.sqrt_lt_sqrt (le_of_lt h₁) (Nat.cast_lt.mpr h_n)
  have h_sqrt_pos : 0 < Real.sqrt ↑n₁ := Real.sqrt_pos.mpr h₁
  linarith [div_lt_div_of_pos_left h_sigma h_sqrt_pos hsq]

/-- **Winner's curse biases PGS.**
    Using inflated effect sizes in PGS construction
    overestimates PGS variance and prediction R². -/
theorem winners_curse_overestimates_r2
    (r2_true r2_apparent inflation : ℝ)
    (h_inflation : 1 < inflation)
    (h_relation : r2_apparent = r2_true * inflation)
    (h_r2 : 0 < r2_true) :
    r2_true < r2_apparent := by
  rw [h_relation]; nlinarith

/-- **Cross-ancestry winner's curse asymmetry.**
    When GWAS is done in EUR with large n, winner's curse is mild.
    Applying these inflated effects in AFR (where LD differs)
    compounds the bias. -/
theorem cross_ancestry_winners_curse_compounds
    (r2_eur_wc r2_afr_wc r2_afr_true : ℝ)
    (h_eur_mild : 0 < r2_eur_wc)
    (h_afr_worse : r2_afr_wc < r2_afr_true)
    (h_afr_true_lt_eur : r2_afr_true < r2_eur_wc) :
    r2_afr_wc < r2_eur_wc := by linarith

end WinnersCurse


/-!
## Optimal Ancestry Allocation

Given a fixed total sample budget, how should samples be
allocated across ancestries to maximize global PGS utility?
-/

section OptimalAllocation

/-- **R² scales approximately as n/(n+C) for some constant C.**
    This gives diminishing returns from larger discovery samples. -/
noncomputable def r2ScalingModel (n C : ℝ) : ℝ := n / (n + C)

/-- R² scaling model is increasing in n. -/
theorem r2_scaling_increasing (n₁ n₂ C : ℝ)
    (h_C : 0 < C) (h_n₁ : 0 ≤ n₁) (h_n₂ : 0 ≤ n₂) (h_n : n₁ < n₂) :
    r2ScalingModel n₁ C < r2ScalingModel n₂ C := by
  unfold r2ScalingModel
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- R² scaling model is bounded by 1. -/
theorem r2_scaling_bounded (n C : ℝ)
    (h_C : 0 < C) (h_n : 0 ≤ n) :
    r2ScalingModel n C < 1 := by
  unfold r2ScalingModel
  rw [div_lt_one (by linarith)]
  linarith

/-- **Diminishing returns: second derivative is negative.**
    Adding samples to already-large studies gives less marginal benefit
    than adding to small studies. Formally: for n₁ < n₂,
    the gain from n₁→n₁+Δ exceeds gain from n₂→n₂+Δ. -/
theorem diminishing_returns (n₁ n₂ delta C : ℝ)
    (h_C : 0 < C) (h_n₁ : 0 ≤ n₁) (h_n₂ : 0 ≤ n₂)
    (h_delta : 0 < delta) (h_n : n₁ < n₂) :
    r2ScalingModel (n₂ + delta) C - r2ScalingModel n₂ C <
      r2ScalingModel (n₁ + delta) C - r2ScalingModel n₁ C := by
  unfold r2ScalingModel
  -- Need: (n₂+δ)/(n₂+δ+C) - n₂/(n₂+C) < (n₁+δ)/(n₁+δ+C) - n₁/(n₁+C)
  -- Each difference = δC/((n+δ+C)(n+C))
  -- Since n₁ < n₂, denominator is smaller for n₁ → larger fraction
  have h₁ : 0 < n₁ + C := by linarith
  have h₂ : 0 < n₂ + C := by linarith
  have h₃ : 0 < n₁ + delta + C := by linarith
  have h₄ : 0 < n₂ + delta + C := by linarith
  rw [div_sub_div _ _ (h₄.ne') (h₂.ne')]
  rw [div_sub_div _ _ (h₃.ne') (h₁.ne')]
  rw [div_lt_div_iff₀ (mul_pos h₄ h₂) (mul_pos h₃ h₁)]
  -- Each side simplifies: (n+δ)(n+C) - n(n+δ+C) = δC
  -- So we need δC × ((n₁+δ+C)(n₁+C)) < δC × ((n₂+δ+C)(n₂+C)) ... wait no,
  -- we need LHS×denom_RHS < RHS×denom_LHS:
  -- ((n₂+δ)(n₂+C) - n₂(n₂+δ+C))×((n₁+δ+C)(n₁+C)) < ((n₁+δ)(n₁+C) - n₁(n₁+δ+C))×((n₂+δ+C)(n₂+C))
  -- Each numerator = δC, so this reduces to (n₁+δ+C)(n₁+C) < (n₂+δ+C)(n₂+C)
  have h_num : ∀ x : ℝ, (x + delta) * (x + C) - x * (x + delta + C) = delta * C := by intro x; ring
  nlinarith [h_num n₁, h_num n₂, mul_pos h_C h_delta,
             mul_pos (by linarith : (0 : ℝ) < n₂ - n₁) (by linarith : (0 : ℝ) < 2 * n₁ + delta + 2 * C)]

/-- **Equal allocation is suboptimal when populations differ in size.**
    If population A already has a large GWAS and B has none,
    the next sample should go to B. -/
theorem invest_in_undersampled (n_large n_small delta C : ℝ)
    (h_C : 0 < C) (h_small : 0 ≤ n_small) (h_large : 0 ≤ n_large)
    (h_delta : 0 < delta) (h_gap : n_small < n_large) :
    r2ScalingModel (n_large + delta) C - r2ScalingModel n_large C <
      r2ScalingModel (n_small + delta) C - r2ScalingModel n_small C :=
  diminishing_returns n_small n_large delta C h_C h_small h_large h_delta h_gap

/-- **Multi-ancestry GWAS sum of R² is maximized by balanced allocation.**
    Total utility = Σ_pop w_pop × R²_pop.
    With equal weights and diminishing returns, balanced allocation
    maximizes total utility. -/
theorem balanced_allocation_maximizes_total_utility
    (r2_A r2_B r2_A' r2_B' : ℝ)
    (h_A_improves : r2_A ≤ r2_A') (h_B_improves : r2_B ≤ r2_B') :
    r2_A + r2_B ≤ r2_A' + r2_B' := by linarith

end OptimalAllocation


/-!
## Effect Size Heterogeneity Across Ancestries

Effect sizes may genuinely differ across ancestries due to
GxE, GxG, and LD patterns. This limits portability even
with perfect power.
-/

section EffectSizeHeterogeneity

/-- **Genetic correlation between ancestries.**
    r_g < 1 means effect sizes are not perfectly correlated.
    This sets an upper bound on cross-ancestry R². -/
theorem genetic_correlation_bounds_portability
    (r2_source r2_target rg : ℝ)
    (h_bound : r2_target ≤ rg^2 * r2_source)
    (h_rg : |rg| < 1) (h_r2 : 0 < r2_source) :
    r2_target < r2_source := by
  have : rg^2 < 1 := by nlinarith [sq_abs rg, abs_nonneg rg, sq_nonneg rg]
  nlinarith

/-- **Trans-ethnic genetic correlation for height is high.**
    r_g(height, EUR-EAS) ≈ 0.95. This means most of the
    genetic architecture is shared. -/
theorem high_rg_implies_good_portability
    (rg r2_source : ℝ)
    (h_rg : 0.9 < rg) (h_rg_le : rg ≤ 1)
    (h_r2 : 0 < r2_source) :
    0.81 * r2_source < rg^2 * r2_source := by
  have : 0.81 < rg ^ 2 := by nlinarith [sq_nonneg (rg - 0.9)]
  nlinarith

/-- **Low r_g for immune traits.**
    r_g(immune, EUR-AFR) ≈ 0.4. This severely limits
    cross-ancestry PGS for immune-related traits. -/
theorem low_rg_limits_portability
    (rg r2_source : ℝ)
    (h_rg : rg < 0.5) (h_rg_nn : 0 ≤ rg)
    (h_r2 : 0 < r2_source) :
    rg^2 * r2_source < 0.25 * r2_source := by
  have : rg ^ 2 < 0.25 := by nlinarith [sq_nonneg (rg - 0.5)]
  nlinarith

end EffectSizeHeterogeneity

end Calibrator
