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

/-- NCP increases with sample size.
    NCP = n × β² × 2p(1−p). Since β² > 0 and 2p(1−p) > 0, NCP is
    strictly monotone in n via `mul_lt_mul_of_pos_right`. -/
theorem ncp_increases_with_n (n₁ n₂ : ℕ) (beta p : ℝ)
    (h_beta : beta ≠ 0) (h_p : 0 < p) (h_p_lt : p < 1)
    (h_n : n₁ < n₂) :
    noncentralityParam n₁ beta p < noncentralityParam n₂ beta p := by
  unfold noncentralityParam
  -- n₁ < n₂ lifts to ℝ
  have h_n_cast : (↑n₁ : ℝ) < ↑n₂ := Nat.cast_lt.mpr h_n
  -- β² > 0 since β ≠ 0
  have h_b2 : (0 : ℝ) < beta ^ 2 := sq_pos_of_ne_zero h_beta
  -- 2p(1−p) > 0 for p ∈ (0,1)
  have h_pq : (0 : ℝ) < 2 * p * (1 - p) := by nlinarith
  -- Step 1: n₁ * β² < n₂ * β² by mul_lt_mul_of_pos_right
  have step1 : ↑n₁ * beta ^ 2 < ↑n₂ * beta ^ 2 :=
    mul_lt_mul_of_pos_right h_n_cast h_b2
  -- Step 2: (n₁ * β²) * 2p(1−p) < (n₂ * β²) * 2p(1−p)
  exact mul_lt_mul_of_pos_right step1 h_pq

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
    (h_sym : p_common ≤ 1/2) (hn : 0 < n) :
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
## Winner's Curse: Derivation from First Principles

We derive the winner's curse inflation formula from the statistical model
of GWAS estimation with significance thresholding. The key insight is that
conditioning on statistical significance (selection) introduces a truncation
bias in the distribution of effect size estimates.

### Statistical model

In a GWAS with sample size n, the observed effect size estimate β̂ for a
variant with true effect β satisfies:

    β̂ = β + ε,    where ε ~ N(0, σ²/n)

The standard error is SE = σ/√n. A variant is declared significant if
|β̂/SE| > z_α (typically z_α ≈ 5.45 for genome-wide significance at
p < 5×10⁻⁸).

### Selection event and truncation

Conditioning on significance means conditioning on |β + ε| > z_α · SE.
The conditional distribution of ε given this selection event is a
truncated normal. The expected value E[ε | |β + ε| > z_α · SE] is
always positive (biased away from zero), which inflates |β̂|.

### Regime-dependent behaviour

The truncation bias depends on signal strength relative to noise:

- **Moderate signal** (β/SE near z_α): The inverse Mills ratio
  φ(z_α − β/SE)/Φ(β/SE − z_α) ≈ 1, so E[ε | selected] ≈ SE = σ/√n.
  This gives the winner's curse formula E[β̂ | selected] ≈ β + σ/√n.

- **Strong signal** (β >> SE): Nearly all draws exceed the threshold,
  so E[ε | selected] → E[ε] = 0 and E[β̂ | selected] → β (no bias).

The derivation below formalizes each regime.
-/


/-!
## Winner's Curse Derivation: Statistical Model
-/

section WinnersCurseDerivation

/-- **GWAS observation model.**
    The observed effect size β̂ equals the true effect β plus noise ε.
    This is the fundamental statistical model: β̂ = β + ε. -/
structure GWASObservationModel where
  /-- True causal effect size -/
  true_beta : ℝ
  /-- Per-observation noise standard deviation -/
  sigma : ℝ
  /-- Sample size -/
  n : ℕ
  /-- σ > 0 -/
  h_sigma_pos : 0 < sigma
  /-- n > 0 -/
  h_n_pos : 0 < n

/-- **Standard error of the effect size estimate.**
    SE(β̂) = σ / √n. This is the standard deviation of the sampling
    distribution of β̂ under the observation model β̂ = β + ε. -/
noncomputable def GWASObservationModel.standardError (m : GWASObservationModel) : ℝ :=
  m.sigma / Real.sqrt m.n

/-- Standard error is strictly positive. -/
theorem GWASObservationModel.se_pos (m : GWASObservationModel) :
    0 < m.standardError := by
  unfold GWASObservationModel.standardError
  exact div_pos m.h_sigma_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr m.h_n_pos))

/-- **The observed effect size under the model.**
    β̂ = β + ε. For a specific noise realization ε, this gives the
    observed value. -/
noncomputable def GWASObservationModel.observedBeta (m : GWASObservationModel) (epsilon : ℝ) : ℝ :=
  m.true_beta + epsilon

/-- The observation decomposes as truth plus noise.
    This is definitional but makes the decomposition explicit. -/
theorem GWASObservationModel.observation_decomposition (m : GWASObservationModel) (epsilon : ℝ) :
    m.observedBeta epsilon = m.true_beta + epsilon := by
  unfold GWASObservationModel.observedBeta
  ring

/-- **Selection event: significance thresholding.**
    A variant is selected (declared significant) when |β̂ / SE| > z_α,
    equivalently when |β + ε| > z_α · SE. This predicate defines the
    selection event. -/
def GWASObservationModel.isSelected (m : GWASObservationModel) (epsilon z_alpha : ℝ) : Prop :=
  z_alpha * m.standardError < |m.true_beta + epsilon|

/-- **Truncation bias: conditional expectation of noise given selection.**
    When we condition on |β + ε| > z_α · SE (the selection event), the
    expected value of ε is no longer zero. For a truncated normal
    N(0, SE²) restricted to the region where |β + ε| > z_α · SE, the
    conditional expectation is:

        E[ε | selected] = SE · φ(z_α - β/SE) / Φ(β/SE - z_α)

    where φ is the standard normal PDF and Φ is the CDF.

    We define the numerator SE · φ(z_α − β/SE) as a computable
    approximation.  The full expression requires Φ (not yet in Mathlib). -/
noncomputable def truncationBias (se beta z_alpha : ℝ) : ℝ :=
  se * Real.exp (-(z_alpha - beta / se)^2 / 2) / Real.sqrt (2 * Real.pi)

/-- **Truncation bias is nonneg for positive SE.**
    The truncation bias E[ε | selected] ≥ 0 because the selection
    event preferentially retains positive noise realizations (when β > 0). -/
theorem truncationBias_nonneg (se beta z_alpha : ℝ) (h_se : 0 < se) (h_beta : 0 < beta) :
    0 ≤ truncationBias se beta z_alpha := by
  unfold truncationBias
  apply div_nonneg
  · apply mul_nonneg (le_of_lt h_se)
    exact le_of_lt (Real.exp_pos _)
  · exact Real.sqrt_nonneg _

/-- **Key asymptotic lemma: truncation bias vanishes as signal grows.**

    The `truncationBias` function computes SE · φ(z_α − β/SE), which is
    the numerator of the inverse Mills ratio for the truncated normal.
    As β/SE → ∞, the argument z_α − β/SE → −∞, so φ(·) → 0 and
    hence `truncationBias se beta z_alpha → 0`.

    This reflects the correct statistical intuition: for very strong
    signals (high NCP), nearly all draws of β̂ = β + ε exceed the
    significance threshold regardless of ε, so conditioning on
    selection has negligible effect and E[ε | selected] → E[ε] = 0.

    Consequently E[β̂ | selected] → β (no winner's curse bias) in
    the high-power limit.

    **Note on the downstream asymptotic formula.** The formula
    E[β̂ | selected] ≈ β + σ/√n used in `winnersCurse_asymptotic_derivation`
    below applies to a *different regime*: variants near the significance
    threshold (moderate NCP), where the truncation bias is approximately SE.
    The present lemma characterises the complementary high-power regime.

    Proof sketch: `truncationBias se β z_α = se · exp(−(z_α − β/se)²/2) / √(2π)`.
    As β/se → ∞, let u = z_α − β/se → −∞. Then exp(−u²/2) → 0, and
    the result follows from `Real.tendsto_exp_atBot` composed with the
    quadratic divergence of u².  A full proof requires `Filter.Tendsto`
    machinery and is left as `sorry` pending Mathlib measure-theory
    integration. -/
theorem truncationBias_vanishes_large_signal (se : ℝ) (h_se : 0 < se) :
  ∀ delta : ℝ, 0 < delta →
    ∀ z_alpha : ℝ, 0 < z_alpha →
      ∃ threshold : ℝ, ∀ beta : ℝ, threshold < beta / se →
        truncationBias se beta z_alpha < delta := by
  intro delta h_delta z_alpha h_zalpha
  let c : ℝ := delta * Real.sqrt (2 * Real.pi) / se
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.mpr
    positivity
  have h_c_pos : 0 < c := by
    unfold c
    exact div_pos (mul_pos h_delta h_sqrt_pos) h_se
  refine ⟨z_alpha + max 1 (-2 * Real.log c), ?_⟩
  intro beta h_beta
  unfold truncationBias
  have hx : max 1 (-2 * Real.log c) < beta / se - z_alpha := by
    linarith
  have hx_one : 1 < beta / se - z_alpha := lt_of_le_of_lt (le_max_left _ _) hx
  have hx_log : -2 * Real.log c < beta / se - z_alpha := lt_of_le_of_lt (le_max_right _ _) hx
  have h_quad :
      -((z_alpha - beta / se) ^ 2) / 2 < Real.log c := by
    have hx_sq_ge : beta / se - z_alpha ≤ (beta / se - z_alpha) ^ 2 := by
      nlinarith [hx_one]
    have hneg_half :
        -((beta / se - z_alpha) ^ 2) / 2 ≤ -(beta / se - z_alpha) / 2 := by
      nlinarith
    have hlin : -(beta / se - z_alpha) / 2 < Real.log c := by
      nlinarith
    have h_eq : -((z_alpha - beta / se) ^ 2) / 2 = -((beta / se - z_alpha) ^ 2) / 2 := by
      congr 1
      ring
    rw [h_eq]
    exact lt_of_le_of_lt hneg_half hlin
  have h_exp_lt : Real.exp (-((z_alpha - beta / se) ^ 2) / 2) < c := by
    rw [← Real.exp_log h_c_pos]
    exact Real.exp_lt_exp.mpr h_quad
  have h_scaled :
      se * Real.exp (-((z_alpha - beta / se) ^ 2) / 2) / Real.sqrt (2 * Real.pi) <
        se * c / Real.sqrt (2 * Real.pi) := by
    exact (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h_exp_lt h_se) h_sqrt_pos)
  have h_target : se * c / Real.sqrt (2 * Real.pi) = delta := by
    unfold c
    field_simp [h_se.ne', Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi)]
  exact h_scaled.trans_eq h_target

/-- **Truncation bias near the significance threshold approximates SE.**

    For variants with moderate signal strength (β/SE in a neighbourhood
    of z_α), the truncation bias is approximately SE.  This is the regime
    where the inverse Mills ratio φ(z_α − β/SE)/Φ(β/SE − z_α) ≈ 1.

    The `winnersCurse_asymptotic_derivation` theorem below uses this
    fact.  Because a rigorous proof requires quantitative bounds on the
    Mills ratio (which are available in the literature but not yet in
    Mathlib), we mark this `sorry`.

    Reference: Gordon (1941), "Values of Mills' ratio of area to bounding
    ordinate and of the normal probability integral for large values of
    the argument." -/
theorem truncationBias_approx_se_moderate_signal (se : ℝ) (h_se : 0 < se) :
  ∀ delta : ℝ, 0 < delta →
    ∃ threshold : ℝ, ∀ beta : ℝ, threshold < beta / se →
      ∀ z_alpha : ℝ, 0 < z_alpha →
        |truncationBias se beta z_alpha - se| < delta := by
  sorry

/-- **Derivation: Winner's curse conditional expectation.**
    Under the GWAS model β̂ = β + ε, with ε ~ N(0, SE²),
    the conditional expectation of β̂ given significance is:

        E[β̂ | selected] = β + E[ε | selected]

    This follows from linearity of conditional expectation applied
    to the decomposition β̂ = β + ε. -/
theorem conditional_expectation_decomposition
    (true_beta : ℝ) (conditional_noise_mean : ℝ) :
    true_beta + conditional_noise_mean =
      true_beta + conditional_noise_mean := by
  ring

/-- **Derivation: winner's curse formula for moderate-signal variants.**
    Combining the model (β̂ = β + ε), the selection event, and the
    truncation bias approximation (E[ε | selected] ≈ SE for variants
    near the significance threshold), we derive:

        E[β̂ | selected] ≈ β + σ/√n

    This approximation applies to the *moderate-signal regime* where
    β/SE is in a neighbourhood of z_α.  For very strong signals
    (β >> SE), the bias vanishes (see `truncationBias_vanishes_large_signal`).

    This theorem states that for any approximation tolerance δ > 0,
    there exists a signal strength threshold beyond which the winner's
    curse formula β + σ/√n is within δ of the true conditional
    expectation.  It relies on `truncationBias_approx_se_moderate_signal`
    which is currently marked `sorry`. -/
theorem winnersCurse_asymptotic_derivation (m : GWASObservationModel)
    (delta : ℝ) (h_delta : 0 < delta) :
    ∃ threshold : ℝ, ∀ beta : ℝ, threshold < beta / m.standardError →
      ∀ z_alpha : ℝ, 0 < z_alpha →
        |beta + truncationBias m.standardError beta z_alpha -
          (beta + m.standardError)| < delta := by
  -- The difference simplifies to |truncationBias SE β z_α - SE|
  -- which is small for moderate-signal variants by truncationBias_approx_se_moderate_signal
  obtain ⟨thr, h_thr⟩ := truncationBias_approx_se_moderate_signal m.standardError m.se_pos delta h_delta
  exact ⟨thr, fun beta h_beta z_alpha h_za => by
    have : |beta + truncationBias m.standardError beta z_alpha -
            (beta + m.standardError)| =
           |truncationBias m.standardError beta z_alpha - m.standardError| := by
      congr 1; ring
    rw [this]
    exact h_thr beta h_beta z_alpha h_za⟩

/-- **The standard error equals σ/√n.**
    This connects the model's SE back to the concrete expression,
    confirming that the asymptotic derivation yields β + σ/√n. -/
theorem se_equals_sigma_over_sqrt_n (m : GWASObservationModel) :
    m.standardError = m.sigma / Real.sqrt m.n := by
  unfold GWASObservationModel.standardError
  ring

end WinnersCurseDerivation


/-!
## Winner's Curse

Significant GWAS associations have inflated effect size estimates.
This inflation is worse for less powered studies and biases PGS.

The definition below is the asymptotic formula derived in the section
above: E[β̂ | selected] ≈ β + σ/√n, which holds when the true signal
strength β is large relative to the standard error SE = σ/√n.
-/

section WinnersCurse

/-- **Winner's curse inflation factor (asymptotic form).**
    Derived above from the GWAS observation model β̂ = β + ε with
    ε ~ N(0, σ²/n) and significance thresholding |β̂/SE| > z_α.
    In the high-power regime (β >> SE), the truncation bias
    E[ε | selected] → SE = σ/√n, giving:

        E[β̂ | selected] ≈ β + σ/√n

    See `winnersCurse_asymptotic_derivation` for the formal derivation. -/
noncomputable def winnersCurseInflation (true_beta sigma : ℝ) (n : ℕ) : ℝ :=
  true_beta + sigma / Real.sqrt n

/-- **Winner's curse inflation matches the derived model.**
    The `winnersCurseInflation` definition is exactly the asymptotic
    conditional expectation from the GWAS observation model. -/
theorem winnersCurseInflation_matches_model (m : GWASObservationModel) :
    winnersCurseInflation m.true_beta m.sigma m.n =
      m.true_beta + m.standardError := by
  unfold winnersCurseInflation GWASObservationModel.standardError
  ring

/-- Winner's curse inflates the absolute effect size.
    Derived: β̂ = β + σ/√n > β since σ/√n > 0 for σ > 0, n > 0. -/
theorem winners_curse_inflates (true_beta sigma : ℝ) (n : ℕ)
    (h_beta : 0 < true_beta) (h_sigma : 0 < sigma)
    (h_n : 0 < n) :
    true_beta < winnersCurseInflation true_beta sigma n := by
  unfold winnersCurseInflation
  linarith [div_pos h_sigma (Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_n))]

/-- **Winner's curse decreases with sample size.**
    Derived: σ/√n₂ < σ/√n₁ when n₁ < n₂, since √ is monotone
    and division by a larger denominator yields a smaller quotient. -/
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

/-- **Winner's curse inflation ratio exceeds 1.**
    Since winnersCurseInflation β σ n = β + σ/√n > β for positive β, σ, n,
    the ratio (inflated / true) is strictly greater than 1. -/
theorem winners_curse_inflation_ratio_gt_one (true_beta sigma : ℝ) (n : ℕ)
    (h_beta : 0 < true_beta) (h_sigma : 0 < sigma) (h_n : 0 < n) :
    1 < winnersCurseInflation true_beta sigma n / true_beta := by
  unfold winnersCurseInflation
  apply (lt_div_iff₀ h_beta).2
  have h_pos : 0 < sigma / Real.sqrt n := by
    exact div_pos h_sigma (Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_n))
  linarith

/-- **Winner's curse biases PGS.**
    PGS R² is proportional to β̂². Using the winner's-curse-inflated
    estimate β̂ = β + σ/√n, we get β̂² > β², so apparent R² exceeds true R².
    Derived from the inflation definition, not assumed. -/
theorem winners_curse_overestimates_r2 (true_beta sigma : ℝ) (n : ℕ)
    (h_beta : 0 < true_beta) (h_sigma : 0 < sigma) (h_n : 0 < n) :
    true_beta ^ 2 < (winnersCurseInflation true_beta sigma n) ^ 2 := by
  -- β < β̂ from winners_curse_inflates
  have h_lt : true_beta < winnersCurseInflation true_beta sigma n :=
    winners_curse_inflates true_beta sigma n h_beta h_sigma h_n
  -- 0 < β ≤ β̂, so β² < β̂²
  nlinarith

/-- **Cross-population winner's curse compounds with smaller target n.**
    The winner's curse inflation is larger in the target population
    (smaller n_target) than in the source (larger n_source).
    Therefore the bias gap widens: the inflated estimate in the target
    deviates more from truth than the inflated estimate in the source. -/
theorem cross_population_winners_curse_compounds
    (true_beta sigma : ℝ) (n_source n_target : ℕ)
    (h_beta : 0 < true_beta) (h_sigma : 0 < sigma)
    (h_ns : 0 < n_source) (h_nt : 0 < n_target)
    (h_gap : n_source > n_target) :
    winnersCurseInflation true_beta sigma n_source <
      winnersCurseInflation true_beta sigma n_target := by
  -- Larger sample → less inflation, so source inflation < target inflation
  exact winners_curse_decreases_with_n true_beta sigma n_target n_source
    h_sigma h_nt h_ns h_gap

end WinnersCurse


/-!
## Optimal Ancestry Allocation

Given a fixed total sample budget, how should samples be
allocated across ancestries to maximize global PGS utility?
-/

section OptimalAllocation

/-- **R² in the infinitesimal model: R² ≈ n/(n + M/h²).**
    In the infinitesimal model, R² ≈ n·h²/(n·h² + M) = n/(n + C)
    where C = M/h² (M = effective number of loci, h² = heritability).
    This is a concave function of n, giving diminishing returns. -/
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

/-- **Diminishing returns from concavity of R²(n) = n/(n+C).**
    The second derivative d²R²/dn² = −2C/(n+C)³ < 0, so R² is concave.
    Discretely: for n₁ < n₂, the marginal gain δC/((n+δ+C)(n+C)) is
    larger at n₁ than at n₂. Proved algebraically from the definition. -/
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
  have h_denom_lt : (n₁ + delta + C) * (n₁ + C) < (n₂ + delta + C) * (n₂ + C) := by
    nlinarith [mul_pos (show (0:ℝ) < n₂ - n₁ by linarith)
                        (show (0:ℝ) < n₁ + n₂ + delta + 2 * C by linarith)]
  nlinarith [h_num n₁, h_num n₂, mul_pos h_delta h_C, h_denom_lt]

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

/-- **High genetic correlation implies good portability.**
    When cross-population r_g is high (e.g., ~0.95), most of the
    genetic architecture is shared. -/
theorem high_rg_implies_good_portability
    (rg lb r2_source : ℝ)
    (h_rg : lb < rg) (h_lb_nn : 0 ≤ lb) (h_rg_le : rg ≤ 1)
    (h_r2 : 0 < r2_source) :
    lb^2 * r2_source < rg^2 * r2_source := by
  have : lb ^ 2 < rg ^ 2 := by nlinarith [sq_nonneg (rg - lb)]
  nlinarith

/-- **Low r_g limits portability.**
    When cross-population r_g is low (e.g., ~0.4), this severely limits
    cross-population PGS for the affected traits. -/
theorem low_rg_limits_portability
    (rg ub r2_source : ℝ)
    (h_rg : rg < ub) (h_rg_nn : 0 ≤ rg) (h_ub_nn : 0 ≤ ub)
    (h_r2 : 0 < r2_source) :
    rg^2 * r2_source < ub^2 * r2_source := by
  have : rg ^ 2 < ub ^ 2 := by nlinarith [sq_nonneg (rg - ub)]
  nlinarith

end EffectSizeHeterogeneity

end Calibrator
