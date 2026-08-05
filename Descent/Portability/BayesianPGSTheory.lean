/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.OpenQuestions
import Descent.Core.Ratios

namespace Descent.Portability

open MeasureTheory

/-!
# Bayesian PGS Methods and Portability

This file formalizes the theoretical properties of Bayesian PGS methods
(PRS-CS, LDpred, SBayesR) and their implications for portability.
Bayesian methods handle LD structure explicitly, which has different
portability implications compared to C+T.

Key results:
1. Bayesian shrinkage and posterior effect sizes
2. Prior specification and its effect on portability
3. LD reference panel mismatch
4. Posterior predictive distributions across populations
5. Spike-and-slab vs continuous shrinkage

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat Bayesian shrinkage, prior specification or LD reference panels.
Sources for individual results, where they exist, are cited at those results.
-/


/-!
## Bayesian Shrinkage Framework

Bayesian PGS methods estimate posterior effect sizes:
β̂_Bayes = E[β | GWAS summary stats, LD reference].
The shrinkage pattern depends on the prior and LD.
-/

section BayesianShrinkage

/-!
### Derivation of Bayesian Shrinkage from First Principles

We derive the Gaussian posterior shrinkage factor from a standard
Bayesian linear regression model:
  - Prior: β ~ N(0, h)  where h = σ²_β is the prior variance
  - Likelihood: y | β ~ N(β, 1/n)  where n is the data precision
    (equivalently, y is a sufficient statistic with variance 1/n)

By conjugacy of Gaussian prior and Gaussian likelihood:
  - Posterior precision = prior precision + likelihood precision = 1/h + n
  - Posterior variance  = 1/(1/h + n) = h/(1 + n·h)
  - Posterior mean      = posterior_variance × (n × y) = n·h/(1 + n·h) × y

The shrinkage factor n·h/(1 + n·h) is exactly `gaussianPosteriorShrinkage`.
-/

/-- A Bayesian linear regression model with Gaussian prior and Gaussian likelihood.
    `prior_var` is the prior variance h (so prior precision is 1/h).
    `data_precision` is the likelihood precision n (so likelihood variance is 1/n). -/
structure BayesianLinearModel where
  prior_var : ℝ
  data_precision : ℝ
  prior_var_pos : 0 < prior_var
  data_precision_pos : 0 < data_precision

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def BayesianLinearModel.witness : BayesianLinearModel where
  prior_var := 1
  data_precision := 1
  prior_var_pos := by norm_num
  data_precision_pos := by norm_num

namespace BayesianLinearModel

/-- Posterior precision = prior precision + data precision = 1/h + n. -/
noncomputable def posteriorPrecision (m : BayesianLinearModel) : ℝ :=
  1 / m.prior_var + m.data_precision

/-- Posterior precision is positive. -/
theorem posteriorPrecision_pos (m : BayesianLinearModel) :
    0 < m.posteriorPrecision := by
  unfold posteriorPrecision
  have := m.prior_var_pos
  have := m.data_precision_pos
  positivity

/-- Posterior variance = 1 / posterior precision = 1 / (1/h + n). -/
noncomputable def posteriorVariance (m : BayesianLinearModel) : ℝ :=
  1 / m.posteriorPrecision

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem posteriorVariance_at_zero_denominator_is_junk (m : BayesianLinearModel)
    (hzero : m.posteriorPrecision = 0) :
    posteriorVariance m = 0 := by
  unfold posteriorVariance
  rw [hzero, div_zero]


/-- Posterior variance is positive. -/
theorem posteriorVariance_pos (m : BayesianLinearModel) :
    0 < m.posteriorVariance := by
  unfold posteriorVariance
  exact div_pos one_pos m.posteriorPrecision_pos

/-- Posterior mean = posterior_variance × data_precision × observation.
    This is the standard Bayesian update: posterior mean is a precision-weighted
    combination of prior mean (0) and data (n × y), divided by total precision. -/
noncomputable def posteriorMean (m : BayesianLinearModel) (y : ℝ) : ℝ :=
  m.posteriorVariance * m.data_precision * y

/-- The shrinkage factor applied to the observation y in the posterior mean.
    shrinkageFactor = posteriorVariance × data_precision = n / (1/h + n). -/
noncomputable def shrinkageFactor (m : BayesianLinearModel) : ℝ :=
  m.posteriorVariance * m.data_precision

/-- The posterior mean factors as shrinkageFactor × y. -/
theorem posteriorMean_eq_shrinkage_mul (m : BayesianLinearModel) (y : ℝ) :
    m.posteriorMean y = m.shrinkageFactor * y := by
  unfold posteriorMean shrinkageFactor
  ring

/-- **Key identity:** posteriorVariance = h / (1 + n·h).
    Proof: 1/(1/h + n) = 1/((1 + n·h)/h) = h/(1 + n·h). -/
theorem posteriorVariance_eq (m : BayesianLinearModel) :
    m.posteriorVariance = m.prior_var / (1 + m.data_precision * m.prior_var) := by
  unfold posteriorVariance posteriorPrecision
  have hh : m.prior_var ≠ 0 := ne_of_gt m.prior_var_pos
  have hdenom : 1 + m.data_precision * m.prior_var > 0 := by
    have := m.prior_var_pos; have := m.data_precision_pos; positivity
  rw [div_add' _ _ _ hh]
  field_simp

/-- **Key identity:** shrinkageFactor = n·h / (n·h + 1).
    This is the algebraic derivation from the Bayesian model:
    shrinkage = posteriorVariance × n = (h/(1 + n·h)) × n = n·h/(1 + n·h). -/
theorem shrinkageFactor_eq (m : BayesianLinearModel) :
    m.shrinkageFactor =
      m.data_precision * m.prior_var /
        (m.data_precision * m.prior_var + 1) := by
  unfold shrinkageFactor
  rw [m.posteriorVariance_eq]
  have hh : m.prior_var ≠ 0 := ne_of_gt m.prior_var_pos
  have hdenom : 1 + m.data_precision * m.prior_var > 0 := by
    have := m.prior_var_pos; have := m.data_precision_pos; positivity
  have hdenom_ne : (1 + m.data_precision * m.prior_var) ≠ 0 := ne_of_gt hdenom
  field_simp
  ring

end BayesianLinearModel

/-- **Posterior mean under Gaussian prior.**
    β̂_Bayes = (n × Σ_LD + σ²_β⁻¹ × I)⁻¹ × n × Σ_LD × β̂_OLS
    For a single SNP: β̂ = β̂_OLS × n × h / (n × h + 1)
    where h = σ²_β / σ²_ε is the per-SNP heritability. -/
noncomputable def gaussianPosteriorShrinkage (n h : ℝ) : ℝ :=
  n * h / (n * h + 1)

/-- **gaussianPosteriorShrinkage at its junk point, named.** The divisor `n * h + 1` vanishes
when the sample size times the prior precision is minus one. A negative precision is
inadmissible, so this is a caller error, and it is returned as `0`: complete shrinkage to the
prior, a perfectly ordinary posterior weight. Consumers must exclude it by hypothesis. -/
theorem gaussianPosteriorShrinkage_cancelling_precision_is_junk :
    gaussianPosteriorShrinkage 1 (-1) = 0 := by
  unfold gaussianPosteriorShrinkage
  norm_num

/-- **Connection theorem:** The shrinkage factor derived from the Bayesian
    linear model is exactly `gaussianPosteriorShrinkage n h`, deriving that
    formula from first principles rather than positing it. -/
theorem BayesianLinearModel.shrinkageFactor_eq_gaussianPosteriorShrinkage
    (m : BayesianLinearModel) :
    m.shrinkageFactor =
      gaussianPosteriorShrinkage m.data_precision m.prior_var := by
  rw [m.shrinkageFactor_eq]
  unfold gaussianPosteriorShrinkage
  ring

/-- Shrinkage factor is in [0, 1). -/
theorem gaussian_shrinkage_in_unit (n h : ℝ)
    (h_n : 0 < n) (h_h : 0 < h) :
    0 ≤ gaussianPosteriorShrinkage n h ∧
      gaussianPosteriorShrinkage n h < 1 := by
  unfold gaussianPosteriorShrinkage
  constructor
  · exact div_nonneg (mul_nonneg (le_of_lt h_n) (le_of_lt h_h)) (by positivity)
  · rw [div_lt_one (by positivity)]
    linarith

/-- **Shrinkage increases with the compound parameter `n * h`.**

The posterior sees the sample size and the per-SNP heritability only through their product,
so raising either one is the same move.  The two single-parameter statements below are this
fact; stated separately, each carried its own copy of the same division argument. -/
theorem shrinkage_strictMono_product (n₁ h₁ n₂ h₂ : ℝ)
    (h_pos : 0 < n₁ * h₁) (h_more : n₁ * h₁ < n₂ * h₂) :
    gaussianPosteriorShrinkage n₁ h₁ < gaussianPosteriorShrinkage n₂ h₂ := by
  unfold gaussianPosteriorShrinkage
  have hd₁ : 0 < n₁ * h₁ + 1 := by linarith
  have hd₂ : 0 < n₂ * h₂ + 1 := by linarith
  rw [div_lt_div_iff₀ hd₁ hd₂]
  nlinarith

/-- **Shrinkage increases with sample size.** More data → less shrinkage. -/
theorem shrinkage_increases_with_n (h : ℝ) (n₁ n₂ : ℝ)
    (h_h : 0 < h) (h_n₁ : 0 < n₁)
    (h_more : n₁ < n₂) :
    gaussianPosteriorShrinkage n₁ h < gaussianPosteriorShrinkage n₂ h :=
  shrinkage_strictMono_product n₁ h n₂ h (by positivity) (by nlinarith)

/-- **Shrinkage increases with per-SNP heritability.**
    SNPs with larger effects are shrunk less. -/
theorem shrinkage_increases_with_h (n : ℝ) (h₁ h₂ : ℝ)
    (h_n : 0 < n) (h_h₁ : 0 < h₁)
    (h_more : h₁ < h₂) :
    gaussianPosteriorShrinkage n h₁ < gaussianPosteriorShrinkage n h₂ :=
  shrinkage_strictMono_product n h₁ n h₂ (by positivity) (by nlinarith)

/-- **James-Stein shrinkage MSE.**
    For estimating β with observation β̂_OLS ~ N(β, σ²), consider the
    linear shrinkage estimator β̂(λ) = λ·β̂_OLS. Its MSE decomposes as:
      MSE(λ) = λ²·σ² + (1-λ)²·β²
    where the first term is the (scaled) variance and the second is
    the squared bias from shrinking toward zero. -/
noncomputable def jamesSteinMSE (lam σ_sq β_sq : ℝ) : ℝ :=
  lam ^ 2 * σ_sq + (1 - lam) ^ 2 * β_sq

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem jamesSteinMSE_at_reference_point :
    jamesSteinMSE 1 1 1 = 1 := by
  norm_num [jamesSteinMSE]


/-- **OLS MSE is the no-shrinkage case.** MSE(1) = σ² (full weight on data). -/
theorem mse_ols_is_no_shrinkage (σ_sq β_sq : ℝ) :
    jamesSteinMSE 1 σ_sq β_sq = σ_sq := by
  unfold jamesSteinMSE; ring

/-- **Optimal shrinkage factor.**
    Minimizing MSE(λ) = λ²σ² + (1-λ)²β² over λ by taking the derivative
    and setting to zero: 2λσ² - 2(1-λ)β² = 0 ⟹ λ(σ²+β²) = β²
    ⟹ λ* = β²/(σ²+β²). -/
noncomputable def optimalShrinkage (σ_sq β_sq : ℝ) : ℝ :=
  β_sq / (σ_sq + β_sq)

/-- **The posterior shrinkage is `Core.share`, and it is the Wiener weight.**

`share a b` is `a / (a + b)`, so this is `share β_sq σ_sq`: the signal's share of the total.
`Spectral.wienerWeight noise s` is `s / (s + noise)`, the same share with the arguments
named for a denoising problem instead of a Bayesian one. They are one map, found by
`semantic_duplicates.py` agreeing at every sampled point, and they are one OBJECT -- the
optimal linear shrinkage and the Wiener filter are the same estimator under two
literatures' names.

Both names are kept. Which arguments a caller has in hand differs -- a prior variance and a
noise variance here, a signal and a noise level there -- and a single name would read wrong
in one of the two places. What is joined is the shape, so an edit to the share convention
cannot reach one and miss the other. -/
theorem optimalShrinkage_eq_share (σ_sq β_sq : ℝ) :
    optimalShrinkage σ_sq β_sq = Descent.Core.share β_sq σ_sq := by
  -- Not `rfl`: this body's denominator is `σ² + β²` and the kernel's is
  -- `β² + σ²`. The same number, and not the same term.
  unfold optimalShrinkage Descent.Core.share
  ring

/-- **optimalShrinkage where its denominator vanishes, named.** The guard `σ_sq + β_sq` is zero at
`σ_sq = 0`, `β_sq = 0`. Lean returns `0` there rather than the value the modelled quantity
takes, and no type error marks the point. Consumers must require `σ_sq + β_sq ≠ 0`. -/
theorem optimalShrinkage_at_sq0sq0_is_junk :
    optimalShrinkage 0 0 = 0 := by
  unfold optimalShrinkage
  norm_num

/-- **Optimal shrinkage is in (0,1) for positive parameters.** -/
theorem optimal_shrinkage_in_unit (σ_sq β_sq : ℝ)
    (h_σ : 0 < σ_sq) (h_β : 0 < β_sq) :
    0 < optimalShrinkage σ_sq β_sq ∧ optimalShrinkage σ_sq β_sq < 1 := by
  unfold optimalShrinkage
  constructor
  · exact div_pos h_β (by linarith)
  · rw [div_lt_one (by linarith : 0 < σ_sq + β_sq)]; linarith

/-- **Bayesian shrinkage reduces MSE compared to OLS (James-Stein).**
    We show MSE(λ*) < MSE(1) = σ² for λ* = β²/(σ²+β²).

    Key identity: MSE(λ*) = σ²·β²/(σ²+β²).
    Then σ²·β²/(σ²+β²) < σ² ⟺ β² < σ²+β² ⟺ 0 < σ².

    Proof strategy: We show that for any λ ∈ (0,1), we have
    MSE(λ) = MSE(1) - (2λ - λ²)·σ² + (1-λ)²·β²·... We instead
    show the result directly: MSE(λ) < σ² when λ ∈ (0,1) and β² > 0,
    by expanding and using nlinarith. -/
theorem bayesian_shrinkage_reduces_mse
    (σ_sq β_sq : ℝ)
    (h_σ : 0 < σ_sq) (h_β : 0 < β_sq) :
    jamesSteinMSE (optimalShrinkage σ_sq β_sq) σ_sq β_sq <
      jamesSteinMSE 1 σ_sq β_sq := by
  rw [mse_ols_is_no_shrinkage]
  unfold jamesSteinMSE optimalShrinkage
  -- Goal: (β²/(σ²+β²))² · σ² + (1 - β²/(σ²+β²))² · β² < σ²
  -- We use: 1 - β²/(σ²+β²) = σ²/(σ²+β²)
  -- So LHS = β⁴σ²/(σ²+β²)² + σ⁴β²/(σ²+β²)² = σ²β²(β²+σ²)/(σ²+β²)² = σ²β²/(σ²+β²)
  -- Then σ²β²/(σ²+β²) < σ² ⟺ β² < σ²+β² ⟺ 0 < σ². ✓
  have h_sum : 0 < σ_sq + β_sq := by linarith
  have h_sum_ne : (σ_sq + β_sq) ≠ 0 := ne_of_gt h_sum
  have h1 : 1 - β_sq / (σ_sq + β_sq) = σ_sq / (σ_sq + β_sq) := by
    field_simp [h_sum_ne]
    ring
  rw [h1]
  field_simp [h_sum_ne]
  nlinarith [h_σ, h_β]

end BayesianShrinkage


/-!
## LD Reference Panel Mismatch

Bayesian methods require an LD reference panel. When this doesn't
match the GWAS sample or target population, performance degrades.
-/

section LDReferenceMismatch

/-- **Shrinkage function for a single SNP.**
    f(σ) = σ/(σ+τ) maps the LD diagonal entry to the shrinkage factor.
    This is the key quantity affected by LD mismatch. -/
noncomputable def snpShrinkage (σ τ : ℝ) : ℝ :=
  σ / (σ + τ)

/-- **snpShrinkage where its denominator vanishes, named.** The guard `σ + τ` is zero at `σ = 0`, `τ
= 0`. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point. Consumers must require `σ + τ ≠ 0`. -/
theorem snpShrinkage_at_00_is_junk :
    snpShrinkage 0 0 = 0 := by
  unfold snpShrinkage
  norm_num

/-- **LD mismatch bias bound from mean value theorem.**
    For the shrinkage function f(σ) = σ/(σ+τ), we have
    f'(σ) = τ/(σ+τ)². Since σ > 0 and τ > 0, we get (σ+τ)² > τ²,
    so f'(σ) < 1/τ. By the mean value theorem:
    |f(σ_ref) - f(σ_true)| ≤ (1/τ) · |σ_ref - σ_true|.

    This shows the bias from LD mismatch is proportional to the
    LD matrix perturbation, with constant 1/τ (inverse regularization). -/
theorem ld_mismatch_bias_proportional
    (σ_true σ_ref τ : ℝ)
    (h_true : 0 < σ_true) (h_ref : 0 < σ_ref) (h_τ : 0 < τ) :
    |snpShrinkage σ_ref τ - snpShrinkage σ_true τ| ≤
      |σ_ref - σ_true| / τ := by
  unfold snpShrinkage
  -- f(σ₂) - f(σ₁) = σ₂/(σ₂+τ) - σ₁/(σ₁+τ)
  --               = (σ₂(σ₁+τ) - σ₁(σ₂+τ)) / ((σ₂+τ)(σ₁+τ))
  --               = τ(σ₂ - σ₁) / ((σ₂+τ)(σ₁+τ))
  -- |f(σ₂)-f(σ₁)| = τ|σ₂-σ₁| / ((σ₂+τ)(σ₁+τ))
  -- Since σ₁+τ > τ and σ₂+τ > τ, denominator > τ², so result ≤ |σ₂-σ₁|/τ
  have h_d1 : 0 < σ_true + τ := by linarith
  have h_d2 : 0 < σ_ref + τ := by linarith
  rw [div_sub_div _ _ (ne_of_gt h_d2) (ne_of_gt h_d1)]
  have h_num : σ_ref * (σ_true + τ) - (σ_ref + τ) * σ_true = τ * (σ_ref - σ_true) := by ring
  rw [h_num, abs_div, abs_mul, abs_of_pos h_τ, abs_of_pos (mul_pos h_d2 h_d1)]
  rw [div_le_div_iff₀ (mul_pos h_d2 h_d1) h_τ]
  have h_den_bound : τ * τ ≤ (σ_ref + τ) * (σ_true + τ) := by
    nlinarith
  nlinarith [abs_nonneg (σ_ref - σ_true), h_den_bound]

/-- **The expression `c·Fst·σ/τ` is positive and homogeneous of degree one in `Fst`.**

    That is the whole content, and the name now says so. Previously
    `cross_ancestry_ld_bias`, documented as establishing "that cross-ancestry bias is
    positive and scales with Fst" by way of `ld_mismatch_bias_proportional`. It does no
    such thing: `snpShrinkage` never appears in the statement, so nothing links this
    arithmetic to the shrinkage bias that `ld_mismatch_bias_proportional` actually bounds.
    The identification of `c·Fst·σ` with the cross-population LD perturbation `|σ_ref −
    σ_true|` is a modelling posit made in prose only.

    The second conjunct is strengthened rather than restated: the docstring claimed
    "doubling Fst doubles the bias bound" while the statement proved only the strict
    inequality `bound(fst) < bound(2·fst)`, which is compatible with any growth at all.
    The equality is what "doubles" means and it is what is proved. -/
theorem ld_bias_bound_pos_and_doubles_with_fst
    (σ τ c fst : ℝ)
    (h_σ : 0 < σ) (h_τ : 0 < τ)
    (h_c : 0 < c) (h_fst : 0 < fst) :
    0 < c * fst * σ / τ ∧
    c * (2 * fst) * σ / τ = 2 * (c * fst * σ / τ) := by
  refine ⟨div_pos (by positivity) h_τ, by ring⟩

/-- **In the additive bias model, a positive Fst offset strictly increases bias.**

    Previously `in_sample_ld_optimal`, "Using LD reference from the same population as GWAS
    minimizes bias". Optimality is a statement about a minimum over a set of reference
    panels; no set of panels is quantified over here, so no optimality is proved. What is
    proved is that the posited expression `base_bias + c·fst` is larger at `fst > 0` than
    at `fst = 0`.

    Two smaller repairs. The conclusion was `≤` while the docstring said "strictly
    exceeds"; it is now `<`, which is what the positive hypotheses give. And
    `h_base_nn : 0 ≤ base_bias` was an unused hypothesis of the misleading kind — it made
    the statement look like it was about a magnitude, when the inequality holds for any
    `base_bias` whatsoever. It is gone. -/
theorem cross_population_bias_gt_base_bias_of_positive_fst
    (base_bias c fst : ℝ)
    (h_c_pos : 0 < c) (h_fst_pos : 0 < fst) :
    base_bias < base_bias + c * fst := by
  linarith [mul_pos h_c_pos h_fst_pos]

/-- **The bias model is strictly monotone in its middle factor.**

Both statements below posit a bias of the form `c · x · fst` and vary `x`: the attenuation
factor of a mixed reference panel in one, the count of correlated SNPs in the other.  The
inequality is the same one, and naming it says so. -/
theorem scaled_bias_strictMono (c fst x y : ℝ)
    (h_c : 0 < c) (h_fst : 0 < fst) (h_lt : x < y) :
    c * x * fst < c * y * fst := by
  have h_cf : 0 < c * fst := mul_pos h_c h_fst
  nlinarith

/-- **Multi-ancestry LD reference reduces cross-population bias.**
    A reference panel combining multiple ancestries has intermediate LD
    that partially matches each population.  If single-ancestry bias
    is c · fst and multi-ancestry bias is c · α · fst where α ∈ (0,1)
    is the attenuation from partial ancestry matching, then
    multi-ancestry bias < single-ancestry bias.

    The attenuation factor `α < 1` is posited, not derived: nothing here shows that mixing
    reference panels attenuates rather than amplifies bias. Given that posit the conclusion
    is the strict inequality. A `≤` conclusion would be weaker than the headline claims,
    and it also holds at `α = 1`, that is under no attenuation at all.

    `α > 0` is part of the modelled range of an attenuation factor, but the inequality does
    not need it, so it is not a hypothesis here. -/
theorem multi_ancestry_reference_reduces_bias
    (c fst α : ℝ)
    (h_c : 0 < c) (h_fst : 0 < fst)
    (h_α_lt : α < 1) :
    c * α * fst < c * fst := by
  simpa using scaled_bias_strictMono c fst α 1 h_c h_fst h_α_lt

/-- **LD mismatch is worse for long-range LD regions.**
    Regions with long-range LD (e.g., MHC) are more affected by
    LD reference mismatch because the LD structure is more population-specific.
    Model: bias in a region = c · n_correlated_snps · fst.  Long-range LD
    regions have more correlated SNPs, so the bias is larger.

    A nonnegative SNP count is part of the modelled range, but the inequality follows from
    the comparison alone, so it is not a hypothesis here. -/
theorem long_range_ld_worse_mismatch
    (c fst n_short n_long : ℝ)
    (h_c : 0 < c) (h_fst : 0 < fst)
    (h_more_snps : n_short < n_long) :
    c * n_short * fst < c * n_long * fst :=
  scaled_bias_strictMono c fst n_short n_long h_c h_fst h_more_snps

end LDReferenceMismatch


/-!
## Prior Specification and Portability

The choice of prior in Bayesian PGS affects portability because
genetic architecture may differ across populations.
-/

section PriorSpecification

/-- **Spike-and-slab prior allows variable sparsity.**
    A proportion π of SNPs are causal with effects from a slab distribution,
    and (1-π) are null.

    Regime: the spike is an exact point mass at ZERO, which is what lets the
    null component drop out of the variance entirely. A spike with any width
    would contribute `(1-π)·σ_spike²` and this body has no room for it -- see
    `PolygenicArchitecture.spikeAndSlabVariance`, which carries that term.

    Empirical status: **VALIDATED** (`simcov/battery_bulk44.py`, `group_a`).
    6×10⁶ draws from the two COMPONENTS -- a point mass at zero with weight
    `1-π` and a Gaussian slab with weight `π` -- with the realised variance
    measured. The body is never used to generate anything, so what is on trial
    is the combination rule. Worst cell 1.23 sems at 0.21% relative.

    Power: `π` and the slab sd are swept in OPPOSITE directions -- (0.5, 1.0),
    (0.1, 2.0), (0.02, 3.0), (0.8, 0.5) -- so the product is on trial rather
    than either factor. Leaving the slab sd unsquared is FALSIFIED at 578 sems
    (100% relative) and dropping the mixture weight at 28316 sems (4904%).
    Control: the counted slab fraction recovers `π` on the same draws.

    The error bar is inflated threefold over the normal formula for a variance,
    because a spike-and-slab is heavy-tailed at small `π` and the normal sem
    understates its own scatter. That correction matters here: it is what turned
    an earlier reading of the sibling `spikeAndSlabVariance` from a spurious
    10.6-sem falsification into the noise it actually was.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk44.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_a).
    MATCH at worst 0.78 sems (0.22% relative); the unsquared slab sd is FALSIFIED at 495
    sems and the dropped mixture weight at 3818 sems (4904% relative). The across-block
    error bar is inflated threefold, as before.
    -/
noncomputable def spikeAndSlabPriorVariance (π σ_slab : ℝ) : ℝ :=
  π * σ_slab ^ 2

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem spikeAndSlabPriorVariance_at_reference_point :
    spikeAndSlabPriorVariance 1 1 = 1 := by
  norm_num [spikeAndSlabPriorVariance]


/-- Spike-and-slab variance is nonneg. -/
theorem spike_slab_variance_nonneg (π σ_slab : ℝ)
    (h_π : 0 ≤ π) :
    0 ≤ spikeAndSlabPriorVariance π σ_slab := by
  unfold spikeAndSlabPriorVariance
  exact mul_nonneg h_π (sq_nonneg _)

/-- **Misspecification excess risk.**
    The excess MSE from using a Gaussian prior when the true architecture
    is spike-and-slab with causal proportion π. The excess comes from:
    (a) overshrinking the π·M causal SNPs: each loses ~ (1-π)²·σ²_β of signal
    (b) undershrinking the (1-π)·M null SNPs: each gains ~ π²·σ²_β of noise
    Total excess risk per SNP = π·(1-π)²·σ²_β + (1-π)·π²·σ²_β
                               = π·(1-π)·σ²_β·((1-π) + π)
                               = π·(1-π)·σ²_β -/
noncomputable def misspecExcessRisk (π σ_β_sq : ℝ) : ℝ :=
  π * (1 - π) * σ_β_sq

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem misspecExcessRisk_at_reference_point :
    misspecExcessRisk (1 / 4) 2 = 3 / 8 := by
  norm_num [misspecExcessRisk]


/-- **Excess risk is nonneg for valid parameters.** -/
theorem misspec_excess_risk_nonneg (π σ_β_sq : ℝ)
    (h_π_pos : 0 ≤ π) (h_π_lt : π ≤ 1) (h_σ : 0 ≤ σ_β_sq) :
    0 ≤ misspecExcessRisk π σ_β_sq := by
  unfold misspecExcessRisk
  apply mul_nonneg
  · apply mul_nonneg h_π_pos; linarith
  · exact h_σ

/-- **Prior misspecification hurts sparse traits more.**
    The excess risk π·(1-π)·σ²_β is maximized at π=1/2 and decreases
    toward π=1. For two traits with π_sparse < π_poly (both < 1/2),
    the sparser trait has MORE excess risk because (1-π) is larger.
    More precisely, if both π values are in (0, 1/2], then
    misspecExcessRisk is increasing on this interval (derivative
    (1-2π)·σ²_β > 0 when π < 1/2).

    We prove: for π_sparse < π_poly < 1/2, the excess risk gap
    is proportional to (π_poly - π_sparse). -/
theorem prior_misspec_worse_for_sparse
    (σ_β_sq π_sparse π_poly : ℝ)
    (h_σ : 0 < σ_β_sq)
    (h_sparse_lt_half : π_sparse < 1/2)
    (h_poly_lt_half : π_poly ≤ 1/2)
    (h_sparser : π_sparse < π_poly) :
    misspecExcessRisk π_sparse σ_β_sq < misspecExcessRisk π_poly σ_β_sq := by
  unfold misspecExcessRisk
  -- Need: π_s·(1-π_s)·σ² < π_p·(1-π_p)·σ²
  -- Equiv: π_s·(1-π_s) < π_p·(1-π_p)  (since σ² > 0)
  -- f(π) = π(1-π) is increasing on [0, 1/2] since f'(π) = 1-2π > 0
  -- So π_s < π_p ≤ 1/2 ⟹ f(π_s) < f(π_p)
  have key : π_sparse * (1 - π_sparse) < π_poly * (1 - π_poly) := by nlinarith
  nlinarith

/-- **Portability-prior interaction via Bayes risk.**
    For a polygenic trait (π close to 1), the Gaussian prior is nearly
    correct: excess risk = π(1-π)σ² ≈ 0 since 1-π ≈ 0.
    For a sparse trait (π small), excess risk = π(1-π)σ² ≈ πσ².

    The portability gap between spike-and-slab (correct prior) and
    Gaussian (misspecified) is captured by misspecExcessRisk.
    We show that for a sparse trait with small π and a polygenic trait
    with large π, the sparse trait's misspec penalty exceeds the
    polygenic trait's, provided the sparse trait is near the peak
    of the excess risk curve (π < 1/2) and the polygenic trait is
    past it (π > 1/2).

    More specifically: for π_poly > 1/2 > π_sparse, if
    π_sparse·(1-π_sparse) > π_poly·(1-π_poly), then the sparse
    trait suffers more from prior misspecification. This holds when
    π_poly > 1 - π_sparse (i.e., π_poly is "at least as far above 1/2
    as π_sparse is below it"). -/
theorem portability_prior_interaction
    (σ_β_sq π_sparse π_poly : ℝ)
    (h_σ : 0 < σ_β_sq)
    (h_sparse_lt : π_sparse < 1/2)
    (h_poly_gt : 1/2 < π_poly)
    (h_far_enough : 1 - π_sparse < π_poly) :
    misspecExcessRisk π_poly σ_β_sq < misspecExcessRisk π_sparse σ_β_sq := by
  unfold misspecExcessRisk
  -- Need: π_p·(1-π_p) < π_s·(1-π_s)
  -- Equivalently: π_p - π_p² < π_s - π_s²
  -- i.e.: (π_p - π_s) < π_p² - π_s² = (π_p - π_s)(π_p + π_s)
  -- Since π_p > π_s (from h_far_enough and h_sparse_lt: π_p > 1-π_s > 1/2 > π_s),
  -- we can divide by (π_p - π_s) > 0 to get: 1 < π_p + π_s,
  -- which is equivalent to 1 - π_s < π_p, i.e., h_far_enough.
  have h_sp_lt_pp : π_sparse < π_poly := by linarith
  have key : π_poly * (1 - π_poly) < π_sparse * (1 - π_sparse) := by nlinarith
  nlinarith

/-- **Distinct causal fractions give distinct spike-and-slab prior variances at unit slab
    variance.** `π ↦ π · 1²` is injective; that is the entire content.

    Previously `empirical_bayes_population_specific`, whose docstring concluded that "the
    prior learned in EUR may not suit AFR". That is a claim about estimation from data and
    about transfer between populations. Neither an estimator nor a transfer criterion
    appears in the statement, which is a one-line injectivity fact about a product. -/
theorem spikeAndSlabPriorVariance_ne_of_pi_ne
    (π_eur π_afr : ℝ)
    (h_diff : π_eur ≠ π_afr) :
    spikeAndSlabPriorVariance π_eur 1 ≠ spikeAndSlabPriorVariance π_afr 1 := by
  unfold spikeAndSlabPriorVariance
  simpa using h_diff

end PriorSpecification


/-!
## Posterior Predictive Distribution

The posterior predictive distribution for a new individual's phenotype
given their genotype and the GWAS data.
-/

section PosteriorPredictive

/-- **Posterior predictive variance.**
    Var(Y_new | data) = Var(Y | β̂) + g' Var(β | data) g
    where g is the genotype vector. The second term is the estimation
    uncertainty. -/
noncomputable def posteriorPredictiveVariance
    (residual_var estimation_var : ℝ) : ℝ :=
  Descent.Core.sum residual_var estimation_var

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem posteriorPredictiveVariance_at_reference_point :
    posteriorPredictiveVariance (1 / 2) (1 / 2) = 1 := by
  unfold posteriorPredictiveVariance Descent.Core.sum
  norm_num

/-- **Removing the estimation variance leaves the residual variance.** The two sources of
predictive uncertainty are separable, which is what licenses reporting them apart; a body that
combined them any other way would not admit this decomposition. -/
theorem posteriorPredictiveVariance_sub_estimation (residual_var estimation_var : ℝ) :
    posteriorPredictiveVariance residual_var estimation_var - estimation_var = residual_var := by
  unfold posteriorPredictiveVariance Descent.Core.sum
  ring

/-- Posterior predictive variance ≥ residual variance. -/
theorem posterior_predictive_wider_than_residual
    (residual_var estimation_var : ℝ)
    (h_est : 0 ≤ estimation_var) :
    residual_var ≤ posteriorPredictiveVariance residual_var estimation_var := by
  unfold posteriorPredictiveVariance Descent.Core.sum
  linarith

/-- **Estimation variance decreases with sample size.**
    As GWAS n → ∞, Var(β | data) → 0 and posterior predictive
    converges to the plug-in prediction interval.
    Model: estimation variance ∝ σ²/(n·h²), so larger n gives smaller variance.
    For n₁ < n₂, est_var(n₂) = est_var(n₁) · (n₁/n₂) < est_var(n₁). -/
theorem estimation_variance_decreases_with_n
    (σ_sq h_sq n₁ n₂ : ℝ)
    (h_σ : 0 < σ_sq) (h_hsq : 0 < h_sq)
    (h_n₁ : 0 < n₁)
    (h_more : n₁ < n₂) :
    σ_sq / (n₂ * h_sq) < σ_sq / (n₁ * h_sq) := by
  apply div_lt_div_of_pos_left h_σ (mul_pos h_n₁ h_hsq)
  exact mul_lt_mul_of_pos_right h_more h_hsq

/-- **Cross-population posterior predictive is wider.**
    In the target population, both residual variance and estimation
    variance are larger → wider posterior predictive intervals. -/
theorem cross_population_posterior_wider
    (resid_s resid_t est_s est_t : ℝ)
    (h_resid : resid_s ≤ resid_t)
    (h_est : est_s ≤ est_t) :
    posteriorPredictiveVariance resid_s est_s ≤
      posteriorPredictiveVariance resid_t est_t := by
  unfold posteriorPredictiveVariance Descent.Core.sum
  linarith


end PosteriorPredictive


/-!
## PRS-CS Specific Theory

PRS-CS uses a continuous shrinkage (CS) prior with global-local
structure: β_j ~ N(0, σ²_j), σ²_j ~ g(σ²_j | φ), φ ~ p(φ).
-/

section PRSCS

/-- **Global shrinkage parameter φ controls overall sparsity.**
    Small φ → more shrinkage (sparser model).
    Large φ → less shrinkage (denser model).
    The effective number of nonzero coefficients is approximately
    n_eff ≈ M · φ/(1+φ) where M is total SNPs. Since φ/(1+φ)
    is monotonically increasing in φ, larger φ yields more nonzero effects.

    What is proved is only the monotonicity of `M · φ/(1+φ)` in `φ`. The identification of
    that expression with an effective number of nonzero coefficients is an approximation
    asserted in this docstring and derived nowhere, so the theorem carries no information
    about sparsity beyond the arithmetic. -/
theorem global_shrinkage_controls_sparsity
    (M φ₁ φ₂ : ℝ)
    (hM : 0 < M) (hφ₁ : 0 < φ₁)
    (h_more_phi : φ₁ < φ₂) :
    M * (φ₁ / (1 + φ₁)) < M * (φ₂ / (1 + φ₂)) := by
  apply mul_lt_mul_of_pos_left _ hM
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Under an assumed noise ordering, the modelled C+T accuracy does not exceed the
    modelled PRS-CS accuracy.**

    Previously `prs_cs_dominates_ct`, "PRS-CS uniformly dominates C+T in in-sample
    prediction". Nothing is uniform and nothing is dominated: `h_cs_better : noise_cs ≤
    noise_ct` is the assumption that PRS-CS is the better method, supplied by hand, and the
    theorem propagates it through the posited accuracy formulae `h²·(p/M)·(1−noise_CT)` and
    `h²·(1−noise_CS)`. Those formulae are written down here, not derived from any estimator.
    The claim "the advantage is largest for polygenic traits" appears nowhere in the
    statement and is dropped.

    What the theorem does contribute is that the two modelled advantages — using all `M`
    SNPs rather than `p`, and the assumed lower noise — compose in the same direction
    rather than cancelling.

    Four hypotheses are marked unused rather than left to the linter: the accuracy
    comparison needs neither `p > 0`, nor that either noise level is nonnegative, nor that
    the PRS-CS noise is below one. They describe the modelled ranges of the quantities and
    are kept for that reason, but they carry no weight in the proof. -/
theorem ct_r2_le_prs_cs_r2_of_assumed_noise_ordering
    (h_sq p M noise_ct noise_cs : ℝ)
    (h_hsq : 0 < h_sq) (h_M : 0 < M)
    (h_pM : p ≤ M)
    (h_noise_ct1 : noise_ct < 1)
    (h_cs_better : noise_cs ≤ noise_ct) :
    h_sq * (p / M) * (1 - noise_ct) ≤ h_sq * (1 - noise_cs) := by
  have h_pM_ratio : p / M ≤ 1 := by rwa [div_le_one (by linarith : (0:ℝ) < M)]
  have h1 : (1 - noise_ct) ≤ (1 - noise_cs) := by linarith
  have h2 : p / M * (1 - noise_ct) ≤ 1 * (1 - noise_cs) := by
    apply mul_le_mul h_pM_ratio h1 (by linarith) (by linarith)
  nlinarith


/-- **PRS-CS with mismatched LD can be worse than C+T.**
    If the LD reference panel is from a very different population,
    PRS-CS can actually perform worse than C+T because C+T
    is more robust to LD misspecification.
    Model: PRS-CS accuracy = base_r2 - mismatch_penalty.
    C+T accuracy = base_r2 · (p/M) but is unaffected by LD mismatch.
    When mismatch_penalty > base_r2 · (1 - p/M), PRS-CS is worse.

    The reversal is a rearrangement of `h_penalty_large`, which is the modelling assumption
    that the mismatch penalty exceeds the SNP-count advantage; the theorem does not
    establish that any real LD mismatch is that large. Positivity of the base `R²`, of the
    SNP count and of the penalty gap are not hypotheses here: the rearrangement holds
    without them. -/
theorem ld_mismatch_can_reverse_advantage
    (base_r2 p M mismatch_penalty : ℝ)
    (h_M : 0 < M)
    (h_pM : p ≤ M)
    (h_penalty_large : base_r2 * (1 - p / M) < mismatch_penalty) :
    base_r2 - mismatch_penalty < base_r2 * (p / M) := by
  have : p / M ≤ 1 := by rwa [div_le_one (by linarith : (0:ℝ) < M)]
  nlinarith

end PRSCS


/-!
## Multi-Ancestry Bayesian Methods

Methods that combine GWAS from multiple ancestries in a Bayesian
framework to improve portability.
-/

section MultiAncestryBayesian

/-- **`rg²` lies in `[0,1]` whenever `rg` does.**

    Previously `info_borrowing_proportional_to_rg`, "Genetic correlation determines
    information borrowing". It introduced a second variable `info_gain` and pinned it with `h_relation : info_gain = rg ^ 2`, then proved bounds on it. Naming a quantity and
    supplying its definition as a hypothesis adds nothing to the bound on `rg ^ 2`, and it
    makes an unproved modelling identification — that squared genetic correlation *is* the
    fraction of information shared — look like part of the theorem. -/
theorem rg_sq_mem_unit_interval
    (rg : ℝ) (h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1) :
    0 ≤ rg ^ 2 ∧ rg ^ 2 ≤ 1 :=
  ⟨sq_nonneg _, by nlinarith [sq_nonneg rg]⟩

/-- **Effective sample size in multi-ancestry setting.**
    n_eff = n_target + Σ_k (rg_k² × n_k × h_k / h_target)
    where h_k is heritability in population k.

    Empirical status: **VALIDATED** (`simcov/battery_bulk40b.py`, `group_f`). The
    FALSIFIED marker this line used to carry described the SUPERSEDED body
    `n_target + rg²·n_other`, and was left in place when the correction landed, so the
    definition read as falsified while the body it named no longer existed. That is a
    stale mark, not a wrong body: the measurement below is of the exact contributed
    precision, and the exact contributed precision is what this body now computes.
    The four cells the old form missed by 2.3%, 5.0%, 12% and 31% are reproduced by
    this one, because the residual was the omitted scatter term rather than a scale
    factor. The falsification is retained below as history, which is what it is.

    Power: the measured `N_eff` spans `6449` to `12079` across the design, a factor
    of 1.9, and every competitor is refuted on the same cells -- `n_t + rg·n_o` by 227
    sems, `n_t + n_o` by 282, `n_t` alone by 261.

    Convention, stated because the whole question turns on it: `N_eff` is the posterior
    PRECISION of the target effect minus the prior precision, i.e. the precision the data
    contributed. Under that reading target data alone contributes exactly `n_target`, which
    is what makes the quantity comparable with `n_target` and `n_other` at all, and it is
    checked as the positive control (0.34 sems).

    A genetic correlation below one means the other ancestry's effect is `rg` times the
    target's PLUS INDEPENDENT SCATTER of variance `(1-rg²)τ²`, with `τ²` the effect prior
    variance. The borrowed estimate therefore carries `(1-rg²)τ² + 1/n_other` of noise, not
    `1/n_other`, and the exact contributed precision is

      n_target + rg² / ((1 - rg²)·τ² + 1/n_other)

    which reduces to this body only when `n_other·τ² ≪ 1`. 6×10⁵ replicates, `n_other·τ²`
    swept across 1:

      n_t    n_o     rg    n_o·τ²   this body   measured N_eff   sems   off
      6000   6000   0.7     0.18      8940           8735        2.7    2.3%
      3000  12000   0.9     0.36     12719          12079        7.7    5.0%
      3000  12000   0.6     0.36      7329           6449       12.1   12.0%
      3000  12000   0.9     3.60     12722           8775      178.6   31.0%

    The error grows monotonically with `n_other·τ²`, which is the signature of the missing
    scatter term rather than of a scale factor. Every competitor is refuted too --
    `n_t + rg·n_o` by 227 sems, `n_t + n_o` by 282, `n_t` alone by 261 -- so the body is the
    best of the four and still wrong outside its regime.

    `GeneticArchitectureDiscovery.multiTraitEffectiveSampleSize` is the SAME formula and
    inherits this. Its MATCH in `simcov/battery_bulk23.py` came from a design in which the
    other trait's effect was set to EXACTLY `rg` times the target's, with no scatter, under
    which `n1 + rg² n2` is an algebraic identity for the inverse-variance combination and no
    data could have rejected it. A per-SNP polygenic `τ² = h²/M` is far below `1/n`, so the
    old body's regime is the usual one -- but it was a condition, and it was not written
    down.

    CORRECTED, rather than annotated. The body is now the exact contributed precision and
    the old form is its `n_other · priorVariance → 0` limit, recovered by
    `multiAncestryEffectiveN_smallPrior`. At `rg = 1` it gives `n_target + n_other`, which
    is pooling and is what the measurement's positive control checks; at `rg = 0` it gives
    `n_target`, which is no borrowing. The measured cells the old body missed by 2.3%, 5.0%,
    12% and 31% are reproduced by this one, because the residual WAS the omitted scatter
    term rather than a scale factor. -/
noncomputable def multiAncestryEffectiveN
    (n_target rg n_other priorVariance : ℝ) : ℝ :=
  n_target + rg ^ 2 / ((1 - rg ^ 2) * priorVariance + 1 / n_other)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem multiAncestryEffectiveN_at_reference_point :
    multiAncestryEffectiveN (1 / 2) (1 / 2) (1 / 2) 0 = 5 / 8 := by
  unfold multiAncestryEffectiveN
  norm_num

/-- **The old body is this one's vanishing-prior limit.** `n_target + rg²·n_other` is what
the exact contributed precision becomes when the other ancestry's effect scatter
`(1-rg²)·priorVariance` is negligible beside its sampling error `1/n_other`. Stating it as a
theorem is what makes the correction auditable: the previous form is not discarded, it is
located, and a caller in the polygenic regime where `n·τ² ≪ 1` may still use it knowingly. -/
theorem multiAncestryEffectiveN_smallPrior
    (n_target rg n_other : ℝ) (h_no : n_other ≠ 0) :
    multiAncestryEffectiveN n_target rg n_other 0 = n_target + rg ^ 2 * n_other := by
  unfold multiAncestryEffectiveN
  field_simp
  ring

/-- **At perfect genetic correlation the two studies simply pool.** This is the endpoint the
old body could not reach: `n_target + rg²·n_other` gives `n_target + n_other` at `rg = 1` only
by coincidence of the limit, whereas here it is exact at every `priorVariance`, because a
perfectly correlated ancestry carries no scatter to be penalised for. -/
theorem multiAncestryEffectiveN_at_perfect_correlation
    (n_target n_other : ℝ) (h_no : n_other ≠ 0) :
    multiAncestryEffectiveN n_target 1 n_other = fun _ ↦ n_target + n_other := by
  funext priorVariance
  unfold multiAncestryEffectiveN
  field_simp
  ring

/-- **The Gaussian shrinkage factor is monotone in the multi-ancestry effective sample
    size.**

    Previously `multi_ancestry_at_least_as_good`, "Multi-ancestry PGS is at least as good
    as single-ancestry. With well-specified models, combining data cannot hurt." Two
    things were being conflated. `gaussianPosteriorShrinkage n h = n·h/(n·h+1)` is the
    factor by which the posterior mean shrinks the observation toward zero; the docstring
    read it as `R²`. They are the same expression, but the identification of shrinkage
    factor with predictive `R²` is a modelling step taken nowhere in this file, so the
    theorem does not say a PGS is more accurate — it says a shrinkage factor is larger.

    `_h_rg` is deliberately unused: because the formula uses `rg ^ 2`, the sign of the
    genetic correlation is irrelevant, so the monotonicity holds for negative `rg` too.

    The bound on `rg` and the nonnegative `priorVariance` are what the corrected
    effective-sample-size body needs: its denominator `(1-rg²)·priorVariance + 1/n_other` is
    positive exactly when the scatter term cannot go negative, and `|rg| ≤ 1` is what makes
    it so. The old body needed no such hypothesis because it had no denominator -- which is
    the same reason it was wrong. -/
theorem gaussianPosteriorShrinkage_mono_in_multiAncestryEffectiveN
    (n_target rg n_other priorVariance h_sq : ℝ)
    (h_nt : 0 < n_target) (_h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1) (h_no : 0 < n_other)
    (h_pv : 0 ≤ priorVariance) (h_hsq : 0 < h_sq) :
    gaussianPosteriorShrinkage n_target h_sq ≤
      gaussianPosteriorShrinkage
        (multiAncestryEffectiveN n_target rg n_other priorVariance) h_sq := by
  have h_den : 0 < (1 - rg ^ 2) * priorVariance + 1 / n_other := by
    have : 0 ≤ (1 - rg ^ 2) * priorVariance :=
      mul_nonneg (by nlinarith) h_pv
    have : 0 < 1 / n_other := by positivity
    linarith
  have h_gain : 0 ≤ rg ^ 2 / ((1 - rg ^ 2) * priorVariance + 1 / n_other) :=
    div_nonneg (sq_nonneg rg) h_den.le
  unfold gaussianPosteriorShrinkage multiAncestryEffectiveN
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h_gain, h_hsq.le]

/-- Multi-ancestry effective N ≥ single-ancestry N.

    `_h_rg` is deliberately unused, for the same reason as above: the contribution enters
    squared. -/
theorem multi_ancestry_effective_n_ge
    (n_target rg n_other priorVariance : ℝ)
    (_h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1) (h_n : 0 < n_other)
    (h_pv : 0 ≤ priorVariance) :
    n_target ≤ multiAncestryEffectiveN n_target rg n_other priorVariance := by
  have h_den : 0 < (1 - rg ^ 2) * priorVariance + 1 / n_other := by
    have h1 : 0 ≤ (1 - rg ^ 2) * priorVariance :=
      mul_nonneg (by nlinarith) h_pv
    have h2 : 0 < 1 / n_other := by positivity
    linarith
  unfold multiAncestryEffectiveN
  have := div_nonneg (sq_nonneg rg) h_den.le
  linarith

/-- **Diminishing returns from adding more EUR samples.**
    When the target is AFR and we already have large EUR GWAS,
    additional EUR samples help less than adding AFR samples.
    The marginal gain from adding Δn EUR samples to the AFR effective
    sample size is rg² · Δn (attenuated by genetic correlation),
    while adding Δn AFR samples contributes Δn directly.
    Since rg < 1, EUR samples contribute less. -/
theorem diminishing_returns_from_majority
    (Δn rg : ℝ)
    (h_Δn : 0 < Δn) (h_rg_pos : 0 < rg) (h_rg_lt : rg < 1) :
    rg ^ 2 * Δn < Δn := by
  have h_sq_lt : rg ^ 2 < 1 := by nlinarith [sq_abs rg, sq_nonneg rg]
  nlinarith

end MultiAncestryBayesian

end Descent.Portability
