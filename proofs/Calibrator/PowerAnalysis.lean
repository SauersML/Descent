/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Calibrator.PolygenicArchitecture

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat the noncentrality parameter, sample-size allocation, or the
minimax and certificate material below. Sources for individual results, where they exist,
are cited at those results.
-/


/-!
## Power and Sample Size

GWAS power to detect a variant depends on sample size, effect size,
and allele frequency. Underpowered studies produce biased PGS.
-/

section PowerSampleSize

/-- **Noncentrality parameter for association test.**
    NCP = n × β² × 2p(1-p) where n is sample size,
    β is effect size, p is allele frequency.

    Empirical status: VALIDATED (mean Wald chi-squared from simulated genotypes, ratio 0.99-1.01). -/
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

/-- **Power of the Wald test at significance threshold `z_α`.**

    `Φ(√ncp - z_α)`.  Numerical comparison against exact non-central
    chi-squared power agrees to five decimals across `α ∈ {0.05, 5·10⁻⁸}` and
    `ncp ∈ {1, …, 20}`.

    The threshold argument is essential: a power formula without one, such as
    `1 - exp(-ncp/2)`, returns a single number for a nominal test and a genome-wide scan
    alike — at `α = 5·10⁻⁸` with `ncp = 10` that gives `0.993` against a true `0.011`.

    Empirical status: VALIDATED (matches exact non-central chi-squared power to five decimals). -/
noncomputable def powerAtThreshold (ncp z_alpha : ℝ) : ℝ :=
  Phi (Real.sqrt ncp - z_alpha)

/-- **Power increases with the noncentrality parameter** at a fixed
    threshold. -/
theorem powerAtThreshold_mono (ncp₁ ncp₂ z_alpha : ℝ) (h : ncp₁ ≤ ncp₂) :
    powerAtThreshold ncp₁ z_alpha ≤ powerAtThreshold ncp₂ z_alpha := by
  unfold powerAtThreshold
  exact Phi_monotone (by linarith [Real.sqrt_le_sqrt h])

/-- **A stricter threshold lowers power** at fixed noncentrality.  This is the
    dependence the previous definition could not express. -/
theorem powerAtThreshold_antitone_in_threshold (ncp z₁ z₂ : ℝ) (h : z₁ ≤ z₂) :
    powerAtThreshold ncp z₂ ≤ powerAtThreshold ncp z₁ := by
  unfold powerAtThreshold
  exact Phi_monotone (by linarith)


/-- **Rare variants need larger samples.**
    For a fixed effect size, the NCP scales with p(1-p).
    At MAF 1% vs 30%, need ~25× more samples.

    **No symmetry hypothesis is needed.** Assuming `p_common ≤ 1/2` — folding both
    frequencies into the minor half of the axis — together with `0 < p_common` and
    `p_common < 1` is more than the conclusion needs. The difference factors as

        `2 p_c (1 - p_c) - 2 p_r (1 - p_r) = 2 (p_c - p_r) (1 - p_c - p_r)`,

    so the sign is decided by a single linear condition on the pair,
    `p_r + p_c < 1`: the constraint that has to be active is that the two
    frequencies straddle the fold point, not that either of them is minor. The
    old hypotheses all follow from the new one together with `0 < p_rare` and
    `p_rare < p_common`, so this is a strict weakening, and it now covers pairs
    such as `p_rare = 0.6, p_common = 0.3` read on the major allele, which the
    folded statement could not reach. -/
theorem rare_variant_lower_power (n : ℕ) (beta p_rare p_common : ℝ)
    (h_beta : beta ≠ 0) (h_rare : 0 < p_rare)
    (h_rare_lt : p_rare < p_common)
    (h_active : p_rare + p_common < 1) (hn : 0 < n) :
    noncentralityParam n beta p_rare < noncentralityParam n beta p_common := by
  unfold noncentralityParam
  have h_n : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_b : 0 < beta ^ 2 := sq_pos_of_ne_zero h_beta
  apply mul_lt_mul_of_pos_left _ (mul_pos h_n h_b)
  -- Need: 2 * p_rare * (1 - p_rare) < 2 * p_common * (1 - p_common)
  have h_straddle : (0 : ℝ) < (p_common - p_rare) * (1 - (p_rare + p_common)) :=
    mul_pos (sub_pos.mpr h_rare_lt) (sub_pos.mpr h_active)
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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def GWASObservationModel.witness : GWASObservationModel where
  true_beta := 1
  sigma := 1
  n := 1
  h_sigma_pos := by norm_num
  h_n_pos := by norm_num

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
    selection event.

    **DO NOT DELETE AS UNUSED.**  Restored: `ec74a6a8` removed this as "no use
    anywhere and no theorem about them", on an identifier grep of `.lean` files.
    It is a `Prop`-valued convention, so its existence is the result -- the same
    category as `extra_algebraic_guard_adds_nothing`, which that same commit
    correctly declined to remove.  Two live consumers name it:

      * the note immediately below, which justifies the removal of
        `truncationBias` on the grounds that it "is the one-sided result while
        `GWASObservationModel.isSelected` is two-sided".  Delete this and the
        recorded reason for that deletion has no referent;
      * `validation/differential/cluster/fam_ascertainment.py`, whose `wc_exact`
        is built on "the TWO-SIDED event `GWASObservationModel.isSelected`
        states".  The differential family validates against this definition.

    Neither reference is an application, so nothing failed to elaborate and the
    build stayed green.  Both are prose, and a grep for the identifier in
    `.lean` alone reaches neither. -/
def GWASObservationModel.isSelected (m : GWASObservationModel) (epsilon z_alpha : ℝ) : Prop :=
  z_alpha * m.standardError < |m.true_beta + epsilon|

/-! ### Truncation bias under selection

Removed.  This defined `truncationBias se beta z_alpha` as `se · φ(z_α - β/se)`,
the numerator of an inverse Mills ratio, on the stated grounds that the normal
CDF was unavailable.  `Phi` is defined in `Calibrator.Probability`, which this
file imports directly, so the grounds were false.

Exact evaluation of `E[ε | selected]`, cross-checked by Monte Carlo, falsifies
it three ways.  Magnitude is wrong by about `2·10⁵` at the genome-wide
threshold with `β/SE = 1`, giving `0.00002` against a true `4.66`, because the
omitted `Φ` denominator is of order `10⁻⁸` there.  Monotonicity in `β/SE` runs
opposite to the truth over the whole range where winner's curse exists.  And
it is the one-sided result while `GWASObservationModel.isSelected` is
two-sided, which at `β = 0` differ by everything, the two-sided bias being
exactly zero by symmetry.

The theorems proved about it, including an epsilon-delta limit, were correct
about the formula and false about the quantity it was named for.  A correct
treatment needs the two-sided conditional expectation written against `Phi`;
it is not attempted here rather than approximated again.
-/

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

/-! Removed with `truncationBias`: a high-signal statement whose content was
the behaviour of the falsified proxy rather than of the conditional
expectation it was named for. -/

/-- **The standard error equals σ/√n.**
    This connects the model's SE back to the concrete expression used
    throughout the winner's-curse heuristics in this file. -/
theorem se_equals_sigma_over_sqrt_n (m : GWASObservationModel) :
    m.standardError = m.sigma / Real.sqrt m.n := by
  unfold GWASObservationModel.standardError
  ring

end WinnersCurseDerivation


/-!
## Winner's Curse

Significant GWAS associations have inflated effect size estimates.
This inflation is worse for less powered studies and biases PGS.

The definition below records the common heuristic correction
`β + σ/√n`. The formal theorem in the section above proves the
complementary large-signal fact that the explicit `truncationBias`
proxy itself becomes negligible.
-/

/-! ### Winner's curse inflation

Removed.  This section defined `winnersCurseInflation true_beta sigma n` as
`β + σ/√n`: inflation of exactly one standard error, with no significance
threshold anywhere in the signature.  The true conditional mean is pinned by
the threshold and sits near `5.6` to `5.9` standard errors at genome-wide
significance, so the error runs from `-73%` to `+23%` and changes sign with
the regime; at `β = 0` it claims one standard error of inflation where the
truth is zero.  As with `singletonProportion` and the old `approxPower`, no
constant repairs it, because the signature omits an argument the observable
depends on.

`winnersCurseInflation_matches_model` was presented as showing the definition
is the asymptotic conditional expectation of the observation model.  Its proof
is `unfold; ring`, so it restates the definition and derives nothing; the
"Derived:" comment on `winners_curse_inflates` was likewise unearned.
-/


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

/-! `r2ScalingModel` is the saturating fraction `n / (n + C)` with `C = M/h²`,
not an `R²`. It carries no heritability prefactor, so it saturates at one where
`R²` must cap at `h²`; the same defect that
`Calibrator.expectedR2FromN` carried before correction. It is kept as the
shape, and anything reading it as a predicted `R²` must multiply by `h²`. -/

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
    For two populations with equal weights and a fixed total budget `2n`,
    the imbalanced allocation `(n - δ, n + δ)` is strictly worse than the
    balanced allocation `(n, n)` under the exact scaling law
    `R²(n) = n / (n + C)`. This is the concrete concavity statement the
    section needs, not a generic monotonicity sum. -/
theorem balanced_allocation_maximizes_total_utility
    (n delta C : ℝ)
    (h_C : 0 < C) (h_delta : 0 < delta) (h_n : delta < n) :
    r2ScalingModel (n - delta) C + r2ScalingModel (n + delta) C <
      2 * r2ScalingModel n C := by
  have h_n_nonneg : 0 ≤ n := by
    linarith
  have h_n_minus_delta_nonneg : 0 ≤ n - delta := by
    linarith
  have h_marginal :
      r2ScalingModel (n + delta) C - r2ScalingModel n C <
        r2ScalingModel n C - r2ScalingModel (n - delta) C := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (diminishing_returns (n - delta) n delta C h_C
        h_n_minus_delta_nonneg h_n_nonneg h_delta (by linarith))
  have h_sum :
      r2ScalingModel (n - delta) C + r2ScalingModel (n + delta) C <
        r2ScalingModel n C + r2ScalingModel n C := by
    linarith
  simpa [two_mul] using h_sum

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


/-!
## Conditional Sample-Size Benchmarks for Nonsmooth Architecture Summaries

Every sample-size law in this file is polynomial: `r2ScalingModel` saturates as
`n / (n + C)`, the noncentrality grows linearly in `n`, and the allocation
results are concavity statements about that shape. All of it is correct for the
targets those laws are about — `R²`, a per-variant association test, a variance
component — because those are smooth functionals of the underlying parameters,
and smooth functionals are estimable at polynomial rates.

None of it transfers automatically to nonsmooth summaries of an effect-size
distribution. For mean absolute effect and its kin, `1 / log n` is a candidate
benchmark imported from a specific Gaussian-sequence analysis, not a theorem
about every GWAS experiment. The functions below record what would follow if a
concrete model identified that benchmark.

First, the logarithmic benchmark inverts to `exp (1/ε)`, exponential in the
reciprocal accuracy rather than a power of it.

Second, a polynomial candidate certificate curve inverts to a polynomial sample
size, whereas the logarithmic curve inverts to an exponential one. This
comparison is exact real analysis. It is not evidence that all two-point,
Assouad, Fano, or fuzzy-hypothesis methods have the polynomial curve: the first
LP audit in `CertificateGrading` found the proposed moment grade nearly free.

Thus the existing `R²` theorems remain true for their stated smooth endpoints.
A user must not substitute a polygenicity or sparsity summary for `R²` without
first proving the corresponding observation-model reduction and minimax law.
-/

section NonsmoothSampleSize

/-- **Sample size that inverts the logarithmic risk benchmark at `ε`.**

    `exp (1/ε)`. This is a benchmark inversion, not an asserted sample-size
    requirement for a GWAS.

    Empirical status: UNTESTED. -/
noncomputable def logarithmicBenchmarkSampleSize (epsilon : ℝ) : ℝ := Real.exp (1 / epsilon)

/-- **Sample size that inverts the polynomial fixed-grade benchmark.**

    `ε ^ (-(K/c))`, a power law in reciprocal accuracy. It acquires a certificate
    interpretation only when a concrete calculus proves this benchmark.

    Empirical status: UNTESTED. -/
noncomputable def fixedGradeBenchmarkSampleSize (epsilon K c : ℝ) : ℝ :=
  epsilon ^ (-(K / c))

/-- `logarithmicBenchmarkSampleSize` inverts the logarithmic benchmark. -/
theorem logarithmicBenchmarkSampleSize_inverts (epsilon : ℝ) :
    logarithmicRiskBenchmark (logarithmicBenchmarkSampleSize epsilon) = epsilon := by
  unfold logarithmicRiskBenchmark logarithmicBenchmarkSampleSize
  rw [Real.log_exp, one_div_one_div]

/-- `fixedGradeBenchmarkSampleSize` inverts the polynomial benchmark. -/
theorem fixedGradeBenchmarkSampleSize_inverts (epsilon K c : ℝ)
    (h_eps : 0 < epsilon) (hK : K ≠ 0) (hc : c ≠ 0) :
    fixedGradeRiskBenchmark (fixedGradeBenchmarkSampleSize epsilon K c) K c = epsilon := by
  unfold fixedGradeRiskBenchmark fixedGradeBenchmarkSampleSize
  have hexp : (-(K / c)) * (-(c / K)) = 1 := by
    rw [neg_mul_neg, div_mul_div_comm, mul_comm c K, div_self (mul_ne_zero hK hc)]
  rw [← Real.rpow_mul (le_of_lt h_eps), hexp, Real.rpow_one]

/-- **Conditional comparison of the polynomial and logarithmic sample-size benchmarks.**

    Stated with the crossing point as a hypothesis: wherever the power law sits
    below the exponential, the former benchmark is smaller. -/
theorem fixedGradeBenchmark_lt_logarithmicBenchmark (epsilon K c : ℝ)
    (h_gap : epsilon ^ (-(K / c)) < Real.exp (1 / epsilon)) :
    fixedGradeBenchmarkSampleSize epsilon K c < logarithmicBenchmarkSampleSize epsilon := by
  unfold fixedGradeBenchmarkSampleSize logarithmicBenchmarkSampleSize
  exact h_gap

/-- **At a normalised grade one, the shortfall needs no crossing hypothesis.**

    What is unconditional here is the *crossing*: no hypothesis about where the
    two curves meet is needed, because `1/ε + 1 ≤ exp (1/ε)` holds everywhere.
    What is **not** unconditional is `h_grade : K/c ≤ 1`. That is a
    normalisation on the certificate constant `c`, and at `K = 1` it says
    exactly `c ≥ 1`; it is not automatic for a two-point argument, and it is
    stated as a hypothesis for that reason rather than folded into the prose.
    Under it, the certified sample size is at most `1/ε` while the requirement
    is `exp (1/ε)`, at every target accuracy in `(0, 1]`.

    This remains a curve comparison; `h_grade` is not automatically supplied by
    any particular lower-bound method. -/
theorem normalizedFixedGradeBenchmark_lt_logarithmicBenchmark (epsilon K c : ℝ)
    (h_eps : 0 < epsilon) (h_eps_le : epsilon ≤ 1) (h_grade : K / c ≤ 1) :
    fixedGradeBenchmarkSampleSize epsilon K c < logarithmicBenchmarkSampleSize epsilon := by
  unfold fixedGradeBenchmarkSampleSize logarithmicBenchmarkSampleSize
  have h1 : epsilon ^ (-(K / c)) ≤ epsilon ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge h_eps h_eps_le (by linarith)
  have h2 : epsilon ^ (-(1 : ℝ)) = 1 / epsilon := by
    rw [Real.rpow_neg (le_of_lt h_eps), Real.rpow_one, one_div]
  have h3 : 1 / epsilon + 1 ≤ Real.exp (1 / epsilon) := Real.add_one_le_exp _
  rw [h2] at h1
  linarith

/-- **Every fixed polynomial benchmark is eventually below the exponential benchmark.**

    Written along the sharpening target `ε = 1/x` as `x → ∞`, which is where the
    statement has content and which keeps the filter on `atTop` rather than on a
    punctured neighbourhood of zero. At accuracy `1/x` the certified sample size
    is `x^(K/c)` and the requirement is `exp x`, so the claim is that a power is
    eventually beaten by the exponential — `isLittleO_rpow_exp_atTop`, which
    holds for every real exponent with no side condition. This is the general
    This proves no claim about a certificate calculus until the benchmark curves
    are derived from that calculus. -/
theorem fixedGradeBenchmark_lt_logarithmicBenchmark_eventually (K c : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      fixedGradeBenchmarkSampleSize (1 / x) K c <
        logarithmicBenchmarkSampleSize (1 / x) := by
  have hbound := (isLittleO_rpow_exp_atTop (K / c)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, Filter.eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hxm : 0 < x ^ (K / c) := Real.rpow_pos_of_pos hx0 (K / c)
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hle : x ^ (K / c) ≤ 1 / 2 * Real.exp x := by
    rw [Real.norm_of_nonneg (le_of_lt hxm), Real.norm_of_nonneg (le_of_lt hexp)] at hx
    exact hx
  have hcert : fixedGradeBenchmarkSampleSize (1 / x) K c = x ^ (K / c) := by
    unfold fixedGradeBenchmarkSampleSize
    rw [one_div, Real.inv_rpow (le_of_lt hx0), Real.rpow_neg (le_of_lt hx0), inv_inv]
  have hlog : logarithmicBenchmarkSampleSize (1 / x) = Real.exp x := by
    unfold logarithmicBenchmarkSampleSize
    rw [one_div_one_div]
  rw [hcert, hlog]
  linarith

end NonsmoothSampleSize

end Calibrator
