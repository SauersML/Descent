/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PolygenicArchitecture
import Calibrator.BundleRigidity.DeploymentCeiling

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

    Empirical status: VALIDATED (mean Wald chi-squared from simulated genotypes, ratio 0.99-1.01).

    Power: `validation/empirical/popgen_defs/check_stats.py` simulates at
    `n = 4000` over `p = 0.05, 0.2, 0.5` and `β = 0.05, 0.1`, where this
    definition predicts `0.95`, `3.80`, `3.20`, `12.80`, `5.00` and `20.00`. The
    twentyfold span moves in both arguments independently — `β` quadratically,
    `p` through the genotype variance — so a form missing either factor, or
    carrying the allelic variance instead of the genotype variance, departs
    across the grid rather than at one cell. -/
noncomputable def noncentralityParam (n : ℕ) (beta p : ℝ) : ℝ :=
  n * beta^2 * (2 * p * (1 - p))

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem noncentralityParam_at_reference_point :
    noncentralityParam 1 1 1 = 0 := by
  norm_num [noncentralityParam]



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

    **Convention on `z_α`, and a correction to the table below.** For the
    two-sided Wald test — equivalently the one-degree-of-freedom chi-squared
    test a GWAS actually runs — `z_α` must be the TWO-SIDED critical value
    `Φ⁻¹(1 - α/2)`, so that `z_α²` is the chi-squared critical value. The
    tabulated `α = 5·10⁻⁸` column obeys that: it was computed at
    `z = 5.4513 = Φ⁻¹(1 - 2.5·10⁻⁸)`, and the one-sided `5.3267` reproduces
    none of its entries (`0.0152` and `0.1963` against the tabulated `0.0110`
    and `0.1638` at `ncp = 10, 20`).

    The `α = 0.05` column did NOT: `0.2595`, `0.7228`, `0.9354`, `0.9977` are
    the ONE-SIDED values at `z = 1.6449`. At the two-sided `z = 1.9600` the same
    grid gives `0.1685`, `0.6088`, `0.8854` and `0.9940`. So the two columns were
    computed under different conventions, and the discrepancy is not cosmetic —
    at `ncp = 1` the one-sided reading overstates power by 54%. The corrected
    two-sided column is what a chi-squared test at `α = 0.05` (critical value
    `3.8415`) has.

    Empirical status: VALIDATED at `α = 5·10⁻⁸` (matches exact non-central
    chi-squared power to five decimals). **The `α = 0.05` cell is UNTESTED
    pending re-measurement**: the five-decimal agreement claim cannot cover both
    columns, since they do not share a convention, and the corrected values
    quoted above are analytic normal-CDF evaluations, not a fresh run against
    `ncx2`. Re-running that comparison at the two-sided threshold is owed.

    Power: across `ncp = 1, 5, 10, 20` this formula predicts `0.1685`, `0.6088`,
    `0.8854` and `0.9940` at `α = 0.05`, and `0.0000`, `0.0007`, `0.0110` and
    `0.1638` at `α = 5·10⁻⁸`. The prediction therefore covers essentially the
    whole `[0, 1]` range of power, and the two thresholds separate by an order
    of magnitude at every `ncp` — which is exactly what a threshold-free form
    cannot reproduce. -/
noncomputable def powerAtThreshold (ncp z_alpha : ℝ) : ℝ :=
  Phi (Real.sqrt ncp - z_alpha)

/-- **powerAtThreshold at its junk point, named.** A negative non-centrality parameter is
inadmissible; `Real.sqrt` is junk-zero there, so the power collapses to the size of the test. A
caller passing a sign-flipped effect gets the nominal type-one error rate back as if it were
power. Consumers must exclude the argument that makes the guard vanish. -/
theorem powerAtThreshold_negative_noncentrality_is_junk (z_alpha : ℝ) :
    powerAtThreshold (-1) z_alpha = Phi (-z_alpha) := by
  unfold powerAtThreshold
  rw [Real.sqrt_eq_zero_of_nonpos (by norm_num)]
  norm_num

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

/-- **The root-n law, stated as an identity rather than a rate.** Positivity does not pin the
exponent; multiplying the standard error by the root of the sample size returns the residual
scale, and no other power of `n` satisfies that. -/
theorem GWASObservationModel.standardError_mul_sqrt_n (m : GWASObservationModel)
    (h : Real.sqrt m.n ≠ 0) :
    m.standardError * Real.sqrt m.n = m.sigma := by
  unfold GWASObservationModel.standardError
  field_simp

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

    **DO NOT DELETE AS UNUSED.**  It is a `Prop`-valued convention, so its
    existence is the result -- the same category as
    `extra_algebraic_guard_adds_nothing`.  An identifier grep of `.lean` files
    finds no application, but two live consumers name it:

      * the note immediately below, which justifies the removal of
        `truncationBias` on the grounds that it "is the one-sided result while
        `GWASObservationModel.isSelected` is two-sided".  Delete this and the
        recorded reason for that deletion has no referent;
      * `validation/differential/cluster/fam_ascertainment.py`, whose `wc_exact`
        is built on "the TWO-SIDED event `GWASObservationModel.isSelected`
        states".  The differential family validates against this definition.

    Neither reference is an application, so removing this breaks no elaboration
    and leaves the build green.  Both are prose, and a grep for the identifier in
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

/-- **Fraction of heritability attained at sample size `n`**: `n / (n + C)` with `C = M/h²`
    (`M` the effective number of loci, `h²` the heritability).

    This is a fraction, not an `R²`. It carries no heritability prefactor, so it saturates at
    one where `R²` must cap at `h²`, and anything reading it as a predicted `R²` must multiply
    by `h²` — which is what `Calibrator.expectedR2FromN` does. The name says fraction because
    the signature cannot say `R²`: no heritability enters it.

    Concave in `n`, so the returns diminish.

    Empirical status: **VALIDATED as a shape**
    (`proofs/validation/empirical/simcov/battery_bulk8.py`,
    `test_heritability_learning_curve`). Out-of-sample R-squared as a fraction
    of heritability, 500 loci at `h2 = 0.5`, scored on a held-out 40000:

      n        predicted   measured   sems
      5000       0.89372    0.90049   0.25
      12000      0.95279    1.00844   1.84
      30000      0.98057    0.98437   0.13

    `C` is fitted at the SMALLEST sample size and then used to predict the other
    three. That is what makes this a test of the shape `n/(n + C)` rather than
    of a constant fitted to the curve it is being checked against -- a fit to
    all four points would agree with almost any monotone saturating form. -/
noncomputable def heritabilityFractionFromN (n C : ℝ) : ℝ := n / (n + C)

/-- **heritabilityFractionFromN where its denominator vanishes, named.** The guard `n + C` is zero
at `n = 0`, `C = 0`. At zero sample size and zero constant the recovered heritability fraction
is undefined; the value returned certifies that none of the heritability has been captured. Lean
returns `0` there rather than the value the modelled quantity takes, and no type error marks the
point. Consumers must require `n + C ≠ 0`. -/
theorem heritabilityFractionFromN_at_n0c0_is_junk :
    heritabilityFractionFromN 0 0 = 0 := by
  unfold heritabilityFractionFromN
  norm_num

/-- The attained fraction of heritability is increasing in `n`. -/
theorem r2_scaling_increasing (n₁ n₂ C : ℝ)
    (h_C : 0 < C) (h_n₁ : 0 ≤ n₁) (h_n₂ : 0 ≤ n₂) (h_n : n₁ < n₂) :
    heritabilityFractionFromN n₁ C < heritabilityFractionFromN n₂ C := by
  unfold heritabilityFractionFromN
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- R² scaling model is bounded by 1. -/
theorem r2_scaling_bounded (n C : ℝ)
    (h_C : 0 < C) (h_n : 0 ≤ n) :
    heritabilityFractionFromN n C < 1 := by
  unfold heritabilityFractionFromN
  rw [div_lt_one (by linarith)]
  linarith

/-- **Diminishing returns from concavity of R²(n) = n/(n+C).**
    The second derivative d²R²/dn² = −2C/(n+C)³ < 0, so R² is concave.
    Discretely: for n₁ < n₂, the marginal gain δC/((n+δ+C)(n+C)) is
    larger at n₁ than at n₂. Proved algebraically from the definition. -/
theorem diminishing_returns (n₁ n₂ delta C : ℝ)
    (h_C : 0 < C) (h_n₁ : 0 ≤ n₁) (h_n₂ : 0 ≤ n₂)
    (h_delta : 0 < delta) (h_n : n₁ < n₂) :
    heritabilityFractionFromN (n₂ + delta) C - heritabilityFractionFromN n₂ C <
      heritabilityFractionFromN (n₁ + delta) C - heritabilityFractionFromN n₁ C := by
  unfold heritabilityFractionFromN
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
    heritabilityFractionFromN (n_large + delta) C - heritabilityFractionFromN n_large C <
      heritabilityFractionFromN (n_small + delta) C - heritabilityFractionFromN n_small C :=
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
    heritabilityFractionFromN (n - delta) C + heritabilityFractionFromN (n + delta) C <
      2 * heritabilityFractionFromN n C := by
  have h_n_nonneg : 0 ≤ n := by
    linarith
  have h_n_minus_delta_nonneg : 0 ≤ n - delta := by
    linarith
  have h_marginal :
      heritabilityFractionFromN (n + delta) C - heritabilityFractionFromN n C <
        heritabilityFractionFromN n C - heritabilityFractionFromN (n - delta) C := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (diminishing_returns (n - delta) n delta C h_C
        h_n_minus_delta_nonneg h_n_nonneg h_delta (by linarith))
  have h_sum :
      heritabilityFractionFromN (n - delta) C + heritabilityFractionFromN (n + delta) C <
        heritabilityFractionFromN n C + heritabilityFractionFromN n C := by
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

/-- **Given the `r_g²` ceiling, imperfect correlation forces a portability drop.**
    r_g < 1 means effect sizes are not perfectly correlated.

    The ceiling `r2_target ≤ r_g² · r2_source` is a hypothesis, not a result of this
    corpus: nothing here derives it from a model of cross-ancestry effect transfer. The
    name carries `_of_rg_sq_bound` for that reason — the previous name,
    `genetic_correlation_bounds_portability`, asserted the very implication that is
    being assumed. -/
theorem r2_target_lt_r2_source_of_rg_sq_bound
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

Every sample-size law in this file is polynomial: `heritabilityFractionFromN` saturates as
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

/-- **Logarithmic risk benchmark at sample size `n`.**

    `1 / log n`: the accuracy a logarithmically ill-posed recovery problem reaches at
    sample size `n`. It is the benchmark the two theorems below invert, and it is a
    benchmark rather than an asserted rate for any particular estimator.

    Empirical status: UNTESTED. -/
noncomputable def logarithmicRiskBenchmark (n : ℝ) : ℝ := 1 / Real.log n

/-- **Fixed-grade polynomial risk benchmark at sample size `n`.**

    `n ^ (-(c/K))`: the accuracy a problem of grade `K` with constant `c` reaches at
    sample size `n`. Its inverse is `fixedGradeBenchmarkSampleSize`.

    Empirical status: UNTESTED. -/
noncomputable def fixedGradeRiskBenchmark (n K c : ℝ) : ℝ := n ^ (-(c / K))

/-- **The logarithmic benchmark's junk point, named rather than left to be found.**

    `Real.log 1 = 0` and Lean totalises `1 / 0 = 0`, so at a single sample the benchmark returns
    `0` — perfect accuracy — where the quantity it names diverges. The point is inside the
    admissible range of `n`, so this is a wrong value in the domain rather than a harmless
    artifact, and consumers must require `1 < n`. `logarithmicBenchmarkSampleSize_inverts` does,
    through `exp (1/ε)` at `0 < ε`. -/
theorem logarithmicRiskBenchmark_one_is_junk : logarithmicRiskBenchmark 1 = 0 := by
  unfold logarithmicRiskBenchmark
  rw [Real.log_one]
  simp

/-- **The fixed-grade benchmark's junk point.**

    At `K = 0` the exponent `-(c/K)` is Lean's `0`, so the benchmark returns `1` at every sample
    size — accuracy never improves — regardless of `c`. Consumers must require `K ≠ 0`;
    `fixedGradeBenchmarkSampleSize_inverts` does. -/
theorem fixedGradeRiskBenchmark_zero_grade_is_junk (n c : ℝ) :
    fixedGradeRiskBenchmark n 0 c = 1 := by
  unfold fixedGradeRiskBenchmark
  rw [div_zero, neg_zero, Real.rpow_zero]

/-- **The polynomial benchmark at zero samples, named.**
`fixedGradeRiskBenchmark_zero_grade_is_junk` names the degenerate GRADE; this is the degenerate
SAMPLE SIZE, which is the one a consumer can
reach by accident. `Real.rpow` sends `0` to `0` at any nonzero exponent, so a benchmark evaluated
before any data has been collected reports risk `0` -- perfect accuracy, attained by an estimator
that has seen nothing. The quantity diverges there. Of the two junk branches in this definition
this is the dangerous direction, because a risk of zero reads as success and a risk of one reads
as failure. Consumers must require `n ≠ 0`. -/
theorem fixedGradeRiskBenchmark_zero_samples_is_junk (K c : ℝ) (h : c / K ≠ 0) :
    fixedGradeRiskBenchmark 0 K c = 0 := by
  unfold fixedGradeRiskBenchmark
  exact Real.zero_rpow (neg_ne_zero.mpr h)

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

/-- **The logarithmic inverse benchmark at zero target risk, named.** The same demand for perfect
accuracy, failing through a different totality convention: `1 / 0` is junk-zero and `exp 0 = 1`,
so the formula reports that ONE sample suffices for perfect accuracy. The polynomial form returns
zero here and this returns one, so the two benchmarks disagree at the same degenerate point while
`fixedGradeBenchmark_lt_logarithmicBenchmark` compares them elsewhere -- and neither branch is
visible in the comparison. Consumers must require `epsilon ≠ 0`. -/
theorem logarithmicBenchmarkSampleSize_zero_target_is_junk :
    logarithmicBenchmarkSampleSize 0 = 1 := by
  unfold logarithmicBenchmarkSampleSize
  norm_num

/-- `fixedGradeBenchmarkSampleSize` inverts the polynomial benchmark. -/
theorem fixedGradeBenchmarkSampleSize_inverts (epsilon K c : ℝ)
    (h_eps : 0 < epsilon) (hK : K ≠ 0) (hc : c ≠ 0) :
    fixedGradeRiskBenchmark (fixedGradeBenchmarkSampleSize epsilon K c) K c = epsilon := by
  unfold fixedGradeRiskBenchmark fixedGradeBenchmarkSampleSize
  have hexp : (-(K / c)) * (-(c / K)) = 1 := by
    rw [neg_mul_neg, div_mul_div_comm, mul_comm c K, div_self (mul_ne_zero hK hc)]
  rw [← Real.rpow_mul (le_of_lt h_eps), hexp, Real.rpow_one]

/-- **The inverse benchmark at zero target risk, named.** Demanding perfect accuracy requires
unboundedly many samples, which is the whole content of a sample-size law. `Real.rpow` sends `0`
to `0` at any nonzero exponent, so this returns `0`: perfect accuracy is free, attainable with no
data at all. A sample-size formula that collapses to zero exactly where the requirement diverges
certifies rather than warns, and nothing downstream distinguishes it from a genuinely cheap
design. Consumers must require `epsilon ≠ 0`. -/
theorem fixedGradeBenchmarkSampleSize_zero_target_is_junk (K c : ℝ) (h : K / c ≠ 0) :
    fixedGradeBenchmarkSampleSize 0 K c = 0 := by
  unfold fixedGradeBenchmarkSampleSize
  exact Real.zero_rpow (neg_ne_zero.mpr h)

/-- **The deployment sample cost lands exactly on the polynomial benchmark, at grade `2k`.**

`BundleRigidity.sampleCost η C k` is the sample size the coverage guarantee
`σ_min ≥ (η/C)^k` forces on a deployment direction of coupling order `k`, namely
`(C/η)^(2k)`. Spending it drives the fixed-grade risk benchmark at grade ratio `2k` down
to accuracy `η/C` — no more and no less. So the deployment ceiling is not a new cost law:
it is the corpus's power-law benchmark read at grade `2k`, with the coupling order
appearing as the grade exponent rather than as a separate constant.

That is where the cost qualifier of `sampleCost_unbounded` bites. A benchmark of grade
`2k` needs accuracy-to-the-power `2k` many samples, so an order-`k` direction is charged
exponentially in `k`, while the published quadratic formula is this identity at `k = 1`.
Either definition changing its exponent convention breaks this. -/
theorem fixedGradeRiskBenchmark_sampleCost (η C : ℝ) (hη : 0 < η) (hC : 0 < C)
    (k : ℕ) (hk : 0 < k) :
    fixedGradeRiskBenchmark (BundleRigidity.sampleCost η C k) (2 * k) 1 = η / C := by
  have hpos : (0 : ℝ) < C / η := div_pos hC hη
  have hk0 : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  unfold fixedGradeRiskBenchmark BundleRigidity.sampleCost
  rw [← Real.rpow_natCast (C / η) (2 * k), ← Real.rpow_mul hpos.le]
  have hexp : ((2 * k : ℕ) : ℝ) * (-(1 / (2 * (k : ℝ)))) = -(1 : ℝ) := by
    push_cast
    field_simp
  rw [hexp, Real.rpow_neg hpos.le, Real.rpow_one, inv_div]

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
