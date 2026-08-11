/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Ratios
import Descent.Layer

assert_below Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent.PopGen

/-!
# Shrinkage estimators

The James-Stein risk of a shrunk estimate, the shrinkage factor that minimises it, the
Gaussian posterior shrinkage, and the effective sample size that a multi-ancestry prior
buys.

None of it is about transport. Each is a fact about estimating one population's effects
from one population's data, and they sat in the portability chapter because the Bayesian
PGS methods that consume them were written there. That put a PopGen file in the position
of importing `Portability` in order to state an architecture theorem about shrinkage,
which is the layer order running backwards.
-/

/-- **Posterior mean under Gaussian prior.**
    β̂_Bayes = (n × Σ_LD + σ²_β⁻¹ × I)⁻¹ × n × Σ_LD × β̂_OLS
    For a single SNP: β̂ = β̂_OLS × n × h / (n × h + 1)
    where h = σ²_β / σ²_ε is the per-SNP heritability. -/
noncomputable def gaussianPosteriorShrinkage (n h : ℝ) : ℝ :=
  n * h / (n * h + 1)

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

    **THE HYPOTHESIS IS `|rg| ≤ 1`, AND IT WAS PREVIOUSLY WRITTEN AS A PAIR ONE HALF OF
    WHICH THE DOCSTRING CALLED UNUSED.** The signature carried `0 ≤ rg` and `rg ≤ 1`, with
    prose saying the first was deliberately unused because the formula squares `rg`, so the
    result held for negative `rg` too. The statement did not say that, and the proof did not
    have it either: what the denominator needs is `0 ≤ 1 - rg²`, `nlinarith` was reading
    BOTH bounds out of the context to get it, and `rg ≤ 1` alone is satisfied by `rg = -5`.
    So the claim lived only in the prose. It is now in the signature, where a reader and a
    tactic see the same thing.

    The bound on `rg` and the nonnegative `priorVariance` are what the corrected
    effective-sample-size body needs: its denominator `(1-rg²)·priorVariance + 1/n_other` is
    positive exactly when the scatter term cannot go negative, and `|rg| ≤ 1` is what makes
    it so. The old body needed no such hypothesis because it had no denominator -- which is
    the same reason it was wrong. -/
theorem gaussianPosteriorShrinkage_mono_in_multiAncestryEffectiveN
    (n_target rg n_other priorVariance h_sq : ℝ)
    (h_nt : 0 < n_target) (h_rg : |rg| ≤ 1) (h_no : 0 < n_other)
    (h_pv : 0 ≤ priorVariance) (h_hsq : 0 < h_sq) :
    gaussianPosteriorShrinkage n_target h_sq ≤
      gaussianPosteriorShrinkage
        (multiAncestryEffectiveN n_target rg n_other priorVariance) h_sq := by
  have h_bounds := abs_le.mp h_rg
  have h_sq_le : rg ^ 2 ≤ 1 := by nlinarith [h_bounds.1, h_bounds.2]
  have h_den : 0 < (1 - rg ^ 2) * priorVariance + 1 / n_other := by
    have : 0 ≤ (1 - rg ^ 2) * priorVariance :=
      mul_nonneg (by linarith) h_pv
    have : 0 < 1 / n_other := by positivity
    linarith
  have h_gain : 0 ≤ rg ^ 2 / ((1 - rg ^ 2) * priorVariance + 1 / n_other) :=
    div_nonneg (sq_nonneg rg) h_den.le
  unfold gaussianPosteriorShrinkage multiAncestryEffectiveN
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h_gain, h_hsq.le]

/-- Multi-ancestry effective N ≥ single-ancestry N.

    `|rg| ≤ 1` for the same reason as above, and it replaces the same pair: the contribution
    enters squared, so the sign of `rg` is irrelevant and its MAGNITUDE is not. -/
theorem multi_ancestry_effective_n_ge
    (n_target rg n_other priorVariance : ℝ)
    (h_rg : |rg| ≤ 1) (h_n : 0 < n_other)
    (h_pv : 0 ≤ priorVariance) :
    n_target ≤ multiAncestryEffectiveN n_target rg n_other priorVariance := by
  have h_bounds := abs_le.mp h_rg
  have h_sq_le : rg ^ 2 ≤ 1 := by nlinarith [h_bounds.1, h_bounds.2]
  have h_den : 0 < (1 - rg ^ 2) * priorVariance + 1 / n_other := by
    have h1 : 0 ≤ (1 - rg ^ 2) * priorVariance :=
      mul_nonneg (by linarith) h_pv
    have h2 : 0 < 1 / n_other := by positivity
    linarith
  unfold multiAncestryEffectiveN
  have := div_nonneg (sq_nonneg rg) h_den.le
  linarith

end Descent.PopGen
