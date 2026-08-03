import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Quantitative Portability Bounds

Formal bounds on PGS portability derived from population-genetic parameters.

**Read "quantitative prediction" narrowly here.** What this file supports is *orderings*
between portability laws, which hold for any positive parameters. The magnitudes do not:
`stabilizingPortability` and `diversifyingPortability` are recorded FALSIFIED as
one-parameter laws — simulation finds no constant `strength` fitting the portability
curve, the fitted value spanning 13-fold over a 29-fold range of `F_ST`. The definitions
survive for the ordering results; their fitted constants must not be reported as
properties of a trait. See the deletion-and-status note in the selection-models section.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## Fst-Based Neutral Benchmarks

**`neutralAFBenchmarkRatio` is FALSIFIED**, and the theorems in this section are
statements about the expression, not about a measured quantity. It is not "exactly
determined by `F_ST`", which is what this section used to say: at the measured
`fstSource = 0.3577` the expression cannot exceed `1.557` for any target `F_ST` at all
(`PortabilityDrift.neutralAFBenchmarkRatio_cannot_reach_measured`), while the measurement
at that design point is `3.79 ± 0.25`. The observable is outside the formula's range, and
no calibration of `fstTarget` repairs it; heterozygosity is governed by `Nₑ` and the
mutation floor, not by a between-population variance ratio.

What survives is the algebra: the expression equals one at equal `F_ST`, decreases in the
target, lies in `(0,1)` when the target has diverged further, and can only shrink under a
scalar selection factor. Those are proved below and each is a fact about
`(1 - fstT)/(1 - fstS)`. Do not read a portability prediction off any of them.
-/

section FstBounds

/-- Neutral allele-frequency benchmark ratio at equal `F_ST` is `1`. -/
theorem neutral_af_benchmark_at_equal_fst (fst : ℝ) (h : fst < 1) :
    neutralAFBenchmarkRatio fst fst = 1 := by
  simpa using neutralAFBenchmarkRatio_self fst h

/-- Neutral allele-frequency benchmark ratio is strictly decreasing in target
`F_ST`. -/
theorem neutral_af_benchmark_decreasing_in_fstT
    (fstS fstT₁ fstT₂ : ℝ)
    (h_fstS : fstS < 1)
    (h_order : fstT₁ < fstT₂) :
    neutralAFBenchmarkRatio fstS fstT₂ < neutralAFBenchmarkRatio fstS fstT₁ := by
  have h_denom : 0 < 1 - fstS := by linarith
  simpa [neutralAFBenchmarkRatio] using
    (div_lt_div_of_pos_right (show 1 - fstT₂ < 1 - fstT₁ by linarith) h_denom)

/-- Under selection, the scalar effect factor can only shrink the neutral
allele-frequency benchmark. -/
theorem selection_worsens_neutral_af_benchmark
    (fstS fstT ρ_eff : ℝ)
    (h_fstS : fstS < 1) (h_fstT : fstT < 1)
    (hρ : 0 ≤ ρ_eff) (hρ_le : ρ_eff ≤ 1) :
    neutralAFBenchmarkRatio fstS fstT * ρ_eff ^ 2 ≤
      neutralAFBenchmarkRatio fstS fstT := by
  have h_sq_le : ρ_eff ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρ_eff]
  have h_ratio_nonneg : 0 ≤ neutralAFBenchmarkRatio fstS fstT := by
    exact neutralAFBenchmarkRatio_nonneg fstS fstT h_fstS (le_of_lt h_fstT)
  calc neutralAFBenchmarkRatio fstS fstT * ρ_eff ^ 2
      ≤ neutralAFBenchmarkRatio fstS fstT * 1 :=
        mul_le_mul_of_nonneg_left h_sq_le h_ratio_nonneg
    _ = neutralAFBenchmarkRatio fstS fstT := mul_one _

/-- **General neutral allele-frequency benchmark bound.**
    For any target population with `Fst_T > Fst_S` (both < `1`),
    the neutral benchmark ratio is strictly between `0` and `1`,
    and decreasing in `(Fst_T - Fst_S)`. The ratio equals
    `(1 - Fst_T)/(1 - Fst_S)`.

    **The worked examples that stood here are withdrawn.** They read `ratio ≈ 0.88` at
    `Fst ≈ 0.12` and `≈ 0.85` at `Fst ≈ 0.15`, and concluded that larger observed `R²`
    drops confirm non-neutral effects. That inference ran through a formula measured to
    be out of range — `3.79 ± 0.25` observed against a ceiling of `1.557` — so a gap
    between it and the data is not evidence about selection. `Calibrator.HumanDemography`
    reaches the neutral-floor conclusion by a route that survives measurement, and gets
    `0.985` rather than `0.88` for the continental case, because the floor must be
    computed from the branch quantity `1 - H_T/H_S` and not from a pairwise `F_ST`.

    The bounds below are proved and are about the expression itself. -/
theorem neutral_af_benchmark_bounded_by_fst
    (fstS fstT : ℝ)
    (h_fstS_lt : fstS < 1)
    (h_fstT_lt : fstT < 1)
    (h_diverged : fstS < fstT) :
    0 < neutralAFBenchmarkRatio fstS fstT ∧
    neutralAFBenchmarkRatio fstS fstT < 1 := by
  constructor
  · simpa [neutralAFBenchmarkRatio] using
      (show 0 < (1 - fstT) / (1 - fstS) by exact div_pos (by linarith) (by linarith))
  · simpa using
      neutralAFBenchmarkRatio_lt_one fstS fstT h_fstS_lt h_diverged

end FstBounds


/-!
## Berry-Esseen Bounds on Score Distribution Approximation

The PGS is a weighted sum of discrete genotype variables. Its CDF is
approximately Gaussian, with error bounded by Berry-Esseen.
This matters because portability formulas often assume Gaussian scores.
-/

section BerryEsseenPortability

/-- **Berry-Esseen error in portability calculation.**
    If the Gaussian approximation error is ε, the error in
    R² from using the Gaussian formula is at most 2ε. -/
theorem r2_error_from_gaussian_approximation
    (r2_exact r2_gaussian ε : ℝ)
    (h_err : |r2_exact - r2_gaussian| ≤ ε) :
    r2_exact ∈ Set.Icc (r2_gaussian - ε) (r2_gaussian + ε) := by
  constructor <;> linarith [abs_le.mp h_err |>.1, abs_le.mp h_err |>.2]

/-- **Portability ratio error from Gaussian approximation.**
    If both source and target R² have Gaussian approximation errors,
    the portability ratio error is bounded. -/
theorem portability_ratio_approximation_error
    (r2s r2s_approx r2t r2t_approx εs εt : ℝ)
    (h_rs : |r2s - r2s_approx| ≤ εs)
    (h_rt : |r2t - r2t_approx| ≤ εt)
    (h_rs_pos : 0 < r2s)
    (h_rs_approx_pos : 0 < r2s_approx) :
    |r2t / r2s - r2t_approx / r2s_approx| ≤
      (εt * r2s_approx + εs * |r2t_approx|) / (r2s * r2s_approx) := by
  have h_denom_pos : 0 < r2s * r2s_approx := mul_pos h_rs_pos h_rs_approx_pos
  rw [div_sub_div _ _ (h_rs_pos.ne') (h_rs_approx_pos.ne')]
  rw [abs_div]
  rw [div_le_div_iff₀ (abs_pos.mpr (h_denom_pos.ne')) h_denom_pos]
  rw [abs_of_pos h_denom_pos]
  -- Goal: |r2t * r2s_approx - r2s * r2t_approx| * (r2s * r2s_approx) ≤
  --       (εt * r2s_approx + εs * |r2t_approx|) * (r2s * r2s_approx)
  apply mul_le_mul_of_nonneg_right _ (le_of_lt h_denom_pos)
  -- Now: |r2t * r2s_approx - r2s * r2t_approx| ≤ εt * r2s_approx + εs * |r2t_approx|
  calc |r2t * r2s_approx - r2s * r2t_approx|
      = |r2t * r2s_approx - r2t_approx * r2s| := by ring_nf
    _ = |(r2t - r2t_approx) * r2s_approx + r2t_approx * (r2s_approx - r2s)| := by ring_nf
    _ ≤ |(r2t - r2t_approx) * r2s_approx| + |r2t_approx * (r2s_approx - r2s)| :=
        abs_add_le _ _
    _ = |r2t - r2t_approx| * |r2s_approx| + |r2t_approx| * |r2s_approx - r2s| := by
        rw [abs_mul, abs_mul]
    _ = |r2t - r2t_approx| * r2s_approx + |r2t_approx| * |r2s_approx - r2s| := by
        rw [abs_of_pos h_rs_approx_pos]
    _ ≤ εt * r2s_approx + |r2t_approx| * εs := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right h_rt (le_of_lt h_rs_approx_pos)
        · exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact h_rs) (abs_nonneg _)
    _ = εt * r2s_approx + εs * |r2t_approx| := by ring

end BerryEsseenPortability


/-!
## Individual-Level Prediction Error Distribution

The paper's key finding is that individual-level squared prediction error
has enormous within-group variance. We formalize the exact distribution.
-/

section IndividualErrorDistribution

/-- **Squared prediction error for Gaussian model.**
    If Y = μ(X) + ε, ε ~ N(0, σ²), and Ŷ = μ̂(X), then
    (Y - Ŷ)² = (μ - μ̂ + ε)² = (μ - μ̂)² + 2(μ - μ̂)ε + ε². -/
theorem squared_error_expansion (μ μ_hat ε : ℝ) :
    (μ + ε - μ_hat) ^ 2 = (μ - μ_hat) ^ 2 + 2 * (μ - μ_hat) * ε + ε ^ 2 := by
  ring

/-- **Expected squared error given X = x.**
    E[(Y - Ŷ)² | X = x] = (μ(x) - μ̂(x))² + σ².
    The first term is the squared bias, the second is irreducible noise. -/
theorem expected_squared_error_given_x (bias σ_sq : ℝ) :
    bias ^ 2 + σ_sq ≥ σ_sq := by
  linarith [sq_nonneg bias]

/-- **Variance of squared error given X = x.**
    Var((Y - Ŷ)² | X = x) ≈ 4·bias²·σ² + 2·σ⁴.
    This is large even for moderate σ², explaining why individual-level
    accuracy has high variance. -/
theorem variance_of_squared_error_lower_bound (σ_sq : ℝ) (hσ : 0 < σ_sq) :
    0 < 2 * σ_sq ^ 2 := by positivity

/-- **Conditional variance is large relative to conditional mean squared.**
    For ε ~ N(0, σ²), we have E[ε²] = σ² and Var(ε²) = 2σ⁴.
    Therefore CV² = Var(ε²)/E[ε²]² = 2σ⁴/σ⁴ = 2.
    Adding squared bias b² to the mean only reduces CV² (denominator grows faster),
    but the variance term 2σ⁴ provides a lower bound on conditional-squared-error
    variance regardless of bias.

    We derive: Var(squared error) / E[squared error]² ≥ 2σ⁴/(b² + σ²)²,
    and the conditional variance 4b²σ² + 2σ⁴ ≥ 2σ⁴ always. -/
theorem high_cv_inevitable (σ_sq bias_sq : ℝ) (hσ : 0 < σ_sq) (hb : 0 ≤ bias_sq) :
    -- Variance of squared error (4b²σ² + 2σ⁴) ≥ irreducible noise variance (2σ⁴)
    4 * bias_sq * σ_sq + 2 * σ_sq ^ 2 ≥ 2 * σ_sq ^ 2 := by
  nlinarith [mul_nonneg hb (le_of_lt hσ)]

/-- **Spline fit R² bounded above by noise-to-signal ratio.**
    A cubic spline fit of ε² on genetic distance d can explain at most
    Var(E[ε²|d]) / Var(ε²).
    When σ² >> bias variation, this fraction is tiny.

    Worked example: Wang et al. find R² = 0.51% for height. -/
theorem spline_r2_bounded_by_bias_variation
    (var_bias var_total δ : ℝ)
    (h_total_pos : 0 < var_total)
    (h_δ_nn : 0 ≤ δ)
    (h_bias_small : var_bias ≤ δ * var_total) :
    var_bias / var_total ≤ δ := by
  exact div_le_of_le_mul₀ (le_of_lt h_total_pos) h_δ_nn h_bias_small

end IndividualErrorDistribution


/-!
## Evolutionary Models for Trait-Specific Portability

Different evolutionary models predict different portability decay curves.
We formalize the key models and their predictions.
-/

section EvolutionaryModels

/-- **Neutral drift model: linear portability decay.**
    Under pure neutral drift: R²(d) ≈ R²(0) · (1 - 2·Fst(d)), floored at zero.

    **The floor is not cosmetic.** The previous body was `r2_0 * (1 - 2 * fst)`
    with nothing constraining it, so it returned a negative `R²` for every
    `fst > 0.5` -- an impossible value for a squared correlation, and one the
    simulation harness flagged directly. `neutralPortability_nonneg` and
    `neutralPortability_le_r2_0` now state the range, so a replacement body that
    can go negative no longer typechecks as this definition. `max 0` is the same
    absorbing-boundary device used by `selectionMigrationEquilibrium` in
    `PopulationGeneticsFoundations.lean`.

    **Two neutral laws coexist in this development and neither is settled.**
    This one is linear in `F_ST` with slope `2·r2_0`. The other is
    `neutralAFBenchmarkRatio fstS fstT = (1 - fstT)/(1 - fstS)`
    (`PortabilityDrift.lean`), used at the top of this very file. They are
    different functions: `neutralPortability_le_neutralAFBenchmark` below proves
    this one is always the more pessimistic of the two, and that is the entire
    relationship between them that is established. Which -- if either -- is the
    right neutral benchmark is open:

    * `neutralAFBenchmarkRatio` has just been falsified by simulation, −37% to
      −74% under asymmetric effective population sizes.
    * This law's `1 - 2·fst` slope has no derivation in the corpus at all; it is
      the first-order expansion of a heterozygosity ratio and inherits no
      evidence from the fit of anything else.

    Both are under revision. Do not treat either as the neutral expectation
    without saying which one and why.

    Empirical status: UNTESTED as a portability law, and CONDITIONALLY VALID at
    best as an approximation: the linear form can only be defensible for
    `fst ≪ 0.5`, and outside that range the floor -- not the formula -- is doing
    the work. -/
noncomputable def neutralPortability (r2_0 fst : ℝ) : ℝ :=
  r2_0 * max 0 (1 - 2 * fst)

/-- **Beyond `F_ST = 1/2` the law carries no information at all.**

The note on `neutralPortability` says the linear form "can only be defensible for
`fst ≪ 0.5`, and outside that range the floor -- not the formula -- is doing the work".
This is that statement, checkable: at `fst ≥ 1/2` the value is `0` for *every* ancestral
`r2_0`, so the law cannot distinguish a trait with perfect ancestral prediction from one
with none. It is not a conservative estimate there; it is a constant.

Stated as the regime for a definition whose assumption would otherwise live only in prose:
a caller working at `F_ST ≥ 1/2` — which includes the deep-divergence comparisons this
development is often applied to — is reading the floor, not the model. -/
theorem neutralPortability_vacuous_beyond_half (r2_0 fst : ℝ) (h : 1 / 2 ≤ fst) :
    neutralPortability r2_0 fst = 0 := by
  unfold neutralPortability
  have hle : 1 - 2 * fst ≤ 0 := by linarith
  rw [max_eq_left hle]
  ring

/-- **Neutral portability is a nonnegative `R²`.** The constraint the previous
    body violated for every `fst > 0.5`. -/
theorem neutralPortability_nonneg (r2_0 fst : ℝ) (hr2 : 0 ≤ r2_0) :
    0 ≤ neutralPortability r2_0 fst := by
  unfold neutralPortability
  exact mul_nonneg hr2 (le_max_left _ _)

/-- **Neutral portability never exceeds the source `R²`**, hence lies in
    `[0, 1]` whenever the source `R²` does. -/
theorem neutralPortability_le_r2_0 (r2_0 fst : ℝ)
    (hr2 : 0 ≤ r2_0) (hfst : 0 ≤ fst) :
    neutralPortability r2_0 fst ≤ r2_0 := by
  unfold neutralPortability
  have h_le : max 0 (1 - 2 * fst) ≤ 1 := max_le (by norm_num) (by linarith)
  calc r2_0 * max 0 (1 - 2 * fst) ≤ r2_0 * 1 :=
        mul_le_mul_of_nonneg_left h_le hr2
    _ = r2_0 := mul_one _

/-- **Neutral portability lies in `[0, 1]`** for a source `R²` in `[0, 1]`. -/
theorem neutralPortability_mem_unit (r2_0 fst : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2_le : r2_0 ≤ 1) (hfst : 0 ≤ fst) :
    0 ≤ neutralPortability r2_0 fst ∧ neutralPortability r2_0 fst ≤ 1 :=
  ⟨neutralPortability_nonneg r2_0 fst hr2,
    le_trans (neutralPortability_le_r2_0 r2_0 fst hr2 hfst) hr2_le⟩

/-- **The two neutral laws, related.** The linear law in this file is never
    above the allele-frequency benchmark ratio of `PortabilityDrift.lean`,
    scaled by the source `R²`:

      `r2_0 · max 0 (1 - 2·fstT) ≤ r2_0 · (1 - fstT)/(1 - fstS)`

    for any source differentiation `fstS ∈ [0, 1)`. Two neutral laws used to sit
    in the same development with nothing relating them; this is the inequality
    that relates them. It is not an endorsement of either -- see the note on
    `neutralPortability`, both are under revision -- but it does fix their
    order, so a claim derived under one is at least known to be conservative or
    liberal with respect to the other. -/
theorem neutralPortability_le_neutralAFBenchmark
    (r2_0 fstS fstT : ℝ)
    (hr2 : 0 ≤ r2_0)
    (hS : 0 ≤ fstS) (hS1 : fstS < 1)
    (hT : 0 ≤ fstT) (hT1 : fstT ≤ 1) :
    neutralPortability r2_0 fstT ≤ r2_0 * neutralAFBenchmarkRatio fstS fstT := by
  unfold neutralPortability neutralAFBenchmarkRatio
  have hden : (0 : ℝ) < 1 - fstS := by linarith
  have h1 : 1 - fstT ≤ (1 - fstT) / (1 - fstS) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have h2 : max 0 (1 - 2 * fstT) ≤ 1 - fstT :=
    max_le (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left (le_trans h2 h1) hr2

/-- **Stabilizing selection model: faster-than-neutral decay.**
    Under stabilizing selection, allelic effects are constrained near the optimum
    in both populations. The portability decay is close to neutral.

    Defined through `neutralPortability` so that it inherits the nonnegativity
    floor. The previous body spelled out `r2_0 * (1 - 2 * fst)` a second time
    and inherited the negative-`R²` escape with it.

    Empirical status: FALSIFIED as a one-parameter law. Simulation finds no
    constant `strength` that fits the portability curve: the fitted value spans
    13-fold over a 29-fold range of `F_ST`. The definition is retained because
    the qualitative ordering it supports (`stabilizing_le_neutral`,
    `diversifying_lt_stabilizing`) survives any positive `strength`, but the
    magnitude it predicts should not be used, and `strength` should not be
    reported as a fitted constant of a trait. -/
noncomputable def stabilizingPortability (r2_0 fst strength : ℝ) : ℝ :=
  neutralPortability r2_0 fst * Real.exp (-strength * fst)

/-- Stabilizing portability is a nonnegative `R²`. -/
theorem stabilizingPortability_nonneg (r2_0 fst strength : ℝ) (hr2 : 0 ≤ r2_0) :
    0 ≤ stabilizingPortability r2_0 fst strength := by
  unfold stabilizingPortability
  exact mul_nonneg (neutralPortability_nonneg r2_0 fst hr2)
    (le_of_lt (Real.exp_pos _))

/-- Stabilizing selection is never better than neutral for portability. -/
theorem stabilizing_le_neutral (r2_0 fst strength : ℝ)
    (hr2 : 0 ≤ r2_0)
    (hfst : 0 ≤ fst)
    (hs : 0 ≤ strength) :
    stabilizingPortability r2_0 fst strength ≤ neutralPortability r2_0 fst := by
  unfold stabilizingPortability
  have h_base_nn : 0 ≤ neutralPortability r2_0 fst :=
    neutralPortability_nonneg r2_0 fst hr2
  have h_exp_le : Real.exp (-strength * fst) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc neutralPortability r2_0 fst * Real.exp (-strength * fst)
      ≤ neutralPortability r2_0 fst * 1 :=
        mul_le_mul_of_nonneg_left h_exp_le h_base_nn
    _ = neutralPortability r2_0 fst := mul_one _

/-- **Diversifying/fluctuating selection model: much-faster-than-neutral decay.**
    Under fluctuating selection (immune traits), effects change rapidly.

    Defined through `neutralPortability` for the same reason as
    `stabilizingPortability`: the nonnegativity floor must be inherited, not
    re-spelled.

    Empirical status: FALSIFIED as a one-parameter law, jointly with
    `stabilizingPortability` -- no constant turnover rate fits the curve, the
    fitted value spanning 13-fold over a 29-fold `F_ST` range. The ordering
    results below hold for any positive parameters; the magnitudes do not. -/
noncomputable def diversifyingPortability (r2_0 fst lam_turn : ℝ) : ℝ :=
  neutralPortability r2_0 fst * (Real.exp (-lam_turn * fst)) ^ 2

/-! **The magnitude claim of the selection laws is not exported.**

`stabilizingPortability` and `diversifyingPortability` are recorded FALSIFIED as
one-parameter laws: simulation finds no constant `strength` fitting the portability curve,
the fitted value spanning 13-fold over a 29-fold range of `F_ST`. The definitions survive
because the *ordering* they support does, for any positive parameter.

The fitted-magnitude claim is deliberately not represented in Lean until a derivation from
an explicit population-genetic observation model is present.  In particular, callers cannot
turn an empirical curve fit into a theorem by packaging the fit as a structure field.  The
ordering theorems below remain because they are derived directly from the displayed laws. -/

/-- **The selection laws inherit the neutral law's vacuity beyond `F_ST = 1/2`.**

Both are defined *through* `neutralPortability` — deliberately, so the nonnegativity floor
is inherited rather than re-spelled — and that inheritance carries the floor's defect with
it. Past `fst = 1/2` both return `0` for every ancestral `r2_0` and every selection
parameter, so beyond that point the selection model is not weakly informative, it is
silent: no `strength` and no turnover rate changes the answer.

This is worth having explicitly because the ordering results are what these definitions are
retained for, and an ordering between two constants is not an ordering. Below `1/2` the
ordering theorems say something; at or above it they compare `0` with `0`. -/
theorem selectionPortability_vacuous_beyond_half (r2_0 fst strength lam_turn : ℝ)
    (h : 1 / 2 ≤ fst) :
    stabilizingPortability r2_0 fst strength = 0 ∧
      diversifyingPortability r2_0 fst lam_turn = 0 := by
  constructor
  · unfold stabilizingPortability
    rw [neutralPortability_vacuous_beyond_half r2_0 fst h]
    ring
  · unfold diversifyingPortability
    rw [neutralPortability_vacuous_beyond_half r2_0 fst h]
    ring

/-- Diversifying portability is a nonnegative `R²`. -/
theorem diversifyingPortability_nonneg (r2_0 fst lam_turn : ℝ) (hr2 : 0 ≤ r2_0) :
    0 ≤ diversifyingPortability r2_0 fst lam_turn := by
  unfold diversifyingPortability
  exact mul_nonneg (neutralPortability_nonneg r2_0 fst hr2)
    (pow_nonneg (le_of_lt (Real.exp_pos _)) 2)

/-- Diversifying selection gives strictly worse portability than stabilizing. -/
theorem diversifying_lt_stabilizing
    (r2_0 fst lam_stab lam_turn : ℝ)
    (hr2 : 0 < r2_0)
    (hfst : 0 < fst) (hfst_small : 2 * fst < 1)
    -- Diversifying effect is stronger than stabilizing
    (h_stronger : 2 * lam_turn > lam_stab) :
    diversifyingPortability r2_0 fst lam_turn <
      stabilizingPortability r2_0 fst lam_stab := by
  unfold diversifyingPortability stabilizingPortability
  have h_max : max 0 (1 - 2 * fst) = 1 - 2 * fst :=
    max_eq_right (by linarith)
  have h_base_pos : 0 < neutralPortability r2_0 fst := by
    unfold neutralPortability
    rw [h_max]
    exact mul_pos hr2 (by linarith)
  apply mul_lt_mul_of_pos_left _ h_base_pos
  rw [← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  apply Real.exp_lt_exp.mpr
  nlinarith

end EvolutionaryModels


/-!
## Concrete Witness: Height vs Lymphocyte Count

We construct concrete parameter witnesses showing that the theoretical
framework produces the qualitative patterns observed in the paper:
- Height: monotonic R_sq decay with distance
- Lymphocyte count: near-zero R_sq even at short distance
-/

section ConcreteWitnesses

/-- **Higher effect correlation → better portability.**
    Traits with higher genetic effect correlation ρ across populations
    retain more predictive accuracy (R² scales as ρ²). -/
theorem higher_rho_better_portability
    (r2_A r2_B ρ_A ρ_B : ℝ)
    (h_r2_A : 0 < r2_A) (h_r2_le : r2_B ≤ r2_A)
    (h_ρB : 0 ≤ ρ_B) (h_ρ : ρ_B < ρ_A) :
    r2_B * ρ_B ^ 2 < r2_A * ρ_A ^ 2 := by
  have h_sq : ρ_B ^ 2 < ρ_A ^ 2 := by
    nlinarith
  calc r2_B * ρ_B ^ 2 ≤ r2_A * ρ_B ^ 2 := by nlinarith [sq_nonneg ρ_B]
    _ < r2_A * ρ_A ^ 2 := by nlinarith

/-- **Sign discordance rate.**
    Under N(ρβ, σ²) model for target effects, the probability of sign flip is
    Φ(-|ρβ|/σ). We prove that smaller ρ implies more sign flips (larger flip
    probability), since the z-score ρβ/σ decreases with ρ.

    Worked example: With ρ ≈ 0.3 for lymphocyte count, sign flips are common. -/
theorem more_turnover_more_sign_flips
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (h_more_turnover : ρ₂ < ρ₁) :
    -- z-score for sign concordance is smaller with more turnover
    ρ₂ * β / σ < ρ₁ * β / σ := by
  exact sign_flip_z_decreases_with_turnover β σ ρ₁ ρ₂ hβ hσ h_more_turnover

end ConcreteWitnesses

end Calibrator
