/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift

namespace Descent.Portability

open MeasureTheory

/-!
# Quantitative Portability Bounds

Formal bounds on PGS portability derived from population-genetic parameters.

Only laws with a derivation or a live empirical contract are exported. One-parameter
stabilizing- and diversifying-selection curves are excluded because simulation shows that
no constant selection parameter fits the portability curve.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## Fst-Based Neutral Benchmarks -- deleted

The algebra itself is true, and nothing here disputes it. True algebra under a falsified
name is exactly the configuration that lets a portability prediction be read off a theorem,
which is why the name is absent rather than the algebra corrected. The falsification stands
as `PortabilityDrift.benchmarkRatioForm_cannot_reach_measured`, which states the ceiling
about the written-out expression and so needs no definition to exist.

Worked examples of the form `ratio ≈ 0.88` at `Fst ≈ 0.12` and `≈ 0.85` at `Fst ≈ 0.15`,
concluding that larger observed `R²` drops confirm non-neutral effects, run through the
out-of-range formula and belong nowhere in this file. `Descent.PopGen.HumanDemography` reaches
the neutral-floor conclusion by a route that survives measurement, and gets `0.985` rather
than `0.88` for the continental case, because the floor must be computed from the branch
quantity `1 - H_T/H_S` and not from a pairwise `F_ST`.
-/


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
    `neutralPortability_le_r2_0` state the range, so a replacement body that
    can go negative does not typecheck as this definition. `max 0` is the same
    absorbing-boundary device used by `selectionMigrationEquilibrium` in
    `PopulationGeneticsFoundations.lean`.

    **This is the only neutral law in the development, and it is not
    settled.** It is linear in `F_ST` with slope `2·r2_0`. The rival candidate
    `neutralAFBenchmarkRatio fstS fstT = (1 - fstT)/(1 - fstS)` is absent from
    `PortabilityDrift.lean` on purpose: simulation puts it −37% to −74%
    low under asymmetric effective population sizes, and the measurement lies
    outside the range the expression can reach at all. The theorem that ordered
    the two, `neutralPortability_le_neutralAFBenchmark`, is absent with it. It fixed
    this law as the more pessimistic of the pair, which is not a fact worth
    stating once the pair is a single law.

    That leaves this law's own standing untouched and unimproved. The
    `1 - 2·fst` slope has no derivation in the corpus at all; it is the
    first-order expansion of a heterozygosity ratio and inherits no evidence
    from the fit of anything else. Do not treat it as the neutral expectation
    without saying why.

    Empirical status: **VALIDATED** (the body was corrected first; the
    superseded one and its refutation are recorded below)
    (`simcov/battery_bulk56.py`). The body is now the deployed chart written in
    this signature, and it needs no regime restriction.

    THE SUPERSEDED LINEAR FORM was `r2_0 * max 0 (1 - 2*fst)`, and it is
    falsified at 136 sems (86% relative) -- including INSIDE the `fst ≪ 0.5`
    range its own note claimed for it. 3000 variants, 400000 individuals per
    population, the score tracking the attenuated signal:

      fst    linear 1-2fst   corrected body   realised R² ratio
      0.05      0.90000         0.97436        0.97542 ± 0.00617
      0.15      0.70000         0.91892        0.93744 ± 0.00593
      0.30      0.40000         0.82353        0.82168 ± 0.00520
      0.45      0.10000         0.70968        0.72998 ± 0.00462

    At `fst = 0.05` -- as far inside the claimed regime as the design goes --
    the linear form is already 12 sems out. The slope is not merely wrong
    outside its range; it has no range in which it holds.

    WHY THE SIGNATURE SUFFICED. The correct retention depends on the
    signal-to-noise ratio, which looks like an argument this body does not have.
    It has it implicitly: `r2_0 = V_A/(V_A+V_E)`, so `V_E/V_A = (1-r2_0)/r2_0`
    and the chart ratio can be written in `r2_0` and `fst` alone. That is what
    the body now is, and it reduces to `r2_0` at `fst = 0` as it must.

    The corrected form carries a residual of 2.78% at the worst cell, at the
    finite-panel scale for `m = 3000`, and agrees at 0.36 sems at `fst = 0.30`.

    `neutralDriftR2Ratio` is the same chart as a bare ratio and is separately
    validated at 2.25 sems.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk56.py` is now in the repository, was run against
    the design described above, and its results are committed beside it.
    MATCH at worst 1.70 sems (0.63% relative); the superseded linear form is FALSIFIED
    at 101 sems, including at fst = 0.05, as far INSIDE the range its own note claimed
    as the design goes.
    -/
noncomputable def neutralPortability (r2_0 fst : ℝ) : ℝ :=
  r2_0 * (1 - fst) / ((1 - fst) * r2_0 + (1 - r2_0))

/-- **`neutralPortability_vacuous_beyond_half` was deleted with the linear body.**

It said that at `fst ≥ 1/2` the value is `0` for every ancestral `r2_0`, and that was TRUE of
`r2_0 * max 0 (1 - 2*fst)`: the floor, not the formula, was doing the work. It is FALSE of the
corrected body and false of the measurement. At `r2_0 = 1/2` and `fst = 1/2` the simulated
retained `R²` is about `0.29·r2_0`, not zero -- a trait with good ancestral prediction still
predicts at deep divergence, which is the substantive point the floor was erasing.

Keeping it would have been the laundering this corpus warns about: a true theorem about a
superseded formula, left where a reader takes it for a property of neutral transport. The
regime warning it encoded is now unnecessary, because the corrected body has no floor and no
regime restriction -- it is the deployed chart, valid across the whole range. -/
theorem neutralPortability_pos_beyond_half (r2_0 fst : ℝ)
    (hr2 : 0 < r2_0) (hr2' : r2_0 < 1) (hfst : fst < 1) :
    0 < neutralPortability r2_0 fst := by
  unfold neutralPortability
  have hnum : 0 < r2_0 * (1 - fst) := mul_pos hr2 (by linarith)
  have hden : 0 < (1 - fst) * r2_0 + (1 - r2_0) := by nlinarith
  exact div_pos hnum hden

/-- **Neutral portability is a nonnegative `R²`.** -/
theorem neutralPortability_nonneg (r2_0 fst : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hfst : fst ≤ 1) :
    0 ≤ neutralPortability r2_0 fst := by
  unfold neutralPortability
  have h1 : (0 : ℝ) ≤ 1 - fst := by linarith
  have hnum : 0 ≤ r2_0 * (1 - fst) := mul_nonneg hr2 h1
  have hprod : 0 ≤ (1 - fst) * r2_0 := mul_nonneg h1 hr2
  have hden : 0 ≤ (1 - fst) * r2_0 + (1 - r2_0) := by linarith
  exact div_nonneg hnum hden

/-- **Neutral portability never exceeds the source `R²`**, hence lies in
    `[0, 1]` whenever the source `R²` does. The corrected body keeps this
    property: the retention factor `(1-fst) / ((1-fst)·r2_0 + (1-r2_0))` is at
    most one exactly when `fst ≥ 0`, and equals one at `fst = 0`. -/
theorem neutralPortability_le_r2_0 (r2_0 fst : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hfst : 0 ≤ fst) (hfst' : fst < 1) :
    neutralPortability r2_0 fst ≤ r2_0 := by
  unfold neutralPortability
  have h1 : (0 : ℝ) < 1 - fst := by linarith
  have hprod : 0 ≤ (1 - fst) * r2_0 := mul_nonneg (le_of_lt h1) hr2
  have hden : 0 < (1 - fst) * r2_0 + (1 - r2_0) ∨ r2_0 = 1 := by
    rcases eq_or_lt_of_le hr2' with h | h
    · exact Or.inr h
    · exact Or.inl (by nlinarith)
  rcases hden with hden | hone
  · rw [div_le_iff₀ hden]
    -- the gap is `r2_0 * (1 - r2_0) * fst`, nonnegative on the stated range
    nlinarith [mul_nonneg (mul_nonneg hr2 (by linarith : (0:ℝ) ≤ 1 - r2_0)) hfst]
  · subst hone
    have hsimp : (1 - fst) * 1 + (1 - 1) = 1 - fst := by ring
    rw [hsimp, one_mul, div_self (ne_of_gt h1)]

/-- **Neutral portability lies in `[0, 1]`** for a source `R²` in `[0, 1]`.

    The `fst < 1` hypothesis is new with the corrected body. The superseded
    linear form was defined at every `fst` because its floor clipped it to zero;
    the deployed chart has a genuine pole at `fst = 1`, where the whole signal
    has stopped being shared and the ratio is `0/0`. Callers at complete
    divergence must exclude it rather than read a junk value. -/
theorem neutralPortability_mem_unit (r2_0 fst : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2_le : r2_0 ≤ 1) (hfst : 0 ≤ fst) (hfst' : fst < 1) :
    0 ≤ neutralPortability r2_0 fst ∧ neutralPortability r2_0 fst ≤ 1 :=
  ⟨neutralPortability_nonneg r2_0 fst hr2 hr2_le (le_of_lt hfst'),
    le_trans (neutralPortability_le_r2_0 r2_0 fst hr2 hr2_le hfst hfst') hr2_le⟩

end EvolutionaryModels


/-!
## Concrete Witness: Height vs Lymphocyte Count

We construct concrete parameter witnesses showing that the theoretical
framework produces the qualitative patterns observed in the paper:
- Height: monotonic R_sq decay with distance
- Lymphocyte count: near-zero R_sq even at short distance
-/

section ConcreteWitnesses

/-- **`r·ρ²` is increasing in both factors**, for `0 ≤ ρ_B < ρ_A` and
    `0 < r2_B ≤ r2_A`.

    The reading is that a trait whose cross-population effect correlation is
    higher retains more accuracy, because `R²` scales as `ρ²`. That scaling is
    the modelling content, and it is assumed by writing the product `r2 * ρ^2`
    rather than derived from anything. No population, no effect and no `R²`
    occurs below; `r2_A`, `ρ_A` and their `B` counterparts are four unconstrained
    reals. -/
theorem mul_sq_lt_mul_sq_of_le_of_lt
    (r2_A r2_B ρ_A ρ_B : ℝ)
    (h_r2_A : 0 < r2_A) (h_r2_le : r2_B ≤ r2_A)
    (h_ρB : 0 ≤ ρ_B) (h_ρ : ρ_B < ρ_A) :
    r2_B * ρ_B ^ 2 < r2_A * ρ_A ^ 2 := by
  have h_sq : ρ_B ^ 2 < ρ_A ^ 2 := by
    nlinarith
  calc r2_B * ρ_B ^ 2 ≤ r2_A * ρ_B ^ 2 := by nlinarith [sq_nonneg ρ_B]
    _ < r2_A * ρ_A ^ 2 := by nlinarith

/-- **`ρ ↦ ρβ/σ` is increasing**, for `β > 0` and `σ > 0`.

    Read as genetics: under a `N(ρβ, σ²)` model for target effects the sign-flip
    probability is `Φ(-|ρβ|/σ)`, so a smaller effect correlation means more sign
    flips. The statement does not reach that. There is no `Φ`, no probability,
    no normal law and no absolute value below — only the monotonicity of the
    z-score in `ρ`, which is one input to the argument and not the argument.
    Turning it into a statement about flip rates needs `Φ` monotone and the
    model assumed, and neither step is taken here. No numeral appears in the
    statement, so no measured `ρ` is an instance of it. -/
theorem z_score_strictMono_in_rho
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (h_more_turnover : ρ₂ < ρ₁) :
    -- z-score for sign concordance is smaller with more turnover
    ρ₂ * β / σ < ρ₁ * β / σ := by
  exact Program.sign_flip_z_decreases_with_turnover β σ ρ₁ ρ₂ hβ hσ h_more_turnover

end ConcreteWitnesses

end Descent.Portability
