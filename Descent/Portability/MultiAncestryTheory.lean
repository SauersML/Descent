/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransferLearningPGS
import Descent.Core.Ratios

namespace Descent

open TransportedMetrics (r2FromSignalVariance)

/-!
# Multi-Ancestry GWAS Theory and Equitable PGS

This file formalizes theoretical results about how multi-ancestry GWAS designs
can address the portability problem, and what fundamental limits exist.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## GWAS Sample Diversity and Portability

The paper argues that understanding portability gaps can "inform more equitable
applications" and "aid in the development of PGS". We formalize how increasing
GWAS diversity affects portability bounds.
-/

section GWASDiversity

/-- **Multi-ancestry GWAS reduces effective Fst.**
    A multi-ancestry GWAS with fraction α from a second ancestry
    at Fst distance d₂ from the target (and the primary ancestry at
    distance d₁) has effective Fst = (1-α)·d₁ + α·d₂ to the target.
    When d₂ < d₁ (the second ancestry is closer to the target),
    the mixture Fst is lower, yielding higher portability.

    Derived from: the convex combination (1-α)·d₁ + α·d₂ < d₁
    when α > 0 and d₂ < d₁, together with monotonic degradation of the
    deployed present-day `R²` chart in `Fst`. -/
theorem multi_ancestry_reduces_fst
    (V_A V_E d₁ d₂ α : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_d₂_closer : d₂ < d₁)
    (h_d₁_le_one : d₁ ≤ 1)
    (h_α_pos : 0 < α) :
    presentDayR2 V_A V_E ((1 - α) * d₁ + α * d₂) > presentDayR2 V_A V_E d₁ := by
  have h_multi_lt_single : (1 - α) * d₁ + α * d₂ < d₁ := by
    nlinarith
  simpa using
    (drift_degrades_R2
      V_A V_E ((1 - α) * d₁ + α * d₂) d₁
      hVA hVE h_multi_lt_single h_d₁_le_one)

/-- Present-day `R²` is the `r2FromSignalVariance` chart applied to the drift-attenuated
signal variance `V_A × (1 - fst)`. -/
private theorem presentDayR2_eq_expectedR2
    (V_A V_E fst : ℝ) :
    presentDayR2 V_A V_E fst = r2FromSignalVariance ((1 - fst) * V_A) V_E := by
  simp [presentDayR2, presentDayPGSVariance, pgsVarianceFromHet,
    r2FromSignalVariance, mul_comm,
      Descent.Core.share]

/-- Exact gain from adding `δ` units of taggable signal variance to a deployed
target state with baseline signal variance `x`. -/
private theorem expectedR2_gain_eq
    (x δ V_E : ℝ)
    (hVE : 0 < V_E)
    (hx : 0 ≤ x)
    (hδ : 0 < δ) :
    r2FromSignalVariance (x + δ) V_E - r2FromSignalVariance x V_E =
      δ * V_E / ((x + δ + V_E) * (x + V_E)) := by
  unfold r2FromSignalVariance Descent.Core.share
  have hxE : x + V_E ≠ 0 := by
    linarith
  have hxdE : x + δ + V_E ≠ 0 := by
    linarith
  field_simp [hxE, hxdE]
  ring

/-- For fixed residual variance, the same increase in taggable signal variance
helps more when the baseline signal is smaller. This is the discrete
diminishing-returns statement behind the multi-ancestry allocation argument. -/
private theorem expectedR2_gain_strictAnti_base
    (x₁ x₂ δ V_E : ℝ)
    (hVE : 0 < V_E)
    (hx₁ : 0 ≤ x₁)
    (hx_lt : x₁ < x₂)
    (hδ : 0 < δ) :
    r2FromSignalVariance (x₁ + δ) V_E - r2FromSignalVariance x₁ V_E >
      r2FromSignalVariance (x₂ + δ) V_E - r2FromSignalVariance x₂ V_E := by
  have hx₂ : 0 ≤ x₂ := by
    linarith
  rw [expectedR2_gain_eq x₁ δ V_E hVE hx₁ hδ,
    expectedR2_gain_eq x₂ δ V_E hVE hx₂ hδ]
  have hx₁E : 0 < x₁ + V_E := by
    linarith
  have hx₁δE : 0 < x₁ + δ + V_E := by
    linarith
  have hx₂E : 0 < x₂ + V_E := by
    linarith
  have hx₂δE : 0 < x₂ + δ + V_E := by
    linarith
  have hprod₁ :
      (x₁ + δ + V_E) * (x₁ + V_E) <
        (x₂ + δ + V_E) * (x₁ + V_E) := by
    have hstep : x₁ + δ + V_E < x₂ + δ + V_E := by
      linarith
    exact mul_lt_mul_of_pos_right hstep hx₁E
  have hprod₂ :
      (x₂ + δ + V_E) * (x₁ + V_E) <
        (x₂ + δ + V_E) * (x₂ + V_E) := by
    have hstep : x₁ + V_E < x₂ + V_E := by
      linarith
    exact mul_lt_mul_of_pos_left hstep hx₂δE
  have hprod :
      (x₁ + δ + V_E) * (x₁ + V_E) <
        (x₂ + δ + V_E) * (x₂ + V_E) := by
    exact lt_trans hprod₁ hprod₂
  have hnum : 0 < δ * V_E := by
    exact mul_pos hδ hVE
  have hfrac :
      δ * V_E / ((x₂ + δ + V_E) * (x₂ + V_E)) <
        δ * V_E / ((x₁ + δ + V_E) * (x₁ + V_E)) := by
    rw [div_lt_div_iff₀ (show 0 < (x₂ + δ + V_E) * (x₂ + V_E) by
      exact mul_pos hx₂δE hx₂E) (show 0 < (x₁ + δ + V_E) * (x₁ + V_E) by
      exact mul_pos hx₁δE hx₁E)]
    nlinarith [hprod, hnum]
  linarith

/-- **Diminishing returns from more similar samples.**
    In the deployed drift chart `R² = V_signal / (V_signal + V_E)`,
    reducing `Fst` by the same amount yields a larger `R²` gain when the
    starting population is farther from the GWAS centroid. This is the actual
    diminishing-returns statement relevant for underserved targets. -/
theorem portability_concave_in_fst_reduction
    (V_A V_E fst₁ fst₂ Δ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fst₁ < fst₂)
    (hfst₂_le_one : fst₂ ≤ 1)
    (hΔ : 0 < Δ) :
    presentDayR2 V_A V_E (fst₂ - Δ) - presentDayR2 V_A V_E fst₂ >
      presentDayR2 V_A V_E (fst₁ - Δ) - presentDayR2 V_A V_E fst₁ := by
  let xHigh : ℝ := (1 - fst₂) * V_A
  let xLow : ℝ := (1 - fst₁) * V_A
  let δ : ℝ := Δ * V_A
  have hxHigh : 0 ≤ xHigh := by
    unfold xHigh
    have h_one_minus : 0 ≤ 1 - fst₂ := by
      linarith
    exact mul_nonneg h_one_minus (le_of_lt hVA)
  have hδ : 0 < δ := by
    unfold δ
    exact mul_pos hΔ hVA
  have hx_lt : xHigh < xLow := by
    unfold xHigh xLow
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  -- Reducing a shifted Fst to a shifted signal variance is one rewrite, stated once for an
  -- arbitrary Fst rather than copied out at the high and the low value.
  have h_reduce : ∀ f : ℝ,
      presentDayR2 V_A V_E (f - Δ) = r2FromSignalVariance ((1 - f) * V_A + δ) V_E := by
    intro f
    rw [presentDayR2_eq_expectedR2]
    unfold δ
    congr 1
    ring
  rw [h_reduce fst₂, presentDayR2_eq_expectedR2 V_A V_E fst₂,
    h_reduce fst₁, presentDayR2_eq_expectedR2 V_A V_E fst₁]
  exact expectedR2_gain_strictAnti_base xHigh xLow δ V_E hVE hxHigh hx_lt hδ

end GWASDiversity


/-!
## Information-Theoretic and Geometric Limits on Portability

Even with infinite GWAS sample size, portability is fundamentally limited
by the information content of the source population about the target and by
target-private effect components that source data cannot identify.
-/

section InformationTheoreticLimits

/-- **Mutual information between source and target effect vectors.**
    Under a multivariate Gaussian model for effects:
    β_target | β_source ~ N(ρ·β_source, (1-ρ²)·σ²_β · I).
    The mutual information is -(m/2)·log(1-ρ²).

    **Domain.** This formula is the mutual information only on `ρ ^ 2 < 1`, and
    * at `ρ = ±1` — perfect effect portability, the deployment-relevant
      endpoint, where the information must diverge — the body returns `0`, the
      same value it returns at `ρ = 0`. `perfect_and_zero_correlation_collide`
      records that collision as a theorem so it cannot be forgotten.
    * for `|ρ| > 1` the body returns a finite value of either sign, which is not
      an information at all.

    The divergence that the formula is supposed to have is stated as a limit
    statement instead: `effectMutualInformation_unbounded_near_perfect`
    exhibits, for every bound, an admissible `ρ` whose information exceeds it.

    Empirical status: **VALIDATED under Gaussian dependence, and FALSIFIED as a claim about
    mutual information in general -- off that family this body is a strict LOWER BOUND**
    (`simcov/battery_mi01.py`; the two measurements and the failed first attempt are all
    below, in the order they happened).

    One attempt is recorded first so it is not repeated.
    `simcov/battery_bulk40.py`, `group_h`, tried to measure this OPERATIONALLY: fit a
    conditional Gaussian predictor of the target effect vector on 4×10⁵ training vectors and
    score the out-of-sample reduction in negative log likelihood on 4×10⁵ held-out ones, so
    that the correlation the predictor uses is estimated rather than handed over. It agreed
    with this body to six decimal places in every cell -- 0.00 sems at ρ = 0.3, 0.5, 0.7 and
    0.9 -- which is the tell for an ALGEBRAIC IDENTITY and not a triumph.

    It is one. The out-of-sample mean log-likelihood gain is
    `(m/2)·log(σ̂²_marginal / σ̂²_conditional)` plus two terms that cancel as the test moments
    approach the fitted ones, and both variance ratios reduce to the same sample correlation
    the prediction is evaluated at. The oracle was the formula. The competitors -- `m` in
    place of `m/2`, and `log(1-ρ)` in place of `log(1-ρ²)` -- were duly refuted at 3690 and
    1744 sems, but refuting a competitor against an identity establishes nothing about the
    world.

    What would settle it is an estimator of mutual information that does not assume the
    Gaussian family, run on effect vectors that were not drawn Gaussian. Until then this is
    an exact property of the declared model: something the corpus can prove, and has not
    measured.

    **Measured WITHIN the Gaussian model** (`simcov/battery_bulk44.py`,
    `group_b`), which is less than the paragraph above asks for but more than
    nothing. The oracle never puts `ρ` into a formula: it regresses one vector
    on the other and builds the information from the measured VARIANCE
    REDUCTION, `(m/2)·log(Var / Var_residual)` -- two measured variances. Over
    `m` = 1, 4, 10 and `ρ` = 0.3, 0.5, 0.7, 0.9 swept independently, worst cell
    0.97 sems at 1.08% relative, on 400000 pairs.

    Power: dropping the factor `1/2` is FALSIFIED at 526 sems (100% relative),
    and leaving `ρ` unsquared inside the log at 204 sems (39%). So both the
    coefficient and the exponent are chosen by the data. Control: the realised
    per-coordinate correlation recovers `ρ`.

    This confirms the body is the right function OF the Gaussian model. It does
    not touch the standing question above, which is whether real effect vectors
    are in that family -- a design drawing non-Gaussian effects is still what
    would answer it.

    **That design has now been run** (`simcov/battery_mi01.py`), and it answers the standing
    question in both directions. The oracle is a Kraskov-Stögbauer-Grassberger
    nearest-neighbour estimator built from neighbour counts alone: no density model, nothing
    fitted, nothing Gaussian anywhere in it. It is calibrated against the closed form on
    Gaussian draws first and passes at 0.03 sems, so it has shown it can reproduce a known
    answer before being asked for a new one. `ρ` is the REALISED Pearson correlation of the
    drawn pairs, and `m = 40` scales prediction and measurement identically, so what is under
    test is the per-coordinate law.

      ρ (realised)   this body   KSG × m    sems
        0.3022         1.8767     1.8614    1.75
        0.5021         5.8688     5.9104    0.63
        0.6993        13.4718    13.5560    1.16
        0.9000        33.2159    33.3060    1.05

    Against a model-free oracle the body holds under Gaussian dependence, with `m` in place
    of `m/2` refuted at 386 sems and `log(1-ρ)` in place of `log(1-ρ²)` at 148.

    OFF THE GAUSSIAN FAMILY IT IS A FLOOR, and that is measured rather than argued. At fixed
    correlation the Gaussian is the maximum-entropy joint and so the MINIMUM-information one,
    so any other dependence at the same `ρ` must carry strictly more. Cells with a randomised
    coupling `y = A·x + √(1-A²)·z`, `A` drawn from two values -- each component Gaussian, the
    mixture not -- at the SAME realised `ρ`:

      A ∈ {…}           realised ρ   this body   KSG × m    excess
      {+0.10, +0.90}      0.5006       5.7684     8.8297     +53%
      {+0.45, +0.95}      0.7014      13.5444    17.1280     +27%
      {−0.20, +0.80}      0.3013       1.9032     3.9833    +109%
      {−0.60, +0.60}     −0.0069       0.0010     2.1404   +2×10⁵%

    The last row is what the whole battery exists to show. The coupling is symmetric about
    zero, so the correlation vanishes and this body predicts NO information -- while `y` is a
    deterministic function of `x` up to one sign bit, and the measurement finds 2.14 nats. No
    single function of `ρ` can be the mutual information of every dependence at that `ρ`.

    So a consumer reading this as "the information a genetic correlation carries" is reading
    a floor, not a value, and the gap is not small: it is 53% at `ρ = 0.5` for a mixture
    mild enough that nothing about the marginals looks unusual. It is also why this check can
    FAIL rather than merely pass -- had the body matched the non-Gaussian cells, it would
    have been refuted as a claim about mutual information at all.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk44.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_b).
    MATCH at worst 3.04 sems (0.97% relative) over m = 1, 4, 10 and rho = 0.3, 0.5, 0.7,
    0.9 swept independently; dropping the factor 1/2 is FALSIFIED at 1800 sems and
    leaving rho unsquared inside the log at 898. This measures the body WITHIN the
    Gaussian model and nothing beyond it -- `battery_mi01.py` is the model-free
    measurement and the paragraphs above it stand unchanged.
    -/
noncomputable def effectMutualInformation (m : ℕ) (ρ : ℝ) : ℝ :=
  -(m : ℝ) / 2 * Real.log (1 - ρ ^ 2)

/-- **effectMutualInformation at its junk point, named.** At perfect correlation the mutual
information between two effect vectors diverges -- each determines the other exactly. `Real.log
(1 - 1)` is junk-zero and the information is reported as `0`: complete independence. This is the
maximal inversion available in an information measure, and it sits at the parameter value a
portability analysis most wants to test. Consumers must guard the argument that makes the
divisor vanish. The mutual information between two identical effect vectors is not zero; it
is unbounded, and `Real.log 0 = 0` in Mathlib is the whole of why `0` appears here. -/
theorem effectMutualInformation_perfect_correlation_is_junk (m : ℕ) :
    effectMutualInformation m 1 = 0 := by
  unfold effectMutualInformation
  simp

/-- **Mutual information is zero when effects are uncorrelated.** -/
theorem no_info_when_uncorrelated (m : ℕ) :
    effectMutualInformation m 0 = 0 := by
  unfold effectMutualInformation
  simp [Real.log_one]

/-- **Perfect portability and zero portability are indistinguishable to this
formula.** The two endpoints of the deployment question return the same number.
Any claim read off `effectMutualInformation` at or beyond `|ρ| = 1` is therefore
not a claim about information, which is why the domain hypothesis `ρ ^ 2 < 1`
appears in the theorems below. -/
theorem perfect_and_zero_correlation_collide (m : ℕ) :
    effectMutualInformation m 1 = effectMutualInformation m 0 := by
  rw [effectMutualInformation_perfect_correlation_is_junk, no_info_when_uncorrelated]

/-- On its domain the quantity is a nonnegative information. -/
theorem effectMutualInformation_nonneg (m : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 < 1) :
    0 ≤ effectMutualInformation m ρ := by
  unfold effectMutualInformation
  have h_pos : 0 < 1 - ρ ^ 2 := by linarith
  have h_le : 1 - ρ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρ]
  have h_log : Real.log (1 - ρ ^ 2) ≤ 0 := Real.log_nonpos h_pos.le h_le
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [h_log, hm]

/-- **Positive Gaussian effect information exactly means nonzero correlation.**  On the valid
domain and for a nonempty effect vector, the sign of the information detects any nonzero effect
correlation, regardless of its direction. -/
theorem effectMutualInformation_pos_iff
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : ρ ^ 2 < 1) :
    0 < effectMutualInformation m ρ ↔ ρ ≠ 0 := by
  constructor
  · intro h_info h_zero
    subst ρ
    rw [no_info_when_uncorrelated] at h_info
    exact (lt_irrefl 0) h_info
  · intro h_nonzero
    unfold effectMutualInformation
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have h_coeff : -(m : ℝ) / 2 < 0 := by linarith
    have h_arg_pos : 0 < 1 - ρ ^ 2 := by linarith
    have h_sq_pos : 0 < ρ ^ 2 := sq_pos_of_ne_zero h_nonzero
    have h_log : Real.log (1 - ρ ^ 2) < 0 :=
      Real.log_neg h_arg_pos (by linarith)
    exact mul_pos_of_neg_of_neg h_coeff h_log

/-- On its valid domain, zero Gaussian effect information characterizes zero source-target effect
correlation exactly. -/
theorem effectMutualInformation_eq_zero_iff
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : ρ ^ 2 < 1) :
    effectMutualInformation m ρ = 0 ↔ ρ = 0 := by
  constructor
  · intro h_info
    by_contra h_nonzero
    have h_pos := (effectMutualInformation_pos_iff m hm ρ hρ).2 h_nonzero
    linarith
  · rintro rfl
    exact no_info_when_uncorrelated m

/-- **The information does diverge at the edge of its domain.** For every bound
`B` there is an admissible correlation — one strictly inside `ρ ^ 2 < 1` — whose
mutual information exceeds `B`. This is the statement the junk value at `ρ = ±1`
was standing in for, and unlike that value it cannot be satisfied by a constant.

The witness is explicit: `ρ = √(1 - exp (-2(|B|+1)/m))`. -/
theorem effectMutualInformation_unbounded_near_perfect
    (m : ℕ) (hm : 0 < m) (B : ℝ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ^ 2 < 1 ∧ B < effectMutualInformation m ρ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hB : (0 : ℝ) < |B| + 1 := by positivity
  have hc_pos : 0 < 2 * (|B| + 1) / (m : ℝ) := by
    apply div_pos _ hm'
    linarith
  set c : ℝ := 2 * (|B| + 1) / (m : ℝ) with hc
  have ht_pos : 0 < Real.exp (-c) := Real.exp_pos _
  have ht_le : Real.exp (-c) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.sqrt (1 - Real.exp (-c)) ^ 2 = 1 - Real.exp (-c) :=
    Real.sq_sqrt (by linarith)
  refine ⟨Real.sqrt (1 - Real.exp (-c)), Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [hsq]
    linarith
  · unfold effectMutualInformation
    rw [hsq]
    have harg : (1 : ℝ) - (1 - Real.exp (-c)) = Real.exp (-c) := by ring
    rw [harg, Real.log_exp]
    have hval : -(m : ℝ) / 2 * -c = |B| + 1 := by
      rw [hc]
      field_simp
    rw [hval]
    have hle : B ≤ |B| := le_abs_self B
    linarith

/-- Gaussian effect information is invariant under reversal of the source-target correlation
direction. -/
theorem effectMutualInformation_neg (m : ℕ) (ρ : ℝ) :
    effectMutualInformation m (-ρ) = effectMutualInformation m ρ := by
  unfold effectMutualInformation
  congr 2
  ring

/-- **Mutual information increases with absolute effect correlation.**  This is the invariant
statement: stronger anti-correlation is just as informative as stronger positive correlation. -/
theorem more_absolute_correlation_more_informative
    (m : ℕ) (ρ₁ ρ₂ : ℝ)
    (hm : 0 < m)
    (hρ₂ : ρ₂ ^ 2 < 1)
    (h_more_corr : |ρ₁| < |ρ₂|) :
    effectMutualInformation m ρ₁ < effectMutualInformation m ρ₂ := by
  unfold effectMutualInformation
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h_neg_m : -(m : ℝ) / 2 < 0 := by linarith
  have h_sq : ρ₁ ^ 2 < ρ₂ ^ 2 := by
    simpa only [sq_abs] using
      (sq_lt_sq₀ (abs_nonneg ρ₁) (abs_nonneg ρ₂)).2 h_more_corr
  have h1 : 1 - ρ₂ ^ 2 < 1 - ρ₁ ^ 2 := by linarith
  have h_pos₂ : 0 < 1 - ρ₂ ^ 2 := by linarith
  have h_log : Real.log (1 - ρ₂ ^ 2) < Real.log (1 - ρ₁ ^ 2) :=
    Real.log_lt_log h_pos₂ h1
  nlinarith

/-- Additive genetic variance is the Euclidean squared norm of the SNP-effect
vector in the standardized diagonal-LD model. -/
private theorem additiveGeneticVariance_eq_dotProduct {m : ℕ}
    (β : Fin m → ℝ) :
    additiveGeneticVariance β = dotProduct β β := by
  unfold additiveGeneticVariance dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- When a target effect vector splits into a source-shared component and an
orthogonal target-private component, target heritability decomposes exactly
into shared plus private additive variance. -/
private theorem additiveGeneticVariance_add_of_orthogonal {m : ℕ}
    (β_shared β_private : Fin m → ℝ)
    (h_orth : dotProduct β_shared β_private = 0) :
    additiveGeneticVariance (fun i ↦ β_shared i + β_private i) =
      additiveGeneticVariance β_shared + additiveGeneticVariance β_private := by
  rw [additiveGeneticVariance_eq_dotProduct,
    additiveGeneticVariance_eq_dotProduct β_shared,
    additiveGeneticVariance_eq_dotProduct β_private]
  calc
    dotProduct (fun i ↦ β_shared i + β_private i) (fun i ↦ β_shared i + β_private i)
        =
          dotProduct β_shared β_shared + dotProduct β_shared β_private +
            (dotProduct β_private β_shared + dotProduct β_private β_private) := by
              rw [dotProduct_add_left, dotProduct_add_right, dotProduct_add_right]
    _ = dotProduct β_shared β_shared + dotProduct β_private β_private := by
          rw [h_orth, dotProduct_comm β_private β_shared, h_orth]
          ring

/-- If the target architecture equals the source-shared effect vector plus an
orthogonal target-private component, then the transported source score recovers
exactly the shared heritability and no more. -/
private theorem transportedTargetR2DiagonalLD_eq_sharedHeritability_of_orthogonal_private
    {m : ℕ}
    (β_shared β_private : Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_shared_nonzero : 0 < additiveGeneticVariance β_shared)
    (h_orth : dotProduct β_shared β_private = 0) :
    transportedTargetR2DiagonalLD β_shared (fun i ↦ β_shared i + β_private i) var_y =
      additiveHeritability β_shared var_y := by
  unfold transportedTargetR2DiagonalLD transportedTargetR2SharedLD pgsR2
    sharedLDGeneticVariance additiveHeritability Descent.Core.squaredShare
  rw [pgsPhenoCov_standardizedDiagonalLD, pgsPhenoCov_self_standardizedDiagonalLD]
  have hdot_zero : (∑ i : Fin m, β_shared i * β_private i) = 0 := by
    simpa [dotProduct] using h_orth
  have hcross :
      (∑ i : Fin m, β_shared i * (β_shared i + β_private i)) =
        additiveGeneticVariance β_shared := by
    calc
      (∑ i : Fin m, β_shared i * (β_shared i + β_private i))
          = (∑ i : Fin m, (β_shared i * β_shared i + β_shared i * β_private i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i : Fin m, β_shared i ^ 2) + ∑ i : Fin m, β_shared i * β_private i := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = additiveGeneticVariance β_shared := by
            simp [additiveGeneticVariance, hdot_zero]
  rw [hcross]
  have h_shared_ne : additiveGeneticVariance β_shared ≠ 0 := ne_of_gt h_shared_nonzero
  have h_var_y_ne : var_y ≠ 0 := ne_of_gt h_var_y
  field_simp [h_shared_ne, h_var_y_ne]

/-- **Fundamental portability limit from target-private SNP effects.**
    If the target architecture contains an orthogonal target-private effect
    component, the transferred source score can explain at most the shared
    heritability. The missing heritability is exactly the private target
    component, not an artifact of finite sample size. -/
theorem fundamental_portability_limit
    {m : ℕ}
    (β_shared β_private : Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_shared_nonzero : 0 < additiveGeneticVariance β_shared)
    (h_orth : dotProduct β_shared β_private = 0) :
    transportedTargetR2DiagonalLD β_shared (fun i ↦ β_shared i + β_private i) var_y +
      additiveHeritability β_private var_y =
        additiveHeritability (fun i ↦ β_shared i + β_private i) var_y := by
  rw [transportedTargetR2DiagonalLD_eq_sharedHeritability_of_orthogonal_private
    β_shared β_private var_y h_var_y h_shared_nonzero h_orth]
  unfold additiveHeritability
  rw [additiveGeneticVariance_add_of_orthogonal β_shared β_private h_orth]
  have h_var_y_ne : var_y ≠ 0 := ne_of_gt h_var_y
  field_simp [h_var_y_ne]

/-- **No free lunch for portability when source and target SNP effects are
orthogonal.**
    In the standardized diagonal-LD model, zero source-target effect overlap
    forces the transported target `R²` to be exactly zero. -/
theorem no_free_lunch_portability
    {m : ℕ}
    (β_source β_target : Fin m → ℝ)
    (var_y : ℝ)
    (h_orth : dotProduct β_source β_target = 0) :
    transportedTargetR2DiagonalLD β_source β_target var_y = 0 := by
  unfold transportedTargetR2DiagonalLD transportedTargetR2SharedLD pgsR2
    sharedLDGeneticVariance Descent.Core.squaredShare
  rw [pgsPhenoCov_standardizedDiagonalLD, pgsPhenoCov_self_standardizedDiagonalLD]
  have hcross : (∑ i : Fin m, β_source i * β_target i) = 0 := by
    simpa [dotProduct] using h_orth
  rw [hcross]
  simp

end InformationTheoreticLimits


/-!
## Equity Implications

The paper discusses equitable applications of PGS. We formalize
the key equity-relevant theoretical results.
-/

section EquityImplications

/-- **Portability gap as a measure of inequity.**
    The portability gap = R²_source - R²_target measures the
    disadvantage faced by individuals in the target population. -/
noncomputable def portabilityGap (r2_source r2_target : ℝ) : ℝ :=
  Descent.Core.difference r2_source r2_target

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem portabilityGap_at_reference_point :
    portabilityGap 3 1 = 2 := by
  norm_num [portabilityGap,
      Descent.Core.difference]


/-- **Portability gap is always non-negative under drift.** -/
theorem portability_gap_nonneg
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS ≤ fstT) (hfstT : fstT ≤ 1) :
    0 ≤ portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fstT) := by
  unfold portabilityGap Descent.Core.difference
  by_cases h : fstS = fstT
  · simp [h]
  · have hfst_strict : fstS < fstT := lt_of_le_of_ne hfst h
    exact le_of_lt (sub_pos.mpr
      (drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst_strict hfstT))

/-- **Portability gap increases with genetic distance from GWAS.** -/
theorem portability_gap_increases_with_distance
    (V_A V_E fstS fstT₁ fstT₂ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst₂ : fstT₁ < fstT₂) (hfstT₂ : fstT₂ ≤ 1) :
    portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fstT₁) <
      portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fstT₂) := by
  unfold portabilityGap Descent.Core.difference
  have h1 : presentDayR2 V_A V_E fstT₂ < presentDayR2 V_A V_E fstT₁ :=
    drift_degrades_R2 V_A V_E fstT₁ fstT₂ hVA hVE hfst₂ hfstT₂
  linarith

/-- **Diversifying GWAS reduces maximum portability gap.**
    If multi-ancestry GWAS reduces the effective Fst for the
    worst-off population, the maximum portability gap decreases.

    This formalizes the argument for GWAS diversification as
    an equity intervention. -/
theorem diversity_reduces_max_gap
    (V_A V_E fstS fst_worst_single fst_worst_multi : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_single_bound : fst_worst_single ≤ 1)
    (h_improvement : fst_worst_multi < fst_worst_single) :
    portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fst_worst_multi) <
      portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fst_worst_single) :=
  -- Diversification lowers the worst population's effective `Fst`, and "the gap grows with
  -- distance" read backwards is exactly that. The two were one theorem with the target pair
  -- renamed, proved twice.
  portability_gap_increases_with_distance V_A V_E fstS fst_worst_multi fst_worst_single
    hVA hVE h_improvement h_single_bound

end EquityImplications


/-!
## Variant Count and Estimation Noise

We formalize how the number of variants and effect estimation approach
affect portability noise and stability.
-/

section VariantCountAndEstimationNoise

/-- Per-variant contribution to the sampling variance of a portability estimate. -/
noncomputable def portabilityNoiseVariance (variantCount : ℕ) (varianceScale : ℝ) : ℝ :=
  varianceScale / (variantCount : ℝ)

/-- **More variants strictly reduce portability noise.**  At fixed positive per-variant
variance scale, the `1 / m` law is strictly decreasing in the number of variants. -/
theorem portabilityNoiseVariance_strictAnti
    (m₁ m₂ : ℕ) (varianceScale : ℝ)
    (hm : m₁ < m₂) (h_variance : 0 < varianceScale)
    (hm₁ : 0 < m₁) :
    portabilityNoiseVariance m₂ varianceScale <
      portabilityNoiseVariance m₁ varianceScale := by
  unfold portabilityNoiseVariance
  apply div_lt_div_of_pos_left h_variance
  · exact Nat.cast_pos.mpr hm₁
  · exact Nat.cast_lt.mpr hm

/-- Portability noise is positive exactly in the biologically meaningful positive-variance,
nonempty-panel regime. -/
theorem portabilityNoiseVariance_pos
    (m : ℕ) (varianceScale : ℝ)
    (h_variance : 0 < varianceScale) (hm : 0 < m) :
    0 < portabilityNoiseVariance m varianceScale := by
  exact div_pos h_variance (Nat.cast_pos.mpr hm)

/-- **Doubling the variant count exactly halves portability noise.**  This is the actionable
finite-panel consequence of the `1 / m` law; it makes no positivity assumption on the variance
scale because the identity is algebraic. -/
theorem portabilityNoiseVariance_two_mul
    (m : ℕ) (varianceScale : ℝ) (hm : 0 < m) :
    portabilityNoiseVariance (2 * m) varianceScale =
      portabilityNoiseVariance m varianceScale / 2 := by
  unfold portabilityNoiseVariance
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  norm_num [Nat.cast_mul]
  field_simp [hm']

/-- **Shrinkage regularization dampens portability noise.**
    Bayesian shrinkage pulls small effects toward zero,
    reducing the impact of LD-specific noise on portability. -/
theorem sq_mul_le_sq_mul_of_abs_le
    (β_raw β_shrunk σ_sq_noise : ℝ)
    (h_shrunk : |β_shrunk| ≤ |β_raw|)
    (hσ : 0 < σ_sq_noise) :
    β_shrunk ^ 2 * σ_sq_noise ≤ β_raw ^ 2 * σ_sq_noise := by
  apply mul_le_mul_of_nonneg_right _ (le_of_lt hσ)
  nlinarith [sq_abs β_shrunk, sq_abs β_raw, abs_nonneg β_shrunk, abs_nonneg β_raw]

end VariantCountAndEstimationNoise

end Descent
