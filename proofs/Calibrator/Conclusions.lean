/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability

namespace Calibrator

universe u

open scoped InnerProductSpace
open InnerProductSpace
open MeasureTheory

/-!
=================================================================
## Bayesian Decision Theory: Brier Score Optimality
=================================================================

This section formalizes the decision-theoretic justification for using
the **Posterior Mean** rather than the **MAP estimate** (Mode) for
probabilistic predictions.

### The Problem

In calibrated prediction, we have uncertainty about the linear predictor η.
Given η ~ P(η), we want to predict the probability p = P(Y=1).

Two natural choices:
1. **Mode prediction**: p̂ = sigmoid(E[η])  -- plug in the MAP estimate
2. **Mean prediction**: p̂ = E[sigmoid(η)]  -- integrate over uncertainty

These are NOT equal due to Jensen's inequality (sigmoid is nonlinear).

### What is actually proved

Two separate things, and it matters which is which.

1. **Properness of the Brier score** (`brierScore_minimized_at_true_prob`,
   `brierScore_strict_minimum`): among all constant predictions `p`, the expected
   Bernoulli(π) squared error is uniquely minimised at `p = π`. This is proved outright.
2. **Strict concavity of `sigmoid` on `[0, ∞)`** (`calibration_shrinkage`): for a
   non-degenerate `X > 0`, `E[σ(X)] < σ(E[X])`, by Jensen. Also proved outright.

Composing the two gives `posterior_mean_strictly_beats_mode_of_jensen`: the mean
prediction strictly beats the mode prediction, with the *gap* between them derived
rather than assumed.

What is **not** proved anywhere in this file is the law of iterated expectations
`π = E[σ(η)]`. No outcome variable and no conditional expectation is formalised here,
so that identification enters as an explicit hypothesis of the composed theorem. The
decision-theoretic reading — "integrate over posterior uncertainty rather than plugging
in the MAP estimate" — is therefore conditional on that hypothesis.
-/

section BrierScore

/-! ### Definition of Brier Score -/

/-- The Brier Score measures squared error between predicted probability and outcome.
    For a binary outcome y ∈ {0, 1} and prediction p ∈ [0, 1]:
    BS(p, y) = (y - p)²

    This is the standard proper scoring rule for probability forecasts. -/
noncomputable def brierScore (p : ℝ) (y : ℝ) : ℝ := (y - p) ^ 2

/-- Expected Brier Score when Y is Bernoulli(π).
    E[(Y - p)²] = π(1-p)² + (1-π)p²

    This is the loss we want to minimize by choosing p optimally. -/
noncomputable def expectedBrierScore (p : ℝ) (π : ℝ) : ℝ :=
  π * (1 - p) ^ 2 + (1 - π) * p ^ 2

/-- The expected Brier score can be rewritten as:
    E[(Y - p)²] = π - 2πp + p²
    This form makes it clear it's a quadratic in p. -/
theorem expectedBrierScore_quadratic (p π : ℝ) :
    expectedBrierScore p π = π - 2 * π * p + p ^ 2 := by
  unfold expectedBrierScore
  ring

/-- The derivative of expected Brier score with respect to p is:
    d/dp E[(Y-p)²] = -2π + 2p = 2(p - π)

    Setting this to zero gives p* = π. -/
theorem expectedBrierScore_deriv (p π : ℝ) :
    deriv (fun x : ℝ ↦ expectedBrierScore x π) p = 2 * (p - π) := by
  have h_eq : (fun x : ℝ ↦ expectedBrierScore x π) = fun x : ℝ ↦ π - 2 * π * x + x ^ 2 := by
    ext x
    exact expectedBrierScore_quadratic x π
  rw [h_eq]
  have hd1 : DifferentiableAt ℝ (fun x : ℝ ↦ π - 2 * π * x) p := by
    apply DifferentiableAt.sub
    · exact differentiableAt_const π
    · apply DifferentiableAt.const_mul
      exact differentiableAt_id
  have hd2 : DifferentiableAt ℝ (fun x : ℝ ↦ x ^ 2) p :=
    differentiableAt_id.pow 2
  have h_deriv_add : deriv (fun x : ℝ ↦ (π - 2 * π * x) + x ^ 2) p = deriv (fun x : ℝ ↦ π - 2 * π * x) p + deriv (fun x : ℝ ↦ x ^ 2) p :=
    deriv_add hd1 hd2
  have h_eq_add : (fun x : ℝ ↦ π - 2 * π * x + x ^ 2) = (fun x : ℝ ↦ (π - 2 * π * x) + x ^ 2) := rfl
  rw [h_eq_add, h_deriv_add]
  have hd1_sub1 : DifferentiableAt ℝ (fun x : ℝ ↦ π) p := differentiableAt_const π
  have hd1_sub2 : DifferentiableAt ℝ (fun x : ℝ ↦ 2 * π * x) p := differentiableAt_id.const_mul (2 * π)
  have h_deriv_sub : deriv (fun x : ℝ ↦ π - 2 * π * x) p = deriv (fun x : ℝ ↦ π) p - deriv (fun x : ℝ ↦ 2 * π * x) p :=
    deriv_sub hd1_sub1 hd1_sub2
  rw [h_deriv_sub]
  rw [deriv_const]
  have h_deriv_const_mul : deriv (fun x : ℝ ↦ 2 * π * x) p = 2 * π * deriv (fun x : ℝ ↦ x) p :=
    deriv_const_mul (2 * π) differentiableAt_id
  rw [h_deriv_const_mul]
  have h_deriv_id : deriv (fun x : ℝ ↦ x) p = 1 :=
    deriv_id p
  rw [h_deriv_id]
  have h_deriv_pow : deriv (fun x : ℝ ↦ x ^ 2) p = 2 * p ^ (2 - 1) * deriv (fun x : ℝ ↦ x) p :=
    deriv_pow (n := 2) differentiableAt_id
  rw [h_deriv_pow]
  rw [h_deriv_id]
  ring

/-! ### Brier Score is a Proper Scoring Rule -/

/-- **Key Theorem**: The Brier Score is minimized when the predicted probability
    equals the true probability.

    For any true probability π ∈ [0,1], the expected Brier score E[(Y-p)²]
    is uniquely minimized at p = π.

    Proof: The expected score is quadratic in p with positive leading coefficient,
    so it has a unique minimum where the derivative equals zero, i.e., p = π. -/
theorem brierScore_minimized_at_true_prob (π : ℝ) :
    ∀ p : ℝ, expectedBrierScore π π ≤ expectedBrierScore p π := by
  intro p
  -- Expand both sides
  rw [expectedBrierScore_quadratic, expectedBrierScore_quadratic]
  -- At p = π: π - 2π² + π² = π - π² = π(1-π)
  -- At general p: π - 2πp + p²
  -- Difference: (π - 2πp + p²) - (π - π²) = p² - 2πp + π² = (p - π)²
  have h : π - 2 * π * p + p ^ 2 - (π - 2 * π * π + π ^ 2) = (p - π) ^ 2 := by ring
  linarith [sq_nonneg (p - π)]

/-- The Brier score at the true probability simplifies to π(1-π),
    which is the irreducible variance of a Bernoulli(π) variable. -/
theorem brierScore_at_true_prob (π : ℝ) :
    expectedBrierScore π π = π * (1 - π) := by
  unfold expectedBrierScore
  ring

/-- Strict improvement: if p ≠ π, the Brier score is strictly worse. -/
theorem brierScore_strict_minimum (π p : ℝ) (hp : p ≠ π) :
    expectedBrierScore π π < expectedBrierScore p π := by
  rw [expectedBrierScore_quadratic, expectedBrierScore_quadratic]
  have h : π - 2 * π * p + p ^ 2 - (π - 2 * π * π + π ^ 2) = (p - π) ^ 2 := by ring
  have hne : p - π ≠ 0 := sub_ne_zero.mpr hp
  have hsq : (p - π) ^ 2 > 0 := sq_pos_of_ne_zero hne
  linarith

/-- Exact population Brier risk of a calibrated predictor (`q = η`). -/
noncomputable def exactBrierRiskOfCalibrated {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (η : Z → ℝ) : ℝ :=
  ∫ z, expectedBrierScore (η z) (η z) ∂μ

/-- Exact calibrated Brier-risk identity: pointwise Bernoulli variance integrated over the population. -/
theorem exactBrierRiskOfCalibrated_eq_integral {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (η : Z → ℝ) :
    exactBrierRiskOfCalibrated μ η = ∫ z, η z * (1 - η z) ∂μ := by
  unfold exactBrierRiskOfCalibrated
  refine integral_congr_ae ?_
  filter_upwards with z
  simp [brierScore_at_true_prob]

/-! ### Posterior Mean Optimality -/

/-- The posterior mean prediction for a binary outcome.

    Given a distribution over the linear predictor η (represented by its mean μ
    and the expected value of sigmoid(η)), the posterior mean prediction is
    E[sigmoid(η)], NOT sigmoid(E[η]).

    This structure captures the key distinction between Mode and Mean prediction. -/
structure PosteriorPrediction where
  /- The posterior mean of η (the linear predictor) -/
  η_mean : ℝ
  /-- The posterior mean of sigmoid(η) = E[sigmoid(η)] -/
  prob_mean : ℝ

/-- **The mode prediction, `sigmoid(E[η])`.**

This was a field of `PosteriorPrediction` pinned by the hypothesis
`mode_is_sigmoid_of_mean : prob_mode = 1 / (1 + exp (-η_mean))`. Carrying it as a free
field meant the structure had a degree of freedom the equation immediately removed, and
every consumer had to be handed the equation to make use of it. Computing it makes
`mode_is_sigmoid_of_mean` an `rfl` theorem, and the distinction this structure exists to
draw — that `prob_mean` is `E[sigmoid(η)]` while the mode is `sigmoid(E[η])` — is now
carried by the shape of the definitions rather than by an assumption. -/
noncomputable def PosteriorPrediction.prob_mode (pred : PosteriorPrediction) : ℝ :=
  1 / (1 + Real.exp (-pred.η_mean))

theorem PosteriorPrediction.mode_is_sigmoid_of_mean (pred : PosteriorPrediction) :
    pred.prob_mode = 1 / (1 + Real.exp (-pred.η_mean)) := rfl

/-- **Brier properness, specialised to a predictor whose value is assumed to be the true
probability. NOT the Bayesian posterior-mean theorem, which this file does not prove.**

This was called `posterior_mean_optimal` and documented as "**Main Theorem**: The Posterior
Mean is the Bayes-optimal predictor under Brier Score", with a proof sketch whose step 2 was
"the true `π = E[sigmoid(η)]` **by the law of iterated expectations**". That step is not
proved here. **It is the hypothesis `h_true`.**

What is actually established: if `π` happens to equal `pred.prob_mean`, then predicting
`pred.prob_mean` beats predicting anything else — which is the properness of the Brier
score, already available as `brierScore_minimized_at_true_prob`, with `prob_mean`
substituted for the true probability. `prob_mean` is a bare real field of
`PosteriorPrediction`; nothing in this development makes it an expectation of anything.

**What would close the gap**, so a reader knows what is missing rather than believing it
closed:

1. a formalised posterior distribution over `η` — a measure, not a pair of reals;
2. `prob_mean` *defined* as `∫ sigmoid(η) dμ(η)` rather than posited;
3. the law of iterated expectations, `E[Y | X] = E[E[Y | X, η] | X]`, proved for that
   measure, which is what would discharge `h_true` instead of assuming it.

Until those exist, this is a correct conditional theorem about Brier scores and carries no
Bayesian content. The rename is the point: the previous name asserted the conclusion that
steps 1–3 would have licensed. -/
theorem brier_le_at_prob_mean_when_mean_is_true (pred : PosteriorPrediction)
    (π : ℝ) (_hπ : 0 ≤ π ∧ π ≤ 1)
    (h_true : π = pred.prob_mean) :
    expectedBrierScore pred.prob_mean π ≤ expectedBrierScore pred.prob_mode π := by
  -- The posterior mean IS the true probability, so by the proper scoring rule,
  -- it achieves the minimum Brier score
  rw [← h_true]
  exact brierScore_minimized_at_true_prob π pred.prob_mode

/-- Strict Brier properness under the same assumed identification: if `π` is assumed equal
to `pred.prob_mean` and the mode differs from it, the mode scores strictly worse.

Same scope as the theorem above, and the same gap: `h_true` is the law of iterated
expectations supplied as a hypothesis, not derived. This says nothing about posteriors. -/
theorem brier_lt_at_prob_mean_when_mean_is_true (pred : PosteriorPrediction)
    (π : ℝ) (h_true : π = pred.prob_mean)
    (h_uncertainty : pred.prob_mean ≠ pred.prob_mode) :
    expectedBrierScore pred.prob_mean π < expectedBrierScore pred.prob_mode π := by
  rw [← h_true]
  have h_ne : pred.prob_mode ≠ π := by rw [h_true]; exact h_uncertainty.symm
  exact brierScore_strict_minimum π pred.prob_mode h_ne

/-! ### Jensen's Inequality and the Direction of Bias -/

/-- The sigmoid function (logistic function).
    σ(x) = 1 / (1 + e^(-x)) -/
noncomputable def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- Sigmoid is bounded in (0, 1). -/
theorem sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  unfold sigmoid
  apply div_pos one_pos
  have h : Real.exp (-x) > 0 := Real.exp_pos (-x)
  linarith

theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  unfold sigmoid
  rw [div_lt_one]
  · have h : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith
  · have h : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith

/-- Sigmoid at zero equals 1/2. -/
theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  unfold sigmoid
  simp only [neg_zero, Real.exp_zero]
  norm_num

/-- Sigmoid is greater than 1/2 for positive inputs (monotonicity). -/
theorem sigmoid_gt_half {x : ℝ} (hx : x > 0) : sigmoid x > 1 / 2 := by
  unfold sigmoid
  have hexp_lt : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hexp_pos : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 0 := by linarith
  have hdenom_lt : 1 + Real.exp (-x) < 2 := by linarith
  -- Want: 1 / (1 + exp(-x)) > 1/2
  -- Equivalent to: 1 + exp(-x) < 2 (since 1/a < 1/b ↔ b < a for positive a, b)
  have h2pos : (2 : ℝ) > 0 := by norm_num
  rw [gt_iff_lt, one_div_lt_one_div h2pos hdenom]
  exact hdenom_lt

/-- Sigmoid is less than 1/2 for negative inputs (monotonicity). -/
theorem sigmoid_lt_half {x : ℝ} (hx : x < 0) : sigmoid x < 1 / 2 := by
  unfold sigmoid
  have hexp_gt : Real.exp (-x) > 1 := by
    rw [gt_iff_lt, ← Real.exp_zero]
    exact Real.exp_strictMono (by linarith : (0 : ℝ) < -x)
  have hexp_pos : Real.exp (-x) > 0 := Real.exp_pos (-x)
  have hdenom : 1 + Real.exp (-x) > 0 := by linarith
  have hdenom_gt : 1 + Real.exp (-x) > 2 := by linarith
  -- Want: 1 / (1 + exp(-x)) < 1/2
  -- Equivalent to: 2 < 1 + exp(-x) (since 1/a < 1/b ↔ b < a for positive a, b)
  have h2pos : (2 : ℝ) > 0 := by norm_num
  rw [one_div_lt_one_div hdenom h2pos]
  exact hdenom_gt

/-- Sigmoid is strictly monotone increasing. -/
theorem sigmoid_monotone : StrictMono sigmoid := by
  intro x y hxy
  unfold sigmoid
  have hx_pos : 1 + Real.exp (-x) > 0 := by have := Real.exp_pos (-x); linarith
  have hy_pos : 1 + Real.exp (-y) > 0 := by have := Real.exp_pos (-y); linarith
  rw [one_div_lt_one_div hx_pos hy_pos]
  have h1 : Real.exp (-y) < Real.exp (-x) := Real.exp_strictMono (by linarith : -y < -x)
  linarith

lemma differentiable_sigmoid (x : ℝ) : DifferentiableAt ℝ sigmoid x := by
  unfold sigmoid
  apply DifferentiableAt.div
  · exact differentiableAt_const _
  · apply DifferentiableAt.add
    · exact differentiableAt_const _
    · apply DifferentiableAt.exp
      exact differentiableAt_id.neg
  · have : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith

lemma deriv_sigmoid (x : ℝ) : deriv sigmoid x = sigmoid x * (1 - sigmoid x) := by
  have h_diff : DifferentiableAt ℝ (fun x ↦ 1 + Real.exp (-x)) x := by
    apply DifferentiableAt.add
    · exact differentiableAt_const _
    · apply DifferentiableAt.exp
      exact differentiableAt_id.neg
  have h_ne : 1 + Real.exp (-x) ≠ 0 := by
    have : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith
  unfold sigmoid
  simp only [one_div]
  apply HasDerivAt.deriv
  convert HasDerivAt.inv (c := fun x ↦ 1 + Real.exp (-x)) (by
      apply HasDerivAt.add
      · apply hasDerivAt_const
      · apply HasDerivAt.exp
        apply HasDerivAt.neg
        apply hasDerivAt_id
    ) h_ne using 1
  field_simp [h_ne]
  ring

lemma deriv2_sigmoid (x : ℝ) : deriv (deriv sigmoid) x = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x) := by
  have h_eq : deriv sigmoid = fun x ↦ sigmoid x * (1 - sigmoid x) := by
    ext y; rw [deriv_sigmoid]
  rw [h_eq]
  apply HasDerivAt.deriv
  have h_has_deriv_sig : HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
    rw [← deriv_sigmoid]
    exact DifferentiableAt.hasDerivAt (differentiable_sigmoid x)
  convert HasDerivAt.mul h_has_deriv_sig (HasDerivAt.sub (hasDerivAt_const x (1:ℝ)) h_has_deriv_sig) using 1
  simp; ring

lemma sigmoid_strictConcaveOn_Ici : StrictConcaveOn ℝ (Set.Ici 0) sigmoid := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
  · have h_diff : Differentiable ℝ sigmoid := fun x ↦ differentiable_sigmoid x
    exact h_diff.continuous.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    dsimp only [Nat.iterate, Function.comp]
    rw [deriv2_sigmoid]
    apply mul_neg_of_pos_of_neg
    · apply mul_pos (sigmoid_pos x)
      rw [sub_pos]
      exact sigmoid_lt_one x
    · have h := sigmoid_gt_half hx
      linarith

/-- Calibration Shrinkage (Via Jensen's Inequality):
    The sigmoid function is strictly concave on (0, ∞).
    Therefore, for any random variable X with support in (0, ∞) (and non-degenerate),
    by Jensen's Inequality: E[sigmoid(X)] < sigmoid(E[X]).

    Since sigmoid(E[X]) > 0.5 (as E[X] > 0), this implies the expected probability
    ("calibrated probability") is strictly less than the probability at the mean score.
    i.e., The model is "over-confident" if it predicts sigmoid(E[X]).
    The true probability E[sigmoid(X)] is "shrunk" toward 0.5. -/
  theorem calibration_shrinkage {Ω : Type*} [MeasurableSpace Ω] (μ : ℝ)
      (X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
      (h_measurable : Measurable X) (h_integrable : Integrable X P)
      (h_mean : ∫ ω, X ω ∂P = μ)
      (h_support : ∀ᵐ ω ∂P, X ω > 0)
      (h_non_degenerate : ¬ ∀ᵐ ω ∂P, X ω = μ) :
      (∫ ω, sigmoid (X ω) ∂P) < sigmoid μ := by
    have h_mem : ∀ᵐ ω ∂P, X ω ∈ Set.Ici 0 := by
      filter_upwards [h_support] with ω hω
      exact le_of_lt hω
    have h_ae_meas : AEStronglyMeasurable X P := h_measurable.aestronglyMeasurable
    have h_diff : Differentiable ℝ sigmoid := fun x ↦ differentiable_sigmoid x
    have h_cont : ContinuousOn sigmoid (Set.Ici 0) := h_diff.continuous.continuousOn
    have h_int_sigmoid : Integrable (sigmoid ∘ X) P := by
      have h_cont_sig : Continuous sigmoid := Differentiable.continuous (fun x ↦ differentiable_sigmoid x)
      refine Integrable.of_bound (h_cont_sig.comp_aestronglyMeasurable h_ae_meas) (1:ℝ) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · apply le_trans (by norm_num : (-1:ℝ) ≤ 0) (le_of_lt (sigmoid_pos _))
      · exact le_of_lt (sigmoid_lt_one _)
    rcases sigmoid_strictConcaveOn_Ici.ae_eq_const_or_lt_map_average h_cont isClosed_Ici h_mem h_integrable h_int_sigmoid with h_eq | h_lt
    · exfalso
      simp only [average_eq_integral] at h_eq
      rw [h_mean] at h_eq
      exact h_non_degenerate h_eq
    · simp only [average_eq_integral] at h_lt
      rw [h_mean] at h_lt
      exact h_lt
    
end BrierScore

section OracleAndRegret

/-! ### Oracle Comparison at Population Level -/

/-- True conditional probability on feature space `Z`. -/
abbrev TrueCondProb (Z : Type u) := Z → UnitProb

/-- Predictor on feature space `Z`. -/
abbrev ProbPredictor (Z : Type u) := Z → UnitProb

/-- Population risk under Bernoulli mixing with true probability `p(z)`. -/
noncomputable def populationRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (q : ProbPredictor Z) : ℝ :=
  ∫ z, (p z).1 * ℓ (q z).1 true + (1 - (p z).1) * ℓ (q z).1 false ∂μ

/-- Population-level oracle risk over a model class `F`. -/
noncomputable def oracleRisk {α : Type u} (R : α → ℝ) (F : Set α) : ℝ :=
  sInf (R '' F)

/-- Oracle infimum risk for a predictor class `F`. -/
noncomputable def infRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (F : Set (ProbPredictor Z)) : ℝ :=
  oracleRisk (populationRisk μ ℓ p) F

/-- If your class contains the baseline class, its oracle risk is no worse. -/
theorem oracleRisk_mono {α : Type u} (R : α → ℝ) (Fyours Fbaseline : Set α)
    (hsub : Fbaseline ⊆ Fyours)
    (h_bdd : BddBelow (R '' Fyours))
    (h_nonempty_base : (R '' Fbaseline).Nonempty) :
    oracleRisk R Fyours ≤ oracleRisk R Fbaseline := by
  unfold oracleRisk
  refine csInf_le_csInf h_bdd h_nonempty_base ?_
  intro y hy
  rcases hy with ⟨b, hb, rfl⟩
  exact ⟨b, hsub hb, rfl⟩

/-- Reusable monotonicity lemma: if `F ⊆ G`, then `infRisk G ≤ infRisk F`. -/
theorem infRisk_mono {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (F G : Set (ProbPredictor Z))
    (hFG : F ⊆ G)
    (h_bdd : BddBelow ((populationRisk μ ℓ p) '' G))
    (h_nonempty : ((populationRisk μ ℓ p) '' F).Nonempty) :
    infRisk μ ℓ p G ≤ infRisk μ ℓ p F :=
  oracleRisk_mono (R := populationRisk μ ℓ p) (Fyours := G) (Fbaseline := F) hFG h_bdd h_nonempty

/-- Strict oracle improvement from a witness in `Fyours` that beats every baseline member. -/
theorem oracleRisk_strict_of_witness {α : Type u} (R : α → ℝ) (Fyours Fbaseline : Set α)
    (h_bdd : BddBelow (R '' Fyours))
    (h_nonempty_base : (R '' Fbaseline).Nonempty)
    (h_witness : ∃ y ∈ Fyours, ∃ ε > 0, ∀ b ∈ Fbaseline, R y + ε ≤ R b) :
    oracleRisk R Fyours < oracleRisk R Fbaseline := by
  rcases h_witness with ⟨y, hy_mem, ε, hε_pos, hy_margin⟩
  have h_left : oracleRisk R Fyours ≤ R y := by
    unfold oracleRisk
    exact csInf_le h_bdd ⟨y, hy_mem, rfl⟩
  have h_margin_inf : R y + ε ≤ oracleRisk R Fbaseline := by
    unfold oracleRisk
    refine le_csInf h_nonempty_base ?_
    intro b hb
    rcases hb with ⟨b0, hb0, rfl⟩
    exact hy_margin b0 hb0
  have h_right : R y < oracleRisk R Fbaseline := by
    linarith
  exact lt_of_le_of_lt h_left h_right

/-- Bayes risk over a class: `R⋆(F) = inf_{p∈F} R(p)`. -/
noncomputable def BayesRisk {α : Type u} (R : α → ℝ) (F : Set α) : ℝ :=
  oracleRisk R F

/-- Monotonicity under inclusion for Bayes risk. -/
theorem BayesRisk_mono {α : Type u} (R : α → ℝ) (F G : Set α)
    (hFG : F ⊆ G)
    (h_bdd : BddBelow (R '' G))
    (h_nonempty : (R '' F).Nonempty) :
    BayesRisk R G ≤ BayesRisk R F :=
  oracleRisk_mono (R := R) (Fyours := G) (Fbaseline := F) hFG h_bdd h_nonempty

/-! ### Magnitude Certificates: Log Loss (KL) and Brier (L²) -/


/-- Bernoulli log-loss (cross-entropy) at truth `p` and prediction `q`. -/
noncomputable def bernoulliLogLoss (p q : ℝ) : ℝ :=
  -(p * Real.log q + (1 - p) * Real.log (1 - q))

/-- Real-valued Bernoulli KL divergence formula. -/
noncomputable def bernoulliKLReal (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Bernoulli KL on `[0,1]` probabilities. -/
noncomputable def klBernReal (p q : UnitProb) : ℝ :=
  bernoulliKLReal p.1 q.1

theorem bernoulliKLReal_nonneg (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ bernoulliKLReal p q := by
  unfold bernoulliKLReal
  have h1 : Real.log (q / p) ≤ q / p - 1 := by
    apply Real.log_le_sub_one_of_pos
    positivity
  have h2 : Real.log ((1 - q) / (1 - p)) ≤ (1 - q) / (1 - p) - 1 := by
    apply Real.log_le_sub_one_of_pos
    have : 0 < 1 - q := by linarith
    have : 0 < 1 - p := by linarith
    positivity
  have hp_pos : 0 < p := hp0
  have hp1_pos : 0 < 1 - p := by linarith
  have h1_neg : - (p * Real.log (q / p)) ≥ - p * (q / p - 1) := by
    linarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hp_pos)]
  have h2_neg : - ((1 - p) * Real.log ((1 - q) / (1 - p))) ≥ - (1 - p) * ((1 - q) / (1 - p) - 1) := by
    linarith [mul_le_mul_of_nonneg_left h2 (le_of_lt hp1_pos)]
  have h_log_inv1 : Real.log (p / q) = - Real.log (q / p) := by
    rw [Real.log_div (hp0.ne') (hq0.ne'), Real.log_div (hq0.ne') (hp0.ne')]
    ring
  have h_log_inv2 : Real.log ((1 - p) / (1 - q)) = - Real.log ((1 - q) / (1 - p)) := by
    have h1p : 1 - p ≠ 0 := by linarith
    have h1q : 1 - q ≠ 0 := by linarith
    rw [Real.log_div h1p h1q, Real.log_div h1q h1p]
    ring
  rw [h_log_inv1, h_log_inv2]
  calc
    p * -Real.log (q / p) + (1 - p) * -Real.log ((1 - q) / (1 - p))
      = - (p * Real.log (q / p)) - ((1 - p) * Real.log ((1 - q) / (1 - p))) := by ring
    _ ≥ - p * (q / p - 1) - (1 - p) * ((1 - q) / (1 - p) - 1) := by linarith
    _ = - (p * (q / p)) + p - ((1 - p) * ((1 - q) / (1 - p))) + (1 - p) := by ring
    _ = - q + p - (1 - q) + (1 - p) := by
      have hqp : p * (q / p) = q := by
        rw [mul_div_cancel₀ _ (hp0.ne')]
      have h1qp : (1 - p) * ((1 - q) / (1 - p)) = 1 - q := by
        rw [mul_div_cancel₀ _ (by linarith)]
      rw [hqp, h1qp]
    _ = 0 := by ring

/-- **Strict Gibbs inequality for the Bernoulli KL divergence.**

`bernoulliKLReal_nonneg` above gives one half of Gibbs' inequality. Strictness follows by
using `log x < x - 1` on `x = q / p` whenever `q ≠ p`; the complementary-coordinate term
retains the non-strict bound. -/
theorem bernoulliKLReal_eq_zero_iff (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliKLReal p q = 0 ↔ q = p := by
  constructor
  · intro hzero
    by_contra hqp
    have hratio_ne : q / p ≠ 1 := by
      intro hratio
      apply hqp
      field_simp [hp0.ne'] at hratio
      exact hratio
    have h1 : Real.log (q / p) < q / p - 1 := by
      exact Real.log_lt_sub_one_of_pos (div_pos hq0 hp0) hratio_ne
    have h2 : Real.log ((1 - q) / (1 - p)) ≤ (1 - q) / (1 - p) - 1 := by
      apply Real.log_le_sub_one_of_pos
      exact div_pos (by linarith) (by linarith)
    have h1_neg :
        -p * Real.log (q / p) > -p * (q / p - 1) := by
      nlinarith [mul_lt_mul_of_pos_left h1 hp0]
    have h2_neg :
        -(1 - p) * Real.log ((1 - q) / (1 - p)) ≥
          -(1 - p) * ((1 - q) / (1 - p) - 1) := by
      have hp_compl : 0 ≤ 1 - p := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hp_compl]
    have h_log_inv1 : Real.log (p / q) = -Real.log (q / p) := by
      rw [Real.log_div hp0.ne' hq0.ne', Real.log_div hq0.ne' hp0.ne']
      ring
    have h_log_inv2 :
        Real.log ((1 - p) / (1 - q)) = -Real.log ((1 - q) / (1 - p)) := by
      have h1p : 1 - p ≠ 0 := by linarith
      have h1q : 1 - q ≠ 0 := by linarith
      rw [Real.log_div h1p h1q, Real.log_div h1q h1p]
      ring
    have hpositive : 0 < bernoulliKLReal p q := by
      unfold bernoulliKLReal
      rw [h_log_inv1, h_log_inv2]
      calc
        p * -Real.log (q / p) + (1 - p) * -Real.log ((1 - q) / (1 - p))
            > -p * (q / p - 1) -
                (1 - p) * ((1 - q) / (1 - p) - 1) := by
              nlinarith
        _ = -q + p - (1 - q) + (1 - p) := by
          have hqp_cancel : p * (q / p) = q := by
            rw [mul_div_cancel₀ _ hp0.ne']
          have hcompl_cancel : (1 - p) * ((1 - q) / (1 - p)) = 1 - q := by
            rw [mul_div_cancel₀ _ (by linarith)]
          calc
            -p * (q / p - 1) - (1 - p) * ((1 - q) / (1 - p) - 1) =
                -(p * (q / p)) + p -
                  ((1 - p) * ((1 - q) / (1 - p))) + (1 - p) := by ring
            _ = -q + p - (1 - q) + (1 - p) := by
              rw [hqp_cancel, hcompl_cancel]
        _ = 0 := by ring
    exact hpositive.ne' hzero
  · intro h
    subst q
    simp [bernoulliKLReal]

/-- `UnitProb` form of `bernoulliKLReal_eq_zero_iff`. -/
theorem klBernReal_eq_zero_iff (p q : UnitProb)
    (hp : 0 < p.1 ∧ p.1 < 1) (hq : 0 < q.1 ∧ q.1 < 1) :
    klBernReal p q = 0 ↔ q = p := by
  unfold klBernReal
  have hiff : bernoulliKLReal p.1 q.1 = 0 ↔ q.1 = p.1 :=
    bernoulliKLReal_eq_zero_iff p.1 q.1 hp.1 hp.2 hq.1 hq.2
  constructor
  · intro h
    exact Subtype.ext (hiff.mp h)
  · intro h
    exact hiff.mpr (by rw [h])

/-- Pointwise log-loss regret equals Bernoulli KL. -/
theorem logLoss_regret_eq_kl_pointwise (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliLogLoss p q - bernoulliLogLoss p p = bernoulliKLReal p q := by
  have hp_ne : p ≠ 0 := hp0.ne'
  have hq_ne : q ≠ 0 := hq0.ne'
  have hp1_ne : 1 - p ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp1).symm
  have hq1_ne : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hq1).symm
  unfold bernoulliLogLoss bernoulliKLReal
  rw [Real.log_div hp_ne hq_ne, Real.log_div hp1_ne hq1_ne]
  ring

/-- Population log-loss regret. -/
noncomputable def logLossRegret {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, bernoulliLogLoss (p z) (q z) - bernoulliLogLoss (p z) (p z) ∂μ

/-- Population Bernoulli KL certificate. -/
noncomputable def logLossKLCertificate {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, bernoulliKLReal (p z) (q z) ∂μ

/-- Regret identity for log-loss at population level. -/
theorem logLoss_regret_eq_integral_kl {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ)
    (hp : ∀ z, 0 < p z ∧ p z < 1)
    (hq : ∀ z, 0 < q z ∧ q z < 1) :
    logLossRegret μ p q = logLossKLCertificate μ p q := by
  unfold logLossRegret logLossKLCertificate
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z ↦ by
    exact logLoss_regret_eq_kl_pointwise (p z) (q z) (hp z).1 (hp z).2 (hq z).1 (hq z).2)

/-- Method-agnostic main theorem:
`R_log(q) - R_log(p) = ∫ klBernReal(p(z), q(z)) dμ`. -/
theorem logRisk_regret_eq_expected_klBernReal {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hq : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    (∫ z, bernoulliLogLoss (p z).1 (q z).1 - bernoulliLogLoss (p z).1 (p z).1 ∂μ)
      = ∫ z, klBernReal (p z) (q z) ∂μ := by
  unfold klBernReal
  exact logLoss_regret_eq_integral_kl μ (fun z ↦ (p z).1) (fun z ↦ (q z).1) hp hq

/-- Method-comparison magnitude identity:
the log-risk gap equals the KL-gap integral. -/
theorem logRisk_gap_eq_integral_klGap {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p qBaseline qYours : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hqBaseline : ∀ z, 0 < (qBaseline z).1 ∧ (qBaseline z).1 < 1)
    (hqYours : ∀ z, 0 < (qYours z).1 ∧ (qYours z).1 < 1) :
    (∫ z, bernoulliLogLoss (p z).1 (qBaseline z).1 - bernoulliLogLoss (p z).1 (qYours z).1 ∂μ)
      = ∫ z, (klBernReal (p z) (qBaseline z) - klBernReal (p z) (qYours z)) ∂μ := by
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z ↦ by
    have hB := logLoss_regret_eq_kl_pointwise (p z).1 (qBaseline z).1
      (hp z).1 (hp z).2 (hqBaseline z).1 (hqBaseline z).2
    have hY := logLoss_regret_eq_kl_pointwise (p z).1 (qYours z).1
      (hp z).1 (hp z).2 (hqYours z).1 (hqYours z).2
    unfold klBernReal
    linarith [hB, hY])

/-- Corollary: nonnegativity of log-loss regret from pointwise nonnegativity of `klBernReal`. -/
theorem logRisk_regret_nonneg {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hq : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    0 ≤ (∫ z, bernoulliLogLoss (p z).1 (q z).1 - bernoulliLogLoss (p z).1 (p z).1 ∂μ) := by
  rw [logRisk_regret_eq_expected_klBernReal μ p q hp hq]
  have h_kl_nonneg : ∀ z, 0 ≤ klBernReal (p z) (q z) := by
    intro z
    unfold klBernReal
    exact bernoulliKLReal_nonneg (p z).1 (q z).1 (hp z).1 (hp z).2 (hq z).1 (hq z).2
  exact integral_nonneg h_kl_nonneg

/-- Corollary: strictness criterion.
Regret is zero iff `q = p` almost everywhere. The pointwise KL characterization it needs
is `klBernReal_eq_zero_iff`, proved (modulo the admitted strictness half) above rather
than assumed here. -/
theorem logRisk_regret_zero_iff_ae_eq {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hq : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)
    (h_int : Integrable (fun z ↦ klBernReal (p z) (q z)) μ) :
    (∫ z, bernoulliLogLoss (p z).1 (q z).1 - bernoulliLogLoss (p z).1 (p z).1 ∂μ) = 0
      ↔ q =ᵐ[μ] p := by
  have h_kl_zero_iff : ∀ z, klBernReal (p z) (q z) = 0 ↔ q z = p z := fun z ↦
    klBernReal_eq_zero_iff (p z) (q z) (hp z) (hq z)
  have h_kl_nonneg : ∀ z, 0 ≤ klBernReal (p z) (q z) := by
    intro z
    unfold klBernReal
    exact bernoulliKLReal_nonneg (p z).1 (q z).1 (hp z).1 (hp z).2 (hq z).1 (hq z).2
  rw [logRisk_regret_eq_expected_klBernReal μ p q hp hq]
  constructor
  · intro h0
    have h_ae_zero : (fun z ↦ klBernReal (p z) (q z)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg h_kl_nonneg h_int).mp h0
    filter_upwards [h_ae_zero] with z hz
    exact (h_kl_zero_iff z).1 hz
  · intro hqeqp
    have h_ae_zero : (fun z ↦ klBernReal (p z) (q z)) =ᵐ[μ] 0 := by
      filter_upwards [hqeqp] with z hz
      exact (h_kl_zero_iff z).2 hz
    rw [integral_congr_ae h_ae_zero]
    simp

/-- Pointwise Brier regret identity (L² certificate). -/
theorem brier_regret_pointwise (p q : ℝ) :
    expectedBrierScore q p - expectedBrierScore p p = (q - p) ^ 2 := by
  unfold expectedBrierScore
  ring

/-- Population Brier regret. -/
noncomputable def brierRegret {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, expectedBrierScore (q z) (p z) - expectedBrierScore (p z) (p z) ∂μ

/-- Population L² certificate for Brier regret. -/
noncomputable def brierL2Certificate {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, (q z - p z) ^ 2 ∂μ

theorem brier_regret_eq_l2_certificate {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) :
    brierRegret μ p q = brierL2Certificate μ p q := by
  unfold brierRegret brierL2Certificate
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z ↦ by simpa using brier_regret_pointwise (p z) (q z))

/-- Method-agnostic Brier identity on `p,q : Z → [0,1]`:
regret equals the `L²` distance. -/
theorem brier_regret_eq_l2_probPredictor {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z) :
    (∫ z, expectedBrierScore (q z).1 (p z).1 - expectedBrierScore (p z).1 (p z).1 ∂μ)
      = ∫ z, ((p z).1 - (q z).1) ^ 2 ∂μ := by
  have h := brier_regret_eq_l2_certificate μ (fun z ↦ (p z).1) (fun z ↦ (q z).1)
  calc
    (∫ z, expectedBrierScore (q z).1 (p z).1 - expectedBrierScore (p z).1 (p z).1 ∂μ)
        = ∫ z, ((q z).1 - (p z).1) ^ 2 ∂μ := by
          simpa [brierRegret, brierL2Certificate] using h
    _ = ∫ z, ((p z).1 - (q z).1) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun z ↦ by ring)

/-! ### Clean Bayes-Optimal Target Statements -/

/-- Population log-loss risk for Bernoulli truth `η`. -/
noncomputable def logRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) : ℝ :=
  ∫ z, bernoulliLogLoss (η z).1 (q z).1 ∂μ

/-- Population Brier risk for Bernoulli truth `η`. -/
noncomputable def brierRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) : ℝ :=
  ∫ z, expectedBrierScore (q z).1 (η z).1 ∂μ

/-- Covariate-shift transport bound for Brier risk under a bounded density ratio.
If `μT = w · μS` and `w(z) ≤ M`, then `R_T ≤ M · R_S`. -/
theorem brierRisk_target_le_mul_source_of_withDensity
    {Z : Type u} [MeasurableSpace Z]
    (μS μT : Measure Z)
    (η q : ProbPredictor Z)
    (w : Z → ℝ) (M : ℝ)
    (h_density : μT = μS.withDensity (fun z ↦ ENNReal.ofReal (w z)))
    (hw_meas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) μS)
    (hw_nonneg : ∀ z, 0 ≤ w z)
    (hw_bdd : ∀ z, w z ≤ M)
    (_hM_nonneg : 0 ≤ M)
    (h_int_source : Integrable (fun z ↦ expectedBrierScore (q z).1 (η z).1) μS)
    (h_int_weighted : Integrable (fun z ↦ w z * expectedBrierScore (q z).1 (η z).1) μS) :
    brierRisk μT η q ≤ M * brierRisk μS η q := by
  let ℓ : Z → ℝ := fun z ↦ expectedBrierScore (q z).1 (η z).1
  have hℓ_nonneg : ∀ z, 0 ≤ ℓ z := by
    intro z
    unfold ℓ expectedBrierScore
    have hη0 : 0 ≤ (η z).1 := (η z).2.1
    have hη1 : (η z).1 ≤ 1 := (η z).2.2
    have h1η : 0 ≤ 1 - (η z).1 := by linarith
    nlinarith [sq_nonneg (1 - (q z).1), sq_nonneg ((q z).1), hη0, h1η]
  have h_pointwise : ∀ z, w z * ℓ z ≤ M * ℓ z := by
    intro z
    nlinarith [hw_bdd z, hℓ_nonneg z]
  have h_rw :
      brierRisk μT η q = ∫ z, w z * ℓ z ∂μS := by
    unfold brierRisk
    simp [ℓ]
    rw [h_density]
    have h_lt_top : ∀ᵐ z ∂μS, ENNReal.ofReal (w z) < ⊤ :=
      Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)
    calc
      ∫ z, ℓ z ∂μS.withDensity (fun z ↦ ENNReal.ofReal (w z))
          = ∫ z, ((ENNReal.ofReal (w z)).toReal) • ℓ z ∂μS := by
              simpa using
                (integral_withDensity_eq_integral_toReal_smul₀
                  (μ := μS) (f := fun z ↦ ENNReal.ofReal (w z)) hw_meas h_lt_top ℓ)
      _ = ∫ z, w z * ℓ z ∂μS := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun z ↦ by
              simp [smul_eq_mul, ENNReal.toReal_ofReal (hw_nonneg z)])
  have h_int_Mℓ : Integrable (fun z ↦ M * ℓ z) μS := h_int_source.const_mul M
  have h_mono :
      ∫ z, w z * ℓ z ∂μS ≤ ∫ z, M * ℓ z ∂μS :=
    integral_mono_ae h_int_weighted h_int_Mℓ (Filter.Eventually.of_forall h_pointwise)
  have h_scal :
      (∫ z, M * ℓ z ∂μS) = M * ∫ z, ℓ z ∂μS := by
    simpa using (integral_const_mul M ℓ)
  calc
    brierRisk μT η q = ∫ z, w z * ℓ z ∂μS := h_rw
    _ ≤ ∫ z, M * ℓ z ∂μS := h_mono
    _ = M * ∫ z, ℓ z ∂μS := h_scal
    _ = M * brierRisk μS η q := by simp [brierRisk, ℓ]

/-- **Log-loss Bayes-optimality: `η` minimizes risk among competitors that are open-valued
and integrable against it.**

Do not quantify the side conditions over the whole predictor type:

    (h_int_q : ∀ q : ProbPredictor Z, Integrable (fun z ↦ bernoulliLogLoss (η z).1 (q z).1) μ)
    (h_q_open : ∀ q : ProbPredictor Z, ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)

`h_q_open` in that form **cannot be satisfied**. `ProbPredictor Z` is `Z → Set.Icc (0:ℝ) 1`,
a closed interval, so for any inhabited `Z` the constant predictor `fun _ ↦ ⟨0, _⟩` is a
term of the type and refutes it. Every instance of such a theorem carries a false
hypothesis, which makes the theorem vacuous rather than merely over-strong. `h_int_q` is
unsatisfiable in the same style for any `μ` and `Z` admitting a non-measurable function,
since `ProbPredictor` carries no measurability requirement and `Integrable` demands
`AEStronglyMeasurable`.

Both conditions are demanded of the competitor `q` actually being compared against, which
is all the proof uses them for, and which is satisfiable. -/
theorem logRisk_minimized_at_eta {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z)
    (hη_open : ∀ z, 0 < (η z).1 ∧ (η z).1 < 1)
    (h_int_eta : Integrable (fun z ↦ bernoulliLogLoss (η z).1 (η z).1) μ) :
    ∀ q : ProbPredictor Z,
      (∀ z, 0 < (q z).1 ∧ (q z).1 < 1) →
      Integrable (fun z ↦ bernoulliLogLoss (η z).1 (q z).1) μ →
      logRisk μ η η ≤ logRisk μ η q := by
  intro q hq_open h_int_q
  have hreg :
      0 ≤
        (∫ z,
          bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ) :=
    logRisk_regret_nonneg μ η q hη_open hq_open
  have hsub :
      (∫ z,
        bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ)
        = logRisk μ η q - logRisk μ η η := by
    unfold logRisk
    simpa [sub_eq_add_neg] using integral_sub h_int_q h_int_eta
  linarith [hreg, hsub]

/-- Log-loss uniqueness: equality of risks iff equality of predictors a.e. -/
theorem logRisk_eq_iff_ae_eq_eta {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z)
    (hη_open : ∀ z, 0 < (η z).1 ∧ (η z).1 < 1)
    (hq_open : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)
    (h_int_kl : Integrable (fun z ↦ klBernReal (η z) (q z)) μ)
    (h_int_eta : Integrable (fun z ↦ bernoulliLogLoss (η z).1 (η z).1) μ)
    (h_int_q : Integrable (fun z ↦ bernoulliLogLoss (η z).1 (q z).1) μ) :
    logRisk μ η q = logRisk μ η η ↔ q =ᵐ[μ] η := by
  have hzero :
      (∫ z,
        bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ) = 0
        ↔ q =ᵐ[μ] η :=
    logRisk_regret_zero_iff_ae_eq μ η q hη_open hq_open h_int_kl
  have hsub :
      (∫ z,
        bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ)
        = logRisk μ η q - logRisk μ η η := by
    unfold logRisk
    simpa [sub_eq_add_neg] using integral_sub h_int_q h_int_eta
  constructor
  · intro hEq
    apply hzero.mp
    linarith [hsub, hEq]
  · intro hAe
    have h0 : (∫ z, bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ) = 0 :=
      hzero.mpr hAe
    linarith [hsub, h0]

/-- **Brier Bayes-optimality among competitors integrable against `η`.**

`h_int_q` was quantified over the whole of `ProbPredictor Z`, demanding integrability
against *every* function `Z → Set.Icc (0:ℝ) 1`. `ProbPredictor` imposes no measurability,
so on any `Z` carrying a non-measurable function that requirement cannot be met and the
theorem was vacuous. It is now demanded of the competitor being compared against, which is
the only place the proof used it. -/
theorem brierRisk_minimized_at_eta {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z)
    (h_int_eta : Integrable (fun z ↦ expectedBrierScore (η z).1 (η z).1) μ) :
    ∀ q : ProbPredictor Z,
      Integrable (fun z ↦ expectedBrierScore (q z).1 (η z).1) μ →
      brierRisk μ η η ≤ brierRisk μ η q := by
  intro q h_int_q
  have hreg : (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
      = ∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ :=
    brier_regret_eq_l2_probPredictor μ η q
  have hnonneg : 0 ≤ ∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ :=
    integral_nonneg (μ := μ) (fun z ↦ sq_nonneg ((η z).1 - (q z).1))
  have hsub :
      (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
        = brierRisk μ η q - brierRisk μ η η := by
    unfold brierRisk
    simpa [sub_eq_add_neg] using integral_sub h_int_q h_int_eta
  have hdiff_nonneg : 0 ≤ brierRisk μ η q - brierRisk μ η η := by
    linarith [hreg, hnonneg, hsub]
  exact sub_nonneg.mp hdiff_nonneg

/-- Brier uniqueness: equal risks iff predictors are equal a.e. -/
theorem brierRisk_eq_iff_ae_eq_eta {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z)
    (h_int_eta : Integrable (fun z ↦ expectedBrierScore (η z).1 (η z).1) μ)
    (h_int_q : Integrable (fun z ↦ expectedBrierScore (q z).1 (η z).1) μ)
    (h_int_sq : Integrable (fun z ↦ ((η z).1 - (q z).1) ^ 2) μ) :
    brierRisk μ η q = brierRisk μ η η ↔ q =ᵐ[μ] η := by
  have hreg : (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
      = ∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ :=
    brier_regret_eq_l2_probPredictor μ η q
  have hsub :
      (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
        = brierRisk μ η q - brierRisk μ η η := by
    unfold brierRisk
    simpa [sub_eq_add_neg] using integral_sub h_int_q h_int_eta
  have hzero_sq :
      (∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ) = 0
      ↔ (fun z ↦ ((η z).1 - (q z).1) ^ 2) =ᵐ[μ] 0 :=
    integral_eq_zero_iff_of_nonneg (fun z ↦ sq_nonneg ((η z).1 - (q z).1)) h_int_sq
  constructor
  · intro hEq
    have h0 : (∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ) = 0 := by
      linarith [hreg, hsub, hEq]
    have h_ae_zero : (fun z ↦ ((η z).1 - (q z).1) ^ 2) =ᵐ[μ] 0 := (hzero_sq.mp h0)
    filter_upwards [h_ae_zero] with z hz
    have hsub : (η z).1 - (q z).1 = 0 := sq_eq_zero_iff.mp hz
    apply Subtype.ext
    linarith
  · intro hAe
    have h_ae_zero : (fun z ↦ ((η z).1 - (q z).1) ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [hAe] with z hz
      have hsub : (η z).1 - (q z).1 = 0 := by
        have : (q z).1 = (η z).1 := congrArg Subtype.val hz
        linarith
      exact sq_eq_zero_iff.mpr hsub
    have h0 : (∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ) = 0 := by
      rw [integral_congr_ae h_ae_zero]
      simp
    have hdiff : brierRisk μ η q - brierRisk μ η η = 0 := by
      linarith [hreg, hsub, h0]
    linarith [hdiff]

/-! ### Pointwise Properness and Population Risk -/

/-- Pointwise Bernoulli Brier risk at true parameter `η` and prediction `q`. -/
noncomputable def brierBernoulliRisk (η q : ℝ) : ℝ :=
  expectedBrierScore q η

theorem brierBernoulliRisk_decomp (η q : ℝ) :
    brierBernoulliRisk η q = η * (1 - η) + (q - η) ^ 2 := by
  unfold brierBernoulliRisk expectedBrierScore
  ring

theorem brierBernoulliRisk_min (η q : ℝ) :
    brierBernoulliRisk η η ≤ brierBernoulliRisk η q := by
  rw [brierBernoulliRisk_decomp η η, brierBernoulliRisk_decomp η q]
  nlinarith [sq_nonneg (q - η)]

theorem brierBernoulliRisk_eq_iff (η q : ℝ) :
    brierBernoulliRisk η q = brierBernoulliRisk η η ↔ q = η := by
  rw [brierBernoulliRisk_decomp η q, brierBernoulliRisk_decomp η η]
  constructor
  · intro h
    have hsq : (q - η) ^ 2 = 0 := by linarith
    nlinarith [sq_eq_zero_iff.mp hsq]
  · intro h
    subst h
    ring

/-- Pointwise Bernoulli log-risk (cross-entropy form). -/
noncomputable def logBernoulliRisk (η q : ℝ) : ℝ :=
  bernoulliLogLoss η q

theorem logBernoulliRisk_min (η q : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    logBernoulliRisk η η ≤ logBernoulliRisk η q := by
  have h_kl_nonneg : 0 ≤ bernoulliKLReal η q := bernoulliKLReal_nonneg η q hη0 hη1 hq0 hq1
  have hreg := logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1
  unfold logBernoulliRisk at *
  linarith

theorem logBernoulliRisk_eq_iff (η q : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    logBernoulliRisk η q = logBernoulliRisk η η ↔ q = η := by
  have h_kl_zero_iff : bernoulliKLReal η q = 0 ↔ q = η :=
    bernoulliKLReal_eq_zero_iff η q hη0 hη1 hq0 hq1
  have h_kl_nonneg : 0 ≤ bernoulliKLReal η q := bernoulliKLReal_nonneg η q hη0 hη1 hq0 hq1
  have hreg := logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1
  unfold logBernoulliRisk at *
  constructor
  · intro hEq
    have hkl : bernoulliKLReal η q = 0 := by linarith [hreg, hEq]
    exact h_kl_zero_iff.mp hkl
  · intro hq
    subst hq
    ring


/-! ### Population AUC (Conditional-Law Form) -/

/-- Binary-outcome population described by the conditional feature laws:
`Z⁺ ~ law(Z|Y=1)`, `Z⁻ ~ law(Z|Y=0)`, independent. -/
structure BinaryPopulation (Z : Type u) [MeasurableSpace Z] where
  μpos : Measure Z
  μneg : Measure Z

/-- Population AUC of a score:
`P(s(Z⁺) > s(Z⁻)) + 1/2 P(s(Z⁺)=s(Z⁻))`. -/
noncomputable def populationAUC {Z : Type u} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (s : Z → ℝ) : ENNReal :=
  (pop.μpos.prod pop.μneg) {zz : Z × Z | s zz.1 > s zz.2} +
    (ENNReal.ofReal (1 / 2 : ℝ)) *
      (pop.μpos.prod pop.μneg) {zz : Z × Z | s zz.1 = s zz.2}

theorem populationAUC_strictMono_invariant {Z : Type u} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (s : Z → ℝ) (g : ℝ → ℝ) (hg : StrictMono g) :
    populationAUC pop (g ∘ s) = populationAUC pop s := by
  unfold populationAUC
  have h_gt :
      {zz : Z × Z | g (s zz.1) > g (s zz.2)} = {zz : Z × Z | s zz.1 > s zz.2} := by
    ext zz
    exact hg.lt_iff_lt
  have h_eq :
      {zz : Z × Z | g (s zz.1) = g (s zz.2)} = {zz : Z × Z | s zz.1 = s zz.2} := by
    ext zz
    constructor <;> intro h
    · exact hg.injective h
    · simpa using congrArg g h
  simp [h_gt, h_eq]

/-- A strictly increasing transform of an AUC-optimal posterior score is also AUC-optimal. -/
theorem populationAUC_optimal_of_eta_transform {Z : Type u} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (η score : Z → ℝ)
    (h_opt_eta : ∀ s : Z → ℝ, populationAUC pop s ≤ populationAUC pop η)
    (h_rep : ∃ g : ℝ → ℝ, StrictMono g ∧ score = g ∘ η) :
    ∀ s : Z → ℝ, populationAUC pop s ≤ populationAUC pop score := by
  rcases h_rep with ⟨g, hg, hscore⟩
  intro s
  have h_eq : populationAUC pop score = populationAUC pop η := by
    rw [hscore]
    exact populationAUC_strictMono_invariant pop η g hg
  calc
    populationAUC pop s ≤ populationAUC pop η := h_opt_eta s
    _ = populationAUC pop score := h_eq.symm

/-! ### Classwise Bayes Comparisons -/

/-- Log-loss Bayes risk over a predictor class. -/
noncomputable def logBayesRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z)) : ℝ :=
  BayesRisk (logRisk μ η) F

/-- Brier Bayes risk over a predictor class. -/
noncomputable def brierBayesRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z)) : ℝ :=
  BayesRisk (brierRisk μ η) F

/-- The side conditions are demanded of the members of `F`, the class the infimum is taken
over, rather than of every term of `ProbPredictor Z`. In the previous form `h_q_open` was
unsatisfiable, since `ProbPredictor Z = Z → Set.Icc (0:ℝ) 1` contains the constant `0`
predictor, and the theorem held vacuously for every `F`. -/
theorem logBayesRisk_eq_eta_of_mem {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z))
    (h_eta_mem : η ∈ F)
    (h_bdd : BddBelow ((logRisk μ η) '' F))
    (hη_open : ∀ z, 0 < (η z).1 ∧ (η z).1 < 1)
    (h_int_eta : Integrable (fun z ↦ bernoulliLogLoss (η z).1 (η z).1) μ)
    (h_int_q : ∀ q ∈ F, Integrable (fun z ↦ bernoulliLogLoss (η z).1 (q z).1) μ)
    (h_q_open : ∀ q ∈ F, ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    logBayesRisk μ η F = logRisk μ η η := by
  unfold logBayesRisk BayesRisk oracleRisk
  apply le_antisymm
  · exact csInf_le h_bdd ⟨η, h_eta_mem, rfl⟩
  · refine le_csInf ?_ ?_
    · exact ⟨logRisk μ η η, ⟨η, h_eta_mem, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨q, hqF, rfl⟩
      exact logRisk_minimized_at_eta μ η hη_open h_int_eta q (h_q_open q hqF) (h_int_q q hqF)

/-- As for the log-loss version, integrability is demanded of the members of `F` rather
than of every term of `ProbPredictor Z`. -/
theorem brierBayesRisk_eq_eta_of_mem {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z))
    (h_eta_mem : η ∈ F)
    (h_bdd : BddBelow ((brierRisk μ η) '' F))
    (h_int_eta : Integrable (fun z ↦ expectedBrierScore (η z).1 (η z).1) μ)
    (h_int_q : ∀ q ∈ F, Integrable (fun z ↦ expectedBrierScore (q z).1 (η z).1) μ) :
    brierBayesRisk μ η F = brierRisk μ η η := by
  unfold brierBayesRisk BayesRisk oracleRisk
  apply le_antisymm
  · exact csInf_le h_bdd ⟨η, h_eta_mem, rfl⟩
  · refine le_csInf ?_ ?_
    · exact ⟨brierRisk μ η η, ⟨η, h_eta_mem, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨q, hqF, rfl⟩
      exact brierRisk_minimized_at_eta μ η h_int_eta q (h_int_q q hqF)

/-- Non-strict full-vs-baseline comparison from class inclusion. -/
theorem logBayesRisk_full_le_baseline {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (Ffull Fbase : Set (ProbPredictor Z))
    (h_sub : Fbase ⊆ Ffull)
    (h_bdd_full : BddBelow ((logRisk μ η) '' Ffull))
    (h_nonempty_base : ((logRisk μ η) '' Fbase).Nonempty) :
    logBayesRisk μ η Ffull ≤ logBayesRisk μ η Fbase :=
  BayesRisk_mono (R := logRisk μ η) Fbase Ffull h_sub h_bdd_full h_nonempty_base

/-- Strict full-vs-baseline theorem under a margin nondegeneracy condition. -/
theorem logBayesRisk_full_lt_baseline_of_margin {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (Ffull Fbase : Set (ProbPredictor Z))
    (h_eta_mem_full : η ∈ Ffull)
    (h_bdd_full : BddBelow ((logRisk μ η) '' Ffull))
    (h_nonempty_base : ((logRisk μ η) '' Fbase).Nonempty)
    (h_margin : ∃ ε > 0, ∀ q ∈ Fbase, logRisk μ η η + ε ≤ logRisk μ η q) :
    logBayesRisk μ η Ffull < logBayesRisk μ η Fbase := by
  rcases h_margin with ⟨ε, hε, hgap⟩
  unfold logBayesRisk BayesRisk
  refine oracleRisk_strict_of_witness (R := logRisk μ η) (Fyours := Ffull) (Fbaseline := Fbase)
    h_bdd_full h_nonempty_base ?_
  refine ⟨η, h_eta_mem_full, ε, hε, ?_⟩
  intro q hq
  exact hgap q hq

/-- Strict full-vs-baseline theorem for Brier loss under a margin condition. -/
theorem brierBayesRisk_full_lt_baseline_of_margin {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (Ffull Fbase : Set (ProbPredictor Z))
    (h_eta_mem_full : η ∈ Ffull)
    (h_bdd_full : BddBelow ((brierRisk μ η) '' Ffull))
    (h_nonempty_base : ((brierRisk μ η) '' Fbase).Nonempty)
    (h_margin : ∃ ε > 0, ∀ q ∈ Fbase, brierRisk μ η η + ε ≤ brierRisk μ η q) :
    brierBayesRisk μ η Ffull < brierBayesRisk μ η Fbase := by
  rcases h_margin with ⟨ε, hε, hgap⟩
  unfold brierBayesRisk BayesRisk
  refine oracleRisk_strict_of_witness (R := brierRisk μ η) (Fyours := Ffull) (Fbaseline := Fbase)
    h_bdd_full h_nonempty_base ?_
  refine ⟨η, h_eta_mem_full, ε, hε, ?_⟩
  intro q hq
  exact hgap q hq

/-- Strict Bayes-risk improvement from an explicit truth witness and a uniform baseline margin. -/
theorem BayesRisk_strict_of_truth_witness_and_margin
    {α : Type u} (R : α → ℝ) (truth : α) (Fsmall Fbig : Set α) :
    truth ∈ Fbig →
    BddBelow (R '' Fbig) →
    (R '' Fsmall).Nonempty →
    (∃ ε > 0, ∀ a ∈ Fsmall, R truth + ε ≤ R a) →
    BayesRisk R Fbig < BayesRisk R Fsmall := by
  intro h_truth_mem_big h_bdd_big h_nonempty_small h_margin
  refine oracleRisk_strict_of_witness (R := R) (Fyours := Fbig) (Fbaseline := Fsmall)
    h_bdd_big h_nonempty_small ?_
  rcases h_margin with ⟨ε, hε, hgap⟩
  exact ⟨truth, h_truth_mem_big, ε, hε, hgap⟩

/-- Log-loss strictness via witness+margin (proved, no axioms). -/
theorem logBayesRisk_strict_of_eta_in_closure_not_in_baseline_closure
    {Z : Type u} [MeasurableSpace Z]
    (μ : Measure Z) (η : ProbPredictor Z) (Fbase Ffull : Set (ProbPredictor Z)) :
    η ∈ Ffull →
    BddBelow ((logRisk μ η) '' Ffull) →
    ((logRisk μ η) '' Fbase).Nonempty →
    (∃ ε > 0, ∀ q ∈ Fbase, logRisk μ η η + ε ≤ logRisk μ η q) →
    logBayesRisk μ η Ffull < logBayesRisk μ η Fbase := by
  intro h_eta_mem_full h_bdd_full h_nonempty_base h_margin
  exact logBayesRisk_full_lt_baseline_of_margin μ η Ffull Fbase
    h_eta_mem_full h_bdd_full h_nonempty_base h_margin

/-- Brier-loss strictness via witness+margin (proved, no axioms). -/
theorem brierBayesRisk_strict_of_eta_in_closure_not_in_baseline_closure
    {Z : Type u} [MeasurableSpace Z]
    (μ : Measure Z) (η : ProbPredictor Z) (Fbase Ffull : Set (ProbPredictor Z)) :
    η ∈ Ffull →
    BddBelow ((brierRisk μ η) '' Ffull) →
    ((brierRisk μ η) '' Fbase).Nonempty →
    (∃ ε > 0, ∀ q ∈ Fbase, brierRisk μ η η + ε ≤ brierRisk μ η q) →
    brierBayesRisk μ η Ffull < brierBayesRisk μ η Fbase := by
  intro h_eta_mem_full h_bdd_full h_nonempty_base h_margin
  exact brierBayesRisk_full_lt_baseline_of_margin μ η Ffull Fbase
    h_eta_mem_full h_bdd_full h_nonempty_base h_margin

end OracleAndRegret

theorem BayesRisk_strict_of_truth_in_closure_not_in_baseline_closure
    {α : Type*} [TopologicalSpace α]
    (R : α → ℝ) (truth : α) (Fsmall Fbig : Set α)
    (h_cont : Continuous R)
    (h_truth_mem_big : truth ∈ closure Fbig)
    (h_truth_not_in_small : truth ∉ closure Fsmall)
    (h_bdd_big : BddBelow (R '' Fbig))
    (h_attain : ∃ a ∈ closure Fsmall, BayesRisk R Fsmall = R a)
    (h_strict_min : ∀ a ∈ closure Fsmall, a ≠ truth → R truth < R a) :
    BayesRisk R Fbig < BayesRisk R Fsmall := by
  rcases h_attain with ⟨a, ha_mem, ha_eq⟩
  have h_inf_le : BayesRisk R Fbig ≤ R truth := by
    unfold BayesRisk
    have hr_mem : R truth ∈ closure (R '' Fbig) :=
      image_closure_subset_closure_image h_cont (Set.mem_image_of_mem R h_truth_mem_big)
    have h_le_closure : closure (R '' Fbig) ⊆ Set.Ici (sInf (R '' Fbig)) := by
      apply isClosed_Ici.closure_subset_iff.mpr
      intro x hx
      exact csInf_le h_bdd_big hx
    exact h_le_closure hr_mem
  have h_neq : a ≠ truth := by
    intro heq
    subst heq
    contradiction
  have h_strict : R truth < R a := h_strict_min a ha_mem h_neq
  rw [ha_eq]
  linarith

end Calibrator
