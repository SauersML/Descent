/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Descent.Foundations.Probability
import Descent.Foundations.BernoulliLosses

namespace Descent.Program

universe u

open scoped InnerProductSpace
open InnerProductSpace
open MeasureTheory
open Descent.Foundations (expectedBrierScore brierScore_at_true_prob
  exactBrierRiskOfCalibrated exactBrierRiskOfCalibrated_eq_integral bernoulliLogLoss
  bernoulliKLReal bernoulliKLReal_certain_forecast_is_junk logLoss_regret_eq_kl_pointwise
  brier_regret_pointwise brierBernoulliRisk)

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

/-- The score is never negative: it is a squared error, so a body that lost the square would
fail here wherever the prediction overshoots. -/
theorem brierScore_nonneg (p y : ℝ) : 0 ≤ brierScore p y := by
  unfold brierScore; positivity

/-- **Anchors of the Brier score.** A confident correct call scores `0`, a confident wrong call
scores `1`, and the uninformative call scores `1/4`. Three numbers rather than one, because a
single anchor is met by many wrong bodies. -/
theorem brierScore_anchors :
    brierScore 1 1 = 0 ∧ brierScore 0 1 = 1 ∧ brierScore (1 / 2) 1 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold brierScore <;> norm_num

/-- The score vanishes exactly on a correct point prediction. -/
theorem brierScore_eq_zero_iff (p y : ℝ) : brierScore p y = 0 ↔ p = y := by
  unfold brierScore
  rw [pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  exact eq_comm

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
  have h_deriv_add : deriv (fun x : ℝ ↦ (π - 2 * π * x) + x ^ 2) p = deriv (fun x : ℝ ↦ π - 2 * π *
      x) p + deriv (fun x : ℝ ↦ x ^ 2) p :=
    deriv_add hd1 hd2
  have h_eq_add : (fun x : ℝ ↦ π - 2 * π * x + x ^ 2) = (fun x : ℝ ↦ (π - 2 * π * x) + x ^ 2) := rfl
  rw [h_eq_add, h_deriv_add]
  have hd1_sub1 : DifferentiableAt ℝ (fun x : ℝ ↦ π) p := differentiableAt_const π
  have hd1_sub2 : DifferentiableAt ℝ (fun x : ℝ ↦ 2 * π * x) p :=
    differentiableAt_id.const_mul (2 * π)
  have h_deriv_sub : deriv (fun x : ℝ ↦ π - 2 * π * x) p = deriv (fun x : ℝ ↦ π) p - deriv (fun x :
      ℝ ↦ 2 * π * x) p :=
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

/-- Strict improvement: if p ≠ π, the Brier score is strictly worse. -/
theorem brierScore_strict_minimum (π p : ℝ) (hp : p ≠ π) :
    expectedBrierScore π π < expectedBrierScore p π := by
  rw [expectedBrierScore_quadratic, expectedBrierScore_quadratic]
  have h : π - 2 * π * p + p ^ 2 - (π - 2 * π * π + π ^ 2) = (p - π) ^ 2 := by ring
  have hne : p - π ≠ 0 := sub_ne_zero.mpr hp
  have hsq : (p - π) ^ 2 > 0 := sq_pos_of_ne_zero hne
  linarith

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

/-- **The point-mass posterior**: all posterior mass at one linear predictor, so
`E[sigmoid(η)]` is `sigmoid(E[η])` and the two predictions coincide.

`PosteriorPrediction` had no exhibited inhabitant, and for a structure whose
whole purpose is to keep `prob_mean` and `prob_mode` apart, the case where they
COINCIDE is the informative one to exhibit: it shows the gap the structure
tracks is a gap about posterior spread, not a typographical distinction between
two fields. `prob_mean` is a bare field, so nothing forces it to be an
expectation of anything -- here it is set to the value a degenerate posterior
would give it, which is the one case that needs no law of iterated expectations
to justify.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the degenerate point of the
    parameter space, written down. The Jensen gap at a nondegenerate posterior is
    where the content is, and this does not bound it. -/
noncomputable def PosteriorPrediction.pointMass (η : ℝ) : PosteriorPrediction where
  η_mean := η
  prob_mean := 1 / (1 + Real.exp (-η))

instance PosteriorPrediction.instNonempty : Nonempty PosteriorPrediction :=
  ⟨PosteriorPrediction.pointMass 0⟩

/-- **Mean and mode agree exactly at a point-mass posterior.** Together with the
fact that they are separate fields in general, this says the mean/mode split is
carried entirely by posterior spread: remove the spread and the split closes. -/
theorem PosteriorPrediction.pointMass_prob_mean_eq_prob_mode (η : ℝ) :
    (PosteriorPrediction.pointMass η).prob_mean =
      (PosteriorPrediction.pointMass η).prob_mode := rfl

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
    (π : ℝ)
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

/-- The sigmoid function (logistic function), `σ(x) = 1 / (1 + e^(-x))`.

This is Mathlib's `Real.sigmoid`, which carries positivity, the upper bound
one, strict monotonicity, the derivative and differentiability already; only
the statements below that Mathlib does not have are proved here.  The local
abbreviation exists because the surrounding calibration statements read in
terms of `sigmoid`, and it is reducible, so every `Real.sigmoid_*` lemma
applies to it directly. -/
noncomputable abbrev sigmoid : ℝ → ℝ := Real.sigmoid

/-- Sigmoid is greater than 1/2 for positive inputs (monotonicity).  Mathlib
has the strict monotonicity and the value at zero; this is the composite. -/
theorem sigmoid_gt_half {x : ℝ} (hx : x > 0) : sigmoid x > 1 / 2 := by
  have h := (Real.sigmoid_lt_iff (a := 0) (b := x)).mpr hx
  rw [Real.sigmoid_zero] at h
  linarith

/-- Sigmoid is less than 1/2 for negative inputs (monotonicity). -/
theorem sigmoid_lt_half {x : ℝ} (hx : x < 0) : sigmoid x < 1 / 2 := by
  have h := (Real.sigmoid_lt_iff (a := x) (b := 0)).mpr hx
  rw [Real.sigmoid_zero] at h
  linarith

/-- The second derivative.  Mathlib has the first derivative and its
`HasDerivAt` form; only the second derivative is proved here. -/
lemma deriv2_sigmoid (x : ℝ) : deriv (deriv sigmoid) x = sigmoid x * (1 - sigmoid x) * (1 - 2 *
    sigmoid x) := by
  have h_eq : deriv sigmoid = fun x ↦ sigmoid x * (1 - sigmoid x) := Real.deriv_sigmoid
  rw [h_eq]
  apply HasDerivAt.deriv
  have h_has_deriv_sig : HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x :=
    Real.hasDerivAt_sigmoid x
  convert HasDerivAt.mul h_has_deriv_sig (HasDerivAt.sub (hasDerivAt_const x (1:ℝ))
      h_has_deriv_sig) using 1
  simp; ring

lemma sigmoid_strictConcaveOn_Ici : StrictConcaveOn ℝ (Set.Ici 0) sigmoid := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
  · have h_diff : Differentiable ℝ sigmoid := _root_.differentiable_sigmoid
    exact h_diff.continuous.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    dsimp only [Nat.iterate, Function.comp]
    rw [deriv2_sigmoid]
    apply mul_neg_of_pos_of_neg
    · apply mul_pos (Real.sigmoid_pos x)
      rw [sub_pos]
      exact Real.sigmoid_lt_one x
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
    have h_diff : Differentiable ℝ sigmoid := _root_.differentiable_sigmoid
    have h_cont : ContinuousOn sigmoid (Set.Ici 0) := h_diff.continuous.continuousOn
    have h_int_sigmoid : Integrable (sigmoid ∘ X) P := by
      have h_cont_sig : Continuous sigmoid :=
        _root_.continuous_sigmoid
      refine Integrable.of_bound (h_cont_sig.comp_aestronglyMeasurable h_ae_meas) (1:ℝ) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · apply le_trans (by norm_num : (-1:ℝ) ≤ 0) (le_of_lt (Real.sigmoid_pos _))
      · exact le_of_lt (Real.sigmoid_lt_one _)
    rcases sigmoid_strictConcaveOn_Ici.ae_eq_const_or_lt_map_average h_cont isClosed_Ici
      h_mem h_integrable h_int_sigmoid with h_eq | h_lt
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

/-- A map from a feature space to a probability. Both names below are this type; they
differ in what the map is CLAIMED to be, and the whole oracle comparison is about the
gap between the two claims. -/
abbrev ProbMap (Z : Type u) := Z → Foundations.UnitProb

/-- True conditional probability on feature space `Z`: the map nature supplies. -/
abbrev TrueCondProb (Z : Type u) := ProbMap Z

/-- Predictor on feature space `Z`: the map a method fits. Same type as `TrueCondProb`
and never the same object -- that they are indistinguishable to the type checker is the
reason the comparison below has to be stated rather than assumed. -/
abbrev ProbPredictor (Z : Type u) := ProbMap Z

/-- Population risk under Bernoulli mixing with true probability `p(z)`. -/
noncomputable def populationRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (q : ProbPredictor Z) : ℝ :=
  ∫ z, (p z).1 * ℓ (q z).1 true + (1 - (p z).1) * ℓ (q z).1 false ∂μ

/-- Vanishing identity: against the zero measure every predictor has zero risk, which is the
degenerate end of the experiment rather than a good predictor. -/
theorem populationRisk_zero_measure_eq_zero {Z : Type u} [MeasurableSpace Z]
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (q : ProbPredictor Z) :
    populationRisk 0 ℓ p q = 0 := by
  unfold populationRisk
  simp


/-- Population-level oracle risk over a model class `F`. -/
noncomputable def oracleRisk {α : Type u} (R : α → ℝ) (F : Set α) : ℝ :=
  sInf (R '' F)

/-- Reference evaluation: over a one-element class the oracle risk is that element's risk. -/
theorem oracleRisk_at_reference_point {α : Type u} (R : α → ℝ) (a : α) :
    oracleRisk R {a} = R a := by
  unfold oracleRisk
  simp


/-- Oracle infimum risk for a predictor class `F`. -/
noncomputable def infRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (F : Set (ProbPredictor Z)) : ℝ :=
  oracleRisk (populationRisk μ ℓ p) F

/-- Reference evaluation: against the zero measure a one-element class has zero inf risk. -/
theorem infRisk_at_zero_measure {Z : Type u} [MeasurableSpace Z]
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (q : ProbPredictor Z) :
    infRisk 0 ℓ p {q} = 0 := by
  unfold infRisk oracleRisk populationRisk
  simp


/-- Reference evaluation: over a one-element predictor class the inf risk is that predictor's. -/
theorem infRisk_at_reference_point {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (q : ProbPredictor Z) :
    infRisk μ ℓ p {q} = populationRisk μ ℓ p q := by
  unfold infRisk
  simp [oracleRisk]


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


/-- **bernoulliLogLoss at its junk point, named.** A forecast of probability zero for an outcome
that occurs is infinitely costly -- that is the whole point of a log score. `Real.log 0` is
junk-zero and the loss is `0`: a PERFECT score, awarded to the most confidently wrong forecast
expressible. Nothing in the corpus's scoring chain distinguishes it from a correct certain
forecast. Consumers must exclude the argument that makes the guard vanish. -/
theorem bernoulliLogLoss_certain_and_wrong_is_junk :
    bernoulliLogLoss 1 0 = 0 := by
  unfold bernoulliLogLoss
  simp

/-- **The log loss is in nats, pinned.** `bernoulliLogLoss_certain_correct` fixes the loss where
the forecast is certain and right, which is zero for every body of the form `c * loss` and so
fixes no unit. A certain outcome forecast at one half costs `log 2` -- one bit, measured in nats
-- which fixes `c = 1` and with it the base of the logarithm. -/
theorem bernoulliLogLoss_half_forecast :
    bernoulliLogLoss 1 (1 / 2) = Real.log 2 := by
  unfold bernoulliLogLoss
  simp [one_div, Real.log_inv]

/-- **A confident correct prediction costs nothing.** At `p = 1` and `q = 1` both terms vanish --
the second because its coefficient does -- so the loss is exactly zero. That endpoint fixes the
normalisation: a body carrying an additive constant, or the wrong sign on either term, is still a
sum of weighted logarithms and would fail here. -/
theorem bernoulliLogLoss_certain_correct : bernoulliLogLoss 1 1 = 0 := by
  unfold bernoulliLogLoss
  norm_num

/-- **The `log1p` form of the Bernoulli KL divergence: the same number, evaluable.**

`p/q = 1 + (p-q)/q` and `(1-p)/(1-q) = 1 - (p-q)/(1-q)`, so each logarithm can be
taken of `1 + (something small)` rather than of a ratio that rounds to `1` before
the logarithm ever sees it. A library `log1p` then evaluates each term to full
relative precision. The hypotheses are exactly the two points at which the
rewrite is not an identity -- `q = 0` and `q = 1` -- which are also the two
forecasts `bernoulliKLReal_certain_forecast_is_junk` names as junk, so this
theorem excludes nothing a consumer was entitled to evaluate anyway.

See the measured comparison in the docstring of `bernoulliKLReal`. -/
theorem bernoulliKLReal_eq_logOnePlus {p q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    bernoulliKLReal p q =
      p * Real.log (1 + (p - q) / q)
        + (1 - p) * Real.log (1 - (p - q) / (1 - q)) := by
  have hq1' : (1 : ℝ) - q ≠ 0 := sub_ne_zero_of_ne (Ne.symm hq1)
  have h1 : 1 + (p - q) / q = p / q := by field_simp; ring
  have h2 : 1 - (p - q) / (1 - q) = (1 - p) / (1 - q) := by field_simp; ring
  unfold bernoulliKLReal
  rw [h1, h2]

/-- **A forecast that matches the truth has zero divergence.** Both logarithms are of one, so the
divergence vanishes identically on the diagonal. Nonnegativity is shared by every positive
multiple and by bodies with an additive floor; vanishing exactly at agreement is not, and it is
what makes this a divergence rather than a monotone rescaling of one. -/
theorem bernoulliKLReal_self (p : ℝ) : bernoulliKLReal p p = 0 := by
  unfold bernoulliKLReal
  rcases eq_or_ne p 0 with hp | hp
  · rw [hp]; norm_num
  · rcases eq_or_ne (1 - p) 0 with hq | hq
    · rw [hq, div_self hp]; norm_num
    · rw [div_self hp, div_self hq]; norm_num

/-- Bernoulli KL on `[0,1]` probabilities. -/
noncomputable def klBernReal (p q : Foundations.UnitProb) : ℝ :=
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
  have h2_neg : - ((1 - p) * Real.log ((1 - q) / (1 - p))) ≥ - (1 - p) * ((1 - q) / (1 - p) -
      1) := by
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
theorem klBernReal_eq_zero_iff (p q : Foundations.UnitProb)
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

/-- Population log-loss regret. -/
noncomputable def logLossRegret {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, bernoulliLogLoss (p z) (q z) - bernoulliLogLoss (p z) (p z) ∂μ

/-- Vanishing identity: a predictor that matches the truth has zero regret. -/
theorem logLossRegret_self_eq_zero {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p : Z → ℝ) :
    logLossRegret μ p p = 0 := by
  unfold logLossRegret
  simp


/-- Population Bernoulli KL certificate. -/
noncomputable def logLossKLCertificate {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, bernoulliKLReal (p z) (q z) ∂μ

/-- Vanishing identity: against the zero measure the certificate is zero. -/
theorem logLossKLCertificate_zero_measure_eq_zero {Z : Type u} [MeasurableSpace Z] (p q : Z → ℝ) :
    logLossKLCertificate 0 p q = 0 := by
  unfold logLossKLCertificate
  simp


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

/-- Population Brier regret. -/
noncomputable def brierRegret {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, expectedBrierScore (q z) (p z) - expectedBrierScore (p z) (p z) ∂μ

/-- Vanishing identity: a predictor that matches the truth has zero regret. -/
theorem brierRegret_self_eq_zero {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p : Z → ℝ) :
    brierRegret μ p p = 0 := by
  unfold brierRegret
  simp


/-- Population L² certificate for Brier regret. -/
noncomputable def brierL2Certificate {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, (q z - p z) ^ 2 ∂μ

/-- Vanishing identity: the certificate vanishes exactly on a matching predictor. -/
theorem brierL2Certificate_self_eq_zero {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (p : Z → ℝ) :
    brierL2Certificate μ p p = 0 := by
  unfold brierL2Certificate
  simp


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


/-! ### Classwise Bayes Comparisons -/

/-- Log-loss Bayes risk over a predictor class. -/
noncomputable def logBayesRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z)) : ℝ :=
  BayesRisk (logRisk μ η) F

/-- Reference evaluation against the zero measure. -/
theorem logBayesRisk_at_zero_measure {Z : Type u} [MeasurableSpace Z]
    (η q : ProbPredictor Z) :
    logBayesRisk 0 η {q} = 0 := by
  unfold logBayesRisk BayesRisk oracleRisk logRisk
  simp


/-- Reference evaluation over a one-element class. -/
theorem logBayesRisk_at_reference_point {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) :
    logBayesRisk μ η {q} = logRisk μ η q := by
  unfold logBayesRisk BayesRisk oracleRisk
  simp


/-- Brier Bayes risk over a predictor class. -/
noncomputable def brierBayesRisk {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z)) : ℝ :=
  BayesRisk (brierRisk μ η) F

/-- Reference evaluation against the zero measure. -/
theorem brierBayesRisk_at_zero_measure {Z : Type u} [MeasurableSpace Z]
    (η q : ProbPredictor Z) :
    brierBayesRisk 0 η {q} = 0 := by
  unfold brierBayesRisk BayesRisk oracleRisk brierRisk
  simp


/-- Reference evaluation over a one-element class. -/
theorem brierBayesRisk_at_reference_point {Z : Type u} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) :
    brierBayesRisk μ η {q} = brierRisk μ η q := by
  unfold brierBayesRisk BayesRisk oracleRisk
  simp


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

end Descent.Program
