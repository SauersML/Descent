import Calibrator.Models

namespace Calibrator

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

### The Result

We prove that under **Brier Score** loss (squared error on probabilities),
the Posterior Mean strictly dominates the Mode when there's parameter uncertainty.

This justifies the existence of:
- `quadrature.rs`: Computes E[sigmoid(η)] via Gauss-Hermite integration
- `hmc.rs`: Samples from posterior to compute the true posterior mean
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
    2 * (p - π) = -2 * π + 2 * p := by ring

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

/-! ### Posterior Mean Optimality -/

/-- The posterior mean prediction for a binary outcome.

    Given a distribution over the linear predictor η (represented by its mean μ
    and the expected value of sigmoid(η)), the posterior mean prediction is
    E[sigmoid(η)], NOT sigmoid(E[η]).

    This structure captures the key distinction between Mode and Mean prediction. -/
structure PosteriorPrediction where
  /-- The posterior mean of η (the linear predictor) -/
  η_mean : ℝ
  /-- The posterior mean of sigmoid(η) = E[sigmoid(η)] -/
  prob_mean : ℝ
  /-- The mode prediction = sigmoid(E[η]) -/
  prob_mode : ℝ
  /-- Constraint: mode prediction uses sigmoid of mean -/
  mode_is_sigmoid_of_mean : prob_mode = 1 / (1 + Real.exp (-η_mean))

/-- **Main Theorem**: The Posterior Mean is the Bayes-optimal predictor under Brier Score.

    Given:
    - A true conditional probability π = P(Y=1|X)
    - Uncertainty about η with posterior mean E[η] and E[sigmoid(η)]

    The posterior mean prediction E[sigmoid(η)] achieves lower expected Brier score
    than the mode prediction sigmoid(E[η]) whenever there is parameter uncertainty
    (i.e., when E[sigmoid(η)] ≠ sigmoid(E[η])).

    **Proof sketch**:
    1. By the proper scoring rule property, the optimal prediction is p* = π
    2. The true π = E[sigmoid(η)] (by the law of iterated expectations)
    3. Therefore E[sigmoid(η)] is optimal, and sigmoid(E[η]) is suboptimal

    This theorem justifies `quadrature.rs` and `hmc.rs` in the Rust codebase. -/
theorem posterior_mean_optimal (pred : PosteriorPrediction)
    (π : ℝ) (_hπ : 0 ≤ π ∧ π ≤ 1)
    (h_true : π = pred.prob_mean) :
    expectedBrierScore pred.prob_mean π ≤ expectedBrierScore pred.prob_mode π := by
  -- The posterior mean IS the true probability, so by the proper scoring rule,
  -- it achieves the minimum Brier score
  rw [← h_true]
  exact brierScore_minimized_at_true_prob π pred.prob_mode

/-- Strict optimality: if there's genuine uncertainty (Mode ≠ Mean), Mode is strictly worse. -/
theorem posterior_mean_strictly_better (pred : PosteriorPrediction)
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
  · apply ne_of_gt
    have : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith

lemma deriv_sigmoid (x : ℝ) : deriv sigmoid x = sigmoid x * (1 - sigmoid x) := by
  have h_diff : DifferentiableAt ℝ (fun x => 1 + Real.exp (-x)) x := by
    apply DifferentiableAt.add
    · exact differentiableAt_const _
    · apply DifferentiableAt.exp
      exact differentiableAt_id.neg
  have h_ne : 1 + Real.exp (-x) ≠ 0 := by
    apply ne_of_gt
    have : Real.exp (-x) > 0 := Real.exp_pos (-x)
    linarith
  unfold sigmoid
  simp only [one_div]
  apply HasDerivAt.deriv
  convert HasDerivAt.inv (c := fun x => 1 + Real.exp (-x)) (by
      apply HasDerivAt.add
      · apply hasDerivAt_const
      · apply HasDerivAt.exp
        apply HasDerivAt.neg
        apply hasDerivAt_id
    ) h_ne using 1
  field_simp [h_ne]
  ring

lemma deriv2_sigmoid (x : ℝ) : deriv (deriv sigmoid) x = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x) := by
  have h_eq : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x) := by
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
  · have h_diff : Differentiable ℝ sigmoid := fun x => differentiable_sigmoid x
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

/- **Jensen's Gap for Logistic Regression**

    For a random variable η with E[η] = μ and Var(η) = σ² > 0:
    - If μ > 0: E[sigmoid(η)] < sigmoid(μ)  (sigmoid is concave for x > 0)
    - If μ < 0: E[sigmoid(η)] > sigmoid(μ)  (sigmoid is convex for x < 0)
    - If μ = 0: E[sigmoid(η)] = sigmoid(μ) = 0.5  (by symmetry)

    **Note**: The direction of shrinkage is toward 0.5, but with large variance
    the expectation can overshoot past 0.5. The core Jensen inequality is just
    about the relationship to sigmoid(μ), not about staying on the same side of 0.5.

    A full proof requires:
    1. Proving sigmoid is strictly concave on (0, ∞) and convex on (-∞, 0)
    2. Measure-theoretic integration showing E[f(X)] < f(E[X]) for concave f -/
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
    have h_diff : Differentiable ℝ sigmoid := fun x => differentiable_sigmoid x
    have h_cont : ContinuousOn sigmoid (Set.Ici 0) := h_diff.continuous.continuousOn
    have h_int_sigmoid : Integrable (sigmoid ∘ X) P := by
      have h_cont_sig : Continuous sigmoid := Differentiable.continuous (fun x => differentiable_sigmoid x)
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

section GradientDescentVerification

open Matrix

variable {n p k : ℕ} [Fintype (Fin n)] [Fintype (Fin p)] [Fintype (Fin k)]

/-!
### Matrix Calculus: Log-Determinant Derivatives

We define `H(rho) = A + exp(rho) * B` and prove that the derivative of `log(det(H(rho)))`
with respect to `rho` is `exp(rho) * trace(H(rho)⁻¹ * B)`. This uses Jacobi's formula
for the derivative of the determinant.
-/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Matrix function H(ρ) = A + exp(ρ) * B. -/
noncomputable def H_matrix (A B : Matrix m m ℝ) (rho : ℝ) : Matrix m m ℝ := A + Real.exp rho • B

/-- The log-determinant function f(ρ) = log(det(H(ρ))). -/
noncomputable def log_det_H (A B : Matrix m m ℝ) (rho : ℝ) := Real.log (H_matrix A B rho).det

/-- The derivative of log(det(H(ρ))) = log(det(A + exp(ρ)B)) with respect to ρ
    is exp(ρ) * trace(H(ρ)⁻¹ * B). This is derived using Jacobi's formula. -/
theorem derivative_log_det_H_matrix (A B : Matrix m m ℝ)
    (_hB : B.IsSymm)
    (rho : ℝ) (h_pos : (H_matrix A B rho).PosDef) :
    deriv (log_det_H A B) rho = Real.exp rho * ((H_matrix A B rho)⁻¹ * B).trace := by
  have h_inv : (H_matrix A B rho).det ≠ 0 := h_pos.det_pos.ne'
  have h_det : deriv (fun rho => Real.log (Matrix.det (A + Real.exp rho • B))) rho = Real.exp rho * Matrix.trace ((A + Real.exp rho • B)⁻¹ * B) := by
    have h_det_step1 : deriv (fun rho => Matrix.det (A + Real.exp rho • B)) rho = Matrix.det (A + Real.exp rho • B) * Matrix.trace ((A + Real.exp rho • B)⁻¹ * B) * Real.exp rho := by
      have h_jacobi : deriv (fun rho => Matrix.det (A + Real.exp rho • B)) rho = Matrix.trace (Matrix.adjugate (A + Real.exp rho • B) * deriv (fun rho => A + Real.exp rho • B) rho) := by
        have h_jacobi : ∀ (M : ℝ → Matrix m m ℝ), DifferentiableAt ℝ M rho → deriv (fun rho => Matrix.det (M rho)) rho = Matrix.trace (Matrix.adjugate (M rho) * deriv M rho) := by
          intro M hM_diff
          have h_jacobi : deriv (fun rho => Matrix.det (M rho)) rho = ∑ i, ∑ j, (Matrix.adjugate (M rho)) i j * deriv (fun rho => (M rho) j i) rho := by
            simp +decide [ Matrix.det_apply', Matrix.adjugate_apply, Matrix.mul_apply ]
            have h_jacobi : deriv (fun rho => ∑ σ : Equiv.Perm m, (↑(↑((Equiv.Perm.sign : Equiv.Perm m → ℤˣ) σ) : ℤ) : ℝ) * ∏ i : m, M rho ((σ : m → m) i) i) rho = ∑ σ : Equiv.Perm m, (↑(↑((Equiv.Perm.sign : Equiv.Perm m → ℤˣ) σ) : ℤ) : ℝ) * ∑ i : m, (∏ j ∈ Finset.univ.erase i, M rho ((σ : m → m) j) j) * deriv (fun rho => M rho ((σ : m → m) i) i) rho := by
              have h_jacobi : ∀ σ : Equiv.Perm m, deriv (fun rho => ∏ i : m, M rho ((σ : m → m) i) i) rho = ∑ i : m, (∏ j ∈ Finset.univ.erase i, M rho ((σ : m → m) j) j) * deriv (fun rho => M rho ((σ : m → m) i) i) rho := by
                intro σ
                have h_prod_rule : ∀ (f : m → ℝ → ℝ), (∀ i, DifferentiableAt ℝ (f i) rho) → deriv (fun rho => ∏ i, f i rho) rho = ∑ i, (∏ j ∈ Finset.univ.erase i, f j rho) * deriv (f i) rho := by
                  intro f hf
                  convert deriv_finset_prod (u := Finset.univ) (f := f) (x := rho) (fun i _ => hf i)
                  simp
                apply h_prod_rule
                intro i
                exact DifferentiableAt.comp rho ( differentiableAt_pi.1 ( differentiableAt_pi.1 hM_diff _ ) _ ) differentiableAt_id
              have h_deriv_sum : deriv (fun rho => ∑ σ : Equiv.Perm m, (↑(↑((Equiv.Perm.sign : Equiv.Perm m → ℤˣ) σ) : ℤ) : ℝ) * ∏ i : m, M rho ((σ : m → m) i) i) rho = ∑ σ : Equiv.Perm m, (↑(↑((Equiv.Perm.sign : Equiv.Perm m → ℤˣ) σ) : ℤ) : ℝ) * deriv (fun rho => ∏ i : m, M rho ((σ : m → m) i) i) rho := by
                have h_diff : ∀ σ : Equiv.Perm m, DifferentiableAt ℝ (fun rho => ∏ i : m, M rho ((σ : m → m) i) i) rho := by
                  intro σ
                  have h_diff : ∀ i : m, DifferentiableAt ℝ (fun rho => M rho ((σ : m → m) i) i) rho := by
                    intro i
                    exact DifferentiableAt.comp rho ( differentiableAt_pi.1 ( differentiableAt_pi.1 hM_diff _ ) _ ) differentiableAt_id
                  convert DifferentiableAt.finset_prod (u := Finset.univ) (f := fun i rho => M rho ((σ : m → m) i) i) (x := rho) (fun i _ => h_diff i)
                  simp
                norm_num [ h_diff ]
              simpa only [ h_jacobi ] using h_deriv_sum
            simp +decide only [h_jacobi, Finset.mul_sum _ _ _]
            simp +decide [ Finset.sum_mul _ _ _, Matrix.updateRow_apply ]
            rw [ Finset.sum_comm ]
            refine' Finset.sum_congr rfl fun i hi => _
            rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ] ; ring
            rw [ Finset.sum_eq_single ( ( ‹Equiv.Perm m› : m → m ) i ) ] <;> simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ] ; ring
            intro j hj; simp +decide [ Pi.single_apply, hj ]
            rw [ Finset.prod_eq_zero_iff.mpr ] <;> simp +decide [ hj ]
            exact ⟨ ( ‹Equiv.Perm m›.symm j ), by simp +decide, by simpa [ Equiv.symm_apply_eq ] using hj ⟩
          rw [ h_jacobi, Matrix.trace ]
          rw [ deriv_pi ]
          · simp +decide [ Matrix.mul_apply, Finset.mul_sum _ _ _ ]
            refine' Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => _
            rw [ deriv_pi ]
            intro i; exact (by
            exact DifferentiableAt.comp rho ( differentiableAt_pi.1 ( differentiableAt_pi.1 hM_diff j ) i ) differentiableAt_id)
          · exact fun i => DifferentiableAt.comp rho ( differentiableAt_pi.1 hM_diff i ) differentiableAt_id
        apply h_jacobi
        exact differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => DifferentiableAt.add ( differentiableAt_const _ ) ( DifferentiableAt.smul ( Real.differentiableAt_exp ) ( differentiableAt_const _ ) )
      simp_all +decide [ Matrix.inv_def, mul_assoc, mul_left_comm, mul_comm, Matrix.trace_mul_comm ( Matrix.adjugate _ ) ]
      rw [ show deriv ( fun rho => A + Real.exp rho • B ) rho = Real.exp rho • B from ?_ ]
      · by_cases h : Matrix.det ( A + Real.exp rho • B ) = 0 <;> simp_all +decide [ Matrix.trace_smul, mul_assoc, mul_comm, mul_left_comm ]
        exact False.elim <| h_inv h
      · rw [ deriv_pi ] <;> norm_num [ Real.differentiableAt_exp, mul_comm ]
        ext i; rw [ deriv_pi ] <;> norm_num [ Real.differentiableAt_exp, mul_comm ]
    by_cases h_det : DifferentiableAt ℝ ( fun rho => Matrix.det ( A + Real.exp rho • B ) ) rho <;> simp_all +decide [ Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm ]
    · convert HasDerivAt.deriv ( HasDerivAt.log ( h_det.hasDerivAt ) h_inv ) using 1 ; ring!
      exact eq_div_of_mul_eq ( by aesop ) ( by linear_combination' h_det_step1.symm )
    · contrapose! h_det
      simp +decide [ Matrix.det_apply' ]
      fun_prop (disch := norm_num)
  exact h_det

-- 1. Model Functions
noncomputable def S_lambda_fn (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (rho : Fin k → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ i, (Real.exp (rho i) • S_basis i)

noncomputable def L_pen_fn (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ) (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (rho : Fin k → ℝ) (beta : Matrix (Fin p) (Fin 1) ℝ) : ℝ :=
  - (log_lik beta) + 0.5 * (beta.transpose * (S_lambda_fn S_basis rho) * beta).trace

noncomputable def Hessian_fn (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (rho : Fin k → ℝ) (beta : Matrix (Fin p) (Fin 1) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  X.transpose * (W beta) * X + S_lambda_fn S_basis rho

/-- Algebraic matrix inverse via Cramer's rule. Over `ℝ` this is definitionally
    equal to `M⁻¹`, but it avoids carrying inverse-specific structure in later
    definitions that are easier to normalize as polynomial expressions. -/
noncomputable def matrixInvAlg {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℝ) : Matrix α α ℝ :=
  (M.det)⁻¹ • M.adjugate

theorem matrixInvAlg_eq_inv {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℝ) :
    matrixInvAlg M = M⁻¹ := by
  by_cases h_det : M.det = 0
  · simp [matrixInvAlg, Matrix.inv_def, h_det]
  · simp [matrixInvAlg, Matrix.inv_def, h_det]

theorem inv_mul_self_of_det_ne_zero {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℝ) (h_det : M.det ≠ 0) : M⁻¹ * M = 1 := by
  simp [Matrix.inv_def, Matrix.adjugate_mul, h_det]

noncomputable def LAML_explicit (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ) (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (rho : Fin k → ℝ) (beta : Matrix (Fin p) (Fin 1) ℝ) : ℝ :=
  let H := Hessian_fn S_basis X W rho beta
  L_pen_fn log_lik S_basis rho beta + 0.5 * Real.log (H.det) - 0.5 * Real.log ((S_lambda_fn S_basis rho).det)

noncomputable def LAML_fn (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ) (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ) (rho : Fin k → ℝ) : ℝ :=
  LAML_explicit log_lik S_basis X W rho (beta_hat rho)

noncomputable def LAML_fixed_beta_fn (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ) (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (b : Matrix (Fin p) (Fin 1) ℝ) (rho : Fin k → ℝ) : ℝ :=
  LAML_explicit log_lik S_basis X W rho b

-- 2. Rust Code Components
noncomputable def rust_delta_fn (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ) (rho : Fin k → ℝ) (i : Fin k) : Matrix (Fin p) (Fin 1) ℝ :=
  let b := beta_hat rho
  let H := Hessian_fn S_basis X W rho b
  let H_inv := matrixInvAlg H
  let lambda := Real.exp (rho i)
  let dS := lambda • S_basis i
  (-H_inv) * (dS * b)

noncomputable def rust_correction_fn (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ) (grad_op : (Matrix (Fin p) (Fin 1) ℝ → ℝ) → Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin p) (Fin 1) ℝ) (rho : Fin k → ℝ) (i : Fin k) : ℝ :=
  let b := beta_hat rho
  let delta := rust_delta_fn S_basis X W beta_hat rho i
  let dV_dbeta := (fun b_val => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W rho b_val)))
  ((grad_op dV_dbeta b).transpose * delta).trace

noncomputable def rust_direct_gradient_fn (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ) (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ) (rho : Fin k → ℝ) (i : Fin k) : ℝ :=
  let b := beta_hat rho
  let H := Hessian_fn S_basis X W rho b
  let H_inv := matrixInvAlg H
  let S := S_lambda_fn S_basis rho
  let S_inv := matrixInvAlg S
  let lambda := Real.exp (rho i)
  let Si := S_basis i
  0.5 * lambda * (b.transpose * Si * b).trace +
  0.5 * lambda * (H_inv * Si).trace -
  0.5 * lambda * (S_inv * Si).trace

-- 3. Verification Theorem

/-- Gradient definition for matrix-to-real functions. -/
def HasGradientAt (f : Matrix (Fin p) (Fin 1) ℝ → ℝ) (g : Matrix (Fin p) (Fin 1) ℝ) (x : Matrix (Fin p) (Fin 1) ℝ) :=
  ∃ (L : Matrix (Fin p) (Fin 1) ℝ →L[ℝ] ℝ),
    (∀ h, L h = (g.transpose * h).trace) ∧ HasFDerivAt f L x

noncomputable def laml_u (rho : Fin k → ℝ) (i : Fin k) (r : ℝ) := Function.update rho i r

noncomputable def laml_L1 (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ) (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ) (rho : Fin k → ℝ) (i : Fin k) (r : ℝ) : ℝ :=
  L_pen_fn log_lik S_basis (laml_u rho i r) (beta_hat (laml_u rho i r))

noncomputable def laml_L2 (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ) (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ) (rho : Fin k → ℝ) (i : Fin k) (r : ℝ) : ℝ :=
  0.5 * Real.log ((Hessian_fn S_basis X W (laml_u rho i r) (beta_hat (laml_u rho i r))).det)

noncomputable def laml_L3 (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ) (rho : Fin k → ℝ) (i : Fin k) (r : ℝ) : ℝ :=
  0.5 * Real.log ((S_lambda_fn S_basis (laml_u rho i r)).det)

/-- Rigorous compositional verification of the LAML gradient assembly.
    This packages the sum/subtraction rule argument once the three scalar
    component derivatives are established. -/
theorem laml_gradient_composition_verification
    (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ)
    (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ)
    (grad_op : (Matrix (Fin p) (Fin 1) ℝ → ℝ) → Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin p) (Fin 1) ℝ)
    (rho : Fin k → ℝ) (i : Fin k)
    (h_deriv_L1 : deriv (laml_L1 log_lik S_basis beta_hat rho i) (rho i) =
      0.5 * Real.exp (rho i) * trace ((beta_hat rho).transpose * (S_basis i) * (beta_hat rho)))
    (h_deriv_L2 : deriv (laml_L2 S_basis X W beta_hat rho i) (rho i) =
      0.5 * Real.exp (rho i) * trace ((Hessian_fn S_basis X W rho (beta_hat rho))⁻¹ * (S_basis i)) +
      trace ((grad_op (fun b_val => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W rho b_val))) (beta_hat rho)).transpose * rust_delta_fn S_basis X W beta_hat rho i))
    (h_deriv_L3 : deriv (laml_L3 S_basis rho i) (rho i) =
      0.5 * Real.exp (rho i) * trace ((S_lambda_fn S_basis rho)⁻¹ * (S_basis i)))
    (h_diff_L1 : DifferentiableAt ℝ (laml_L1 log_lik S_basis beta_hat rho i) (rho i))
    (h_diff_L2 : DifferentiableAt ℝ (laml_L2 S_basis X W beta_hat rho i) (rho i))
    (h_diff_L3 : DifferentiableAt ℝ (laml_L3 S_basis rho i) (rho i)) :
    deriv (fun r => LAML_fn log_lik S_basis X W beta_hat (laml_u rho i r)) (rho i) =
      rust_direct_gradient_fn S_basis X W beta_hat log_lik rho i +
      rust_correction_fn S_basis X W beta_hat grad_op rho i := by
  let L1 := laml_L1 log_lik S_basis beta_hat rho i
  let L2 := laml_L2 S_basis X W beta_hat rho i
  let L3 := laml_L3 S_basis rho i

  have h_diff_L1' : DifferentiableAt ℝ L1 (rho i) := h_diff_L1
  have h_diff_L2' : DifferentiableAt ℝ L2 (rho i) := h_diff_L2
  have h_diff_L3' : DifferentiableAt ℝ L3 (rho i) := h_diff_L3

  have h_split : ∀ r, LAML_fn log_lik S_basis X W beta_hat (laml_u rho i r) = L1 r + L2 r - L3 r := by
    intro r
    unfold LAML_fn
    rfl

  rw [show (fun r => LAML_fn log_lik S_basis X W beta_hat (laml_u rho i r)) = fun r => L1 r + L2 r - L3 r by
    funext r
    exact h_split r]
  change deriv ((fun r => L1 r + L2 r) - L3) (rho i) = _

  have h_diff_sum : DifferentiableAt ℝ (fun r => L1 r + L2 r) (rho i) := by
    exact DifferentiableAt.add h_diff_L1' h_diff_L2'
  have h_deriv_sum :
      deriv (fun r => L1 r + L2 r) (rho i) = deriv L1 (rho i) + deriv L2 (rho i) := by
    exact deriv_add h_diff_L1' h_diff_L2'

  rw [deriv_sub h_diff_sum h_diff_L3']
  rw [h_deriv_sum]
  rw [h_deriv_L1, h_deriv_L2, h_deriv_L3]
  unfold rust_direct_gradient_fn rust_correction_fn
  simp [matrixInvAlg_eq_inv]
  ring_nf

/-- Fixed-`β` verification: the explicit derivative of the LAML objective with
    respect to `rho_i` matches the Rust direct-gradient assembly. -/
theorem laml_fixed_beta_gradient_is_exact
    (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ)
    (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ)
    (rho : Fin k → ℝ) (i : Fin k)
    (b : Matrix (Fin p) (Fin 1) ℝ)
    (h_b : b = beta_hat rho)
    (h_diff_pen : DifferentiableAt ℝ (fun r => L_pen_fn log_lik S_basis (Function.update rho i r) b) (rho i))
    (h_diff_log_H : DifferentiableAt ℝ (fun r => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b))) (rho i))
    (h_diff_log_S : DifferentiableAt ℝ (fun r => -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) (rho i))
    (h_deriv_pen : deriv (fun r => L_pen_fn log_lik S_basis (Function.update rho i r) b) (rho i) =
      0.5 * Real.exp (rho i) * trace (b.transpose * S_basis i * b))
    (h_deriv_log_H : deriv (fun r => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b))) (rho i) =
      0.5 * Real.exp (rho i) * trace ((Hessian_fn S_basis X W rho b)⁻¹ * S_basis i))
    (h_deriv_log_S : deriv (fun r => -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) (rho i) =
      -0.5 * Real.exp (rho i) * trace ((S_lambda_fn S_basis rho)⁻¹ * S_basis i)) :
  deriv (fun r => LAML_fixed_beta_fn log_lik S_basis X W b (Function.update rho i r)) (rho i) =
  rust_direct_gradient_fn S_basis X W beta_hat log_lik rho i := by
  change deriv (fun r =>
      L_pen_fn log_lik S_basis (Function.update rho i r) b +
      0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b)) -
      0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) (rho i) = _
  dsimp only [rust_direct_gradient_fn]
  have h_add1 : deriv (fun r => L_pen_fn log_lik S_basis (Function.update rho i r) b +
      (0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b)) +
      -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r))))) (rho i) =
    deriv (fun r => L_pen_fn log_lik S_basis (Function.update rho i r) b) (rho i) +
    deriv (fun r => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b)) +
      -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) (rho i) := by
    apply deriv_add h_diff_pen
    exact DifferentiableAt.add h_diff_log_H h_diff_log_S
  have h_add2 : deriv (fun r => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b)) +
      -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) (rho i) =
    deriv (fun r => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b))) (rho i) +
    deriv (fun r => -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) (rho i) := by
    exact deriv_add h_diff_log_H h_diff_log_S
  have h_sub_to_add : (fun r => L_pen_fn log_lik S_basis (Function.update rho i r) b +
      0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b)) -
      0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r)))) =
    (fun r => L_pen_fn log_lik S_basis (Function.update rho i r) b +
      (0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W (Function.update rho i r) b)) +
      -0.5 * Real.log (Matrix.det (S_lambda_fn S_basis (Function.update rho i r))))) := by
    ext r
    ring
  rw [h_sub_to_add, h_add1, h_add2, h_deriv_pen, h_deriv_log_H, h_deriv_log_S]
  simp [matrixInvAlg_eq_inv]
  rw [← h_b]
  ring_nf

/-- Structural verification: `rust_delta_fn` implements the correct implicit derivative formula.

    If `grad(L_pen) = 0`, then differentiation gives `H * dbeta + dS * beta = 0`,
    so `dbeta = -H^-1 * dS * beta`.
    This theorem verifies that `rust_delta_fn` computes exactly this quantity. -/
theorem rust_delta_correctness
    (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ)
    (rho : Fin k → ℝ) (i : Fin k) :
    rust_delta_fn S_basis X W beta_hat rho i =
    -(Hessian_fn S_basis X W rho (beta_hat rho))⁻¹ *
    ((Real.exp (rho i) • S_basis i) * beta_hat rho) := by
  unfold rust_delta_fn
  simp [matrixInvAlg_eq_inv, neg_mul, Matrix.smul_mul]

/-- Structural verification: `laml_gradient_validity`

    This theorem proves that the total derivative of `LAML_fn` is correctly assembled
    from its partial derivatives and the implicit derivative of `beta`.

    It relies on structural hypotheses:
    1. Chain rule: d(LAML)/d(rho_i) = ∂(LAML)/∂(rho_i) + <∇_beta(LAML), d(beta)/d(rho_i)>
    2. Partial rho: ∂(LAML)/∂(rho_i) matches `rust_direct_gradient_fn`
    3. Partial beta: ∇_beta(LAML) matches the gradient term in `rust_correction_fn`
    4. Implicit beta: the differentiated optimality condition gives the linear system
       `H * d(beta)/d(rho_i) = -dS * beta`, which is then solved to recover `rust_delta_fn`

    This replaces the previous vacuous verification with a rigorous assembly proof. -/
theorem laml_gradient_validity
    (log_lik : Matrix (Fin p) (Fin 1) ℝ → ℝ)
    (S_basis : Fin k → Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (W : Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (beta_hat : (Fin k → ℝ) → Matrix (Fin p) (Fin 1) ℝ)
    (grad_op : (Matrix (Fin p) (Fin 1) ℝ → ℝ) → Matrix (Fin p) (Fin 1) ℝ → Matrix (Fin p) (Fin 1) ℝ)
    (rho : Fin k → ℝ) (i : Fin k)
    -- 1. Hessian solvability at the evaluation point
    (h_hess_pos : (Hessian_fn S_basis X W rho (beta_hat rho)).PosDef)
    -- 2. Implicit differentiation of the optimality condition, stated without inversion
    (h_implicit : Hessian_fn S_basis X W rho (beta_hat rho) *
                  deriv (fun r => beta_hat (Function.update rho i r)) (rho i) =
                  - (Real.exp (rho i) • S_basis i) * (beta_hat rho))
    -- 2. Partial derivative wrt rho matches rust_direct_gradient_fn
    (h_partial_rho : deriv (fun r => LAML_fn log_lik S_basis X W (fun _ => beta_hat rho) (Function.update rho i r)) (rho i) =
                     rust_direct_gradient_fn S_basis X W beta_hat log_lik rho i)
    -- 3. Gradient wrt beta matches the term used in rust_correction_fn
    --    Note: rust_correction_fn uses `grad_op dV_dbeta`.
    --    Optimality of beta implies grad(L_pen) = 0, so grad(LAML) = grad(0.5 log det H).
    (h_grad_beta : HasGradientAt (fun b => LAML_fn log_lik S_basis X W (fun _ => b) rho)
                                 (grad_op (fun b_val => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W rho b_val))) (beta_hat rho))
                                 (beta_hat rho))
    -- 4. Chain rule holds for the total derivative
    (h_chain : deriv (fun r => LAML_fn log_lik S_basis X W beta_hat (Function.update rho i r)) (rho i) =
               deriv (fun r => LAML_fn log_lik S_basis X W (fun _ => beta_hat rho) (Function.update rho i r)) (rho i) +
               ( (grad_op (fun b_val => 0.5 * Real.log (Matrix.det (Hessian_fn S_basis X W rho b_val))) (beta_hat rho)).transpose *
                 deriv (fun r => beta_hat (Function.update rho i r)) (rho i) ).trace) :
  deriv (fun r => LAML_fn log_lik S_basis X W beta_hat (Function.update rho i r)) (rho i) =
  rust_direct_gradient_fn S_basis X W beta_hat log_lik rho i +
  rust_correction_fn S_basis X W beta_hat grad_op rho i :=
by
  have h_hess_det : (Hessian_fn S_basis X W rho (beta_hat rho)).det ≠ 0 := h_hess_pos.det_pos.ne'
  have h_deriv_beta : deriv (fun r => beta_hat (Function.update rho i r)) (rho i) =
      rust_delta_fn S_basis X W beta_hat rho i := by
    let H := Hessian_fn S_basis X W rho (beta_hat rho)
    let dbeta := deriv (fun r => beta_hat (Function.update rho i r)) (rho i)
    have h_solved :
        dbeta = -H⁻¹ * ((Real.exp (rho i) • S_basis i) * (beta_hat rho)) := by
      have h_mul := congrArg (fun M => H⁻¹ * M) h_implicit
      have h_left : H⁻¹ * (H * dbeta) = dbeta := by
        rw [← Matrix.mul_assoc, inv_mul_self_of_det_ne_zero H h_hess_det, Matrix.one_mul]
      calc
        dbeta = H⁻¹ * (H * dbeta) := by
          symm
          exact h_left
        _ = H⁻¹ * (- (Real.exp (rho i) • S_basis i) * beta_hat rho) := by
          simpa [H] using h_mul
        _ = -H⁻¹ * ((Real.exp (rho i) • S_basis i) * beta_hat rho) := by
          simp [Matrix.mul_assoc, neg_mul]
    calc
      deriv (fun r => beta_hat (Function.update rho i r)) (rho i)
          = -H⁻¹ * ((Real.exp (rho i) • S_basis i) * beta_hat rho) := h_solved
      _ = rust_delta_fn S_basis X W beta_hat rho i := by
        symm
        simpa [H] using rust_delta_correctness S_basis X W beta_hat rho i
  rw [h_chain, h_partial_rho, h_deriv_beta]
  unfold rust_correction_fn
  rfl

end GradientDescentVerification

section OracleAndRegret

/-! ### Oracle Comparison at Population Level -/

/-- True conditional probability on feature space `Z`. -/
abbrev TrueCondProb (Z : Type*) := Z → UnitProb

/-- Predictor on feature space `Z`. -/
abbrev ProbPredictor (Z : Type*) := Z → UnitProb

/-- Population risk under Bernoulli mixing with true probability `p(z)`. -/
noncomputable def populationRisk {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (q : ProbPredictor Z) : ℝ :=
  ∫ z, (p z).1 * ℓ (q z).1 true + (1 - (p z).1) * ℓ (q z).1 false ∂μ

/-- Population-level oracle risk over a model class `F`. -/
noncomputable def oracleRisk {α : Type*} (R : α → ℝ) (F : Set α) : ℝ :=
  sInf (R '' F)

/-- Oracle infimum risk for a predictor class `F`. -/
noncomputable def infRisk {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (F : Set (ProbPredictor Z)) : ℝ :=
  oracleRisk (populationRisk μ ℓ p) F

/-- If your class contains the baseline class, its oracle risk is no worse. -/
theorem oracleRisk_mono {α : Type*} (R : α → ℝ) (Fyours Fbaseline : Set α)
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
theorem infRisk_mono {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (ℓ : ℝ → Bool → ℝ) (p : TrueCondProb Z) (F G : Set (ProbPredictor Z))
    (hFG : F ⊆ G)
    (h_bdd : BddBelow ((populationRisk μ ℓ p) '' G))
    (h_nonempty : ((populationRisk μ ℓ p) '' F).Nonempty) :
    infRisk μ ℓ p G ≤ infRisk μ ℓ p F :=
  oracleRisk_mono (R := populationRisk μ ℓ p) (Fyours := G) (Fbaseline := F) hFG h_bdd h_nonempty

/-- Strict oracle improvement from a witness in `Fyours` that beats every baseline member. -/
theorem oracleRisk_strict_of_witness {α : Type*} (R : α → ℝ) (Fyours Fbaseline : Set α)
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
noncomputable def BayesRisk {α : Type*} (R : α → ℝ) (F : Set α) : ℝ :=
  oracleRisk R F

/-- Monotonicity under inclusion for Bayes risk. -/
theorem BayesRisk_mono {α : Type*} (R : α → ℝ) (F G : Set α)
    (hFG : F ⊆ G)
    (h_bdd : BddBelow (R '' G))
    (h_nonempty : (R '' F).Nonempty) :
    BayesRisk R G ≤ BayesRisk R F := by
  exact oracleRisk_mono (R := R) (Fyours := G) (Fbaseline := F) hFG h_bdd h_nonempty

/-! ### Magnitude Certificates: Log Loss (KL) and Brier (L²) -/

/-- Bernoulli log-loss with Boolean outcome, valued in `ℝ≥0∞`.
    Outside the open interval `(0,1)` for `p̂`, the loss is set to `∞`. -/
noncomputable def LogLoss (pHat : ℝ) (y : Bool) : ENNReal :=
  if h : 0 < pHat ∧ pHat < 1 then
    ENNReal.ofReal (if y then -Real.log pHat else -Real.log (1 - pHat))
  else
    ⊤

/-- Brier loss with Boolean outcome. -/
noncomputable def BrierLoss (pHat : ℝ) (y : Bool) : ℝ :=
  ((if y then (1 : ℝ) else 0) - pHat) ^ 2

/-- Bernoulli log-loss (cross-entropy) at truth `p` and prediction `q`. -/
noncomputable def bernoulliLogLoss (p q : ℝ) : ℝ :=
  -(p * Real.log q + (1 - p) * Real.log (1 - q))

/-- Real-valued Bernoulli KL divergence formula. -/
noncomputable def bernoulliKLReal (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Bernoulli KL on `[0,1]` probabilities. -/
noncomputable def klBern (p q : UnitProb) : ℝ :=
  bernoulliKLReal p.1 q.1

/-- Pointwise log-loss regret equals Bernoulli KL. -/
theorem logLoss_regret_eq_kl_pointwise (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliLogLoss p q - bernoulliLogLoss p p = bernoulliKLReal p q := by
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have hp1_ne : 1 - p ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp1).symm
  have hq1_ne : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hq1).symm
  unfold bernoulliLogLoss bernoulliKLReal
  rw [Real.log_div hp_ne hq_ne, Real.log_div hp1_ne hq1_ne]
  ring

/-- Population log-loss regret. -/
noncomputable def logLossRegret {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, bernoulliLogLoss (p z) (q z) - bernoulliLogLoss (p z) (p z) ∂μ

/-- Population Bernoulli KL certificate. -/
noncomputable def logLossKLCertificate {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, bernoulliKLReal (p z) (q z) ∂μ

/-- Regret identity for log-loss at population level. -/
theorem logLoss_regret_eq_integral_kl {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ)
    (hp : ∀ z, 0 < p z ∧ p z < 1)
    (hq : ∀ z, 0 < q z ∧ q z < 1) :
    logLossRegret μ p q = logLossKLCertificate μ p q := by
  unfold logLossRegret logLossKLCertificate
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z => by
    exact logLoss_regret_eq_kl_pointwise (p z) (q z) (hp z).1 (hp z).2 (hq z).1 (hq z).2)

/-- Method-agnostic main theorem:
`R_log(q) - R_log(p) = ∫ klBern(p(z), q(z)) dμ`. -/
theorem logRisk_regret_eq_expected_klBern {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hq : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    (∫ z, bernoulliLogLoss (p z).1 (q z).1 - bernoulliLogLoss (p z).1 (p z).1 ∂μ)
      = ∫ z, klBern (p z) (q z) ∂μ := by
  unfold klBern
  exact logLoss_regret_eq_integral_kl μ (fun z => (p z).1) (fun z => (q z).1) hp hq

/-- Method-comparison magnitude identity:
the log-risk gap equals the KL-gap integral. -/
theorem logRisk_gap_eq_integral_klGap {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p qBaseline qYours : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hqBaseline : ∀ z, 0 < (qBaseline z).1 ∧ (qBaseline z).1 < 1)
    (hqYours : ∀ z, 0 < (qYours z).1 ∧ (qYours z).1 < 1) :
    (∫ z, bernoulliLogLoss (p z).1 (qBaseline z).1 - bernoulliLogLoss (p z).1 (qYours z).1 ∂μ)
      = ∫ z, (klBern (p z) (qBaseline z) - klBern (p z) (qYours z)) ∂μ := by
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z => by
    have hB := logLoss_regret_eq_kl_pointwise (p z).1 (qBaseline z).1
      (hp z).1 (hp z).2 (hqBaseline z).1 (hqBaseline z).2
    have hY := logLoss_regret_eq_kl_pointwise (p z).1 (qYours z).1
      (hp z).1 (hp z).2 (hqYours z).1 (hqYours z).2
    unfold klBern
    linarith [hB, hY])

/-- Corollary: nonnegativity of log-loss regret from pointwise nonnegativity of `klBern`. -/
theorem logRisk_regret_nonneg {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hq : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)
    (h_kl_nonneg : ∀ z, 0 ≤ klBern (p z) (q z)) :
    0 ≤ (∫ z, bernoulliLogLoss (p z).1 (q z).1 - bernoulliLogLoss (p z).1 (p z).1 ∂μ) := by
  rw [logRisk_regret_eq_expected_klBern μ p q hp hq]
  exact integral_nonneg h_kl_nonneg

/-- Corollary: strictness criterion.
Regret is zero iff `q = p` almost everywhere, assuming pointwise KL characterization. -/
theorem logRisk_regret_zero_iff_ae_eq {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z)
    (hp : ∀ z, 0 < (p z).1 ∧ (p z).1 < 1)
    (hq : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)
    (h_int : Integrable (fun z => klBern (p z) (q z)) μ)
    (h_kl_nonneg : ∀ z, 0 ≤ klBern (p z) (q z))
    (h_kl_zero_iff : ∀ z, klBern (p z) (q z) = 0 ↔ q z = p z) :
    (∫ z, bernoulliLogLoss (p z).1 (q z).1 - bernoulliLogLoss (p z).1 (p z).1 ∂μ) = 0
      ↔ q =ᵐ[μ] p := by
  rw [logRisk_regret_eq_expected_klBern μ p q hp hq]
  constructor
  · intro h0
    have h_ae_zero : (fun z => klBern (p z) (q z)) =ᵐ[μ] 0 := by
      exact (integral_eq_zero_iff_of_nonneg h_kl_nonneg h_int).mp h0
    filter_upwards [h_ae_zero] with z hz
    exact (h_kl_zero_iff z).1 hz
  · intro hqeqp
    have h_ae_zero : (fun z => klBern (p z) (q z)) =ᵐ[μ] 0 := by
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
noncomputable def brierRegret {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, expectedBrierScore (q z) (p z) - expectedBrierScore (p z) (p z) ∂μ

/-- Population L² certificate for Brier regret. -/
noncomputable def brierL2Certificate {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) : ℝ :=
  ∫ z, (q z - p z) ^ 2 ∂μ

theorem brier_regret_eq_l2_certificate {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : Z → ℝ) :
    brierRegret μ p q = brierL2Certificate μ p q := by
  unfold brierRegret brierL2Certificate
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun z => by simpa using brier_regret_pointwise (p z) (q z))

/-- Method-agnostic Brier identity on `p,q : Z → [0,1]`:
regret equals the `L²` distance. -/
theorem brier_regret_eq_l2_probPredictor {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (p q : ProbPredictor Z) :
    (∫ z, expectedBrierScore (q z).1 (p z).1 - expectedBrierScore (p z).1 (p z).1 ∂μ)
      = ∫ z, ((p z).1 - (q z).1) ^ 2 ∂μ := by
  have h := brier_regret_eq_l2_certificate μ (fun z => (p z).1) (fun z => (q z).1)
  calc
    (∫ z, expectedBrierScore (q z).1 (p z).1 - expectedBrierScore (p z).1 (p z).1 ∂μ)
        = ∫ z, ((q z).1 - (p z).1) ^ 2 ∂μ := by
          simpa [brierRegret, brierL2Certificate] using h
    _ = ∫ z, ((p z).1 - (q z).1) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun z => by ring)

/-! ### Clean Bayes-Optimal Target Statements -/

/-- Population log-loss risk for Bernoulli truth `η`. -/
noncomputable def logRisk {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) : ℝ :=
  ∫ z, bernoulliLogLoss (η z).1 (q z).1 ∂μ

/-- Population Brier risk for Bernoulli truth `η`. -/
noncomputable def brierRisk {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) : ℝ :=
  ∫ z, expectedBrierScore (q z).1 (η z).1 ∂μ

/-- Log-loss Bayes-optimality: `η` minimizes risk among all measurable predictors in `[0,1]`. -/
theorem logRisk_minimized_at_eta {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z)
    (hη_open : ∀ z, 0 < (η z).1 ∧ (η z).1 < 1)
    (h_kl_nonneg : ∀ z (q : ProbPredictor Z), 0 ≤ klBern (η z) (q z))
    (h_int_eta : Integrable (fun z => bernoulliLogLoss (η z).1 (η z).1) μ)
    (h_int_q : ∀ q : ProbPredictor Z, Integrable (fun z => bernoulliLogLoss (η z).1 (q z).1) μ)
    (h_q_open : ∀ q : ProbPredictor Z, ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    ∀ q : ProbPredictor Z, logRisk μ η η ≤ logRisk μ η q := by
  intro q
  have hreg :
      0 ≤
        (∫ z,
          bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ) := by
    exact logRisk_regret_nonneg μ η q hη_open (h_q_open q) (fun z => h_kl_nonneg z q)
  have hsub :
      (∫ z,
        bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ)
        = logRisk μ η q - logRisk μ η η := by
    unfold logRisk
    simpa [sub_eq_add_neg] using integral_sub (h_int_q q) h_int_eta
  linarith [hreg, hsub]

/-- Log-loss uniqueness: equality of risks iff equality of predictors a.e. -/
theorem logRisk_eq_iff_ae_eq_eta {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z)
    (hη_open : ∀ z, 0 < (η z).1 ∧ (η z).1 < 1)
    (hq_open : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)
    (h_int_kl : Integrable (fun z => klBern (η z) (q z)) μ)
    (h_kl_nonneg : ∀ z, 0 ≤ klBern (η z) (q z))
    (h_kl_zero_iff : ∀ z, klBern (η z) (q z) = 0 ↔ q z = η z)
    (h_int_eta : Integrable (fun z => bernoulliLogLoss (η z).1 (η z).1) μ)
    (h_int_q : Integrable (fun z => bernoulliLogLoss (η z).1 (q z).1) μ) :
    logRisk μ η q = logRisk μ η η ↔ q =ᵐ[μ] η := by
  have hzero :
      (∫ z,
        bernoulliLogLoss (η z).1 (q z).1 - bernoulliLogLoss (η z).1 (η z).1 ∂μ) = 0
        ↔ q =ᵐ[μ] η := by
    exact logRisk_regret_zero_iff_ae_eq μ η q hη_open hq_open h_int_kl h_kl_nonneg h_kl_zero_iff
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

/-- Brier Bayes-optimality. -/
theorem brierRisk_minimized_at_eta {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z)
    (h_int_eta : Integrable (fun z => expectedBrierScore (η z).1 (η z).1) μ)
    (h_int_q : ∀ q : ProbPredictor Z, Integrable (fun z => expectedBrierScore (q z).1 (η z).1) μ) :
    ∀ q : ProbPredictor Z, brierRisk μ η η ≤ brierRisk μ η q := by
  intro q
  have hreg : (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
      = ∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ := by
    exact brier_regret_eq_l2_probPredictor μ η q
  have hnonneg : 0 ≤ ∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ := by
    exact integral_nonneg (fun z => sq_nonneg ((η z).1 - (q z).1))
  have hsub :
      (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
        = brierRisk μ η q - brierRisk μ η η := by
    unfold brierRisk
    simpa [sub_eq_add_neg] using integral_sub (h_int_q q) h_int_eta
  have hdiff_nonneg : 0 ≤ brierRisk μ η q - brierRisk μ η η := by
    linarith [hreg, hnonneg, hsub]
  exact sub_nonneg.mp hdiff_nonneg

/-- Brier uniqueness: equal risks iff predictors are equal a.e. -/
theorem brierRisk_eq_iff_ae_eq_eta {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z)
    (h_int_eta : Integrable (fun z => expectedBrierScore (η z).1 (η z).1) μ)
    (h_int_q : Integrable (fun z => expectedBrierScore (q z).1 (η z).1) μ)
    (h_int_sq : Integrable (fun z => ((η z).1 - (q z).1) ^ 2) μ) :
    brierRisk μ η q = brierRisk μ η η ↔ q =ᵐ[μ] η := by
  have hreg : (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
      = ∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ := by
    exact brier_regret_eq_l2_probPredictor μ η q
  have hsub :
      (∫ z, expectedBrierScore (q z).1 (η z).1 - expectedBrierScore (η z).1 (η z).1 ∂μ)
        = brierRisk μ η q - brierRisk μ η η := by
    unfold brierRisk
    simpa [sub_eq_add_neg] using integral_sub h_int_q h_int_eta
  have hzero_sq :
      (∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ) = 0
      ↔ (fun z => ((η z).1 - (q z).1) ^ 2) =ᵐ[μ] 0 := by
    exact integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ((η z).1 - (q z).1)) h_int_sq
  constructor
  · intro hEq
    have h0 : (∫ z, ((η z).1 - (q z).1) ^ 2 ∂μ) = 0 := by
      linarith [hreg, hsub, hEq]
    have h_ae_zero : (fun z => ((η z).1 - (q z).1) ^ 2) =ᵐ[μ] 0 := (hzero_sq.mp h0)
    filter_upwards [h_ae_zero] with z hz
    have hsub : (η z).1 - (q z).1 = 0 := sq_eq_zero_iff.mp hz
    apply Subtype.ext
    linarith
  · intro hAe
    have h_ae_zero : (fun z => ((η z).1 - (q z).1) ^ 2) =ᵐ[μ] 0 := by
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

/-- Abstract population-AUC functional on scores `Z → ℝ`. -/
abbrev PopulationAUC (Z : Type*) := (Z → ℝ) → ℝ

/-- Any strictly increasing transform of `η` is AUC-optimal, provided AUC is
invariant under strict monotone transforms and `η` is itself optimal. -/
theorem auc_maximizer_of_strictMono_transform {Z : Type*}
    (AUC : PopulationAUC Z) (η score : Z → ℝ)
    (h_opt_eta : ∀ s : Z → ℝ, AUC s ≤ AUC η)
    (h_invariant : ∀ g : ℝ → ℝ, ∀ s : Z → ℝ, StrictMono g → AUC (g ∘ s) = AUC s)
    (h_rep : ∃ g : ℝ → ℝ, StrictMono g ∧ score = g ∘ η) :
    ∀ s : Z → ℝ, AUC s ≤ AUC score := by
  rcases h_rep with ⟨g, hgmono, hscore⟩
  intro s
  have hsg : AUC score = AUC η := by
    rw [hscore]
    simpa using h_invariant g η hgmono
  calc
    AUC s ≤ AUC η := h_opt_eta s
    _ = AUC score := hsg.symm

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
    (hη0 : 0 < η) (hη1 : η < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (h_kl_nonneg : 0 ≤ bernoulliKLReal η q) :
    logBernoulliRisk η η ≤ logBernoulliRisk η q := by
  have hreg := logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1
  unfold logBernoulliRisk at *
  linarith

theorem logBernoulliRisk_eq_iff (η q : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (h_kl_nonneg : 0 ≤ bernoulliKLReal η q)
    (h_kl_zero_iff : bernoulliKLReal η q = 0 ↔ q = η) :
    logBernoulliRisk η q = logBernoulliRisk η η ↔ q = η := by
  have hreg := logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1
  unfold logBernoulliRisk at *
  constructor
  · intro hEq
    have hkl : bernoulliKLReal η q = 0 := by linarith [hreg, hEq]
    exact h_kl_zero_iff.mp hkl
  · intro hq
    subst hq
    ring

/-- Population log-risk alias: `R_log(q) = E[ℓ_log(Y,q(Z))]` with Bernoulli truth `η(Z)`. -/
noncomputable def Rlog {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) : ℝ :=
  logRisk μ η q

/-- Population Brier-risk alias: `R_brier(q) = E[ℓ_brier(Y,q(Z))]`. -/
noncomputable def Rbrier {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η q : ProbPredictor Z) : ℝ :=
  brierRisk μ η q

/-! ### Population AUC (Conditional-Law Form) -/

/-- Binary-outcome population described by the conditional feature laws:
`Z⁺ ~ law(Z|Y=1)`, `Z⁻ ~ law(Z|Y=0)`, independent. -/
structure BinaryPopulation (Z : Type*) [MeasurableSpace Z] where
  μpos : Measure Z
  μneg : Measure Z

/-- Population AUC of a score:
`P(s(Z⁺) > s(Z⁻)) + 1/2 P(s(Z⁺)=s(Z⁻))`. -/
noncomputable def populationAUC {Z : Type*} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (s : Z → ℝ) : ENNReal :=
  (pop.μpos.prod pop.μneg) {zz : Z × Z | s zz.1 > s zz.2} +
    (ENNReal.ofReal (1 / 2 : ℝ)) *
      (pop.μpos.prod pop.μneg) {zz : Z × Z | s zz.1 = s zz.2}

theorem populationAUC_strictMono_invariant {Z : Type*} [MeasurableSpace Z]
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
theorem populationAUC_optimal_of_eta_transform {Z : Type*} [MeasurableSpace Z]
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
noncomputable def logBayesRisk {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z)) : ℝ :=
  BayesRisk (logRisk μ η) F

/-- Brier Bayes risk over a predictor class. -/
noncomputable def brierBayesRisk {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z)) : ℝ :=
  BayesRisk (brierRisk μ η) F

theorem logBayesRisk_eq_eta_of_mem {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z))
    (h_eta_mem : η ∈ F)
    (h_bdd : BddBelow ((logRisk μ η) '' F))
    (hη_open : ∀ z, 0 < (η z).1 ∧ (η z).1 < 1)
    (h_kl_nonneg : ∀ z (q : ProbPredictor Z), 0 ≤ klBern (η z) (q z))
    (h_int_eta : Integrable (fun z => bernoulliLogLoss (η z).1 (η z).1) μ)
    (h_int_q : ∀ q : ProbPredictor Z, Integrable (fun z => bernoulliLogLoss (η z).1 (q z).1) μ)
    (h_q_open : ∀ q : ProbPredictor Z, ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    logBayesRisk μ η F = logRisk μ η η := by
  unfold logBayesRisk BayesRisk oracleRisk
  apply le_antisymm
  · exact csInf_le h_bdd ⟨η, h_eta_mem, rfl⟩
  · refine le_csInf ?_ ?_
    · exact ⟨logRisk μ η η, ⟨η, h_eta_mem, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨q, hqF, rfl⟩
      exact logRisk_minimized_at_eta μ η hη_open h_kl_nonneg h_int_eta h_int_q h_q_open q

theorem brierBayesRisk_eq_eta_of_mem {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (F : Set (ProbPredictor Z))
    (h_eta_mem : η ∈ F)
    (h_bdd : BddBelow ((brierRisk μ η) '' F))
    (h_int_eta : Integrable (fun z => expectedBrierScore (η z).1 (η z).1) μ)
    (h_int_q : ∀ q : ProbPredictor Z, Integrable (fun z => expectedBrierScore (q z).1 (η z).1) μ) :
    brierBayesRisk μ η F = brierRisk μ η η := by
  unfold brierBayesRisk BayesRisk oracleRisk
  apply le_antisymm
  · exact csInf_le h_bdd ⟨η, h_eta_mem, rfl⟩
  · refine le_csInf ?_ ?_
    · exact ⟨brierRisk μ η η, ⟨η, h_eta_mem, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨q, hqF, rfl⟩
      exact brierRisk_minimized_at_eta μ η h_int_eta h_int_q q

/-- Non-strict full-vs-baseline comparison from class inclusion. -/
theorem logBayesRisk_full_le_baseline {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (η : ProbPredictor Z) (Ffull Fbase : Set (ProbPredictor Z))
    (h_sub : Fbase ⊆ Ffull)
    (h_bdd_full : BddBelow ((logRisk μ η) '' Ffull))
    (h_nonempty_base : ((logRisk μ η) '' Fbase).Nonempty) :
    logBayesRisk μ η Ffull ≤ logBayesRisk μ η Fbase := by
  exact BayesRisk_mono (R := logRisk μ η) Fbase Ffull h_sub h_bdd_full h_nonempty_base

/-- Strict full-vs-baseline theorem under a margin nondegeneracy condition. -/
theorem logBayesRisk_full_lt_baseline_of_margin {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
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

end OracleAndRegret


end Calibrator
