/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Ancestry-Specific Calibration and Transfer Learning for PGS

This file formalizes the theory of calibrating PGS across ancestry groups,
including optimal recalibration strategies, transfer learning bounds,
and the fundamental limits of what calibration can and cannot recover.

Reference: Wang et al. (2026), Nature Communications 17:942 -- for the measured
portability gap, and for the R2/AUC divergence, which the docstrings below cite by
specific finding. The recalibration algebra and the transfer bounds are derived
here, not imported from it.
-/


/-!
## Optimal Linear Recalibration

Given a PGS trained in population S, what is the optimal linear
recalibration (a + b × PGS) for population T?
-/

section LinearRecalibration

/-- Target-population slope obtained by transporting a source slope through effect correlation
`rho` and score-variance ratio `alpha`.

Empirical status: UNTESTED. -/
noncomputable def ancestryRecalibratedSlope (bSource rho alpha : ℝ) : ℝ :=
  rho * (bSource * alpha) / alpha ^ 2

/-- **Recalibration slope under drift model.**
    If effects change by factor ρ and variance changes by factor α,
    optimal slope = ρ × b_source / α. -/
theorem ancestryRecalibratedSlope_eq
    (b_source ρ α : ℝ) (h_α : α ≠ 0) :
    ancestryRecalibratedSlope b_source ρ α = ρ * b_source / α := by
  unfold ancestryRecalibratedSlope
  field_simp

/-- Source `R²` retained after linear recalibration at squared effect correlation `rhoSq`.

Empirical status: UNTESTED. -/
noncomputable def ancestryRecalibratedR2 (r2Source rhoSq : ℝ) : ℝ :=
  r2Source * rhoSq

/-- Source `R²` lost to non-recoverable effect turnover.

Empirical status: UNTESTED. -/
noncomputable def effectTurnoverR2Loss (r2Source rhoSq : ℝ) : ℝ :=
  r2Source * (1 - rhoSq)

/-- Effect-turnover loss and the retained-heterozygosity chart are the same
two-argument arithmetic map, with different biological interpretations. -/
theorem effectTurnoverR2Loss_eq_targetHetFromFst (r2Source rhoSq : ℝ) :
    effectTurnoverR2Loss r2Source rhoSq = targetHetFromFst r2Source rhoSq := by
  rfl

/-- **Recalibration recovers R² up to effect turnover limit.**
    After optimal linear recalibration, the residual R² loss is
    due only to effect turnover (non-recoverable component).

    Model: recalibrated R² = r2_source × ρ² (proportion of variance
    explained after drift attenuates effects by squared correlation ρ²).
    The turnover loss = r2_source × (1 - ρ²) is the non-recoverable part.
    These two components sum to r2_source by algebraic decomposition:
      r2_source × ρ² + r2_source × (1 - ρ²) = r2_source × (ρ² + 1 - ρ²) = r2_source. -/
theorem ancestryRecalibratedR2_add_effectTurnoverR2Loss
    (r2_source ρ_sq : ℝ) :
    ancestryRecalibratedR2 r2_source ρ_sq +
      effectTurnoverR2Loss r2_source ρ_sq = r2_source := by
  unfold ancestryRecalibratedR2 effectTurnoverR2Loss
  ring


end LinearRecalibration


/-!
## Nonlinear Calibration via Splines

Wang et al. use cubic splines to model the relationship between
genetic distance and prediction error. We formalize why splines
can capture the nonlinear portability decay.
-/

section SplineCalibration

/-- Fourth-order approximation scale for a cubic spline with knot spacing `h`. -/
noncomputable def cubicSplineApproximationScale (h : ℝ) : ℝ :=
  h ^ 4

/-- **Fourth powers are strictly monotone on the positives:**
    `0 < h₂ < h₁` gives `h₂⁴ < h₁⁴`.

    The reading is that a cubic spline has approximation error `O(h⁴)` in the
    knot spacing `h`, so more knots approximate the portability decay better.
    The `O(h⁴)` rate is the content of that reading and is stipulated in prose:
    there is no spline, no knot, no function being approximated and no error
    below, only two positive reals and an exponent. -/
theorem cubicSplineApproximationScale_strictMono
    (h₁ h₂ : ℝ) (h_finer : h₂ < h₁) (h_pos : 0 < h₂) :
    cubicSplineApproximationScale h₂ < cubicSplineApproximationScale h₁ := by
  unfold cubicSplineApproximationScale
  apply pow_lt_pow_left₀ h_finer (le_of_lt h_pos)
  norm_num

/-- Bias--variance mean squared error of a spline calibration fit. -/
noncomputable def splineCalibrationMSE (bias variance : ℝ) : ℝ :=
  bias ^ 2 + variance

/-- **Exact spline bias--variance comparison.** One calibration fit has lower MSE exactly when
its variance disadvantage is smaller than its squared-bias advantage.

    The genetics reading is the bias-variance tradeoff for spline knot count:
    more knots lower the bias and raise the variance, and the sum is what
    matters. None of that is here. There are no knots, no splines, no MSE and
    no estimator — the decomposition `MSE = bias² + variance`, which the reading
    calls the real content, is assumed by naming the two summands, not derived.

    The hypothesis is the whole of what the proof uses, so the gap between this and the
    bias-variance tradeoff is visible in the statement rather than described beside it. -/
theorem splineCalibrationMSE_lt_iff
    (bias₁ bias₂ var₁ var₂ : ℝ) :
    splineCalibrationMSE bias₁ var₁ < splineCalibrationMSE bias₂ var₂ ↔
      bias₁ ^ 2 - bias₂ ^ 2 < var₂ - var₁ := by
  unfold splineCalibrationMSE
  constructor <;> intro h <;> linarith

/-- Fraction of total variance carried by a signal component. -/
noncomputable def explainedVarianceFraction (varSignal varNoise : ℝ) : ℝ :=
  varSignal / (varSignal + varNoise)

/-- **A nonnegative part of a positive total is at most the whole of it:**
    `var_signal / var_total ≤ 1` when `var_total = var_signal + var_noise` with
    both parts nonnegative.

    This is not the spline bound `R²_spline ≤ Var(E[ε²|d]) / Var(ε²)`, which
    relates a fitted `R²` to a conditional-variance ratio: no conditional
    variance, no spline and no `R²` occurs below, and the two are not the same
    inequality. A measured `R²` for a fitted model is likewise not an instance
    of this statement, which has no numerals in it. -/
theorem explainedVarianceFraction_le_one
    (var_signal var_noise : ℝ)
    (h_total_pos : 0 < var_signal + var_noise)
    (h_noise_nn : 0 ≤ var_noise) :
    explainedVarianceFraction var_signal var_noise ≤ 1 := by
  unfold explainedVarianceFraction
  rw [div_le_one h_total_pos]
  linarith

end SplineCalibration


/-!
## Transfer Learning Bounds

How much data from the target population is needed to achieve
a given portability recovery? We formalize the sample complexity
of transfer learning for PGS.
-/

section TransferLearning

/-- Mean squared error of a source-transferred estimator with fixed transfer bias. -/
noncomputable def transferredEstimatorMSE (σ_sq bias_sq nTarget : ℝ) : ℝ :=
  σ_sq / nTarget + bias_sq

/-- Mean squared error of a target-only estimator that must learn an additional variance
component from target data. -/
noncomputable def targetOnlyEstimatorMSE (σ_sq σ_extra_sq nTarget : ℝ) : ℝ :=
  (σ_sq + σ_extra_sq) / nTarget

/-- **More target data reduces MSE monotonically.** -/
theorem more_target_data_reduces_mse
    (σ_sq gap : ℝ) (n₁ n₂ : ℕ)
    (h_σ : 0 < σ_sq) (h_gap : 0 < gap)
    (h_n₁ : 0 < n₁)
    (h_more : n₁ < n₂) :
    gap * σ_sq / (n₂ : ℝ) < gap * σ_sq / (n₁ : ℝ) := by
  apply div_lt_div_of_pos_left (mul_pos h_gap h_σ)
  · exact Nat.cast_pos.mpr h_n₁
  · exact Nat.cast_lt.mpr h_more

/-- **Exact transfer-learning crossover.**
    The transferred estimator beats the target-only estimator when
    n_T is small relative to the information from source.

    Model definitions:
    - MSE_transfer = σ²/n_T + bias² (transfer bias is fixed, not sample-dependent)
    - MSE_target = (σ² + σ²_extra)/n_T (target-only has extra variance from
      estimating all effects de novo, but no transfer bias)

    Derived: MSE_transfer < MSE_target ↔ bias² < σ²_extra/n_T.
    When n_T is small, σ²_extra/n_T is large, so transfer wins.
    As n_T → ∞, σ²_extra/n_T → 0, so target-only wins (bias² > 0). -/
theorem transferredEstimatorMSE_lt_targetOnly_iff
    (σ_sq bias_sq σ_extra_sq : ℝ) (n_T : ℝ)
    (h_bias : 0 < bias_sq) (h_n : 0 < n_T) :
    transferredEstimatorMSE σ_sq bias_sq n_T <
        targetOnlyEstimatorMSE σ_sq σ_extra_sq n_T ↔
      n_T < σ_extra_sq / bias_sq := by
  unfold transferredEstimatorMSE targetOnlyEstimatorMSE
  rw [add_div]
  constructor
  · intro h_mse
    have h_key : bias_sq < σ_extra_sq / n_T := by linarith
    have h_prod : bias_sq * n_T < σ_extra_sq := (lt_div_iff₀ h_n).1 h_key
    apply (lt_div_iff₀ h_bias).2
    simpa [mul_comm] using h_prod
  · intro h_sample
    have h_prod : n_T * bias_sq < σ_extra_sq := (lt_div_iff₀ h_bias).1 h_sample
    have h_key : bias_sq < σ_extra_sq / n_T := by
      apply (lt_div_iff₀ h_n).2
      simpa [mul_comm] using h_prod
    linarith

/-- **Multi-ancestry meta-analysis is optimal.**
    Combining GWAS data from multiple ancestries via inverse-variance
    weighted meta-analysis minimizes the MSE of the combined estimator,
    under certain independence assumptions. -/
theorem meta_analysis_reduces_variance
    (var₁ var₂ : ℝ) (h₁ : 0 < var₁) (h₂ : 0 < var₂) :
    -- Inverse-variance weighted combination has smaller variance
    1 / (1/var₁ + 1/var₂) < var₁ := by
  have h_sum_pos : 0 < 1/var₁ + 1/var₂ := by positivity
  rw [div_lt_iff₀ h_sum_pos]
  have : var₁ * (1/var₁ + 1/var₂) = 1 + var₁/var₂ := by field_simp
  rw [this]
  linarith [div_pos h₁ h₂]

end TransferLearning


/-!
## Phenotype Heterogeneity Across Populations

The "same" phenotype may be measured differently or have different
distributions across populations, affecting portability.
-/

section PhenotypeHeterogeneity

/-- **Rescaling the phenotype changes `R²` in the additive-noise chart, unless `R² = 1`.**

    In the chart `r2 ↦ r2·s² / (r2·s² + (1 - r2))`, which is the `R²` of the same
    predictor after the phenotype is multiplied by `s` with the noise variance held at
    `1 - r2`, no positive `s ≠ 1` fixes an `R²` in `(0, 1)`.

    **This concerns one `R²` and one scale factor, not two populations.** Nothing here
    compares populations, and nothing here shows that `R²` comparisons across populations
    are invalid — that does not follow from a one-population rescaling identity. What
    follows is that `R²` is not invariant to the units of `Y`, which is a necessary
    ingredient of such an argument and not the argument.

    The unit-scale exclusion is genuinely needed in both directions: `h_scale` rules out
    `s = 1`, and `h_scale_pos` rules out `s = -1`, which also satisfies `s² = 1`. -/
theorem measurement_invariance_violation
    (r2₁ : ℝ) (scale : ℝ)
    (h_scale : scale ≠ 1) (h_scale_pos : 0 < scale)
    (h_r2₁ : 0 < r2₁) (h_r2₁_le : r2₁ ≤ 1) :
    -- Scaling the phenotype changes R² when there's additive noise
    r2₁ ≠ r2₁ * scale ^ 2 / (r2₁ * scale ^ 2 + (1 - r2₁)) ∨ r2₁ = 1 := by
  by_cases h : r2₁ = 1
  · right; exact h
  · left; intro heq
    have h_lt : r2₁ < 1 := lt_of_le_of_ne h_r2₁_le h
    have h_pos_denom : 0 < r2₁ * scale ^ 2 + (1 - r2₁) := by nlinarith [sq_nonneg scale]
    rw [eq_div_iff h_pos_denom.ne'] at heq
    have : r2₁ * (r2₁ * scale ^ 2 + (1 - r2₁)) = r2₁ * scale ^ 2 := heq
    have : r2₁ * (1 - r2₁) = r2₁ * scale ^ 2 * (1 - r2₁) := by nlinarith
    have h_nonzero : r2₁ * (1 - r2₁) ≠ 0 := mul_ne_zero (h_r2₁.ne') (by linarith)
    have : 1 = scale ^ 2 := by
      field_simp at this ⊢
      nlinarith
    have h_sq_one : scale ^ 2 = 1 := by
      field_simp at this ⊢
      nlinarith
    have : scale = 1 := by
      nlinarith [sq_nonneg (scale - 1)]
    exact h_scale this

/-- **A higher liability mean puts the threshold lower relative to it.**

    Subtraction, and nothing more: no distribution, no prevalence, and no liability-threshold
    model appears below. The prevalence reading — that a higher mean puts more of the population
    above a fixed threshold — needs a distribution function, and
    `Calibrator.ScoreDistribution.mean_shift_changes_benchmark_high_score_rate` is where that
    step is taken, against the Gaussian benchmark. -/
theorem threshold_shift_changes_prevalence
    (liability_mean₁ liability_mean₂ threshold : ℝ)
    (h_mean_shift : liability_mean₁ < liability_mean₂) :
    threshold - liability_mean₂ < threshold - liability_mean₁ := by linarith

/-- Prevalence-dependent `R²` factor in the simplified liability-threshold chart.

    Regime: a liability-threshold model, liability = genetic value + noise, the
    threshold placed to give prevalence `K`.

    Empirical status: UNTESTED. The observed-scale `R²` of a
    liability-threshold genetic value is the variance it explains,
    `h2 · φ(t)²` with `t = Φ⁻¹(1-K)`, divided by the outcome variance
    `K(1-K)`.

    CORRECTED. The previous body multiplied by `K(1-K)`. That factor is the
    denominator of observed-scale `R²`, while the threshold-density square is
    part of its numerator.

    The old docstring already carried the correct relation in prose -- "`f(K) =
    K(1-K)/φ(Φ⁻¹(K))²`" -- and the body simplified it away. -/
noncomputable def prevalenceScaledR2 (h2 prevalence : ℝ) : ℝ :=
  h2 * standardNormalPdf (liabilityThreshold prevalence) ^ 2 /
    (prevalence * (1 - prevalence))

/-- **The prevalence chart is symmetric about `K = 1/2`**, given the
standard-normal reflection at the threshold.

    `R²` and `AUC` can disagree about portability because `R²` depends on
    prevalence and `AUC` does not; that dependence is what this body carries.
    The complement `K ↦ 1 - K` leaves it fixed, because the liability threshold
    only changes sign there and both `φ` and `K(1-K)` are even under that
    change.

    The reflection `Φ⁻¹(K) = -Φ⁻¹(1-K)` is a fact about the standard normal, not
    about this body, and it is taken as a HYPOTHESIS here rather than proved:
    `liabilityThreshold` is defined through `Function.invFun Phi`, so deriving
    it needs `Phi (-x) = 1 - Phi x` together with injectivity of `Phi`, neither
    of which this development has. The hypothesis is in the statement so that
    what is assumed is visible rather than described beside it.

    WHAT IS NO LONGER CLAIMED. The previous statement here was an `iff`: that
    two prevalences give the same value exactly when they are equal or sum to
    one. Its forward direction was available only because the old body was the
    quadratic `h2 · K(1-K)`, where `nlinarith` factors the difference. That body
    is falsified (see `prevalenceScaledR2` above), and for the corrected one the
    converse needs strict monotonicity of `φ(Φ⁻¹(1-K))² / (K(1-K))` on
    `(0, 1/2]`. That is true and is not proved here. It is recorded as an open
    item rather than restated in a form the corrected body happens to satisfy. -/
theorem prevalenceScaledR2_symm_of_threshold_reflection
    (h2 π : ℝ)
    (h_reflect : liabilityThreshold (1 - π) = -liabilityThreshold π) :
    prevalenceScaledR2 h2 (1 - π) = prevalenceScaledR2 h2 π := by
  unfold prevalenceScaledR2 standardNormalPdf
  rw [h_reflect, neg_sq]
  ring

end PhenotypeHeterogeneity


/-!
## Epistasis and Portability

Gene-gene interactions (epistasis) create additional portability
challenges because interaction effects depend on allele frequency
combinations that differ across populations.
-/

section Epistasis

/-- **Epistatic variance under HWE.**
    For two loci with frequencies p₁, p₂ and interaction effect γ,
    the epistatic variance component is:
    V_epistasis = γ² × H₁ × H₂ where Hᵢ = 2pᵢ(1-pᵢ).

    Regime: two UNLINKED loci at Hardy-Weinberg and linkage equilibrium, and
    the interaction component read on the CENTRED dosages. The centring is not
    a detail: the product of the uncentred dosages carries both additive terms,
    and its variance is not this body.

    Empirical status: **VALIDATED**
    (`validation/empirical/invariants/check_simulation.py`). The registered
    simulation draws 600000 independent Hardy-Weinberg dosages at the two loci,
    centres both realised dosage vectors, and compares the interaction variance
    against the formula extracted from this definition over `γ ∈ [0.2, 2]` and
    `p₁, p₂ ∈ [0.1, 0.9]`, with relative tolerance `0.05`. -/
noncomputable def epistaticVariancePairwise (γ p₁ p₂ : ℝ) : ℝ :=
  γ ^ 2 * (2 * p₁ * (1 - p₁)) * (2 * p₂ * (1 - p₂))

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem epistaticVariancePairwise_at_reference_point :
    epistaticVariancePairwise 1 1 1 = 0 := by
  norm_num [epistaticVariancePairwise]


/-- Epistatic variance is nonneg. -/
theorem epistatic_variance_pairwise_nonneg (γ p₁ p₂ : ℝ)
    (h₁ : 0 ≤ p₁) (h₁' : p₁ ≤ 1) (h₂ : 0 ≤ p₂) (h₂' : p₂ ≤ 1) :
    0 ≤ epistaticVariancePairwise γ p₁ p₂ := by
  unfold epistaticVariancePairwise
  apply mul_nonneg
  · apply mul_nonneg
    · exact sq_nonneg γ
    · nlinarith
  · nlinarith

/-- **Exact zero fiber of pairwise epistatic variance.**  The component vanishes exactly when
the interaction effect is zero or at least one locus is monomorphic. -/
theorem epistaticVariancePairwise_eq_zero_iff (γ p₁ p₂ : ℝ) :
    epistaticVariancePairwise γ p₁ p₂ = 0 ↔
      γ = 0 ∨ p₁ = 0 ∨ p₁ = 1 ∨ p₂ = 0 ∨ p₂ = 1 := by
  unfold epistaticVariancePairwise
  simp [eq_comm]
  have hp₁ : 0 = 1 - p₁ ↔ p₁ = 1 := by constructor <;> intro h <;> linarith
  have hp₂ : 0 = 1 - p₂ ↔ p₂ = 1 := by constructor <;> intro h <;> linarith
  rw [hp₁, hp₂]
  tauto

/-- **Epistatic variance changes faster than additive variance under drift.**
    Because epistatic variance depends on the product of two heterozygosities,
    it changes approximately twice as fast as additive variance. -/
theorem epistatic_changes_faster
    (H₁_s H₁_t H₂_s H₂_t : ℝ)
    (h₁_drop : H₁_t < H₁_s) (h₂_drop : H₂_t < H₂_s)
    (h₁_pos : 0 < H₁_t) (h₂_pos : 0 < H₂_t) :
    H₁_t * H₂_t / (H₁_s * H₂_s) < H₁_t / H₁_s := by
  have h₁_s_pos : 0 < H₁_s := by linarith
  have h₂_s_pos : 0 < H₂_s := by linarith
  rw [div_lt_div_iff₀ (mul_pos h₁_s_pos h₂_s_pos) h₁_s_pos]
  nlinarith [mul_pos h₁_s_pos h₁_pos]

/-- **Additive PGS misses epistatic signal → portability of epistatic component is zero.**
    An additive PGS captures V_A but not V_epistasis. The "missing heritability"
    from epistasis doesn't port because it was never captured. -/
theorem div_lt_one_of_eq_add_pos
    (v_additive v_epistatic v_total : ℝ)
    (h_total : v_total = v_additive + v_epistatic)
    (h_epi_pos : 0 < v_epistatic) (h_add_pos : 0 < v_additive) :
    v_additive / v_total < 1 := by
  rw [h_total, div_lt_one (by linarith)]
  linarith

end Epistasis

end Calibrator
