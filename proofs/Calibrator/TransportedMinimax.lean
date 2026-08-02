import Mathlib

namespace Calibrator

/-!
# Transport-aware spectral regularization

For the relaxed robust objective

`(||(φ - 1)S|| + r)² + τ² ||φ||²`,

write `a = ||(φ - 1)S||`. Differentiating at a nonzero-bias interior point gives a ridge
filter with effective parameter

`η = τ² a/(a+r)`.

The direction matters: `η < τ²` whenever `r > 0`. Transport uncertainty makes residual
bias more costly and therefore calls for **less** shrinkage. This corrects the inverse
factor `τ²(1+r/a)` in the proposed design manuscript.

The module proves the finite algebra and its sign. Establishing a Whittle reduction,
near-unit-root uniformity, or a sharp `3/(2n)` minimax constant requires separate
statistical experiments and is not asserted here.
-/

/-- Effective ridge parameter at bias norm `a`, noise level `τ`, and drift radius `r`. -/
noncomputable def transportedRidgeParameter (τ a r : ℝ) : ℝ :=
  τ ^ 2 * a / (a + r)

/-- Robust drift strictly decreases the interior effective ridge parameter. -/
theorem transportedRidgeParameter_lt_source (τ a r : ℝ)
    (hτ : τ ≠ 0) (ha : 0 < a) (hr : 0 < r) :
    transportedRidgeParameter τ a r < τ ^ 2 := by
  have hden : 0 < a + r := by linarith
  have hfrac : a / (a + r) < 1 := (div_lt_one hden).2 (by linarith)
  have hτsq : 0 < τ ^ 2 := sq_pos_of_ne_zero hτ
  unfold transportedRidgeParameter
  rw [mul_div_assoc]
  nlinarith [mul_lt_mul_of_pos_left hfrac hτsq]

/-- The corrected ridge parameter remains positive. -/
theorem transportedRidgeParameter_pos (τ a r : ℝ)
    (hτ : τ ≠ 0) (ha : 0 < a) (hr : 0 ≤ r) :
    0 < transportedRidgeParameter τ a r := by
  unfold transportedRidgeParameter
  exact div_pos (mul_pos (sq_pos_of_ne_zero hτ) ha) (by linarith)

/-- Scalar form of the robust stationarity solution before imposing the bias fixed point. -/
noncomputable def robustRidgeCandidate (S τ a r : ℝ) : ℝ :=
  (a + r) * S ^ 2 / ((a + r) * S ^ 2 + τ ^ 2 * a)

/-- The candidate is the usual ridge filter with the corrected effective parameter. -/
theorem robustRidgeCandidate_eq (S τ a r : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hS : S ≠ 0) :
    robustRidgeCandidate S τ a r =
      S ^ 2 / (S ^ 2 + transportedRidgeParameter τ a r) := by
  have har : a + r ≠ 0 := ne_of_gt (by linarith)
  unfold robustRidgeCandidate transportedRidgeParameter
  field_simp [har, hS]

/-- The candidate satisfies the scalar first-order stationarity equation. -/
theorem robustRidgeCandidate_stationary (S τ a r : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hS : S ≠ 0) :
    (a + r) * (robustRidgeCandidate S τ a r - 1) * S ^ 2 +
      τ ^ 2 * a * robustRidgeCandidate S τ a r = 0 := by
  have hden : (a + r) * S ^ 2 + τ ^ 2 * a ≠ 0 := by
    positivity
  unfold robustRidgeCandidate
  field_simp [hden]
  ring

end Calibrator
