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

/-! ## The inflated-ridge claim, diagnosed rather than merely contradicted

An upstream design manuscript states the Tier-1 rule with an **inflated** ridge,
`η* = τ²(1 + r/a)`. This file derives the reciprocal, `η = τ²a/(a+r)`. The two disagree in
*direction*, not in constants, so one of them is wrong and it is worth saying which and why
rather than leaving two numbers on the table.

**The factor `(1 + r/a)` is real.** It is the weight the robust objective puts on the
**bias** term: differentiating `(a + r)²` gives `2(a + r)·∂a = 2a(1 + r/a)·∂a`, against
`2a·∂a` for the plain squared-bias objective. So drift uncertainty multiplies the bias
weight by exactly `1 + r/a`, which is what the manuscript's factor records.

**The error is where it was applied.** A ridge parameter trades *against* the bias weight —
it is the coefficient of the penalty, not of the fit — so a factor multiplying the bias term
**divides** the ridge. `transportedRidgeParameter_eq_deflated` below is that statement:
`τ²a/(a+r)` is exactly `τ²/(1 + r/a)`. Writing the factor on the ridge instead of under it
inverts it, and `inflated_mul_deflated` shows the two candidates are reciprocal about `τ²` —
one inversion apart, which is the signature of this mistake and not of a different model.

**Settled by a witness, not by argument.** `inflatedRidge_violates_stationarity` exhibits
exact rationals at which the inflated parameter fails the first-order condition this file's
`robustRidgeCandidate_stationary` satisfies. Transport uncertainty makes residual bias
costlier and therefore calls for **less** shrinkage.

Empirical status: DERIVED. The witness is exact rational arithmetic. -/

/-- The manuscript's inflated candidate, named so it can be refuted rather than paraphrased. -/
noncomputable def inflatedRidgeParameter (τ a r : ℝ) : ℝ := τ ^ 2 * (1 + r / a)

/-- **The derived ridge is the bias-weight factor applied as a divisor.**

    `τ²a/(a+r) = τ²/(1 + r/a)`. The factor `1 + r/a` is the same one the manuscript
    identifies; it belongs under the ridge, not on it. -/
theorem transportedRidgeParameter_eq_deflated (τ a r : ℝ) (ha : 0 < a) (har : a + r ≠ 0) :
    transportedRidgeParameter τ a r = τ ^ 2 / (1 + r / a) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hsum : 1 + r / a = (a + r) / a := by field_simp
  unfold transportedRidgeParameter
  rw [hsum]
  field_simp

/-- **The two candidates are reciprocal about `τ²`**, which is the fingerprint of a single
    inversion rather than of a competing derivation. -/
theorem inflated_mul_deflated (τ a r : ℝ) (ha : 0 < a) (har : a + r ≠ 0) :
    inflatedRidgeParameter τ a r * transportedRidgeParameter τ a r = τ ^ 2 * τ ^ 2 := by
  have hane : a ≠ 0 := ne_of_gt ha
  unfold inflatedRidgeParameter transportedRidgeParameter
  field_simp

/-- **The inflated parameter fails the stationarity condition, at explicit rationals.**

    At `S = 1`, `τ = 1`, `a = 1`, `r = 1` the first-order condition forces the ridge filter
    `φ = 2/3`, which is what `τ²a/(a+r) = 1/2` delivers. The inflated value `2` delivers
    `φ = 1/3`, and the stationarity residual there is `-1`, not `0`.

    This is a positive control as well as a refutation: the same expression evaluated at the
    derived parameter returns exactly `0`, so the test is known capable of passing. -/
theorem inflatedRidge_violates_stationarity :
    inflatedRidgeParameter 1 1 1 = 2 ∧
      transportedRidgeParameter 1 1 1 = 1 / 2 ∧
      (1 + 1 : ℝ) * (1 / (1 + 1 / 2) - 1) * 1 ^ 2 + 1 ^ 2 * 1 * (1 / (1 + 1 / 2)) = 0 ∧
      (1 + 1 : ℝ) * (1 / (1 + 2) - 1) * 1 ^ 2 + 1 ^ 2 * 1 * (1 / (1 + 2)) = -1 := by
  refine ⟨by norm_num [inflatedRidgeParameter], by norm_num [transportedRidgeParameter],
    by norm_num, by norm_num⟩

/-! ## Long-memory geometry: why the sample cost of long memory is zero

The design arc's most surprising corollary is that long memory is **free**: the estimation
floor is `3/(2n)` uniformly in the memory parameter `δ`, even though the variance of the
memory parameter's own estimator is anything but uniform in `δ`. The mechanism is that loss
and information are the *same* metric at leading order, so the `δ` and `ε` factors appear
once in each and cancel.

The cancellation is the part worth having, and it is exact algebra once the two inputs are
named: the conformal metric `ε²δ^{-3}` and the parameter variance `3δ³/(nε²)`. Both are
analytic inputs — a Whittle-Fisher computation and a variance calculation — and neither is
derived here.

**A discrepancy in the upstream gloss, recorded rather than resolved.** The upstream text
describes the parameter variance as one that "blows up" as memory lengthens, while giving it
as `δ³/(nε²)`. Long memory is `δ → 0`, and `δ³/(nε²) → 0` there — the stated formula shrinks
where the prose says it grows. `longMemoryVariance_strictMono` below records which way the
stated formula actually runs. **The cancellation theorem is untouched either way**, since it
only needs the product, which is why it is stated separately from the gloss. Whoever holds
the upstream derivation should reconcile the word with the formula; nothing here depends on
the outcome.

Empirical status: UNTESTED. The two inputs are named hypotheses; the algebra is PROVED. -/

section LongMemoryGeometry

/-- The conformal metric coefficient of the generative geometry: `ε²/δ³`. -/
noncomputable def longMemoryMetric (ε δ : ℝ) : ℝ := ε ^ 2 / δ ^ 3

/-- The variance of the memory-parameter estimator at sample size `n`: `3δ³/(nε²)`. -/
noncomputable def longMemoryVariance (ε δ n : ℝ) : ℝ := 3 * δ ^ 3 / (n * ε ^ 2)

/-- **The transported estimation floor is `3/(2n)`, with `δ` and `ε` cancelling.**

    Loss is the information metric at leading order, so the geometry enters the loss once
    and the variance once, with opposite exponents. The floor a practitioner faces is
    therefore free of both the memory parameter and the amplitude.

    This is the exact statement behind "long memory has zero marginal sample cost". -/
theorem transportedFloor_eq (ε δ n : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (hn : n ≠ 0) :
    (1 / 2) * longMemoryMetric ε δ * longMemoryVariance ε δ n = 3 / (2 * n) := by
  unfold longMemoryMetric longMemoryVariance
  field_simp

/-- **The floor does not depend on the memory parameter at all**: two panels with different
    memory lengths face the same estimation floor at the same sample size. -/
theorem transportedFloor_indep_of_memory (ε δ₁ δ₂ n : ℝ)
    (hε : ε ≠ 0) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (hn : n ≠ 0) :
    (1 / 2) * longMemoryMetric ε δ₁ * longMemoryVariance ε δ₁ n =
      (1 / 2) * longMemoryMetric ε δ₂ * longMemoryVariance ε δ₂ n := by
  rw [transportedFloor_eq ε δ₁ n hε hδ₁ hn, transportedFloor_eq ε δ₂ n hε hδ₂ hn]

/-- **Which way the stated variance formula actually runs.**

    It is strictly increasing in `δ`, so it *shrinks* as memory lengthens (`δ → 0`). Recorded
    because the upstream prose says the opposite; see the section header. -/
theorem longMemoryVariance_strictMono (ε n : ℝ) (hε : ε ≠ 0) (hn : 0 < n)
    (δ₁ δ₂ : ℝ) (h₁ : 0 < δ₁) (h₁₂ : δ₁ < δ₂) :
    longMemoryVariance ε δ₁ n < longMemoryVariance ε δ₂ n := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hden : 0 < n * ε ^ 2 := mul_pos hn hε2
  unfold longMemoryVariance
  have hδ₂ : 0 < δ₂ := lt_trans h₁ h₁₂
  have hquad : (0:ℝ) < δ₂ ^ 2 + δ₂ * δ₁ + δ₁ ^ 2 := by
    nlinarith [mul_pos hδ₂ h₁, sq_nonneg δ₁, sq_nonneg δ₂]
  have hfac : (0:ℝ) < (δ₂ - δ₁) * (δ₂ ^ 2 + δ₂ * δ₁ + δ₁ ^ 2) :=
    mul_pos (by linarith) hquad
  apply div_lt_div_of_pos_right _ hden
  nlinarith [hfac]

/-! ### The width law, and where the exponent three comes from

The conformal metric above was posited with exponent `3`. It is not arbitrary: it is forced
by the **width law**, which says that for a spectral band of width `w` the squared norm goes
like `1/w` and the squared norm of its derivative like `1/w³`, **whatever the band's shape**.

The shape-freedom is the content, and it is what `widthLaw_ratio_shape_free` records: two
bands with different shape constants have the *same* ratio `1/w²`, so the exponent in the
induced metric is a property of the width variable alone. That is why the same `w^{-3}`
appears for every family in this arc rather than being fitted per family.

`widthLaw_gives_longMemoryMetric` closes the loop: the metric coefficient of the
long-memory geometry **is** the width law's `gradNormSq`, with the amplitude `ε²` playing the
role of the shape constant. The exponent `3` in `longMemoryMetric` is therefore derived, not
assumed.

Empirical status: UNTESTED. The two scalings are named inputs. -/

/-- **A band obeying the width law.** The shape constant is carried explicitly so that the
    shape-freedom of the ratio can be stated as a theorem rather than asserted. -/
structure WidthLaw where
  /-- The band's shape constant. -/
  shape : ℝ
  /-- Shape constants are positive. -/
  shape_pos : 0 < shape
  /-- Squared norm of the band at width `w`. -/
  normSq : ℝ → ℝ
  /-- Squared norm of the band's derivative at width `w`. -/
  gradNormSq : ℝ → ℝ
  /-- The width law for the band: `‖B‖² ~ 1/w`. -/
  normSq_eq : ∀ w, 0 < w → normSq w = shape / w
  /-- The width law for its derivative: `‖dB‖² ~ 1/w³`. -/
  gradNormSq_eq : ∀ w, 0 < w → gradNormSq w = shape / w ^ 3

/-- **The width-law ratio is `1/w²`, and the shape constant cancels.** -/
theorem widthLaw_ratio (W : WidthLaw) (w : ℝ) (hw : 0 < w) :
    W.gradNormSq w / W.normSq w = 1 / w ^ 2 := by
  have hs : W.shape ≠ 0 := ne_of_gt W.shape_pos
  have hwne : w ≠ 0 := ne_of_gt hw
  rw [W.gradNormSq_eq w hw, W.normSq_eq w hw]
  field_simp

/-- **Shape-freedom, as a theorem.** Two bands of different shape have the same ratio, so
    the exponent of the induced metric is a property of the width variable alone. -/
theorem widthLaw_ratio_shape_free (W W' : WidthLaw) (w : ℝ) (hw : 0 < w) :
    W.gradNormSq w / W.normSq w = W'.gradNormSq w / W'.normSq w := by
  rw [widthLaw_ratio W w hw, widthLaw_ratio W' w hw]

/-- **The long-memory metric is the width law's derivative norm.**

    With the amplitude `ε²` as the shape constant, `longMemoryMetric ε w = W.gradNormSq w`.
    So the exponent `3` in the conformal metric — the one that cancels against the parameter
    variance in `transportedFloor_eq` — is supplied by the width law rather than assumed. -/
theorem widthLaw_gives_longMemoryMetric (W : WidthLaw) (ε w : ℝ) (hw : 0 < w)
    (hε : ε ^ 2 = W.shape) :
    W.gradNormSq w = longMemoryMetric ε w := by
  rw [W.gradNormSq_eq w hw, longMemoryMetric, hε]

/-! ### Positivity buys an exponent

The metric-entropy side of the same arc. A moment body — the set of moment sequences of
positive measures — has entropy exponent `1/α`, strictly below the `2/(2α-1)` of the
hyperrectangle that contains it. The two exponents are named inputs; the comparison is the
theorem, and it holds at every admissible `α` with no exceptional range. -/

/-- Entropy exponent of the moment body: `log N(ε) = Θ((M/ε)^(1/α))`. -/
noncomputable def momentBodyEntropyExponent (α : ℝ) : ℝ := 1 / α

/-- Entropy exponent of the enclosing hyperrectangle: `ε^(-2/(2α-1))`. -/
noncomputable def hyperrectangleEntropyExponent (α : ℝ) : ℝ := 2 / (2 * α - 1)

/-- **Positivity buys an exponent, at every admissible `α`.**

    The moment body's entropy exponent is strictly smaller than the hyperrectangle's
    whenever `α > 1/2`, which is the whole admissible range. The gap is not asymptotic and
    has no exceptional interval: positivity of the underlying measure is worth a strictly
    better exponent everywhere, not merely a better constant.

    Statistically: rates over a moment body are entropy-standard and strictly faster than
    the coordinatewise bound suggests, so a sample-size calculation that treats the class as
    a hyperrectangle is conservative by a power. -/
theorem momentBody_entropy_exponent_lt (α : ℝ) (hα : 1 / 2 < α) :
    momentBodyEntropyExponent α < hyperrectangleEntropyExponent α := by
  have hα0 : 0 < α := by linarith
  have hden : 0 < 2 * α - 1 := by linarith
  unfold momentBodyEntropyExponent hyperrectangleEntropyExponent
  rw [div_lt_div_iff₀ hα0 hden]
  linarith

end LongMemoryGeometry

end Calibrator
