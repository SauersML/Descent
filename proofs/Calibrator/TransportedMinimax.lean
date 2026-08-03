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

/-! ## Long-memory geometry: the floor is real, the mechanism I gave for it was not

The estimation floor is `3/(2n)` uniformly in the memory parameter `δ`. **That survived
measurement and I could not break it.** Everything this section originally said about *why*
did not survive, and the correction is more interesting than the claim.

**Measured, on a near-unit-root AR(1) (`ρ = 1 - δ`) with an ARFIMA arm alongside, Whittle
estimation, 20000 replicates, controls passing first (iid variance `1.005`–`1.009×` theory,
AR(1) at `ρ=0.5` `0.994`–`1.022×`):**

* **The parameter variance scales as `δ^{+1}`, not `δ³`.** Fitted exponent `0.686, 0.870,
  0.926` at `n = 1024, 4096, 16384`, converging to `1` as the near-unit-root finite-sample
  effect dies. Observed over claimed runs from `2.0` at `δ = 0.5` to `1639` at `δ = 0.005`,
  `ε = 2.5`.
* **There is no `ε` dependence at all.** Measured `Var(ε=2.5)/Var(ε=1)` is `0.963`–`1.015`
  across every cell; the claimed metric predicts `1/6.25 = 0.16`. And this needs no
  simulation: in any family `f = ε²·g(λ;δ)` the amplitude enters `log f` *additively*, so
  `∂(log f)/∂δ` is `ε`-free and the information for `δ` cannot depend on `ε`.

So `ε²/δ³` **is not the Fisher information for a memory rate**; the true one is
`1/(δ(2-δ)) ≈ 1/(2δ)`. With the claimed metric the transported loss is not flat at all — it
runs `3.0, 23.0, 95.1, 388, 2542, 10679, 44740` as `δ` falls from `0.5` to `0.005`, four
orders of magnitude, and scales with `ε²`.

**With the true information it is flat, and the constant is the parameter count.** One
parameter: `n·(1/2)·I·V = 0.5103, 0.4985, 0.5003, 0.4970, 0.5136, 0.5367, 0.5607` across the
same `δ` range — flat at `0.500`. Three parameters (`ρ`, innovation variance, mean):
`1.4969, 1.5151, 1.5002, 1.5083, 1.5100, 1.6046` — flat at `1.500 = 3/2`.

**The mechanism is reparameterisation invariance, and it is trivial.** When loss *is* the
Fisher metric, an efficient estimator has expected transported loss exactly `p/(2n)` for `p`
parameters, because the metric and the variance are reciprocal *by construction* — `δ` and
`ε` cancel because the factors of **any** parameterisation cancel. `efficientFloor_eq` below
is that statement, and it is one line. The original `transportedFloor_eq` is the same algebra
with two inputs that are **each wrong, reciprocally**, which is exactly why their product
survived. It is kept because the identity is true and is the shape a reader will look for,
but it should not be read as evidence for either factor.

The honest residue: long memory has zero marginal sample cost *because loss is measured in
the information metric*, and that is a statement about the choice of loss, not about memory.

**The gloss discrepancy is resolved: absolute versus relative.** This section previously
recorded that the upstream text calls the variance one that "blows up" while giving a formula
that shrinks, and declined to adjudicate. Both are right about different quantities.
Absolute `Var(δ̂)` at `n = 1024` is `7.45e-4, 2.04e-4, 5.69e-5, 3.51e-5` as `δ` goes
`0.5 → 0.005` — it *shrinks*, as `longMemoryVariance_strictMono` says. Relative precision
*blows up*: `Var(log δ̂)` is `2.96e-3, 1.92e-2, 1.09e-1, 9.01e-1` over the same range, a
factor of 300, and `sd(δ̂)/δ` reaches `1.185` — at `δ = 0.005, n = 1024` **the memory
parameter is not identified at all**, even though its absolute variance is the smallest in
the table. The prose describes relative precision and is correct; the formula is an absolute
variance and is correct.

Empirical status: **the `p/(2n)` floor is VALIDATED and its stated mechanism is FALSIFIED**;
the metric and the variance are each refuted individually. See `proofs/validation/longmemory/`.
The measurement bounds the Whittle estimator's risk, so the floor is an efficiency statement,
not a minimax lower bound. -/

section LongMemoryGeometry

/-- The conformal metric coefficient as originally posited: `ε²/δ³`.

    **Retained as a named object, not endorsed.** Measurement shows this is not the Fisher
    information for a memory rate — the information is `ε`-free for structural reasons and
    scales as `1/δ`, not `1/δ³`. See the section header. -/
noncomputable def longMemoryMetric (ε δ : ℝ) : ℝ := ε ^ 2 / δ ^ 3

/-- The parameter variance as originally posited: `3δ³/(nε²)`.

    **Retained as a named object, not endorsed.** The measured scaling is `δ^{+1}` with no
    `ε` dependence. -/
noncomputable def longMemoryVariance (ε δ n : ℝ) : ℝ := 3 * δ ^ 3 / (n * ε ^ 2)

/-- **The actual mechanism: an efficient estimator's transported loss is `p/(2n)`.**

    If loss is the information metric `g` and the estimator attains the Cramér–Rao variance
    `1/(n·g)`, the transported loss is `1/(2n)` — **whatever `g` is**. The metric cancels
    identically, so no property of the family, and in particular no property of long memory,
    is doing any work. For `p` parameters the same computation gives `p/(2n)`.

    This is the honest form of "long memory is free": it is free because loss is being
    measured in the information metric, which is a choice about the loss and not a fact
    about memory. -/
theorem efficientFloor_eq (g n : ℝ) (hg : g ≠ 0) (hn : n ≠ 0) :
    (1 / 2) * g * (1 / (n * g)) = 1 / (2 * n) := by
  field_simp

/-- The `p`-parameter form: `p` independent coordinates each contribute `1/(2n)`. -/
theorem efficientFloor_dim (p g n : ℝ) (hg : g ≠ 0) (hn : n ≠ 0) :
    p * ((1 / 2) * g * (1 / (n * g))) = p / (2 * n) := by
  rw [efficientFloor_eq g n hg hn]
  ring

/-- **The originally posited pair reproduces `3/(2n)`** — because its two factors are wrong
    reciprocally, not because either is right. Kept for continuity with the upstream
    statement; see `efficientFloor_eq` for the mechanism that actually holds. -/
theorem transportedFloor_eq (ε δ n : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (hn : n ≠ 0) :
    (1 / 2) * longMemoryMetric ε δ * longMemoryVariance ε δ n = 3 / (2 * n) := by
  unfold longMemoryMetric longMemoryVariance
  field_simp

/-- The floor does not depend on the memory parameter. True, and true for every `δ`-dependent
    pair whose product is constant — which is the point of `efficientFloor_eq`. -/
theorem transportedFloor_indep_of_memory (ε δ₁ δ₂ n : ℝ)
    (hε : ε ≠ 0) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (hn : n ≠ 0) :
    (1 / 2) * longMemoryMetric ε δ₁ * longMemoryVariance ε δ₁ n =
      (1 / 2) * longMemoryMetric ε δ₂ * longMemoryVariance ε δ₂ n := by
  rw [transportedFloor_eq ε δ₁ n hε hδ₁ hn, transportedFloor_eq ε δ₂ n hε hδ₂ hn]

/-- **The stated formula is increasing in `δ`**, so the absolute variance shrinks as memory
    lengthens. Confirmed by measurement (`7.45e-4 → 3.51e-5` as `δ` falls `0.5 → 0.005`);
    what blows up over the same range is *relative* precision, by a factor of 300. -/
theorem longMemoryVariance_strictMono (ε n : ℝ) (hε : ε ≠ 0) (hn : 0 < n)
    (δ₁ δ₂ : ℝ) (h₁ : 0 < δ₁) (h₁₂ : δ₁ < δ₂) :
    longMemoryVariance ε δ₁ n < longMemoryVariance ε δ₂ n := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hden : 0 < n * ε ^ 2 := mul_pos hn hε2
  unfold longMemoryVariance
  have hδ₂ : 0 < δ₂ := lt_trans h₁ h₁₂
  have hquad : (0 : ℝ) < δ₂ ^ 2 + δ₂ * δ₁ + δ₁ ^ 2 := by
    nlinarith [mul_pos hδ₂ h₁, sq_nonneg δ₁, sq_nonneg δ₂]
  have hfac : (0 : ℝ) < (δ₂ - δ₁) * (δ₂ ^ 2 + δ₂ * δ₁ + δ₁ ^ 2) :=
    mul_pos (by linarith) hquad
  apply div_lt_div_of_pos_right _ hden
  nlinarith [hfac]

/-! ### The width law: the exponents are shape-free, the constant is not

For a spectral band of width `w`, `‖B‖² ~ 1/w` and `‖dB‖² ~ 1/w³`. **Measured across seven
shapes, the exponents hold to fifteen digits** — fitted slopes `-1.0000000000000002` and
`-3.0000000000000013`, ratio `-2.0000000000000004`, with a planted-exponent control on the
fitter passing exactly.

**But the ratio constant is not shape-free, and a first version of this section asserted that
it was.** That version gave `WidthLaw` a *single* shape constant appearing in both norms,
which made `widthLaw_ratio_shape_free` true by construction — a tautology resting on a false
premise. The two constants are independent and their ratio `C₂/C₁` measures:

| shape | `C₁` | `C₂` | `C₂/C₁` |
|---|---|---|---|
| Gaussian | 0.2821 | 0.1410 | **0.500** |
| Lorentzian | 0.1592 | 0.0796 | **0.500** |
| gamma-3 (asymmetric) | 0.1875 | 0.0625 | **0.333** |
| triangular | 0.6667 | 2.0 | **3.00** |
| skew-normal (asymmetric) | 0.4946 | 1.0952 | **2.21** |
| Hann | 1.5 | 19.739 | **13.16** |
| rectangular | 1.0 | **∞** | **∞** |

A factor of forty across the smooth shapes, and the rectangular band has no finite `‖dB‖²`
at all — its derivative is a pair of Dirac deltas, so the theorem simply does not apply to a
discontinuous band. That is a scope restriction, not a rounding error.

**What survives is the scale invariance.** `w²·(‖dB‖²/‖B‖²)` is independent of `w` for every
shape — that is the shape-free content and it is what `widthLaw_scaleInvariant` states. The
*value* of that constant is a property of the band's profile.

**The identification with the estimation metric is withdrawn.** A previous theorem here,
`widthLaw_gives_longMemoryMetric`, identified the conformal coefficient `ε²/δ³` with the band
derivative norm at shape `ε²`, in order to make the exponent `3` "derived rather than
assumed". That was a **category error**, and it is wrong twice over: measurement shows
`ε²/δ³` is not the Fisher information for a memory rate (see the section above — the
information is `ε`-free and scales as `1/δ`), and the width-law constant is not universal, so
there is no canonical `ε²` to identify it with. The `w^{-3}` of a band norm and the `δ^{-3}`
that was posited in the metric are different objects that happened to share an exponent. The
theorem is deleted rather than weakened, because its only purpose was the identification.

Empirical status: **exponents VALIDATED to 15 digits across seven shapes; shape-freedom of
the constant FALSIFIED (spread 0.333–13.16, infinite for rectangular); the metric
identification WITHDRAWN.** See `proofs/validation/width_law/`. -/

/-- **A band obeying the width law.**

    The two constants are **independent**. An earlier version used one constant for both,
    which silently forced the ratio to `1/w²` and made shape-freedom a tautology. -/
structure WidthLaw where
  /-- The constant in `‖B‖² = C₁/w`. -/
  normConst : ℝ
  /-- The constant in `‖dB‖² = C₂/w³`. Independent of `normConst`; measured ratios
      `C₂/C₁` range from `0.333` to `13.16` across shapes. -/
  gradConst : ℝ
  /-- Norm constants are positive. -/
  normConst_pos : 0 < normConst
  /-- Derivative-norm constants are positive on the shapes where they are finite at all;
      a rectangular band has none. -/
  gradConst_pos : 0 < gradConst
  /-- Squared norm of the band at width `w`. -/
  normSq : ℝ → ℝ
  /-- Squared norm of the band's derivative at width `w`. -/
  gradNormSq : ℝ → ℝ
  /-- The width law for the band. -/
  normSq_eq : ∀ w, 0 < w → normSq w = normConst / w
  /-- The width law for its derivative. -/
  gradNormSq_eq : ∀ w, 0 < w → gradNormSq w = gradConst / w ^ 3

/-- **The width-law ratio is `(C₂/C₁)/w²`.** The `w`-dependence is universal; the constant
    is not. -/
theorem widthLaw_ratio (W : WidthLaw) (w : ℝ) (hw : 0 < w) :
    W.gradNormSq w / W.normSq w = (W.gradConst / W.normConst) / w ^ 2 := by
  have hn : W.normConst ≠ 0 := ne_of_gt W.normConst_pos
  have hwne : w ≠ 0 := ne_of_gt hw
  rw [W.gradNormSq_eq w hw, W.normSq_eq w hw]
  field_simp

/-- **The shape-free content, stated correctly: scale invariance.**

    `w²` times the ratio is independent of `w`, for every shape. This is what makes the
    exponent a property of the width variable alone — and it is all that does. -/
theorem widthLaw_scaleInvariant (W : WidthLaw) (w : ℝ) (hw : 0 < w) :
    w ^ 2 * (W.gradNormSq w / W.normSq w) = W.gradConst / W.normConst := by
  have hwne : w ≠ 0 := ne_of_gt hw
  rw [widthLaw_ratio W w hw]
  field_simp

/-- **Two bands agree in the exponent at every width**, which is the honest form of the
    shape-freedom claim: their scale-invariant constants may differ, but neither depends on
    `w`. -/
theorem widthLaw_exponent_shape_free (W W' : WidthLaw) (w w' : ℝ)
    (hw : 0 < w) (hw' : 0 < w') :
    w ^ 2 * (W.gradNormSq w / W.normSq w) = w' ^ 2 * (W.gradNormSq w' / W.normSq w') ∧
      w ^ 2 * (W'.gradNormSq w / W'.normSq w) =
        w' ^ 2 * (W'.gradNormSq w' / W'.normSq w') := by
  refine ⟨?_, ?_⟩
  · rw [widthLaw_scaleInvariant W w hw, widthLaw_scaleInvariant W w' hw']
  · rw [widthLaw_scaleInvariant W' w hw, widthLaw_scaleInvariant W' w' hw']

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
