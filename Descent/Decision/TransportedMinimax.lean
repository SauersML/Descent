/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Descent.Layer

assert_below Descent.Program

namespace Descent.Decision

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

/-- **transportedRidgeParameter where its denominator vanishes, named.** The guard `a + r` is zero
at `a = 0`, `r = 0`. Lean returns `0` there rather than the value the modelled quantity takes,
and no type error marks the point. Consumers must require `a + r ≠ 0`. -/
theorem transportedRidgeParameter_at_a0r0_is_junk (τ : ℝ) :
    transportedRidgeParameter τ 0 0 = 0 := by
  unfold transportedRidgeParameter
  norm_num

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

/-- **robustRidgeCandidate where its denominator vanishes, named.** The guard `(a + r) * S ^ 2 + τ ^
2 * a` is zero at `S = 0`, `τ = 0`, `a = 0`, `r = 0`. Lean returns `0` there rather than the
value the modelled quantity takes, and no type error marks the point. Consumers must require `(a
+ r) * S ^ 2 + τ ^ 2 * a ≠ 0`. -/
theorem robustRidgeCandidate_at_s00a0r0_is_junk :
    robustRidgeCandidate 0 0 0 0 = 0 := by
  unfold robustRidgeCandidate
  norm_num

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

/-- **inflatedRidgeParameter at its junk point, named.** The inflation factor `1 + r / a` diverges
as the scale vanishes. The divisor is zero, the ratio is junk-zero, and the ridge parameter is
returned UNINFLATED -- exactly the regularisation the inflation exists to prevent. Consumers
must exclude the argument that makes the guard vanish. -/
theorem inflatedRidgeParameter_zero_scale_is_junk (τ r : ℝ) :
    inflatedRidgeParameter τ 0 r = τ ^ 2 := by
  unfold inflatedRidgeParameter
  simp

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
is that statement, and it is one line.

**The two factors are now REPAIRED rather than retained.** `longMemoryMetric` is the measured
information `1/(δ(2-δ))` and `longMemoryVariance` is its Cramér-Rao reciprocal `δ(2-δ)/n`, so
`transportedFloor_eq` reads `1/(2n)` — the one-parameter floor measured at `0.500` — and it is
now an instance of `efficientFloor_eq` rather than a coincidence. The superseded pair produced
`3/(2n)` by the same algebra for the OPPOSITE reason, its two inputs being **each wrong,
reciprocally**, which is precisely why a check on their product could not catch either. That
`3` was a parameter count folded into a one-parameter variance; it now lives in
`efficientFloor_dim`'s `p`, where the three-parameter measurement reads `1.500`.

The honest residue: long memory has zero marginal sample cost *because loss is measured in
the information metric*, and that is a statement about the choice of loss, not about memory.

**Absolute versus relative variance.** The upstream text calls the variance one that
"blows up" while giving a formula that shrinks. Both are right, about different quantities.
Absolute `Var(δ̂)` at `n = 1024` is `7.45e-4, 2.04e-4, 5.69e-5, 3.51e-5` as `δ` goes
`0.5 → 0.005` — it *shrinks*, as `longMemoryVariance_strictMono` says. Relative precision
*blows up*: `Var(log δ̂)` is `2.96e-3, 1.92e-2, 1.09e-1, 9.01e-1` over the same range, a
factor of 300, and `sd(δ̂)/δ` reaches `1.185` — at `δ = 0.005, n = 1024` **the memory
parameter is not identified at all**, even though its absolute variance is the smallest in
the table. The prose describes relative precision and is correct; the formula is an absolute
variance and is correct.

Empirical status: **MIXED** -- the `p/(2n)` floor is VALIDATED and the mechanism originally
stated for it is FALSIFIED. The metric and the variance were each refuted individually and
have each been REPLACED by the form the same runs measured: the information is `ε`-free and
scales as `1/δ`, the variance is its reciprocal. See `validation/empirical/longmemory/`.
The measurement bounds the Whittle estimator's risk, so the floor is an efficiency statement,
not a minimax lower bound. -/

section LongMemoryGeometry

/-- **The Fisher information for a memory rate**, `1/(δ·(2-δ))`, which is `≈ 1/(2δ)` at small
    `δ`.

    THE AMPLITUDE IS ABSENT FOR A STRUCTURAL REASON, not because it was measured small. In any
    family `f = ε²·g(λ; δ)` the amplitude enters `log f` ADDITIVELY, so `∂(log f)/∂δ` is
    `ε`-free and the information for `δ` cannot depend on `ε` at all. The measurement agrees
    and could have disagreed: `Var(ε=2.5)/Var(ε=1)` is `0.963`–`1.015` across every cell where
    the superseded `ε²/δ³` predicted `1/6.25 = 0.16`.

    THE SUPERSEDED FORM WAS WRONG IN BOTH FEATURES and the module docstring above carries the
    run: it scaled as `δ^{-3}` where the observed exponent converges to `1`, and it carried an
    `ε` that cannot be there. The `3` came from a width law that was withdrawn as a category
    error — see the note at the end of this section. -/
noncomputable def longMemoryMetric (δ : ℝ) : ℝ := 1 / (δ * (2 - δ))

/-- **longMemoryMetric where its denominator vanishes, named.** The guard `δ ^ 3` is zero at `δ =
0`. Lean returns `0` there rather than the value the modelled quantity takes, and no type error
marks the point. A zero bandwidth gives an infinite metric, and what is reported instead is `0`,
the finest possible resolution, for a bandwidth that resolves nothing. Consumers must require
`δ ≠ 0`. -/
theorem longMemoryMetric_at_0_is_junk :
    longMemoryMetric 0 = 0 := by
  unfold longMemoryMetric
  norm_num

/-- **The Cramér-Rao variance of the memory rate at that information**, `δ·(2-δ)/n` — the
    reciprocal of `n · longMemoryMetric δ`, which is what an efficient estimator attains.

    The measured scaling is `δ^{+1}` with no `ε` dependence, which is this form at small `δ`.
    The superseded `3δ³/(nε²)` was wrong in the exponent, wrong in carrying `ε`, and wrong in
    its numerator: that `3` was a PARAMETER COUNT — `ρ`, the innovation variance and the mean —
    that had been folded into a one-parameter variance, which is why the floor it produced read
    `3/(2n)` where the one-parameter measurement reads `0.500 = 1/2` for `n·(1/2)·I·V`. The
    count belongs in `efficientFloor_dim`'s `p` and nowhere else. -/
noncomputable def longMemoryVariance (δ n : ℝ) : ℝ := δ * (2 - δ) / n

/-- **longMemoryVariance where its denominator vanishes, named.** The guard `n` is zero at no
sample. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point: no data is reported as a perfectly estimated parameter. Consumers must
require `n ≠ 0`.

The companion junk point at `ε = 0` is gone with the amplitude itself — the information for a
memory rate does not depend on the signal scale, so there is no zero-amplitude case to guard. -/
theorem longMemoryVariance_at_n0_is_junk (δ : ℝ) :
    longMemoryVariance δ 0 = 0 := by
  unfold longMemoryVariance
  norm_num

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

/-- **The repaired pair gives the ONE-parameter floor `1/(2n)`**, which is the measurement:
    `n·(1/2)·I·V` is flat at `0.500` across `δ` from `0.5` to `0.005`. The superseded pair
    reproduced `3/(2n)` instead, and the `3` was not a property of memory but a parameter count
    folded into the variance — with three parameters the same measurement reads `1.500`, which
    is `efficientFloor_dim` at `p = 3` and not a different floor.

    This is now an instance of `efficientFloor_eq` rather than a coincidence: the factors
    cancel because the variance IS the reciprocal of `n` times the information, which is what
    an efficient estimator attains. Under the superseded pair the same algebra went through for
    the opposite reason — two factors each wrong, reciprocally — which is exactly why their
    product survived a check that should have caught them. -/
theorem transportedFloor_eq (δ n : ℝ) (hδ : δ ≠ 0) (hδ' : δ ≠ 2) (hn : n ≠ 0) :
    (1 / 2) * longMemoryMetric δ * longMemoryVariance δ n = 1 / (2 * n) := by
  unfold longMemoryMetric longMemoryVariance
  have h2 : (2 : ℝ) - δ ≠ 0 := by intro h; apply hδ'; linarith
  field_simp

/-- The floor does not depend on the memory parameter. True, and true for every `δ`-dependent
    pair whose product is constant — which is the point of `efficientFloor_eq`. -/
theorem transportedFloor_indep_of_memory (δ₁ δ₂ n : ℝ)
    (hδ₁ : δ₁ ≠ 0) (hδ₁' : δ₁ ≠ 2) (hδ₂ : δ₂ ≠ 0) (hδ₂' : δ₂ ≠ 2) (hn : n ≠ 0) :
    (1 / 2) * longMemoryMetric δ₁ * longMemoryVariance δ₁ n =
      (1 / 2) * longMemoryMetric δ₂ * longMemoryVariance δ₂ n := by
  rw [transportedFloor_eq δ₁ n hδ₁ hδ₁' hn, transportedFloor_eq δ₂ n hδ₂ hδ₂' hn]

/-- **The variance is increasing in `δ` on the admissible range**, so the absolute variance
    shrinks as memory lengthens. Confirmed by measurement (`7.45e-4 → 3.51e-5` as `δ` falls
    `0.5 → 0.005`); what blows up over the same range is *relative* precision, by a factor of
    300.

    THE UPPER BOUND `δ₂ ≤ 1` IS NEW WITH THE REPAIRED BODY and is not a convenience. `δ(2-δ)`
    turns over at `δ = 1`, so the monotonicity is a statement about memory rates below one,
    which is where a memory rate lives; the superseded `δ³` was monotone everywhere and that
    was one of the ways it did not look like an information-metric variance. -/
theorem longMemoryVariance_strictMono (n : ℝ) (hn : 0 < n)
    (δ₁ δ₂ : ℝ) (h₁₂ : δ₁ < δ₂) (h₂ : δ₂ ≤ 1) :
    longMemoryVariance δ₁ n < longMemoryVariance δ₂ n := by
  unfold longMemoryVariance
  apply div_lt_div_of_pos_right _ hn
  nlinarith [mul_pos (sub_pos.mpr h₁₂) (show (0 : ℝ) < 2 - (δ₁ + δ₂) by linarith)]

/-! ### The width law, removed

A `WidthLaw` structure used to sit here, carrying `‖B‖² = C₁/w` and `‖dB‖² = C₂/w³` as
**structure fields** — results this module does not prove — together with three theorems that
consumed them. Measurement had confirmed the exponents (`-1` and `-3` to fifteen digits across
five shapes, `L¹`-normalised bands, finite Sobolev seminorm required) and refuted the
shape-freedom of the constant (`C₂/C₁` spanning `0.333` to `13.16`, infinite for a rectangular
band).

None of that is a reason to carry it as an assumption. The structure and its theorems are
**deleted**: an exponent verified by simulation elsewhere is not a theorem of this corpus, and
writing it as a field made it look like one.

This is where the superseded `δ^{-3}` came from: the width law's `w^{-3}` was carried across
to the memory rate, which was a category error twice over — the identification was never
proved here, and the Whittle measurement recorded above contradicts the exponent directly.
`longMemoryMetric` now carries `1/(δ(2-δ))`, which owes nothing to a width law. -/

/-! ### Positivity buys an exponent

The metric-entropy side of the same arc. A moment body — the set of moment sequences of
positive measures — has entropy exponent `1/α`, strictly below the `2/(2α-1)` of the
hyperrectangle that contains it. The two exponents are named inputs; the comparison is the
theorem, and it holds at every admissible `α` with no exceptional range. -/

/-- Entropy exponent of the moment body: `log N(ε) = Θ((M/ε)^(1/α))`. -/
noncomputable def momentBodyEntropyExponent (α : ℝ) : ℝ := 1 / α

/-- **The entropy exponent's junk branch, named.** At `α = 0` the exponent diverges and Lean
returns `0`. Consumers must require `α ≠ 0`. -/
theorem momentBodyEntropyExponent_zero_is_junk : momentBodyEntropyExponent 0 = 0 := by
  unfold momentBodyEntropyExponent; simp

/-- Entropy exponent of the enclosing hyperrectangle: `ε^(-2/(2α-1))`. -/
noncomputable def hyperrectangleEntropyExponent (α : ℝ) : ℝ := 2 / (2 * α - 1)

/-- **hyperrectangleEntropyExponent at its junk point, named.** At `α = 1 / 2` the hyperrectangle
entropy exponent diverges: this is the critical smoothness where the minimax rate changes
character. The divisor `2 * α - 1` is zero and the exponent is `0`, reporting no entropy growth
at the one value where it is unbounded. Consumers must exclude the argument that makes the guard
vanish. -/
theorem hyperrectangleEntropyExponent_critical_smoothness_is_junk :
    hyperrectangleEntropyExponent (1 / 2) = 0 := by
  unfold hyperrectangleEntropyExponent
  norm_num

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

end Descent.Decision
