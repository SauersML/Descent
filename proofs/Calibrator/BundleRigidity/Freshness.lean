import Mathlib

/-!
# Effective independence dimension and the master decay bound

This module is **self-contained: it imports only Mathlib**.

## What this replaces

Everywhere else in this development, oscillatory decay was bought by factoring a
characteristic function as a **product over coordinates**. That step needs independence,
and under linkage disequilibrium it is false. The master bound below replaces it with one
inequality that holds for **any coupling whatsoever**.

## The objects

Fix an ordering of the coordinates. The **sequential freshness** `ε i` of coordinate `i`
is the largest `ε` with

```
Law(X i | earlier coordinates)  ≥  ε · (fiber reference measure)     a.s.
```

— how much genuinely new randomness coordinate `i` still carries once everything before it
is known. The **effective independence dimension** `D` is the maximum over orderings of
`∑ i, ε i`. For independent coordinates every `ε i = 1` and `D` is the number of
coordinates; under strong dependence `D` collapses.

## The master theorem

```
| E ∏ᵢ χ_s(t i, X i) |  ≤  exp( - θ · γ(s) · D )
```

with `θ = 1/2` in the current proof.

## The proof is a telescope, and that is why it formalizes cleanly

Condition on the past. The freshness bound splits the conditional law into an `ε` piece
that sees the reference measure and a `1 - ε` piece about which nothing is known, giving

```
|E(χ_s(X n) | past)|  ≤  (1 - ε n) + ε n · |∫ χ_s|  ≤  1 - ε n · γ n(s).
```

Iterating multiplies these, and `1 - x ≤ e^{-x}` converts the product into the
exponential. Both halves are proved here without hypotheses:

* `abs_le_prod_of_step` — the telescope itself, by induction;
* `prod_one_sub_le_exp_neg_sum` — the product-to-exponential conversion.

`master_decay_bound` composes them.

## The audit points, carried honestly

**(AP-α) — the constant is a parameter, not a baked-in `1/2`.** Sequential freshness is
**order-dependent**, and the factor `θ` absorbs the step where the worst half of the fibers
is discarded by Markov to obtain an average `γ`. Whether an order-free simultaneous
splitting improves `θ` beyond `1/2` is open. Because a failure there **weakens constants,
not statements**, `θ` appears as an explicit argument of `master_decay_bound`: any
improved discard constant is substituted without restating the theorem, and any collapse
of the argument shows up as a worse `θ` rather than as a false conclusion.

**(AP-β) — the band hypothesis.** The passage from a *pointwise kernel band* to an
*operator-norm bound on measures*, in the coupled slice theorem, is carried as the named
field `bandToOperatorNorm` of `CoupledSliceHypotheses`. It is not proved here.

The conditional step bound itself is likewise an input (`stepBound`): deriving it from a
genuine conditional law requires the disintegration machinery, which this module does not
carry. What the module *does* prove is that the step bound implies the master bound —
which is the whole of the telescope, and the part that was worth checking.

## A principle worth recording: continuation kills identities, not inequalities

An earlier obstruction ruled out exact operator identities across sheets of a single
analytic curve — equal constant weights, equal maps. Those are **closed** conditions, and
analytic continuation violates them.

The M5 mechanism needs only **open** conditions: strict containment of images, a fixed
point in an open gap, a strict ratio inequality. **Open conditions coexist with
continuation.** That is why M5 is realizable despite the obstruction, and it is a more
useful statement than either the obstruction or any particular construction: it says which
side of the closed/open line a proposed mechanism must land on to survive continuation.

An explicit 8-atom analytic family realizes M5: atoms `±√(1 ± v t)` at mass `P/4` and
`±√(1 ± w t)` at mass `(1-P)/4`, so the modulus law is `P·δ_{v} + (1-P)·δ_{w}` with
exactly two values and no stray branches, which is what makes the sheet-operator equations
the *complete* bundle equations.

**This does not reopen our own case.** The genotype family has more than two modulus
values, its cycle variety is empty, and M5 is unavailable for two independent reasons: the
image-free region the mechanism needs is empty, and the band has a single return generator
so the required composition cannot be formed.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators
open Finset

/-! ## The two proved halves of the telescope -/

/-- **The telescope.**

If each conditioning step contracts the partial expectation by a factor `1 - a k`, and the
initial expectation is bounded by one, then the `n`-th partial expectation is bounded by
the product of the contraction factors.

This is the entire iteration of the master theorem, proved by induction and with no
hypothesis beyond `0 ≤ a k ≤ 1`. -/
theorem abs_le_prod_of_step (E : ℕ → ℝ) (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - a k) * |E k|) (n : ℕ) :
    |E n| ≤ ∏ k ∈ range n, (1 - a k) := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hfac : (0 : ℝ) ≤ 1 - a n := by linarith [ha1 n]
    calc |E (n + 1)| ≤ (1 - a n) * |E n| := hstep n
      _ ≤ (1 - a n) * ∏ k ∈ range n, (1 - a k) := by
          exact mul_le_mul_of_nonneg_left ih hfac
      _ = ∏ k ∈ range (n + 1), (1 - a k) := by
          rw [Finset.prod_range_succ]
          ring

/-- **Product to exponential**: `∏ (1 - a k) ≤ exp (- ∑ a k)`.

Each factor obeys `1 - x ≤ e^{-x}`, and the factors are non-negative, so the products
compare. This is the step that turns the telescope into a decay rate. -/
theorem prod_one_sub_le_exp_neg_sum (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) (n : ℕ) :
    ∏ k ∈ range n, (1 - a k) ≤ Real.exp (-(∑ k ∈ range n, a k)) := by
  have hterm : ∀ k ∈ range n, (1 - a k) ≤ Real.exp (-(a k)) := by
    intro k _
    have := Real.add_one_le_exp (-(a k))
    linarith
  have hnonneg : ∀ k ∈ range n, (0 : ℝ) ≤ 1 - a k := by
    intro k _
    linarith [ha1 k]
  calc ∏ k ∈ range n, (1 - a k)
      ≤ ∏ k ∈ range n, Real.exp (-(a k)) :=
        Finset.prod_le_prod hnonneg hterm
    _ = Real.exp (∑ k ∈ range n, -(a k)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ k ∈ range n, a k)) := by rw [Finset.sum_neg_distrib]

/-! ## The master decay bound -/

/-- **The master decay bound.**

`|E ∏ χ| ≤ exp(- ∑ θ · ε k · γ k)`, where `ε k` is the sequential freshness of coordinate
`k` and `γ k` the oscillation gain there.

**The discard constant `θ` is a parameter.** In the current proof `θ = 1/2`, coming from
the Markov step that throws away the worst half of the fibers to obtain an average `γ`.
Audit point AP-α asks whether an order-free simultaneous splitting improves it. Because it
is an argument rather than a literal, a better constant is substituted without restating
the theorem, and a failure of that argument degrades `θ` rather than falsifying anything.

The per-step contraction is the hypothesis `hstep`; deriving it from a genuine conditional
law needs disintegration, which this module does not carry. What is proved here is that
the step bound gives the exponential bound, for **any coupling whatsoever** — which is the
point of the theorem, and the step that replaces the product-of-characteristic-functions
argument everywhere downstream. -/
theorem master_decay_bound (E : ℕ → ℝ) (θ : ℝ) (ε γ : ℕ → ℝ)
    (hθ0 : 0 ≤ θ) (hfresh : ∀ k, 0 ≤ ε k) (hgain : ∀ k, 0 ≤ γ k)
    (hle : ∀ k, θ * ε k * γ k ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - θ * ε k * γ k) * |E k|) (n : ℕ) :
    |E n| ≤ Real.exp (-(∑ k ∈ range n, θ * ε k * γ k)) := by
  have ha0 : ∀ k, 0 ≤ θ * ε k * γ k := fun k =>
    mul_nonneg (mul_nonneg hθ0 (hfresh k)) (hgain k)
  exact le_trans (abs_le_prod_of_step E _ ha0 hle h0 hstep n)
    (prod_one_sub_le_exp_neg_sum _ ha0 hle n)

/-- **The master bound in terms of the effective independence dimension.**

If the oscillation gain is uniform, `γ k = γ`, then the exponent is `θ · γ · D` with
`D = ∑ ε k` the effective independence dimension along the chosen ordering. Taking the
maximum over orderings gives `D` and hence the sharpest form of the bound.

For independent coordinates every `ε k = 1`, so `D = n` and the bound recovers the
classical product decay. Under dependence `D` collapses gracefully — which is exactly the
behaviour the product-of-characteristic-functions step could not express. -/
theorem master_decay_bound_uniform (E : ℕ → ℝ) (θ γ : ℝ) (ε : ℕ → ℝ)
    (hθ0 : 0 ≤ θ) (hγ0 : 0 ≤ γ) (hfresh : ∀ k, 0 ≤ ε k)
    (hle : ∀ k, θ * ε k * γ ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - θ * ε k * γ) * |E k|) (n : ℕ) :
    |E n| ≤ Real.exp (-(θ * γ * ∑ k ∈ range n, ε k)) := by
  have hmain := master_decay_bound E θ ε (fun _ => γ) hθ0 hfresh (fun _ => hγ0) hle h0
    hstep n
  have hrw : ∑ k ∈ range n, θ * ε k * γ = θ * γ * ∑ k ∈ range n, ε k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rwa [hrw] at hmain

/-! ## The named inputs

House style: what this development does not prove appears as a named field, so anything
derived from it carries the input in its own type.
-/

/-- **Audit point AP-β**, and the disintegration input, carried as named fields.

`bandToOperatorNorm` is the passage from a pointwise kernel band to an operator-norm bound
on measures, in the coupled slice theorem. `stepBoundFromFreshness` is the derivation of
the per-step contraction from a genuine conditional law. Neither is proved here. -/
structure CoupledSliceHypotheses where
  /-- **AP-β.** Pointwise kernel band implies an operator-norm bound on measures. -/
  bandToOperatorNorm : Prop
  /-- The per-step contraction, derived from the conditional law by disintegration. -/
  stepBoundFromFreshness : Prop
  /-- **AP-α.** Whether an order-free simultaneous splitting improves the discard constant
  beyond `1/2`. Open; a failure weakens constants, not statements. -/
  orderFreeSplitting : Prop

end Calibrator.BundleRigidity
