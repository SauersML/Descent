/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# The nearest-drift count generator and the pointwise convex comparison

This module formalizes the finite-grid core of the dynamic convex-order theorem of
`DC §3` / `PL §5`: the supporting-secant facts for grid-convex functions, the
pointwise convex-generator inequality (DC Lemma 3.4, PL (5.12)), and convexity
preservation under the one-step skeleton of the minimizing generator (DC Lemma 3.3,
PL (5.11)).

`countDrift n α β k = β (n - k) - α k` is the conditional drift of the occupied count
of `n` coordinates whose individual turnover rates are `1 → 0 : α` and `0 → 1 : β`
conditional on the full joint past (DC (3.3)). `nearestDriftGen` is the birth-death
generator `L_*` of DC (3.4) / PL (5.8) built from it, and `driftStep n α β τ` is the
one-step skeleton `I + τ L_*`.

Hypotheses are exactly the manuscript's domain conditions: nonnegative coordinate
rates, a state inside `{0, …, n}`, grid convexity of the test function, and a step
length short enough that `I + τ L_*` is substochastic. Nothing assumes the comparison,
the convexity of the evolved function, or any intermediate identity.

Built on `Descent.Portability.PortabilityMasterTheorem`: the generator inequality is
also stated against `weightedExp`, the expectation attached to a finite rate/probability
vector there.

## Empirical status

None. The bodies here are algebra: `countDrift`, `nearestDriftGen` and `driftStep` are the
drift, the generator and the one-step operator of a model, and the theorems are identities
and inequalities about them. What would carry an empirical status is a named quantity in a
subsystem module asserting that this algebra computes a measured turnover rate; no such
claim is made here, and no rate in this file is fitted to anything.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConvexOrderCoupling

open Foundations

noncomputable section

/-! ## The minimizing count generator -/

/-- The conditional drift `b(k) = β (n - k) - α k` of the occupied count at count `k`,
DC (3.3) / PL Theorem 5.3.  Every admissible joint process has this drift regardless of
how its coordinates are coupled, because the coordinate rates are fixed. -/
def countDrift (n : ℕ) (α β : ℝ) (k : ℤ) : ℝ := β * ((n : ℝ) - (k : ℝ)) - α * (k : ℝ)

/-- The upward rate `b(k)₊` of the nearest-drift generator DC (3.4). -/
def upRate (n : ℕ) (α β : ℝ) (k : ℤ) : ℝ := max (countDrift n α β k) 0

/-- The downward rate `(-b(k))₊` of the nearest-drift generator DC (3.4). -/
def downRate (n : ℕ) (α β : ℝ) (k : ℤ) : ℝ := max (-(countDrift n α β k)) 0

/-- The nearest-drift birth-death generator `L_*` of DC (3.4) / PL (5.8): all the drift
is spent on the single adjacent step in its own direction, and nothing else moves. -/
def nearestDriftGen (n : ℕ) (α β : ℝ) (f : ℤ → ℝ) (k : ℤ) : ℝ :=
  upRate n α β k * (f (k + 1) - f k) + downRate n α β k * (f (k - 1) - f k)

/-- One step `I + τ L_*` of the skeleton chain of the nearest-drift generator. -/
def driftStep (n : ℕ) (α β τ : ℝ) (f : ℤ → ℝ) : ℤ → ℝ :=
  fun k ↦ f k + τ * nearestDriftGen n α β f k

/-- Both rates are nonnegative. -/
theorem upRate_nonneg (n : ℕ) (α β : ℝ) (k : ℤ) : 0 ≤ upRate n α β k := le_max_right _ _

/-- Both rates are nonnegative. -/
theorem downRate_nonneg (n : ℕ) (α β : ℝ) (k : ℤ) : 0 ≤ downRate n α β k := le_max_right _ _

/-- The two rates differ by the drift: `b(k)₊ - (-b(k))₊ = b(k)`. -/
theorem downRate_eq (n : ℕ) (α β : ℝ) (k : ℤ) :
    downRate n α β k = upRate n α β k - countDrift n α β k := by
  simp only [upRate, downRate]
  rcases le_total 0 (countDrift n α β k) with hk | hk
  · rw [max_eq_left hk, max_eq_right (neg_nonpos.mpr hk)]
    ring
  · rw [max_eq_right hk, max_eq_left (neg_nonneg.mpr hk)]
    ring

/-- There is no upward rate at the top state: the count cannot leave `{0, …, n}`. -/
theorem upRate_top (n : ℕ) (α β : ℝ) (hα : 0 ≤ α) : upRate n α β (n : ℤ) = 0 := by
  simp only [upRate, countDrift]
  have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [hcast]
  have : β * ((n : ℝ) - (n : ℝ)) - α * (n : ℝ) ≤ 0 := by
    have : 0 ≤ α * (n : ℝ) := mul_nonneg hα (Nat.cast_nonneg n)
    nlinarith
  exact max_eq_right this

/-- There is no downward rate at the bottom state. -/
theorem downRate_bot (n : ℕ) (α β : ℝ) (hβ : 0 ≤ β) : downRate n α β 0 = 0 := by
  simp only [downRate, countDrift]
  have hcast : (((0 : ℤ)) : ℝ) = (0 : ℝ) := by norm_num
  rw [hcast]
  have : -(β * ((n : ℝ) - 0) - α * 0) ≤ 0 := by
    have : 0 ≤ β * (n : ℝ) := mul_nonneg hβ (Nat.cast_nonneg n)
    nlinarith
  exact max_eq_right this

/-! ## Supporting secants of a grid-convex function

A function on `{0, …, n}` is grid convex when `f (k-1) - 2 f k + f (k+1) ≥ 0` for
`1 ≤ k < n`.  This hypothesis is written out at each use rather than named, so that no
theorem below rests on an unwitnessed `Prop`. -/

/-- Adjacent slopes of a grid-convex function are nondecreasing. -/
theorem slope_le_slope (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {a c : ℤ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c + 1 ≤ (n : ℤ)) :
    f (a + 1) - f a ≤ f (c + 1) - f c := by
  revert hc
  induction c, hac using Int.le_induction with
  | base => intro _; exact le_rfl
  | succ c hac ih =>
    intro hc
    have h1 : f (a + 1) - f a ≤ f (c + 1) - f c := ih (by omega)
    have h2 : 0 ≤ f c - 2 * f (c + 1) + f (c + 1 + 1) := by
      have hx := hf (c + 1) (by omega) (by omega)
      have he : c + 1 - 1 = c := by ring
      rw [he] at hx
      exact hx
    linarith

/-- The right adjacent secant at `k` supports a grid-convex function at every grid point
above `k`. -/
theorem right_secant_up (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {k : ℤ} (hk0 : 0 ≤ k) (hkn : k + 1 ≤ (n : ℤ)) :
    ∀ j : ℤ, k ≤ j → j ≤ (n : ℤ) → (f (k + 1) - f k) * ((j : ℝ) - (k : ℝ)) ≤ f j - f k := by
  intro j hkj
  induction j, hkj using Int.le_induction with
  | base => intro _; simp
  | succ j hkj ih =>
    intro hjn
    have h1 : (f (k + 1) - f k) * ((j : ℝ) - (k : ℝ)) ≤ f j - f k := ih (by omega)
    have h2 : f (k + 1) - f k ≤ f (j + 1) - f j := slope_le_slope n f hf hk0 hkj (by omega)
    have hcast : (((j + 1 : ℤ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hx : (f (k + 1) - f k) * ((j : ℝ) + 1 - (k : ℝ))
        = (f (k + 1) - f k) * ((j : ℝ) - (k : ℝ)) + (f (k + 1) - f k) := by ring
    rw [hx]
    linarith

/-- The right adjacent secant at `k` also supports the function below `k`, because the
slopes below `k` are no larger. -/
theorem right_secant_down (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {k : ℤ} (hk0 : 0 ≤ k) (hkn : k + 1 ≤ (n : ℤ)) (d : ℕ) :
    0 ≤ k - (d : ℤ) →
      (f (k + 1) - f k) * (((k - (d : ℤ) : ℤ) : ℝ) - (k : ℝ)) ≤ f (k - (d : ℤ)) - f k := by
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have hstep : (k : ℤ) - ((d + 1 : ℕ) : ℤ) = k - (d : ℤ) - 1 := by push_cast; ring
    rw [hstep] at hd ⊢
    have h1 := ih (by omega)
    have h2 : f (k - (d : ℤ) - 1 + 1) - f (k - (d : ℤ) - 1) ≤ f (k + 1) - f k :=
      slope_le_slope n f hf (by omega) (by omega) hkn
    have he : k - (d : ℤ) - 1 + 1 = k - (d : ℤ) := by ring
    rw [he] at h2
    have hc1 : (((k - (d : ℤ) - 1 : ℤ)) : ℝ) = (((k - (d : ℤ) : ℤ)) : ℝ) - 1 := by
      push_cast; ring
    rw [hc1]
    have hx : (f (k + 1) - f k) * ((((k - (d : ℤ) : ℤ)) : ℝ) - 1 - (k : ℝ))
        = (f (k + 1) - f k) * ((((k - (d : ℤ) : ℤ)) : ℝ) - (k : ℝ)) - (f (k + 1) - f k) := by
      ring
    rw [hx]
    linarith

/-- **Right-secant support** (the inequality DC Lemma 3.4 calls "summing adjacent
slopes"): for grid-convex `f` and any grid point `j`, `f j - f k ≥ (f (k+1) - f k)(j - k)`. -/
theorem right_secant_support (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {k j : ℤ} (hk0 : 0 ≤ k) (hkn : k + 1 ≤ (n : ℤ)) (hj0 : 0 ≤ j) (hjn : j ≤ (n : ℤ)) :
    (f (k + 1) - f k) * ((j : ℝ) - (k : ℝ)) ≤ f j - f k := by
  rcases le_total k j with hkj | hjk
  · exact right_secant_up n f hf hk0 hkn j hkj hjn
  · have h := right_secant_down n f hf hk0 hkn (k - j).toNat (by omega)
    have he : k - (((k - j).toNat : ℕ) : ℤ) = j := by omega
    rw [he] at h
    exact h

/-- **Left-secant support**: the left adjacent secant at `k` also supports a grid-convex
function at every grid point. -/
theorem left_secant_support (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {k j : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ (n : ℤ)) (hj0 : 0 ≤ j) (hjn : j ≤ (n : ℤ)) :
    (f k - f (k - 1)) * ((j : ℝ) - (k : ℝ)) ≤ f j - f k := by
  have h := right_secant_support n f hf (k := k - 1) (j := j) (by omega) (by omega) hj0 hjn
  have hk' : k - 1 + 1 = k := by ring
  rw [hk'] at h
  have hc : (((k - 1 : ℤ)) : ℝ) = (k : ℝ) - 1 := by push_cast; ring
  rw [hc] at h
  have hx : (f k - f (k - 1)) * ((j : ℝ) - ((k : ℝ) - 1))
      = (f k - f (k - 1)) * ((j : ℝ) - (k : ℝ)) + (f k - f (k - 1)) := by ring
  rw [hx] at h
  linarith

/-- **Endpoint chord bound**: a grid-convex function lies below the chord joining its two
endpoints, `n · f k ≤ (n - k) f 0 + k f n`.  This is the inequality supplying the upper
half of DC (3.6) / PL (5.10). -/
theorem chord_bound (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {k : ℤ} (hk0 : 0 ≤ k) (hkn : k ≤ (n : ℤ)) :
    (n : ℝ) * f k ≤ ((n : ℝ) - (k : ℝ)) * f 0 + (k : ℝ) * f ((n : ℤ)) := by
  rcases eq_or_lt_of_le hkn with heq | hlt
  · rw [heq]
    have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
    rw [hcast]
    ring_nf
    exact le_rfl
  · have hk1n : k + 1 ≤ (n : ℤ) := by omega
    have h0 := right_secant_support n f hf hk0 hk1n (j := 0) le_rfl (by omega)
    have hn := right_secant_support n f hf hk0 hk1n (j := (n : ℤ)) (by omega) le_rfl
    have hx0 : (f (k + 1) - f k) * ((((0 : ℤ)) : ℝ) - (k : ℝ))
        = -((f (k + 1) - f k) * (k : ℝ)) := by push_cast; ring
    rw [hx0] at h0
    have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
    rw [hcast] at hn
    have hnk : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
      have : ((k : ℤ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hkn
      linarith
    have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
    have e1 : ((n : ℝ) - (k : ℝ)) * (f k - (f (k + 1) - f k) * (k : ℝ))
        ≤ ((n : ℝ) - (k : ℝ)) * f 0 := by
      apply mul_le_mul_of_nonneg_left _ hnk
      linarith
    have e2 : (k : ℝ) * (f k + (f (k + 1) - f k) * ((n : ℝ) - (k : ℝ)))
        ≤ (k : ℝ) * f ((n : ℤ)) := by
      apply mul_le_mul_of_nonneg_left _ hkR
      linarith
    have key : ((n : ℝ) - (k : ℝ)) * (f k - (f (k + 1) - f k) * (k : ℝ))
        + (k : ℝ) * (f k + (f (k + 1) - f k) * ((n : ℝ) - (k : ℝ))) = (n : ℝ) * f k := by
      ring
    linarith

/-! ## Convexity preservation under the minimizing step -/

/-- The algebraic identity behind DC (3.8) / PL (5.11): the second difference of
`(I + τ L) f` is a nonnegative combination of second differences of `f`, provided only
that the drift `b` is affine (`bm + bp = 2 b0`) and the rates satisfy `ℓ - d = b`. -/
theorem second_difference_identity (τ bm b0 bp lm l0 lp fm2 fm1 f0 f1 f2 : ℝ)
    (haff : bm + bp = 2 * b0) :
    (fm1 + τ * (lm * (f0 - fm1) + (lm - bm) * (fm2 - fm1)))
        - 2 * (f0 + τ * (l0 * (f1 - f0) + (l0 - b0) * (fm1 - f0)))
        + (f1 + τ * (lp * (f2 - f1) + (lp - bp) * (f0 - f1)))
      = (fm1 - 2 * f0 + f1)
        + τ * (lp * (f0 - 2 * f1 + f2) + (lm - bm) * (fm2 - 2 * fm1 + f0)
          + (bp - 2 * l0) * (fm1 - 2 * f0 + f1)) := by
  linear_combination (τ * (f0 - fm1)) * haff

/-- The drift of the count is affine in the count, which is what makes DC (3.8) work. -/
theorem countDrift_affine (n : ℕ) (α β : ℝ) (k : ℤ) :
    countDrift n α β (k - 1) + countDrift n α β (k + 1) = 2 * countDrift n α β k := by
  simp only [countDrift]
  push_cast
  ring

/-- Second difference of one nearest-drift step, DC (3.8) / PL (5.11) in skeleton form. -/
theorem driftStep_second_difference (n : ℕ) (α β τ : ℝ) (f : ℤ → ℝ) (k : ℤ) :
    driftStep n α β τ f (k - 1) - 2 * driftStep n α β τ f k + driftStep n α β τ f (k + 1)
      = (f (k - 1) - 2 * f k + f (k + 1))
        + τ * (upRate n α β (k + 1) * (f k - 2 * f (k + 1) + f (k + 2))
          + downRate n α β (k - 1) * (f (k - 2) - 2 * f (k - 1) + f k)
          + (countDrift n α β (k + 1) - 2 * upRate n α β k)
            * (f (k - 1) - 2 * f k + f (k + 1))) := by
  simp only [driftStep, nearestDriftGen, downRate_eq]
  have e1 : k - 1 + 1 = k := by ring
  have e2 : k - 1 - 1 = k - 2 := by ring
  have e3 : k + 1 + 1 = k + 2 := by ring
  have e4 : k + 1 - 1 = k := by ring
  rw [e1, e2, e3, e4]
  linear_combination (τ * (f k - f (k - 1))) * countDrift_affine n α β k

/-- **Convexity preservation, DC Lemma 3.3 / PL (5.11), in skeleton form.**

One step `I + τ L_*` of the nearest-drift generator maps grid-convex functions to
grid-convex functions, provided the step is short: `τ · 2 n (α + β) ≤ 1`.  The three
ingredients are the second-difference identity, the vanishing of the outward rates at
the two endpoints, and nonnegativity of the diagonal coefficient. -/
theorem driftStep_gridConvex (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    (j : ℤ) (hj1 : 1 ≤ j) (hjn : j + 1 ≤ (n : ℤ)) :
    0 ≤ driftStep n α β τ f (j - 1) - 2 * driftStep n α β τ f j
      + driftStep n α β τ f (j + 1) := by
  have hH : 0 ≤ f (j - 1) - 2 * f j + f (j + 1) := hf j hj1 hjn
  have hA : 0 ≤ upRate n α β (j + 1) * (f j - 2 * f (j + 1) + f (j + 2)) := by
    by_cases hcase : j + 2 ≤ (n : ℤ)
    · have hx := hf (j + 1) (by omega) (by omega)
      have ea : j + 1 - 1 = j := by ring
      have eb : j + 1 + 1 = j + 2 := by ring
      rw [ea, eb] at hx
      exact mul_nonneg (upRate_nonneg n α β _) hx
    · have hje : j + 1 = (n : ℤ) := by omega
      rw [hje, upRate_top n α β hα]
      simp
  have hB : 0 ≤ downRate n α β (j - 1) * (f (j - 2) - 2 * f (j - 1) + f j) := by
    by_cases hcase : 1 ≤ j - 1
    · have hx := hf (j - 1) hcase (by omega)
      have ea : j - 1 - 1 = j - 2 := by ring
      have eb : j - 1 + 1 = j := by ring
      rw [ea, eb] at hx
      exact mul_nonneg (downRate_nonneg n α β _) hx
    · have hje : j - 1 = 0 := by omega
      rw [hje, downRate_bot n α β hβ]
      simp
  have hjR : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ j)
  have hj1R : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcd : -((n : ℝ) * α) ≤ countDrift n α β (j + 1) := by
    simp only [countDrift]
    push_cast
    nlinarith [mul_nonneg hβ (by linarith : (0 : ℝ) ≤ (n : ℝ) - ((j : ℝ) + 1)),
      mul_le_mul_of_nonneg_left hj1R hα]
  have hup : upRate n α β j ≤ (n : ℝ) * β := by
    simp only [upRate, countDrift]
    rcases le_total (β * ((n : ℝ) - (j : ℝ)) - α * (j : ℝ)) 0 with hcase | hcase
    · rw [max_eq_right hcase]
      exact mul_nonneg hnR hβ
    · rw [max_eq_left hcase]
      nlinarith [mul_nonneg hα hjR, mul_le_mul_of_nonneg_left hjR hβ]
  have hc : 0 ≤ 1 + τ * (countDrift n α β (j + 1) - 2 * upRate n α β j) := by
    have hlow : -(2 * (n : ℝ) * (α + β))
        ≤ countDrift n α β (j + 1) - 2 * upRate n α β j := by
      nlinarith [mul_nonneg hnR hα]
    nlinarith [mul_le_mul_of_nonneg_left hlow hτ]
  have hrw : f (j - 1) - 2 * f j + f (j + 1)
        + τ * (upRate n α β (j + 1) * (f j - 2 * f (j + 1) + f (j + 2))
          + downRate n α β (j - 1) * (f (j - 2) - 2 * f (j - 1) + f j)
          + (countDrift n α β (j + 1) - 2 * upRate n α β j)
            * (f (j - 1) - 2 * f j + f (j + 1)))
      = (1 + τ * (countDrift n α β (j + 1) - 2 * upRate n α β j))
          * (f (j - 1) - 2 * f j + f (j + 1))
        + τ * (upRate n α β (j + 1) * (f j - 2 * f (j + 1) + f (j + 2)))
        + τ * (downRate n α β (j - 1) * (f (j - 2) - 2 * f (j - 1) + f j)) := by
    ring
  rw [driftStep_second_difference, hrw]
  have t1 := mul_nonneg hc hH
  have t2 := mul_nonneg hτ hA
  have t3 := mul_nonneg hτ hB
  linarith

/-- Every iterate of the nearest-drift step preserves grid convexity. -/
theorem driftStep_iterate_gridConvex (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1)) (m : ℕ) :
    ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ (driftStep n α β τ)^[m] f (j - 1) - 2 * (driftStep n α β τ)^[m] f j
        + (driftStep n α β τ)^[m] f (j + 1) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    intro j hj1 hjn
    rw [Function.iterate_succ_apply']
    exact driftStep_gridConvex n α β τ hα hβ hτ hshort _ ih j hj1 hjn

/-! ## The pointwise convex-generator inequality -/

/-- Summing a supporting-secant inequality against nonnegative rates with prescribed
total drift.  This is the single algebraic step in the proof of DC Lemma 3.4. -/
theorem sum_rate_secant_bound {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ A, 0 ≤ r A)
    (Δ : ι → ℤ) (f : ℤ → ℝ) (k : ℤ) (s D : ℝ)
    (hsupp : ∀ A, s * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ)) ≤ f (k + Δ A) - f k)
    (hdrift : ∑ A, r A * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ)) = D) :
    s * D ≤ ∑ A, r A * (f (k + Δ A) - f k) := by
  have h1 : ∑ A, r A * (s * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ)))
      ≤ ∑ A, r A * (f (k + Δ A) - f k) :=
    Finset.sum_le_sum fun A _ ↦ mul_le_mul_of_nonneg_left (hsupp A) (hr A)
  have h2 : ∑ A, r A * (s * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ))) = s * D := by
    rw [← hdrift, Finset.mul_sum]
    exact Finset.sum_congr rfl fun A _ ↦ by ring
  linarith

/-- **The pointwise convex-generator inequality, DC Lemma 3.4 / PL (5.12).**

Let `f` be grid convex on `{0, …, n}` and let `r` be any nonnegative family of subset-flip
rates at a state with count `k`, with integer count changes `Δ` that stay inside the grid
and total drift `τ · b(k)` fixed by the coordinate-rate constraints DC (3.2) / PL (5.7).
Then the generator of the count acting on `f` is at least the nearest-drift generator:
no admissible coupling can push a convex aggregate below `L_*`.

The hypotheses are the manuscript's: nonnegative rates, states inside the grid, and the
drift constraint.  Nothing about the geometry of the subsets is assumed, so the statement
covers arbitrary simultaneous flips and arbitrary history dependence at that instant. -/
theorem nearestDrift_generator_le (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    (k : ℤ) (hk0 : 0 ≤ k) (hkn : k ≤ (n : ℤ)) {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ A, 0 ≤ r A) (Δ : ι → ℤ) (hΔ0 : ∀ A, 0 ≤ k + Δ A) (hΔn : ∀ A, k + Δ A ≤ (n : ℤ))
    (hdrift : ∑ A, r A * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ)) = τ * countDrift n α β k) :
    τ * nearestDriftGen n α β f k ≤ ∑ A, r A * (f (k + Δ A) - f k) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  rcases lt_trichotomy (countDrift n α β k) 0 with hb | hb | hb
  · -- downward drift: the state is not the bottom, use the left secant
    have hk1 : 1 ≤ k := by
      by_contra hcon
      have hk0' : k = 0 := by omega
      rw [hk0'] at hb
      simp only [countDrift] at hb
      have : (((0 : ℤ)) : ℝ) = (0 : ℝ) := by norm_num
      rw [this] at hb
      nlinarith [mul_nonneg hβ (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hsupp : ∀ A, (f k - f (k - 1)) * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ))
        ≤ f (k + Δ A) - f k := fun A ↦
      left_secant_support n f hf hk1 hkn (hΔ0 A) (hΔn A)
    have hmain := sum_rate_secant_bound r hr Δ f k (f k - f (k - 1))
      (τ * countDrift n α β k) hsupp hdrift
    have hup : upRate n α β k = 0 := max_eq_right (le_of_lt hb)
    have hdn : downRate n α β k = -(countDrift n α β k) :=
      max_eq_left (by linarith : (0 : ℝ) ≤ -(countDrift n α β k))
    simp only [nearestDriftGen, hup, hdn]
    nlinarith [hmain]
  · -- zero drift: the nearest-drift generator contributes nothing
    have hup : upRate n α β k = 0 := by simp [upRate, hb]
    have hdn : downRate n α β k = 0 := by simp [downRate, hb]
    have hgoal : τ * nearestDriftGen n α β f k = 0 := by
      simp only [nearestDriftGen, hup, hdn]
      ring
    rw [hgoal]
    by_cases hk1n : k + 1 ≤ (n : ℤ)
    · have hsupp : ∀ A, (f (k + 1) - f k) * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ))
          ≤ f (k + Δ A) - f k := fun A ↦
        right_secant_support n f hf hk0 hk1n (hΔ0 A) (hΔn A)
      have hmain := sum_rate_secant_bound r hr Δ f k (f (k + 1) - f k)
        (τ * countDrift n α β k) hsupp hdrift
      rw [hb] at hmain
      nlinarith [hmain]
    · by_cases hk1 : 1 ≤ k
      · have hsupp : ∀ A, (f k - f (k - 1)) * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ))
            ≤ f (k + Δ A) - f k := fun A ↦
          left_secant_support n f hf hk1 hkn (hΔ0 A) (hΔn A)
        have hmain := sum_rate_secant_bound r hr Δ f k (f k - f (k - 1))
          (τ * countDrift n α β k) hsupp hdrift
        rw [hb] at hmain
        nlinarith [hmain]
      · have hzero : ∀ A, Δ A = 0 := by
          intro A
          have h1 := hΔ0 A
          have h2 := hΔn A
          omega
        have : ∑ A, r A * (f (k + Δ A) - f k) = 0 := by
          refine Finset.sum_eq_zero fun A _ ↦ ?_
          rw [hzero A]
          simp
        rw [this]
  · -- upward drift: the state is not the top, use the right secant
    have hk1n : k + 1 ≤ (n : ℤ) := by
      by_contra hcon
      have hke : k = (n : ℤ) := by omega
      rw [hke] at hb
      simp only [countDrift] at hb
      have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
      rw [hcast] at hb
      nlinarith [mul_nonneg hα (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hsupp : ∀ A, (f (k + 1) - f k) * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ))
        ≤ f (k + Δ A) - f k := fun A ↦
      right_secant_support n f hf hk0 hk1n (hΔ0 A) (hΔn A)
    have hmain := sum_rate_secant_bound r hr Δ f k (f (k + 1) - f k)
      (τ * countDrift n α β k) hsupp hdrift
    have hup : upRate n α β k = countDrift n α β k := max_eq_left (le_of_lt hb)
    have hdn : downRate n α β k = 0 :=
      max_eq_right (by linarith : -(countDrift n α β k) ≤ 0)
    simp only [nearestDriftGen, hup, hdn]
    nlinarith [hmain]

/-- The generator inequality stated against the corpus expectation functional
`Descent.Portability.weightedExp`: when the admissible instantaneous rates are a
probability vector (a one-step kernel row), the nearest-drift generator is a lower bound
for the expected increment of any grid-convex aggregate report. -/
theorem nearestDrift_generator_le_weightedExp (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    (k : ℤ) (hk0 : 0 ≤ k) (hkn : k ≤ (n : ℤ)) {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ A, 0 ≤ p A) (hsum : ∑ A, p A = 1) (Δ : ι → ℤ) (hΔ0 : ∀ A, 0 ≤ k + Δ A)
    (hΔn : ∀ A, k + Δ A ≤ (n : ℤ))
    (hdrift : ∑ A, p A * ((((k + Δ A : ℤ)) : ℝ) - (k : ℝ)) = τ * countDrift n α β k) :
    τ * nearestDriftGen n α β f k
      ≤ weightedExp p hp hsum (fun A ↦ f (k + Δ A) - f k) := by
  simpa using nearestDrift_generator_le n α β τ hα hβ f hf k hk0 hkn p hp Δ hΔ0 hΔn hdrift


/-! ## Coadapted discrete-time couplings on the configuration space -/

/-- The occupied count `N = ∑ᵢ Bᵢ` of a configuration of `n` binary coordinates. -/
def occupiedCount {n : ℕ} (s : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ s i = true).card

/-- The count never leaves the grid `{0, …, n}`. -/
theorem occupiedCount_le {n : ℕ} (s : Fin n → Bool) : occupiedCount s ≤ n := by
  simpa using Finset.card_filter_le Finset.univ (fun i ↦ s i = true)

/-- The count is the sum of the coordinate indicators. -/
theorem occupiedCount_eq_sum {n : ℕ} (s : Fin n → Bool) :
    ((occupiedCount s : ℕ) : ℝ) = ∑ i, (if s i = true then (1 : ℝ) else 0) := by
  simp [occupiedCount, Finset.sum_boole]

/-- The complementary count. -/
theorem occupiedCount_compl {n : ℕ} (s : Fin n → Bool) :
    ∑ i, (if s i = true then (0 : ℝ) else 1) = (n : ℝ) - ((occupiedCount s : ℕ) : ℝ) := by
  have hpt : ∀ i : Fin n,
      (if s i = true then (0 : ℝ) else 1) = 1 - (if s i = true then (1 : ℝ) else 0) := by
    intro i
    cases hsi : s i <;> simp
  rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_sub_distrib, ← occupiedCount_eq_sum]
  simp

/-- **The count drift is forced by the coordinate rates, DC (3.3) / PL Theorem 5.3.**

If a one-step kernel row `K s ·` changes coordinate `i` with total probability
`τ α` when `sᵢ = 1` and `τ β` when `sᵢ = 0` -- which is DC (3.2) / PL (5.7) written for a
discrete skeleton -- then the mean change of the count is exactly `τ b(k)`, whatever the
joint geometry of the simultaneous flips. -/
theorem kernel_count_drift {n : ℕ} (α β τ : ℝ) (K : (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (s : Fin n → Bool)
    (hflip : ∀ i : Fin n, ∑ s', (if s' i = s i then (0 : ℝ) else K s s')
      = τ * (if s i = true then α else β)) :
    ∑ s', K s s' * (((occupiedCount s' : ℕ) : ℝ) - ((occupiedCount s : ℕ) : ℝ))
      = τ * (β * ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ))
        - α * ((occupiedCount s : ℕ) : ℝ)) := by
  have hexp : ∀ s' : Fin n → Bool,
      K s s' * (((occupiedCount s' : ℕ) : ℝ) - ((occupiedCount s : ℕ) : ℝ))
        = ∑ i, K s s' * ((if s' i = true then (1 : ℝ) else 0)
          - (if s i = true then (1 : ℝ) else 0)) := by
    intro s'
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← occupiedCount_eq_sum, ← occupiedCount_eq_sum]
  have hterm : ∀ (i : Fin n) (s' : Fin n → Bool),
      K s s' * ((if s' i = true then (1 : ℝ) else 0) - (if s i = true then (1 : ℝ) else 0))
        = (if s' i = s i then (0 : ℝ) else K s s') * (if s i = true then (-1 : ℝ) else 1) := by
    intro i s'
    cases hsi : s i <;> cases hsi' : s' i <;> simp
  have hi : ∀ i : Fin n,
      ∑ s' : Fin n → Bool, K s s' * ((if s' i = true then (1 : ℝ) else 0)
        - (if s i = true then (1 : ℝ) else 0))
      = (if s i = true then (-1 : ℝ) else 1) * (τ * (if s i = true then α else β)) := by
    intro i
    rw [Finset.sum_congr rfl fun s' _ ↦ hterm i s', ← Finset.sum_mul, hflip i]
    ring
  rw [Finset.sum_congr rfl fun s' _ ↦ hexp s', Finset.sum_comm,
    Finset.sum_congr rfl fun i _ ↦ hi i]
  have hsplit : ∀ i : Fin n,
      (if s i = true then (-1 : ℝ) else 1) * (τ * (if s i = true then α else β))
        = (if s i = true then (1 : ℝ) else 0) * (-(τ * α))
          + (if s i = true then (0 : ℝ) else 1) * (τ * β) := by
    intro i
    cases hsi : s i <;> simp
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, ← occupiedCount_eq_sum, occupiedCount_compl]
  ring

/-- The expected report of a possibly history-dependent joint turnover process.
`pathExp K m hist s g` is `E[g(S_m)]` for a process currently at configuration `s` with
past `hist`, running `m` further skeleton steps under the kernel family `K`.  The kernel
may depend on the whole past, so this covers non-Markov, non-exchangeable couplings. -/
def pathExp {n : ℕ} (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    ℕ → List (Fin n → Bool) → (Fin n → Bool) → ((Fin n → Bool) → ℝ) → ℝ
  | 0, _, s, g => g s
  | (m + 1), hist, s, g => ∑ s', K hist s s' * pathExp K m (s :: hist) s' g

/-- A path expectation is monotone in its report. -/
theorem pathExp_mono {n : ℕ} (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK0 : ∀ hist s s', 0 ≤ K hist s s') (g g' : (Fin n → Bool) → ℝ) (hg : ∀ x, g x ≤ g' x)
    (m : ℕ) : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      pathExp K m hist s g ≤ pathExp K m hist s g' := by
  induction m with
  | zero => intro hist s; simpa [pathExp] using hg s
  | succ m ih =>
    intro hist s
    simp only [pathExp]
    exact Finset.sum_le_sum fun s' _ ↦
      mul_le_mul_of_nonneg_left (ih (s :: hist) s') (hK0 hist s s')

/-- A path expectation commutes with affine maps of its report. -/
theorem pathExp_affine {n : ℕ} (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK1 : ∀ hist s, ∑ s', K hist s s' = 1) (a c : ℝ) (g : (Fin n → Bool) → ℝ) (m : ℕ) :
    ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      pathExp K m hist s (fun x ↦ a + c * g x) = a + c * pathExp K m hist s g := by
  induction m with
  | zero => intro hist s; simp [pathExp]
  | succ m ih =>
    intro hist s
    have hpt : ∀ s' : Fin n → Bool,
        K hist s s' * pathExp K m (s :: hist) s' (fun x ↦ a + c * g x)
          = a * K hist s s' + c * (K hist s s' * pathExp K m (s :: hist) s' g) := by
      intro s'
      rw [ih (s :: hist) s']
      ring
    simp only [pathExp]
    rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hK1 hist s, mul_one]

/-- **One skeleton step of an admissible coupling dominates the nearest-drift step.**

This is DC Lemma 3.4 transported from rates to a one-step kernel on `{0,1}ⁿ`: the only
facts used about `K` are that its row is a probability vector and that it flips each
coordinate with the prescribed probability. -/
theorem step_le_kernel {n : ℕ} (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (hK0 : ∀ s', 0 ≤ K s s') (hK1 : ∑ s', K s s' = 1)
    (hflip : ∀ i : Fin n, ∑ s', (if s' i = s i then (0 : ℝ) else K s s')
      = τ * (if s i = true then α else β)) :
    driftStep n α β τ f ((occupiedCount s : ℕ) : ℤ)
      ≤ ∑ s', K s s' * f ((occupiedCount s' : ℕ) : ℤ) := by
  set k : ℤ := ((occupiedCount s : ℕ) : ℤ) with hkdef
  have hidx : ∀ s' : Fin n → Bool,
      k + (((occupiedCount s' : ℕ) : ℤ) - k) = ((occupiedCount s' : ℕ) : ℤ) := by
    intro s'
    ring
  have hdrift : ∑ s' : Fin n → Bool,
      K s s' * ((((k + (((occupiedCount s' : ℕ) : ℤ) - k)) : ℤ) : ℝ) - (k : ℝ))
      = τ * countDrift n α β k := by
    have hpt : ∀ s' : Fin n → Bool,
        K s s' * ((((k + (((occupiedCount s' : ℕ) : ℤ) - k)) : ℤ) : ℝ) - (k : ℝ))
          = K s s' * (((occupiedCount s' : ℕ) : ℝ) - ((occupiedCount s : ℕ) : ℝ)) := by
      intro s'
      rw [hidx s', hkdef]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', kernel_count_drift α β τ K s hflip, hkdef]
    simp only [countDrift]
    push_cast
    ring
  have hgen := nearestDrift_generator_le n α β τ hα hβ f hf k (by positivity)
    (by rw [hkdef]; exact_mod_cast occupiedCount_le s) (K s) hK0
    (fun s' ↦ ((occupiedCount s' : ℕ) : ℤ) - k)
    (fun s' ↦ by rw [hidx s']; positivity)
    (fun s' ↦ by rw [hidx s']; exact_mod_cast occupiedCount_le s') hdrift
  have hrhs : ∑ s' : Fin n → Bool,
      K s s' * (f (k + (((occupiedCount s' : ℕ) : ℤ) - k)) - f k)
      = (∑ s' : Fin n → Bool, K s s' * f ((occupiedCount s' : ℕ) : ℤ)) - f k := by
    have hpt : ∀ s' : Fin n → Bool,
        K s s' * (f (k + (((occupiedCount s' : ℕ) : ℤ) - k)) - f k)
          = K s s' * f ((occupiedCount s' : ℕ) : ℤ) - K s s' * f k := by
      intro s'
      rw [hidx s']
      ring
    rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', Finset.sum_sub_distrib, ← Finset.sum_mul, hK1,
      one_mul]
  rw [hrhs] at hgen
  simp only [driftStep]
  linarith

/-- **The sharp dynamic convex-order theorem, DC Theorem 3.1 / PL Theorem 5.3, proved in
discrete skeleton form.**

For every family of one-step kernels indexed by the entire past -- so for every possibly
history-dependent, non-Markov, non-exchangeable coadapted coupling whose coordinates flip
with the prescribed probabilities `τ α` and `τ β` -- and for every grid-convex report `f`
and every horizon `m`, the iterated nearest-drift step is a lower bound:
`(I + τ L_*)^m f (N₀) ≤ E f(N_m)`.  One and the same comparison chain works for every
convex `f` and every `m` simultaneously, which is the content of DC (3.5).

The step length enters only through `τ · 2 n (α + β) ≤ 1`, the condition making
`I + τ L_*` substochastic; the continuous-time statement is its `τ → 0` limit and is not
claimed here. -/
theorem pathExp_nearestDrift_le {n : ℕ} (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1)
    (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK0 : ∀ hist s s', 0 ≤ K hist s s') (hK1 : ∀ hist s, ∑ s', K hist s s' = 1)
    (hflip : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool) (i : Fin n),
      ∑ s', (if s' i = s i then (0 : ℝ) else K hist s s')
        = τ * (if s i = true then α else β)) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1)) (m : ℕ) :
    ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      (driftStep n α β τ)^[m] f ((occupiedCount s : ℕ) : ℤ)
        ≤ pathExp K m hist s (fun s' ↦ f ((occupiedCount s' : ℕ) : ℤ)) := by
  induction m with
  | zero => intro hist s; simp [pathExp]
  | succ m ih =>
    intro hist s
    rw [Function.iterate_succ_apply']
    have hconv := driftStep_iterate_gridConvex n α β τ hα hβ hτ hshort f hf m
    have h1 : driftStep n α β τ ((driftStep n α β τ)^[m] f) ((occupiedCount s : ℕ) : ℤ)
        ≤ ∑ s', K hist s s' * (driftStep n α β τ)^[m] f ((occupiedCount s' : ℕ) : ℤ) :=
      step_le_kernel α β τ hα hβ _ hconv (K hist) s (hK0 hist s) (hK1 hist s) (hflip hist s)
    have h2 : ∑ s' : Fin n → Bool,
        K hist s s' * (driftStep n α β τ)^[m] f ((occupiedCount s' : ℕ) : ℤ)
        ≤ ∑ s' : Fin n → Bool,
          K hist s s' * pathExp K m (s :: hist) s' (fun x ↦ f ((occupiedCount x : ℕ) : ℤ)) :=
      Finset.sum_le_sum fun s' _ ↦
        mul_le_mul_of_nonneg_left (ih (s :: hist) s') (hK0 hist s s')
    simp only [pathExp]
    linarith

/-! ## The common mean and the endpoint chord upper bound -/

/-- One step of the count-mean recursion forced by the coordinate-rate constraints:
`x ↦ x + τ (β (n - x) - α x)`.  Every admissible coupling obeys it, so all of them share
one mean-count trajectory (DC Theorem 3.1, "every admissible process has mean determined
by `m' = nβ - (α+β)m`"). -/
def meanStep (n : ℕ) (α β τ : ℝ) (x : ℝ) : ℝ := x + τ * (β * ((n : ℝ) - x) - α * x)

/-- Iterates of an affine map are affine. -/
theorem meanStep_iterate_affine (n : ℕ) (α β τ : ℝ) (m : ℕ) :
    ∃ a c : ℝ, ∀ x : ℝ, (meanStep n α β τ)^[m] x = a + c * x := by
  induction m with
  | zero => exact ⟨0, 1, fun x ↦ by simp⟩
  | succ m ih =>
    obtain ⟨a, c, hac⟩ := ih
    refine ⟨a + c * (τ * β * (n : ℝ)), c * (1 - τ * (α + β)), fun x ↦ ?_⟩
    rw [Function.iterate_succ_apply, hac (meanStep n α β τ x)]
    simp only [meanStep]
    ring

/-- **The mean count is the same for every admissible coupling.**

The coordinate-rate constraints alone pin the whole mean-count trajectory, which is what
makes the two extremal couplings comparable and is used for the chord bound. -/
theorem pathExp_count_mean {n : ℕ} (α β τ : ℝ)
    (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK1 : ∀ hist s, ∑ s', K hist s s' = 1)
    (hflip : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool) (i : Fin n),
      ∑ s', (if s' i = s i then (0 : ℝ) else K hist s s')
        = τ * (if s i = true then α else β)) (m : ℕ) :
    ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      pathExp K m hist s (fun s' ↦ ((occupiedCount s' : ℕ) : ℝ))
        = (meanStep n α β τ)^[m] ((occupiedCount s : ℕ) : ℝ) := by
  induction m with
  | zero => intro hist s; simp [pathExp]
  | succ m ih =>
    intro hist s
    obtain ⟨a, c, hac⟩ := meanStep_iterate_affine n α β τ m
    have hone : ∑ s' : Fin n → Bool, K hist s s' * ((occupiedCount s' : ℕ) : ℝ)
        = meanStep n α β τ ((occupiedCount s : ℕ) : ℝ) := by
      have hd := kernel_count_drift α β τ (K hist) s (hflip hist s)
      have hpt : ∀ s' : Fin n → Bool,
          K hist s s' * (((occupiedCount s' : ℕ) : ℝ) - ((occupiedCount s : ℕ) : ℝ))
            = K hist s s' * ((occupiedCount s' : ℕ) : ℝ)
              - K hist s s' * ((occupiedCount s : ℕ) : ℝ) := fun s' ↦ by ring
      rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', Finset.sum_sub_distrib, ← Finset.sum_mul,
        hK1 hist s, one_mul] at hd
      simp only [meanStep]
      linarith
    have hpt : ∀ s' : Fin n → Bool,
        K hist s s' * pathExp K m (s :: hist) s' (fun x ↦ ((occupiedCount x : ℕ) : ℝ))
          = a * K hist s s' + c * (K hist s s' * ((occupiedCount s' : ℕ) : ℝ)) := by
      intro s'
      rw [ih (s :: hist) s', hac]
      ring
    simp only [pathExp]
    rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hK1 hist s, mul_one, hone, Function.iterate_succ_apply,
      hac (meanStep n α β τ ((occupiedCount s : ℕ) : ℝ))]

/-- **The endpoint chord upper bound, DC (3.6) / PL (5.10).**

Every admissible coupling reports at most the chord value at the common mean count. Since
all admissible couplings share that mean, the synchronous all-coordinate coupling -- whose
count is supported on `{0, n}` -- attains this bound. -/
theorem pathExp_le_chord {n : ℕ} (α β τ : ℝ)
    (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK0 : ∀ hist s s', 0 ≤ K hist s s') (hK1 : ∀ hist s, ∑ s', K hist s s' = 1)
    (hflip : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool) (i : Fin n),
      ∑ s', (if s' i = s i then (0 : ℝ) else K hist s s')
        = τ * (if s i = true then α else β)) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1)) (m : ℕ)
    (hist : List (Fin n → Bool)) (s : Fin n → Bool) :
    (n : ℝ) * pathExp K m hist s (fun s' ↦ f ((occupiedCount s' : ℕ) : ℤ))
      ≤ ((n : ℝ) - (meanStep n α β τ)^[m] ((occupiedCount s : ℕ) : ℝ)) * f 0
        + ((meanStep n α β τ)^[m] ((occupiedCount s : ℕ) : ℝ)) * f ((n : ℤ)) := by
  have hpt : ∀ x : Fin n → Bool,
      (0 : ℝ) + (n : ℝ) * f ((occupiedCount x : ℕ) : ℤ)
        ≤ (n : ℝ) * f 0 + (f ((n : ℤ)) - f 0) * ((occupiedCount x : ℕ) : ℝ) := by
    intro x
    have hc := chord_bound n f hf (k := ((occupiedCount x : ℕ) : ℤ)) (by positivity)
      (by exact_mod_cast occupiedCount_le x)
    have hcast : (((((occupiedCount x : ℕ) : ℤ)) : ℝ)) = ((occupiedCount x : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast] at hc
    nlinarith [hc]
  have hmono := pathExp_mono K hK0 _ _ hpt m hist s
  rw [pathExp_affine K hK1 0 (n : ℝ) (fun x ↦ f ((occupiedCount x : ℕ) : ℤ)) m hist s,
    pathExp_affine K hK1 ((n : ℝ) * f 0) (f ((n : ℤ)) - f 0)
      (fun x ↦ ((occupiedCount x : ℕ) : ℝ)) m hist s,
    pathExp_count_mean α β τ K hK1 hflip m hist s] at hmono
  linarith

end

end Descent.Portability.ConvexOrderCoupling
