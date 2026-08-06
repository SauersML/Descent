/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Coming down from infinity: `n(t) = 2/t`

`Descent.Coalescent.Rates` proves the summability that makes an infinite start legitimate:
`Σ_{r≥k} d_r⁻¹ = 2/(k-1)` (`tsum_one_div_deathRate_tail`, K-C p.239).  The mean time to
descend from infinitely many lineages to `k` of them is finite, so a coalescent started from
`∞` is in a finite state at every positive time.  That is an entrance boundary, and it is
where the corpus stopped.

It does not say HOW FAST.  With `n` lineages alive the coalescence rate is `d_n = n(n-1)/2`,
so the block count obeys, in the deterministic large-`n` approximation,

  `n'(t) = -n(t)²/2`,

and the solution that starts at infinity is `n(t) = 2/t` -- Aldous's descent curve.  This
file is that curve: `descentCurve_ode` verifies the equation through Mathlib's `deriv`, and
`descentCurve_at_entranceTime` checks the curve against the corpus's own exact means.

## The check that makes it worth stating

The curve is an approximation -- `d_n = n(n-1)/2` is replaced by `n²/2` -- so a formalisation
that merely wrote it down would be asserting a heuristic.  Instead it is tested against a
theorem the corpus proves exactly.  `Rates.tsum_one_div_deathRate_tail` says the mean time to
reach `k` lineages is `Σ_{r≥k} d_r⁻¹ = 2/(k-1)`.  Evaluate the curve there:

  `n(2/(k-1)) = k - 1`,

which is `descentCurve_at_entranceTime`.  The deterministic curve reproduces the EXACT mean
entrance times, displaced by exactly the one lineage that `n(n-1)` versus `n²` accounts for.
An approximation that is off by a constant factor would fail this; this one is off by the
single lineage its own derivation drops.

At `k = 2` the statement reads `n(2) = 1`: after the mean transit time `2` -- the bound
`Rates.meanTransitTime_lt_two` proves uniform in `n` -- one lineage remains.  The curve and
the transit time are the same fact.

## What it means

`descentCurve_unbounded` is the entrance from infinity itself: for any bound, there is a
positive time at which the curve is above it.  A sample of any size, however large, has
collapsed to a handful of lineages almost immediately -- the number of ancestors at time `t`
does not depend on the sample size at all once `t > 2/n`.

That is the strongest form of the corpus's recurring observation about sample size.
`Descent.Coalescent.BranchLength.height_bounded_length_unbounded` says the tree stops getting
deeper; this says it stops getting deeper IMMEDIATELY, and that everything a large sample
adds is added in the first instant of its history, on the terminal branches.

Not every coalescent does this.  `Descent.Coalescent.Lambda`'s family contains members that
never come down from infinity -- the Bolthausen-Sznitman coalescent among them -- and the
criterion separating them is a statement about `Λ` near zero.  Kingman's case is settled by
the summability `Rates` already has; the general criterion is not here.

## Main results

- `descentCurve`: `n(t) = 2/t`.
- `hasDerivAt_descentCurve`, `descentCurve_ode`: **`n' = -n²/2`**, through `deriv`.
- `descentCurve_two_div`: `n(2/x) = x`, the inversion the checks below use.
- `descentCurve_at_entranceTime`: **the curve at `Rates`'s exact mean entrance time is
  `k - 1`**.
- `descentCurve_two`: `n(2) = 1`, against `Rates.meanTransitTime_lt_two`.
- `descentCurve_unbounded`: the entrance from infinity.
-/

namespace Coalescent

/-! ### The curve -/

/-- Aldous's descent curve `n(t) = 2/t`: the deterministic number of ancestral lineages at
time `t` in a Kingman coalescent started from infinitely many.

Empirical status: DERIVED, with one approximation named.  It is the solution of
`n' = -n²/2`, and `n²/2` is `deathRate` with `n(n-1)` replaced by `n²`.  That replacement is
the only inexactness, and `descentCurve_at_entranceTime` measures it: the curve lands one
lineage below the exact mean entrance time's index, which is precisely the dropped `-n`. -/
noncomputable def descentCurve (t : ℝ) : ℝ := 2 / t

@[simp] theorem descentCurve_apply (t : ℝ) : descentCurve t = 2 / t := rfl

/-- The derivative of the descent curve, computed rather than quoted. -/
theorem hasDerivAt_descentCurve {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt descentCurve (-(2 / t ^ 2)) t := by
  have h : HasDerivAt (fun y : ℝ ↦ y⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht
  have h2 : HasDerivAt (fun y : ℝ ↦ 2 * y⁻¹) (2 * -(t ^ 2)⁻¹) t := h.const_mul 2
  have hfun : (fun y : ℝ ↦ 2 * y⁻¹) = descentCurve := by
    funext y
    unfold descentCurve
    rw [div_eq_mul_inv]
  rw [hfun] at h2
  have hval : 2 * -((t ^ 2)⁻¹) = -(2 / t ^ 2) := by
    rw [div_eq_mul_inv]
    ring
  rwa [hval] at h2

/-- **The descent equation: `n' = -n²/2`.**  With `n` lineages the coalescence rate is
quadratic in `n`, so the block count falls quadratically, and `2/t` is what solves that from
an infinite start.  The equation is verified against the actual derivative, not asserted. -/
theorem descentCurve_ode {t : ℝ} (ht : t ≠ 0) :
    deriv descentCurve t = -(descentCurve t ^ 2 / 2) := by
  have hsq : ((2 : ℝ) / t) ^ 2 / 2 = 2 / t ^ 2 := by
    rw [div_pow, div_div,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 ht) (by norm_num : (2 : ℝ) ≠ 0))
        (pow_ne_zero 2 ht)]
    ring
  rw [(hasDerivAt_descentCurve ht).deriv]
  unfold descentCurve
  rw [hsq]

/-! ### Inversion, and the checks against `Rates` -/

/-- `n(2/x) = x`: the curve inverted.  Every check below is an instance of this, which is why
it is stated once. -/
theorem descentCurve_two_div (x : ℝ) : descentCurve (2 / x) = x := by
  unfold descentCurve
  rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (by norm_num : (2 : ℝ) ≠ 0),
    mul_one]

/-- **The curve, evaluated at the corpus's exact mean entrance time, is `k - 1`.**

`Rates.tsum_one_div_deathRate_tail` proves that the mean time to come down from infinitely
many lineages to `k` is `Σ_{r≥k} d_r⁻¹ = 2/(k-1)`, exactly, with no approximation anywhere.
The descent curve at that time reads `k - 1`.

The displacement by one is not an error: the curve solves `n' = -n²/2` while the process has
rate `n(n-1)/2`, and the difference between `n²` and `n(n-1)` is exactly one lineage.  An
approximation wrong in its leading constant would land somewhere else entirely; this one
lands one lineage away, which is the discrepancy its own derivation predicts. -/
theorem descentCurve_at_entranceTime {k : ℕ} (hk : 2 ≤ k) :
    descentCurve (∑' j : ℕ, 1 / deathRate (k + j)) = (k : ℝ) - 1 := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hne : ((k : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith)
  rw [tsum_one_div_deathRate_tail hk]
  exact descentCurve_two_div _

/-- **`n(2) = 1`.**  The mean transit time of the whole coalescent is `2` -- the bound
`Rates.meanTransitTime_lt_two` proves uniform in the sample size -- and the descent curve says
that at time `2` there is one lineage left.  The two developments agree at the point where
both are exact. -/
@[simp] theorem descentCurve_two : descentCurve 2 = 1 := by
  unfold descentCurve
  norm_num

/-- The curve is positive wherever time is. -/
theorem descentCurve_pos {t : ℝ} (ht : 0 < t) : 0 < descentCurve t := by
  unfold descentCurve
  exact div_pos (by norm_num) ht

/-- **The entrance from infinity.**  For any bound there is a positive time at which more
than that many lineages are alive: the curve leaves every level as `t` approaches the
present.  This is the content of "the coalescent comes down from infinity" -- not that the
process starts anywhere in particular, but that no finite state is where it started. -/
theorem descentCurve_unbounded (B : ℝ) : ∃ t : ℝ, 0 < t ∧ B < descentCurve t := by
  have hpos : (0 : ℝ) < |B| + 1 := by positivity
  refine ⟨2 / (|B| + 1), by positivity, ?_⟩
  rw [descentCurve_two_div]
  have := le_abs_self B
  linarith

/-- And it is spent almost immediately: halving the time doubles the lineage count, so all
but a bounded number of a large sample's coalescences happen in an initial window that
shrinks as the sample grows.  Stated as the scaling identity, which is the whole of it. -/
theorem descentCurve_halving (t : ℝ) :
    descentCurve (t / 2) = 2 * descentCurve t := by
  unfold descentCurve
  rw [div_div_eq_mul_div, mul_div_assoc]

end Coalescent

end Descent
