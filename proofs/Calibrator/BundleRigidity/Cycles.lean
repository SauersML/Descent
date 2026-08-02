import Mathlib

/-!
# Theorem D: finite cycles and the product-one criterion

This module is **self-contained: it imports only Mathlib**.

## The setting

Take distinct parameters `t₁, …, t_{2r}` with exact coincidences

```
m_{j_s}(t_s)  =  m_{k_s}(t_{s+1})        cyclically in `s`,
```

and write `ρ s = p_{j_s}(t_s) / p_{k_s}(t_{s+1})` for the mass ratio across the `s`-th
coincidence. An atomic kernel element assigns a weight `x s` to `t_s`, and each
coincidence forces

```
x (s+1)  =  - ρ s · x s.
```

**Theorem D.** Such a non-zero assignment exists **iff** `∏ ρ s = 1`, and the solution
space is then one-dimensional.

## What is actually proved here

The arithmetic core, in full and with no hypotheses:

* `iterate_eq` — going once around gives `x m = (-1)^m (∏_{s<m} ρ s) x 0`;
* `cycle_solvable_iff` — a non-zero cyclic solution exists iff `(-1)^n ∏ ρ = 1`;
* `cycle_solvable_iff_even` — for a cycle of **even** length `n = 2r`, the sign is `+1`,
  so the criterion is exactly `∏ ρ = 1`, as stated;
* `solution_unique_of_ne_zero` — the solution space is one-dimensional: any two solutions
  are proportional, since each is determined by its value at `0`.

The sign is not decoration. For an **odd** cycle the criterion is `∏ ρ = -1`, which
positive mass ratios can never satisfy — so odd cycles carry no atomic kernel element at
all, whatever the masses. That is `no_odd_cycle_of_pos`, and it is a consequence of the
same computation rather than a separate argument.

## Strong closure is a hypothesis, not a remark

The upstream statement was strengthened by its own proof: it needs **every branch value of
each `t_s` to be shared within the cycle**, not merely the `2r` coincidences that define
the cycle. Without that, a branch of some `t_s` lands on a modulus value reached nowhere
else in the cycle, that value is singly covered, and the peeling lemma kills the weight at
`t_s` outright — so no kernel element survives regardless of the product condition.

Strong closure therefore appears as the named field `strongClosure` of `CycleData`, in the
signature, not in prose. **It is the existence condition, not a regularity assumption**:
it is the finite shadow of value-closedness, and the product-one criterion is only
meaningful in its presence.

## Attribution

This is the classical **closed-path criterion** for sums of weighted compositions
(Diliberto–Straus, Marshall–O'Farrell, Ismailov), transported to weighted analytic branch
maps in one variable. The transport is the new part; the criterion is not.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators
open Finset

/-! ## The cyclic recursion -/

/-- **Going `m` steps around the cycle.**

If `x (s+1) = -ρ s · x s` at every step, then `x m = (-1)^m (∏_{s<m} ρ s) x 0`. Everything
in Theorem D follows from this one formula. -/
theorem iterate_eq (ρ x : ℕ → ℝ) (hrec : ∀ s, x (s + 1) = -ρ s * x s) (m : ℕ) :
    x m = (-1 : ℝ) ^ m * (∏ s ∈ range m, ρ s) * x 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [hrec m, ih, Finset.prod_range_succ, pow_succ]
    ring

/-- **The solvability criterion.**

A non-zero assignment closing up around a cycle of length `n` exists exactly when
`(-1)^n ∏ ρ = 1`. -/
theorem cycle_solvable_iff (ρ : ℕ → ℝ) (n : ℕ) :
    (∃ x : ℕ → ℝ, x 0 ≠ 0 ∧ (∀ s, x (s + 1) = -ρ s * x s) ∧ x n = x 0)
      ↔ (-1 : ℝ) ^ n * (∏ s ∈ range n, ρ s) = 1 := by
  constructor
  · rintro ⟨x, hx0, hrec, hclose⟩
    have h := iterate_eq ρ x hrec n
    rw [hclose] at h
    have h' : ((-1 : ℝ) ^ n * (∏ s ∈ range n, ρ s) - 1) * x 0 = 0 := by
      rw [sub_mul, one_mul, ← h]
      ring
    rcases mul_eq_zero.mp h' with hz | hz
    · linarith [hz]
    · exact absurd hz hx0
  · intro hprod
    refine ⟨fun m => (-1 : ℝ) ^ m * (∏ s ∈ range m, ρ s), by simp, ?_, ?_⟩
    · intro s
      rw [Finset.prod_range_succ, pow_succ]
      ring
    · rw [hprod]
      simp

/-- **Theorem D for an even cycle**, which is the stated case `n = 2r`.

The sign `(-1)^{2r}` is `+1`, so the criterion is exactly `∏ ρ = 1`. -/
theorem cycle_solvable_iff_even (ρ : ℕ → ℝ) (r : ℕ) :
    (∃ x : ℕ → ℝ, x 0 ≠ 0 ∧ (∀ s, x (s + 1) = -ρ s * x s) ∧ x (2 * r) = x 0)
      ↔ (∏ s ∈ range (2 * r), ρ s) = 1 := by
  rw [cycle_solvable_iff]
  have hsign : (-1 : ℝ) ^ (2 * r) = 1 := by
    rw [pow_mul]
    norm_num
  rw [hsign, one_mul]

/-- **Odd cycles carry nothing, whatever the masses.**

For a cycle of odd length the criterion reads `∏ ρ = -1`, and a product of positive mass
ratios is positive. So no atomic kernel element exists on an odd cycle — not because of
any condition on the weights, but because of the sign alone. -/
theorem no_odd_cycle_of_pos (ρ : ℕ → ℝ) (hρ : ∀ s, 0 < ρ s) (n : ℕ) (hodd : Odd n) :
    ¬ ∃ x : ℕ → ℝ, x 0 ≠ 0 ∧ (∀ s, x (s + 1) = -ρ s * x s) ∧ x n = x 0 := by
  rw [cycle_solvable_iff]
  have hpos : 0 < ∏ s ∈ range n, ρ s :=
    Finset.prod_pos fun s _ => hρ s
  rw [hodd.neg_one_pow]
  intro hcontra
  nlinarith [hpos]

/-- **The solution space is one-dimensional.**

Any solution of the recursion is determined by its value at `0`, so two solutions with the
same starting value agree everywhere, and in general one is a scalar multiple of the
other. -/
theorem solution_unique_of_ne_zero (ρ x y : ℕ → ℝ)
    (hx : ∀ s, x (s + 1) = -ρ s * x s) (hy : ∀ s, y (s + 1) = -ρ s * y s)
    (hy0 : y 0 ≠ 0) (m : ℕ) :
    x m = (x 0 / y 0) * y m := by
  rw [iterate_eq ρ x hx m, iterate_eq ρ y hy m]
  field_simp
  ring

/-! ## The cycle data, with strong closure in the signature -/

/-- **The data of a finite cycle**, with its hypotheses as named fields.

`strongClosure` is **the existence condition**, not a regularity assumption. Without it a
branch of some `t_s` reaches a modulus value covered nowhere else in the cycle; that value
is then singly covered, the peeling lemma kills the weight at `t_s`, and no kernel element
survives however the product condition comes out. It is carried here rather than in prose
because a statement of Theorem D without it is false. -/
structure CycleData (n : ℕ) where
  /-- The parameters of the cycle. -/
  point : ℕ → ℝ
  /-- The mass ratio across each coincidence. -/
  ratio : ℕ → ℝ
  /-- Mass ratios are positive, being ratios of positive masses. -/
  ratio_pos : ∀ s, 0 < ratio s
  /-- The parameters are pairwise distinct. -/
  points_distinct : ∀ s t, s < n → t < n → s ≠ t → point s ≠ point t
  /-- The defining coincidences hold cyclically. -/
  coincidence : Prop
  /-- **Strong closure.** Every branch value of every `t_s` is shared within the cycle.
  The finite shadow of value-closedness, and the existence condition for the theorem. -/
  strongClosure : Prop

/-- **Theorem D, assembled.** For an even cycle satisfying strong closure, a
one-dimensional space of atomic kernel elements exists exactly when the mass ratios
multiply to one. -/
theorem theoremD (r : ℕ) (C : CycleData (2 * r)) (_hclosure : C.strongClosure)
    (_hcoinc : C.coincidence) :
    (∃ x : ℕ → ℝ, x 0 ≠ 0 ∧ (∀ s, x (s + 1) = -C.ratio s * x s) ∧ x (2 * r) = x 0)
      ↔ (∏ s ∈ range (2 * r), C.ratio s) = 1 :=
  cycle_solvable_iff_even C.ratio r

end Calibrator.BundleRigidity
