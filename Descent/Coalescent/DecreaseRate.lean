/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.ComingDownCriterion
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# The multiple-merger correction: two rates, not one

`Descent.Coalescent.ThreeSeries` closes Schweinsberg's equivalence for a block count that
drops ONE level at a time, and `Descent.Coalescent.Program` records what that leaves: for a
`Λ`-coalescent several blocks can merge at once, and then the quantity in the criterion is
not the rate at which the count leaves a level.

There are two rates, and this file separates them.  `Lambda.totalRate` is the rate of
LEAVING level `b` -- one jump, whatever its size:

  `λ_b = Σ_k C(b,k) λ_{b,k}`.

Schweinsberg's `γ_b` is the expected rate of DECREASE, weighting each merger by the `k-1`
blocks it destroys:

  `γ_b = Σ_k (k-1) C(b,k) λ_{b,k}`.

The mean sojourn at level `b` is `λ_b⁻¹`, so the naive level-by-level argument -- the one
`ThreeSeries` makes rigorous -- proves coming down from `Σ λ_b⁻¹ < ∞`.  Schweinsberg's
condition is `Σ γ_b⁻¹ < ∞`, and `totalRate_le_decreaseRate` says why that is weaker: every
merger destroys at least one block, so `λ_b ≤ γ_b` and `γ_b⁻¹ ≤ λ_b⁻¹`.

  `Σ λ_b⁻¹ < ∞  ⟹  Σ γ_b⁻¹ < ∞`,   and not conversely.

`comesDownFromInfinity_of_summable_totalRate` is that implication.  So the corpus proves
coming down under a condition STRICTLY STRONGER than Schweinsberg's, and the gap between them
is exactly the levels a multiple merger skips: the count can fall from `b` to `b - k + 1` in
one jump, paying one sojourn instead of `k - 1` of them.  Closing it needs a comparison
argument on the process, not a sum over levels, and that is Schweinsberg's theorem --
NOW PROVED, in `Coalescent.SchweinsbergBound`.  The comparison turns out to be deterministic:
on the jump chain's mean-time recursion, the sojourn `λ_b⁻¹` a multiple merger fails to pay is
exactly recovered from the `k - 1` levels it skips, because `Σ_k (k-1) p_{b,k} = γ_b/λ_b` is
the definition of `γ_b` divided by `λ_b`.  The two cancel to an equality, giving
`h(b) ≤ Σ_{j=2}^b γ_j⁻¹`.

`decreaseRate_eq_totalRate_of_binary` is the other half of the picture: when only pairs
merge, the two rates coincide and there is nothing to correct.  Kingman is that case
(`kingman_rates_eq`), which is why everything else in this group is exact rather than
approximate.

## Main results

- `decreaseRate`: `γ_b = Σ_k (k-1) C(b,k) λ_{b,k}`, Schweinsberg's rate.
- `totalRate_le_decreaseRate`: **`λ_b ≤ γ_b`** -- every merger costs at least one block.
- `decreaseRate_eq_totalRate_of_binary`: with only pairwise mergers they agree.
- `kingman_rates_eq`: and Kingman is that case, both equal to `deathRate`.
- `comesDownFromInfinity_of_summable_totalRate`: **the corpus's condition implies
  Schweinsberg's**, and the gap is the skipped levels.
-/

namespace Coalescent

open Finset

/-- **Schweinsberg's rate.**  The expected rate at which the block count DECREASES: each
`k`-fold merger destroys `k - 1` blocks, and there are `C(b,k)` sets of `k` to merge.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a weighted sum of the family's rates; which
rates a population has is the empirical question, and `Descent.Blindness.MultipleMergerBlindness`
records which statistics could tell. -/
noncomputable def decreaseRate (lam : ℕ → ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 b, ((k : ℝ) - 1) * (b.choose k : ℝ) * lam b k

/-- **`λ_b ≤ γ_b`: every merger costs at least one block.**  Termwise, because `k - 1 ≥ 1`
for `k ≥ 2`.  This is the whole of the multiple-merger correction: the rate of leaving a
level is at most the rate of decreasing, and they differ by exactly the extra blocks a
multiple merger destroys. -/
theorem totalRate_le_decreaseRate {lam : ℕ → ℕ → ℝ} (hnn : ∀ b k, 0 ≤ lam b k) (b : ℕ) :
    totalRate lam b ≤ decreaseRate lam b := by
  unfold totalRate decreaseRate
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hcb : (0 : ℝ) ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ ((k : ℝ) - 1 - 1) * ((b.choose k : ℝ) * lam b k) :=
    mul_nonneg (by linarith) (mul_nonneg hcb (hnn b k))
  nlinarith [hprod]

/-- **With only pairwise mergers the two rates agree.**  Every surviving term has `k = 2`, so
the weight `k - 1` is one and the decrease rate is the jump rate.  There is nothing to
correct, which is why the binary treatment in `ThreeSeries` is exact where it applies. -/
theorem decreaseRate_eq_totalRate_of_binary {lam : ℕ → ℕ → ℝ} {b : ℕ}
    (hbin : ∀ k, 3 ≤ k → lam b k = 0) :
    decreaseRate lam b = totalRate lam b := by
  unfold decreaseRate totalRate
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  rcases eq_or_lt_of_le hk2 with h2 | h3
  · rw [← h2]
    norm_num
  · rw [hbin k h3, mul_zero, mul_zero]

/-- **Kingman is the binary case, and both rates are `deathRate`.** -/
theorem kingman_rates_eq {b : ℕ} (hb : 2 ≤ b) :
    decreaseRate kingmanRate b = deathRate b ∧ totalRate kingmanRate b = deathRate b := by
  have hbin : ∀ k, 3 ≤ k → kingmanRate b k = 0 := by
    intro k hk
    unfold kingmanRate
    rw [if_neg (by omega)]
  exact ⟨(decreaseRate_eq_totalRate_of_binary hbin).trans (totalRate_kingman hb),
    totalRate_kingman hb⟩

/-- **The corpus's condition implies Schweinsberg's.**  Summable reciprocal JUMP rates give
summable reciprocal DECREASE rates, because the jump rate is the smaller of the two.

So `ThreeSeries.ae_descent_dichotomy`, applied at `λ_b`, proves coming down under a condition
strictly stronger than Schweinsberg's.  The gap is the levels a multiple merger skips: a jump
from `b` to `b - k + 1` pays one sojourn where the level-by-level argument charges `k - 1`.
Closing it is a comparison on the process rather than a sum over levels. -/
theorem comesDownFromInfinity_of_summable_totalRate {lam : ℕ → ℕ → ℝ}
    (hnn : ∀ b k, 0 ≤ lam b k) (hpos : ∀ b, 0 < totalRate lam b)
    (h : comesDownFromInfinity (totalRate lam)) :
    comesDownFromInfinity (decreaseRate lam) := by
  unfold comesDownFromInfinity at h ⊢
  refine Summable.of_nonneg_of_le (fun b ↦ ?_) (fun b ↦ ?_) h
  · have hle := totalRate_le_decreaseRate hnn (b + 2)
    have hp := hpos (b + 2)
    have : 0 < decreaseRate lam (b + 2) := lt_of_lt_of_le hp hle
    positivity
  · have hle := totalRate_le_decreaseRate hnn (b + 2)
    have hp := hpos (b + 2)
    exact one_div_le_one_div_of_le hp hle

end Coalescent

end Descent
