/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SpatialCoalescent
import Descent.Coalescent.BertrandDescent
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# Pólya's criterion in one dimension, and what it decides for spatial lineages

`Descent.Coalescent.SpatialCoalescent` reduces the coalescence of two spatial lineages to a
hitting time: they meet exactly when their difference walk is at zero
(`meet_iff_difference_walk_zero`).  Whether that ever happens is a question about random
walks, and `Descent.Coalescent.Program` recorded it as the outstanding dependency.

Half of it is combinatorics, and that half is here.  A `±1` walk of length `2n` is a choice of
which steps go up, so there are `2^{2n} = 4^n` of them, and it is back at the origin exactly
when `n` of the steps went up -- `C(2n, n)` of them.  The counts ARE the probabilities, as
everywhere in this group:

  `P(S_{2n} = 0) = C(2n,n) / 4^n`.

Pólya's criterion says the walk is recurrent exactly when those sum to infinity, and in one
dimension they do.  Mathlib's `Nat.four_pow_lt_mul_centralBinom` gives `4^n < n · C(2n,n)`
for `n ≥ 4`, so the terms exceed `1/n`, and the harmonic series settles it
(`not_summable_returnProb`).

## What this closes and what it leaves

CLOSED: the counting -- `returnProb_eq_card_ratio` -- and the divergence.  The genealogical
consequence is then immediate and needs no probability at all: if the difference walk is ever
at zero, the lineages have met, which is `SpatialCoalescent.meet_iff_difference_walk_zero`
read forwards (`lineages_meet_of_difference_zero`).

LEFT: the renewal identity `Σ_n P(S_n = 0) = (1 - f)⁻¹` that turns the divergence into
`f = 1`, almost-sure return.  That needs the walk as a process with the strong Markov
property, which Mathlib does not have; it is a theorem about random walks, and no coalescent
paper proves it either -- they cite Pólya.  The corpus now cites him for exactly one step
rather than for the whole question.

## Main results

- `card_balancedPaths`: `C(2n,n)` step-sets of length `2n` return to the origin.
- `returnProb`, `returnProb_eq_card_ratio`: **`P(S_{2n} = 0) = C(2n,n)/4^n`**, counted.
- `returnProb_gt_one_div`: the terms exceed `1/n`, from Mathlib's central-binomial bound.
- `not_summable_returnProb`: **Pólya's criterion holds in one dimension**.
- `lineages_meet_of_difference_zero`: and a return is a coalescence.
-/

namespace Coalescent

open Finset

/-! ### Counting the returning paths -/

/-- The step-sets of a `±1` walk of length `2n` that end at the origin: those with exactly `n`
steps up.  There are `C(2n, n)` of them. -/
theorem card_balancedPaths (n : ℕ) :
    ((univ : Finset (Fin (2 * n))).powersetCard n).card = (2 * n).choose n := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- And `2^{2n} = 4^n` step-sets in all. -/
theorem card_allPaths (n : ℕ) :
    (Finset.univ : Finset (Finset (Fin (2 * n)))).card = 4 ^ n := by
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
    show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]

/-- **A walk of length `2n` ends at the origin exactly when `n` of its steps went up.**  The
displacement is `#up - #down = 2·#up - 2n`, so it vanishes precisely at `#up = n`. -/
theorem displacement_eq_zero_iff {n : ℕ} (up : Finset (Fin (2 * n))) :
    2 * (up.card : ℤ) - 2 * (n : ℤ) = 0 ↔ up.card = n := by
  constructor
  · intro h
    have : (up.card : ℤ) = (n : ℤ) := by linarith
    exact_mod_cast this
  · intro h
    rw [h]
    ring

/-- `P(S_{2n} = 0)`, the chance a `±1` walk is back at the origin after `2n` steps.

Empirical status: DERIVED, not posited -- `returnProb_eq_card_ratio` identifies it as the
number of returning step-sets over the number of step-sets, which is its probability under the
uniform law on step-sets, i.e. under independent fair steps. -/
noncomputable def returnProb (n : ℕ) : ℝ := ((2 * n).choose n : ℝ) / 4 ^ n

/-- **The count is the probability.** -/
theorem returnProb_eq_card_ratio (n : ℕ) :
    returnProb n
      = (((univ : Finset (Fin (2 * n))).powersetCard n).card : ℝ)
          / ((Finset.univ : Finset (Finset (Fin (2 * n)))).card : ℝ) := by
  rw [card_balancedPaths, card_allPaths]
  unfold returnProb
  push_cast
  ring

theorem returnProb_nonneg (n : ℕ) : 0 ≤ returnProb n := by
  unfold returnProb
  positivity

/-- **The terms exceed `1/n`.**  Mathlib's `4^n < n · C(2n,n)` for `n ≥ 4`, divided through.
This is the estimate that makes the one-dimensional walk recurrent: the return probabilities
decay, but only like `n^{-1/2}`, and their sum diverges. -/
theorem returnProb_gt_one_div {n : ℕ} (hn : 4 ≤ n) : 1 / (n : ℝ) < returnProb n := by
  have hb := Nat.four_pow_lt_mul_centralBinom n hn
  rw [Nat.centralBinom_eq_two_mul_choose] at hb
  have hbR : (4 : ℝ) ^ n < (n : ℝ) * ((2 * n).choose n : ℝ) := by exact_mod_cast hb
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  unfold returnProb
  rw [div_lt_div_iff₀ hnpos h4]
  linarith

/-- **Pólya's criterion, one dimension: the return probabilities are not summable.**

Hence the simple random walk on `ℤ` is recurrent.  `Coalescent.RenewalCriterion` supplies the
step from divergence to recurrence -- `polya_certain_return` -- so what was once a citation is
now a named hypothesis (the renewal identity) with the whole deduction around it proved.  This
theorem is the half that needs no probability: a count and the harmonic series. -/
theorem not_summable_returnProb : ¬ Summable returnProb := by
  intro hsum
  have hshift : Summable fun k : ℕ ↦ returnProb (k + 4) := (summable_nat_add_iff 4).mpr hsum
  have hcmp : ∀ k : ℕ, 1 / ((k : ℝ) + 4) ≤ returnProb (k + 4) := by
    intro k
    have h := returnProb_gt_one_div (n := k + 4) (by omega)
    have hcast : (((k + 4 : ℕ) : ℝ)) = (k : ℝ) + 4 := by push_cast; ring
    rw [hcast] at h
    exact le_of_lt h
  have hharm : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 4) :=
    Summable.of_nonneg_of_le (fun k ↦ by positivity) hcmp hshift
  have hbase : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := by
    refine (summable_nat_add_iff (f := fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) 3).mp ?_
    refine hharm.congr fun k ↦ ?_
    push_cast
    ring
  have hno := mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).mp
    Real.not_summable_one_div_natCast
  refine hno ?_
  refine hbase.congr fun k ↦ ?_
  push_cast
  ring

/-! ### What a return means for the genealogy -/

/-- **A return of the difference walk is a coalescence.**  The genealogical half of the
question needs no probability: `SpatialCoalescent.meet_iff_difference_walk_zero` already says
the two lineages are at the same site exactly when the difference walk is at zero, so any
statement about the walk's returns transfers verbatim.

The dependency on Pólya is therefore isolated to one implication -- "the difference walk
returns almost surely" -- and everything genealogical downstream of it is already proved. -/
theorem lineages_meet_of_difference_zero (x₀ y₀ : ℤ) (ξ η : ℕ → ℤ) (t : ℕ)
    (h : walk (x₀ - y₀) (fun s ↦ ξ s - η s) t = 0) :
    walk x₀ ξ t = walk y₀ η t :=
  (meet_iff_difference_walk_zero x₀ y₀ ξ η t).mpr h

end Coalescent

end Descent
