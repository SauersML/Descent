/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Descent.Coalescent.BertrandDescent

namespace Descent

/-!
# What Schweinsberg's condition says about time

`Descent.Coalescent.ComingDownCriterion` states the condition `Σ γ_b⁻¹ < ∞` and decides it
for three named coalescents.  It does not say what the sum MEANS, and
`Descent.Coalescent.Program` recorded the equivalence -- condition iff coming down -- as open
because it is a theorem about a process the corpus has only at rate level.

Half of that equivalence is not about the process at all.  A block count that leaves level
`k` at rate `γ_k` spends mean time `γ_k⁻¹` there, so the mean time to descend from infinity
to level `b` is

  `Σ_{k > b} γ_k⁻¹`,

and the condition is exactly the statement that this is finite.  `meanDescentTime` is that sum,
`kingman_meanDescentTime` evaluates it at Kingman's ladder against `Rates` -- `2/(b-1)`, K-C
p.239 -- and `meanDescentTime_tendsto_atTop_of_not_comesDown` is the converse: when the condition
fails, the partial sums diverge, so there is no finite time by which the count is finite.

## What is proved, and what is not

PROVED: the condition is equivalent to the finiteness of the expected descent time, for a
block count that drops one level at a time at rate `γ_k`.  That covers Kingman exactly, and
covers any `Λ`-coalescent's binary part.

NOT PROVED: the almost-sure statement.  Going from "the expected descent time is finite" to
"the block count is finite at every positive time, almost surely" needs the process and a
Borel-Cantelli argument, exactly as `Descent.Coalescent.PolyaCriterion` needs the renewal
identity to turn a divergent series into an almost-sure return.  Both are the same shape of
gap: the corpus computes the series, and cites the probability theorem that reads it.

Nor is the multiple-merger correction proved: when several blocks can merge at once, `γ_b`
is the expected DECREASE rate rather than the rate of leaving level `b`, and the identity
between the sum and the mean descent time is an inequality.  That is Schweinsberg's actual
theorem and it is not here.

## Main results

- `meanDescentTime`: `Σ_{k ≥ b} γ_k⁻¹`, the mean time to come down to level `b`.
- `kingman_meanDescentTime`: **`2/(b-1)` for Kingman**, K-C p.239, from `Rates`.
- `comesDownFromInfinity_iff_summable_descent`: the condition is finiteness of that time.
- `meanDescentTime_tendsto_atTop_of_not_comesDown`: **and when it fails, the time is infinite**.
-/

namespace Coalescent

open Filter Topology

/-- The mean time for a block count to descend from infinity to level `b`, when it leaves
level `k` at rate `γ_k`: the sum of the mean sojourns.

Empirical status: DERIVED given the rates.  Each summand is the mean of an exponential of
rate `γ_k`, which `Descent.Coalescent.HoldingTime.integral_id_mul_holdDensity` computes from
K-C (1.7)'s density. -/
noncomputable def meanDescentTime (γ : ℕ → ℝ) (b : ℕ) : ℝ := ∑' j : ℕ, 1 / γ (b + j)

/-- **Kingman's descent time is `2/(b-1)`.**  K-C p.239, which `Rates` proves as a tail sum;
here it is read as the time to come down from infinity to `b` lineages. -/
theorem kingman_meanDescentTime {b : ℕ} (hb : 2 ≤ b) :
    meanDescentTime deathRate b = 2 / ((b : ℝ) - 1) :=
  tsum_one_div_deathRate_tail hb

/-- At `b = 2` it is `2`, the mean transit time of the whole coalescent -- the bound
`Rates.meanTransitTime_lt_two` proves uniform in the sample size, now read as a descent from
infinity rather than from a sample. -/
theorem kingman_meanDescentTime_two : meanDescentTime deathRate 2 = 2 := by
  rw [kingman_meanDescentTime (le_refl 2)]
  norm_num

/-- **The condition is the finiteness of the descent time.**  Definitionally: Schweinsberg's
`Σ γ_b⁻¹ < ∞` is the summability of the sojourn means, which is what makes `meanDescentTime` a
real number rather than a divergent sum. -/
theorem comesDownFromInfinity_iff_summable_descent (γ : ℕ → ℝ) :
    comesDownFromInfinity γ ↔ Summable fun j : ℕ ↦ 1 / γ (j + 2) :=
  Iff.rfl

/-- **And when the condition fails, the descent time is infinite.**  The partial sums of the
sojourn means tend to infinity, so no level is reached in bounded expected time.

This is the direction that makes the condition a dichotomy rather than a definition: a
coalescent failing it does not merely lack a proof of coming down, it has no finite expected
time in which to do so. -/
theorem meanDescentTime_tendsto_atTop_of_not_comesDown {γ : ℕ → ℝ}
    (hpos : ∀ j : ℕ, 0 < γ (j + 2)) (h : ¬ comesDownFromInfinity γ) :
    Tendsto (fun m : ℕ ↦ ∑ j ∈ Finset.range m, 1 / γ (j + 2)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact h
  · intro j
    exact le_of_lt (one_div_pos.mpr (hpos j))

/-- The star coalescent has no finite descent time: `γ_b = b - 1`, and the harmonic series
diverges.  `ComingDownCriterion.star_not_comesDownFromInfinity` supplies the failure. -/
theorem star_meanDescentTime_tendsto_atTop :
    Tendsto (fun m : ℕ ↦ ∑ j ∈ Finset.range m, 1 / ((((j + 2 : ℕ)) : ℝ) - 1)) atTop atTop :=
  meanDescentTime_tendsto_atTop_of_not_comesDown (γ := fun b : ℕ ↦ (b : ℝ) - 1)
    (fun j ↦ by push_cast; linarith) star_not_comesDownFromInfinity

/-- And neither has the Bolthausen-Sznitman coalescent, whose `γ_b = b(H_b - 1)` grows like
`b log b` -- `BertrandDescent.bolthausenSznitman_not_comesDownFromInfinity`. -/
theorem bolthausenSznitman_meanDescentTime_tendsto_atTop :
    Tendsto (fun m : ℕ ↦ ∑ j ∈ Finset.range m, 1 / bsRate (j + 2)) atTop atTop := by
  refine meanDescentTime_tendsto_atTop_of_not_comesDown (γ := bsRate) ?_ ?_
  · exact fun j ↦ bsRate_pos j
  · exact bolthausenSznitman_not_comesDownFromInfinity

end Coalescent

end Descent
