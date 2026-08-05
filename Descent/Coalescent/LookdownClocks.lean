/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Lookdown
import Descent.Coalescent.CompetingRates
import Descent.Coalescent.StepLaw
import Descent.Coalescent.NeutralMutation
import Mathlib.Tactic

namespace Descent

/-!
# The clocks that drive the lookdown

`Descent.Coalescent.Lookdown` proves the level structure's consistency and records what it
does not supply: the clocks.  Donnelly and Kurtz drive the construction with one independent
rate-one Poisson process per pair of levels `i < j`; at a jump of the `(i,j)` process, level
`j` looks down at level `i`.  Without those clocks the lookdown is a consistent family of
maps and not a coalescent.

This file supplies them, from parts the corpus already has.  Three facts, all at the finest
state `Δ` where the blocks ARE the levels:

* the covers of `Δ` are the pairs of levels, and there are `C(n,2)` of them --
  `NeutralMutation.card_covers_delta`, which this file uses rather than restates;
* `C(n,2)` unit-rate clocks all survive to time `t` with probability `e^{-d_n t}`
  (`lookdown_survival`, an instance of `CompetingRates.prod_survival_covers`) -- so the wait
  until SOME pair looks down is exponential with the coalescent's rate;
* the density of "pair `p` looks down at time `t`" factorises as
  `jumpProb n · d_n e^{-d_n t}` (`lookdown_clock_factors`), the same first factor for every
  pair -- so which pair looks down is uniform and independent of when.

Those three are the Poisson clocks: independent unit-rate processes on the pairs, minimum
exponential at rate `d_n`, argmin uniform.  With `Lookdown`'s consistency they give the
`n`-coalescent's jump chain and holding law at every `n` simultaneously, on one space.

## What remains

One step, not the whole path.  `Descent.Coalescent.Law.coalescentLaw` couples a trajectory to
a clock for a whole path and `Descent.Coalescent.CompetingRates.pathDensity_factors` gives
the density version, so the path-level statement exists; what is not written is the
composition of THAT with `Lookdown`'s level maps, which would need the trajectory to be
indexed by pairs rather than by covers.  The arithmetic is the same and the bookkeeping is
not, and pretending otherwise is what a corpus like this exists to prevent.

## Main results

- `lookdown_survival`: **`C(n,2)` unit clocks survive with probability `e^{-d_n t}`**.
- `lookdown_clock_factors`: **the pair and the time are independent**, with the pair uniform.
- `lookdown_pair_prob`: each pair is chosen with probability `2/(n(n-1))`.
-/

namespace Coalescent

open scoped Classical

/-- **The clocks.**  One unit-rate clock per pair of levels; all of them survive to time `t`
with probability `e^{-d_n t}`, so the wait until some pair looks down is exponential at the
coalescent's own rate.  Nothing is assumed here beyond K-C (1.3)'s unit rates: the exponent
is the COUNT of pairs, `card_covers_eq_deathRate`. -/
theorem lookdown_survival (n : ℕ) (t : ℝ) :
    ∏ _p : {η : ER n // Covers (Delta n) η}, Real.exp (-t)
      = Real.exp (-(deathRate n * t)) := by
  have h := prod_survival_covers (Delta n) t
  rwa [blocks_bot n] at h

/-- **The pair and the time are independent, and the pair is uniform.**  The density of
"this pair looks down at time `t`" is `jumpProb n · d_n e^{-d_n t}`: a factor depending only
on which pair -- the same for every pair -- times a factor depending only on when.

That is the Poisson-clock statement in the form the lookdown needs, and it is
`CompetingRates.jointDensity_factors` read at the starting state. -/
theorem lookdown_clock_factors {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    Real.exp (-(deathRate n * t))
      = jumpProb n * (deathRate n * Real.exp (-(deathRate n * t))) :=
  jointDensity_factors hn t

/-- **Each pair of levels is chosen with probability `2/(n(n-1))`**, which is `1/C(n,2)`:
the uniform law on pairs, obtained from the clocks rather than imposed on them. -/
theorem lookdown_pair_prob {n : ℕ} (hn : 2 ≤ n) :
    jumpProb n = 2 / ((n : ℝ) * ((n : ℝ) - 1)) :=
  jumpProb_eq hn

/-- The `C(n,2)` pair probabilities sum to one, so the clocks define a distribution on pairs
and not merely a set of weights. -/
theorem lookdown_pair_prob_normalised {n : ℕ} (hn : 2 ≤ n) :
    ((n.choose 2 : ℕ) : ℝ) * jumpProb n = 1 := by
  have h := card_covers_mul_jumpProb (Delta n) (by rw [blocks_bot n]; exact hn)
  rwa [card_covers_delta n, blocks_bot n] at h

/-- **The clocks, assembled.**  At the starting state of an `n`-level lookdown: the wait is
exponential at rate `d_n`, the pair is uniform on the `C(n,2)` pairs, and the two are
independent.  With `Lookdown.lookdown_consistent` this is the Donnelly-Kurtz construction's
one-step law, at every `n` at once. -/
theorem lookdown_driven_by_pair_clocks {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    (∏ _p : {η : ER n // Covers (Delta n) η}, Real.exp (-t)
        = Real.exp (-(deathRate n * t)))
      ∧ (Real.exp (-(deathRate n * t))
        = jumpProb n * (deathRate n * Real.exp (-(deathRate n * t))))
      ∧ ((n.choose 2 : ℕ) : ℝ) * jumpProb n = 1 :=
  ⟨lookdown_survival n t, lookdown_clock_factors hn t, lookdown_pair_prob_normalised hn⟩

end Coalescent

end Descent
