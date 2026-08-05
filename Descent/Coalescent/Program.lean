/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Split
import Descent.Coalescent.CutSets
import Descent.Coalescent.CutCount
import Descent.Coalescent.Path
import Descent.Coalescent.Trajectory
import Descent.Coalescent.Law
import Descent.Coalescent.HoldingTime
import Descent.Coalescent.Extend
import Descent.Coalescent.Ewens
import Descent.Coalescent.Mutation
import Descent.Coalescent.Kernel
import Mathlib.Tactic

namespace Descent

/-!
# What the coalescent group proves, and what it does not

This group formalises Kingman (1982), *The coalescent* (**K-C**) and *On the genealogy of
large populations* (**K-G**).  It does not formalise all of them.  This file is the record
of the difference, in the corpus rather than in a commit message, because an unrecorded gap
reads as a covered one.

## Settled, and where

* The rate ladder `d_k = k(k-1)/2` is a CARDINALITY of the state space, not a formula:
  `StateSpace.card_covers_eq_deathRate`.  K-C (1.6).
* The Wright-Fisher mechanism is explicit and the one-generation rates are counted off it
  within `(d_k/N)²/2`: `WrightFisher.coalescenceProb_le`, `.le_coalescenceProb`.  K-G (2.9).
* `hetRecurrence`, which the corpus previously posited, is that mechanism's pair-survival
  probability: `WrightFisher.hetRecurrence_eq_pairDistinct`.
* The jump chain is a Markov kernel on `𝓔ₙ` whose values are equivalence relations:
  `Kernel.jumpKernel`, `Process.jumpStep_apply_eq_jumpProb`.  K-C (2.2).
* Covers are merges from below and cuts from above: `StateSpace.covers_iff_exists_merge`,
  `Split.covers_iff_exists_splitBy`.
* Restriction is consistent, so sub-samples are coalescents: `Restriction.restrict_restrict`.
  K-G (7.2).
* Transit time, entrance boundary, absorption factor: `Rates`.  K-G (5.7)-(5.13), K-C p.239.
* Ewens (3.8) normalises at `n = 2, 3`: `Mutation.ewensProb_two_total`, `.ewensProb_three_total`.

## Open, and why

(Items 1 and 2 below are settled; they are kept in place with their proofs named.)

**1. The split count.**  SETTLED, by `CutCount.card_covers_below`:
`#{ξ ; ξ ≺ η} = Σ_c (2^{λ_c - 1} - 1)`.  The route was to stop dividing by two.
`Split.splitBy_compl` shows each cut is named twice; `CutSets` breaks the tie with each
class's canonical representative, so that a CUT SET -- a nonempty subset of one class
omitting its representative -- names each state exactly once
(`CutSets.splitBy_injective_on_cutSets`, `CutSets.exists_cutSet_of_covers`).  Counting cut
sets is then counting subsets (`CutCount.isCutSetOf_iff`, `CutCount.card_cutSetsOf`), and
`sum_choose_interior_eq_two_mul_cutCount` below checks the total against Kingman's
`Σ_ν ½C(λ,ν)`.

**2. Ewens normalisation for general `n`.**  SETTLED, by `Ewens.sum_ewensWeight`:
`Σ_{ξ ∈ 𝓔ₙ} θ^{|ξ|-1} ∏(λ_a - 1)! = (θ+1)⋯(θ+n-1)`, which is what makes K-G (3.8) a
probability distribution and what `Mutation` could previously only check at `n = 2, 3`.  The
proof is Kingman's restaurant: `Extend` gives the fibre of restriction over `ξ` as
`Option (Quotient ξ)`, `Ewens.sum_ER_succ` decomposes the sum by seating, and
`Ewens.sum_seatings_ewensWeight` values the seatings at `θ + n` -- `θ` for a new class,
`λ_c` for joining class `c`.  Listed here because it was open, and left listed because the
record of what a group had to build to close something is worth more than a tick.

**3. K-C Theorem 2, the paintbox representation.**  Every exchangeable random equivalence
relation is a mixture of paintboxes.  `Paintbox` builds the paintbox and proves the
construction equivariant, which is the direction that needs no probability.  The converse is
a de Finetti theorem proved through a reversed martingale convergence argument (K-C cites
Doob VII.4.25), and nothing in this corpus is close to it.

**4. K-C Theorem 1's real content: independence.**  The factorisation `R_t = ℛ_{D_t}` with
the jump chain independent of the death process is what makes the finite-dimensional
distributions computable.  `Coalescent.Path` now supplies the object this was blocked on:
the path of ONE trajectory, `pathState`, with `|R_t| = D(n,t)` (K-G (6.6),
`Path.blocks_pathState`), `R_0 = Δ`, absorption at the transit time, and monotone coarsening.
What is still missing is the LAW.  Taking the chain and the holds independent makes
independence true by construction -- that is Theorem 3's direction -- while Theorem 1's
direction, that an ARBITRARY `n`-coalescent factorises, needs the general theory of jump
chains for continuous-time Markov chains, which this corpus does not have.

**5. K-G section 6, the temporal coupling, and K-C Theorem 3, the infinite coalescent.**
The deterministic half of the temporal coupling is now `Coalescent.Path`: K-G (6.1)'s
`descentTime`, (6.2)'s death process as a step function, (6.5)'s `R_t = ℛ_{D(n,t)}` and
(6.6).  The estimate that lets the death process start from infinity --
`Σ_{r≥k} d_r⁻¹ = 2/(k-1)` -- is `Rates.hasSum_one_div_deathRate_tail`.  The discrete half of the measure is now `Coalescent.Trajectory`: `chainLaw` is a law on
whole TRAJECTORIES, and `Trajectory.chainLaw_support_chain'` is K-C (1.13) -- every
trajectory in its support is a descending chain of covers (repeating once absorbed, which is
`Kernel.jumpKernel_absorbing`'s convention).  `Coalescent.Law` then couples the trajectory to a clock: `coalescentLaw` is the product of
`chainLaw` with `m` independent copies of a holding-time law, and `coalescentLaw_prod` is
the independence K-G section 6 needs -- ARRANGED, not derived, which is exactly what
Theorem 3 does and exactly what Theorem 1 does not.  `Coalescent.HoldingTime` then supplies the clock: K-C (1.7)'s density `d_k e^{-d_k t}` is a
probability measure (`integral_holdDensity`, the one genuine integral in this group), so
`HoldingTime.coalescentLawExp` is the coupling with no parameter left open.  The mean `E(τ_r) = d_r⁻¹` of K-G (5.6) is proved too
(`HoldingTime.integral_id_mul_holdDensity`, a second integral against the same density,
rescaling to `Γ(2) = 1`), so `Rates.meanTransitTime_eq_two_sub` -- `E(T_n) = 2 - 2/n` -- now
runs from K-C (1.7)'s density rather than from a cited mean.  What is not done: the passage
to `n = ∞` that Theorem 3 needs on top of the finite construction.

None of the five is asserted anywhere in the group.  Where a result depends on one, the
dependence is a written hypothesis, not a hidden one.

## Main results

- `sum_choose_interior_add_two`: `Σ_{ν=1}^{λ-1} C(λ,ν) = 2^λ - 2`.
- `two_mul_cutCount_add_two`: so the cuts of a `λ`-class number `2^{λ-1} - 1`, which is the
  `½` in `½ C(λ, ν)` summed.
-/

namespace Coalescent

open Finset

/-- The interior binomial coefficients of row `λ` sum to `2^λ - 2`.  Stated additively to
keep it clear of truncated subtraction. -/
theorem sum_choose_interior_add_two {lam : ℕ} (h : 1 ≤ lam) :
    (∑ nu ∈ Finset.Ico 1 lam, lam.choose nu) + 2 = 2 ^ lam := by
  have hfull : ∑ nu ∈ Finset.range (lam + 1), lam.choose nu = 2 ^ lam :=
    Nat.sum_range_choose lam
  have hsplit : ∑ nu ∈ Finset.range (lam + 1), lam.choose nu
      = lam.choose 0 + ∑ nu ∈ Finset.Ico 1 (lam + 1), lam.choose nu := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  have htop : ∑ nu ∈ Finset.Ico 1 (lam + 1), lam.choose nu
      = (∑ nu ∈ Finset.Ico 1 lam, lam.choose nu) + lam.choose lam :=
    Finset.sum_Ico_succ_top h _
  rw [hsplit, htop, Nat.choose_zero_right, Nat.choose_self] at hfull
  omega

/-- The number of ways to cut a class of size `λ` into two nonempty pieces: `2^{λ-1} - 1`.
Each cut is named twice by the piece sizes -- once as `ν` and once as `λ - ν` -- which is
exactly Kingman's factor `½`, and `Split.splitBy_eq_iff` is the statement that those two
names give the same state. -/
theorem two_mul_cutCount_add_two {lam : ℕ} (h : 1 ≤ lam) :
    2 * (2 ^ (lam - 1) - 1) + 2 = 2 ^ lam := by
  obtain ⟨m, rfl⟩ : ∃ m, lam = m + 1 := ⟨lam - 1, by omega⟩
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  simp only [Nat.add_sub_cancel]
  omega

/-- **The two counts agree.**  Summing `½ C(λ, ν)` over the interior of row `λ` gives the
number of cuts of a `λ`-class.  This is the arithmetic half of open item 1: it says the
weight Kingman writes is the right weight, given that cuts and refining states correspond.
The correspondence itself is the half that is missing. -/
theorem sum_choose_interior_eq_two_mul_cutCount {lam : ℕ} (h : 1 ≤ lam) :
    ∑ nu ∈ Finset.Ico 1 lam, lam.choose nu = 2 * (2 ^ (lam - 1) - 1) := by
  have h1 := sum_choose_interior_add_two h
  have h2 := two_mul_cutCount_add_two h
  omega

/-- A class of size two has exactly one cut: into two singletons. -/
theorem cutCount_two : 2 ^ (2 - 1) - 1 = 1 := by norm_num

/-- A class of size three has three cuts, one for each element left alone. -/
theorem cutCount_three : 2 ^ (3 - 1) - 1 = 3 := by norm_num

end Coalescent

end Descent
