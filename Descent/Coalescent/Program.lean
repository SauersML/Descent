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
import Descent.Coalescent.Infinite
import Descent.Coalescent.Encoding
import Descent.Coalescent.CompetingRates
import Descent.Coalescent.PaintboxFrequency
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

## The five hard items, and where each stands

**1. The split count.**  SETTLED, `CutCount.card_covers_below`:
`#{ξ ; ξ ≺ η} = Σ_c (2^{λ_c - 1} - 1)`.  The route was to stop dividing by two.
`Split.splitBy_compl` shows each cut is named twice; `CutSets` breaks the tie with each
class's representative so a cut set names each state once; counting cut sets is then
counting subsets.  `sum_choose_interior_eq_two_mul_cutCount` below checks the total against
Kingman's `Σ_ν ½C(λ,ν)`.

**2. Ewens normalisation for general `n`.**  SETTLED, `Ewens.sum_ewensWeight`:
`Σ_{ξ ∈ 𝓔ₙ} θ^{|ξ|-1} ∏(λ_a - 1)! = (θ+1)⋯(θ+n-1)`, by the Chinese restaurant.  `Extend`
gives the fibre of restriction as `Option (Quotient ξ)`; seating multiplies the weight by
`θ` or by `λ_c`; `sum_classSize` turns the class sum into `n`.

**3. K-C Theorem 2, the paintbox representation.**  HALF SETTLED.  That a paintbox HAS
asymptotic frequencies, and that they are its own parameters, is
`PaintboxFrequency.tendsto_colourFrequency` -- K-C (3.8) by the strong law.  `Paintbox`
also proves the construction permutation-equivariant, which is the exchangeability that
needs no probability.  OPEN: the converse, that every exchangeable random equivalence
relation is a paintbox mixture.  K-C proves it by reversed martingale convergence (Doob
VII.4.25) and nothing in this corpus is close to it.

**4. K-C Theorem 1, independence of the jump chain and the death process.**  ONE STEP
SETTLED.  `CompetingRates`: unit rate on each cover makes the survivals multiply to
`e^{-d_k t}` (`prod_survival_covers`), and the joint density of "cover `η` at time `t`"
factorises as `(1/d_k) · d_k e^{-d_k t}` (`jointDensity_factors`), the same first factor for
every cover.  A density that splits is independence.  `Trajectory.chainLaw_head_blocks` adds
the structural reason it can hold at all: after `k` jumps the block count is `n - k` on every
trajectory, so the death process learns nothing from it.  The induction over steps is
`CompetingRates.pathDensity_factors`: the path's density is a product of one-step densities,
and a product of factorised terms factorises, so the whole path's density splits into a
trajectory factor and a clock factor.  OPEN: the passage from a factorised density to
independent random objects, which needs the continuous-time process.

**5. K-G section 6 and K-C Theorem 3, the constructions.**  FINITE `n` SETTLED.
`Trajectory.chainLaw` is a law on whole trajectories, with K-C (1.13) as
`chainLaw_support_chain'` and `chainLaw_head_eq_top`; `Path` turns a trajectory and holds
into `R_t = ℛ_{D(n,t)}` with `|R_t| = D(n,t)` (K-G (6.6)) and the death process pinned down
pathwise (`blockCountAt_eq`, K-C (2.6)); `Law` couples them; `HoldingTime` supplies K-C
(1.7)'s clock and proves both its integrals, so `E(T_n) = 2 - 2/n` runs from the density.
`Infinite` proves `𝓔` is the projective limit of the `𝓔ₙ` as a set, so specifying a process
by its restrictions is well posed.  `Encoding` supplies the measurable structure K-C
section 3 gets from viewing `𝓔` inside `2^{ℕ×ℕ}`: the embedding is injective, the σ-algebra
is the pullback, and every `ρ_n` is measurable -- so "the finite-dimensional distributions of
a process on `𝓔`" is now a well-formed phrase.  OPEN: the extension of a consistent family of
MEASURES to `n = ∞`, Theorem 3's Kakutani-Nelson step.  It is open for a stated reason -- a
theorem about measures -- rather than for want of a space to state it in.

Nothing above is asserted where it is open.  Where a result depends on an open item, the
dependence is a written hypothesis.

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
