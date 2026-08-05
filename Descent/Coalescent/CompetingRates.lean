/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.HoldingTime
import Descent.Coalescent.Process
import Mathlib.Tactic

namespace Descent

/-!
# Competing clocks: why the jump chain and the holding time are independent

K-C Theorem 1 says the death process and the jump chain of an `n`-coalescent are
independent.  `Descent.Coalescent.Law` arranges independence by building a product; this
file gives the reason it is true of the coalescent itself, at the level of one step, where
it is an algebraic identity rather than a construction.

The mechanism is competing exponential clocks.  K-C (1.3) puts rate `1` on each cover of the
current state; equivalently, each of the `C(k,2)` available mergers carries an independent
unit-rate clock, and the chain takes whichever rings first.  Then

* the first ring happens at rate `d_k`, because the clocks' survival probabilities multiply:
  `∏_{covers} e^{-t} = e^{-d_k t}` (`prod_survival_covers`), using
  `StateSpace.card_covers_eq_deathRate` to turn the number of covers into the rate;
* the joint density of "cover `η` rings, at time `t`" is `e^{-d_k t}`, the same for every
  cover, and it factorises as `(1/d_k) · d_k e^{-d_k t}` -- the uniform choice of
  `Process.jumpStep` times the holding density of `HoldingTime` (`jointDensity_factors`).

A joint density that factorises into a function of the state times a function of the time IS
independence.  So the one-step statement of K-C Theorem 1 is here, and what is missing for
the full theorem is the induction over steps and the passage from densities to the joint law
of the whole path -- which needs the continuous-time process the corpus does not have.

## Main results

- `prod_survival_covers`: competing unit-rate clocks on the covers survive at rate `d_k`.
- `jointDensity_factors`: the joint density splits into `jumpProb × holding density`.
- `jointDensity_indep_of_cover`: and the split does not depend on which cover -- the two
  halves of independence.
-/

namespace Coalescent

open scoped Classical

/-- **Competing unit-rate clocks ring at rate `d_k`.**  One clock per cover, each surviving
to time `t` with probability `e^{-t}`; all surviving is `e^{-d_k t}`, because the number of
covers is `d_k` (`card_covers_eq_deathRate`).  This is K-C (1.5)-(1.6) in survival form: the
total rate out of a state is the sum of the rates on its transitions. -/
theorem prod_survival_covers {n : ℕ} (ξ : ER n) (t : ℝ) :
    ∏ _η : {η : ER n // Covers ξ η}, Real.exp (-t)
      = Real.exp (-(deathRate (blocks ξ) * t)) := by
  classical
  rw [Finset.prod_const, Finset.card_univ]
  rw [← Real.exp_nat_mul]
  congr 1
  have hcard : (Fintype.card {η : ER n // Covers ξ η} : ℝ) = deathRate (blocks ξ) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_covers_eq_deathRate ξ
  rw [hcard]
  ring

/-- **The joint density factorises.**  The density of "the chain jumps to the cover `η` at
time `t`" is `e^{-d_k t}` -- one clock rings, the rest have not -- and that is exactly
`jumpProb k` times the holding density `d_k e^{-d_k t}`.

A density that splits into a function of the state times a function of the time is
independence, so this is K-C Theorem 1 for a single step. -/
theorem jointDensity_factors {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    Real.exp (-(deathRate k * t))
      = jumpProb k * (deathRate k * Real.exp (-(deathRate k * t))) := by
  have hd : deathRate k ≠ 0 := deathRate_ne_zero hk
  unfold jumpProb
  field_simp

/-- **And the factorisation is the same for every cover.**  The state-dependent factor is
`1/d_k` whichever cover is taken, which is the other half of independence: the time tells
you nothing about the destination.  It is also why the jump chain is uniform on covers
(`Process.jumpStep_apply_eq_jumpProb`) -- the two facts are the same computation. -/
theorem jointDensity_indep_of_cover {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (η η' : {η : ER n // Covers ξ η}) (t : ℝ) :
    (jumpStep ξ hk η).toReal * (deathRate (blocks ξ) * Real.exp (-(deathRate (blocks ξ) * t)))
      = (jumpStep ξ hk η').toReal
        * (deathRate (blocks ξ) * Real.exp (-(deathRate (blocks ξ) * t))) := by
  rw [jumpStep_apply_eq_jumpProb ξ hk η, jumpStep_apply_eq_jumpProb ξ hk η']

/-! ### All the steps at once

`jointDensity_factors` splits one step.  Kingman's Theorem 1 is about the whole path, and
the passage from one step to all of them is a product identity: a product of factorised
terms factorises. -/

/-- **The whole path's density factorises.**  Along a trajectory visiting block counts
`K 0, K 1, …` with holding times `t 0, t 1, …`, the joint density is a product of one-step
densities, and it splits into a factor depending only on the trajectory and a factor
depending only on the clock.

That is K-C Theorem 1's independence at the level of densities, for every step rather than
one -- the induction the one-step case needed.  What it is not is a statement about
measures; turning a factorised density into independent random objects needs the
continuous-time process, which `Descent.Coalescent.Program` still lists. -/
theorem pathDensity_factors (K : ℕ → ℕ) (t : ℕ → ℝ) (m : ℕ) :
    ∏ i ∈ Finset.range m,
        (jumpProb (K i) * (deathRate (K i) * Real.exp (-(deathRate (K i) * t i))))
      = (∏ i ∈ Finset.range m, jumpProb (K i))
        * ∏ i ∈ Finset.range m, (deathRate (K i) * Real.exp (-(deathRate (K i) * t i))) :=
  Finset.prod_mul_distrib

/-- **And the density being factorised is the one the competing clocks give.**  Each step's
density is `e^{-d_k t}` -- one clock rings, the others have not -- so the path density is
`∏ e^{-d_{K i} t_i}`, and `pathDensity_factors` splits exactly that. -/
theorem pathDensity_eq_prod_exp {K : ℕ → ℕ} (hK : ∀ i, 2 ≤ K i) (t : ℕ → ℝ) (m : ℕ) :
    ∏ i ∈ Finset.range m, Real.exp (-(deathRate (K i) * t i))
      = ∏ i ∈ Finset.range m,
          (jumpProb (K i) * (deathRate (K i) * Real.exp (-(deathRate (K i) * t i)))) :=
  Finset.prod_congr rfl fun i _ ↦ jointDensity_factors (hK i) (t i)

/-- The trajectory factor, written out: the probability of a given sequence of choices is the
product of the uniform weights, and it carries no dependence on the clock at all. -/
theorem pathDensity_chain_factor {K : ℕ → ℕ} (hK : ∀ i, 2 ≤ K i) (m : ℕ) :
    ∏ i ∈ Finset.range m, jumpProb (K i)
      = ∏ i ∈ Finset.range m, 2 / ((K i : ℝ) * ((K i : ℝ) - 1)) :=
  Finset.prod_congr rfl fun i _ ↦ jumpProb_eq (hK i)

/-- The total density over all covers is the holding density: nothing leaks.  This is the
consistency check that the factorisation is a probability statement and not just an
algebraic identity -- summing the joint density over destinations returns the marginal in
time. -/
theorem sum_jointDensity {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) (t : ℝ) :
    ∑ _η : {η : ER n // Covers ξ η}, Real.exp (-(deathRate (blocks ξ) * t))
      = deathRate (blocks ξ) * Real.exp (-(deathRate (blocks ξ) * t)) := by
  classical
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card {η : ER n // Covers ξ η} : ℝ) = deathRate (blocks ξ) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_covers_eq_deathRate ξ
  rw [hcard]

end Coalescent

end Descent
