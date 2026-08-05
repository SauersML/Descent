/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.JumpChain
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace Descent

/-!
# The partition-valued step: the jump chain as an actual law on `𝓔ₙ`

`Descent.Coalescent.JumpChain` proves the arithmetic of Kingman's Theorem 1 -- the weight
`2/(k(k-1))` on each cover, and that the weights normalise.  This file turns that arithmetic
into an object: a probability mass function whose values are equivalence relations.

That is the thing the corpus did not have.  Merger rates were formalised as integrals,
coalescence times as real-valued summaries, drift as a scalar recurrence -- and all of them
are functions of a genealogy nobody had written down.  `jumpStep` writes it down: from a
state with `k ≥ 2` blocks, the chain moves to one of its `C(k,2)` covers, uniformly.

Two things make it more than a definition.  First, the state space it ranges over is
finite, and that is a theorem, not an instance declaration: `coversFintype` gets it from the
bijection with two-element sets of blocks proved in
`Descent.Coalescent.StateSpace.coverOfPair_bijective`.  Second, its value is Kingman's
(2.2): `jumpStep_apply` evaluates the mass on each cover as `1/C(k,2)`, which
`jumpStep_apply_eq_jumpProb` identifies with `2/(k(k-1))`.

What is NOT here: the continuous-time process.  Assembling `R_t = ℛ_{D_t}` from this jump
chain and an independent pure death process (K-C (2.1), K-G (6.5)) needs the death process
as a measure on paths, and that is not built.  The two halves of Kingman's factorisation
exist separately in this corpus -- the death process arithmetically in
`Descent.Coalescent.Rates`, the jump chain as a law here -- and their independence, which is
the content of Theorem 1, is not formalised.  Saying so is the point of saying it.

## Main results

- `coversFintype`: the covers of a state form a finite type.
- `card_covers_fintype`: there are `C(k,2)` of them, from `card_covers`.
- `jumpStep`: the partition-valued transition law.
- `jumpStep_apply_eq_jumpProb`: its value is K-C (2.2), `2/(k(k-1))`.
-/

namespace Coalescent

open scoped Classical

/-- The covers of a state form a finite type: they biject with the two-element subsets of
its block set.  This is `coverOfPair_bijective` cashed in as an instance rather than left as
a counting fact. -/
noncomputable instance coversFintype {n : ℕ} (ξ : ER n) : Fintype {η : ER n // Covers ξ η} := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  exact Fintype.ofEquiv {s : Finset (Quotient ξ) // s.card = 2}
    (Equiv.ofBijective _ (coverOfPair_bijective ξ))

theorem card_covers_fintype {n : ℕ} (ξ : ER n) :
    Fintype.card {η : ER n // Covers ξ η} = (blocks ξ).choose 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_covers ξ

/-- A state with at least two blocks has somewhere to go: pick two distinct blocks and merge
them.  Without this the jump chain would have no next state, which is exactly the absorbing
case `k = 1`. -/
theorem covers_nonempty {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) :
    Nonempty {η : ER n // Covers ξ η} := by
  classical
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  have hcard : 2 ≤ Fintype.card (Quotient ξ) := by
    rw [← Nat.card_eq_fintype_card]
    exact hk
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := Quotient ξ) (by omega)
  exact ⟨⟨merge ξ a b, merge_covers ξ hab⟩⟩

/-- **The partition-valued transition law of the `n`-coalescent's jump chain.**

From a state with `k ≥ 2` blocks, the chain merges a uniformly chosen pair of blocks.  The
values of this `PMF` are equivalence relations on the sample -- genealogies, not summaries of
them.

Empirical status: NOT AN EMPIRICAL CLAIM.  Uniformity is forced by K-C (1.3)'s unit rates
together with `card_covers`, not assumed: see `jumpStep_apply_eq_jumpProb`, which recovers
Kingman's `q_{ξη}/q_ξ`. -/
noncomputable def jumpStep {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) :
    PMF {η : ER n // Covers ξ η} :=
  letI := covers_nonempty ξ hk
  PMF.uniformOfFintype {η : ER n // Covers ξ η}

/-- Every cover gets the same mass, `1/C(k,2)`. -/
theorem jumpStep_apply {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (η : {η : ER n // Covers ξ η}) :
    jumpStep ξ hk η = (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ := by
  letI := covers_nonempty ξ hk
  rw [jumpStep, PMF.uniformOfFintype_apply, card_covers_fintype]

/-- **K-C (2.2), as a value of the law.**  The mass on each cover is `2/(k(k-1))`: the
`jumpProb` of `Descent.Coalescent.JumpChain`, which was introduced there as `q_{ξη}/q_ξ`.
The formula and the law agree. -/
theorem jumpStep_apply_eq_jumpProb {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (η : {η : ER n // Covers ξ η}) :
    (jumpStep ξ hk η).toReal = jumpProb (blocks ξ) := by
  have hd : deathRate (blocks ξ) ≠ 0 := deathRate_ne_zero hk
  have hchoose : ((blocks ξ).choose 2 : ℝ) = deathRate (blocks ξ) := by
    have := card_covers_eq_deathRate ξ
    rwa [card_covers] at this
  have hne : (((blocks ξ).choose 2 : ℕ) : ENNReal) ≠ 0 := by
    have hpos : 0 < ((blocks ξ).choose 2 : ℝ) := by
      rw [hchoose]
      exact deathRate_pos hk
    have : (blocks ξ).choose 2 ≠ 0 := by
      intro h
      rw [h] at hpos
      norm_num at hpos
    simpa using this
  rw [jumpStep_apply ξ hk η, ENNReal.toReal_inv, ENNReal.toReal_natCast, jumpProb, hchoose,
    one_div]

end Coalescent

end Descent
