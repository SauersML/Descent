/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.CompetingRates
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# One step of the coalescent, as a law: where it goes and when, independently

`Descent.Coalescent.CompetingRates` shows the joint DENSITY of "which cover, at what time"
factorises -- `e^{-d_k t} = (1/d_k) · d_k e^{-d_k t}` -- and `pathDensity_factors` extends
that to every step.  `Descent.Coalescent.Program` item 4 then asked for the passage from a
factorised density to independent random objects.  For one step, that passage is here.

`stepLaw` is the joint law of the pair (destination, holding time): the uniform choice among
covers of `Descent.Coalescent.Process.jumpStep`, producted with K-C (1.7)'s clock at rate
`d_k` from `Descent.Coalescent.HoldingTime`.  `stepLaw_prod` is independence as a statement
about measures rather than densities -- the law of a rectangle is the product of the
marginals.

As in `Descent.Coalescent.Law`, the independence here is arranged rather than derived, and
that is Kingman's Theorem 3 direction.  What makes it more than a definition is that the
density it corresponds to is the one competing clocks actually produce
(`CompetingRates.jointDensity_factors`), so the arranged product is the right product and
not merely a convenient one.

## Main results

- `stepLaw`: the joint law of destination and holding time.
- `stepLaw_isProbabilityMeasure`: it is a probability measure.
- `stepLaw_prod`: **one-step independence, in measure** -- rectangles factorise.
- `stepLaw_destination_marginal`, `stepLaw_time_marginal`: and the marginals are the two
  laws it was built from, so nothing was distorted by coupling them.
-/

namespace Coalescent

open MeasureTheory

/-- **The joint law of one step: where the chain goes, and how long it waits.**

Empirical status: NOT AN EMPIRICAL CLAIM.  Both factors are forced -- the destination law by
K-C (1.3)'s unit rates through `card_covers`, the clock by K-C (1.7) -- and their
independence is arranged, as in K-C Theorem 3. -/
noncomputable def stepLaw {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) :
    Measure ({η : ER n // Covers ξ η} × ℝ) :=
  (jumpStep ξ hk).toMeasure.prod (holdMeasure (deathRate (blocks ξ)))

instance stepLaw_isProbabilityMeasure {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) :
    IsProbabilityMeasure (stepLaw ξ hk) := by
  haveI : IsProbabilityMeasure (holdMeasure (deathRate (blocks ξ))) :=
    holdMeasure_isProbabilityMeasure (deathRate_pos hk)
  haveI : IsProbabilityMeasure (jumpStep ξ hk).toMeasure :=
    inferInstance
  unfold stepLaw
  infer_instance

/-- **One-step independence, as a statement about measures.**  The chance of landing in `A`
and waiting a time in `B` is the product of the two chances: the destination says nothing
about the wait, and the wait says nothing about the destination.

`CompetingRates.jointDensity_factors` is the same fact at the level of densities; this is the
form that speaks about random objects rather than about functions. -/
theorem stepLaw_prod {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (A : Set {η : ER n // Covers ξ η}) (B : Set ℝ) :
    stepLaw ξ hk (A ×ˢ B)
      = (jumpStep ξ hk).toMeasure A * holdMeasure (deathRate (blocks ξ)) B := by
  haveI : IsProbabilityMeasure (holdMeasure (deathRate (blocks ξ))) :=
    holdMeasure_isProbabilityMeasure (deathRate_pos hk)
  haveI : IsProbabilityMeasure (jumpStep ξ hk).toMeasure :=
    inferInstance
  unfold stepLaw
  exact Measure.prod_prod A B

/-- The destination marginal is the uniform choice among covers: coupling it to a clock did
not change where the chain goes. -/
theorem stepLaw_destination_marginal {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (A : Set {η : ER n // Covers ξ η}) :
    stepLaw ξ hk (A ×ˢ Set.univ) = (jumpStep ξ hk).toMeasure A := by
  haveI : IsProbabilityMeasure (holdMeasure (deathRate (blocks ξ))) :=
    holdMeasure_isProbabilityMeasure (deathRate_pos hk)
  rw [stepLaw_prod, measure_univ, mul_one]

/-- The waiting-time marginal is K-C (1.7)'s clock, likewise. -/
theorem stepLaw_time_marginal {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) (B : Set ℝ) :
    stepLaw ξ hk (Set.univ ×ˢ B) = holdMeasure (deathRate (blocks ξ)) B := by
  haveI : IsProbabilityMeasure (jumpStep ξ hk).toMeasure :=
    inferInstance
  rw [stepLaw_prod, measure_univ, one_mul]

/-! ### `stepLaw_destination_uniform` is deleted

It claimed that every destination is equally likely whatever the clock does, and its
statement `((jumpStep ξ hk) η).toReal = jumpProb (blocks ξ)` named neither `stepLaw` nor
the clock: it was `Process.jumpStep_apply_eq_jumpProb` restated, word for word and proof
for proof, and `Kernel.jumpKernel_apply_cover` is the same restatement in a third module.
The uniformity of the destination under the coupled law is `stepLaw_destination_marginal`
composed with the parent theorem, and a reader who wants it should be sent to those two
rather than to a third name that hides which one is doing the work. -/

end Coalescent

end Descent
