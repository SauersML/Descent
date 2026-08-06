/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Trajectory
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# A law on the coalescent's path space

`Descent.Coalescent.Path` builds a coalescent path from a trajectory and a sequence of
holding times.  `Descent.Coalescent.Trajectory` gives the law of the trajectory.  This file
supplies the remaining ingredient for K-G section 6's temporal coupling at finite `n`: a law
on the PAIR, under which the jump chain and the holding times are independent.

The independence is not proved; it is arranged.  That is the honest description, and it is
also Kingman's: K-C Theorem 3 and K-G section 6 CONSTRUCT an `n`-coalescent by combining a
jump chain with an independent death process, and independence there is a property of the
construction.  K-C Theorem 1 is the converse -- that an arbitrary `n`-coalescent factorises
with independent factors -- and that is a different statement, still open here, needing the
general theory of jump chains for continuous-time Markov chains.

`Descent.Coalescent.Program` item 4 asks for Theorem 1 and item 5 for the constructions.
What lands here is item 5's direction, at finite `n`.  The holding-time law is an argument
rather than a fixed choice, which keeps what the coupling rests on visible in the signature;
`Descent.Coalescent.HoldingTime` supplies K-C (1.7)'s exponential and its integral, so
nothing is left open by the parametrisation.

## Main results

- `coalescentLaw`: the product law on trajectories × holding times.
- `coalescentLaw_isProbabilityMeasure`: it is a probability measure.
- `coalescentLaw_prod`: **independence, in the form it is arranged** -- the law of a
  rectangle factorises.
- `coalescentLaw_chain_marginal`: the trajectory marginal is `chainLaw`, so nothing about
  the jump chain was changed by coupling it to the clock.
- `coalescentLaw_finiteDimensional`: **K-C (2.5)**, the finite-dimensional distribution
  splits into a death-process factor and a jump-chain factor.
-/

namespace Coalescent

open MeasureTheory

/-- **The law of a coupled trajectory and clock.**  The jump chain's law, producted with `m`
independent copies of a holding-time law.

Empirical status: NOT AN EMPIRICAL CLAIM, and in particular the independence of the two
factors is BUILT IN rather than derived -- see the module docstring.  Kingman's Theorem 3
does the same; his Theorem 1, which derives it, is a different theorem and is not here. -/
noncomputable def coalescentLaw (n k m : ℕ) (holdLaw : Measure ℝ) :
    Measure (List (ER n) × (Fin m → ℝ)) :=
  (chainLaw n k).toMeasure.prod (Measure.pi fun _ : Fin m ↦ holdLaw)

instance coalescentLaw_isProbabilityMeasure (n k m : ℕ) (holdLaw : Measure ℝ)
    [IsProbabilityMeasure holdLaw] :
    IsProbabilityMeasure (coalescentLaw n k m holdLaw) := by
  unfold coalescentLaw
  haveI : IsProbabilityMeasure (chainLaw n k).toMeasure :=
    inferInstance
  infer_instance

/-- **Independence, in the form the construction arranges it.**  The law of a rectangle is
the product of the marginals: knowing the trajectory says nothing about the clock, and
conversely.  This is what K-G section 6 needs of the coupling, and it holds because the law
was built as a product. -/
theorem coalescentLaw_prod (n k m : ℕ) (holdLaw : Measure ℝ) [IsProbabilityMeasure holdLaw]
    (A : Set (List (ER n))) (B : Set (Fin m → ℝ)) :
    coalescentLaw n k m holdLaw (A ×ˢ B)
      = (chainLaw n k).toMeasure A * (Measure.pi fun _ : Fin m ↦ holdLaw) B := by
  haveI : IsProbabilityMeasure (chainLaw n k).toMeasure :=
    inferInstance
  unfold coalescentLaw
  exact Measure.prod_prod A B

/-- The trajectory marginal is the jump chain's own law: coupling it to a clock changed
nothing about it.  This is the compatibility K-C Theorem 1 asserts and this construction
supplies. -/
theorem coalescentLaw_chain_marginal (n k m : ℕ) (holdLaw : Measure ℝ)
    [IsProbabilityMeasure holdLaw] (A : Set (List (ER n))) :
    coalescentLaw n k m holdLaw (A ×ˢ Set.univ) = (chainLaw n k).toMeasure A := by
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin m ↦ holdLaw) := by infer_instance
  rw [coalescentLaw_prod, measure_univ, mul_one]

/-- The clock marginal, likewise. -/
theorem coalescentLaw_hold_marginal (n k m : ℕ) (holdLaw : Measure ℝ)
    [IsProbabilityMeasure holdLaw] (B : Set (Fin m → ℝ)) :
    coalescentLaw n k m holdLaw (Set.univ ×ˢ B)
      = (Measure.pi fun _ : Fin m ↦ holdLaw) B := by
  haveI : IsProbabilityMeasure (chainLaw n k).toMeasure :=
    inferInstance
  rw [coalescentLaw_prod, measure_univ, one_mul]

/-- **K-C (2.5): the finite-dimensional distribution factorises.**

`P{R_t = ξ} = P{D_t = k} · P{ℛ_k = ξ}`.  The event "the trajectory does `A` and the clock has
brought the count to `j` by time `t`" is a rectangle, because the first condition constrains
only the trajectory and the second only the clock.  Under the coupled law its probability is
the product -- which is what makes Kingman's factorisation a computation: the death process
supplies `P{D_t = k}` by convolving the holding times (K-C (2.6)) and the jump chain supplies
`P{ℛ_k = ξ}` by (2.3), and neither has to know about the other. -/
theorem coalescentLaw_finiteDimensional (n k m : ℕ) (holdLaw : Measure ℝ)
    [IsProbabilityMeasure holdLaw] (A : Set (List (ER n))) (t : ℝ) (j : ℕ) :
    coalescentLaw n k m holdLaw
        (A ×ˢ {h : Fin m → ℝ | blockCountAt n (extendHold h) t = j})
      = (chainLaw n k).toMeasure A
        * (Measure.pi fun _ : Fin m ↦ holdLaw) {h | blockCountAt n (extendHold h) t = j} :=
  coalescentLaw_prod n k m holdLaw A _

/-- **Almost every coupled path is a genuine coalescent path.**  Whatever the clock does,
the trajectory component is a descending chain of covers (`Trajectory.chainLaw_support_chain'`),
so `Path.pathState` applied to it is a path that starts at `Δ`, coarsens, and is absorbed --
which is what K-G (6.5) claims of the coupling. -/
theorem coalescentLaw_support_chain' (n k m : ℕ) (holdLaw : Measure ℝ)
    [IsProbabilityMeasure holdLaw] {p : List (ER n) × (Fin m → ℝ)}
    (hp : p.1 ∈ (chainLaw n k).support) :
    List.Chain' (fun y x ↦ Covers x y ∨ y = x) p.1 :=
  chainLaw_support_chain' k hp

end Coalescent

end Descent
