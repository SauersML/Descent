/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

namespace Descent.Blindness

open scoped BigOperators

/-!
# An exchange rate between covariance-indistinguishable demes is not identifiable

Self-contained: imports only Mathlib.

`Descent.Spectral.ErgodicCovariancePencil` builds source and target covariance operators as two time
slices of one stationary field, which raises the identification question: given the observable
covariance process, which parameters of the underlying demography are recoverable?
`Descent.Blindness.HiddenConeAmbiguity` answers the abstract version — the gauge freedom is large and
carried by the unbounded-distortion escape rather than by a wild symmetry. This is the finite
instance, and it is stronger than a stability statement.

Three demes. Demes `1` and `2` carry the same covariance signature; deme `0` differs. Gene flow is
symmetric at rate `a` between the hub `0` and each of `1`, `2`, and at rate `b` directly between
`1` and `2`. Every observable is a function of the covariance signature, hence takes the same
value on `1` and `2` — a lumped function. Two facts:

* `lumped_closed_under_generator`: lumped functions are closed under the generator, so the
  observable process is itself Markov;
* `lumped_generator_blind_to_exchange`: on lumped functions the two generators are equal as
  functions, for any pair of exchange rates.

`lumped_dynamics_blind_to_exchange` iterates the second through the first, so every generator
iterate — hence every generator-polynomial observable, not just the two-point ones — is
independent of `b`. Passing from that to complete path laws is the standard matrix-exponential
argument and is not packaged here. `hubDrift_has_no_exchange_rate` gives the mechanism: flow out
of the hub is `2a(f₁ - f₀)` and never touches the leaf-to-leaf channel.

So the direct migration rate between two populations sharing a covariance signature is not poorly
estimated; it is not estimated at this order. This is the
`Descent.Conditionals.DeclaredInteractionClass` dichotomy in demography: the
identified set is the full fibre, and the only repair is a declaration fixing `b` from outside the
data. Three consequences:

1. A fit reporting this rate is reporting its prior — the likelihood is flat along that
   coordinate, so the number came from the parameterisation, the penalty or the starting point.
2. The blindness is exact, so it is testable: a method returning different values of `b` for
   datasets with the same observable law is defective, detectably and without new data.
3. It is symmetry, not degeneracy. The invisible direction is the antisymmetric mode of the two
   lumped demes. Distinguishability returns with any observable separating them — one
   differentiating marker, one differing exposure — so the measurement to spend is on breaking
   the lumping, not on more samples under it.

Scope: proved here are closure of the lumped class, exact `b`-independence on it, propagation to
every iterate, and the hub identity. Whether a given pair of human populations is lumpable at the
resolution of the observable is not asserted; per point 3 it is measurable.

Empirical status: DERIVED. The unidentifiability is proved for the stated family; its bearing on a
study depends on how nearly two populations share a covariance signature.
-/

/-- Symmetric gene-flow rates on three demes: `a` between the hub `0` and each leaf, and `b`
directly between the two leaves. -/
def demeRate (a b : ℝ) (i j : Fin 3) : ℝ :=
  if i = j then 0 else if i = 0 ∨ j = 0 then a else b

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem demeRate_at_reference_point (a b : ℝ) :
    demeRate a b 0 0 = 0 ∧ demeRate a b 0 1 = a ∧ demeRate a b 1 2 = b := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [demeRate]


/-- Action of a rate matrix on a function of the state. -/
def generatorApply (q : Fin 3 → Fin 3 → ℝ) (f : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j, q i j * (f j - f i)

/-- A function of the state that cannot separate the two covariance-indistinguishable demes. -/
def Lumped (f : Fin 3 → ℝ) : Prop := f 1 = f 2

/-- The observable class is closed under the dynamics, so the observable process is Markov in its
own right and the blindness below cannot be evaded by iterating. -/
theorem lumped_closed_under_generator (a b : ℝ) (f : Fin 3 → ℝ) (hf : Lumped f) :
    Lumped (generatorApply (demeRate a b) f) := by
  unfold Lumped at hf ⊢
  simp [generatorApply, demeRate, Fin.sum_univ_three, hf]

/-- On the observable class the two generators are equal as functions, for any pair of
leaf-to-leaf rates. -/
theorem lumped_generator_blind_to_exchange (a b b' : ℝ) (f : Fin 3 → ℝ) (hf : Lumped f) :
    generatorApply (demeRate a b) f = generatorApply (demeRate a b') f := by
  unfold Lumped at hf
  funext i
  fin_cases i <;>
    simp [generatorApply, demeRate, Fin.sum_univ_three, hf]

/-- The flow out of the hub is `2a(f₁ - f₀)`: the leaf-to-leaf channel never enters it. -/
theorem hubDrift_has_no_exchange_rate (a b : ℝ) (f : Fin 3 → ℝ) (hf : Lumped f) :
    generatorApply (demeRate a b) f 0 = 2 * a * (f 1 - f 0) := by
  unfold Lumped at hf
  simp [generatorApply, demeRate, Fin.sum_univ_three, hf]
  ring

/-- Iterated action of the generator: the observable process at every order. -/
def generatorIter (q : Fin 3 → Fin 3 → ℝ) (f : Fin 3 → ℝ) : ℕ → (Fin 3 → ℝ)
  | 0 => f
  | n + 1 => generatorApply q (generatorIter q f n)

/-- Every generator iterate of the observable dynamics is blind to the exchange rate.

    This proves equality of all generator-polynomial observables.  It does not package the
    separate matrix-exponential argument identifying complete path laws. -/
theorem lumped_dynamics_blind_to_exchange (a b b' : ℝ) (f : Fin 3 → ℝ) (hf : Lumped f) :
    ∀ n, generatorIter (demeRate a b) f n = generatorIter (demeRate a b') f n := by
  have key : ∀ n, generatorIter (demeRate a b) f n = generatorIter (demeRate a b') f n ∧
      Lumped (generatorIter (demeRate a b) f n) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, hf⟩
    | succ n ih =>
      obtain ⟨heq, hlump⟩ := ih
      refine ⟨?_, ?_⟩
      · show generatorApply (demeRate a b) (generatorIter (demeRate a b) f n)
            = generatorApply (demeRate a b') (generatorIter (demeRate a b') f n)
        rw [← heq]
        exact lumped_generator_blind_to_exchange a b b' _ hlump
      · exact lumped_closed_under_generator a b _ hlump
  exact fun n ↦ (key n).1

end Descent.Blindness
