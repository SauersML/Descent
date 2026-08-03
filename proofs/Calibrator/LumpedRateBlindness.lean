import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators

/-!
# An exchange rate between covariance-indistinguishable demes is not identifiable

This module is **self-contained: it imports only Mathlib.**

`Calibrator.ErgodicCovariancePencil` builds source and target covariance operators as two time
slices of one stationary field, and its biological reading makes the coupling time a separation
between two populations or sampling epochs. That raises the identification question the pencil
program cannot avoid: **given the observable covariance process, which parameters of the
underlying demography are recoverable?** `Calibrator.HiddenConeAmbiguity` answers the abstract
version — the gauge freedom is large, and carried by the unbounded-distortion escape rather than
by a wild symmetry. This module gives the finite, fully explicit instance, and it is worse than a
stability problem.

## The witness

Three demes. Demes `1` and `2` carry the **same** covariance signature; deme `0` differs. Gene
flow is symmetric at rate `a` between the hub `0` and each of `1`, `2`, and at rate `b` directly
between `1` and `2`.

Every observable is a function of the covariance signature, hence a function on the state space
that takes the same value on `1` and `2` — a *lumped* function. Two facts, both proved below:

* `lumped_closed_under_generator`: lumped functions are closed under the generator. So the
  observable process is itself Markov, with its own two-state generator.
* `lumped_generator_blind_to_exchange`: on lumped functions the generator **does not depend on
  `b`**. Not weakly, not to leading order: the two generators are equal as functions.

`lumped_dynamics_blind_to_exchange` iterates the second through the first, so every
generator-polynomial observable is independent of `b`. `hubDrift_has_no_exchange_rate` records
the mechanism in one line: the flow out of the hub is `2a(f₁ - f₀)` and never sees the
leaf-to-leaf channel at all. Equality of the resulting finite-state semigroups follows by the
matrix exponential, but that analytic bridge is not exported as a theorem here.

## What this means

Within the generator-polynomial observation class, the direct migration rate between two
populations that share a covariance signature is **not identified**: every observable proved
here is literally identical across the whole family of `b`. This is the
`Calibrator.DeclaredInteractionClass`
dichotomy arriving in demography: the identified set is the full fibre, and the only repair is a
declaration — an assumption, made in advance and recorded, that fixes `b` from outside the data.

Three consequences worth separating:

1. **A demographic fit that reports this rate is reporting its prior.** The likelihood is flat
   along that coordinate; whatever number comes out was put in by the parameterisation, the
   penalty or the optimiser's starting point.
2. **The blindness is exact, so it is also a test.** If a method returns different values of `b`
   for datasets whose observable laws agree, that is a defect of the method and detectable
   without new data.
3. **It is symmetry, not degeneracy.** The invisible direction is the antisymmetric mode of the
   two lumped demes, an exact eigenvector of the generator whose eigenvalue is the only thing `b`
   moves. Distinguishability is therefore recovered by *any* observable separating demes `1` and
   `2` — one differentiating marker, one differing environmental exposure. The design implication
   is concrete: **spend the measurement on breaking the lumping, not on more samples under it.**

## Scope

Proved here: closure of the lumped class, exact `b`-independence of the generator on it, its
propagation to every iterate, and the hub identity. Not asserted here: that a specific human
demography is lumpable at any specific pair of populations. Lumping is the hypothesis under which
the blindness bites, and whether it holds is measurable — that is point 3 above.

Empirical status: DERIVED. The unidentifiability is proved for the stated family; its bearing on a
real study depends on how nearly two populations share a covariance signature, which is an
empirical quantity this result asks to be reported rather than assumed away.
-/

/-- Symmetric gene-flow rates on three demes: `a` between the hub `0` and each leaf, and `b`
directly between the two leaves. -/
def demeRate (a b : ℝ) (i j : Fin 3) : ℝ :=
  if i = j then 0 else if i = 0 ∨ j = 0 then a else b

/-- Action of a rate matrix on a function of the state. -/
def generatorApply (q : Fin 3 → Fin 3 → ℝ) (f : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j, q i j * (f j - f i)

/-- A function of the state that cannot separate the two covariance-indistinguishable demes. -/
def Lumped (f : Fin 3 → ℝ) : Prop := f 1 = f 2

/-- **The observable class is closed under the dynamics**, so the observable process is Markov in
its own right and the blindness below cannot be evaded by iterating. -/
theorem lumped_closed_under_generator (a b : ℝ) (f : Fin 3 → ℝ) (hf : Lumped f) :
    Lumped (generatorApply (demeRate a b) f) := by
  unfold Lumped at hf ⊢
  simp [generatorApply, demeRate, Fin.sum_univ_three, hf]

/-- **The exchange rate is invisible.** On the observable class the two generators are equal as
functions, for any pair of leaf-to-leaf rates. -/
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

/-- **Every generator iterate of the observable dynamics is blind to the exchange rate.**

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
  exact fun n => (key n).1

end Calibrator
