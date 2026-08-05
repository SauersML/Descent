/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace Descent

/-!
# Moment duality: the forward diffusion and the backward coalescent are one calculation

Population genetics has two descriptions of the same neutral population and they run in
opposite directions.  Forwards, the frequency `X_t` of an allele is a Wright-Fisher
diffusion, with generator

  `L f(x) = ½ x(1-x) f''(x)`

on `[0,1]`.  Backwards, a sample of `n` has a genealogy in which pairs merge at rate `1`, so
the number of ancestral lineages is a pure death process with rates `d_n = n(n-1)/2`
(`Descent.Coalescent.Rates.deathRate`).  The two are connected by a single algebraic
identity, and this file is that identity.

Take the *duality function* `f(x, n) = xⁿ`, which has a genealogical meaning: if the allele
is at frequency `x`, then `xⁿ` is the chance that `n` independently sampled individuals all
carry it.  Apply the diffusion generator in `x`:

  `L xⁿ = ½ x(1-x) · n(n-1) x^{n-2} = ½n(n-1)(x^{n-1} - xⁿ) = d_n (x^{n-1} - xⁿ)`,

and the right-hand side is the coalescent's block-count generator applied in `n`: from `n`
lineages, jump to `n-1` at rate `d_n`.  So

  `L_x f(x,n) = L_n f(x,n)`,

which is Kingman's duality, and it is the reason the coalescent computes anything about the
forward model at all.  The moments of the diffusion satisfy a CLOSED system -- `d/dt E xⁿ`
involves only `E x^{n-1}` and `E xⁿ`, never a higher moment -- and the closure is exactly the
fact that lineages only ever merge.

## Why this belongs in a corpus about mechanisms

Everything else in `Descent.Coalescent` derives backward quantities from a backward
mechanism.  This file is the only place the FORWARD model appears, and it says the two are
not two models: a statement about the diffusion of allele frequencies and a statement about
the genealogy of a sample are the same statement read in two directions.  The corpus's
scalar laws -- drift, `F_ST`, heterozygosity decay -- are forward statements whose
justification has always been backward, and the duality is what licenses that.

The identity is proved twice, deliberately.  `duality_identity` is the algebra, with no
analysis in it at all; `diffusionGenerator_pow` computes the same thing through Mathlib's
`deriv`, so that "the diffusion generator" means the second derivative and not a formula
that was named after one.

## Main results

- `duality_identity`: **`½x(1-x)·n(n-1)x^{n-2} = d_n(x^{n-1} - xⁿ)`**, the algebra.
- `diffusionGenerator_pow`: the same with `L` the actual second-derivative operator.
- `moment_closure`: the generator of the `n`-th moment involves only the `(n-1)`-st and the
  `n`-th, which is the statement that the system closes.
- `duality_two`: at `n = 2` both sides are `x(1-x)`, the classical variance-of-drift term --
  so the corpus's per-generation drift variance and the pair coalescence rate are one number.
- `duality_boundary`: at `x = 0` and `x = 1` both sides vanish, the fixation states being
  absorbing for the diffusion and having nothing left to say for the genealogy.
-/

namespace Coalescent

/-! ### The algebra -/

/-- The Wright-Fisher diffusion's generator acting on the monomial `xⁿ`, written out: the
diffusion coefficient `½x(1-x)` times the second derivative `n(n-1)x^{n-2}`.  The exponent is
written `m + 2` so that `n - 2` is a genuine natural number and no truncated subtraction can
hide in the statement.

Empirical status: THIS IS THE MODEL.  `½x(1-x)` is the Wright-Fisher diffusion's variance
term -- binomial sampling variance `x(1-x)/N` per generation, rescaled by `N` generations --
and asserting it of a population is asserting neutrality and constant size. -/
noncomputable def diffusionOnPow (m : ℕ) (x : ℝ) : ℝ :=
  x * (1 - x) / 2 * (((m : ℝ) + 2) * ((m : ℝ) + 1) * x ^ m)

/-- The coalescent's block-count generator acting on the same monomial: at rate `d_n` the
lineage count drops from `n` to `n - 1`, changing `xⁿ` to `x^{n-1}`.

Empirical status: DERIVED.  `deathRate` is a cardinality of the state space
(`Descent.Coalescent.StateSpace.card_covers_eq_deathRate`), and the jump is to a state with one
fewer block, which is K-C (1.4). -/
noncomputable def coalescentOnPow (m : ℕ) (x : ℝ) : ℝ :=
  deathRate (m + 2) * (x ^ (m + 1) - x ^ (m + 2))

/-- **The duality identity.**  The forward generator applied to `xⁿ` in `x` equals the
backward generator applied to `xⁿ` in `n`.  This is the whole of the connection between the
diffusion and the coalescent, and it is an identity between polynomials -- no limits, no
measure theory, no approximation. -/
theorem duality_identity (m : ℕ) (x : ℝ) : diffusionOnPow m x = coalescentOnPow m x := by
  unfold diffusionOnPow coalescentOnPow deathRate Descent.Core.pairCount
  push_cast
  ring

/-- At `n = 2` the identity is `x(1-x) = x - x²`: the binomial sampling variance of a single
generation, and the rate at which two lineages coalesce, are the same quantity.  Every
scalar drift law in the corpus rests on this coincidence, and it is not a coincidence. -/
theorem duality_two (x : ℝ) : diffusionOnPow 0 x = x * (1 - x) := by
  unfold diffusionOnPow
  ring

/-- The fixation states are fixed points of both descriptions: at `x = 0` and `x = 1` the
diffusion has no variance left and the genealogy has nothing to distinguish. -/
theorem duality_boundary (m : ℕ) :
    diffusionOnPow m 0 = 0 ∧ diffusionOnPow m 1 = 0 := by
  refine ⟨?_, ?_⟩
  · simp [diffusionOnPow]
  · simp [diffusionOnPow]

/-- **Moment closure.**  The generator of the `n`-th moment is a combination of the `n`-th
and the `(n-1)`-st and of nothing else.  Written as an explicit two-term combination so the
absence of higher moments is visible in the statement rather than in a remark.

This is what makes the coalescent USEFUL: an infinite hierarchy of moment equations that
closes downward can be solved from the bottom, and the solution is the death process. -/
theorem moment_closure (m : ℕ) (x : ℝ) :
    diffusionOnPow m x
      = deathRate (m + 2) * x ^ (m + 1) + (-deathRate (m + 2)) * x ^ (m + 2) := by
  rw [duality_identity]
  unfold coalescentOnPow
  ring

/-! ### The same statement through the actual derivative

`diffusionOnPow` writes the second derivative of `xⁿ` as a formula.  It is one, but a corpus
that lets a formula stand for an operator has stopped being able to say which operator.  The
two lemmas below compute the derivative and re-prove the identity through it. -/

/-- The second derivative of `x^{m+2}` is `(m+2)(m+1)x^m`. -/
theorem deriv_deriv_pow (m : ℕ) (x : ℝ) :
    deriv (deriv fun y : ℝ ↦ y ^ (m + 2)) x = ((m : ℝ) + 2) * ((m : ℝ) + 1) * x ^ m := by
  have h1 : (deriv fun y : ℝ ↦ y ^ (m + 2)) = fun y : ℝ ↦ ((m : ℝ) + 2) * y ^ (m + 1) := by
    funext y
    simp
  have h2 : (deriv fun y : ℝ ↦ y ^ (m + 1)) x = ((m : ℝ) + 1) * x ^ m := by
    simp
  rw [h1, deriv_const_mul_field, h2]
  ring

/-- **The diffusion generator, as an operator, applied to a monomial.**  `L f = ½x(1-x)f''`
evaluated at `f = xⁿ` gives `diffusionOnPow`, so the identity above is about the generator
and not about a formula chosen to resemble one. -/
theorem diffusionGenerator_pow (m : ℕ) (x : ℝ) :
    x * (1 - x) / 2 * deriv (deriv fun y : ℝ ↦ y ^ (m + 2)) x = diffusionOnPow m x := by
  unfold diffusionOnPow
  rw [deriv_deriv_pow]

/-- **Duality, stated with the operator.**  The composite of the two lemmas above: the
Wright-Fisher generator applied to `xⁿ` is the coalescent's death-rate combination.  This is
the form in which the result is usually quoted, and now the form in which it is proved. -/
theorem duality_deriv (m : ℕ) (x : ℝ) :
    x * (1 - x) / 2 * deriv (deriv fun y : ℝ ↦ y ^ (m + 2)) x
      = deathRate (m + 2) * (x ^ (m + 1) - x ^ (m + 2)) := by
  rw [diffusionGenerator_pow, duality_identity]
  rfl

end Coalescent

end Descent
