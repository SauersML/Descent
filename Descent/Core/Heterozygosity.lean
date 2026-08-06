/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Ratios
import Descent.Layer

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Core: the heterozygosity decay recurrence

**Depth 1. Imports `Core.Ratios` and Mathlib, and nothing else from this corpus.**

## Why this is here and not in `PopGen`

`hetRecurrence` is the single most load-bearing posit in the corpus: heterozygosity
decays by a factor `1 - 1/(2Nₑ)` per generation, and `F_ST`, the drift-retention factor,
the transient island equilibrium and the deployed metrics all descend from it.

`Coalescent/WrightFisher` DERIVES it. Its `hetRecurrence_eq_pairDistinct` shows the decay
factor is the probability that two lineages fail to coalesce in one Wright--Fisher
generation, which is what makes `1 - 1/(2Nₑ)` a mechanism rather than a coefficient.

The dependency used to run the wrong way: `WrightFisher` imported
`PopGen.PopulationGeneticsFoundations` to reach the posit, so the module holding the
derivation sat ABOVE the module holding the thing derived, and every downstream consumer
of `hetRecurrence` depended on the posit rather than on the mechanism. Moving the
recurrence to depth 1 lets both sides reach it: `PopGen` computes with it, `Coalescent`
grounds it, and neither imports the other.

## What is and is not claimed here

The recurrence is a definition. That a real population's heterozygosity follows it is a
claim about Wright--Fisher reproduction, and that claim lives where the mechanism is --
in `Coalescent/WrightFisher`, whose own docstring records what it closes. Nothing in this
file carries an empirical status, and the closed form below is algebra: an induction on
the step law, true of any geometric decay.
-/

namespace Descent.Core

/-- **Heterozygosity under drift alone**, `H(t+1) = (1 - 1/(2Nₑ)) · H(t)`.

The factor is the probability that two lineages sampled in the child generation do not
share a parent. Writing it as a recurrence rather than as its closed form is deliberate:
the step is what a mechanism can be compared against, and `hetRecurrence_closed_form`
below derives the power.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def hetRecurrence (Ne : ℝ) (H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => (1 - 1 / (2 * Ne)) * hetRecurrence Ne H₀ t

/-- **At time zero nothing has been lost.** -/
@[simp] theorem hetRecurrence_zero (Ne H₀ : ℝ) : hetRecurrence Ne H₀ 0 = H₀ := rfl

/-- **Closed form**, `H(t) = (1 - 1/(2Nₑ))^t · H₀`, by induction on the step law. -/
theorem hetRecurrence_closed_form (Ne H₀ : ℝ) (t : ℕ) :
    hetRecurrence Ne H₀ t = (1 - 1 / (2 * Ne)) ^ t * H₀ := by
  induction t with
  | zero => simp [hetRecurrence]
  | succ n ih =>
    simp only [hetRecurrence, ih]
    ring

/-- **The decay is a geometric one on the retained fraction.** Stated through the kernel
so that this recurrence and the corpus's other `(1-r)^t` quantities cannot drift apart. -/
theorem hetRecurrence_eq_geometricDecay (Ne H₀ : ℝ) (t : ℕ) :
    hetRecurrence Ne H₀ t = geometricDecay (1 / (2 * Ne)) t * H₀ := by
  rw [hetRecurrence_closed_form]
  rfl

/-- **Fraction of ancestral heterozygosity lost by generation `t`**,
`1 - (1 - 1/(2Nₑ))^t`.

This is `proportionalReduction` of the retained heterozygosity against the ancestral
one, and it is written under two names in `PopGen` -- `heterozygosityLossFromDrift` and
`heterozygosityLossDerived`. The second has since been deleted; the first calls this.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def heterozygosityLoss (Ne : ℝ) (t : ℕ) : ℝ :=
  complement (geometricDecay (1 / (2 * Ne)) t)

/-- **The loss is the proportional reduction the recurrence produces**, which is what
ties the two readings together rather than leaving them to agree by inspection. -/
theorem heterozygosityLoss_eq_proportionalReduction (Ne H₀ : ℝ) (t : ℕ) (h : H₀ ≠ 0) :
    heterozygosityLoss Ne t = proportionalReduction (hetRecurrence Ne H₀ t) H₀ := by
  unfold heterozygosityLoss complement proportionalReduction geometricDecay
  rw [hetRecurrence_closed_form]
  field_simp

/-- **Nothing is lost at time zero.** -/
@[simp] theorem heterozygosityLoss_zero (Ne : ℝ) : heterozygosityLoss Ne 0 = 0 := by
  unfold heterozygosityLoss complement geometricDecay
  norm_num

/-- **heterozygosityLoss at an empty population, named.** At `Nₑ = 0` the per-generation
factor is `1 - 1/0 = 1`, so Lean reports no loss at all for a population that has no
members to lose anything. Consumers must require `Nₑ ≠ 0`. -/
theorem heterozygosityLoss_empty_is_junk (t : ℕ) :
    heterozygosityLoss 0 t = complement 1 := by
  unfold heterozygosityLoss geometricDecay
  norm_num

end Descent.Core
