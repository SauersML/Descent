import Mathlib.Data.Real.Basic

namespace Calibrator

/-!
# Identification: a name that cannot be claimed without an obligation

## The bug class

A `def` in Lean is an unfalsifiable assertion of meaning. Writing

```
noncomputable def singletonProportion (N₀ N₁ : ℝ) : ℝ := 1 - Real.log N₀ / Real.log N₁
```

claims that this expression *is* the singleton proportion. Nothing in the
system can contradict the claim, so every theorem proved about it is
machine-checked and, if the claim is false, misleading. Two such claims have
now been falsified by simulation:

* `demographicSpike` had `2 F m_eff` where measurement gives `4 F m_eff`.
* `singletonProportion` returns `0` where the truth is `0.187`, is wrong
  elsewhere by 40 to 70 percent, and — decisively — takes no sample size,
  although the observable moves from `0.427` to `0.368` as `n` goes from 50 to
  200.

The second is the instructive one. It is not a wrong constant. No choice of
coefficients repairs it, because the *signature* cannot express a quantity
that depends on `n`. Relating formulas to other formulas, which is what
`Calibrator.Conventions` does, cannot detect this.

## The mechanism

An empirical quantity is introduced as an `Identification`: a closed-form
expression, the observable it is claimed to equal, and a proof that they
agree. There is no way to construct one without supplying the third field, so
a name can no longer be attached to a formula for free.

Three things follow, and they are the reason this shape was chosen.

**A wrong signature becomes a type error.** To identify a closed form with an
observable that depends on `n`, the closed form must be applied at `n`. A
two-argument `N₀ N₁` expression cannot be offered as an identification of an
`n`-dependent observable, because the equation does not typecheck. This is the
`singletonProportion` failure, and it is caught at elaboration.

**A wrong constant becomes an unprovable goal.** If the observable is given
independently — as a coalescent expectation, or as the variance of a
standardized contrast — then a formula with the wrong coefficient produces a
`derivation` field that cannot be discharged. This is the `demographicSpike`
failure.

**An undischarged obligation is visible.** Where the derivation is not yet
available the field is `sorry`, which appears in `#print axioms`, is
greppable, and is counted by CI. An honest `sorry` records that a claim is
unproved; a bare `def` records nothing. The corpus previously had zero
`sorry`s and two false identifications, which is the worse state of the two.

## Scope

This is the mechanism, with the primitives it needs supplied per domain. A
domain that has no primitive for its observable cannot use it, and that
inability is itself the finding: it says the development has been naming
quantities it has no independent handle on.
-/

universe u

/-- The status of an identification, recorded so that unproved claims are
distinguishable from proved ones without reading the proof term. -/
inductive Evidence where
  /-- The derivation is discharged from a primitive in this development. -/
  | derived
  /-- The derivation is not discharged; the identification is asserted and its
      `derivation` field is expected to be `sorry`. Simulation agreement, if
      any, is recorded in the docstring and is not a proof. -/
  | asserted
  /-- Simulation contradicts the identification. Present only so that a
      falsified claim can be marked while it is being removed; nothing should
      remain in this state across a commit. -/
  | falsified
deriving DecidableEq, Repr

/-- **An identification of a closed form with an observable.**

`formula` is the expression one wants to compute with, `observable` is the
quantity it is claimed to be, and `derivation` is the obligation. The type is
deliberately without special structure: its whole purpose is that the third
field cannot be omitted.

The intended use is that `observable` is defined from a primitive — a
coalescent expectation, a standardized genotype contrast — and never from
`formula`. Supplying `observable := formula` discharges the obligation by
`rfl` and identifies nothing; that pattern is the bare `def` in disguise and
is what `evidence` is for. -/
structure Identification (α : Type u) where
  /-- The closed form intended for computation. -/
  formula : α
  /-- The quantity the closed form is claimed to equal, defined independently. -/
  observable : α
  /-- The obligation. `sorry` here is honest; its absence is not. -/
  derivation : formula = observable
  /-- Whether the obligation is discharged from a primitive. -/
  evidence : Evidence

namespace Identification

variable {α : Type u}

/-- The formula may be used wherever the observable is expected. This is the
only way to get a value out, so downstream use always travels through the
obligation. -/
theorem formula_eq_observable (i : Identification α) :
    i.formula = i.observable := i.derivation

/-- Two identifications of the same observable have equal formulas. Stated to
make the over-determination check available generically: if a quantity is
identified twice, independently, the two closed forms must agree, and a
disagreement is a failed proof rather than a silent divergence. -/
theorem formulas_agree (i j : Identification α)
    (h : i.observable = j.observable) : i.formula = j.formula := by
  rw [i.derivation, j.derivation, h]

end Identification

end Calibrator
