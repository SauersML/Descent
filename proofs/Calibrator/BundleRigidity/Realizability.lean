import Mathlib

/-!
# Realizability: the moment identities are vacuous, and folds fix constants

This module is **self-contained: it imports only Mathlib**.

## The headline, which is a refutation of a plausible count

The naive count says a connected analytic family has "one free analytic function per sheet".
**That is false.** The configuration germ — the distinct modulus values with pooled weights
— is real-analytic, and an analytic function on an interval is determined by its
restriction to *any* subinterval. So sheet `1`'s data determines the germ on its arc, hence
on all of `T` by continuation, hence **every later sheet**. Realizable arrays are exactly
the branch tuples of **one** germ read along **one** visit pattern.

The earlier slogan "continuation kills identities, not inequalities" is **retired**. The
precise form is: **continuation determines everything; what varies is only which germ and
which visit pattern.** This module does not prove that theorem — it is analysis, and it is
carried as named hypotheses in `RealizabilityHypotheses`. What it proves are the two
elementary pieces that are fully finite.

## Item 1: the general-`B` variance identity, and why it is quotable

Split block `b` into four atoms `±√(1 + w b)` and `±√(1 - w b)`, each at mass `q b / 4`.
Then the mean vanishes by symmetry (`block_mean_zero`) and the variance is

```
∑_b (q b / 4)·[ (1 + w b) + (1 + w b) + (1 - w b) + (1 - w b) ]  =  ∑_b q b  =  1
```

**identically** — for every `B`, every choice of defining values `w`, and every weight
vector `q` summing to one (`block_variance_one`). The `w` cancel in pairs before the sum is
ever taken.

The consequence is the quotable one and it is `moment_realizability_vacuous`:

> **pointwise moment realizability is never a condition.**

The entire content of realizability is the continuation relation plus boundary discipline.
The moment constraints absorb themselves and constrain nothing. Anyone reporting a
"moment obstruction" to realizability has found an artefact of their parameterization.

This generalizes to all `B` the `B = 1` identity already recorded in `SingleModulus`
(`fourAtom`), where the same cancellation appears as the fact that the mean identity holds
for *every* `c` and the variance is insensitive to `c`.

## Item 3: folds fix constants — an empirical wall reduced to a corollary

At a fold the two laps are the two branches of one square-root germ. With `τ = √(v₁ - v)`,
the **difference** `(dataᵢ - dataᵢ₊₁)/(2τ)` must stay analytic at `v₁`, so in particular
bounded. A constant numerator divided by `τ` blows up unless the numerator is zero
(`eq_zero_of_bounded_by_linear`). Hence:

> **two sheets carrying different constant weights violate the fold criterion
> immediately**, and no visit pattern evades it (`folds_fix_constants`).

That is an earlier obstruction — originally found the hard way, by three failed hand
constructions — reduced to a two-line corollary of boundedness. It is recorded here as a
corollary precisely because a wall discovered empirically and a wall derived from a
criterion are very different objects, and only the second tells you where the next wall is.

## Problem 7: effective in `(d, D)`, and the negative half is the useful one

For polynomial or Nash data of degree `≤ D` the exceptional set is bounded by `C·d²·D²`,
itemized by critical values, branch coincidences and cross-parameter resultants — so the
block criterion is polynomial in the input degree and effective.

**But there is no bound in `d` alone.** An `8`-atom family with defining value
`v* + ε·sin(N t)` crosses the window edge `2N` times and produces at least `N` blocks:
**fixed atom count, unbounded block count.** `crossings_unbounded_at_fixed_atom_count`
records the counting half of that witness — the atom count does not appear in it, which is
exactly the point.

So the criterion is **semi-effective in `d` and effective in `(d, D)`**, and *any claim
that a bounded atom count bounds the analysis is false.*

## Attribution and scope

The realizability theorem is the source's; only the elementary fragments are proved here.
The reduction that actually matters downstream is their 3.2 — the moduli of a connected
`r`-sheet system needs **one** function's worth of germ plus finite combinatorics rather
than `r` functions — because it is what makes stratification by kernel dimension tractable,
and that stratification says which perturbations of a panel change identifiability. That
reduction is carried as a named field, not proved.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators
open Finset

/-! ## Item 1: the general-`B` moment identities -/

variable {B : ℕ}

/-- **The mean vanishes identically**, for every block decomposition.

Each block contributes `A - A + C - C = 0` before any summation, so the identity needs no
hypothesis on the weights, the defining values, or `B`. -/
theorem block_mean_zero (q A C : Fin B → ℝ) :
    ∑ b, (q b / 4) * (A b + (-A b) + C b + (-C b)) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  ring

/-- **The variance identity, for every `B`.**

With `A b ^ 2 = 1 + w b` and `C b ^ 2 = 1 - w b`, each block contributes exactly `q b`,
because the `w b` cancel in pairs *within* the block. So the total is `∑ q b = 1` whatever
the defining values are. -/
theorem block_variance_one (q w A C : Fin B → ℝ)
    (hA : ∀ b, A b ^ 2 = 1 + w b) (hC : ∀ b, C b ^ 2 = 1 - w b)
    (hq : ∑ b, q b = 1) :
    ∑ b, (q b / 4) * (A b ^ 2 + (-A b) ^ 2 + C b ^ 2 + (-C b) ^ 2) = 1 := by
  have hterm : ∀ b ∈ (univ : Finset (Fin B)),
      (q b / 4) * (A b ^ 2 + (-A b) ^ 2 + C b ^ 2 + (-C b) ^ 2) = q b := by
    intro b _
    have h1 : (-A b) ^ 2 = A b ^ 2 := by ring
    have h2 : (-C b) ^ 2 = C b ^ 2 := by ring
    rw [h1, h2, hA b, hC b]
    ring
  rw [Finset.sum_congr rfl hterm]
  exact hq

/-- **Pointwise moment realizability is never a condition.**

Both standardization identities hold *simultaneously and identically*: for every block
count `B`, every vector of defining values `w`, and every weight vector `q` summing to one,
the four-atom-per-block configuration has mean zero and variance one.

There is no side condition to check and nothing to obstruct. The whole content of
realizability lies in the continuation relation and the boundary discipline; the moment
constraints absorb themselves. -/
theorem moment_realizability_vacuous (q w A C : Fin B → ℝ)
    (hA : ∀ b, A b ^ 2 = 1 + w b) (hC : ∀ b, C b ^ 2 = 1 - w b)
    (hq : ∑ b, q b = 1) :
    (∑ b, (q b / 4) * (A b + (-A b) + C b + (-C b)) = 0) ∧
      (∑ b, (q b / 4) * (A b ^ 2 + (-A b) ^ 2 + C b ^ 2 + (-C b) ^ 2) = 1) :=
  ⟨block_mean_zero q A C, block_variance_one q w A C hA hC hq⟩

/-! ## Item 3: folds fix constants -/

/-- **A quantity dominated by `M · τ` for all small positive `τ` is zero.**

This is the boundedness step of the fold relation, isolated: `(dataᵢ - dataᵢ₊₁)/(2τ)` stays
analytic, hence bounded, near the fold, which says the numerator is `O(τ)`. -/
theorem eq_zero_of_bounded_by_linear (k M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hbound : ∀ τ : ℝ, 0 < τ → τ < δ → |k| ≤ M * τ) : k = 0 := by
  by_contra hk
  have habs : 0 < |k| := abs_pos.mpr hk
  set τ := min (δ / 2) (|k| / (2 * (M + 1))) with hτdef
  have hMpos : (0 : ℝ) < M + 1 := by linarith
  have hτpos : 0 < τ := by
    apply lt_min
    · linarith
    · positivity
  have hτlt : τ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hle := hbound τ hτpos hτlt
  have hτle : τ ≤ |k| / (2 * (M + 1)) := min_le_right _ _
  have hchain : M * τ ≤ M * (|k| / (2 * (M + 1))) :=
    mul_le_mul_of_nonneg_left hτle hM
  have hfrac : M * (|k| / (2 * (M + 1))) < |k| := by
    rw [mul_div_assoc'] at *
    rw [div_lt_iff (by linarith : (0:ℝ) < 2 * (M + 1))]
    nlinarith [habs, hM]
  linarith

/-- **Folds fix constants.**

If two sheets carry constant data `c₁` and `c₂`, the fold relation forces
`|c₁ - c₂| = O(τ)` near the fold, and a constant that is `O(τ)` is zero. So the two
constants agree.

**Two sheets with different constant weights therefore violate the criterion immediately,
and no visit pattern evades it** — the argument never mentions the visit pattern. This is
the earlier obstruction, found originally by three failed hand constructions, as a
corollary. -/
theorem folds_fix_constants (c₁ c₂ M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hfold : ∀ τ : ℝ, 0 < τ → τ < δ → |c₁ - c₂| ≤ M * τ) : c₁ = c₂ := by
  have := eq_zero_of_bounded_by_linear (c₁ - c₂) M δ hM hδ hfold
  linarith [sub_eq_zero.mp this]

/-! ## Problem 7: no bound in the atom count alone -/

/-- **Fixed atom count, unbounded block count.**

The witness family has a fixed atom count (`8`) and defining value `v* + ε·sin(N t)`, whose
level crossings grow without bound in `N`. This lemma records the counting half: `sin(N t)`
has at least `N + 1` distinct zeros, exhibited explicitly at `t = kπ/N`.

**The atom count does not appear in the statement**, which is exactly the content: no
function of `d` alone can bound the number of blocks. The block criterion is therefore
semi-effective in `d`, and effective only in `(d, D)`. -/
theorem crossings_unbounded_at_fixed_atom_count (N : ℕ) (hN : 0 < N) :
    ∃ f : Fin (N + 1) → ℝ, Function.Injective f ∧
      ∀ k : Fin (N + 1), Real.sin ((N : ℝ) * f k) = 0 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff.mp hN).ne'
  refine ⟨fun k => (k : ℕ) * Real.pi / (N : ℝ), ?_, ?_⟩
  · intro k k' hkk'
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hkk'
    rcases hkk' with h | h
    · exact Fin.ext (Nat.cast_injective h)
    · exact absurd h hpi
  · intro k
    have : (N : ℝ) * ((k : ℕ) * Real.pi / (N : ℝ)) = (k : ℕ) * Real.pi := by
      field_simp
    rw [this]
    exact Real.sin_nat_mul_pi _

/-! ## The analytic inputs -/

/-- The realizability analysis this module does not carry, as named fields.

Nothing here is a `sorry`. `configurationGermAnalytic` and `continuationDetermines` are the
content of the headline theorem; `puiseuxFoldRelation` is the `ℤ/2` monodromy at a fold —
the mean is analytic and the difference divided by `2τ` is analytic, so the second sheet's
Puiseux coefficients are the sign-alternated coefficients of the first, checkable
coefficient by coefficient. `boundaryDiscipline` is the remaining side condition once the
moment constraints are known to be vacuous.

`sheetModuliReduction` is their 3.2, and it is the item with real downstream value: the
moduli of a connected `r`-sheet system reduce to one germ plus finite combinatorics rather
than `r` independent functions, which is what makes stratification by kernel dimension
tractable — and that stratification says which perturbations of a panel change
identifiability.

**`blockCollisionStrata` is audit point (AP-b)** and it is the one that touches this
project: the sufficiency argument assumes a constant block pattern, so it is currently
proved *off* the isolated strata where atoms merge. -/
structure RealizabilityHypotheses where
  /-- The configuration germ (distinct modulus values with pooled weights) is
  real-analytic. -/
  configurationGermAnalytic : Prop
  /-- Sheet one's data determines the germ on its arc, hence everywhere by continuation. -/
  continuationDetermines : Prop
  /-- The `ℤ/2` Puiseux monodromy relating the two laps at a fold. -/
  puiseuxFoldRelation : Prop
  /-- The boundary discipline, which with continuation is the entire content of
  realizability once the moment identities are known vacuous. -/
  boundaryDiscipline : Prop
  /-- **Their 3.2.** Connected `r`-sheet moduli reduce to one germ plus finite
  combinatorics. The item with genuine downstream value. -/
  sheetModuliReduction : Prop
  /-- **AP-b.** Sufficiency is proved off the isolated strata where blocks collide. -/
  blockCollisionStrata : Prop

end Calibrator.BundleRigidity
