/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

/-!
# Single-atom modulus families, and a correction to the classification

This module is **self-contained: it imports only Mathlib**, so it sits outside the
in-flight dependency refactor.

## The question

Fix `v ≥ 0`. Which standardized finite distributions have **all their modulus values
equal to `v`** — that is, `|a j ^ 2 - 1| = v` for every atom `j`, so that the transfer
measure is the single atom `δ v`?

"Standardized" means the masses are positive, sum to one, and give mean zero and variance
one. "Distinct" means the atom values are pairwise different, which is what makes the
number of atoms `d` a well-posed quantity rather than an artefact of listing an atom
twice.

## The classification, corrected

An upstream note claimed:

> `TT t = δ v` with `v > 0` holds **iff** `d = 4`, with atoms `± √(1+v)`, `± √(1-v)` and
> masses `(1/4 + c√(1-v), 1/4 - c√(1-v), 1/4 - c√(1+v), 1/4 + c√(1+v))`; **no `d ≤ 3`
> family exists for `v > 0`.**

**The solution line is right. The `d ≤ 3` impossibility is false, and this module refutes
it with an explicit witness.**

`d = 3` families exist for *every* `0 < v < 1`. Take

```
atoms   =  ( √(1+v),  -√(1+v),  -√(1-v) )
masses  =  ( 1/4 + B/(4A),  1/4 - B/(4A),  1/2 )      A = √(1+v),  B = √(1-v)
```

Every mass is strictly positive, because `B < A`. At `v = 3/5` this is `A = 2B` with
`B² = 2/5`, and the masses are exactly `(3/8, 1/8, 1/2)` — see
`threeAtomWitness_threeFifths`, which is rational arithmetic and needs no square-root
manipulation at all.

### Two witnesses, and they are two *different* defects

The refutation has two witnesses, and it matters that they are **not two instances of one
mistake**. They are two independent failures of different kinds, and only the first could
have been caught by being more careful with the existing argument.

1. **`0 < v < 1` (`threeAtom`, and `threeAtomWitness_threeFifths` at `v = 3/5`) — a
   boundary mishandled.** This family *is* expressible in the upstream parameterization:
   it is the closed endpoint `|c| = 1/(4√(1+v))` of the very `c`-line the upstream
   statement writes down. The upstream text restricted to "`|c|` small enough for
   positivity" and then asserted the endpoints were empty. The parameter interval is
   closed and its endpoints are families. A careful redo of the same argument finds this.

2. **`v = 1` (`threeAtomAtOne`) — a case the method cannot express.** This one is *not* a
   point of the `c`-line. At `v = 1` the two `(1-v)`-side atoms collide at zero, so `d = 4`
   is impossible outright (`card_le_three_of_v_eq_one`) and the three-atom family
   `(√2, -√2, 0)` with masses `(1/4, 1/4, 1/2)` is the *only* family there. The upstream
   argument turns on the ratio `√((1+v)/(1-v))`, which **divides by zero at `v = 1`**, so
   the case was never reachable by it at all.

**The second is the more serious kind.** No amount of care with the existing argument
would have found it, because the argument has no value to take at that point. A defect of
type 1 is a slip; a defect of type 2 says the method's domain of validity was never
checked against the domain of the claim.

### Where the upstream argument went wrong, precisely

The upstream proof deleted an atom and derived a negative mass. It deleted a
**`(1-v)`-side** atom: setting `x' = 0` forces `y - y' = -(1/2)√((1+v)/(1-v))`, and since
that ratio exceeds one, `y < 0`. That case is genuinely impossible and the argument for it
is correct.

But the **other** deletion was never checked. Delete a `(1+v)`-side atom — equivalently
set the mass at `√(1-v)` to zero — and the forced value is
`x - x' = √((1-v)/(1+v)) / 2`, whose ratio is **less than** one, so
`x' = 1/4 - B/(4A) > 0`. Every remaining mass is positive. The sign of the inequality
flips with the direction of the deletion, and only one direction was examined.

Structurally: `d = 3` is not a separate case at all. It is the **endpoint of the same
one-parameter line**. The upstream parameter `c` ranges over `|c| ≤ 1/(4√(1+v))`; the
interior gives `d = 4`, and the two endpoints `c = ±1/(4√(1+v))` are exactly the two
`d = 3` families, obtained when the mass at `∓√(1-v)` reaches zero. The upstream
statement quietly restricted to the open interval ("for `|c|` small enough for
positivity") and then asserted the closed endpoints were empty.

### What survives

* `v > 1` is impossible (`v_le_one`) — proved here in general `d`.
* the side masses are forced to be `1/2` and `1/2` (`sideMass_eq_half`) — proved here in
  general `d`, and this is the load-bearing step of the whole classification.
* `d = 2` is impossible for `v > 0` (`two_atom_forces_v_zero`) — proved here, in full,
  with no case left unchecked. This part of the upstream claim is correct.
* `v = 0` is the Rademacher case.

## Method note

This correction is an **executed falsifier, not a named one**. The upstream claim was a
universal negative ("no `d ≤ 3` family exists"), and a universal negative is refuted by
one witness. The witness is exhibited, its four defining identities are checked, and its
masses are rational. A search that reports "no such family" is informative only if it is
known capable of finding one; `threeAtomWitness_threeFifths` is the positive control that
the upstream search failed.

## Attribution

Nothing in this module is deep. It is finite algebra: a two-way case split on
`a² ∈ {1+v, 1-v}`, one linear equation from the variance identity, one from the mean. It
is recorded because a false universal claim was about to be built on.
-/

namespace Descent.BundleRigidity

open scoped BigOperators
open Finset

/-! ## The object -/

/-- A **single-atom modulus family** with `d` distinct atoms and modulus value `v`.

The transfer measure of such a family is the single Dirac mass `δ v`: every atom has the
same modulus `|a² - 1| = v`, so the operator `L` cannot distinguish the atoms at all. -/
structure SingleModulus (d : ℕ) (v : ℝ) where
  /-- The atom values. -/
  atom : Fin d → ℝ
  /-- The atom masses. -/
  mass : Fin d → ℝ
  /-- The atoms are pairwise distinct, so `d` counts atoms rather than repetitions. -/
  atom_inj : Function.Injective atom
  /-- Every mass is strictly positive. -/
  mass_pos : ∀ j, 0 < mass j
  /-- The masses form a probability vector. -/
  mass_sum : ∑ j, mass j = 1
  /-- Standardization: mean zero. -/
  mean_zero : ∑ j, mass j * atom j = 0
  /-- Standardization: variance one. -/
  var_one : ∑ j, mass j * atom j ^ 2 = 1
  /-- Every modulus value equals `v`: the transfer measure is `δ v`. -/
  modulus_eq : ∀ j, |atom j ^ 2 - 1| = v

/-- The standardized two-atom law at `±1`, with mass `1/2` at each atom. -/
noncomputable def SingleModulus.witness : SingleModulus 2 0 where
  atom := fun j ↦ if j = 0 then -1 else 1
  mass := fun _ ↦ 1 / 2
  atom_inj := by
    intro i j h
    fin_cases i
    · fin_cases j
      · rfl
      · norm_num at h
    · fin_cases j
      · norm_num at h
      · rfl
  mass_pos := fun _ ↦ by norm_num
  mass_sum := by norm_num [Fin.sum_univ_two]
  mean_zero := by norm_num [Fin.sum_univ_two]
  var_one := by norm_num [Fin.sum_univ_two]
  modulus_eq := by
    intro j
    fin_cases j <;> norm_num

/-- `SingleModulus 2 0` is inhabited by the explicit symmetric two-atom law. -/
theorem SingleModulus.nonempty : Nonempty (SingleModulus 2 0) :=
  ⟨SingleModulus.witness⟩

namespace SingleModulus

variable {d : ℕ} {v : ℝ}

/-- There is at least one atom: an empty family would have total mass `0 ≠ 1`. -/
theorem pos_of_card (S : SingleModulus d v) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exfalso
    subst h
    have hm := S.mass_sum
    simp at hm
  · exact h

/-- The modulus value is non-negative, being an absolute value. -/
theorem v_nonneg (S : SingleModulus d v) : 0 ≤ v := by
  have h : 0 < d := S.pos_of_card
  have := S.modulus_eq ⟨0, h⟩
  rw [← this]
  exact abs_nonneg _

/-- **The two-sided dichotomy.** Every atom squares to `1 + v` or to `1 - v`; there is
nowhere else for it to be. This is the entire combinatorial content of the problem. -/
theorem sq_cases (S : SingleModulus d v) (j : Fin d) :
    S.atom j ^ 2 = 1 + v ∨ S.atom j ^ 2 = 1 - v := by
  rcases (abs_eq S.v_nonneg).mp (S.modulus_eq j) with h | h
  · left; linarith
  · right; linarith

/-! ## The forced side masses

The single load-bearing computation: the total mass on the `(1+v)` side and on the
`(1-v)` side are each exactly `1/2`, forced by the variance identity alone.
-/

open Classical in
/-- The atoms squaring to `1 + v`. -/
noncomputable def plusSide (S : SingleModulus d v) : Finset (Fin d) :=
  univ.filter fun j ↦ S.atom j ^ 2 = 1 + v

open Classical in
/-- The atoms squaring to `1 - v`. -/
noncomputable def minusSide (S : SingleModulus d v) : Finset (Fin d) :=
  univ.filter fun j ↦ ¬ (S.atom j ^ 2 = 1 + v)

/-- Total mass on the `(1+v)` side. -/
noncomputable def wPlus (S : SingleModulus d v) : ℝ := ∑ j ∈ S.plusSide, S.mass j

/-- Total mass on the `(1-v)` side. -/
noncomputable def wMinus (S : SingleModulus d v) : ℝ := ∑ j ∈ S.minusSide, S.mass j

/-- On the minus side the square really is `1 - v`. -/
theorem sq_of_mem_minusSide (S : SingleModulus d v) {j : Fin d} (hj : j ∈ S.minusSide) :
    S.atom j ^ 2 = 1 - v := by
  classical
  simp only [minusSide, mem_filter] at hj
  rcases S.sq_cases j with h | h
  · exact absurd h hj.2
  · exact h

/-- On the plus side the square is `1 + v`. -/
theorem sq_of_mem_plusSide (S : SingleModulus d v) {j : Fin d} (hj : j ∈ S.plusSide) :
    S.atom j ^ 2 = 1 + v := by
  classical
  simp only [plusSide, mem_filter] at hj
  exact hj.2

/-- The two sides carry the whole mass. -/
theorem wPlus_add_wMinus (S : SingleModulus d v) : S.wPlus + S.wMinus = 1 := by
  classical
  rw [wPlus, wMinus, plusSide, minusSide,
    Finset.sum_filter_add_sum_filter_not univ (fun j ↦ S.atom j ^ 2 = 1 + v) S.mass]
  exact S.mass_sum

/-- The variance identity, resolved onto the two sides. -/
theorem variance_split (S : SingleModulus d v) :
    (1 + v) * S.wPlus + (1 - v) * S.wMinus = 1 := by
  classical
  have hsplit :
      ∑ j ∈ S.plusSide, S.mass j * S.atom j ^ 2
        + ∑ j ∈ S.minusSide, S.mass j * S.atom j ^ 2 = 1 := by
    rw [plusSide, minusSide,
      Finset.sum_filter_add_sum_filter_not univ (fun j ↦ S.atom j ^ 2 = 1 + v)
        (fun j ↦ S.mass j * S.atom j ^ 2)]
    exact S.var_one
  have hp : ∑ j ∈ S.plusSide, S.mass j * S.atom j ^ 2 = (1 + v) * S.wPlus := by
    rw [wPlus, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [S.sq_of_mem_plusSide hj]; ring
  have hm : ∑ j ∈ S.minusSide, S.mass j * S.atom j ^ 2 = (1 - v) * S.wMinus := by
    rw [wMinus, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [S.sq_of_mem_minusSide hj]; ring
  rw [hp, hm] at hsplit
  exact hsplit

/-- **The side masses are forced.** For `v ≠ 0` each side carries exactly half the mass.

This is the step everything else rests on, and it uses only the two standardization
identities: `w₊ + w₋ = 1` and `(1+v)w₊ + (1-v)w₋ = 1` subtract to `v(w₊ - w₋) = 0`. -/
theorem sideMass_eq_half (S : SingleModulus d v) (hv : v ≠ 0) :
    S.wPlus = 1 / 2 ∧ S.wMinus = 1 / 2 := by
  have h1 := S.wPlus_add_wMinus
  have h2 := S.variance_split
  have hz : v * (S.wPlus - S.wMinus) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hv
  · constructor <;> linarith

/-- **`v > 1` is impossible.** If `v` exceeded one, the `(1-v)` side would ask an atom to
have negative square, so it would be empty — but it must carry mass `1/2`. -/
theorem v_le_one (S : SingleModulus d v) (hv : v ≠ 0) : v ≤ 1 := by
  classical
  by_contra hgt
  push_neg at hgt
  have hall : ∀ j, S.atom j ^ 2 = 1 + v := by
    intro j
    rcases S.sq_cases j with h | h
    · exact h
    · exfalso; nlinarith [sq_nonneg (S.atom j)]
  have hempty : S.minusSide = (∅ : Finset (Fin d)) :=
    Finset.filter_false_of_mem fun j _ ↦ not_not_intro (hall j)
  have hzero : S.wMinus = 0 := by rw [wMinus, hempty, Finset.sum_empty]
  have := (S.sideMass_eq_half hv).2
  rw [hzero] at this
  norm_num at this

/-! ## `d = 2` is impossible for `v > 0`

This part of the upstream claim is correct, and it is proved here in full: all four
placements of the two atoms are checked, none is left implicit.
-/

/-- **Two distinct atoms force `v = 0`.** A two-atom standardized family with a single
modulus value is the Rademacher family, and its modulus value is zero.

Every case is discharged: both atoms on the same side forces them to be `±a` with equal
masses and `a² = 1`; atoms on opposite sides forces equal masses by the variance identity
and then `a₁ = -a₀`, hence equal squares, hence `v = 0`. -/
theorem two_atom_forces_v_zero (S : SingleModulus 2 v) : v = 0 := by
  have hsum : S.mass 0 + S.mass 1 = 1 := by
    have := S.mass_sum; rwa [Fin.sum_univ_two] at this
  have hmean : S.mass 0 * S.atom 0 + S.mass 1 * S.atom 1 = 0 := by
    have := S.mean_zero; rwa [Fin.sum_univ_two] at this
  have hvar : S.mass 0 * S.atom 0 ^ 2 + S.mass 1 * S.atom 1 ^ 2 = 1 := by
    have := S.var_one; rwa [Fin.sum_univ_two] at this
  have hne : S.atom 0 ≠ S.atom 1 := by
    intro h
    have : (0 : Fin 2) = 1 := S.atom_inj h
    exact absurd this (by decide)
  -- The shared sub-argument: equal squares force opposite atoms, equal masses, `a² = 1`.
  have same_side : S.atom 0 ^ 2 = S.atom 1 ^ 2 → S.atom 0 ^ 2 = 1 := by
    intro hsq
    have hfac : (S.atom 0 - S.atom 1) * (S.atom 0 + S.atom 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith : S.atom 0 = S.atom 1) hne
    · have ha1 : S.atom 1 = -S.atom 0 := by linarith
      rw [ha1] at hmean
      have hz : S.atom 0 * (S.mass 0 - S.mass 1) = 0 := by linear_combination hmean
      rcases mul_eq_zero.mp hz with h0 | hp
      · exfalso
        apply hne
        rw [ha1, h0]; ring
      · have hm0 : S.mass 0 = 1 / 2 := by linarith
        have hm1 : S.mass 1 = 1 / 2 := by linarith
        rw [ha1, hm0, hm1] at hvar
        linarith [hvar]
  -- The two opposite-sides cases differ only in which mass the variance identity leaves
  -- on the left, and their tails were written out twice, line for line. Equal masses force
  -- the atoms to be antipodal, hence equal squares, whichever way round the sides fell.
  have equal_masses_forces_equal_squares :
      S.mass 0 = S.mass 1 → S.atom 0 ^ 2 = S.atom 1 ^ 2 := by
    intro hmass
    have hm0 : S.mass 0 = 1 / 2 := by linarith
    have hm1 : S.mass 1 = 1 / 2 := by linarith
    rw [hm0, hm1] at hmean
    have ha1 : S.atom 1 = -S.atom 0 := by linarith
    rw [ha1]; ring
  rcases S.sq_cases 0 with e0 | e0 <;> rcases S.sq_cases 1 with e1 | e1
  · -- both on the `(1+v)` side
    have := same_side (by rw [e0, e1])
    rw [e0] at this; linarith
  · -- opposite sides
    have hz : v * (S.mass 0 - S.mass 1) = 0 := by
      rw [e0, e1] at hvar; linear_combination hvar - hsum
    rcases mul_eq_zero.mp hz with h | hp
    · exact h
    · have hsq := equal_masses_forces_equal_squares (by linarith)
      rw [e0, e1] at hsq; linarith
  · -- opposite sides, the other way round
    have hz : v * (S.mass 1 - S.mass 0) = 0 := by
      rw [e0, e1] at hvar; linear_combination hvar - hsum
    rcases mul_eq_zero.mp hz with h | hp
    · exact h
    · have hsq := equal_masses_forces_equal_squares (by linarith)
      rw [e0, e1] at hsq; linarith
  · -- both on the `(1-v)` side
    have := same_side (by rw [e0, e1])
    rw [e0] at this; linarith

/-! ## How many atoms there can be

The atoms are confined to at most four values, and at `v = 1` to at most three, because
the two `(1-v)`-side values collide at zero. That collision is the second defect in the
upstream classification: its ratio `√((1+v)/(1-v))` divides by zero at `v = 1`, so the
case was never reachable by its argument at all.
-/

/-- An injective map from `Fin d` into a finite set of reals bounds `d` by its size. -/
theorem card_le_of_mapsTo {d : ℕ} {f : Fin d → ℝ} (hinj : Function.Injective f)
    (s : Finset ℝ) (hs : ∀ j, f j ∈ s) : d ≤ s.card := by
  classical
  have h1 : (Finset.univ.image f).card = d := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have h2 : Finset.univ.image f ⊆ s := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact hs j
  calc d = (Finset.univ.image f).card := h1.symm
    _ ≤ s.card := Finset.card_le_card h2

/-- **Every atom is one of the four values `±√(1+v)`, `±√(1-v)`.** -/
theorem atom_mem_four (S : SingleModulus d v) {A B : ℝ} (hA : A ^ 2 = 1 + v)
    (hB : B ^ 2 = 1 - v) (j : Fin d) :
    S.atom j ∈ ({A, -A, B, -B} : Finset ℝ) := by
  classical
  rcases S.sq_cases j with h | h
  · have hfac : (S.atom j - A) * (S.atom j + A) = 0 := by
      linear_combination h - hA
    rcases mul_eq_zero.mp hfac with h0 | h0
    · simp [show S.atom j = A by linarith]
    · simp [show S.atom j = -A by linarith]
  · have hfac : (S.atom j - B) * (S.atom j + B) = 0 := by
      linear_combination h - hB
    rcases mul_eq_zero.mp hfac with h0 | h0
    · simp [show S.atom j = B by linarith]
    · simp [show S.atom j = -B by linarith]

/-- **At most four atoms.** -/
theorem card_le_four (S : SingleModulus d v) {A B : ℝ} (hA : A ^ 2 = 1 + v)
    (hB : B ^ 2 = 1 - v) : d ≤ 4 := by
  classical
  refine le_trans (card_le_of_mapsTo S.atom_inj _ (S.atom_mem_four hA hB)) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h1 : ({-A, B, -B} : Finset ℝ).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 : ({B, -B} : Finset ℝ).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega
  omega

/-- **At `v = 1` there are at most three atoms**, because `√(1-v) = 0` and the two
`(1-v)`-side values collide. Consequently the upstream `d = 4` conclusion cannot hold at
`v = 1`, and its argument could never have reached the case: the ratio
`√((1+v)/(1-v))` it depends on is undefined there. -/
theorem card_le_three_of_v_eq_one (S : SingleModulus d 1) {A : ℝ} (hA : A ^ 2 = 2) :
    d ≤ 3 := by
  classical
  have hmem : ∀ j, S.atom j ∈ ({A, -A, (0 : ℝ)} : Finset ℝ) := by
    intro j
    have h := S.atom_mem_four (A := A) (B := 0) (by rw [hA]; norm_num) (by norm_num) j
    simpa using h
  refine le_trans (card_le_of_mapsTo S.atom_inj _ hmem) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h1 : ({-A, (0 : ℝ)} : Finset ℝ).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  omega

end SingleModulus

/-! ## The refutation: `d = 3` families exist for every `0 < v < 1`

The construction, and then the rational witness at `v = 3/5`.
-/

/-- **An atom on the `(1+v)` side has modulus `v`.** -/
theorem modulus_of_sq_eq_one_add {a v : ℝ} (hv : 0 ≤ v) (ha : a ^ 2 = 1 + v) :
    |a ^ 2 - 1| = v := by
  rw [ha, show (1 : ℝ) + v - 1 = v by ring]
  exact abs_of_nonneg hv

/-- **And an atom on the `(1-v)` side has the same modulus**, through the other sign.

Between them these two discharge every `modulus_eq` field in the witnesses below.  Each
witness proved them again for each of its atoms, four lines per atom, and the `±` atoms
proved them a second time through `(-a)^2 = a^2`: the same two facts, eight ways. -/
theorem modulus_of_sq_eq_one_sub {a v : ℝ} (hv : 0 ≤ v) (ha : a ^ 2 = 1 - v) :
    |a ^ 2 - 1| = v := by
  rw [ha, show (1 : ℝ) - v - 1 = -v by ring, abs_neg]
  exact abs_of_nonneg hv

/-- **A three-atom single-modulus family**, for any `0 < v < 1`.

Atoms `A, -A, -B` with `A = √(1+v)`, `B = √(1-v)`; masses
`1/4 + B/(4A)`, `1/4 - B/(4A)`, `1/2`. Positivity of the second mass is exactly `B < A`,
which is exactly `v > 0`.

**This refutes the upstream claim that no `d ≤ 3` family exists for `v > 0`.** It is the
`c = 1/(4A)` endpoint of the upstream one-parameter line, at which the mass on `√(1-v)`
reaches zero and the atom disappears — not a new solution, but an endpoint of the known
one that the upstream positivity analysis excluded by assumption.

Parameterized by the **ratio** `r = B / A` rather than by a quotient written inline: the
masses are then `1/4 + r/4`, `1/4 - r/4`, `1/2`, and the construction contains **no
division at all**. Positivity of the middle mass is exactly `r < 1`, which is exactly
`B < A`, which is exactly `v > 0`. This shape was adopted after a build showed the
divided form failing on renamed division lemmas; it is the same family.

*On the proof style.* The atom vector is written as an explicit finite piecewise function.
This makes `fin_cases` reduce it definitionally and avoids depending on the internal
`Matrix.cons` representation of vector notation. -/
noncomputable def threeAtom (v A B r : ℝ) (hv : 0 ≤ v) (hA : A ^ 2 = 1 + v)
    (hB : B ^ 2 = 1 - v) (hApos : 0 < A) (hBpos : 0 < B)
    (hr0 : 0 < r) (hr1 : r < 1) (hr : B = A * r) :
    SingleModulus 3 v where
  atom := fun j ↦ if j = 0 then A else if j = 1 then -A else -B
  mass := ![1 / 4 + r / 4, 1 / 4 - r / 4, 1 / 2]
  atom_inj := by
    have hBA : B < A := by rw [hr]; nlinarith
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith
  mass_pos := by
    intro j
    fin_cases j
    · show (0:ℝ) < 1 / 4 + r / 4
      linarith
    · show (0:ℝ) < 1 / 4 - r / 4
      linarith
    · show (0:ℝ) < 1 / 2
      norm_num
  mass_sum := by
    rw [Fin.sum_univ_three]
    show (1 / 4 + r / 4) + (1 / 4 - r / 4) + (1 / 2 : ℝ) = 1
    ring
  mean_zero := by
    rw [Fin.sum_univ_three]
    show (1 / 4 + r / 4) * A + (1 / 4 - r / 4) * (-A) + (1 / 2 : ℝ) * (-B) = 0
    rw [hr]; ring
  var_one := by
    rw [Fin.sum_univ_three]
    show (1 / 4 + r / 4) * A ^ 2 + (1 / 4 - r / 4) * (-A) ^ 2
      + (1 / 2 : ℝ) * (-B) ^ 2 = 1
    have hkey : (1 / 4 + r / 4) * A ^ 2 + (1 / 4 - r / 4) * (-A) ^ 2
        + (1 / 2 : ℝ) * (-B) ^ 2 = (1 / 2) * A ^ 2 + (1 / 2) * B ^ 2 := by ring
    rw [hkey, hA, hB]; ring
  modulus_eq := by
    intro j
    fin_cases j
    · exact modulus_of_sq_eq_one_add hv hA
    · exact modulus_of_sq_eq_one_add hv (by simpa using hA)
    · exact modulus_of_sq_eq_one_sub hv (by simpa using hB)

/-- **The rational witness at `v = 3/5`**, which needs no square-root manipulation: with
`B² = 2/5` and `A = 2B`, the masses are exactly `(3/8, 1/8, 1/2)`.

This is the positive control. A search that reports "no `d = 3` family exists for `v > 0`"
must find this one, and the upstream search did not. -/
noncomputable def threeAtomWitness_threeFifths (B : ℝ) (hB : B ^ 2 = 2 / 5)
    (hBpos : 0 < B) : SingleModulus 3 (3 / 5) := by
  refine threeAtom (3 / 5) (2 * B) B (1 / 2) (by norm_num) ?_ (by rw [hB]; norm_num)
    (by linarith) hBpos (by norm_num) (by norm_num) (by ring)
  rw [show (2 * B) ^ 2 = 4 * B ^ 2 by ring, hB]; norm_num

/-- **The `v = 1` family: atoms `(√2, -√2, 0)` with masses `(1/4, 1/4, 1/2)`.**

At `v = 1` the value `√(1-v)` is zero, so the two `(1-v)`-side atoms of the upstream
parameterization collide and `d = 4` becomes impossible
(`SingleModulus.card_le_three_of_v_eq_one`). What remains is this single family, and it
is genuinely a family: all three masses are positive, the mean is zero because the
`±√2` atoms carry equal mass, and the variance is `(1/4)·2 + (1/4)·2 + 0 = 1`.

This is a **second, independent** counterexample to the upstream `d ≤ 3` impossibility,
and a sharper one: it is not a boundary point of the `c`-line but a case the upstream
argument could not have reached at all, since the ratio `√((1+v)/(1-v))` on which that
argument turns is undefined at `v = 1`. -/
noncomputable def threeAtomAtOne (A : ℝ) (hA : A ^ 2 = 2) (hApos : 0 < A) :
    SingleModulus 3 1 where
  atom := fun j ↦ if j = 0 then A else if j = 1 then -A else 0
  mass := ![1 / 4, 1 / 4, 1 / 2]
  atom_inj := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith
  mass_pos := by
    intro j
    fin_cases j
    · show (0:ℝ) < 1 / 4
      norm_num
    · show (0:ℝ) < 1 / 4
      norm_num
    · show (0:ℝ) < 1 / 2
      norm_num
  mass_sum := by
    rw [Fin.sum_univ_three]
    show (1 / 4 : ℝ) + 1 / 4 + 1 / 2 = 1
    norm_num
  mean_zero := by
    rw [Fin.sum_univ_three]
    show (1 / 4 : ℝ) * A + 1 / 4 * (-A) + 1 / 2 * (0 : ℝ) = 0
    ring
  var_one := by
    rw [Fin.sum_univ_three]
    show (1 / 4 : ℝ) * A ^ 2 + 1 / 4 * (-A) ^ 2 + 1 / 2 * (0 : ℝ) ^ 2 = 1
    have hkey : (1 / 4 : ℝ) * A ^ 2 + 1 / 4 * (-A) ^ 2 + 1 / 2 * (0 : ℝ) ^ 2
        = (1 / 2) * A ^ 2 := by ring
    rw [hkey, hA]; norm_num
  modulus_eq := by
    intro j
    fin_cases j
    · show |A ^ 2 - 1| = 1
      rw [hA]; norm_num
    · show |(-A) ^ 2 - 1| = 1
      rw [show (-A) ^ 2 = A ^ 2 by ring, hA]; norm_num
    · show |(0:ℝ) ^ 2 - 1| = 1
      norm_num

/-- **The upstream `d = 4` line, which is correct.**

Atoms `A, -A, B, -B` with masses `1/4 + cB, 1/4 - cB, 1/4 - cA, 1/4 + cA`. The mean
identity holds for *every* `c` — the two cross terms `cAB` cancel identically — and the
variance identity is insensitive to `c` for the same reason. So `c` is a genuinely free
parameter, and the only constraint is positivity: `|c| * A < 1/4`.

At the endpoints `|c| * A = 1/4` one mass vanishes and the family drops to the `d = 3`
family above. That is the whole correction, in one sentence: the parameter interval is
**closed**, and its endpoints are families, not empty. -/
noncomputable def fourAtom (v A B c : ℝ) (hv : 0 ≤ v) (hA : A ^ 2 = 1 + v)
    (hB : B ^ 2 = 1 - v) (hApos : 0 < A) (hBpos : 0 < B) (hBA : B < A)
    (hc : |c| * A < 1 / 4) :
    SingleModulus 4 v where
  -- The branch conditions compare `j.val`, a natural-number literal, rather than `j`
  -- itself. `fin_cases` leaves `j` as a raw `Fin.mk`, and `⟨2, _⟩ = 2` does NOT reduce,
  -- because the right-hand side is an `OfNat` literal while the left is a `Fin.mk`:
  -- `norm_num` gets through `⟨0, _⟩ = 0` and `⟨1, _⟩ = 1` and then stalls, leaving
  -- `hij : A = if ⟨2, ⋯⟩ = 2 then B else -B` with the `if` intact. Comparing `.val`
  -- makes every branch reduce definitionally, with no `Fin` lemma name to get wrong.
  atom := fun j ↦
    if j.val = 0 then A else if j.val = 1 then -A else if j.val = 2 then B else -B
  mass := ![1 / 4 + c * B, 1 / 4 - c * B, 1 / 4 - c * A, 1 / 4 + c * A]
  atom_inj := by
    intro i j hij
    -- `exfalso` supplies the `False` goal that `linarith` needs; `norm_num` leaves the
    -- goal as a `Fin 4` equality, which `linarith` cannot prove. `<;>` runs nothing on a
    -- branch with no goals, so cases already closed by `norm_num` are unaffected.
    fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> exfalso <;> linarith
  mass_pos := by
    intro j
    have hcA : |c * A| < 1 / 4 := by
      rw [abs_mul, abs_of_pos hApos]; exact hc
    have hcB : |c * B| < 1 / 4 := by
      rw [abs_mul, abs_of_pos hBpos]
      have hmul : |c| * B ≤ |c| * A :=
        mul_le_mul_of_nonneg_left (le_of_lt hBA) (abs_nonneg c)
      linarith
    have h1 := abs_lt.mp hcA
    have h2 := abs_lt.mp hcB
    fin_cases j
    · show (0:ℝ) < 1 / 4 + c * B
      linarith [h2.1, h2.2]
    · show (0:ℝ) < 1 / 4 - c * B
      linarith [h2.1, h2.2]
    · show (0:ℝ) < 1 / 4 - c * A
      linarith [h1.1, h1.2]
    · show (0:ℝ) < 1 / 4 + c * A
      linarith [h1.1, h1.2]
  mass_sum := by
    rw [Fin.sum_univ_four]
    show (1 / 4 + c * B) + (1 / 4 - c * B) + (1 / 4 - c * A) + (1 / 4 + c * A) = 1
    ring
  mean_zero := by
    rw [Fin.sum_univ_four]
    show (1 / 4 + c * B) * A + (1 / 4 - c * B) * (-A) + (1 / 4 - c * A) * B
      + (1 / 4 + c * A) * (-B) = 0
    ring
  var_one := by
    rw [Fin.sum_univ_four]
    show (1 / 4 + c * B) * A ^ 2 + (1 / 4 - c * B) * (-A) ^ 2
      + (1 / 4 - c * A) * B ^ 2 + (1 / 4 + c * A) * (-B) ^ 2 = 1
    have hkey : (1 / 4 + c * B) * A ^ 2 + (1 / 4 - c * B) * (-A) ^ 2
        + (1 / 4 - c * A) * B ^ 2 + (1 / 4 + c * A) * (-B) ^ 2
        = (1 / 2) * A ^ 2 + (1 / 2) * B ^ 2 := by ring
    rw [hkey, hA, hB]; ring
  modulus_eq := by
    intro j
    fin_cases j
    · exact modulus_of_sq_eq_one_add hv hA
    · exact modulus_of_sq_eq_one_add hv (by simpa using hA)
    · exact modulus_of_sq_eq_one_sub hv hB
    · exact modulus_of_sq_eq_one_sub hv (by simpa using hB)

/-!
## The three families, with no parameter left free

Each construction above still takes its atoms abstractly -- `threeAtomWitness_threeFifths`
wants a `B` with `B² = 2/5`, `threeAtomAtOne` an `A` with `A² = 2`, `fourAtom` both. A
construction parameterized that way refutes nothing on its own: the caller still has to
supply the square roots, and until someone does, the correction to the upstream `d ≤ 3`
claim is a family conditional on an unmet hypothesis rather than an existence statement.

The three corollaries below supply them, so the counterexamples stand as closed claims.
They are separate from `SingleModulus.nonempty`, which is about `SingleModulus 2 0`; these
inhabit `3 (3/5)`, `3 1` and `4 v` for `0 < v < 1`, which are the cases the upstream
`d ≤ 3` impossibility claim covers.
-/

/-- **The `v = 3/5` three-atom family exists**, at `B = √(2/5)`. -/
theorem nonempty_singleModulus_three_threeFifths :
    Nonempty (SingleModulus 3 (3 / 5 : ℝ)) :=
  ⟨threeAtomWitness_threeFifths (Real.sqrt (2 / 5))
    (Real.sq_sqrt (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))⟩

/-- **The `v = 1` three-atom family exists**, at `A = √2`. This is the case the upstream
ratio argument could not reach at all, since `√((1+v)/(1-v))` is undefined at `v = 1`. -/
theorem nonempty_singleModulus_three_one :
    Nonempty (SingleModulus 3 (1 : ℝ)) :=
  ⟨threeAtomAtOne (Real.sqrt 2) (Real.sq_sqrt (by norm_num))
    (Real.sqrt_pos.mpr (by norm_num))⟩

/-- **The four-atom line is nonempty for every `0 < v < 1`**, at `c = 0` -- the midpoint
of the closed parameter interval, where all four masses are exactly `1/4`. -/
theorem nonempty_singleModulus_four (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    Nonempty (SingleModulus 4 v) :=
  ⟨fourAtom v (Real.sqrt (1 + v)) (Real.sqrt (1 - v)) 0 hv0.le
    (Real.sq_sqrt (by linarith)) (Real.sq_sqrt (by linarith))
    (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
    (Real.sqrt_lt_sqrt (by linarith) (by linarith))
    (by norm_num)⟩

end Descent.BundleRigidity
