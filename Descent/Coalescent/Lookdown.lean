/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Restriction
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The lookdown construction: why all `n` coalescents fit on one probability space

K-G section 7 wants `n`-coalescents for every `n` on a single probability space and gets them
by a projective limit -- Kakutani-Nelson, a topological argument that produces a measure and
exhibits nothing.  `Descent.Coalescent.Program` records the extension theorem as open, and
`Descent.Coalescent.Encoding` supplies only the measurable structure it would need.

Donnelly and Kurtz (Ann. Probab. 24, 1996; Ann. Appl. Probab. 9, 1999) get the same coupling
by construction instead.  Their device is LEVELS.  Particles sit at levels `1, 2, 3, …`; a
coalescence between levels `i < j` is the particle at level `j` "looking down" at level `i`
and adopting what it finds.  Nothing at a level below `j` is touched -- and that one sentence
is the whole coupling, because it means the dynamics of the first `m` levels never consult
level `m+1` or above.

This file is that sentence, proved.  `lookdownApply i j` is the operation, and the two facts
that make it a coupling are:

* `restrict_lookdownApply`: when `j` is below the cut, restricting to the first `m` levels
  commutes with the operation;
* `restrict_lookdownApply_of_le`: when `j` is at or above the cut, the first `m` levels do
  not change at all.

Together: whatever happens above level `m` is invisible below it.  So the level-`m`
configuration is a function of the level-`m` history alone, for every `m` simultaneously,
on one space, with no measure-theoretic extension anywhere.

`restrict_ker_lookdown` carries this to partitions: the relation "same type" restricted to
the first `m` levels is the relation of the restricted configuration, which is
`Descent.Coalescent.Restriction.restrict`.  So the consistency K-G (7.2) states for
coalescents holds here for every realisation of the construction, exactly as
`Descent.Coalescent.Pedigree` gets it for the Wright-Fisher mechanism.

## What is proved, and what is not

PROVED: the level structure and its consistency, pathwise, for arbitrary configurations --
no probability, no rates, and therefore nothing that could fail for a particular model.

NOT PROVED: that driving the levels with independent rate-one Poisson clocks, one per pair
`i < j`, makes the resulting partition process an `n`-coalescent.  That needs the clocks,
which needs the Poisson processes the corpus does not have; `Descent.Coalescent.CompetingRates`
has the density calculation for one step and `Descent.Coalescent.Law` the coupling of a jump
chain to a clock.  What is closed here is the reason the construction is CONSISTENT, which is
the part K-G obtains topologically and Donnelly-Kurtz obtain by looking down.

## Main results

- `lookdownApply`: level `j` adopts level `i`'s type.
- `restrict_lookdownApply`: **it commutes with restriction below the cut**.
- `restrict_lookdownApply_of_le`: **and is invisible above it**.
- `restrict_ker_lookdown`: the induced partition is consistent, K-G (7.2) pathwise.
-/

namespace Coalescent

/-- **The lookdown operation.**  Level `j` looks down at level `i` and adopts its type;
every other level is untouched.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is an assignment, written down.  Which pairs
look down when is the modelling question, and for Kingman's coalescent the answer is
independent rate-one clocks on each pair. -/
def lookdownApply {n : ℕ} {α : Type*} (i j : Fin n) (c : Fin n → α) : Fin n → α :=
  fun l ↦ if l = j then c i else c l

@[simp] theorem lookdownApply_self {n : ℕ} {α : Type*} (i j : Fin n) (c : Fin n → α) :
    lookdownApply i j c j = c i := by
  unfold lookdownApply
  simp

theorem lookdownApply_of_ne {n : ℕ} {α : Type*} (i j : Fin n) (c : Fin n → α) {l : Fin n}
    (h : l ≠ j) : lookdownApply i j c l = c l := by
  unfold lookdownApply
  simp [h]

/-- **Below the cut, restriction commutes with looking down.**  If the looking level `j` is
among the first `m`, then performing the operation and then restricting is performing the
restricted operation. -/
theorem restrict_lookdownApply {m n : ℕ} (h : m ≤ n) {α : Type*} (i j : Fin n)
    (c : Fin n → α) (hi : (i : ℕ) < m) (hj : (j : ℕ) < m) :
    (lookdownApply i j c) ∘ Fin.castLE h
      = lookdownApply (⟨i, hi⟩ : Fin m) ⟨j, hj⟩ (c ∘ Fin.castLE h) := by
  funext l
  unfold lookdownApply
  by_cases hl : l = (⟨j, hj⟩ : Fin m)
  · have hcast : Fin.castLE h l = j := by
      apply Fin.ext
      simp [hl]
    simp [hcast, hl]
  · have hcast : Fin.castLE h l ≠ j := by
      intro hc
      apply hl
      apply Fin.ext
      have : (l : ℕ) = (j : ℕ) := by
        have := congrArg (Fin.val) hc
        simpa using this
      simpa using this
    simp [hcast, hl]

/-- **Above the cut, looking down is invisible.**  If the looking level `j` is at or beyond
the first `m`, the first `m` levels are unchanged.

This is the half that makes the coupling work: the level-`m` process does not merely commute
with the level-`n` process, it ignores everything the level-`n` process does above `m`. -/
theorem restrict_lookdownApply_of_le {m n : ℕ} (h : m ≤ n) {α : Type*} (i j : Fin n)
    (c : Fin n → α) (hj : m ≤ (j : ℕ)) :
    (lookdownApply i j c) ∘ Fin.castLE h = c ∘ Fin.castLE h := by
  funext l
  unfold lookdownApply
  have hne : Fin.castLE h l ≠ j := by
    intro hc
    have hval : (l : ℕ) = (j : ℕ) := by
      have := congrArg (Fin.val) hc
      simpa using this
    have hlm : (l : ℕ) < m := l.isLt
    omega
  simp [hne]

/-- **The induced partition is consistent.**  "Same type" on the first `m` levels is the
same-type relation of the restricted configuration -- so `Descent.Coalescent.Restriction`'s
`ρ_{mn}` applied to the lookdown's partition is the lookdown's partition at level `m`.

That is K-G (7.2), pathwise, for every configuration and every operation, and it needs no
measure at all. -/
theorem restrict_ker_lookdown {m n : ℕ} (h : m ≤ n) {α : Type*} (c : Fin n → α) :
    restrict h (Setoid.ker c) = Setoid.ker (c ∘ Fin.castLE h) :=
  Setoid.ext fun _ _ ↦ Iff.rfl

/-- The two halves combined: for every pair of levels, the first `m` levels of the partition
after the operation depend only on data at levels below `m`.  Stated as the disjunction the
two lemmas above prove, because that IS the coupling. -/
theorem lookdown_consistent {m n : ℕ} (h : m ≤ n) {α : Type*} (i j : Fin n) (c : Fin n → α) :
    (∀ hj : (j : ℕ) < m, ∀ hi : (i : ℕ) < m,
        restrict h (Setoid.ker (lookdownApply i j c))
          = Setoid.ker (lookdownApply (⟨i, hi⟩ : Fin m) ⟨j, hj⟩ (c ∘ Fin.castLE h)))
      ∧ (m ≤ (j : ℕ) →
        restrict h (Setoid.ker (lookdownApply i j c)) = restrict h (Setoid.ker c)) := by
  constructor
  · intro hj hi
    rw [restrict_ker_lookdown, restrict_lookdownApply h i j c hi hj]
  · intro hj
    rw [restrict_ker_lookdown, restrict_ker_lookdown,
      restrict_lookdownApply_of_le h i j c hj]

end Coalescent

end Descent
