/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Descent.Core.Ratios
import Descent.Layer
import Descent.Pangenome.Presentation

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# What a symmetry forbids, and what it forbids it from being

`Descent.Pangenome.Strand` exhibits one symmetry of a pangenome -- the strand convention --
and shows it can be obstructed.  This file asks the prior question: supposing a symmetry acts
and the model is invariant under it, which quantities are allowed to be estimands at all?

The answer is not the one usually reached for.  It is tempting to say that a quantity moved
by a symmetry has expectation zero, and to cite the lattice-gauge theorem that local gauge
symmetry cannot be spontaneously broken.  Both moves are wrong here, in different ways.

**The vanishing claim is false.**  A symmetry-variant quantity does NOT generally have
expectation zero; it has the expectation of its ORBIT AVERAGE, which is usually not zero.
`sum_weight_mul_orbitAverage` is the correct statement, and it is strictly more useful than
the false one, because it is constructive: it does not merely reject a statistic, it names
the admissible quantity that statistic was estimating all along.

**The theorem is not needed.**  The lattice-gauge result is about spontaneous breaking in the
thermodynamic limit, and its content is that the symmetry survives a boundary field sent to
zero after infinite volume.  Nothing here has a thermodynamic limit.  What is actually being
used is averaging over a finite orbit, which is elementary, holds exactly at finite size, and
carries a premise that must be stated: **the weight must itself be invariant**
(`hμ` below).  That premise is a modelling assumption about how the graph was built, and it
is the kind of assumption this corpus names rather than hides.

## The repeat array, which is where this bites

The copies of a tandem array carry a free transitive cyclic action with no canonical first
copy, so "copy `k`" is a choice of register and not a feature of the genome.
`shiftInvariant_sum` and `first_copy_not_shiftInvariant` are the two halves: a symmetric
summary of the copies survives a change of register, and a per-copy readout does not.

Nothing about the second is subtle -- it is two copies and a relabelling -- and that is the
point.  A per-copy statistic is not a hard quantity to estimate; it is not a quantity.

## Empirical status

None.  The bodies are definitions and lemmas about a finite group acting on a finite type and
about `ZMod n`.  Which loci carry repeat arrays, and how large their registers are, are
empirical questions and are not settled here.

## Main results

- `orbitSum_smul`: the orbit sum is constant along orbits, hence a genuine function of the
  invariant content.
- `sum_weight_mul_orbitAverage`: **every estimand is invariant.**  Under an invariant weight,
  a statistic and its orbit average have the same expectation, so what a symmetry-variant
  statistic estimates is its orbit average.
- `shiftInvariant_sum`, `first_copy_not_shiftInvariant`: the repeat array, both ways.
- `registerPresentationIso`: every cyclic choice of first copy is one categorical
  presentation object up to isomorphism.
-/

namespace Descent.Pangenome.Register

open CategoryTheory

/-! ### Averaging over a finite orbit -/

/-- **The orbit sum of a statistic at a point**: the total of `f` over the orbit of `x`,
counted with multiplicity in the group.  Summing rather than averaging keeps the definition
free of a division and so free of a nonvanishing side condition.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is an average of a given function over a given
group action; which group acts on a real pangenome is not settled here. -/
def orbitSum (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    (f : X → ℝ) (x : X) : ℝ :=
  ∑ g : G, f (g • x)

/-- **The orbit sum is constant along orbits.**  Moving the argument by a group element
permutes the terms of the sum and nothing else, so the orbit sum depends only on the orbit --
that is, only on the part of `x` the symmetry does not move.

This is what makes it the canonical invariant replacement for `f` rather than one of many. -/
theorem orbitSum_smul (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    (f : X → ℝ) (h : G) (x : X) : orbitSum G f (h • x) = orbitSum G f x :=
  Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g ↦ congrArg f (mul_smul g h x).symm)

/-- **The orbit average**: the orbit sum divided by the order of the group. -/
noncomputable def orbitAverage (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    (f : X → ℝ) (x : X) : ℝ :=
  orbitSum G f x / (Fintype.card G : ℝ)

/-- **The divisor is the group's order, not the orbit's size.**  Stated through
`Descent.Core.ratio` so the denominator is visible rather than buried in the definition.

The two differ, and the difference is not a technicality: by orbit-stabiliser an orbit has
`|G| / |stabiliser|` points, so whenever a point is fixed by part of the group the orbit sum
visits each of its images several times and `orbitAverage` is a MULTIPLICITY-weighted mean
rather than a uniform one over distinct images.  That is the right choice here -- it is what
makes `sum_weight_mul_orbitAverage` hold with no hypothesis about stabilisers -- but a reader
who assumed "average over the orbit" would have the wrong denominator, so it is recorded. -/
theorem orbitAverage_eq_ratio (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    (f : X → ℝ) (x : X) :
    orbitAverage G f x = Descent.Core.ratio (orbitSum G f x) (Fintype.card G : ℝ) := rfl

/-- **The weights sum to one.**  Averaging a constant returns it, for every group and every
point.

This is the law that fails if the normalisation drifts: an `orbitSum` divided by the orbit
size, or by `|G| - 1`, or left undivided, all break here while leaving every other statement
in the file looking correct.  It is a partition of unity for the orbit weights and the reason
`sum_weight_mul_orbitAverage` can be read as "same expectation" rather than "same up to a
factor". -/
theorem orbitAverage_const (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    (c : ℝ) (x : X) : orbitAverage G (fun _ ↦ c) x = c := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold orbitAverage orbitSum
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The weighted orbit sum, resummed.**  If the weight is invariant then every group element
contributes the same total, so the whole double sum collapses to `|G|` copies of one.

This is the computational core; `sum_weight_mul_orbitAverage` is its useful form. -/
theorem sum_weight_mul_orbitSum (G : Type*) [Group G] [Fintype G] {X : Type*} [MulAction G X]
    [Fintype X] (μ : X → ℝ) (hμ : ∀ (g : G) (x : X), μ (g • x) = μ x) (f : X → ℝ) :
    (∑ x, μ x * orbitSum G f x) = (Fintype.card G : ℝ) * ∑ x, μ x * f x := by
  have key : ∀ g : G, (∑ x, μ x * f (g • x)) = ∑ x, μ x * f x := fun g ↦
    Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun x ↦ by
      show μ x * f (g • x) = μ (g • x) * f (g • x)
      rw [hμ g x])
  calc (∑ x, μ x * orbitSum G f x)
      = ∑ x, ∑ g : G, μ x * f (g • x) := by
        simp only [orbitSum, Finset.mul_sum]
    _ = ∑ g : G, ∑ x, μ x * f (g • x) := Finset.sum_comm
    _ = ∑ _g : G, ∑ x, μ x * f x := Finset.sum_congr rfl (fun g _ ↦ key g)
    _ = (Fintype.card G : ℝ) * ∑ x, μ x * f x := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Every estimand is invariant.**

Under a weight the symmetry preserves, a statistic and its orbit average have exactly the
same expectation.  So a symmetry-variant statistic is not estimating nothing, and it is not
estimating zero: it is estimating its own orbit average, which is an invariant quantity.

This is the admissibility filter in its correct and constructive form.  Reporting a
frame-dependent number is reporting an invariant number, obtained by a needlessly noisy
route, and the invariant one is named by this theorem rather than left to be guessed.  The
premise `hμ` is the whole strength of the conclusion and is stated rather than assumed: if
the construction is not symmetric, nothing here applies. -/
theorem sum_weight_mul_orbitAverage (G : Type*) [Group G] [Fintype G] {X : Type*}
    [MulAction G X] [Fintype X] (μ : X → ℝ) (hμ : ∀ (g : G) (x : X), μ (g • x) = μ x)
    (f : X → ℝ) : (∑ x, μ x * orbitAverage G f x) = ∑ x, μ x * f x := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := sum_weight_mul_orbitSum G μ hμ f
  calc (∑ x, μ x * orbitAverage G f x)
      = (∑ x, μ x * orbitSum G f x) / (Fintype.card G : ℝ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun x _ ↦ by
          simp only [orbitAverage, mul_div_assoc])
    _ = ((Fintype.card G : ℝ) * ∑ x, μ x * f x) / (Fintype.card G : ℝ) := by rw [h]
    _ = ∑ x, μ x * f x := by field_simp

/-! ### The repeat array has no first copy -/

/-- **A change of register on a repeat array of `n` copies.**  The copies are indexed by
`ZMod n` because the array carries a free transitive cyclic action and nothing distinguishes
a starting point; `shift k` is the relabelling that starts counting `k` copies later.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a reindexing of a function on `ZMod n`. -/
def shift {n : ℕ} (k : ZMod n) (a : ZMod n → ℝ) : ZMod n → ℝ := fun i ↦ a (i + k)

/-- **A cyclic register as a pangenome presentation.**  Position `i` receives coordinate
`i + k`, so changing `k` changes only which copy is called first.  Addition by `k` is
surjective, hence no coordinate is dead.

Empirical status: NOT AN EMPIRICAL CLAIM. -/
def registerPresentation {n : ℕ} (k : ZMod n) : Presentation (ZMod n) where
  Coord := ZMod n
  encode i := i + k
  onto := (Equiv.addRight k).surjective

/-- A cyclic register identifies no distinct copies, independently of where counting starts. -/
@[simp]
theorem kernel_registerPresentation {n : ℕ} (k : ZMod n) :
    (registerPresentation k).kernel = ⊥ := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    exact add_right_cancel ((Presentation.kernel_rel_iff (registerPresentation k) x y).mp h)
  · intro h
    exact (Presentation.kernel_rel_iff (registerPresentation k) x y).mpr
      (congrArg (fun z ↦ z + k) h)

/-- **Every choice of first repeat copy is the same presentation.**  The existing group
action and the categorical notion of presentation equivalence therefore agree on the cyclic
register example. -/
noncomputable def registerPresentationIso {n : ℕ} (k l : ZMod n) :
    registerPresentation k ≅ registerPresentation l :=
  Presentation.isoOfKernelEq (by rw [kernel_registerPresentation, kernel_registerPresentation])

/-- Every representation-invariant pangenome statistic ignores the choice of first copy. -/
theorem invariant_registerPresentation {n : ℕ} {Value : Type*}
    (F : Presentation (ZMod n) → Value) (hF : Presentation.IsInvariant F)
    (k l : ZMod n) : F (registerPresentation k) = F (registerPresentation l) :=
  hF _ _ ⟨registerPresentationIso k l⟩

/-- **A summary of a repeat array is register-invariant** when no change of register moves
it.  Only such summaries are functions of the array; the rest are functions of the labelling.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names a property of a summary functional;
`shiftInvariant_sum` witnesses that the property is satisfiable. -/
def RegisterInvariant {n : ℕ} (F : (ZMod n → ℝ) → ℝ) : Prop :=
  ∀ (k : ZMod n) (a : ZMod n → ℝ), F (shift k a) = F a

/-- **A symmetric summary survives the register.**  The total over the copies is unchanged by
relabelling, because relabelling permutes the terms.  Any function of the multiset of copy
values is invariant for the same reason; the sum is the instance that carries the witness. -/
theorem shiftInvariant_sum {n : ℕ} [NeZero n] :
    RegisterInvariant (n := n) (fun a ↦ ∑ i, a i) := by
  intro k a
  exact Fintype.sum_equiv (Equiv.addRight k) _ _ (fun i ↦ rfl)

/-- **A per-copy readout does not survive the register.**

Two copies and one relabelling suffice: the array whose first copy reads `0` and whose second
reads `1` has its "first copy" statistic moved by the shift.  So "the value at copy `k`" is
not a quantity a repeat array has, and any statistic defined by reference to a numbered copy
is a statistic about the annotation.

`sum_weight_mul_orbitAverage` says what such a statistic is nevertheless estimating: the
average over the register, which is `shiftInvariant_sum` up to a factor.  This is why the
construction-difference peaks reported at tandem repeats are not evidence that repeats are
hard to align -- they are what a frame-dependent readout looks like when the frame moves. -/
theorem first_copy_not_shiftInvariant :
    ¬ RegisterInvariant (n := 2) (fun a ↦ a 0) := by
  intro h
  have h1 := h 1 (fun i ↦ if i = 0 then (0 : ℝ) else 1)
  simp [shift] at h1

end Descent.Pangenome.Register
