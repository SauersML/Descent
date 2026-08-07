/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Strand as a `Bool` gauge, and the obstruction an inversion is

`Descent.Pangenome.Construction` takes an aligner's report to be a relation on positions and
asks what quotienting by it costs.  It leaves out half of what an aligner reports.  An
alignment between two sequences carries an ORIENTATION: the segments match either as read or
reverse-complemented, and a builder must record which.

That extra bit is a gauge in the exact sense.  Flipping the strand convention at one position
changes no fact about the genome, only the bookkeeping; a quantity that moves under the flip
is about the bookkeeping.  So the natural home for the data is not `Pos` but `Pos × Bool` --
each position together with a choice of reading direction -- and an alignment identifies
`(p, b)` with `(q, b `xor` s)` where `s` says whether the alignment inverts.

## The obstruction

Walk a closed chain of alignments and multiply the flips.  If the product is `true` you come
back to the position you started from with the opposite strand, and the identification forces
`(p, false)` and `(p, true)` into one class.  That is `Frustrated`.

`frustratedTriangle` is three positions and three alignments -- two direct and one inverted --
whose closure is frustrated, and it is the smallest such thing.  This is an inversion
polymorphism written down: nothing local is wrong, no single alignment is suspect, and the
inconsistency exists only around the cycle.

The word for the product-around-a-cycle is holonomy, and the reason to resist calling it
curvature is that a graph has no infinitesimals to take curvature of.  There is no local
defect anywhere; the whole invariant is the cycle sum, and `frustratedTriangle_frustrated`
shows the invariant is not always trivial.

## What frustration costs, exactly

A `GaugeFixing` is a global choice of reading direction -- one bit per position -- consistent
with every alignment simultaneously.  It is what "lay down a linear reference coordinate"
means when the coordinate is only required to fix strand.

`not_frustrated_of_gaugeFixing` is the theorem: **a frustrated alignment set admits no gauge
fixing at all.**  So the failure is not that a linear reference is awkward or lossy near an
inversion; it is that no linear reference exists, and any pipeline that produces one has
discarded an alignment to get it.  `frustratedTriangle_no_gaugeFixing` states that for the
explicit witness, so the claim rests on an exhibited object rather than a genericity
argument.

The converse direction has a clean partial form here:
`gaugeFixing_const_of_no_inversion` says an alignment set with no inverted alignment is gauge
fixed by the constant convention.  So frustration requires inversions, and where the genome
has none the classical picture is not merely adequate -- it is exactly correct.  **The defect
is localised to the inverted loci and is absent everywhere else**, which is the formal content
of the observation that graph representations pay off at specific places rather than
uniformly.

## Relation to the other indeterminacy

This is a gauge and `Descent.Pangenome.Construction`'s is not, and the two must not be
treated alike.  A strand convention acts on the fiber over a position and changes no fact, so
a strand-dependent quantity is meaningless and the remedy is an invariance requirement.  A
construction choice changes which quotient you took, so the objects genuinely differ and the
remedy is a bracket.  Conflating them prescribes the wrong repair for one of the two.

## Empirical status

None.  The bodies are definitions and lemmas about an equivalence relation generated on
`Pos × Bool`.  Whether a given locus is frustrated in a real panel is the empirical question
and is not settled here.

## Main results

- `frustratedTriangle_frustrated`: **holonomy is not always trivial.**  Three alignments,
  one inverted, and a position identified with its own reverse complement.
- `not_frustrated_of_gaugeFixing`: **frustration forbids a global reference.**  No consistent
  strand assignment exists once a cycle is frustrated.
- `frustratedTriangle_no_gaugeFixing`: the same for the exhibited witness.
- `gaugeFixing_const_of_no_inversion`: without inverted alignments the reference exists, so
  the obstruction is localised to inversions.
-/

namespace Descent.Pangenome.Strand

open Relation

/-! ### The doubled position set -/

/-- **The identification a signed alignment set makes on oriented positions.**

`S p q s` reads "`p` aligns to `q`, inverted iff `s`".  The alignment identifies position `p`
read in direction `b` with position `q` read in direction `b `xor` s`, which is the whole
content of recording an orientation.

Empirical status: NOT AN EMPIRICAL CLAIM.  It transports a reported relation to `Pos × Bool`;
which alignments a real aligner reports is not settled here. -/
def doubled {Pos : Type*} (S : Pos → Pos → Bool → Prop) :
    (Pos × Bool) → (Pos × Bool) → Prop :=
  fun a b => ∃ s, S a.1 b.1 s ∧ b.2 = xor a.2 s

/-- **A frustrated alignment set** is one whose identifications force some position into a
class with its own reverse complement.  Equivalently: some closed chain of alignments has an
odd number of inversions, so its holonomy is the flip.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names a property of a reported relation;
`frustratedTriangle_frustrated` witnesses that the property is satisfiable, and whether a
given locus has it is empirical and not settled here. -/
def Frustrated {Pos : Type*} (S : Pos → Pos → Bool → Prop) : Prop :=
  ∃ p : Pos, EqvGen (doubled S) (p, false) (p, true)

/-- **A gauge fixing** is a global choice of reading direction consistent with every
alignment at once: one bit per position whose difference across an alignment is exactly that
alignment's inversion bit.  This is what a linear reference coordinate provides, restricted
to what it says about strand.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names a compatibility between a reported
relation and an assignment; `gaugeFixing_const_of_no_inversion` witnesses that the property
is satisfiable. -/
def GaugeFixing {Pos : Type*} (S : Pos → Pos → Bool → Prop) (g : Pos → Bool) : Prop :=
  ∀ p q s, S p q s → g q = xor (g p) s

/-! ### A gauge fixing is a conserved quantity -/

/-- **The invariant a gauge fixing defines.**  If `g` is consistent with every alignment then
`xor (g p) b` is unchanged by every identification, hence constant on each class of the
generated equivalence relation.

This is the whole mechanism: a global strand convention turns the alignment identifications
into moves that preserve a single bit, and a frustrated cycle is precisely a closed sequence
of moves that flips it. -/
theorem xor_eq_of_eqvGen {Pos : Type*} {S : Pos → Pos → Bool → Prop} {g : Pos → Bool}
    (hg : GaugeFixing S g) {a b : Pos × Bool} (h : EqvGen (doubled S) a b) :
    xor (g a.1) a.2 = xor (g b.1) b.2 := by
  induction h with
  | rel x y hxy =>
      obtain ⟨s, hS, hy⟩ := hxy
      have hgy : g y.1 = xor (g x.1) s := hg _ _ _ hS
      rw [hgy, hy]
      cases g x.1 <;> cases x.2 <;> cases s <;> rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Frustration forbids a global reference.**

If any closed chain of alignments returns a position to itself with the opposite strand, then
no assignment of reading directions is consistent with every alignment -- because such an
assignment would have to make one bit both equal and unequal to itself.

This is the load-bearing statement of the file.  It says the difficulty at an inversion is
not that a linear coordinate is lossy there: it is that no linear coordinate exists, and a
pipeline that outputs one has necessarily dropped an alignment.  The two repair moves of
`Descent.Pangenome.Construction` reappear here as the only options, and neither is free. -/
theorem not_frustrated_of_gaugeFixing {Pos : Type*} {S : Pos → Pos → Bool → Prop}
    {g : Pos → Bool} (hg : GaugeFixing S g) : ¬ Frustrated S := by
  rintro ⟨p, hp⟩
  have h2 : xor (g p) false = xor (g p) true := xor_eq_of_eqvGen hg hp
  revert h2
  generalize g p = b
  cases b <;> decide

/-! ### The obstruction is real, and it is localised -/

/-- Three positions and three alignments: `0` to `1` direct, `1` to `2` direct, and `2` back
to `0` INVERTED.  Every alignment is individually unremarkable and the inconsistency exists
only around the cycle.  This is an inversion polymorphism in the smallest form that has one.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is an explicit finite relation exhibited to
witness that frustration occurs; it models no particular locus. -/
def frustratedTriangle : Fin 3 → Fin 3 → Bool → Prop := fun p q s =>
  (p = 0 ∧ q = 1 ∧ s = false) ∨ (p = 1 ∧ q = 0 ∧ s = false) ∨
  (p = 1 ∧ q = 2 ∧ s = false) ∨ (p = 2 ∧ q = 1 ∧ s = false) ∨
  (p = 2 ∧ q = 0 ∧ s = true) ∨ (p = 0 ∧ q = 2 ∧ s = true)

instance (p q : Fin 3) (s : Bool) : Decidable (frustratedTriangle p q s) := by
  unfold frustratedTriangle; infer_instance

/-- The first leg: `0` read forward meets `1` read forward. -/
theorem triangle_step_one : doubled frustratedTriangle (0, false) (1, false) := by
  unfold doubled
  exact ⟨false, by decide, by decide⟩

/-- The second leg: `1` read forward meets `2` read forward. -/
theorem triangle_step_two : doubled frustratedTriangle (1, false) (2, false) := by
  unfold doubled
  exact ⟨false, by decide, by decide⟩

/-- The closing leg, and the one that inverts: `2` read forward meets `0` read BACKWARD. -/
theorem triangle_step_three : doubled frustratedTriangle (2, false) (0, true) := by
  unfold doubled
  exact ⟨true, by decide, by decide⟩

/-- **Holonomy is not always trivial.**  Following the three alignments around the cycle
returns position `0` to itself with the opposite strand, so the generated equivalence
relation puts `(0, false)` and `(0, true)` in one class.

Nothing local is wrong here.  Each of the three alignments is consistent with the others
pairwise; the defect appears only on the closed walk, which is why it cannot be found or
repaired by examining alignments one at a time. -/
theorem frustratedTriangle_frustrated : Frustrated frustratedTriangle :=
  ⟨0, EqvGen.trans _ _ _
      (EqvGen.trans _ _ _ (EqvGen.rel _ _ triangle_step_one)
        (EqvGen.rel _ _ triangle_step_two))
      (EqvGen.rel _ _ triangle_step_three)⟩

/-- **No linear reference exists for the frustrated triangle.**  Not "none is convenient" and
not "the best one is lossy": there is no assignment of reading directions to three positions
consistent with three alignments.  A builder handed this input must discard one of them. -/
theorem frustratedTriangle_no_gaugeFixing (g : Fin 3 → Bool) :
    ¬ GaugeFixing frustratedTriangle g :=
  fun h => not_frustrated_of_gaugeFixing h frustratedTriangle_frustrated

/-- **Without inversions the reference exists.**  An alignment set reporting no inverted
alignment is gauge fixed by the constant convention, so it is unfrustrated.

With `not_frustrated_of_gaugeFixing` this localises the obstruction: frustration REQUIRES an
inverted alignment, so wherever a genome has none, a global strand coordinate exists and the
classical coordinate-based picture is not an approximation but exact.  The defect lives at
the inverted loci and nowhere else. -/
theorem gaugeFixing_const_of_no_inversion {Pos : Type*} {S : Pos → Pos → Bool → Prop}
    (h : ∀ p q s, S p q s → s = false) : GaugeFixing S (fun _ => false) := by
  intro p q s hS
  rw [h p q s hS]
  rfl

/-- **Frustration requires an inversion**, stated as the contrapositive that a consumer can
use: an alignment set that is frustrated has reported at least one inverted alignment. -/
theorem exists_inversion_of_frustrated {Pos : Type*} {S : Pos → Pos → Bool → Prop}
    (h : Frustrated S) : ∃ p q s, S p q s ∧ s = true := by
  by_contra hc
  push_neg at hc
  exact not_frustrated_of_gaugeFixing
    (gaugeFixing_const_of_no_inversion (fun p q s hS => by
      cases s with
      | false => rfl
      | true => exact absurd rfl (hc p q true hS))) h

end Descent.Pangenome.Strand
