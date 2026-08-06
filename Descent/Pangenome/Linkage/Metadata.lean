/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Barrier

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Where the identity goes when the topology stops carrying it

`Descent.Pangenome.Linkage.Barrier` leaves an interface three options, and proves only two of
them.  Either the topology keeps the thread identities apart, or it merges them and admits
the extra derivations, or it merges them and keeps the missing distinction somewhere else —
a haplotype index, path colours, an automaton state.  That third option is the one every
haplotype-aware index actually takes, and until it is stated it reads like an escape from the
theorem rather than a priced alternative to it.

This file prices it.  A controller at an interface sees the graph state and an auxiliary
value drawn from an alphabet `A`, and it is EXACT when those two together determine whatever
the legal future depends on.  The whole content is a pigeonhole: two threads in one graph
state whose futures differ must carry different auxiliary values.

## The results

* `resolves_id` — the hypothesis is satisfiable: a controller carrying thread identity
  outright resolves everything, so the bound below constrains a real family of controllers
  rather than an empty one.
* `card_le_card_aux_of_resolves` — the local form.  Any set of threads sharing a graph state
  and pairwise-distinguishable futures injects into `A`.
* `card_le_width_mul_card_aux` — the global form, `m ≤ w · |A|`, when the legal future
  identifies the donor.  Read three ways: `w = m` is the topology carrying identity and
  needing no metadata; `|A| = 1` is no metadata, and by `width_eq_card_of_card_aux_eq_one` it
  forces `w = m`; anything in between pays for the merge in the alphabet.
* `card_aux_ge_of_width_le` — the alphabet a fixed compression demands: merging down to width
  `w` requires at least `m / w` auxiliary values, which is the exponential of the identity
  the interface forgot.

## The trade this makes precise

`Descent.Pangenome.Linkage.Barrier.pow_card_le_pow_width_mul_card_mosaics` prices option two
in derivations; `card_aux_ge_of_width_le` prices option three in auxiliary states.  They are
the same quantity `m/w` read on two sides of one interface, which is what makes the choice a
trade rather than a way out.

## What is not claimed

This is a bound on the state an exact controller must have available AT AN INTERFACE.  It is
not a claim that the costs at different interfaces add as storage: one persistent haplotype
identifier can carry identity through many separators, and nothing here forbids that.  What
is forbidden is deciding an exact transition without the distinction being available.

The bound is also the ZERO-ERROR, cardinality form: it counts how many auxiliary values must
be available, not how many bits a controller must hold on average.  The entropy form of the
same trade is not formalised here.

## Empirical status

None.  The results are pigeonhole statements about finite alphabets.  Which index a given
tool actually carries, and how large its alphabet is, is a measurement about that tool and
not a statement proved here.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u v z

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [Fintype A] [DecidableEq A]
variable {R : Type z}

/-- A controller with auxiliary state `aux` RESOLVES the residual class `ρ` at interface `s`
when the graph state and the auxiliary state together determine it.  `ρ h` is whatever the
legal continuations after arriving on thread `h` depend on; when the panel's suffixes
identify their thread, `ρ` is injective and resolving it means recovering the donor. -/
def Resolves (s : ι → ι) (aux : ι → A) (ρ : ι → R) : Prop :=
  ∀ g h : ι, s g = s h → aux g = aux h → ρ g = ρ h

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
/-- **The hypothesis is satisfiable, and by the obvious controller.**  Auxiliary state that
carries the thread identity outright resolves every residual class, whatever the topology has
merged: the full haplotype index is always a legal answer.  It is also the most expensive one,
since it needs `|A| = m`, which is the extreme `card_le_width_mul_card_aux` permits at `w = 1`
and the reason that bound is a trade rather than an obstruction. -/
theorem resolves_id (s : ι → ι) (ρ : ι → R) : Resolves s (id : ι → ι) ρ :=
  fun _ _ _ haux ↦ congrArg ρ haux

/-- **The local form.**  Threads sharing a graph state but needing different futures must
carry different auxiliary values, so any such set injects into the auxiliary alphabet. -/
theorem card_le_card_aux_of_resolves {s : ι → ι} {aux : ι → A} {ρ : ι → R}
    (hres : Resolves s aux ρ) {a : ι} (t : Finset ι) (ht : t ⊆ stateFiber s a)
    (hinj : ∀ g ∈ t, ∀ h ∈ t, ρ g = ρ h → g = h) :
    t.card ≤ Fintype.card A := by
  have hauxinj : ∀ g ∈ t, ∀ h ∈ t, aux g = aux h → g = h := by
    intro g hg h hh haux
    have hsg : s g = a := mem_stateFiber.mp (ht hg)
    have hsh : s h = a := mem_stateFiber.mp (ht hh)
    exact hinj g hg h hh (hres g h (by rw [hsg, hsh]) haux)
  calc t.card = (t.image aux).card := (Finset.card_image_of_injOn hauxinj).symm
    _ ≤ Fintype.card A := by
        simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (t.image aux))

/-- **The global form: `m ≤ w · |A|`.**  When the legal future identifies the donor -- `ρ`
separating any two threads that share a graph state -- an exact controller needs an auxiliary
alphabet large enough that state and metadata together separate every thread the panel
distinguishes.

Assumes: `Resolves s aux ρ`, which is the exactness of the controller and not a fact about
any graph; `resolves_id` establishes it for the controller that carries thread identity. -/
theorem card_le_width_mul_card_aux (s : ι → ι) (aux : ι → A) (ρ : ι → R)
    (hres : Resolves s aux ρ) (hρ : ∀ g h : ι, s g = s h → ρ g = ρ h → g = h) :
    Fintype.card ι ≤ width s * Fintype.card A := by
  have hinj : Function.Injective fun h : ι ↦ (s h, aux h) := by
    intro g h hgh
    have hs : s g = s h := congrArg Prod.fst hgh
    exact hρ g h hs (hres g h hs (congrArg Prod.snd hgh))
  have hsub : (Finset.univ.image fun h : ι ↦ (s h, aux h))
      ⊆ (Finset.univ.image s) ×ˢ (Finset.univ.image aux) := by
    intro p hp
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem s (Finset.mem_univ h),
        Finset.mem_image_of_mem aux (Finset.mem_univ h)⟩
  have haux : (Finset.univ.image aux).card ≤ Fintype.card A := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (Finset.univ.image aux))
  calc Fintype.card ι
      = (Finset.univ.image fun h : ι ↦ (s h, aux h)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ ((Finset.univ.image s) ×ˢ (Finset.univ.image aux)).card := Finset.card_le_card hsub
    _ = width s * (Finset.univ.image aux).card := Finset.card_product _ _
    _ ≤ width s * Fintype.card A := Nat.mul_le_mul_left _ haux

/-- **No metadata means no merging.**  A single auxiliary value carries no information, so an
exact controller with one is a topology that kept every thread identity apart — the same
conclusion `width_eq_card_of_card_mosaics_eq` reaches from the phantom side. -/
theorem width_eq_card_of_card_aux_eq_one (s : ι → ι) (aux : ι → A) (ρ : ι → R)
    (hone : Fintype.card A = 1) (hres : Resolves s aux ρ)
    (hρ : ∀ g h : ι, s g = s h → ρ g = ρ h → g = h) :
    width s = Fintype.card ι :=
  le_antisymm (width_le_card s)
    (by simpa [hone] using card_le_width_mul_card_aux s aux ρ hres hρ)

/-- **What a fixed compression costs in metadata.**  Merging an interface down to width `w`
obliges an exact controller to carry at least `m / w` auxiliary values — the exponential of
the identity `identityLoss` says the merge discarded. -/
theorem card_aux_ge_of_width_le {w₀ : ℕ} (s : ι → ι) (aux : ι → A) (ρ : ι → R)
    (hw : width s ≤ w₀) (hres : Resolves s aux ρ)
    (hρ : ∀ g h : ι, s g = s h → ρ g = ρ h → g = h) :
    Fintype.card ι ≤ w₀ * Fintype.card A :=
  le_trans (card_le_width_mul_card_aux s aux ρ hres hρ) (Nat.mul_le_mul_right _ hw)

end Descent.Pangenome.Linkage
