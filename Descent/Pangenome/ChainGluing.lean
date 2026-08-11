/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.HaplotypeGluing

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent.Pangenome.Linkage

/-!
# Gluing along a whole chain, not one interface

`Descent.Pangenome.HaplotypeGluing` proves the local-to-global statement for a two-chart
panel, and identifies the gluing defect at ONE interface with this file's `phantoms [s]`.
Its own docstring says the general cover is where that generalization must start. This file
takes the step, and it takes it by extending the existing bridge rather than by building a
second theory: the `r`-interface object is already `Chain ι`, its derivations are already
`mosaics`, and its defect is already `phantoms`, so what was missing was a theorem, not a
construction.

## The result

`phantoms_eq_empty_of_forall_injective`: if every interface along the chain preserves donor
identity, the chain admits no phantom recombinant at all. Equivalently, by
`exists_noninjective_of_phantoms_nonempty`, a single phantom anywhere along a chain of any
length convicts a specific interface of merging two donors.

This is the general-cover form of `HaplotypeGluing.interfacePanel_hasGluing_iff_injective`,
which is the case `r = 1`, and it is proved by the same mechanism made inductive: an
injective interface has singleton fibers, so a derivation reaching a donor has nowhere to
switch to, and the only derivations are the constant ones.

## Both directions, and a correction

`phantoms_eq_empty_iff_forall_injective` is the biconditional: a chain admits no phantom
exactly when every one of its interfaces preserves donor identity. So the per-interface
check is not merely sufficient, it is the whole criterion, and `HaplotypeGluing`'s
`interfacePanel_hasGluing_iff_injective` is its `r = 1` case.

An earlier draft of this file claimed the converse required a decomposition lemma for
`mosaicsFrom` along a list append, and said so in this docstring. That was wrong, and the
error is worth recording because it is the kind that quietly parks work: `mosaicsFrom` is
defined by recursion on the chain, so the induction follows its own recursion and never
needs to split a chain in the middle. The witness is built directly — switch donors at the
offending interface and travel diagonally thereafter — and an injective head interface has
a singleton fiber, which lifts a phantom of the tail to a phantom of the whole chain.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An injective interface has singleton fibers: no two donors share a state, so nothing
may switch there. -/
theorem fiber_eq_singleton_of_injective {s : ι → ι} (hs : Function.Injective s) (h : ι) :
    fiber s h = {h} := by
  ext donor
  simp only [mem_fiber, Finset.mem_singleton]
  exact ⟨fun hstate ↦ hs hstate, fun hdonor ↦ by rw [hdonor]⟩

/-- **Along an all-injective chain the only derivation from a donor is that donor
repeated.** The inductive core: a singleton fiber leaves the derivation nowhere to go. -/
theorem mosaicsFrom_eq_singleton_of_forall_injective :
    ∀ (c : Chain ι) (h : ι), (∀ s ∈ c, Function.Injective s) →
      mosaicsFrom c h = {List.replicate (c.length + 1) h}
  | [], h, _ => by simp [mosaicsFrom]
  | s :: c, h, hinj => by
    have hs : Function.Injective s := hinj s (List.mem_cons_self ..)
    have htail : ∀ t ∈ c, Function.Injective t :=
      fun t ht ↦ hinj t (List.mem_cons_of_mem s ht)
    rw [mosaicsFrom, fiber_eq_singleton_of_injective hs,
      Finset.singleton_biUnion, mosaicsFrom_eq_singleton_of_forall_injective c h htail]
    simp [List.replicate_succ]

/-- **An all-injective chain has no derivations beyond its diagonals.** -/
theorem mosaics_eq_diagonals_of_forall_injective (c : Chain ι)
    (hinj : ∀ s ∈ c, Function.Injective s) : mosaics c = diagonals c := by
  ext derivation
  simp only [mosaics, diagonals, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and, mosaicsFrom_eq_singleton_of_forall_injective c _ hinj, Finset.mem_singleton]
  exact ⟨fun ⟨donor, hdonor⟩ ↦ ⟨donor, hdonor.symm⟩, fun ⟨donor, hdonor⟩ ↦ ⟨donor, hdonor.symm⟩⟩

/-- **Donor-identity preservation at every interface certifies the whole chain.** No phantom
recombinant exists over a chain all of whose interfaces are injective, at any chain length.

This is the general-cover form of the two-chart result: `HaplotypeGluing` proves an
interface glues exactly when it is injective, and this says the property composes along a
chain without loss. The practical reading is that the certificate is per-interface — a
study need not enumerate derivations to rule out phantoms, it need only check each
interface. -/
theorem phantoms_eq_empty_of_forall_injective (c : Chain ι)
    (hinj : ∀ s ∈ c, Function.Injective s) : phantoms c = ∅ := by
  rw [phantoms, mosaics_eq_diagonals_of_forall_injective c hinj, Finset.sdiff_self]

/-- **One phantom convicts one interface.** The contrapositive, and the form an audit uses:
a single locally compatible haplotype absent from the panel proves that some interface along
the chain merged two donors, whatever the chain's length. -/
theorem exists_noninjective_of_phantoms_nonempty (c : Chain ι)
    (hphantom : (phantoms c).Nonempty) : ∃ s ∈ c, ¬ Function.Injective s := by
  by_contra hall
  push_neg at hall
  rw [phantoms_eq_empty_of_forall_injective c hall] at hphantom
  exact absurd hphantom (by simp)

/-- The one-interface case, recovered from the chain theorem rather than restated: this is
the direction of `HaplotypeGluing.interfacePanel_hasGluing_iff_injective` that says an
injective interface admits only diagonal matching families. -/
theorem phantoms_singleton_eq_empty_of_injective (s : ι → ι) (hs : Function.Injective s) :
    phantoms [s] = ∅ := by
  refine phantoms_eq_empty_of_forall_injective [s] ?_
  intro interface hinterface
  rw [List.mem_singleton.mp hinterface]
  exact hs

/-- Membership in the diagonals, unfolded: a derivation is diagonal exactly when it is one
donor repeated. -/
theorem mem_diagonals_iff {c : Chain ι} {derivation : List ι} :
    derivation ∈ diagonals c ↔ ∃ donor : ι, derivation = List.replicate (c.length + 1) donor := by
  simp only [diagonals, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨donor, hdonor⟩ ↦ ⟨donor, hdonor.symm⟩, fun ⟨donor, hdonor⟩ ↦ ⟨donor, hdonor.symm⟩⟩

/-- **A merging interface anywhere along the chain manufactures a phantom.** The witness is
explicit: travel diagonally to the offending interface, switch to the donor it cannot
distinguish, and travel diagonally thereafter. -/
theorem phantoms_nonempty_of_exists_not_injective :
    ∀ (c : Chain ι), (∃ s ∈ c, ¬ Function.Injective s) → (phantoms c).Nonempty
  | [], hbad => by simp at hbad
  | s :: rest, hbad => by
    by_cases hs : Function.Injective s
    · obtain ⟨t, ht, hnot⟩ := hbad
      have htail : t ∈ rest := by
        rcases List.mem_cons.mp ht with rfl | hrest
        · exact absurd hs hnot
        · exact hrest
      obtain ⟨tailPhantom, htail'⟩ :=
        phantoms_nonempty_of_exists_not_injective rest ⟨t, htail, hnot⟩
      rw [phantoms, Finset.mem_sdiff, mosaics, Finset.mem_biUnion] at htail'
      obtain ⟨⟨donor, -, hderivation⟩, hnotdiagonal⟩ := htail'
      refine ⟨donor :: tailPhantom, ?_⟩
      rw [phantoms, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [mosaics, Finset.mem_biUnion]
        refine ⟨donor, Finset.mem_univ _, ?_⟩
        rw [mosaicsFrom, Finset.mem_biUnion]
        exact ⟨donor, by simp, Finset.mem_image_of_mem _ hderivation⟩
      · intro hdiagonal
        apply hnotdiagonal
        obtain ⟨witness, hwitness⟩ := mem_diagonals_iff.mp hdiagonal
        rw [List.length_cons, List.replicate_succ] at hwitness
        obtain ⟨-, htailEq⟩ := List.cons.injEq .. ▸ hwitness
        exact mem_diagonals_iff.mpr ⟨witness, htailEq⟩
    · obtain ⟨left, right, hstate, hne⟩ : ∃ left right, s left = s right ∧ left ≠ right := by
        rw [Function.Injective] at hs
        push_neg at hs
        obtain ⟨left, right, hstate, hne⟩ := hs
        exact ⟨left, right, hstate, hne⟩
      refine ⟨left :: List.replicate (rest.length + 1) right, ?_⟩
      rw [phantoms, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [mosaics, Finset.mem_biUnion]
        refine ⟨left, Finset.mem_univ _, ?_⟩
        rw [mosaicsFrom, Finset.mem_biUnion]
        exact ⟨right, by simp [hstate], Finset.mem_image_of_mem _ (replicate_mem_mosaicsFrom rest right)⟩
      · intro hdiagonal
        obtain ⟨witness, hwitness⟩ := mem_diagonals_iff.mp hdiagonal
        rw [List.length_cons, List.replicate_succ] at hwitness
        obtain ⟨hhead, htailEq⟩ := List.cons.injEq .. ▸ hwitness
        have hright : right = witness := by
          have := congrArg (fun l ↦ l.head?) htailEq
          simpa [List.replicate_succ] using this
        exact hne (hhead.trans hright.symm)

/-- **The criterion, both ways.** A chain admits no phantom recombinant exactly when every
interface along it preserves donor identity. -/
theorem phantoms_eq_empty_iff_forall_injective (c : Chain ι) :
    phantoms c = ∅ ↔ ∀ s ∈ c, Function.Injective s := by
  refine ⟨fun hempty ↦ ?_, phantoms_eq_empty_of_forall_injective c⟩
  by_contra hbad
  push_neg at hbad
  obtain ⟨phantom, hphantom⟩ := phantoms_nonempty_of_exists_not_injective c hbad
  rw [hempty] at hphantom
  exact absurd hphantom (by simp)

end Descent.Pangenome.Linkage
