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

## What is proved here and what is not

The direction proved is the one a study design needs: it certifies a whole chain from a
per-interface check, and the check is on the interface maps alone. The converse — every
non-injective interface anywhere along a chain manufactures a phantom — is true and is NOT
proved here. It needs a decomposition lemma for `mosaicsFrom` along a list append
(`mosaicsFrom (pre ++ s :: post)` in terms of `mosaicsFrom pre` and `mosaicsFrom post`),
which the corpus does not currently have; `HaplotypeGluing` supplies the `r = 1` instance of
it and nothing longer. Stating the missing lemma is the whole of the remaining work, and it
is stated here rather than left for a reader to rediscover.
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

end Descent.Pangenome.Linkage
