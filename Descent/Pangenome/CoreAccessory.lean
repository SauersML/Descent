/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Construction

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Core and accessory, and the two directions they are confounded in

A pangenome study reports how much sequence is CORE -- present in every genome examined --
and how much is accessory.  `Descent.Pangenome.Construction` shows that a node's haplotype
support depends on which construction was used and moves one way as the construction coarsens.
This file adds the other dependence, and it is the one the field already knows about without
treating it as disqualifying: the core depends on WHICH GENOMES WERE EXAMINED, and moves one
way as that set grows.

## Kingman's razor, which is what this is an instance of

`Descent.Coalescent.Restriction` formalises the consistency condition that makes a single
coalescent carry every sample size at once: `ρ_{mn} ∘ ρ_n = ρ_m`, K-G (7.2).  Kingman's point
is that requiring consistency between sample sizes is not a technical convenience but a
filter -- it limits the mathematical possibilities, and what survives is the partition
structures.

A quantity that fails the filter is not a quantity that is hard to estimate.  It is a
quantity that has no `n`-free content, because its value at `n` is partly a statement about
`n`.  `core_not_sampling_consistent` exhibits the failure for the core: a node core to one
sample and not core to a larger one containing it, so "is this sequence core" has no answer
that does not name the panel.

That is not a defect of pangenome graphs.  It is a defect of the summary, and the same
argument disqualifies every openness or growth-curve exponent fitted across nested subsamples,
since those are `n`-indexed by construction.

## The two confounds, and why their signs matter

`core_antitone_in_sample`: enlarging the panel can only shrink the core.
`isCore_mono_in_construction`: coarsening the construction can only grow it.

So the two indeterminacies of a reported core size push in OPPOSITE directions, and both
directions are known.  A study that adds genomes and coarsens its builder at the same time --
which is what happens when a new release adds samples and re-runs a pipeline with a larger
closure -- moves the number by a difference of two effects with known signs and unknown
magnitudes.  Reporting the difference as a biological finding requires ruling both out, and
neither is usually reported at all.

## What is not claimed

Nothing here says a core is uninteresting or that any published number is wrong.  The claims
are the two monotonicities and one witness of inconsistency; the magnitudes on real data are
empirical and are not settled here.

## Empirical status

None.  The bodies are definitions and lemmas about finite equivalence relations, and one
explicit two-position witness.

## Main results

- `core_antitone_in_sample`: **more genomes, no more core.**
- `isCore_mono_in_construction`: **coarser build, no less core.**  Opposite signs.
- `core_not_sampling_consistent`: **the razor bites.**  An explicit node that is core to one
  sample and not to a larger one, so the predicate is not a function of the sequence.
-/

namespace Descent.Pangenome.Construction

/-! ### Core membership -/

/-- **A node is core to a sample** when every haplotype in the sample is represented in it.
This is what "present in every genome examined" means once positions have been quotiented
into nodes, and it is stated against an explicit sample so that the dependence is visible in
the type rather than carried by a convention.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names a property of a node relative to a set of
haplotypes; which nodes are core in a real panel is not settled here. -/
def IsCore {Pos Hap : Type*} (hap : Pos → Hap) (r : Setoid Pos) (S : Set Hap) (x : Pos) :
    Prop :=
  S ⊆ support hap r x

/-- Core membership is a property of the node, not of the position naming it. -/
theorem isCore_congr {Pos Hap : Type*} (hap : Pos → Hap) (r : Setoid Pos) (S : Set Hap)
    {x y : Pos} (hxy : r x y) : IsCore hap r S x ↔ IsCore hap r S y := by
  unfold IsCore
  rw [support_congr hap r hxy]

/-- Every node is core to the empty sample, so `IsCore` is inhabited and the definition is
not vacuous.  It is also the degenerate case that makes the antitonicity below sharp: the
core is largest when nothing has been sampled. -/
theorem isCore_empty {Pos Hap : Type*} (hap : Pos → Hap) (r : Setoid Pos) (x : Pos) :
    IsCore hap r (∅ : Set Hap) x :=
  Set.empty_subset _

/-! ### The two directions -/

/-- **More genomes, no more core.**  If the sample grows, a node core to the larger sample was
already core to the smaller one; equivalently the core can only shrink as genomes are added.

The empirical curve every pangenome paper plots -- core size falling as the panel grows -- is
this inequality, and it holds for every panel and every construction, so observing it is not
evidence about the organism. -/
theorem core_antitone_in_sample {Pos Hap : Type*} (hap : Pos → Hap) (r : Setoid Pos)
    {S T : Set Hap} (hST : S ⊆ T) {x : Pos} (h : IsCore hap r T x) : IsCore hap r S x :=
  Set.Subset.trans hST h

/-- **Coarser build, no less core.**  A construction that merges more gives every node a
larger haplotype support, so a node core under a finer construction stays core under a
coarser one.

This is `support_mono` read at the core, and its sign is OPPOSITE to
`core_antitone_in_sample`.  The two confounds on a reported core size therefore do not
compound into a single direction, and separating them is not optional. -/
theorem isCore_mono_in_construction {Pos Hap : Type*} (hap : Pos → Hap) {r s : Setoid Pos}
    (hrs : r ≤ s) (S : Set Hap) {x : Pos} (h : IsCore hap r S x) : IsCore hap s S x :=
  Set.Subset.trans h (support_mono hap hrs x)

/-! ### The razor -/

/-- The smallest failure: two haplotypes, one position each, and nothing merged.  The node of
position `0` is core to the sample `{0}` and not core to the sample `{0, 1}`.

`Descent.Coalescent.Restriction`'s consistency condition asks that discarding a sampled
individual be a well-defined operation on the quantity.  Here it is not: the answer to "is
this node core" changes under enlargement of the sample, so the predicate is a joint statement
about the sequence and the panel and cannot be reported as a property of the sequence.

Every core-size, openness or pan-genome-growth exponent inherits this, because each is fitted
across nested subsamples and so is `n`-indexed by construction. -/
theorem core_not_sampling_consistent :
    IsCore (id : Fin 2 → Fin 2) ⊥ ({0} : Set (Fin 2)) 0 ∧
      ¬ IsCore (id : Fin 2 → Fin 2) ⊥ (Set.univ : Set (Fin 2)) 0 := by
  have hsupp : support (id : Fin 2 → Fin 2) ⊥ 0 = ({0} : Set (Fin 2)) := by
    ext h
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.symm
    · rintro rfl
      exact ⟨0, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · intro h hh
    rw [hsupp]
    exact hh
  · intro hsub
    have h1 : (1 : Fin 2) ∈ support (id : Fin 2 → Fin 2) ⊥ 0 := hsub (Set.mem_univ 1)
    rw [hsupp] at h1
    exact absurd (Set.mem_singleton_iff.mp h1) (by decide)

end Descent.Pangenome.Construction
