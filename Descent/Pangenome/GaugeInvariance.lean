/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GaugeCounterexample

/-!
# Gauge-invariant functionals on a pangenome graph

`Descent.Pangenome.GaugeCounterexample` exhibits, on one explicit triallelic site,
a pair of spanning trees under which Watterson's `S` differs and Tajima's `D`
changes sign.  This file generalises that witness: it identifies exactly which
functionals of a pangenome variant catalogue survive a change of reference tree,
and computes the defect for the ones that do not.

## The setting

A reference tree is a subset of the graph's edges, represented by its
characteristic function `Tree E := E → Bool`.  The complementary edges are the
variants.  A haplotype walk is recorded by its traversal multiplicity on each
edge, `Walk E := E → Nat`; this is the walk-level datum, and it does not mention
a tree.  The genotype `geno T w` is what a VCF actually stores: the traversal
count on variant edges, and nothing on tree edges.

Nothing here formalises spanning-tree theory.  Where a statement needs two trees
to have the same size — which for spanning trees of a connected graph is
`|V| - 1` — that equality is taken as a hypothesis (`variantCount` agreeing), not
derived.  What is proved is everything downstream of that.

## Results

* `count_split`, `sum_split`: the two combinatorial lemmas everything rests on.
* `segregating_add_hidden`: the exact defect formula
  `S_T + |Z \ T| = b₁`, where `Z` is the tree-independent set of edges no two
  sampled walks disagree on.  `S` is short of the variant count by exactly the
  hidden edges the tree failed to absorb.
* `segregatingCount_gauge_invariant`: if every edge is polymorphic across the
  sample then `Z = ∅` and `S` is the same under every tree of a given size.
  This is the general form of `panel_S_invariant`.
* `rowDist_split`: `rowDist_T + |T ∩ Diff| = walkDist`, the same defect for
  pairwise distance — the general reason row-counting `π` moves.
* `geno_sum_split`, `weighted_geno_sum_split`: the walk-level total of any
  edge weighting splits as VCF part plus tree part, so the walk-level quantity
  is recoverable from the catalogue together with the tree.
* `gaugeInvariant_of_treeFree` and its instances: any functional defined on
  walks alone is gauge-invariant, which is why sequence-level `π` and weighted
  holonomy survive.
* `witness` section: the concrete triallelic example is an instance of this
  framework, its `S` values are reproduced, and its hidden edge is exhibited —
  showing the polymorphism hypothesis of `segregatingCount_gauge_invariant` is
  not removable.

## What this file stops short of

`segregating_add_hidden` is a defect formula for a COUNT.  It becomes a defect
formula for an ESTIMATOR only once the count is divided by Watterson's `a_{n-1}`,
and that constant lives in `Descent.Coalescent.BranchLength`, which this file does
not import.  `Descent.Pangenome.CoalescentGauge` does the division and states the
consequence for `Descent.Coalescent.expectedTajimaNumerator_eq_zero`, whose null
mentions no reference tree and therefore cannot see any of this.
-/

namespace Descent.Pangenome

-- The general theory lives in its own namespace: `GaugeCounterexample` already
-- binds `geno` and `rowDist` for its concrete two-node graph, and the witness
-- section below refers to both sets of names.
namespace Gauge

universe u v

/-- A haplotype walk, recorded by how many times it traverses each edge.
Carries no reference tree: this is the gauge-independent datum. -/
abbrev Walk (E : Type u) := E → Nat

/-- A reference tree, as the characteristic function of its edge set.  The
complementary edges are the variant edges. -/
abbrev Tree (E : Type u) := E → Bool

/-- Number of list elements satisfying `p`.  Defined here rather than as
`(l.filter p).length` so that every lemma below is an induction on this
definition's own equations. -/
def count {α : Type u} (p : α → Bool) : List α → Nat
  | [] => 0
  | a :: as => (if p a then 1 else 0) + count p as

/-- Sum of `f` over a list. -/
def sum {α : Type u} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: as => f a + sum f as

/-! ### The two combinatorial lemmas -/

/-- Splitting a count along a second predicate.  Every defect formula below is
this lemma with a different choice of `p` and `q`. -/
theorem count_split {α : Type u} (p q : α → Bool) : ∀ l : List α,
    count (fun a => p a && q a) l + count (fun a => p a && !q a) l = count p l
  | [] => rfl
  | a :: as => by
    have ih := count_split p q as
    cases hp : p a <;> cases hq : q a <;> simp [count, hp, hq] <;> omega

/-- Counts agree when the predicates agree on the list's elements. -/
theorem count_congr {α : Type u} {p q : α → Bool} : ∀ {l : List α},
    (∀ a, a ∈ l → p a = q a) → count p l = count q l
  | [], _ => rfl
  | a :: as, h => by
    have ha := h a (List.Mem.head _)
    have ih : count p as = count q as :=
      count_congr (fun b hb => h b (List.Mem.tail _ hb))
    simp [count, ha, ih]

/-- Splitting a sum along a predicate. -/
theorem sum_split {α : Type u} (p : α → Bool) (f : α → Nat) : ∀ l : List α,
    sum (fun a => if p a then 0 else f a) l + sum (fun a => if p a then f a else 0) l
      = sum f l
  | [] => rfl
  | a :: as => by
    have ih := sum_split p f as
    cases hp : p a <;> simp [sum, hp] <;> omega

/-! ### Genotypes -/

variable {E : Type u}

/-- The genotype a VCF records for walk `w` at edge `e` under reference tree `T`:
the traversal count on a variant edge, and nothing on a tree edge.

    Empirical status: **NOT AN EMPIRICAL CLAIM**. This is the DEFINITION of what a VCF
    written against a chosen reference tree records, not a model of anything: it says
    which number appears in the file, and a measurement disagreeing with it would be a
    measurement of a different file format. The empirical content of this module is in
    the gauge statements ABOUT this map -- whether a quantity computed from `geno` is
    invariant to the choice of `T` -- and those carry their own markers.

    The name is screened as an empirical claim because it begins `geno`, which is the
    right screen: most `geno`-named definitions in the corpus are genotype models. This
    one is not, and says so rather than being exempted by the screen. -/
def geno (T : Tree E) (w : Walk E) (e : E) : Nat :=
  if T e then 0 else w e

/-- An edge is polymorphic in a sample iff two sampled walks traverse it a
different number of times.  This mentions no tree — the property is a fact about
the walks, which is what makes the defect formula below meaningful. -/
def polymorphic (sample : List (Walk E)) (e : E) : Bool :=
  sample.any (fun w₁ => sample.any (fun w₂ => !(w₁ e == w₂ e)))

/-- Watterson's count of segregating sites: variant edges whose genotype column
is not constant across the sample. -/
def segregatingCount (edges : List E) (T : Tree E) (sample : List (Walk E)) : Nat :=
  count (fun e => !T e && polymorphic sample e) edges

/-- The number of variant edges, i.e. the first Betti number when `T` is a
spanning tree. -/
def variantCount (edges : List E) (T : Tree E) : Nat :=
  count (fun e => !T e) edges

/-- Variant edges that no two sampled walks distinguish.  These are invisible to
the catalogue: present as VCF rows, monomorphic in the sample. -/
def hiddenCount (edges : List E) (T : Tree E) (sample : List (Walk E)) : Nat :=
  count (fun e => !T e && !polymorphic sample e) edges

/-! ### The defect formula for `S` -/

/-- **The exact gauge dependence of Watterson's `S`.**  `S_T` falls short of the
variant count by exactly the number of sample-monomorphic edges the tree failed
to absorb.

The set of monomorphic edges is a property of the sample alone and does not move
with the tree; what moves is how many of them land inside `T`.  So this single
identity both explains why `S` is tree-dependent in general and says precisely
when it is not. -/
theorem segregating_add_hidden (edges : List E) (T : Tree E) (sample : List (Walk E)) :
    segregatingCount edges T sample + hiddenCount edges T sample
      = variantCount edges T :=
  count_split (fun e => !T e) (polymorphic sample) edges

/-- When every edge is polymorphic across the sample, nothing is hidden. -/
theorem hiddenCount_eq_zero (edges : List E) (T : Tree E) (sample : List (Walk E))
    (h : ∀ e, e ∈ edges → polymorphic sample e = true) :
    hiddenCount edges T sample = 0 := by
  have : count (fun e => !T e && !polymorphic sample e) edges
      = count (fun _ => false) edges :=
    count_congr (fun a ha => by simp [h a ha])
  have hzero : ∀ l : List E, count (fun _ => false) l = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons a as ih => simp [count, ih]
  rw [hiddenCount, this, hzero]

/-- Under full polymorphism `S` equals the variant count. -/
theorem segregatingCount_eq_variantCount (edges : List E) (T : Tree E)
    (sample : List (Walk E)) (h : ∀ e, e ∈ edges → polymorphic sample e = true) :
    segregatingCount edges T sample = variantCount edges T := by
  have hd := segregating_add_hidden edges T sample
  rw [hiddenCount_eq_zero edges T sample h] at hd
  omega

/-- **`S` is gauge-invariant when every edge is polymorphic in the sample.**

The size hypothesis is the statement that both trees are spanning trees of the
same graph; spanning-tree theory is not formalised here, so it is assumed rather
than derived.  Everything else is proved.

This is the general form of `panel_S_invariant`: over the full panel that defined
the graph, every edge is traversed by someone and distinguishes someone, so `S`
is pinned to the Betti number under every reference tree. -/
theorem segregatingCount_gauge_invariant (edges : List E) (T₁ T₂ : Tree E)
    (sample : List (Walk E)) (h : ∀ e, e ∈ edges → polymorphic sample e = true)
    (hsize : variantCount edges T₁ = variantCount edges T₂) :
    segregatingCount edges T₁ sample = segregatingCount edges T₂ sample := by
  rw [segregatingCount_eq_variantCount edges T₁ sample h,
      segregatingCount_eq_variantCount edges T₂ sample h, hsize]

/-! ### The defect formula for pairwise distance -/

/-- Number of edges at which two walks differ.  Walk-level: no tree. -/
def walkDist (edges : List E) (w₁ w₂ : Walk E) : Nat :=
  count (fun e => !(w₁ e == w₂ e)) edges

/-- Number of VCF rows at which two walks carry different genotypes. -/
def rowDist (edges : List E) (T : Tree E) (w₁ w₂ : Walk E) : Nat :=
  count (fun e => !(w₁ e == w₂ e) && !T e) edges

/-- **The exact gauge dependence of row-counting distance.**  Row distance falls
short of walk distance by exactly the number of differing edges the tree absorbs.

This is the general reason `π` computed from VCF rows moves with the reference
tree while `π` computed from sequences does not: `walkDist` has no tree argument,
`rowDist` does, and they differ by a tree-dependent term. -/
theorem rowDist_split (edges : List E) (T : Tree E) (w₁ w₂ : Walk E) :
    count (fun e => !(w₁ e == w₂ e) && T e) edges + rowDist edges T w₁ w₂
      = walkDist edges w₁ w₂ :=
  count_split (fun e => !(w₁ e == w₂ e)) T edges

/-- Row distance equals walk distance exactly when the tree absorbs none of the
differing edges. -/
theorem rowDist_eq_walkDist_iff (edges : List E) (T : Tree E) (w₁ w₂ : Walk E) :
    rowDist edges T w₁ w₂ = walkDist edges w₁ w₂
      ↔ count (fun e => !(w₁ e == w₂ e) && T e) edges = 0 := by
  have h := rowDist_split edges T w₁ w₂
  constructor <;> intro hh <;> omega

/-! ### Recovering walk-level totals -/

/-- The walk-level traversal total splits into the part a VCF records and the
part the tree absorbs.  So the gauge-invariant total is recoverable from the
catalogue together with the tree — the information is not destroyed by the
choice, only redistributed. -/
theorem geno_sum_split (edges : List E) (T : Tree E) (w : Walk E) :
    sum (geno T w) edges + sum (fun e => if T e then w e else 0) edges
      = sum w edges :=
  sum_split T w edges

/-- The same for any edge weighting `ℓ` — allele lengths, for instance — so the
weighted holonomy of a walk splits the same way.  With `ℓ` the allele length this
says the total sequence length of a walk is the VCF-visible burden plus the
reference-tree burden. -/
theorem weighted_geno_sum_split (edges : List E) (T : Tree E) (ℓ : E → Nat)
    (w : Walk E) :
    sum (fun e => if T e then 0 else ℓ e * w e) edges
        + sum (fun e => if T e then ℓ e * w e else 0) edges
      = sum (fun e => ℓ e * w e) edges :=
  sum_split T (fun e => ℓ e * w e) edges

/-! ### Gauge-invariant functionals -/

/-- A statistic of the catalogue is gauge-invariant when it does not depend on
the reference tree. -/
def GaugeInvariant {α : Type v} (F : Tree E → List (Walk E) → α) : Prop :=
  ∀ T₁ T₂ : Tree E, ∀ s : List (Walk E), F T₁ s = F T₂ s

/-- **Any functional of the walks alone is gauge-invariant.**  Trivial to prove
and the whole classification: an estimator survives a change of reference tree
exactly when its definition never mentions one.  Sequence-level `π`, weighted
holonomy, and pairwise walk distance are invariant for this reason; `S`, row
distance, allele frequencies and everything built on them are not, because they
are defined on the genotype matrix, which is a coordinate presentation. -/
theorem gaugeInvariant_of_treeFree {α : Type v} (f : List (Walk E) → α) :
    GaugeInvariant (E := E) (fun _ s => f s) :=
  fun _ _ _ => rfl

/-- Mean pairwise walk distance, scaled by the number of unordered pairs to stay
in `Nat`.  The sequence-level `π` of `GaugeCounterexample` is this functional
with one base per edge. -/
def totalWalkDist (edges : List E) (sample : List (Walk E)) : Nat :=
  sum (fun w₁ => sum (fun w₂ => walkDist edges w₁ w₂) sample) sample

/-- Sequence-level diversity is gauge-invariant. -/
theorem totalWalkDist_gaugeInvariant (edges : List E) :
    GaugeInvariant (E := E) (fun _ s => totalWalkDist edges s) :=
  gaugeInvariant_of_treeFree _

/-- Weighted holonomy of a walk — total allele length traversed — is
gauge-invariant. -/
theorem weightedHolonomy_gaugeInvariant (edges : List E) (ℓ : E → Nat) :
    GaugeInvariant (E := E) (fun _ s => sum (fun w => sum (fun e => ℓ e * w e) edges) s) :=
  gaugeInvariant_of_treeFree _

/-! ### The witness is an instance

The triallelic site of `GaugeCounterexample`, presented in the general framework:
each haplotype is the walk that traverses its own allele's edge once. -/

/-- A haplotype as a walk: it traverses its own allele's edge once. -/
def walkOf (h : Hap) : Walk Allele := fun e => if h = e then 1 else 0

/-- A reference tree as a characteristic function. -/
def treeOf (t : RefTree) : Tree Allele := fun e => e == t

/-- The subsample `[A, A, C]` of `GaugeCounterexample`, as walks. -/
def sampleSub : List (Walk Allele) := subsample.map walkOf

/-- The full panel `[A, C, G]`, as walks. -/
def samplePanel : List (Walk Allele) := panel.map walkOf

/-- The general definition reproduces the witness: `S = 1` under the tree keeping
the majority allele, `S = 2` under the tree keeping the allele no sampled walk
carries. -/
theorem general_reproduces_witness :
    segregatingCount allEdges (treeOf Allele.A) sampleSub = 1
      ∧ segregatingCount allEdges (treeOf Allele.G) sampleSub = 2 := by
  constructor <;> rfl

/-- And the defect formula accounts for the difference exactly: under tree `A`
the hidden edge `G` sits outside the tree and is lost from `S`; under tree `G` it
is absorbed by the tree and nothing is hidden.  Both trees have variant count
`2`, the Betti number. -/
theorem general_explains_witness :
    hiddenCount allEdges (treeOf Allele.A) sampleSub = 1
      ∧ hiddenCount allEdges (treeOf Allele.G) sampleSub = 0
      ∧ variantCount allEdges (treeOf Allele.A) = 2
      ∧ variantCount allEdges (treeOf Allele.G) = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The polymorphism hypothesis of `segregatingCount_gauge_invariant` is not
removable: edge `G` is monomorphic in the subsample, and that single failure is
what lets `S` move. -/
theorem subsample_has_monomorphic_edge :
    polymorphic sampleSub Allele.G = false := rfl

/-- Over the full panel every edge is polymorphic, so the general invariance
theorem applies and re-proves `panel_S_invariant` from the framework rather than
by computation. -/
theorem panel_allPolymorphic :
    ∀ e, e ∈ allEdges → polymorphic samplePanel e = true := by
  intro e he
  cases e <;> rfl

/-- Consequently `S` over the full panel is the same under every reference tree
of the Betti-number size, for the general reason. -/
theorem panel_S_gauge_invariant (T₁ T₂ : Tree Allele)
    (hsize : variantCount allEdges T₁ = variantCount allEdges T₂) :
    segregatingCount allEdges T₁ samplePanel = segregatingCount allEdges T₂ samplePanel :=
  segregatingCount_gauge_invariant allEdges T₁ T₂ samplePanel panel_allPolymorphic hsize

end Gauge

end Descent.Pangenome
