/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Genome
import Descent.Pangenome.CoreAccessory
import Mathlib.Data.Fin.VecNotation

assert_below Descent.Coalescent Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# The positional graph of a phased panel: where the pangenome chapter meets the data objects

`Descent.Pangenome.Construction` takes a pangenome graph to be a quotient of an abstract
position set by the closure of an aligner's report, and prices what the closure invents.
`Descent.Core.Genome` owns the objects the corpus's empirical claims are about -- `Allele`,
`Haplotype`, `Genome.ofHaplotypes`.  Until this file the two did not meet: the chapter's
theorems quantified over position types nothing in the corpus inhabits, so nothing connected
what a graph forgets to what a genotype matrix records.  This file is the instantiation.  A
phased panel `H : Fin m → Core.Haplotype n` induces a position set `Fin m × Core.Locus n`
and an aligner relation -- POSITIONAL homology: same locus, same allele -- and everything
the chapter proves about constructions lands on it.

## What provably degenerates, and why the degeneration is the content

Three pathologies of the general theory vanish at this construction, each as a theorem
rather than a convention:

* **The closure adds nothing.**  `posAlign` is already transitive (`posAlign_equivalence`),
  because a coordinate system compares every pair of positions -- the failed cocycle that
  `Construction.closure` repairs by fiat holds for free.  `closure_posAlign` is the
  collapse: the construction bracket of `honors_iff_closure_le` degenerates to a point, so
  a coordinate-anchored (VCF-like) build involves no builder's choice at all.
* **Nothing collapses within a haplotype.**  `posSetoid_collapseFree`: distinct loci are
  distinct nodes, so no haplotype traverses a node twice and the traversal multiplicities
  of `Descent.Pangenome.GaugeInvariance` are all `0` or `1` here.
* **Support is allele-sharing.**  `support_posSetoid`: a node's haplotype support is
  exactly the carriers of its allele, so the node frequency spectrum IS the sample allele
  frequency spectrum and the `Construction` confound has nowhere to act.

Read forward, these say a positional build is deterministic.  Read backward, they say what
that determinacy costs: the coordinate frame is ASSUMED, so the repeats, inversions and
rearrangements whose closure and collapse the general theory prices are exactly what a
positional construction cannot represent.  What an HPRC-style graph adds over a VCF is the
regime where these three theorems fail, and the chapter's abstract half is the account of
that regime.

## The size law

`nodeCount_eq_add_segregatingCount`: with at least one haplotype, the graph carries exactly
`n + segregatingCount H` nodes -- the reference length plus one extra node per segregating
locus.  **A positional pangenome graph is its coordinate system plus Watterson's `S`**, not
in expectation but panel by panel, and `Descent.Pangenome.Growth` is that identity composed
with the coalescent's `E(S)`.

## The diploid identification

`segregatesAt_pair_iff_het`: a locus is a bubble in the two-haplotype graph exactly when
the diploid genome those two gametes make -- `Core.Genome.ofHaplotypes`, the corpus's only
definition of that sentence -- is heterozygous there.  `segregatingCount_pair_eq_hetCount`
lifts it to counts: the pair graph's bubble count IS the genome's heterozygous-call count.
`Core.hweProb_het` then prices each locus at `Core.hweHeterozygosity`, the kernel the whole
`F_ST` layer is written in, so the bubble density of a pair pangenome and the
heterozygosity of a diploid are one quantity with two vocabularies.

## Empirical status

None.  Every body is finite combinatorics of a given panel; which panels arise, and whether
positional homology is the homology a study wants, are empirical questions and are not
settled here.

## Main results

- `posAlign_equivalence`, `closure_posAlign`: **the bracket collapses.**  Positional
  homology is total, so the closure invents nothing and the construction is forced.
- `posSetoid_collapseFree`: a coordinate build has no repeats.
- `support_posSetoid`, `isCore_univ_iff`: support is allele-sharing; a node is core to the
  panel exactly when its allele is universal.
- `segregatesAt_iff_exists_not_core`: a locus segregates exactly when some node at it
  fails to be core.
- `nodeCount_eq_add_segregatingCount`: **`pan = reference + S`.**
- `nodeCount_subsample_le`, `segregatingCount_subsample_le`: more genomes, no fewer nodes
  -- the growth curve is monotone before any model is assumed.
- `segregatesAt_pair_iff_het`, `segregatingCount_pair_eq_hetCount`: **a pair graph's
  bubbles are a diploid's heterozygous calls.**
-/

namespace Descent.Pangenome.PanelGraph

/-! ### The positional construction -/

/-- **Positional homology**: two panel positions are aligned when they sit at the same
locus and carry the same allele.  This is the relation a reference-coordinate pipeline
asserts -- every haplotype is indexed by the same `Core.Locus`, so every pair of positions
is compared, through the coordinate system rather than through a pairwise aligner.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names a relation induced by a panel; whether
positional homology is the homology a study wants at a structurally variable locus is the
empirical question, and is not settled here. -/
def posAlign {m n : ℕ} (H : Fin m → Core.Haplotype n) :
    Fin m × Core.Locus n → Fin m × Core.Locus n → Prop :=
  fun p q ↦ p.2 = q.2 ∧ H p.1 p.2 = H q.1 q.2

/-- **Positional homology is already an equivalence relation.**  Reflexive and symmetric as
every aligner report is, and -- unlike a pairwise aligner's report -- TRANSITIVE, because
the coordinate system leaves no pair uncompared.  The failed cocycle condition that
`Construction.closure` exists to repair holds for free here. -/
theorem posAlign_equivalence {m n : ℕ} (H : Fin m → Core.Haplotype n) :
    Equivalence (posAlign H) :=
  ⟨fun _ ↦ ⟨rfl, rfl⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩,
    fun h₁ h₂ ↦ ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

/-- **The positional construction**: the setoid positional homology already is.  No closure
is taken because none is needed, which is the point recorded by `closure_posAlign`.

Empirical status: NOT AN EMPIRICAL CLAIM.  It packages `posAlign` with its equivalence
proof; nothing about a population is asserted. -/
def posSetoid {m n : ℕ} (H : Fin m → Core.Haplotype n) : Setoid (Fin m × Core.Locus n) :=
  ⟨posAlign H, posAlign_equivalence H⟩

/-- The construction relates exactly what positional homology relates.  Definitional, and
stated as the `Iff` so consumers rewrite rather than re-derive. -/
theorem posSetoid_rel_iff {m n : ℕ} (H : Fin m → Core.Haplotype n)
    (p q : Fin m × Core.Locus n) :
    posSetoid H p q ↔ p.2 = q.2 ∧ H p.1 p.2 = H q.1 q.2 := Iff.rfl

/-- **The construction bracket collapses to a point.**  The closure of positional homology
is positional homology: `Construction.honors_iff_closure_le` says the closure is the least
construction believing the aligner, and here the aligner's report is itself a construction,
so the least one believing it is it.  A positional build therefore involves NO builder's
choice -- seqwish's forced repair, and the oriented confound `Construction.support_mono`
prices, are properties of pairwise alignment that a coordinate system buys its way out of
by assuming the coordinates.  The repeats it thereby cannot represent are where the
chapter's abstract half takes over. -/
theorem closure_posAlign {m n : ℕ} (H : Fin m → Core.Haplotype n) :
    Construction.closure (posAlign H) = posSetoid H := by
  refine le_antisymm ((Construction.honors_iff_closure_le _ _).mp fun _ _ h ↦ h) ?_
  exact Setoid.le_def.mpr fun h ↦ Relation.EqvGen.rel _ _ h

/-- **A positional build has no repeats.**  The construction never identifies two distinct
positions of one haplotype, since they sit at distinct loci.  So the traversal
multiplicities that `Construction.collapseFree_iff_quotient_inj` forces on a general graph
are trivial here -- which is the formal statement that a coordinate build cannot see copy
number, not a statement that copy number is absent. -/
theorem posSetoid_collapseFree {m n : ℕ} (H : Fin m → Core.Haplotype n) :
    Construction.CollapseFree Prod.fst (posSetoid H) := by
  rintro ⟨i, l⟩ ⟨j, l'⟩ ⟨hl, -⟩ hij
  cases hl
  cases hij
  rfl

/-! ### Support, core, and segregation -/

/-- **A node's support is the carriers of its allele.**  The abstract
`Construction.support` -- which haplotypes are represented in a node -- evaluates, at the
positional construction, to the set a genotype matrix column records.  This is the
identification that makes the node frequency spectrum of a positional graph the sample
allele frequency spectrum. -/
theorem support_posSetoid {m n : ℕ} (H : Fin m → Core.Haplotype n) (i : Fin m)
    (l : Core.Locus n) :
    Construction.support Prod.fst (posSetoid H) (i, l) = {j | H j l = H i l} := by
  ext j
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨j', l'⟩, ⟨hl, ha⟩, rfl⟩
    cases hl
    exact ha.symm
  · intro hj
    exact ⟨(j, l), ⟨rfl, hj.symm⟩, rfl⟩

/-- **A node is core to the panel exactly when its allele is universal.**  The abstract
core predicate of `Descent.Pangenome.CoreAccessory`, taken at the full panel, evaluates to
the sentence a pangenome paper means by "present in every genome examined" -- and both
confounds proved there apply verbatim, since this is an instance, not a new notion. -/
theorem isCore_univ_iff {m n : ℕ} (H : Fin m → Core.Haplotype n) (i : Fin m)
    (l : Core.Locus n) :
    Construction.IsCore Prod.fst (posSetoid H) Set.univ (i, l) ↔ ∀ j, H j l = H i l := by
  unfold Construction.IsCore
  rw [support_posSetoid]
  exact ⟨fun h j ↦ h (Set.mem_univ j), fun h j _ ↦ h j⟩

/-- **A locus segregates** when two panel haplotypes disagree there.  This is the panel's
own Watterson `S`, locus by locus, before any model is put on the panel.

Empirical status: NOT AN EMPIRICAL CLAIM.  It names a property of a given panel at a given
locus; which loci of a real panel segregate is data, not derivation. -/
def SegregatesAt {m n : ℕ} (H : Fin m → Core.Haplotype n) (l : Core.Locus n) : Prop :=
  ∃ i j : Fin m, H i l ≠ H j l

instance {m n : ℕ} (H : Fin m → Core.Haplotype n) (l : Core.Locus n) :
    Decidable (SegregatesAt H l) := by
  unfold SegregatesAt
  infer_instance

/-- **The predicate is inhabited**: the smallest polymorphic panel -- one locus, one
haplotype carrying each allele -- segregates there.  A witness rather than an assumption,
so the theorems below constrain a nonempty family. -/
theorem segregatesAt_witness :
    SegregatesAt ![fun _ : Core.Locus 1 ↦ Core.Allele.ref, fun _ ↦ Core.Allele.alt] 0 :=
  ⟨0, 1, by decide⟩

/-- **Segregation is the failure of core.**  A locus segregates exactly when some node at
it is not core to the panel.  With `isCore_univ_iff` this closes the triangle between the
chapter's abstract core/accessory split and the population-genetic notion of a segregating
site: accessory sequence at a positional locus IS polymorphism there. -/
theorem segregatesAt_iff_exists_not_core {m n : ℕ} (H : Fin m → Core.Haplotype n)
    (l : Core.Locus n) :
    SegregatesAt H l ↔
      ∃ i, ¬ Construction.IsCore Prod.fst (posSetoid H) Set.univ (i, l) := by
  constructor
  · rintro ⟨i, j, hij⟩
    exact ⟨i, fun hcore ↦ hij ((isCore_univ_iff H i l).mp hcore j).symm⟩
  · rintro ⟨i, hi⟩
    rw [isCore_univ_iff] at hi
    push_neg at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨j, i, hj⟩

/-! ### The nodes, and the size law -/

/-- **The nodes at a locus**: the alleles the panel presents there.  A positional graph
has one node per allele per locus, and this is that column of it.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite image; what a real panel presents is
data. -/
def nodesAt {m n : ℕ} (H : Fin m → Core.Haplotype n) (l : Core.Locus n) :
    Finset Core.Allele :=
  Finset.image (fun i ↦ H i l) Finset.univ

/-- Membership in a column is being carried by someone: the `Iff` form of the image. -/
theorem mem_nodesAt {m n : ℕ} (H : Fin m → Core.Haplotype n) (l : Core.Locus n)
    (a : Core.Allele) : a ∈ nodesAt H l ↔ ∃ i, H i l = a := by
  simp [nodesAt]

/-- A nonempty panel presents at least one allele at every locus. -/
theorem card_nodesAt_pos {m n : ℕ} (hm : 0 < m) (H : Fin m → Core.Haplotype n)
    (l : Core.Locus n) : 0 < (nodesAt H l).card :=
  Finset.card_pos.mpr ⟨H ⟨0, hm⟩ l, (mem_nodesAt H l _).mpr ⟨⟨0, hm⟩, rfl⟩⟩

/-- A biallelic locus presents at most two alleles: the column is a subset of the allele
type, and `Core.Allele` has two inhabitants by construction. -/
theorem card_nodesAt_le_two {m n : ℕ} (H : Fin m → Core.Haplotype n) (l : Core.Locus n) :
    (nodesAt H l).card ≤ 2 :=
  le_trans (Finset.card_le_card (Finset.subset_univ _)) (by decide)

/-- **Two nodes is segregation.**  A column carries two alleles exactly when the locus
segregates, which is the size law below in its per-locus form. -/
theorem card_nodesAt_eq_two_iff {m n : ℕ} (H : Fin m → Core.Haplotype n)
    (l : Core.Locus n) : (nodesAt H l).card = 2 ↔ SegregatesAt H l := by
  constructor
  · intro h2
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (show 1 < (nodesAt H l).card by omega)
    obtain ⟨i, hi⟩ := (mem_nodesAt H l a).mp ha
    obtain ⟨j, hj⟩ := (mem_nodesAt H l b).mp hb
    exact ⟨i, j, by rw [hi, hj]; exact hab⟩
  · rintro ⟨i, j, hij⟩
    have h1 : 1 < (nodesAt H l).card :=
      Finset.one_lt_card.mpr
        ⟨H i l, (mem_nodesAt H l _).mpr ⟨i, rfl⟩,
          H j l, (mem_nodesAt H l _).mpr ⟨j, rfl⟩, hij⟩
    have h2 := card_nodesAt_le_two H l
    omega

/-- **The size of the graph**: nodes summed over loci.

Empirical status: NOT AN EMPIRICAL CLAIM.  A count of a given panel's graph; the pan-size
a study reports for a real panel is data, and `nodeCount_eq_add_segregatingCount` is what
that number is made of. -/
def nodeCount {m n : ℕ} (H : Fin m → Core.Haplotype n) : ℕ :=
  ∑ l, (nodesAt H l).card

/-- **The panel's segregating-locus count** -- Watterson's `S`, computed from a concrete
panel rather than posited as a summary.

Empirical status: NOT AN EMPIRICAL CLAIM.  A count of a given panel.  What connects it to
the coalescent's `E(S)` is a model, and the connection is made in
`Descent.Pangenome.Growth`, not here. -/
def segregatingCount {m n : ℕ} (H : Fin m → Core.Haplotype n) : ℕ :=
  (Finset.univ.filter fun l ↦ SegregatesAt H l).card

/-- **The size law: `pan = reference + S`.**  With at least one haplotype, the positional
graph carries the reference's `n` nodes plus exactly one extra node per segregating locus.
Every monomorphic column is one node and every segregating column is two, so the excess of
a positional pangenome over its coordinate system is not a new quantity: it IS the panel's
segregating-site count, the statistic Watterson's estimator divides.  The expectation of
this identity under the coalescent is `Descent.Pangenome.Growth.expectedPanSize`. -/
theorem nodeCount_eq_add_segregatingCount {m n : ℕ} (hm : 0 < m)
    (H : Fin m → Core.Haplotype n) : nodeCount H = n + segregatingCount H := by
  unfold nodeCount segregatingCount
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun l ↦ SegregatesAt H l) (fun l ↦ (nodesAt H l).card)
  have h2 : ∀ l ∈ Finset.univ.filter (fun l ↦ SegregatesAt H l),
      (nodesAt H l).card = 2 := fun l hl ↦
    (card_nodesAt_eq_two_iff H l).mpr (Finset.mem_filter.mp hl).2
  have h1 : ∀ l ∈ Finset.univ.filter (fun l ↦ ¬ SegregatesAt H l),
      (nodesAt H l).card = 1 := by
    intro l hl
    have hpos := card_nodesAt_pos hm H l
    have hle := card_nodesAt_le_two H l
    have hne : (nodesAt H l).card ≠ 2 := fun hc ↦
      (Finset.mem_filter.mp hl).2 ((card_nodesAt_eq_two_iff H l).mp hc)
    omega
  rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h1, Finset.sum_const,
    Finset.sum_const, smul_eq_mul, smul_eq_mul] at hsplit
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Core.Locus n))) (p := fun l ↦ SegregatesAt H l)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  omega

/-! ### Growth is monotone before any model

A subsample is a map into the panel, and every count above moves one way under it.  These
are the panel-level halves of the two curves every pangenome paper plots: the pan curve
rises (here) and the core curve falls (`CoreAccessory.core_antitone_in_sample`), and
neither direction is evidence about the organism, because both are theorems about
counting. -/

/-- A subsample presents a subset of the panel's alleles at every locus. -/
theorem nodesAt_subsample_subset {m m' n : ℕ} (H : Fin m → Core.Haplotype n)
    (f : Fin m' → Fin m) (l : Core.Locus n) : nodesAt (H ∘ f) l ⊆ nodesAt H l := by
  intro a ha
  obtain ⟨i, hi⟩ := (mem_nodesAt (H ∘ f) l a).mp ha
  exact (mem_nodesAt H l a).mpr ⟨f i, hi⟩

/-- **More genomes, no fewer nodes.**  The pan curve is monotone in the panel, with no
model assumed: the empirical growth of every pangenome release is this inequality, so
observing growth is not evidence about the gene pool. -/
theorem nodeCount_subsample_le {m m' n : ℕ} (H : Fin m → Core.Haplotype n)
    (f : Fin m' → Fin m) : nodeCount (H ∘ f) ≤ nodeCount H :=
  Finset.sum_le_sum fun l _ ↦ Finset.card_le_card (nodesAt_subsample_subset H f l)

/-- A locus segregating in a subsample segregates in the panel. -/
theorem segregatesAt_subsample {m m' n : ℕ} (H : Fin m → Core.Haplotype n)
    (f : Fin m' → Fin m) (l : Core.Locus n) :
    SegregatesAt (H ∘ f) l → SegregatesAt H l :=
  fun ⟨i, j, hij⟩ ↦ ⟨f i, f j, hij⟩

/-- More genomes, no fewer segregating loci: `S` is monotone in the panel. -/
theorem segregatingCount_subsample_le {m m' n : ℕ} (H : Fin m → Core.Haplotype n)
    (f : Fin m' → Fin m) : segregatingCount (H ∘ f) ≤ segregatingCount H :=
  Finset.card_le_card fun l hl ↦ by
    rw [Finset.mem_filter] at hl ⊢
    exact ⟨hl.1, segregatesAt_subsample H f l hl.2⟩

/-! ### The diploid identification -/

/-- A pair panel segregates at a locus exactly when its two haplotypes disagree there.
The two-element quantifier evaluated, so the diploid statement below is one step away. -/
theorem segregatesAt_pair_iff_ne {n : ℕ} (h₁ h₂ : Core.Haplotype n) (l : Core.Locus n) :
    SegregatesAt ![h₁, h₂] l ↔ h₁ l ≠ h₂ l := by
  constructor
  · rintro ⟨i, j, hij⟩
    intro hne
    apply hij
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, hne]
  · intro hne
    refine ⟨0, 1, ?_⟩
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hne

/-- Two gametes disagree at a locus exactly when the genotype they make there is the
heterozygote: `Core.Genotype.ofAlleles` sends equal pairs to the homozygotes and unequal
pairs to `het`, and this is that fact as an `Iff`. -/
theorem pair_ne_iff_het {n : ℕ} (h₁ h₂ : Core.Haplotype n) (l : Core.Locus n) :
    h₁ l ≠ h₂ l ↔ Core.Genome.ofHaplotypes h₁ h₂ l = Core.Genotype.het := by
  unfold Core.Genome.ofHaplotypes
  cases h₁ l <;> cases h₂ l <;> decide

/-- **A bubble in a pair graph is a heterozygous call.**  The two-haplotype positional
graph segregates at a locus exactly when the diploid genome those gametes make --
`Core.Genome.ofHaplotypes`, the corpus's definition of that sentence -- is heterozygous
there.  Composed with `Core.hweProb_het`, each locus's bubble probability under
Hardy-Weinberg is `Core.hweHeterozygosity` at its allele frequency: the pangenome's bubble
density and the `F_ST` layer's heterozygosity are one quantity in two vocabularies. -/
theorem segregatesAt_pair_iff_het {n : ℕ} (h₁ h₂ : Core.Haplotype n) (l : Core.Locus n) :
    SegregatesAt ![h₁, h₂] l ↔ Core.Genome.ofHaplotypes h₁ h₂ l = Core.Genotype.het :=
  (segregatesAt_pair_iff_ne h₁ h₂ l).trans (pair_ne_iff_het h₁ h₂ l)

/-- **The pair graph's bubble count is the diploid's heterozygous-call count.**  The count
form of `segregatesAt_pair_iff_het`: a two-haplotype pangenome carries exactly one bubble
per heterozygous call of the genome its gametes make, so "how bubbly is this pair graph"
and "how heterozygous is this individual" are the same number computed by two fields. -/
theorem segregatingCount_pair_eq_hetCount {n : ℕ} (h₁ h₂ : Core.Haplotype n) :
    segregatingCount ![h₁, h₂]
      = (Finset.univ.filter fun l : Core.Locus n ↦
          Core.Genome.ofHaplotypes h₁ h₂ l = Core.Genotype.het).card := by
  unfold segregatingCount
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact segregatesAt_pair_iff_het h₁ h₂ l

end Descent.Pangenome.PanelGraph
