/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Reference-tree dependence of population-genetic estimators on a pangenome graph

A pangenome variant catalogue is defined against a *reference tree*: a spanning
tree of the pangenome graph whose complementary (cotree) edges are declared to be
the variants.  Different spanning trees give different variant sets.  The total
number of variants is the first Betti number and so does not move, but which
edges are variants, and which allele is REF, do.

This file settles, by explicit finite computation, whether that choice reaches
population-genetic estimators computed downstream from the resulting genotype
matrix.  It does, and the two headline results point in opposite directions:

* `subsample_S_not_invariant` / `subsample_tajima_sign_flips`: for a *subsample*
  of the panel, Watterson's `S` and hence Tajima's `D` depend on the reference
  tree.  In the witness below `D = 0` under one spanning tree and `D < 0` under
  another, on the same data.  Sequence-level `π` is unmoved.
* `panel_S_invariant`: for the *full panel* that defined the graph, `S` is the
  same under every spanning tree.

The mechanism is visible in the definitions.  A cotree edge is polymorphic in a
sample exactly when some but not all sampled walks traverse it, so `S` counts
sampled-and-not-in-the-tree edges.  When every graph edge is traversed by someone
— which holds for the full panel, since that is why the edges are in the graph —
every spanning tree removes exactly `|V| - 1` traversed edges and `S` is pinned to
the Betti number.  Subsample, and edges go untraversed, and different spanning
trees absorb different numbers of them.

## Scope

This is a witness, not a general theorem.  It shows the dependence is real and
is realised by an honest change of spanning tree (`treeA_spanning`, `treeG_spanning`)
rather than by an abstract unimodular change of basis, which is the gap a purely
linear-algebraic argument leaves open.  The general statements — that `S` is
invariant whenever the sample traverses every edge, and that every estimator
factoring through the genotype matrix alone is otherwise tree-dependent — are not
proved here.

## The graph

Two nodes joined by three parallel edges: one triallelic site, alleles `A`, `C`, `G`,
each a single base.  A haplotype walk is the allele it carries.  Betti number
`|E| - |V| + 1 = 3 - 2 + 1 = 2`, so every reference tree yields two variant edges.

All statistics below are scaled by `6` to stay in `Nat`/`Int`; the unscaled
rational values appear in each docstring.
-/

namespace Descent.Pangenome

/-- The three parallel edges of the two-node graph, equivalently the three alleles
of the triallelic site. -/
inductive Allele
  | A
  | C
  | G
  deriving DecidableEq, BEq, Repr

/-- The edge set of the graph. -/
def allEdges : List Allele := [Allele.A, Allele.C, Allele.G]

/-- A haplotype is a walk through the graph, here determined by the edge it takes. -/
abbrev Hap := Allele

/-- A reference tree, here determined by the single edge it retains.
See `IsSpanningTree`. -/
abbrev RefTree := Allele

/-- A set of edges spans this two-node graph iff it contains at least one edge, and
is acyclic iff it contains at most one — any two parallel edges close a cycle.  So
the spanning trees of this graph are exactly the singletons, and each of the three
edges determines one. -/
def IsSpanningTree (s : List Allele) : Prop := s.length = 1

theorem treeA_spanning : IsSpanningTree [Allele.A] := rfl

theorem treeG_spanning : IsSpanningTree [Allele.G] := rfl

/-- Genotype of haplotype `h` at edge `e` under reference tree `t`: the number of
times the walk traverses `e`, where the tree edge is not a variant and so carries no
genotype. -/
def geno (t : RefTree) (h : Hap) (e : Allele) : Nat :=
  if e = t then 0 else if h = e then 1 else 0

/-- The genotype column of edge `e` across the sample. -/
def column (t : RefTree) (sample : List Hap) (e : Allele) : List Nat :=
  sample.map (fun h => geno t h e)

/-- A column is polymorphic iff two entries differ. -/
def nonConstant (l : List Nat) : Bool :=
  l.any (fun x => l.any (fun y => x != y))

/-- An edge is segregating under `t` iff it is a variant edge (not the tree edge)
and its genotype column is polymorphic. -/
def isSegregating (t : RefTree) (sample : List Hap) (e : Allele) : Bool :=
  (e != t) && nonConstant (column t sample e)

/-- Number of segregating sites `S`, the count entering Watterson's estimator. -/
def S (t : RefTree) (sample : List Hap) : Nat :=
  (allEdges.filter (isSegregating t sample)).length

/-- Unordered pairs of a list, with multiplicity. -/
def unorderedPairs : List Hap → List (Hap × Hap)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

/-- Sequence-level distance between two haplotypes: the number of base positions at
which their walks spell different sequences.  One base here, so `0` or `1`.

Note that this takes no reference tree.  That is the whole point: it is a property
of the two walks, so it cannot depend on a choice of spanning tree. -/
def seqDist (h₁ h₂ : Hap) : Nat := if h₁ = h₂ then 0 else 1

/-- Row-counting distance: the number of VCF rows at which two haplotypes carry
different genotypes.  Unlike `seqDist` this *does* take a reference tree. -/
def rowDist (t : RefTree) (h₁ h₂ : Hap) : Nat :=
  (allEdges.filter (fun e => geno t h₁ e != geno t h₂ e)).length

private def sumOver (l : List (Hap × Hap)) (f : Hap → Hap → Nat) : Nat :=
  (l.map (fun p => f p.1 p.2)).foldr (· + ·) 0

/-- Six times sequence-level `π`, the mean pairwise sequence divergence.
For `subsample` below, `π = 2/3`. -/
def piSeq6 (sample : List Hap) : Nat :=
  2 * sumOver (unorderedPairs sample) seqDist

/-- Six times row-counting `π`, the mean number of VCF rows at which two sampled
haplotypes differ.  For `subsample` below this is `2/3` under tree `A` and `4/3`
under tree `G`. -/
def piRows6 (t : RefTree) (sample : List Hap) : Nat :=
  2 * sumOver (unorderedPairs sample) (rowDist t)

/-- Six times Watterson's `θ_W = S / a_n`, at `n = 3` where `a_3 = 3/2`, so
`6 θ_W = 4 S`. -/
def thetaW6 (t : RefTree) (sample : List Hap) : Nat := 4 * S t sample

/-- Six times the numerator of Tajima's `D`, namely `π - θ_W`, with `π` taken at the
sequence level so that the only tree-dependence entering is through `θ_W`. -/
def tajimaNum6 (t : RefTree) (sample : List Hap) : Int :=
  (piSeq6 sample : Int) - (thetaW6 t sample : Int)

/-! ### The subsample: estimators move

Three haplotypes drawn from a panel whose graph carries all three alleles; the
sampled walks traverse only `A` and `C`, leaving edge `G` untraversed. This is the
ordinary situation for any per-population statistic, where the graph is built from
the whole panel and the estimator is computed on one group. -/

/-- Two copies of allele `A` and one of `C`. Edge `G` is in the graph but is
traversed by no sampled haplotype. -/
def subsample : List Hap := [Allele.A, Allele.A, Allele.C]

/-- Under tree `A` one variant edge segregates; under tree `G` two do.  Both are
spanning trees of the same graph (`treeA_spanning`, `treeG_spanning`) and the data
are identical. -/
theorem subsample_S_not_invariant :
    S Allele.A subsample = 1 ∧ S Allele.G subsample = 2 := by
  constructor <;> rfl

/-- Watterson's estimator inherits the dependence: `θ_W = 2/3` versus `4/3`. -/
theorem subsample_thetaW_not_invariant :
    thetaW6 Allele.A subsample ≠ thetaW6 Allele.G subsample := by decide

/-- Sequence-level `π` is `2/3`, and it cannot move: `piSeq6` takes no reference
tree, because it is a function of the walks alone. Its invariance is definitional,
which is exactly the content of the claim — the estimator that survives is the one
whose definition never mentions the gauge. -/
theorem subsample_piSeq_value : piSeq6 subsample = 4 := rfl

/-- Row-counting `π` — the same symbol as above, computed by counting VCF rows
instead of bases — does move: `2/3` versus `4/3`. -/
theorem subsample_piRows_not_invariant :
    piRows6 Allele.A subsample ≠ piRows6 Allele.G subsample := by decide

/-- The headline. Tajima's `D` is zero under one reference tree and strictly
negative under another, on the same haplotypes and the same graph. A neutrality
test on a pangenome VCF reports the reference tree. -/
theorem subsample_tajima_sign_flips :
    tajimaNum6 Allele.A subsample = 0 ∧ tajimaNum6 Allele.G subsample < 0 := by
  constructor <;> decide

/-! ### The full panel: `S` is pinned

The complementary result. When the sample traverses every edge of the graph — the
defining situation for the panel the graph was built from — every spanning tree
leaves the same number of edges segregating, namely the Betti number. -/

/-- One haplotype per allele: every graph edge is traversed. -/
def panel : List Hap := [Allele.A, Allele.C, Allele.G]

/-- Over the full panel, `S` equals the Betti number `2` under every spanning tree,
so Watterson's estimator is reference-tree invariant here. The dependence exhibited
above is a subsampling phenomenon, not an artefact of the toy graph. -/
theorem panel_S_invariant : ∀ t : RefTree, S t panel = 2 := by
  intro t; cases t <;> rfl

/-- And Tajima's numerator is correspondingly pinned across trees on the panel. -/
theorem panel_tajima_invariant (t₁ t₂ : RefTree) :
    tajimaNum6 t₁ panel = tajimaNum6 t₂ panel := by
  cases t₁ <;> cases t₂ <;> rfl

end Descent.Pangenome
