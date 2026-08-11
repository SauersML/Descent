/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.CovarianceStructure
import Descent.Pangenome.Linkage.Barrier

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Haplotype gluing and recombination closure

A sequence graph confounds three sets: observed chromosomes, mosaics obtainable by joining
observed local pieces, and arbitrary graph walks.  This file separates the first two without
choosing variants or graph nodes.

`TwoChartPanel` is the finite local-to-global core.  A global haplotype has a left and a right
restriction, and both restrict again to one overlap.  `observedSections` is the diagonal image
of the panel.  `matchingClosure` contains every compatible left/right matching family whose
two pieces occur somewhere in the panel, possibly on different chromosomes.

The main result is not a relabelling.  `matchingClosure_le_of_recombinationClosed` proves the
UNIVERSAL PROPERTY: matching closure is the least set containing the observed chromosomes and
closed under compatible crossover.  Thus one compatible crossover already generates the
entire two-chart local-to-global closure.  `matchingClosure_eq_sInter` states the same fact as
an intersection of all recombination-closed supersets.

The abstract closure is then identified with the repository's existing linkage language.
For one graph interface `s`, a matching family is exactly a donor pair in `mosaics [s]`, and
the gluing defect is exactly `phantoms [s]`.  Consequently its size is the pre-existing exact
fiber-square formula minus the observed panel size.  The sheaf language and the graph-splicing
language are therefore two theorems about one object, not parallel metaphors.

Finally `binaryGluingResidual_eq_tableDeterminant` proves that, for a normalized binary
two-locus table, the probabilistic local-to-global residual `p₁₁ - p₁· p·₁` is the classical
linkage-disequilibrium determinant `p₁₁ p₀₀ - p₁₀ p₀₁`.

This is the exact two-locus base case for a graph-native higher gluing theory.  No general
sheafification theorem is claimed here: the theorem proved is the two-chart crossover closure
from which that generalization must start.
-/

namespace Descent.Pangenome.HaplotypeGluing

open Set

universe u v w x

/-! ### Two genomic charts and their overlap -/

/-- A panel observed through two local charts with a common overlap. -/
structure TwoChartPanel
    (Global : Type u) (Left : Type v) (Right : Type w) (Overlap : Type x) where
  /-- Restriction of a global haplotype to the left chart. -/
  left : Global → Left
  /-- Restriction of a global haplotype to the right chart. -/
  right : Global → Right
  /-- Restriction from the left chart to the overlap. -/
  leftOverlap : Left → Overlap
  /-- Restriction from the right chart to the overlap. -/
  rightOverlap : Right → Overlap
  /-- The two restrictions of an observed global haplotype agree. -/
  compatible : ∀ h, leftOverlap (left h) = rightOverlap (right h)

namespace TwoChartPanel

variable {Global : Type u} {Left : Type v} {Right : Type w} {Overlap : Type x}

/-- The pair of local sections carried by an observed global haplotype. -/
def chart (P : TwoChartPanel Global Left Right Overlap) (h : Global) : Left × Right :=
  (P.left h, P.right h)

/-- A left/right pair satisfies the matching condition on the overlap. -/
def Compatible (P : TwoChartPanel Global Left Right Overlap) (z : Left × Right) : Prop :=
  P.leftOverlap z.1 = P.rightOverlap z.2

/-- Global chromosomes actually observed in the panel, represented in the two charts. -/
def observedSections (P : TwoChartPanel Global Left Right Overlap) : Set (Left × Right) :=
  Set.range P.chart

/-- Compatible local pieces observed somewhere in the left and right marginals.  The donors
of the two pieces need not be the same global chromosome. -/
def matchingClosure (P : TwoChartPanel Global Left Right Overlap) : Set (Left × Right) :=
  {z | P.Compatible z ∧ z.1 ∈ Set.range P.left ∧ z.2 ∈ Set.range P.right}

/-- Cross the left piece of `a` with the right piece of `b`. -/
def splice (a b : Left × Right) : Left × Right := (a.1, b.2)

/-- A collection is closed under every crossover whose two chosen pieces match on the
overlap. -/
def RecombinationClosed (P : TwoChartPanel Global Left Right Overlap)
    (T : Set (Left × Right)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, P.Compatible (splice a b) → splice a b ∈ T

/-- Every observed chromosome is a compatible matching family. -/
theorem observedSections_subset_matchingClosure (P : TwoChartPanel Global Left Right Overlap) :
    P.observedSections ⊆ P.matchingClosure := by
  rintro z ⟨h, rfl⟩
  exact ⟨P.compatible h, ⟨h, rfl⟩, ⟨h, rfl⟩⟩

/-- Matching families are closed under compatible crossover. -/
theorem matchingClosure_recombinationClosed (P : TwoChartPanel Global Left Right Overlap) :
    P.RecombinationClosed P.matchingClosure := by
  rintro a ⟨-, haLeft, -⟩ b ⟨-, -, hbRight⟩ hab
  exact ⟨hab, haLeft, hbRight⟩

/-- **Universal property of two-chart recombination closure.**

Any recombination-closed collection containing the observed chromosomes contains every
compatible matching family.  Together with `observedSections_subset_matchingClosure` and
`matchingClosure_recombinationClosed`, this says that matching closure is the LEAST such
collection.  The proof also shows that one crossover suffices: choose one observed donor for
the left piece and one for the right piece. -/
theorem matchingClosure_le_of_recombinationClosed
    (P : TwoChartPanel Global Left Right Overlap) (T : Set (Left × Right))
    (hObserved : P.observedSections ⊆ T) (hClosed : P.RecombinationClosed T) :
    P.matchingClosure ⊆ T := by
  rintro z ⟨hz, ⟨hLeft, hhLeft⟩, ⟨hRight, hhRight⟩⟩
  have ha : P.chart hLeft ∈ T := hObserved ⟨hLeft, rfl⟩
  have hb : P.chart hRight ∈ T := hObserved ⟨hRight, rfl⟩
  have hsplice : splice (P.chart hLeft) (P.chart hRight) = z := by
    apply Prod.ext
    · exact hhLeft
    · exact hhRight
  rw [← hsplice]
  exact hClosed _ ha _ hb (by simpa [hsplice] using hz)

/-- The least-closure theorem in literal closure-system form: matching closure is the
intersection of all recombination-closed supersets of the observed panel. -/
theorem matchingClosure_eq_sInter (P : TwoChartPanel Global Left Right Overlap) :
    P.matchingClosure =
      ⋂₀ {T : Set (Left × Right) |
        P.observedSections ⊆ T ∧ P.RecombinationClosed T} := by
  apply Set.Subset.antisymm
  · intro z hz
    refine Set.mem_sInter.mpr fun T hT ↦ ?_
    exact P.matchingClosure_le_of_recombinationClosed T hT.1 hT.2 hz
  · intro z hz
    exact Set.mem_sInter.mp hz P.matchingClosure
      ⟨P.observedSections_subset_matchingClosure, P.matchingClosure_recombinationClosed⟩

/-- Locally observed, overlap-compatible haplotypes absent from the observed global panel. -/
def gluingDefect (P : TwoChartPanel Global Left Right Overlap) : Set (Left × Right) :=
  P.matchingClosure \ P.observedSections

/-- The observed haplotypes satisfy effective two-chart gluing when every locally observed,
overlap-compatible matching family is already globally observed. -/
def HasGluing (P : TwoChartPanel Global Left Right Overlap) : Prop :=
  P.matchingClosure ⊆ P.observedSections

/-- **Gluing holds exactly when the observed panel is already recombination-closed.**  This
is the logical form of the sheafification/recombination claim for two charts: adding all
matching families changes nothing precisely when compatible crossover changes nothing. -/
theorem hasGluing_iff_observedSections_recombinationClosed
    (P : TwoChartPanel Global Left Right Overlap) :
    P.HasGluing ↔ P.RecombinationClosed P.observedSections := by
  constructor
  · intro hGluing a ha b hb hab
    apply hGluing
    exact P.matchingClosure_recombinationClosed _
      (P.observedSections_subset_matchingClosure ha) _
      (P.observedSections_subset_matchingClosure hb) hab
  · intro hClosed
    exact P.matchingClosure_le_of_recombinationClosed P.observedSections
      (Set.Subset.refl _) hClosed

/-- The gluing axiom holds exactly when its defect set is empty. -/
theorem gluingDefect_eq_empty_iff (P : TwoChartPanel Global Left Right Overlap) :
    P.gluingDefect = ∅ ↔ P.HasGluing := by
  constructor
  · intro hEmpty z hz
    by_contra hMissing
    have hzDefect : z ∈ P.gluingDefect := ⟨hz, hMissing⟩
    rw [hEmpty] at hzDefect
    exact hzDefect
  · intro hGluing
    apply Set.eq_empty_iff_forall_not_mem.mpr
    rintro z ⟨hz, hMissing⟩
    exact hMissing (hGluing hz)

/-! ### One graph interface is exactly a two-chart gluing problem -/

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The two charts on either side of one graph interface.  A donor is visible as itself in
each module and only its interface state is visible on the overlap. -/
def interfacePanel (s : ι → ι) : TwoChartPanel ι ι ι ι where
  left := id
  right := id
  leftOverlap := s
  rightOverlap := s
  compatible := fun _ ↦ rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem compatible_interfacePanel (s : ι → ι) (h g : ι) :
    (interfacePanel s).Compatible (h, g) ↔ s h = s g :=
  Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_matchingClosure_interfacePanel (s : ι → ι) (h g : ι) :
    (h, g) ∈ (interfacePanel s).matchingClosure ↔ s h = s g := by
  simp [matchingClosure, interfacePanel, Compatible]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_observedSections_interfacePanel (s : ι → ι) (h g : ι) :
    (h, g) ∈ (interfacePanel s).observedSections ↔ h = g := by
  constructor
  · rintro ⟨a, ha⟩
    change (a, a) = (h, g) at ha
    injection ha with hLeft hRight
    exact hLeft.symm.trans hRight
  · rintro rfl
    exact ⟨h, rfl⟩

@[simp]
theorem pair_mem_mosaics_singleton_iff (s : ι → ι) (h g : ι) :
    [h, g] ∈ Linkage.mosaics [s] ↔ s h = s g := by
  simp [Linkage.mosaics, Linkage.mosaicsFrom, eq_comm]

/-- **The abstract matching closure is the existing one-interface mosaic language.** -/
theorem pair_mem_mosaics_iff_matchingClosure (s : ι → ι) (h g : ι) :
    [h, g] ∈ Linkage.mosaics [s] ↔
      (h, g) ∈ (interfacePanel s).matchingClosure := by
  rw [pair_mem_mosaics_singleton_iff, mem_matchingClosure_interfacePanel]

@[simp]
theorem mem_gluingDefect_interfacePanel (s : ι → ι) (h g : ι) :
    (h, g) ∈ (interfacePanel s).gluingDefect ↔ s h = s g ∧ h ≠ g := by
  change ((h, g) ∈ (interfacePanel s).matchingClosure ∧
    (h, g) ∉ (interfacePanel s).observedSections) ↔ _
  rw [mem_matchingClosure_interfacePanel, mem_observedSections_interfacePanel]

/-- **An interface satisfies haplotype gluing exactly when it preserves donor identity.**
Any noninjective merge creates the crossed pair of the merged donors as a locally compatible
but globally absent section; an injective interface admits only diagonal matching families.
This is the local-to-global form of the linkage exactness barrier. -/
theorem interfacePanel_hasGluing_iff_injective (s : ι → ι) :
    (interfacePanel s).HasGluing ↔ Function.Injective s := by
  constructor
  · intro hGluing h g hState
    apply (mem_observedSections_interfacePanel s h g).mp
    apply hGluing
    exact (mem_matchingClosure_interfacePanel s h g).mpr hState
  · intro hInjective z hz
    rcases z with ⟨h, g⟩
    apply (mem_observedSections_interfacePanel s h g).mpr
    exact hInjective ((mem_matchingClosure_interfacePanel s h g).mp hz)

/-- **At one interface, the sheaf-style gluing defect is exactly the graph's phantom
recombinant set.** -/
theorem pair_mem_phantoms_iff_gluingDefect (s : ι → ι) (h g : ι) :
    [h, g] ∈ Linkage.phantoms [s] ↔
      (h, g) ∈ (interfacePanel s).gluingDefect := by
  rw [Linkage.phantoms, Finset.mem_sdiff, pair_mem_mosaics_singleton_iff,
    mem_gluingDefect_interfacePanel]
  simp [Linkage.diagonals]

/-- The exact size of the one-interface gluing defect: the sum of squared overlap-fiber
sizes, less the observed diagonal panel. -/
theorem card_phantoms_singleton_eq_gluing_defect (s : ι → ι) :
    (Linkage.phantoms [s]).card =
      ∑ a ∈ Finset.univ.image s, (Linkage.stateFiber s a).card ^ 2 - Fintype.card ι := by
  rw [Linkage.card_phantoms, Linkage.card_mosaics_singleton]

end TwoChartPanel

/-! ### Classical binary LD is the probabilistic gluing residual -/

/-- Probability mass of a global section minus the mass predicted by independent gluing of
its left and right marginals. -/
noncomputable def probabilisticGluingResidual (joint leftMarginal rightMarginal : ℝ) : ℝ :=
  joint - leftMarginal * rightMarginal

/-- The gluing residual for the `11` cell of a binary two-locus table. -/
noncomputable def binaryGluingResidual (_p00 p01 p10 p11 : ℝ) : ℝ :=
  probabilisticGluingResidual p11 (p10 + p11) (p01 + p11)

/-- The classical determinant form of two-locus linkage disequilibrium. -/
noncomputable def binaryLinkageDeterminant (p00 p01 p10 p11 : ℝ) : ℝ :=
  p11 * p00 - p10 * p01

/-- **Classical `D` is the normalized binary gluing obstruction.**  Normalization is the
only hypothesis; nonnegativity is needed for a probability interpretation, not for the
identity. -/
theorem binaryGluingResidual_eq_tableDeterminant
    (p00 p01 p10 p11 : ℝ) (hTotal : p00 + p01 + p10 + p11 = 1) :
    binaryGluingResidual p00 p01 p10 p11 =
      binaryLinkageDeterminant p00 p01 p10 p11 := by
  unfold binaryGluingResidual probabilisticGluingResidual binaryLinkageDeterminant
  linear_combination -p11 * hTotal

/-- The corpus's existing admixture-LD observable is exactly a probabilistic gluing
residual, so the new local-to-global interpretation does not introduce a second LD scalar. -/
theorem admixtureLDTwoLocus_eq_probabilisticGluingResidual
    (alpha pA qA pB qB : ℝ) :
    Descent.Foundations.admixtureLDTwoLocus alpha pA qA pB qB =
      probabilisticGluingResidual
        (Descent.Foundations.haplotypeFreqAdmixed alpha pA qA pB qB)
        (Descent.Core.convexCombination alpha pA pB)
        (Descent.Core.convexCombination alpha qA qB) :=
  rfl

end Descent.Pangenome.HaplotypeGluing
