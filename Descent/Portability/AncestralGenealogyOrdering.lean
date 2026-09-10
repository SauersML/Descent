/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralCladePartition
import Descent.Portability.AncestralGenealogyLaw
import Descent.Portability.OrderedCladeLaw

assert_below Descent.Decision Descent.Program

/-!
The branch compiler's ordering follows from the actual ancestral transitions.
Older branch clades contain every younger clade that they intersect, which
justifies the shared-ancestor nucleotide updates on the compiled genealogy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralGenealogyOrdering

open Coalescent.FiniteGenomeAncestry MarkedAncestralLaw AncestralBranchExposure
open AncestralCladePartition AncestralGenealogyLaw GenealogyGenotypeLaw OrderedCladeLaw
open scoped NNReal

variable {D L n : ℕ}

theorem mem_intervalBranchesAux (locus : Fin L) (exposure : ℝ≥0)
    (lineages : List (Lineage D L n)) (branch : Branch n)
    (hbranch : branch ∈ intervalBranchesAux locus exposure lineages) :
    ∃ lineage ∈ lineages, branch.descendants = locusDescendants lineage.2 locus := by
  induction lineages with
  | nil => simp [intervalBranchesAux] at hbranch
  | cons lineage rest ih =>
      by_cases hne : (locusDescendants lineage.2 locus).Nonempty
      · simp only [intervalBranchesAux, hne, ↓reduceDIte, List.mem_cons] at hbranch
        rcases hbranch with rfl | hbranch
        · exact ⟨lineage, List.mem_cons_self, rfl⟩
        · obtain ⟨old, hold, heq⟩ := ih hbranch
          exact ⟨old, List.mem_cons_of_mem _ hold, heq⟩
      · simp only [intervalBranchesAux, hne, ↓reduceDIte] at hbranch
        obtain ⟨old, hold, heq⟩ := ih hbranch
        exact ⟨old, List.mem_cons_of_mem _ hold, heq⟩

theorem mem_intervalBranches (state : State D L n) (locus : Fin L) (exposure : ℝ≥0)
    (branch : Branch n) (hbranch : branch ∈ intervalBranches state locus exposure) :
    ∃ lineage ∈ state.val, branch.descendants = locusDescendants lineage.2 locus := by
  obtain ⟨lineage, hlineage, heq⟩ :=
    mem_intervalBranchesAux locus exposure state.val.toList branch hbranch
  exact ⟨lineage, Finset.mem_toList.mp hlineage, heq⟩

private theorem pairwise_of_members {A : Type*} (relation : A → A → Prop) (values : List A)
    (h : ∀ a ∈ values, ∀ b ∈ values, relation a b) : values.Pairwise relation := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro b hb
        exact h a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
      · exact ih (fun b hb c hc ↦ h b (List.mem_cons_of_mem _ hb)
          c (List.mem_cons_of_mem _ hc))

theorem intervalBranches_ordered (state : State D L n) (locus : Fin L) (exposure : ℝ≥0) :
    Ordered (intervalBranches state locus exposure) := by
  apply pairwise_of_members
  intro older holder younger hyounger
  obtain ⟨a, ha, hea⟩ := mem_intervalBranches state locus exposure older holder
  obtain ⟨b, hb, heb⟩ := mem_intervalBranches state locus exposure younger hyounger
  unfold Precedes
  rw [hea, heb]
  exact (Extends.refl state).2 a ha b hb locus

/-- Every compiled branch descends from a coarser active clade than every
intersecting clade in an earlier ancestral configuration. -/
theorem traceBranches_extends (locus : Fin L) (mutationRate : ℝ≥0)
    {count : ℕ} {earlier start : State D L n} (trace : Trace count start)
    (hext : Extends earlier start) (duration : ℝ≥0) (times : Fin count → ℝ≥0)
    (branch : Branch n) (hbranch : branch ∈ traceBranches locus mutationRate trace duration times)
    (lineage : Lineage D L n) (hlineage : lineage ∈ earlier.val) :
    Disjoint branch.descendants (locusDescendants lineage.2 locus) ∨
      locusDescendants lineage.2 locus ⊆ branch.descendants := by
  induction count generalizing start duration with
  | zero =>
      obtain ⟨old, hold, heq⟩ := mem_intervalBranches start locus _ branch hbranch
      rw [heq]
      exact hext.2 old hold lineage hlineage locus
  | succ count ih =>
      rcases List.mem_append.mp hbranch with hrest | hfirst
      · exact ih trace.2 (hext.trans (extends_proposal start trace.1)) _ _ hrest
      · obtain ⟨old, hold, heq⟩ := mem_intervalBranches start locus _ branch hfirst
        rw [heq]
        exact hext.2 old hold lineage hlineage locus

/-- The compiler always produces an ordered genealogy. The ordering is a
consequence of migration, recombination, and coalescence, not a caller input. -/
theorem traceBranches_ordered (locus : Fin L) (mutationRate : ℝ≥0)
    {count : ℕ} {start : State D L n} (trace : Trace count start)
    (duration : ℝ≥0) (times : Fin count → ℝ≥0) :
    Ordered (traceBranches locus mutationRate trace duration times) := by
  induction count generalizing start duration with
  | zero => exact intervalBranches_ordered start locus _
  | succ count ih =>
      apply List.pairwise_append.mpr
      refine ⟨ih trace.2 _ _, intervalBranches_ordered start locus _, ?_⟩
      intro older holder younger hyounger
      obtain ⟨lineage, hlineage, heq⟩ := mem_intervalBranches start locus _ younger hyounger
      unfold Precedes
      rw [heq]
      exact traceBranches_extends locus mutationRate trace.2 (extends_proposal start trace.1)
        _ _ older holder lineage hlineage

end Descent.Portability.AncestralGenealogyOrdering

namespace Descent.Portability.AncestralGenealogyLaw

open Coalescent.FiniteGenomeAncestry MarkedAncestralLaw GenealogyGenotypeLaw
open scoped NNReal

variable {D L n count : ℕ}

/-- The rooted branch-kernel calculation compiled from a completed ancestry
trace. The compiler supplies its clade ordering as a proved invariant. -/
noncomputable def traceNucleotideLaw {start : State D L n} (trace : Trace count start)
    (duration : ℝ≥0) (times : Fin count → ℝ≥0) (mutationRate : ℝ≥0) (locus : Fin L)
    (_hcomplete : (terminal trace).val = ∅) (_hmono : Monotone times)
    (_htimes : ∀ i, times i ≤ duration) :
    FiniteReportLaw (Leaves n) :=
  rootedGenealogyLaw (traceBranches locus mutationRate trace duration times)

/-- Every leaf configuration probability is an explicit finite branch recursion,
conditional on the demographic ancestry trace and its times, together with
the derived ordering that justifies its shared-ancestor branch updates. -/
theorem traceNucleotide_expectation {start : State D L n} (trace : Trace count start)
    (duration : ℝ≥0) (times : Fin count → ℝ≥0) (mutationRate : ℝ≥0) (locus : Fin L)
    (hcomplete : (terminal trace).val = ∅) (hmono : Monotone times)
    (htimes : ∀ i, times i ≤ duration)
    (readout : Leaves n → ℝ) :
    OrderedCladeLaw.Ordered (traceBranches locus mutationRate trace duration times) ∧
    (traceNucleotideLaw trace duration times mutationRate locus
      hcomplete hmono htimes).expectation
        readout =
      (∑ root : NucleotideMutationLaw.Nucleotide,
        genealogyExpectation (traceBranches locus mutationRate trace duration times)
          (fun _ ↦ root) readout) / 4 :=
  ⟨AncestralGenealogyOrdering.traceBranches_ordered locus mutationRate trace duration times,
    rootedGenealogy_expectation _ readout⟩


end Descent.Portability.AncestralGenealogyLaw
