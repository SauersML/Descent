/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GenealogyGenotypeLaw
import Mathlib.Data.Fintype.List

assert_below Descent.Decision Descent.Program

/-!
Finite mutation memory sufficient to retain ordered allele discovery and site
presence, including recurrent and back mutations. The catalogue appends a
nucleotide only on its first occurrence. A mutation changes the whole clade,
records its derived nucleotide, and records that a mutation occurred even if
later mutations restore the ancestral nucleotide.

The order supplied to these updates is part of their input. Matching it to
tskit's mutation-table order remains necessary before identifying its allele
indices with these indices. Branch endpoint probabilities cannot establish
that match because they omit the mutation history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OrderedMutationCatalogue

open FiniteReportLaw GenealogyGenotypeLaw NucleotideMutationLaw ProbabilityTheory
open scoped NNReal

variable {n : ℕ}

abbrev Catalogue := { bases : List Nucleotide // bases.Nodup }

def remember (catalogue : Catalogue) (base : Nucleotide) : Catalogue :=
  if h : base ∈ catalogue.val then catalogue else
    ⟨catalogue.val ++ [base], by
      have hsep : ∀ a ∈ catalogue.val, ¬ a = base := by
        intro a ha heq
        exact h (heq ▸ ha)
      simpa [List.nodup_append] using
        And.intro catalogue.property hsep⟩

theorem mem_remember (catalogue : Catalogue) (base : Nucleotide) :
    base ∈ (remember catalogue base).val := by
  unfold remember
  split_ifs with h
  · exact h
  · simp

theorem mem_remember_of_mem (catalogue : Catalogue) (first base : Nucleotide)
    (hfirst : first ∈ catalogue.val) : first ∈ (remember catalogue base).val := by
  unfold remember
  split_ifs <;> simp_all

/-- Appending a newly discovered allele preserves every earlier allele index. -/
theorem remember_old_index (catalogue : Catalogue) (first base : Nucleotide)
    (hfirst : first ∈ catalogue.val) :
    (remember catalogue base).val.idxOf first = catalogue.val.idxOf first := by
  unfold remember
  split_ifs
  · rfl
  · exact List.idxOf_append_of_mem hfirst

theorem remember_new_index (catalogue : Catalogue) (base : Nucleotide)
    (hbase : base ∉ catalogue.val) :
    (remember catalogue base).val.idxOf base = catalogue.val.length := by
  simp [remember, hbase, List.idxOf_append_of_notMem]

abbrev SiteState (n : ℕ) := Leaves n × Catalogue × Bool

def Covered (state : SiteState n) : Prop :=
  ∀ sample, state.1 sample ∈ state.2.1.val

def initialState (root : Nucleotide) : SiteState n :=
  (fun _ ↦ root, ⟨[root], by simp⟩, false)

theorem initialState_covered (root : Nucleotide) : Covered (initialState (n := n) root) := by
  intro sample
  simp [initialState]

def recordMutation (branch : Branch n) (state : SiteState n) (base : Nucleotide) : SiteState n :=
  (overwrite branch state.1 base, remember state.2.1 base, true)

theorem recordMutation_covered (branch : Branch n) (state : SiteState n)
    (base : Nucleotide) (hstate : Covered state) : Covered (recordMutation branch state base) := by
  intro sample
  change (if sample ∈ branch.descendants then base else state.1 sample) ∈
    (remember state.2.1 base).val
  split_ifs
  · exact mem_remember state.2.1 base
  · exact mem_remember_of_mem state.2.1 (state.1 sample) base (hstate sample)

/-- Allele index, distinct from the nucleotide's fixed four-state code. -/
def alleleIndex (state : SiteState n) (sample : Fin n) : ℕ :=
  state.2.1.val.idxOf (state.1 sample)

theorem alleleIndex_decodes (state : SiteState n) (hstate : Covered state) (sample : Fin n) :
    state.2.1.val[alleleIndex state sample]? = some (state.1 sample) :=
  List.getElem?_idxOf (hstate sample)

theorem alleleIndex_lt_four (state : SiteState n) (hstate : Covered state) (sample : Fin n) :
    alleleIndex state sample < 4 := by
  have hlength : state.2.1.val.length ≤ 4 := by
    simpa using state.2.1.property.length_le_card
  exact (List.idxOf_lt_length_iff.mpr (hstate sample)).trans_le hlength

/-- Diploid dosage in the simulator sums allele indices, which can range up to
six at four-state sites; BED encoding clips this sum to two. -/
def rawDosage (state : SiteState n) (first second : Fin n) : ℕ :=
  alleleIndex state first + alleleIndex state second

def bedDosage (state : SiteState n) (first second : Fin n) : ℕ :=
  min (rawDosage state first second) 2

theorem rawDosage_le_six (state : SiteState n) (hstate : Covered state)
    (first second : Fin n) : rawDosage state first second ≤ 6 := by
  have hf := alleleIndex_lt_four state hstate first
  have hs := alleleIndex_lt_four state hstate second
  unfold rawDosage
  omega

theorem bedDosage_le_two (state : SiteState n) (first second : Fin n) :
    bedDosage state first second ≤ 2 := min_le_right _ _

/-- Two valid mutation catalogues with the same ancestral allele and the same
sample nucleotides produce different raw dosages. The earlier derived allele
in the second history changes the discovery index of the final nucleotide. -/
theorem endpoints_do_not_determine_dosage :
    ∃ first second : SiteState 2,
      Covered first ∧ Covered second ∧ first.1 = second.1 ∧
        rawDosage first 0 1 = 2 ∧ rawDosage second 0 1 = 4 ∧
          bedDosage first 0 1 = bedDosage second 0 1 := by
  let first : SiteState 2 := (fun _ ↦ 1, ⟨[0, 1], by decide⟩, true)
  let second : SiteState 2 := (fun _ ↦ 1, ⟨[0, 2, 1], by decide⟩, true)
  exact ⟨first, second, by intro sample; change (1 : Nucleotide) ∈ [0, 1]; decide,
    by intro sample; change (1 : Nucleotide) ∈ [0, 2, 1]; decide,
    rfl, by decide, by decide, by decide⟩

noncomputable def mutationKernel (branch : Branch n) (state : SiteState n) :
    FiniteReportLaw (SiteState n) :=
  (jumpLaw (state.1 branch.representative)).pushforward (recordMutation branch state)

noncomputable def mutationCountLaw (branch : Branch n) (state : SiteState n) (count : ℕ) :
    FiniteReportLaw (SiteState n) :=
  ExactFiniteHistoryLaw.propagate (pointMass state) (fun _ ↦ mutationKernel branch) count

theorem mutationKernel_unsupported (branch : Branch n) (state target : SiteState n)
    (hstate : Covered state) (htarget : ¬ Covered target) :
    (mutationKernel branch state).mass target = 0 := by
  classical
  have hne (base : Nucleotide) : target ≠ recordMutation branch state base := by
    intro heq
    exact htarget (heq ▸ recordMutation_covered branch state base hstate)
  simp [mutationKernel, pushforward, FiniteReportLaw.bind, pointMass, hne]

theorem mutationCount_unsupported (branch : Branch n) (state target : SiteState n)
    (hstate : Covered state) (htarget : ¬ Covered target) (count : ℕ) :
    (mutationCountLaw branch state count).mass target = 0 := by
  classical
  induction count generalizing target with
  | zero =>
      have hne : target ≠ state := by intro heq; exact htarget (heq ▸ hstate)
      simp [mutationCountLaw, ExactFiniteHistoryLaw.propagate, pointMass, hne]
  | succ count ih =>
      change ∑ middle, (mutationCountLaw branch state count).mass middle *
        (mutationKernel branch middle).mass target = 0
      apply Finset.sum_eq_zero
      intro middle _
      by_cases hm : Covered middle
      · rw [mutationKernel_unsupported branch middle target hm htarget, mul_zero]
      · rw [ih middle hm, zero_mul]

/-- Discarding mutation memory recovers the exact recurrent-mutation count law
on a homogeneous descendant clade. This proves the memory is an extension of
the nucleotide process, rather than a competing endpoint model. -/
theorem mutationCount_nucleotide (branch : Branch n) (state : SiteState n)
    (hstate : Homogeneous branch state.1) (count : ℕ) (readout : Leaves n → ℝ) :
    (mutationCountLaw branch state count).expectation (fun target ↦ readout target.1) =
      (NucleotideMutationLaw.countLaw (state.1 branch.representative) count).expectation
        (fun base ↦ readout (overwrite branch state.1 base)) := by
  induction count generalizing readout with
  | zero =>
      simp [mutationCountLaw, NucleotideMutationLaw.countLaw, ExactFiniteHistoryLaw.propagate,
        expectation_pointMass, overwrite_original branch state.1 hstate]
  | succ count ih =>
      change ((mutationCountLaw branch state count).bind (mutationKernel branch)).expectation _ =
        FiniteReportLaw.expectation
          ((NucleotideMutationLaw.countLaw (state.1 branch.representative) count).bind jumpLaw) _
      rw [expectation_bind, expectation_bind]
      simp only [mutationKernel, expectation_pushforward]
      change (mutationCountLaw branch state count).expectation
        (fun target ↦ (jumpLaw (target.1 branch.representative)).expectation
          (fun base ↦ readout (overwrite branch target.1 base))) = _
      rw [ih (fun leaves ↦ (jumpLaw (leaves branch.representative)).expectation
        (fun base ↦ readout (overwrite branch leaves base)))]
      simp only [overwrite_representative, overwrite_overwrite]

private theorem coordinate_summable (branch : Branch n) (state target : SiteState n) :
    Summable (fun count ↦ poissonPMFReal branch.exposure count *
      (mutationCountLaw branch state count).mass target) := by
  apply (poissonPMFRealSum branch.exposure).summable.of_nonneg_of_le
  · intro count
    exact mul_nonneg poissonPMFReal_nonneg
      ((mutationCountLaw branch state count).mass_nonneg target)
  · intro count
    have h : (mutationCountLaw branch state count).mass target ≤ 1 := by
      rw [← (mutationCountLaw branch state count).mass_sum]
      exact Finset.single_le_sum (fun output _ ↦
        (mutationCountLaw branch state count).mass_nonneg output) (Finset.mem_univ target)
    exact mul_le_of_le_one_right poissonPMFReal_nonneg h

/-- The finite augmented branch law marginalizes infinitely many possible
mutation counts while retaining discovered alleles and mutation presence. -/
noncomputable def mutationBranchLaw (branch : Branch n) (state : SiteState n) :
    FiniteReportLaw (SiteState n) where
  mass := fun target ↦ ∑' count, poissonPMFReal branch.exposure count *
    (mutationCountLaw branch state count).mass target
  mass_nonneg := fun target ↦ tsum_nonneg (fun count ↦
    mul_nonneg poissonPMFReal_nonneg ((mutationCountLaw branch state count).mass_nonneg target))
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun target _ ↦ coordinate_summable branch state target)]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
    exact (poissonPMFRealSum branch.exposure).tsum_eq

theorem mutationBranch_expectation (branch : Branch n) (state : SiteState n)
    (readout : SiteState n → ℝ) :
    (mutationBranchLaw branch state).expectation readout =
      ∑' count, poissonPMFReal branch.exposure count *
        (mutationCountLaw branch state count).expectation readout := by
  unfold expectation mutationBranchLaw
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun target _ ↦
    (coordinate_summable branch state target).mul_right (readout target))]
  apply tsum_congr
  intro count
  simp only [Finset.mul_sum, mul_assoc]

theorem mutationBranch_covered (branch : Branch n) (state target : SiteState n)
    (hstate : Covered state) (hpositive : 0 < (mutationBranchLaw branch state).mass target) :
    Covered target := by
  by_contra htarget
  have hzero : (mutationBranchLaw branch state).mass target = 0 := by
    simp [mutationBranchLaw, mutationCount_unsupported branch state target hstate htarget]
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

/-- Marginalizing catalogue and site presence gives precisely the previously
derived JC69 clade endpoint law, for every nonlinear leaf readout. -/
theorem mutationBranch_nucleotide (branch : Branch n) (state : SiteState n)
    (hstate : Homogeneous branch state.1) (readout : Leaves n → ℝ) :
    (mutationBranchLaw branch state).expectation (fun target ↦ readout target.1) =
      (branchKernel branch state.1).expectation readout := by
  rw [mutationBranch_expectation]
  simp only [mutationCount_nucleotide branch state hstate]
  rw [branchKernel, expectation_pushforward]
  unfold expectation NucleotideMutationLaw.branchLaw
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun target _ ↦ ?_)]
  · apply tsum_congr
    intro count
    simp only [Finset.mul_sum, mul_assoc]
  · apply Summable.mul_right
    apply (poissonPMFRealSum branch.exposure).summable.of_nonneg_of_le
    · intro count
      exact mul_nonneg poissonPMFReal_nonneg
        ((NucleotideMutationLaw.countLaw (state.1 branch.representative) count).mass_nonneg target)
    · intro count
      have hmass :
          (NucleotideMutationLaw.countLaw (state.1 branch.representative) count).mass target ≤
            1 := by
        rw [← (NucleotideMutationLaw.countLaw (state.1 branch.representative) count).mass_sum]
        exact Finset.single_le_sum (fun base _ ↦
          (NucleotideMutationLaw.countLaw (state.1 branch.representative) count).mass_nonneg base)
            (Finset.mem_univ target)
      exact mul_le_of_le_one_right poissonPMFReal_nonneg hmass

def presentReadout (state : SiteState n) : ℝ := if state.2.2 then 1 else 0

theorem mutationCount_presence (branch : Branch n) (state : SiteState n) (count : ℕ) :
    (mutationCountLaw branch state count).expectation presentReadout =
      if count = 0 then presentReadout state else 1 := by
  cases count with
  | zero => simp [mutationCountLaw, ExactFiniteHistoryLaw.propagate, expectation_pointMass]
  | succ count =>
      change ((mutationCountLaw branch state count).bind (mutationKernel branch)).expectation _ = _
      rw [expectation_bind]
      simp only [mutationKernel, expectation_pushforward]
      simp [recordMutation, presentReadout,
        expectation, mass_sum]

/-- Back mutations do not erase site presence. The exact presence probability
depends on whether any mutation occurred, rather than endpoint inequality. -/
theorem mutationBranch_presence (branch : Branch n) (state : SiteState n) :
    (mutationBranchLaw branch state).expectation presentReadout =
      1 - Real.exp (-(branch.exposure : ℝ)) * (1 - presentReadout state) := by
  rw [mutationBranch_expectation]
  simp only [mutationCount_presence]
  have hpoint (count : ℕ) :
      poissonPMFReal branch.exposure count * (if count = 0 then presentReadout state else 1) =
        poissonPMFReal branch.exposure count -
          (if count = 0 then poissonPMFReal branch.exposure 0 * (1 - presentReadout state)
            else 0) := by
    split_ifs with h
    · subst count; ring
    · ring
  simp_rw [hpoint]
  rw [Summable.tsum_sub (poissonPMFRealSum branch.exposure).summable
    (hasSum_ite_eq (0 : ℕ)
      (poissonPMFReal branch.exposure 0 * (1 - presentReadout state))).summable]
  simp [no_mutation_mass, (poissonPMFRealSum branch.exposure).tsum_eq]

end Descent.Portability.OrderedMutationCatalogue
