/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NucleotideMutationLaw

assert_below Descent.Decision Descent.Program

/-!
Joint sample nucleotide laws conditional on an ordered clade genealogy. A
branch updates its whole descendant clade with one shared endpoint draw. The
result consequently retains the dependence between descendants of a branch.

The branch list must be in ancestral-to-descendant order to represent the
genealogy. This module proves the resulting finite transition calculation;
construction of that order from the demographic ancestry is separate. Site
presence and mutation-table allele ordering are not nucleotide endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GenealogyGenotypeLaw

open FiniteReportLaw NucleotideMutationLaw
open scoped NNReal

variable {n : ℕ}

structure Branch (n : ℕ) where
  descendants : Finset (Fin n)
  representative : Fin n
  representative_mem : representative ∈ descendants
  exposure : ℝ≥0

abbrev Leaves (n : ℕ) := Fin n → Nucleotide

def overwrite (branch : Branch n) (leaves : Leaves n) (base : Nucleotide) : Leaves n :=
  fun sample ↦ if sample ∈ branch.descendants then base else leaves sample

theorem overwrite_representative (branch : Branch n) (leaves : Leaves n) (base : Nucleotide) :
    overwrite branch leaves base branch.representative = base := by
  simp [overwrite, branch.representative_mem]

theorem overwrite_overwrite (branch : Branch n) (leaves : Leaves n)
    (first second : Nucleotide) :
    overwrite branch (overwrite branch leaves first) second = overwrite branch leaves second := by
  funext sample
  by_cases h : sample ∈ branch.descendants <;> simp [overwrite, h]

theorem overwrite_commute (first second : Branch n)
    (hdisjoint : Disjoint first.descendants second.descendants)
    (leaves : Leaves n) (firstBase secondBase : Nucleotide) :
    overwrite second (overwrite first leaves firstBase) secondBase =
      overwrite first (overwrite second leaves secondBase) firstBase := by
  funext sample
  by_cases hf : sample ∈ first.descendants
  · have hs : sample ∉ second.descendants :=
      fun hs ↦ Finset.disjoint_left.mp hdisjoint hf hs
    simp [overwrite, hf, hs]
  · simp [overwrite, hf]

def Homogeneous (branch : Branch n) (leaves : Leaves n) : Prop :=
  ∀ sample ∈ branch.descendants, leaves sample = leaves branch.representative

theorem overwrite_original (branch : Branch n) (leaves : Leaves n)
    (h : Homogeneous branch leaves) :
    overwrite branch leaves (leaves branch.representative) = leaves := by
  funext sample
  by_cases hs : sample ∈ branch.descendants
  · simp [overwrite, hs, h sample hs]
  · simp [overwrite, hs]

noncomputable def branchKernel (branch : Branch n) (leaves : Leaves n) :
    FiniteReportLaw (Leaves n) :=
  (branchLaw branch.exposure (leaves branch.representative)).pushforward (overwrite branch leaves)

/-- A branch has four possible joint endpoint configurations, with probabilities
derived from every possible recurrent mutation count by the JC69 law. -/
theorem branchKernel_expectation (branch : Branch n) (leaves : Leaves n)
    (readout : Leaves n → ℝ) :
    (branchKernel branch leaves).expectation readout =
      ∑ base : Nucleotide,
        (1 / 4 + Real.exp (-4 * (branch.exposure : ℝ) / 3) *
          ((if base = leaves branch.representative then 1 else 0) - 1 / 4)) *
          readout (overwrite branch leaves base) := by
  rw [branchKernel, expectation_pushforward]
  simp only [expectation, branch_mass]

/-- Mutations on a shared branch leave all its descendants equal at the branch
endpoint, regardless of the number of recurrent or back mutations. -/
theorem shared_branch_equal (branch : Branch n) (leaves : Leaves n)
    (first second : Fin n) (hfirst : first ∈ branch.descendants)
    (hsecond : second ∈ branch.descendants) :
    (branchKernel branch leaves).expectation
      (fun target ↦ if target first = target second then 1 else 0) = 1 := by
  rw [branchKernel, expectation_pushforward]
  simp [expectation, overwrite, hfirst, hsecond, mass_sum]

/-- Branches with disjoint descendant clades commute. Consequently the order
chosen for contemporaneous disjoint branches does not affect their joint law. -/
theorem branchKernel_commute (first second : Branch n)
    (hdisjoint : Disjoint first.descendants second.descendants) (leaves : Leaves n) :
    (branchKernel first leaves).bind (branchKernel second) =
      (branchKernel second leaves).bind (branchKernel first) := by
  have hf : first.representative ∉ second.descendants :=
    fun hf ↦ Finset.disjoint_left.mp hdisjoint first.representative_mem hf
  have hs : second.representative ∉ first.descendants :=
    fun hs ↦ Finset.disjoint_left.mp hdisjoint hs second.representative_mem
  apply (eq_iff_singleton_expectations_eq _ _).mpr
  intro target
  simp only [expectation_bind, branchKernel, expectation_pushforward]
  simp only [expectation, overwrite, hf, hs, ↓reduceIte, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hupdate := overwrite_commute first second hdisjoint leaves b a
  rw [hupdate]
  ring

noncomputable def genealogyLaw : List (Branch n) → Leaves n → FiniteReportLaw (Leaves n)
  | [], leaves => pointMass leaves
  | branch :: rest, leaves => (branchKernel branch leaves).bind (genealogyLaw rest)

/-- The exact joint expectation recursion has only four terms at each branch.
Its dependence on all leaf states remains inside the readout. -/
noncomputable def genealogyExpectation : List (Branch n) → Leaves n → (Leaves n → ℝ) → ℝ
  | [], leaves, readout => readout leaves
  | branch :: rest, leaves, readout =>
      ∑ base : Nucleotide,
        (1 / 4 + Real.exp (-4 * (branch.exposure : ℝ) / 3) *
          ((if base = leaves branch.representative then 1 else 0) - 1 / 4)) *
          genealogyExpectation rest (overwrite branch leaves base) readout

theorem genealogy_expectation (branches : List (Branch n)) (leaves : Leaves n)
    (readout : Leaves n → ℝ) :
    (genealogyLaw branches leaves).expectation readout =
      genealogyExpectation branches leaves readout := by
  induction branches generalizing leaves with
  | nil => exact expectation_pointMass leaves readout
  | cons branch rest ih =>
      rw [genealogyLaw, expectation_bind, branchKernel_expectation]
      simp only [ih, genealogyExpectation]

/-- Exact joint configuration probabilities follow by taking a singleton
readout, without replacing sample dependence by independent marginals. -/
theorem genealogy_mass (branches : List (Branch n)) (leaves target : Leaves n) :
    (genealogyLaw branches leaves).mass target =
      genealogyExpectation branches leaves (fun output ↦ if output = target then 1 else 0) := by
  classical
  simpa [expectation] using
    genealogy_expectation branches leaves (fun output ↦ if output = target then 1 else 0)

/-- Conditional JC69 root law, uniform over four bases. All sampled descendants
start with the same root draw before the clade mutations are applied. -/
noncomputable def rootLaw : FiniteReportLaw Nucleotide where
  mass := fun _ ↦ 1 / 4
  mass_nonneg := by intro _; norm_num
  mass_sum := by norm_num

noncomputable def rootedGenealogyLaw (branches : List (Branch n)) :
    FiniteReportLaw (Leaves n) :=
  rootLaw.bind (fun root ↦ genealogyLaw branches (fun _ ↦ root))

theorem rootedGenealogy_expectation (branches : List (Branch n)) (readout : Leaves n → ℝ) :
    (rootedGenealogyLaw branches).expectation readout =
      (∑ root : Nucleotide, genealogyExpectation branches (fun _ ↦ root) readout) / 4 := by
  rw [rootedGenealogyLaw, expectation_bind]
  simp only [genealogy_expectation]
  simp only [expectation, rootLaw, one_div_mul_eq_div,
    Finset.sum_div]

end Descent.Portability.GenealogyGenotypeLaw
