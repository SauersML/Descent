/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GenealogyGenotypeLaw

assert_below Descent.Decision Descent.Program

/-!
The ordering condition under which shared-clade nucleotide updates represent
a genealogy. Every later clade is either disjoint from an earlier clade or
contained in it. The proofs retain the common ancestral nucleotide needed
by each branch kernel throughout the ordered calculation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OrderedCladeLaw

open GenealogyGenotypeLaw NucleotideMutationLaw

variable {n : ℕ}

def Precedes (older younger : Branch n) : Prop :=
  Disjoint older.descendants younger.descendants ∨ younger.descendants ⊆ older.descendants

def Ordered (branches : List (Branch n)) : Prop := branches.Pairwise Precedes

def Ready (branches : List (Branch n)) (leaves : Leaves n) : Prop :=
  ∀ branch ∈ branches, Homogeneous branch leaves

theorem ready_uniform (branches : List (Branch n)) (root : Nucleotide) :
    Ready branches (fun _ ↦ root) := by
  intro branch _ sample _
  rfl

/-- An older branch update preserves the shared ancestral base on every later
clade, including repeated intervals belonging to the same clade. -/
theorem homogeneous_overwrite (older younger : Branch n) (horder : Precedes older younger)
    (leaves : Leaves n) (hready : Homogeneous younger leaves) (base : Nucleotide) :
    Homogeneous younger (overwrite older leaves base) := by
  intro sample hsample
  rcases horder with hdis | hsub
  · have hs : sample ∉ older.descendants := by
      intro h
      exact Finset.disjoint_left.mp hdis h hsample
    have hr : younger.representative ∉ older.descendants := by
      intro h
      exact Finset.disjoint_left.mp hdis h younger.representative_mem
    simp [overwrite, hs, hr, hready sample hsample]
  · simp [overwrite, hsub hsample, hsub younger.representative_mem]

/-- Every one of the four possible next branch endpoints leaves the remaining
ordered genealogy ready for its next shared-ancestor mutation draw. -/
theorem ready_after_head (first : Branch n) (rest : List (Branch n))
    (horder : Ordered (first :: rest)) (leaves : Leaves n)
    (hready : Ready (first :: rest) leaves) (base : Nucleotide) :
    Ready rest (overwrite first leaves base) := by
  intro branch hbranch
  exact homogeneous_overwrite first branch ((List.pairwise_cons.mp horder).1 branch hbranch)
    leaves (hready branch (List.mem_cons_of_mem _ hbranch)) base

theorem ordered_tail (first : Branch n) (rest : List (Branch n))
    (horder : Ordered (first :: rest)) : Ordered rest :=
  (List.pairwise_cons.mp horder).2

end Descent.Portability.OrderedCladeLaw
