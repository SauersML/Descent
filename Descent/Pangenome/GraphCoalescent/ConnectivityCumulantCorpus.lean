/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantDegree
import Descent.Pangenome.GraphCoalescent.Observation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The connectivity cumulant in the corpus vocabulary of coalescent states

`ConnectivityCumulant` proves Theorem D of the pangenome hidden-clock note on Mathlib's
`Finpartition`. The corpus states the coalescent on `Coalescent.ER n = Setoid (Fin n)`, and the
graph report is `observed s ξ = ξ ⊔ graphKer s` (`Observation`). This module transports
Theorem D to that vocabulary, so (D3) and the degree bound are statements about the interface
kernel `graphKer s` and the report `observed s π`.

`statePartitionEquiv` is the bijection between coalescent states and finite partitions of the
sample. A state goes to its partition into classes, `Finpartition.ofSetoid`, and a partition
goes to the kernel of its part map. `ofSetoid_le_ofSetoid_iff` shows the bijection preserves
the refinement order, and `ofSetoid_top` that it preserves the top state.
`observed_eq_top_iff_reportConnected` identifies the report being connected, `observed s π = ⊤`,
with `ReportConnected`. `instFintypeER` makes the states a finite type through the bijection.

`connectivityCumulant_graphKer_eq_sum_observed` is (D3) in the note's own form:
`C_q(z) = Σ_{π : q ⊔ π = ⊤} (∏_{B ∈ π} |B|!) z^{|π|}`, with `q = graphKer s`, the sum over
coalescent states with a connected report, and `|π| = Coalescent.blocks π`.
`natDegree_connectivityCumulant_graphKer_le` is the degree bound `n - w + 1`, with
`w = Linkage.width s` through `blocks_graphKer`.

## Empirical status

None. The bodies here are the transport of finite combinatorial identities along a bijection
between equivalence relations and finite partitions, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial
open scoped Classical

noncomputable section

variable {n : ℕ}

/-- Two individuals share a part of a coalescent state's partition exactly when the state
relates them. -/
theorem part_ofSetoid_eq_iff (ξ : Coalescent.ER n) (x y : Fin n) :
    (Finpartition.ofSetoid ξ).part x = (Finpartition.ofSetoid ξ).part y ↔ ξ.r x y := by
  constructor
  · intro h
    have hy : y ∈ (Finpartition.ofSetoid ξ).part y :=
      (Finpartition.ofSetoid ξ).mem_part_self.mpr (mem_univ y)
    rw [← h] at hy
    exact Finpartition.mem_part_ofSetoid_iff_rel.mp hy
  · intro h
    have hx : x ∈ (Finpartition.ofSetoid ξ).part y :=
      Finpartition.mem_part_ofSetoid_iff_rel.mpr (ξ.symm h)
    exact Finpartition.part_eq_of_mem _ ((Finpartition.ofSetoid ξ).part_mem.mpr (mem_univ y)) hx

/-- The kernel of the part map of a state's partition is the state. -/
theorem ker_part_ofSetoid (ξ : Coalescent.ER n) :
    Setoid.ker (fun x ↦ (Finpartition.ofSetoid ξ).part x) = ξ := by
  ext x y
  exact Setoid.ker_def.trans (part_ofSetoid_eq_iff ξ x y)

/-- The partition into classes of the kernel of a part map is the partition. -/
theorem ofSetoid_ker_part (P : Finpartition (univ : Finset (Fin n))) :
    Finpartition.ofSetoid (Setoid.ker fun x ↦ P.part x) = P := by
  have hparts : (Finpartition.ofSetoid (Setoid.ker fun x ↦ P.part x)).parts
      = univ.image (fun a ↦ ({b ∈ (univ : Finset (Fin n)) |
          (Setoid.ker fun x ↦ P.part x).r a b} : Finset (Fin n))) := rfl
  have hclass : ∀ a : Fin n, ({b ∈ (univ : Finset (Fin n)) |
      (Setoid.ker fun x ↦ P.part x).r a b} : Finset (Fin n)) = P.part a := by
    intro a
    ext b
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hab
      have hab' : P.part a = P.part b := Setoid.ker_def.mp hab
      exact (P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).mpr hab'.symm
    · intro hb
      exact Setoid.ker_def.mpr ((P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).mp hb).symm
  ext t
  rw [hparts]
  constructor
  · intro ht
    obtain ⟨a, -, rfl⟩ := mem_image.mp ht
    rw [hclass a]
    exact P.part_mem.mpr (mem_univ a)
  · intro ht
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
    exact mem_image.mpr ⟨x, mem_univ x, by rw [hclass x, P.part_eq_of_mem ht hx]⟩

/-- **Coalescent states are finite partitions of the sample.** -/
def statePartitionEquiv : Coalescent.ER n ≃ Finpartition (univ : Finset (Fin n)) where
  toFun ξ := Finpartition.ofSetoid ξ
  invFun P := Setoid.ker fun x ↦ P.part x
  left_inv ξ := ker_part_ofSetoid ξ
  right_inv P := ofSetoid_ker_part P

/-- The coalescent states on `n` individuals form a finite type. -/
instance instFintypeER : Fintype (Coalescent.ER n) :=
  Fintype.ofEquiv _ statePartitionEquiv.symm

/-- The bijection preserves the refinement order in both directions. -/
theorem ofSetoid_le_ofSetoid_iff (ξ η : Coalescent.ER n) :
    Finpartition.ofSetoid ξ ≤ Finpartition.ofSetoid η ↔ ξ ≤ η := by
  constructor
  · intro h x y hxy
    obtain ⟨c, hc, hsub⟩ := h ((Finpartition.ofSetoid ξ).part_mem.mpr (mem_univ x))
    have hsub' : (Finpartition.ofSetoid ξ).part x ⊆ c := hsub
    have hxc : x ∈ c := hsub' ((Finpartition.ofSetoid ξ).mem_part_self.mpr (mem_univ x))
    have hyc : y ∈ c := hsub' (Finpartition.mem_part_ofSetoid_iff_rel.mpr hxy)
    have hcx : (Finpartition.ofSetoid η).part x = c := Finpartition.part_eq_of_mem _ hc hxc
    exact Finpartition.mem_part_ofSetoid_iff_rel.mp (hcx ▸ hyc)
  · intro h t ht
    obtain ⟨x, hx⟩ := (Finpartition.ofSetoid ξ).nonempty_of_mem_parts ht
    have htx : (Finpartition.ofSetoid ξ).part x = t := Finpartition.part_eq_of_mem _ ht hx
    refine ⟨(Finpartition.ofSetoid η).part x, (Finpartition.ofSetoid η).part_mem.mpr (mem_univ x),
      ?_⟩
    intro y hy
    rw [← htx] at hy
    exact Finpartition.mem_part_ofSetoid_iff_rel.mpr
      (h (Finpartition.mem_part_ofSetoid_iff_rel.mp hy))

/-- The top coalescent state is the one-part partition. -/
theorem ofSetoid_top : Finpartition.ofSetoid (⊤ : Coalescent.ER n) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← ofSetoid_ker_part (⊤ : Finpartition (univ : Finset (Fin n))), ofSetoid_le_ofSetoid_iff]
  exact le_top

/-- **The report is connected exactly when `q ⊔ π = ⊤` on partitions.** -/
theorem observed_eq_top_iff_reportConnected (s : Fin n → Fin n) (π : Coalescent.ER n) :
    observed s π = ⊤ ↔
      ReportConnected (Finpartition.ofSetoid (graphKer s)) (Finpartition.ofSetoid π) := by
  constructor
  · intro h σ hq hπ
    have hqτ : graphKer s ≤ Setoid.ker fun x ↦ σ.part x := by
      rw [← ofSetoid_le_ofSetoid_iff, ofSetoid_ker_part]
      exact hq
    have hπτ : π ≤ Setoid.ker fun x ↦ σ.part x := by
      rw [← ofSetoid_le_ofSetoid_iff, ofSetoid_ker_part]
      exact hπ
    have htop : Setoid.ker (fun x ↦ σ.part x) = ⊤ := top_le_iff.mp (h ▸ observed_le hπτ hqτ)
    rw [← ofSetoid_ker_part σ, htop, ofSetoid_top]
  · intro h
    have h1 := h (Finpartition.ofSetoid (observed s π))
      ((ofSetoid_le_ofSetoid_iff _ _).mpr (graphKer_le_observed s π))
      ((ofSetoid_le_ofSetoid_iff _ _).mpr (le_observed s π))
    rw [← ofSetoid_top] at h1
    exact statePartitionEquiv.injective h1

/-- **NOTE Theorem D, (D3), in the corpus vocabulary.** For an interface `s` on `n ≥ 1`
individuals, the connectivity cumulant of `q = graphKer s` is the sum, over the coalescent
states `π` whose report `observed s π = q ⊔ π` is `⊤`, of `∏_{B ∈ π} |B|! z^{blocks π}`. -/
theorem connectivityCumulant_graphKer_eq_sum_observed (s : Fin n → Fin n) (hn : 0 < n) :
    connectivityCumulant (Finpartition.ofSetoid (graphKer s))
      = ∑ π ∈ univ.filter (fun π : Coalescent.ER n ↦ observed s π = ⊤),
          C (blockWeight (Finpartition.ofSetoid π) : ℤ) * X ^ Coalescent.blocks π := by
  rw [connectivityCumulant_eq_sum_connected _ (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩), sum_filter,
    sum_filter]
  refine (Fintype.sum_equiv statePartitionEquiv _ _ fun π ↦ ?_).symm
  simp only [statePartitionEquiv, Equiv.coe_fn_mk, observed_eq_top_iff_reportConnected,
    card_parts_ofSetoid]

/-- **NOTE Theorem D: the degree, in the corpus vocabulary.** The cumulant of `graphKer s` has
degree at most `n + 1 - w`, where `w = Linkage.width s` is the interface width. -/
theorem natDegree_connectivityCumulant_graphKer_le (s : Fin n → Fin n) (hn : 0 < n) :
    (connectivityCumulant (Finpartition.ofSetoid (graphKer s))).natDegree
      ≤ n + 1 - Linkage.width s := by
  have h := natDegree_connectivityCumulant_le (Finpartition.ofSetoid (graphKer s))
    (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  rwa [card_parts_ofSetoid, blocks_graphKer, card_univ, Fintype.card_fin] at h

end

end Descent.Pangenome.GraphCoalescent
