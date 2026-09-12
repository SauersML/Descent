/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LightConeApproximationBound
import Descent.Pangenome.AncestralLocality.SupportChainDynkin

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The truncated support chain read as the circuit of supports

`Descent.Pangenome.AncestralLocality.SupportChainDynkin` builds the support circuit truncated after
`M` decisions as a finite jump chain on slot states. This file relates it to the circuit of
`Descent.Pangenome.AncestralLocality.LocalityBounds`, whose states are multisets of supports and
whose generator is `supportGenerator`, and restates Theorem 9's approximation bound with the laws
of the chain.

## The generators intertwine before the truncation

`supportsOf x` is the multiset of occupied supports of a slot state. The chain started from
`supportChainStart` keeps every slot from `n + k` on empty after `k` decisions (`SlotsVacant`,
`slotsVacant_supportChainStart`, `slotsVacant_supportChainBranch`, `slotsVacant_coalesceTags`),
and its law vanishes off these states (`supportChainLaw_eq_zero_of_not_slotsVacant`). On such a
state a decision reads as `branchSupports` (`supportsOf_supportChainBranch`) and a coalescence as
`coalesceSupports` (`supportsOf_coalesceTags`). The ordered pairs of occupied slots are the
unordered pairs of the occupied supports (`sum_slot_pairs_eq_sum_powersetCard`, through
`sum_powersetCard_two_eq_sum_lt`). Hence, while fewer than `M` decisions have been taken, the
generator of the chain read through `supportsOf` is `supportGenerator`
(`supportChainGenerator_mulVec_comp_supportsOf`).

For the laws, Dynkin's formula for a function of the supports has the derivative
`∫ supportGenerator F` on the states with fewer than `M` decisions
(`hasDerivAt_sum_supportChainLaw_mul_supportsOf`). The frozen mass, the probability that `M`
decisions have been taken by time `T`, is at most `(n |A| / 3)(e^{3 D T} - 1) / M` by (8.3)
(`sum_supportChainLaw_frozen_le`), and it tends to zero as `M → ∞`
(`tendsto_sum_supportChainLaw_frozen`).

## Theorem 9's approximation bound with the chain's laws

`supportChainMeasure` is the law of `supportsOf` under the chain. It is a probability law
(`isProbabilityMeasure_supportChainMeasure`) whose escape probability is the escape sum of the
chain (`measureReal_supportChainMeasure_escapeSet`). With these laws in place of the marginal laws
of `norm_operator_sub_le_lightConeEscape`, the escape bound comes from
`sum_supportChainLaw_escape_le`, and the hypotheses on the start, integrability, continuity and
Dynkin's formula are gone (`norm_operator_sub_le_lightConeEscape_of_supportChain`,
`InfiniteGenomeLimit.LightConeApproximation.ofSupportChain`).

Scope. The hypothesis `hdynkin` of `norm_operator_sub_le_lightConeEscape` is not discharged
literally: on a frozen state the chain takes no decision while `supportGenerator` does, so the
chain's laws obey Dynkin's formula for `supportGenerator` only off the frozen states. The
approximation bound is restated with the chain's laws instead. The untruncated circuit and its path
law are not constructed: the frozen mass tends to zero, but no limit law as `M → ∞` is built. The
sampling duality `hduality` and the agreement until escape `hagree` remain hypotheses, as in
`norm_operator_sub_le_lightConeEscape`.

## Empirical status

None. The bodies here are finite sums, multiset identities and measure inequalities on supplied
rates and evaluations, and no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset MeasureTheory Filter Topology InfiniteGenomeLimit
open scoped NNReal Matrix

noncomputable section

/-! ### Multisets read off slot arrays -/

section Slots

variable {α : Type*}

/-- An unordered pair of distinct slots reads off as the pair of their entries. -/
theorem map_val_pair {ι : Type*} [DecidableEq ι] {a b : ι} (hab : a ≠ b) (f : ι → α) :
    ({a, b} : Finset ι).val.map f = ({f a, f b} : Multiset α) := by
  rw [Finset.insert_val_of_notMem (a := a) (s := {b}) (by simpa using hab), Finset.singleton_val,
    Multiset.map_cons, Multiset.map_singleton, Multiset.insert_eq_cons]

variable [DecidableEq α]

/-- Reading a slot array after one update replaces one copy of the old entry. -/
theorem map_univ_update {N : ℕ} (A : Fin N → α) (a : Fin N) (v : α) :
    univ.val.map (Function.update A a v) = v ::ₘ (univ.val.map A).erase (A a) := by
  have huniv : (univ : Finset (Fin N)).val = a ::ₘ (univ.erase a).val := by
    rw [← Finset.insert_val_of_notMem (Finset.notMem_erase a univ),
      Finset.insert_erase (Finset.mem_univ a)]
  rw [huniv, Multiset.map_cons, Multiset.map_cons, Multiset.erase_cons_head,
    Function.update_self]
  congr 1
  exact Multiset.map_congr rfl fun c hc ↦ Function.update_of_ne (Finset.ne_of_mem_erase hc) _ _

/-- Erasing an entry that fails the predicate does not change the filter. -/
theorem filter_erase_of_not {p : α → Prop} [DecidablePred p] (s : Multiset α) {x : α}
    (hx : ¬p x) : (s.erase x).filter p = s.filter p := by
  by_cases hmem : x ∈ s
  · conv_rhs => rw [← Multiset.cons_erase hmem]
    rw [Multiset.filter_cons_of_neg _ hx]
  · rw [Multiset.erase_of_notMem hmem]

/-- Erasing an entry that satisfies the predicate commutes with the filter. -/
theorem filter_erase_of_pos {p : α → Prop} [DecidablePred p] (s : Multiset α) {x : α}
    (hx : p x) : (s.erase x).filter p = (s.filter p).erase x := by
  by_cases hmem : x ∈ s
  · conv_rhs => rw [← Multiset.cons_erase hmem]
    rw [Multiset.filter_cons_of_pos _ hx, Multiset.erase_cons_head]
  · rw [Multiset.erase_of_notMem hmem,
      Multiset.erase_of_notMem fun h ↦ hmem (Multiset.mem_of_mem_filter h)]

end Slots

/-- **The unordered pairs of a finite set are its ordered pairs `a < b`.** -/
theorem sum_powersetCard_two_eq_sum_lt {ι β : Type*} [LinearOrder ι] [AddCommMonoid β]
    (O : Finset ι) (G : Finset ι → β) :
    ∑ T ∈ O.powersetCard 2, G T = ∑ a ∈ O, ∑ b ∈ O, if a < b then G {a, b} else 0 := by
  induction O using Finset.induction_on_max with
  | h0 =>
    rw [Finset.sum_empty]
    refine Finset.sum_eq_zero fun T hT ↦ ?_
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
    rw [Finset.subset_empty.mp hsub, Finset.card_empty] at hcard
    exact absurd hcard (by norm_num)
  | step a₀ O hmax ih =>
    have hnot : a₀ ∉ O := fun h ↦ lt_irrefl a₀ (hmax a₀ h)
    have hdisj : Disjoint (O.powersetCard 2) ((O.powersetCard 1).image (insert a₀)) := by
      rw [Finset.disjoint_left]
      intro T hT hT'
      obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hT'
      exact hnot ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self a₀ U))
    have hinj : ∀ U ∈ O.powersetCard 1, ∀ U' ∈ O.powersetCard 1,
        insert a₀ U = insert a₀ U' → U = U' := by
      intro U hU U' hU' heq
      have hU0 : a₀ ∉ U := fun h ↦ hnot ((Finset.mem_powersetCard.mp hU).1 h)
      have hU0' : a₀ ∉ U' := fun h ↦ hnot ((Finset.mem_powersetCard.mp hU').1 h)
      rw [← Finset.erase_insert hU0, heq, Finset.erase_insert hU0']
    have hleft : ∑ T ∈ (insert a₀ O).powersetCard 2, G T =
        ∑ T ∈ O.powersetCard 2, G T + ∑ y ∈ O, G {a₀, y} := by
      rw [Finset.powersetCard_succ_insert hnot 1, Finset.sum_union hdisj, Finset.sum_image hinj,
        Finset.powersetCard_one, Finset.sum_map]
      rfl
    have hrow : ∑ b ∈ insert a₀ O, (if a₀ < b then G {a₀, b} else 0) = 0 := by
      refine Finset.sum_eq_zero fun b hb ↦ if_neg fun hlt ↦ ?_
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact lt_irrefl _ hlt
      · exact lt_asymm hlt (hmax b hb)
    have hcol : ∀ a ∈ O, ∑ b ∈ insert a₀ O, (if a < b then G {a, b} else 0) =
        G {a₀, a} + ∑ b ∈ O, if a < b then G {a, b} else 0 := by
      intro a ha
      rw [Finset.sum_insert hnot, if_pos (hmax a ha), Finset.pair_comm]
    rw [hleft, ih, Finset.sum_insert hnot, hrow, zero_add, Finset.sum_congr rfl hcol,
      Finset.sum_add_distrib, add_comm]

/-! ### The occupied supports -/

section Supports

variable {V : Type*} {n M : ℕ}

/-- **The occupied supports of a slot state**: the state of the circuit of `LocalityBounds` that
the slots represent. -/
def supportsOf (x : SupportChainState V n M) : Multiset (Finset V) :=
  (univ.val.map x.1).filter Finset.Nonempty

/-- Summing a function that vanishes at `∅` over the occupied entries sums it over all entries. -/
theorem sum_map_filter_nonempty {β : Type*} [AddCommMonoid β] (g : Finset V → β) (hg : g ∅ = 0)
    (s : Multiset (Finset V)) : ((s.filter Finset.Nonempty).map g).sum = (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons S s ih =>
    by_cases hS : S.Nonempty
    · rw [Multiset.filter_cons_of_pos _ hS, Multiset.map_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.sum_cons, ih]
    · rw [Multiset.filter_cons_of_neg _ hS, Multiset.map_cons, Multiset.sum_cons, ih,
        Finset.not_nonempty_iff_eq_empty.mp hS, hg, zero_add]

/-- A function of the supports that vanishes at `∅`, summed over the slots, is its sum over the
occupied supports. -/
theorem sum_slots_eq_sum_supportsOf {β : Type*} [AddCommMonoid β] (g : Finset V → β)
    (hg : g ∅ = 0) (x : SupportChainState V n M) :
    ∑ a, g (x.1 a) = ((supportsOf x).map g).sum := by
  rw [supportsOf, sum_map_filter_nonempty g hg, Multiset.map_map]
  rfl

/-- The occupied supports carry the tag weight. -/
theorem weightedCount_supportsOf (w : V → ℝ) (x : SupportChainState V n M) :
    weightedCount w (supportsOf x) = tagWeight w x.1 := by
  show ((supportsOf x).map fun S ↦ ∑ v ∈ S, w v).sum = tagWeight w x.1
  rw [← sum_slots_eq_sum_supportsOf (fun S ↦ ∑ v ∈ S, w v) (by simp) x]
  rfl

/-- **The unused slots are empty**: after `k` decisions every slot from `n + k` on is empty. -/
def SlotsVacant (x : SupportChainState V n M) : Prop :=
  ∀ c : Fin (n + M), n + (x.2 : ℕ) ≤ c → x.1 c = ∅

/-- The initial state has its unused slots empty. -/
theorem slotsVacant_supportChainStart (A : Finset V) (n M : ℕ) :
    SlotsVacant (supportChainStart A n M) := by
  intro c hc
  have hle : n ≤ (c : ℕ) := by simpa [supportChainStart] using hc
  obtain ⟨d, rfl⟩ : ∃ d : Fin M, c = Fin.natAdd n d :=
    ⟨⟨(c : ℕ) - n, by have := c.isLt; omega⟩,
      Fin.ext (by simp only [Fin.coe_natAdd]; omega)⟩
  simp [supportChainStart]

/-- An occupied slot of a state with empty unused slots lies before `n + k`. -/
theorem val_lt_of_slotsVacant {x : SupportChainState V n M} (hx : SlotsVacant x)
    {a : Fin (n + M)} (ha : (x.1 a).Nonempty) : (a : ℕ) < n + (x.2 : ℕ) := by
  by_contra hlt
  rw [hx a (not_lt.mp hlt)] at ha
  exact Finset.not_nonempty_empty ha

/-- Ordered pairs of occupied slots, read through their supports. -/
theorem sum_slot_pairs_eq {β : Type*} [AddCommMonoid β] (h : Multiset (Finset V) → β)
    (x : SupportChainState V n M) :
    ∑ a, ∑ b, (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then h {x.1 a, x.1 b} else 0) =
      ∑ a ∈ univ.filter fun a ↦ (x.1 a).Nonempty, ∑ b ∈ univ.filter fun a ↦ (x.1 a).Nonempty,
        if a < b then h (({a, b} : Finset (Fin (n + M))).val.map x.1) else 0 := by
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : (x.1 a).Nonempty
  · simp only [ha, true_and, ↓reduceIte]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    by_cases hb : (x.1 b).Nonempty
    · by_cases hab : a < b
      · simp only [hb, hab, and_self, ↓reduceIte, map_val_pair (ne_of_lt hab)]
      · simp only [hb, hab, false_and, ↓reduceIte]
    · simp only [hb, and_false, ↓reduceIte]
  · simp only [ha, false_and, and_false, ↓reduceIte, Finset.sum_const_zero]

/-- **The ordered pairs of occupied slots are the unordered pairs of the occupied supports.** -/
theorem sum_slot_pairs_eq_sum_powersetCard {β : Type*} [AddCommMonoid β]
    (h : Multiset (Finset V) → β) (x : SupportChainState V n M) :
    ∑ a, ∑ b, (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then h {x.1 a, x.1 b} else 0) =
      (((supportsOf x).powersetCard 2).map h).sum := by
  have hsupports : supportsOf x = (univ.filter fun a ↦ (x.1 a).Nonempty).val.map x.1 := by
    rw [supportsOf, Multiset.filter_map, Finset.filter_val]
    rfl
  rw [hsupports, Multiset.powersetCard_map, Multiset.map_map, ← Finset.map_val_val_powersetCard,
    Multiset.map_map, sum_slot_pairs_eq h x]
  exact (sum_powersetCard_two_eq_sum_lt _ fun T ↦ h (T.val.map x.1)).symm

end Supports

/-! ### The generators intertwine -/

section Intertwining

variable {V : Type*} [DecidableEq V] {n M : ℕ}

/-- Whether the unused slots are empty is decidable. -/
instance decidableSlotsVacant (x : SupportChainState V n M) : Decidable (SlotsVacant x) := by
  unfold SlotsVacant
  infer_instance

/-- **A decision keeps the unused slots empty**, for an argument that holds the target `i`. -/
theorem slotsVacant_supportChainBranch {x : SupportChainState V n M} (hx : SlotsVacant x)
    {a : Fin (n + M)} {i : V} (hi : i ∈ x.1 a) (j : V) :
    SlotsVacant (supportChainBranch x a i j) := by
  have ha := val_lt_of_slotsVacant hx ⟨i, hi⟩
  unfold supportChainBranch
  split_ifs with h
  · intro c hc
    dsimp only at hc ⊢
    have hcp : c ≠ ⟨n + (x.2 : ℕ), by omega⟩ := fun heq ↦ by
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
    have hca : c ≠ a := fun heq ↦ by
      rw [heq] at hc
      omega
    rw [Function.update_of_ne hcp, Function.update_of_ne hca]
    exact hx c (by omega)
  · exact hx

/-- **A coalescence keeps the unused slots empty**, for an occupied second slot. -/
theorem slotsVacant_coalesceTags {x : SupportChainState V n M} (hx : SlotsVacant x)
    {a b : Fin (n + M)} (hb : (x.1 b).Nonempty) :
    SlotsVacant ((coalesceTags a b x.1, x.2) : SupportChainState V n M) := by
  have hb' := val_lt_of_slotsVacant hx hb
  intro c hc
  dsimp only at hc ⊢
  rw [coalesceTags_apply]
  split_ifs with hca hcb
  · rfl
  · exfalso
    rw [hcb] at hc
    omega
  · exact hx c hc

/-- A coalescence of two distinct slots is two slot updates. -/
theorem coalesceTags_eq_update {N : ℕ} {a b : Fin N} (hab : a ≠ b) (A : Fin N → Finset V) :
    coalesceTags a b A = Function.update (Function.update A a ∅) b (A a ∪ A b) := by
  funext c
  simp only [coalesceTags, Function.update_apply]
  by_cases hca : c = a
  · rw [if_pos hca, if_neg fun hcb ↦ hab (hca.symm.trans hcb), if_pos hca]
  · rw [if_neg hca, if_neg hca]

/-- **A decision reads as `branchSupports`** on a state with empty unused slots, before the
truncation. -/
theorem supportsOf_supportChainBranch {x : SupportChainState V n M} (hx : SlotsVacant x)
    (hk : (x.2 : ℕ) < M) {a : Fin (n + M)} {i : V} (hi : i ∈ x.1 a) (j : V) :
    supportsOf (supportChainBranch x a i j) = branchSupports (supportsOf x) (x.1 a) i j := by
  have hne : (x.1 a).Nonempty := ⟨i, hi⟩
  have ha := val_lt_of_slotsVacant hx hne
  have hslot : n + (x.2 : ℕ) < n + M := by omega
  have hpa : (⟨n + (x.2 : ℕ), hslot⟩ : Fin (n + M)) ≠ a := fun heq ↦ by
    have hv := congrArg Fin.val heq
    simp only [Fin.val_mk] at hv
    omega
  have hvacant : x.1 ⟨n + (x.2 : ℕ), hslot⟩ = ∅ := hx _ le_rfl
  have hbranch : (supportChainBranch x a i j).1 =
      Function.update (Function.update x.1 a (insert j (x.1 a))) ⟨n + (x.2 : ℕ), hslot⟩
        {i, j} := by
    simp only [supportChainBranch, dif_pos hk]
  simp only [supportsOf, branchSupports]
  rw [hbranch, map_univ_update, map_univ_update, Function.update_of_ne hpa, hvacant,
    Multiset.erase_cons_tail _ (Finset.insert_nonempty j (x.1 a)).ne_empty,
    Multiset.filter_cons_of_pos _ (Finset.insert_nonempty i {j}),
    Multiset.filter_cons_of_pos _ (Finset.insert_nonempty j (x.1 a)),
    filter_erase_of_not _ Finset.not_nonempty_empty, filter_erase_of_pos _ hne,
    Multiset.cons_swap]

/-- **A coalescence reads as `coalesceSupports`** of the pair of supports. -/
theorem supportsOf_coalesceTags {x : SupportChainState V n M} {a b : Fin (n + M)} (hab : a ≠ b)
    (ha : (x.1 a).Nonempty) (hb : (x.1 b).Nonempty) :
    supportsOf ((coalesceTags a b x.1, x.2) : SupportChainState V n M) =
      coalesceSupports (supportsOf x) {x.1 a, x.1 b} := by
  simp only [supportsOf, coalesceSupports]
  rw [coalesceTags_eq_update hab, map_univ_update, map_univ_update,
    Function.update_of_ne (Ne.symm hab), Multiset.erase_cons_tail _ (Ne.symm hb.ne_empty),
    Multiset.filter_cons_of_pos _ (ha.mono Finset.subset_union_left),
    Multiset.filter_cons_of_neg _ Finset.not_nonempty_empty, filter_erase_of_pos _ hb,
    filter_erase_of_pos _ ha, Multiset.insert_eq_cons, Multiset.sup_cons, Multiset.sup_singleton,
    Finset.sup_eq_union, Multiset.sub_cons, Multiset.sub_singleton]

variable [Fintype V]

/-- Empty slots carry no coordinate, so the occupied supports escape exactly when the slots do. -/
theorem supportsOf_mem_escapeSet_iff {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    (x : SupportChainState V n M) :
    supportsOf x ∈ escapeSet r A ℓ ↔ univ.val.map x.1 ∈ escapeSet r A ℓ := by
  constructor
  · rintro ⟨S, hS, v, hv, hfar⟩
    exact ⟨S, Multiset.mem_of_mem_filter hS, v, hv, hfar⟩
  · rintro ⟨S, hS, v, hv, hfar⟩
    exact ⟨S, Multiset.mem_filter.mpr ⟨hS, v, hv⟩, v, hv, hfar⟩

/-- **The generators intertwine before the truncation.** On a state with empty unused slots and
fewer than `M` decisions, the generator of the truncated chain applied to `F ∘ supportsOf` is
`supportGenerator F` at the occupied supports. -/
theorem supportChainGenerator_mulVec_comp_supportsOf {r : V → V → ℝ} {c : ℝ}
    (F : Multiset (Finset V) → ℝ) {x : SupportChainState V n M} (hx : SlotsVacant x)
    (hk : (x.2 : ℕ) < M) :
    (supportChainGenerator r c *ᵥ fun y ↦ F (supportsOf y)) x =
      supportGenerator r c F (supportsOf x) := by
  rw [supportChainGenerator_mulVec, supportGenerator]
  congr 1
  · have hterm : ∀ a, ∑ i ∈ x.1 a, ∑ j, r i j *
        (F (supportsOf (supportChainBranch x a i j)) - F (supportsOf x)) =
          ∑ i ∈ x.1 a, ∑ j, r i j *
            (F (branchSupports (supportsOf x) (x.1 a) i j) - F (supportsOf x)) := fun a ↦
      Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j _ ↦ by
        rw [supportsOf_supportChainBranch hx hk hi j]
    rw [Finset.sum_congr rfl fun a _ ↦ hterm a]
    exact sum_slots_eq_sum_supportsOf
      (fun S ↦ ∑ i ∈ S, ∑ j, r i j * (F (branchSupports (supportsOf x) S i j) - F (supportsOf x)))
      (by simp) x
  · have hterm : ∀ a b, (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then c else 0) *
        (F (supportsOf (coalesceTags a b x.1, x.2)) - F (supportsOf x)) =
          c * (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then
            F (coalesceSupports (supportsOf x) {x.1 a, x.1 b}) - F (supportsOf x) else 0) := by
      intro a b
      split_ifs with hab
      · rw [supportsOf_coalesceTags (ne_of_lt hab.1) hab.2.1 hab.2.2]
      · rw [zero_mul, mul_zero]
    rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hterm a b]
    simp only [← Finset.mul_sum]
    exact congrArg (c * ·) (sum_slot_pairs_eq_sum_powersetCard
      (fun t ↦ F (coalesceSupports (supportsOf x) t) - F (supportsOf x)) x)

/-- From a state with empty unused slots, the chain jumps only to such states. -/
theorem supportChainRate_eq_zero_of_not_slotsVacant {r : V → V → ℝ} {c : ℝ}
    {x y : SupportChainState V n M} (hx : SlotsVacant x) (hy : ¬SlotsVacant y) :
    supportChainRate r c x y = 0 := by
  have hbranch : ∑ a, ∑ i ∈ x.1 a, ∑ j, (if supportChainBranch x a i j = y then r i j else 0) =
      0 :=
    Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j _ ↦
      if_neg fun (heq : supportChainBranch x a i j = y) ↦
        hy (heq ▸ slotsVacant_supportChainBranch hx hi j)
  have hcoal : ∑ a, ∑ b, (if (coalesceTags a b x.1, x.2) = y then
      (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then c else 0) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    split_ifs with heq hcond
    · exact absurd (heq ▸ slotsVacant_coalesceTags hx hcond.2.2) hy
    · rfl
    · rfl
  rw [supportChainRate, hbranch, hcoal, add_zero]

/-- The generator does not raise the indicator of the states with an occupied unused slot. -/
theorem supportChainGenerator_mulVec_vacancy_le {r : V → V → ℝ} {c : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hc : 0 ≤ c) (x : SupportChainState V n M) :
    (supportChainGenerator r c *ᵥ fun y ↦ if SlotsVacant y then (0 : ℝ) else 1) x ≤
      0 * (if SlotsVacant x then (0 : ℝ) else 1) := by
  rw [zero_mul, supportChainGenerator, jumpRateGenerator_mulVec]
  refine Finset.sum_nonpos fun y _ ↦ ?_
  by_cases hx : SlotsVacant x
  · by_cases hy : SlotsVacant y
    · simp only [hx, hy, ↓reduceIte, sub_self, mul_zero, le_refl]
    · rw [supportChainRate_eq_zero_of_not_slotsVacant hx hy, zero_mul]
  · refine mul_nonpos_of_nonneg_of_nonpos (supportChainRate_nonneg hr hc x y) ?_
    rw [if_neg hx]
    split_ifs <;> norm_num

/-- **The law of the chain vanishes off the states with empty unused slots.** -/
theorem supportChainLaw_eq_zero_of_not_slotsVacant {r : V → V → ℝ} {c : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c) (A : Finset V) (n M : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {y : SupportChainState V n M} (hy : ¬SlotsVacant y) : supportChainLaw r c A n M t y = 0 := by
  have h := sum_jumpChainLaw_mul_le_exp (Q := supportChainGenerator r c)
    (fun _ _ hxy ↦ supportChainGenerator_apply_nonneg hr hc hxy)
    (F := fun y ↦ if SlotsVacant y then (0 : ℝ) else 1) (K := 0)
    (fun x ↦ supportChainGenerator_mulVec_vacancy_le hr hc x) (supportChainStart A n M) ht
  beta_reduce at h
  rw [if_pos (slotsVacant_supportChainStart A n M), zero_mul] at h
  have hnonneg : ∀ z ∈ univ, 0 ≤ supportChainLaw r c A n M t z *
      (if SlotsVacant z then (0 : ℝ) else 1) := fun z _ ↦
    mul_nonneg (supportChainLaw_nonneg hr hc A n M ht z) (by split_ifs <;> norm_num)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
    (le_antisymm h (Finset.sum_nonneg hnonneg)) y (Finset.mem_univ y)
  rwa [if_neg hy, mul_one] at hzero

/-- **Dynkin's formula read through the supports.** For a function `F` of the occupied supports,
the derivative of `∫ F ∘ supportsOf dμ_t` is `∫ supportGenerator F` over the states with fewer
than `M` decisions, plus the chain's own generator on the frozen states. -/
theorem hasDerivAt_sum_supportChainLaw_mul_supportsOf {r : V → V → ℝ} {c : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c) (A : Finset V) (n M : ℕ) (F : Multiset (Finset V) → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u ↦ ∑ y, supportChainLaw r c A n M u y * F (supportsOf y))
      (∑ y, supportChainLaw r c A n M t y *
        (if (y.2 : ℕ) < M then supportGenerator r c F (supportsOf y)
          else (supportChainGenerator r c *ᵥ fun z ↦ F (supportsOf z)) y)) t := by
  refine (hasDerivAt_sum_supportChainLaw_mul r c A n M (fun y ↦ F (supportsOf y)) t).congr_deriv
    (Finset.sum_congr rfl fun y _ ↦ ?_)
  by_cases hk : (y.2 : ℕ) < M
  · rw [if_pos hk]
    by_cases hy : SlotsVacant y
    · rw [supportChainGenerator_mulVec_comp_supportsOf F hy hk]
    · rw [supportChainLaw_eq_zero_of_not_slotsVacant hr hc A n M ht hy, zero_mul, zero_mul]
  · rw [if_neg hk]

/-- **The frozen mass is small**: the probability that `M` decisions have been taken by time `T`
is at most `(n |A| / 3)(e^{3 D T} - 1) / M`. -/
theorem sum_supportChainLaw_frozen_le {r : V → V → ℝ} {c D T : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hD0 : 0 ≤ D) (hc : 0 ≤ c) (A : Finset V) (n M : ℕ) (hM : 0 < M)
    (hT : 0 ≤ T) :
    ∑ y : SupportChainState V n M, (if (y.2 : ℕ) = M then supportChainLaw r c A n M T y else 0) ≤
      n * A.card / 3 * (Real.exp (3 * D * T) - 1) / M := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  rw [le_div_iff₀ hMpos, Finset.sum_mul]
  refine (Finset.sum_le_sum fun y _ ↦ ?_).trans
    (sum_supportChainLaw_mul_count_le hr hD hD0 hc A n M hT)
  split_ifs with hy
  · rw [hy]
  · rw [zero_mul]
    exact mul_nonneg (supportChainLaw_nonneg hr hc A n M hT y) (Nat.cast_nonneg _)

/-- **The frozen mass vanishes as the truncation grows.** -/
theorem tendsto_sum_supportChainLaw_frozen {r : V → V → ℝ} {c D T : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hD0 : 0 ≤ D) (hc : 0 ≤ c) (A : Finset V) (n : ℕ) (hT : 0 ≤ T) :
    Tendsto (fun M : ℕ ↦ ∑ y : SupportChainState V n M,
      (if (y.2 : ℕ) = M then supportChainLaw r c A n M T y else 0)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun M ↦ Finset.sum_nonneg fun y _ ↦ ?_)
    ((eventually_gt_atTop 0).mono fun M hM ↦
      sum_supportChainLaw_frozen_le hr hD hD0 hc A n M hM hT)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  split_ifs
  · exact supportChainLaw_nonneg hr hc A n M hT y
  · exact le_rfl

end Intertwining

/-! ### Theorem 9's approximation bound with the chain's laws -/

section LightCone

variable {V : Type*} [DecidableEq V] [Fintype V] [MeasurableSpace (Multiset (Finset V))]

/-- **The law of the occupied supports** of the truncated chain at time `t`, the image of
`supportChainLaw` under `supportsOf`. -/
def supportChainMeasure (r : V → V → ℝ) (c : ℝ) (A : Finset V) (n M : ℕ) (t : ℝ) :
    Measure (Multiset (Finset V)) :=
  ∑ y : SupportChainState V n M,
    ENNReal.ofReal (supportChainLaw r c A n M t y) • Measure.dirac (supportsOf y)

/-- The measure of a set is the chain's mass on the states whose supports lie in it. -/
theorem supportChainMeasure_apply [MeasurableSingletonClass (Multiset (Finset V))]
    (r : V → V → ℝ) (c : ℝ) (A : Finset V) (n M : ℕ) (t : ℝ) (E : Set (Multiset (Finset V))) :
    supportChainMeasure r c A n M t E =
      ∑ y : SupportChainState V n M,
        ENNReal.ofReal (supportChainLaw r c A n M t y) * E.indicator 1 (supportsOf y) := by
  simp only [supportChainMeasure, Measure.finset_sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]

/-- The law of the occupied supports is a probability law at every time `t ≥ 0`. -/
theorem isProbabilityMeasure_supportChainMeasure [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c) (A : Finset V) (n M : ℕ)
    {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (supportChainMeasure r c A n M t) := by
  constructor
  rw [supportChainMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ supportChainLaw_nonneg hr hc A n M ht y,
    sum_supportChainLaw, ENNReal.ofReal_one]

open scoped Classical in
/-- **The escape probability of the law of the supports is the escape sum of the chain.** -/
theorem measureReal_supportChainMeasure_escapeSet
    [MeasurableSingletonClass (Multiset (Finset V))] {r : V → V → ℝ} {c : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c) (A : Finset V) (n M ℓ : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (supportChainMeasure r c A n M t).real (escapeSet r A ℓ) =
      ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M t y else 0) := by
  have hfinite : ∀ y ∈ (univ : Finset (SupportChainState V n M)),
      ENNReal.ofReal (supportChainLaw r c A n M t y) *
        (escapeSet r A ℓ).indicator 1 (supportsOf y) ≠ ⊤ := fun y _ ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      rw [Set.indicator_apply]
      split_ifs <;> simp)
  rw [measureReal_def, supportChainMeasure_apply, ENNReal.toReal_sum hfinite]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (supportChainLaw_nonneg hr hc A n M ht y),
    Set.indicator_apply]
  by_cases hy : univ.val.map y.1 ∈ escapeSet r A ℓ
  · rw [if_pos ((supportsOf_mem_escapeSet_iff y).mpr hy), if_pos hy, Pi.one_apply,
      ENNReal.toReal_one, mul_one]
  · rw [if_neg fun h ↦ hy ((supportsOf_mem_escapeSet_iff y).mp h), if_neg hy,
      ENNReal.toReal_zero, mul_zero]

/-- **Theorem 9's operator bound with the laws of the truncated chain.** As
`norm_operator_sub_le_lightConeEscape`, with the marginal laws the laws `supportChainMeasure` of
the support chain truncated after `truncation f` decisions: no hypothesis on the start,
integrability, continuity or Dynkin's formula remains.

Assumes: the sampling duality `hduality` of the operators `S m` through bounded integrable
evaluations against `supportChainMeasure`, and agreement `hagree` of the evaluations of `S m` and
every later `S m'` on every state that has not escaped the ball of radius `radius m`. -/
theorem norm_operator_sub_le_lightConeEscape_of_supportChain {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSingletonClass (Multiset (Finset V))] {S : ℕ → FellerSemigroup X}
    {A : Subalgebra ℝ C(X, ℝ)} {r : V → V → ℝ} {c D a : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a) (radius : ℕ → ℕ)
    (observationSet : C(X, ℝ) → Finset V) (sampleSize truncation : C(X, ℝ) → ℕ)
    (evaluation : ℕ → C(X, ℝ) → X → ℝ → Multiset (Finset V) → ℝ)
    (hintegrable : ∀ m f p (t : ℝ≥0), Integrable (evaluation m f p t)
      (supportChainMeasure r c (observationSet f) (sampleSize f) (truncation f) t))
    (hbounded : ∀ m f p t s, |evaluation m f p t s| ≤ ‖f‖)
    (hduality : ∀ f ∈ A, ∀ m p (t : ℝ≥0), (S m).operator t f p =
      ∫ s, evaluation m f p t s
        ∂supportChainMeasure r c (observationSet f) (sampleSize f) (truncation f) t)
    (hagree : ∀ f ∈ A, ∀ m m', m ≤ m' → ∀ p t s,
      s ∉ escapeSet r (observationSet f) (radius m) →
        evaluation m f p t s = evaluation m' f p t s) :
    ∀ f ∈ A, ∀ T t, t ≤ T → ∀ m m', m ≤ m' →
      ‖(S m).operator t f - (S m').operator t f‖ ≤
        2 * ‖f‖ *
          lightConeEscape ((sampleSize f : ℝ) * (observationSet f).card) D a radius T m := by
  intro f hf T t htT m m' hmm'
  have hnumber : (0 : ℝ) ≤ (sampleSize f : ℝ) * (observationSet f).card := by positivity
  have hescapeNonneg : 0 ≤ lightConeEscape ((sampleSize f : ℝ) * (observationSet f).card) D a
      radius T m :=
    le_min zero_le_one
      (div_nonneg (mul_nonneg hnumber (Real.exp_pos _).le) (pow_nonneg (by linarith) _))
  rw [ContinuousMap.norm_le (C0 := mul_nonneg (by positivity) hescapeNonneg)]
  intro p
  rw [ContinuousMap.sub_apply, hduality f hf m p t, hduality f hf m' p t, Real.norm_eq_abs]
  haveI := isProbabilityMeasure_supportChainMeasure hr hc (observationSet f) (sampleSize f)
    (truncation f) t.coe_nonneg
  have hcoupling := abs_integral_sub_le_of_eqOn_compl
    (supportChainMeasure r c (observationSet f) (sampleSize f) (truncation f) t) _ _
    (hintegrable m f p t) (hintegrable m' f p t) (hbounded m f p t) (hbounded m' f p t)
    (hagree f hf m m' hmm' p t)
  have hbound : (supportChainMeasure r c (observationSet f) (sampleSize f) (truncation f) t).real
      (escapeSet r (observationSet f) (radius m)) ≤
        min 1 ((sampleSize f : ℝ) * (observationSet f).card *
          Real.exp (D * (1 + 2 * a) * t) / a ^ radius m) := by
    rw [measureReal_supportChainMeasure_escapeSet hr hc _ _ _ _ t.coe_nonneg]
    exact sum_supportChainLaw_escape_le hr hD hc ha _ _ _ _ t.coe_nonneg
  exact hcoupling.trans ((mul_le_mul_of_nonneg_left hbound (by positivity)).trans
    (mul_le_mul_of_nonneg_left
      (escapeBound_mono_time hnumber hDnonneg ha (NNReal.coe_le_coe.mpr htT)) (by positivity)))

/-- **Theorem 9's approximation hypothesis from the truncated support chain.** Along an
exhaustion whose radius grows without bound, with base `a > 1`, the finite-genome semigroups that
are represented through the laws of the truncated chain form a `LightConeApproximation`.

Assumes: the hypotheses of `norm_operator_sub_le_lightConeEscape_of_supportChain`. -/
def InfiniteGenomeLimit.LightConeApproximation.ofSupportChain {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSingletonClass (Multiset (Finset V))] {S : ℕ → FellerSemigroup X}
    {A : Subalgebra ℝ C(X, ℝ)} {r : V → V → ℝ} {c D a : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c) (ha : 1 < a) (radius : ℕ → ℕ)
    (hradius : Tendsto radius atTop atTop)
    (observationSet : C(X, ℝ) → Finset V) (sampleSize truncation : C(X, ℝ) → ℕ)
    (evaluation : ℕ → C(X, ℝ) → X → ℝ → Multiset (Finset V) → ℝ)
    (hintegrable : ∀ m f p (t : ℝ≥0), Integrable (evaluation m f p t)
      (supportChainMeasure r c (observationSet f) (sampleSize f) (truncation f) t))
    (hbounded : ∀ m f p t s, |evaluation m f p t s| ≤ ‖f‖)
    (hduality : ∀ f ∈ A, ∀ m p (t : ℝ≥0), (S m).operator t f p =
      ∫ s, evaluation m f p t s
        ∂supportChainMeasure r c (observationSet f) (sampleSize f) (truncation f) t)
    (hagree : ∀ f ∈ A, ∀ m m', m ≤ m' → ∀ p t s,
      s ∉ escapeSet r (observationSet f) (radius m) →
        evaluation m f p t s = evaluation m' f p t s) :
    LightConeApproximation S A :=
  LightConeApproximation.ofEscapeBound (fun f ↦ (sampleSize f : ℝ) * (observationSet f).card) D ha
    radius hradius
    (norm_operator_sub_le_lightConeEscape_of_supportChain hr hD hDnonneg hc ha.le radius
      observationSet sampleSize truncation evaluation hintegrable hbounded hduality hagree)

end LightCone

end

end Descent.Pangenome.AncestralLocality
