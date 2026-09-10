/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw
import Mathlib.Algebra.BigOperators.Fin

assert_below Descent.Decision Descent.Program

/-!
Ordered Algorithm R reservoir slots, with the update law derived from its
uniform integer draw. Slot order is retained, rather than replaced by a
uniform permutation of the final unordered sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReservoirSamplingLaw

open FiniteReportLaw

abbrev Slots (capacity seen : ℕ) := Fin capacity ↪ Fin seen

noncomputable instance slotsFintype (capacity seen : ℕ) : Fintype (Slots capacity seen) :=
  Fintype.ofFinite _

noncomputable def uniformDraw (seen : ℕ) : FiniteReportLaw (Fin (seen + 1)) where
  mass := fun _ ↦ 1 / (seen + 1 : ℝ)
  mass_nonneg := fun _ ↦ by positivity
  mass_sum := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

noncomputable def choice (capacity seen : ℕ) (draw : Fin (seen + 1)) : Option (Fin capacity) :=
  if h : draw.val < capacity then some ⟨draw.val, h⟩ else none

noncomputable def choiceLaw (capacity seen : ℕ) : FiniteReportLaw (Option (Fin capacity)) :=
  (uniformDraw seen).pushforward (choice capacity seen)

theorem choice_eq_some_iff (capacity seen : ℕ) (draw : Fin (seen + 1)) (slot : Fin capacity) :
    choice capacity seen draw = some slot ↔ draw.val = slot.val := by
  unfold choice
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [false_iff]
    intro heq
    exact h (heq ▸ slot.isLt)

theorem choiceLaw_some_mass (capacity seen : ℕ) (hc : capacity ≤ seen) (slot : Fin capacity) :
    (choiceLaw capacity seen).mass (some slot) = 1 / (seen + 1 : ℝ) := by
  classical
  let draw : Fin (seen + 1) := ⟨slot.val, lt_of_lt_of_le slot.isLt (Nat.le_succ_of_le hc)⟩
  have hchoice (other : Fin (seen + 1)) :
      some slot = choice capacity seen other ↔ other = draw := by
    rw [eq_comm, choice_eq_some_iff]
    change other.val = draw.val ↔ other = draw
    exact Fin.ext_iff.symm
  simp only [choiceLaw, pushforward, FiniteReportLaw.bind, pointMass, uniformDraw]
  simp only [hchoice]
  simp

theorem choiceLaw_none_mass (capacity seen : ℕ) (hc : capacity ≤ seen) :
    (choiceLaw capacity seen).mass none = 1 - capacity / (seen + 1 : ℝ) := by
  have h := (choiceLaw capacity seen).mass_sum
  rw [Fintype.sum_option] at h
  simp only [choiceLaw_some_mass capacity seen hc, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hm : (capacity : ℝ) * (1 / (seen + 1 : ℝ)) = capacity / (seen + 1 : ℝ) := by ring
  rw [hm] at h
  linarith

/-- The integer draw assigns each specific slot probability `1/(seen+1)`;
all other integers leave every slot unchanged. -/
theorem choiceLaw_expectation (capacity seen : ℕ) (hc : capacity ≤ seen)
    (f : Option (Fin capacity) → ℝ) :
    (choiceLaw capacity seen).expectation f =
      (1 - capacity / (seen + 1 : ℝ)) * f none +
        (1 / (seen + 1 : ℝ)) * ∑ slot, f (some slot) := by
  unfold expectation
  rw [Fintype.sum_option, choiceLaw_none_mass capacity seen hc]
  simp only [choiceLaw_some_mass capacity seen hc, Finset.mul_sum]

def keepSlots {capacity seen : ℕ} (slots : Slots capacity seen) : Slots capacity (seen + 1) where
  toFun := fun slot ↦ (slots slot).castSucc
  inj' := fun _ _ h ↦ slots.injective (Fin.castSucc_injective seen h)

def replaceSlot {capacity seen : ℕ} (slots : Slots capacity seen) (slot : Fin capacity) :
    Slots capacity (seen + 1) where
  toFun := Function.update (fun i ↦ (slots i).castSucc) slot (Fin.last seen)
  inj' := by
    intro a b hab
    by_cases ha : a = slot
    · subst a
      by_cases hb : b = slot
      · exact hb.symm
      · simp only [Function.update_self, Function.update_of_ne hb] at hab
        have hlt := Fin.castSucc_lt_last (slots b)
        rw [← hab] at hlt
        exact False.elim (lt_irrefl _ hlt)
    · by_cases hb : b = slot
      · subst b
        simp only [Function.update_self, Function.update_of_ne ha] at hab
        have hlt := Fin.castSucc_lt_last (slots a)
        rw [hab] at hlt
        exact False.elim (lt_irrefl _ hlt)
      · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact slots.injective (Fin.castSucc_injective seen hab)

def nextSlots {capacity seen : ℕ} (slots : Slots capacity seen) :
    Option (Fin capacity) → Slots capacity (seen + 1)
  | none => keepSlots slots
  | some slot => replaceSlot slots slot

noncomputable def kernel {capacity seen : ℕ} (slots : Slots capacity seen) :
    FiniteReportLaw (Slots capacity (seen + 1)) :=
  (choiceLaw capacity seen).pushforward (nextSlots slots)

/-- Initial filling places the first eligible column in slot zero, and so on.
Every subsequent random update preserves an ordered injection into the stream. -/
noncomputable def lawAfter (capacity : ℕ) :
    (extra : ℕ) → FiniteReportLaw (Slots capacity (capacity + extra))
  | 0 => pointMass (Function.Embedding.refl (Fin capacity))
  | extra + 1 => (lawAfter capacity extra).bind kernel

noncomputable def retainedSum {capacity seen : ℕ} (f : Fin seen → ℝ)
    (slots : Slots capacity seen) : ℝ := ∑ slot, f (slots slot)

theorem retainedSum_keep {capacity seen : ℕ} (f : Fin (seen + 1) → ℝ)
    (slots : Slots capacity seen) :
    retainedSum f (keepSlots slots) = retainedSum (fun i ↦ f i.castSucc) slots := rfl

theorem retainedSum_replace {capacity seen : ℕ} (f : Fin (seen + 1) → ℝ)
    (slots : Slots capacity seen) (slot : Fin capacity) :
    retainedSum f (replaceSlot slots slot) =
      retainedSum (fun i ↦ f i.castSucc) slots - f (slots slot).castSucc + f (Fin.last seen) := by
  have heq : (fun i ↦ f (replaceSlot slots slot i)) =
      Function.update (fun i ↦ f (slots i).castSucc) slot (f (Fin.last seen)) := by
    funext i
    by_cases hi : i = slot
    · subst i
      simp [replaceSlot, Function.update_self]
    · simp [replaceSlot, Function.update_of_ne hi]
  unfold retainedSum
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ slot), Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add Finset.univ (fun i ↦ f (slots i).castSucc) (Finset.mem_univ slot)
  linarith

theorem kernel_expectation {capacity seen : ℕ} (hc : capacity ≤ seen)
    (slots : Slots capacity seen) (f : Slots capacity (seen + 1) → ℝ) :
    (kernel slots).expectation f =
      (1 - capacity / (seen + 1 : ℝ)) * f (keepSlots slots) +
        (1 / (seen + 1 : ℝ)) * ∑ slot, f (replaceSlot slots slot) := by
  rw [kernel, expectation_pushforward, choiceLaw_expectation capacity seen hc]
  rfl

/-- The mean retained sum has a closed one-step law, even though the complete
ordered reservoir law is not uniform over slot permutations. -/
theorem kernel_retainedSum {capacity seen : ℕ} (hc : capacity ≤ seen)
    (slots : Slots capacity seen) (f : Fin (seen + 1) → ℝ) :
    (kernel slots).expectation (retainedSum f) =
      (1 - 1 / (seen + 1 : ℝ)) * retainedSum (fun i ↦ f i.castSucc) slots +
        (capacity / (seen + 1 : ℝ)) * f (Fin.last seen) := by
  rw [kernel_expectation hc]
  simp only [retainedSum_keep, retainedSum_replace, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold retainedSum
  ring

/-- Every eligible stream item has the same first-order retention weight.
The proof uses the ordered Algorithm R update, not an assumed unordered-sample law. -/
theorem lawAfter_expected_retainedSum (capacity extra : ℕ) (hc : 0 < capacity)
    (f : Fin (capacity + extra) → ℝ) :
    (lawAfter capacity extra).expectation (retainedSum f) =
      (capacity / (capacity + extra : ℝ)) * ∑ item, f item := by
  induction extra with
  | zero =>
    rw [lawAfter, expectation_pointMass]
    have hcap : (capacity : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
    simp [retainedSum, hcap]
  | succ extra ih =>
    rw [lawAfter, expectation_bind]
    simp_rw [kernel_retainedSum (Nat.le_add_right capacity extra)]
    have hlinear (a b : ℝ) (g : Slots capacity (capacity + extra) → ℝ) :
        (lawAfter capacity extra).expectation (fun slots ↦ a * g slots + b) =
          a * (lawAfter capacity extra).expectation g + b := by
      unfold expectation
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, (lawAfter capacity extra).mass_sum, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro slots _
      ring
    rw [hlinear, ih]
    have hsum := Fin.sum_univ_castSucc (n := capacity + extra) f
    erw [hsum]
    have hden : (capacity + extra : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- Applying any genotype-column readout to the ordered slot vector yields
its full output law, retaining the ordering supplied to PCA. -/
noncomputable def columnLaw {Column : Type*} [Fintype Column]
    (capacity extra : ℕ) (column : Fin (capacity + extra) → Column) :
    FiniteReportLaw (Fin capacity → Column) :=
  (lawAfter capacity extra).pushforward (fun slots slot ↦ column (slots slot))

theorem columnLaw_expectation {Column : Type*} [Fintype Column]
    (capacity extra : ℕ) (column : Fin (capacity + extra) → Column)
    (readout : (Fin capacity → Column) → ℝ) :
    (columnLaw capacity extra column).expectation readout =
      (lawAfter capacity extra).expectation
        (fun slots ↦ readout (fun slot ↦ column (slots slot))) :=
  expectation_pushforward _ _ _

/-- An early stream item can survive only in the slot where initial filling
placed it. Algorithm R never moves a retained item to another slot. -/
def EarlyStable {capacity seen : ℕ} (slots : Slots capacity seen) : Prop :=
  ∀ slot, (slots slot).val < capacity → (slots slot).val = slot.val

theorem earlyStable_keep {capacity seen : ℕ} (slots : Slots capacity seen)
    (hs : EarlyStable slots) : EarlyStable (keepSlots slots) := hs

theorem earlyStable_replace {capacity seen : ℕ} (hc : capacity ≤ seen)
    (slots : Slots capacity seen) (hs : EarlyStable slots) (slot : Fin capacity) :
    EarlyStable (replaceSlot slots slot) := by
  intro i hi
  by_cases h : i = slot
  · subst i
    simp only [replaceSlot, Function.Embedding.coeFn_mk, Function.update_self, Fin.val_last] at hi
    omega
  · simpa only [replaceSlot, Function.Embedding.coeFn_mk, Function.update_of_ne h,
      Fin.coe_castSucc] using hs i (by simpa [replaceSlot, Function.update_of_ne h] using hi)

theorem kernel_unstable_mass_zero {capacity seen : ℕ} (hc : capacity ≤ seen)
    (slots : Slots capacity seen) (hs : EarlyStable slots)
    (next : Slots capacity (seen + 1)) (hn : ¬ EarlyStable next) :
    (kernel slots).mass next = 0 := by
  classical
  simp only [kernel, pushforward, FiniteReportLaw.bind, pointMass]
  apply Finset.sum_eq_zero
  intro event _
  have hstable : EarlyStable (nextSlots slots event) := by
    cases event with
    | none => exact earlyStable_keep slots hs
    | some slot => exact earlyStable_replace hc slots hs slot
  have hne : next ≠ nextSlots slots event := by
    intro heq
    exact hn (heq ▸ hstable)
  simp [hne]

theorem lawAfter_unstable_mass_zero (capacity extra : ℕ)
    (slots : Slots capacity (capacity + extra)) (hs : ¬ EarlyStable slots) :
    (lawAfter capacity extra).mass slots = 0 := by
  classical
  induction extra with
  | zero =>
    have hstable : EarlyStable (Function.Embedding.refl (Fin capacity)) := by
      intro slot _
      rfl
    have hne : slots ≠ Function.Embedding.refl (Fin capacity) := by
      intro heq
      exact hs (heq ▸ hstable)
    simp [lawAfter, pointMass, hne]
  | succ extra ih =>
    simp only [lawAfter, FiniteReportLaw.bind]
    apply Finset.sum_eq_zero
    intro previous _
    by_cases hp : EarlyStable previous
    · rw [kernel_unstable_mass_zero (Nat.le_add_right capacity extra) previous hp slots hs,
        mul_zero]
    · rw [ih previous hp, zero_mul]

def castSeen {capacity seen total : ℕ} (h : seen = total) (slots : Slots capacity seen) :
    Slots capacity total := slots.trans (finCongr h).toEmbedding

/-- If fewer eligible columns exist than requested slots, the effective
capacity is the stream length and the whole stream is filled deterministically. -/
noncomputable def completeLaw (requested total : ℕ) :
    FiniteReportLaw (Slots (min requested total) total) :=
  (lawAfter (min requested total) (total - min requested total)).pushforward
    (castSeen (Nat.add_sub_of_le (Nat.min_le_right requested total)))

theorem completeLaw_expected_retainedSum (requested total : ℕ)
    (hc : 0 < min requested total) (f : Fin total → ℝ) :
    (completeLaw requested total).expectation (retainedSum f) =
      (min requested total / (total : ℝ)) * ∑ item, f item := by
  let capacity := min requested total
  have hsize : capacity + (total - capacity) = total :=
    Nat.add_sub_of_le (Nat.min_le_right requested total)
  rw [completeLaw, expectation_pushforward]
  change (lawAfter capacity (total - capacity)).expectation
    (retainedSum (fun i ↦ f (finCongr hsize i))) = _
  rw [lawAfter_expected_retainedSum capacity (total - capacity) hc]
  have hsum : (∑ i : Fin (capacity + (total - capacity)), f (finCongr hsize i)) =
      ∑ i : Fin total, f i := Fintype.sum_equiv (finCongr hsize) _ _ (fun _ ↦ rfl)
  rw [hsum]
  have hcast : (capacity : ℝ) + (total - capacity : ℕ) = total := by exact_mod_cast hsize
  rw [hcast]

end Descent.Portability.ReservoirSamplingLaw
