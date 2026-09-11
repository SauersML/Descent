/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Transport
import Mathlib.Data.Fintype.Powerset

assert_below Descent.Decision Descent.Program

/-!
# Modern factorial contrasts identify a degree-limited response

Theorem 3: explicit subset-lattice inversion, with no response information
inferred from finding a sequence alone. `subsetResponse` is the response of
the actual multilinear polynomial at the indicated binary state.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma powerset_eq_filter (S : Finset I) :
    S.powerset = Finset.univ.filter (fun T => T ⊆ S) := by ext; simp

/-- The alternating interval sum that cancels all proper-subset contributions. -/
lemma alternating_subset_sum (S U : Finset I) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * (if U ⊆ T then 1 else 0)) =
      if U = S then 1 else 0 := by
  by_cases hu : U ⊆ S
  · have hg (T : Finset I) (ht : T ⊆ S) :
        (∏ i ∈ S \ T, if i ∈ U then (0 : ℝ) else -1) =
          if U ⊆ T then (-1 : ℝ) ^ (S.card - T.card) else 0 := by
      by_cases h : U ⊆ T
      · rw [if_pos h]
        calc
          _ = ∏ _i ∈ S \ T, (-1 : ℝ) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact if_neg (fun hui => (Finset.mem_sdiff.mp hi).2 (h hui))
          _ = _ := by simp [Finset.card_sdiff_of_subset ht]
      · rw [if_neg h]
        obtain ⟨i, hiU, hiT⟩ := Finset.not_subset.mp h
        exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hu hiU, hiT⟩) (if_pos hiU)
    have hx := Finset.prod_add (fun _ : I => (1 : ℝ)) (fun i => if i ∈ U then 0 else -1) S
    have hl : (∏ i ∈ S, ((1 : ℝ) + if i ∈ U then 0 else -1)) = if U = S then 1 else 0 := by
      by_cases h : U = S
      · subst U
        rw [if_pos rfl]
        exact Finset.prod_eq_one fun i hi => by simp [hi]
      · rw [if_neg h]
        have hn : ¬ S ⊆ U := fun hh => h (Finset.Subset.antisymm hu hh)
        obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp hn
        apply Finset.prod_eq_zero hiS
        simp [hiU]
    rw [hl] at hx
    rw [hx]
    apply Finset.sum_congr rfl
    intro T ht
    rw [hg T (Finset.mem_powerset.mp ht)]
    split_ifs <;> simp
  · rw [if_neg (fun h => hu (by rw [h]))]
    apply Finset.sum_eq_zero
    intro T ht
    have hn : ¬ U ⊆ T := fun h => hu (h.trans (Finset.mem_powerset.mp ht))
    simp [hn]

noncomputable def subsetResponse (a : Finset I → ℝ) (T : Finset I) : ℝ :=
  ∑ U ∈ T.powerset, a U

theorem subsetResponse_evaluation (a : Finset I → ℝ) (T : Finset I) :
    MvPolynomial.eval (fun i => if i ∈ T then (1 : ℝ) else 0) (responsePolynomial a) =
      subsetResponse a T := by
  simp only [responsePolynomial, map_sum, map_mul, map_prod, MvPolynomial.eval_C,
    MvPolynomial.eval_X, subsetResponse, powerset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : S ⊆ T
  · simp [h, Finset.prod_eq_one (fun i hi => if_pos (h hi))]
  · rw [if_neg h]
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp h
    rw [Finset.prod_eq_zero hiS (if_neg hiT), mul_zero]

/-- The explicit Möbius inversion formula, valid at every order. -/
theorem factorial_recovery (a : Finset I → ℝ) (S : Finset I) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * subsetResponse a T = a S := by
  simp only [subsetResponse, powerset_eq_filter, Finset.sum_filter, Finset.mul_sum]
  have houter (T : Finset I) :
      (if T ⊆ S then ∑ U : Finset I, (-1 : ℝ) ^ (S.card - T.card) *
        (if U ⊆ T then a U else 0) else 0) =
      ∑ U : Finset I, if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) *
        (if U ⊆ T then a U else 0) else 0 := by
    by_cases h : T ⊆ S <;> simp [h]
  simp_rw [houter]
  rw [Finset.sum_comm]
  have hterm (U : Finset I) :
      (∑ T : Finset I, if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) *
        (if U ⊆ T then a U else 0) else 0) = a U * (if U = S then 1 else 0) := by
    rw [← alternating_subset_sum S U, Finset.mul_sum]
    rw [powerset_eq_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    by_cases ht : T ⊆ S <;> by_cases hu : U ⊆ T <;> simp [ht, hu] <;> ring
  simp_rw [hterm]
  simp

/-- Low-degree state measurements identify the entire low-degree coefficient map. -/
theorem degree_panel_identifies (d : ℕ) (a b : Finset I → ℝ)
    (ha : ∀ S, d < S.card → a S = 0) (hb : ∀ S, d < S.card → b S = 0)
    (hpanel : ∀ T, T.card ≤ d → subsetResponse a T = subsetResponse b T) : a = b := by
  funext S
  by_cases hs : S.card ≤ d
  · rw [← factorial_recovery a S, ← factorial_recovery b S]
    apply Finset.sum_congr rfl
    intro T ht
    rw [hpanel T ((Finset.card_le_card (Finset.mem_powerset.mp ht)).trans hs)]
  · rw [ha S (Nat.lt_of_not_ge hs), hb S (Nat.lt_of_not_ge hs)]

end Descent.Portability.ArchaicPrediction
