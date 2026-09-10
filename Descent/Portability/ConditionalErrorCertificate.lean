/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteNumericalCertificate

assert_below Descent.Decision Descent.Program

/-!
Sharp amplification of finite-law total variation by conditioning on one
common acceptance event, together with certified ratio intervals. Positive
acceptance probabilities are required rather than assigning values to failure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalErrorCertificate

open FiniteReportLaw FiniteNumericalCertificate

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def eventMass (p : FiniteReportLaw S) (accepted : Finset S) : ℝ :=
  ∑ state, if state ∈ accepted then p.mass state else 0

theorem eventMass_nonneg (p : FiniteReportLaw S) (accepted : Finset S) :
    0 ≤ eventMass p accepted := by
  apply Finset.sum_nonneg
  intro state _
  split_ifs
  · exact p.mass_nonneg state
  · rfl

theorem eventMass_le_one (p : FiniteReportLaw S) (accepted : Finset S) :
    eventMass p accepted ≤ 1 := by
  rw [← p.mass_sum]
  apply Finset.sum_le_sum
  intro state _
  split_ifs
  · rfl
  · exact p.mass_nonneg state

noncomputable def condition (p : FiniteReportLaw S) (accepted : Finset S)
    (hpos : 0 < eventMass p accepted) : FiniteReportLaw S where
  mass := fun state ↦ (if state ∈ accepted then p.mass state else 0) / eventMass p accepted
  mass_nonneg := by
    intro state
    apply div_nonneg _ (le_of_lt hpos)
    split_ifs
    · exact p.mass_nonneg state
    · rfl
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

omit [DecidableEq S] in
theorem totalVariation_overlap (p q : FiniteReportLaw S) :
    p.totalVariation q = 1 - ∑ state, min (p.mass state) (q.mass state) := by
  have hpoint (state : S) : max (p.mass state - q.mass state) 0 =
      p.mass state - min (p.mass state) (q.mass state) := by
    by_cases h : p.mass state ≤ q.mass state
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_self]
    · rw [min_eq_right (le_of_not_ge h), max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
  simp only [totalVariation, hpoint, Finset.sum_sub_distrib, p.mass_sum]

private theorem accepted_overlap_lower (p q : FiniteReportLaw S) (accepted : Finset S) :
    eventMass q accepted - p.totalVariation q ≤
      ∑ state, if state ∈ accepted then min (p.mass state) (q.mass state) else 0 := by
  have hpoint (state : S) : q.mass state - min (p.mass state) (q.mass state) =
      max (q.mass state - p.mass state) 0 := by
    by_cases h : p.mass state ≤ q.mass state
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    · rw [min_eq_right (le_of_not_ge h), max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), sub_self]
  have hle : eventMass q accepted -
      (∑ state, if state ∈ accepted then min (p.mass state) (q.mass state) else 0) ≤
        q.totalVariation p := by
    unfold eventMass totalVariation
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro state _
    by_cases hs : state ∈ accepted
    · simp only [if_pos hs, hpoint]
      exact le_rfl
    · simp only [if_neg hs, sub_self]
      exact le_max_right _ _
  rw [totalVariation_symm q p] at hle
  linarith

private theorem conditional_bound_of_le (p q : FiniteReportLaw S) (accepted : Finset S)
    (hp : 0 < eventMass p accepted) (hq : 0 < eventMass q accepted)
    (hle : eventMass p accepted ≤ eventMass q accepted) :
    (condition p accepted hp).totalVariation (condition q accepted hq) ≤
      p.totalVariation q / eventMass q accepted := by
  have hinside := accepted_overlap_lower p q accepted
  have hsum :
      (∑ state, if state ∈ accepted then min (p.mass state) (q.mass state) else 0) /
          eventMass q accepted ≤
        ∑ state, min ((condition p accepted hp).mass state)
          ((condition q accepted hq).mass state) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro state _
    by_cases hs : state ∈ accepted
    · simp only [if_pos hs, condition]
      apply le_min
      · exact (div_le_div_of_nonneg_left
          (p.mass_nonneg state) hp hle).trans' (div_le_div_of_nonneg_right (min_le_left _ _) hq.le)
      · exact div_le_div_of_nonneg_right (min_le_right _ _) hq.le
    · simp [condition, hs]
  rw [totalVariation_overlap]
  have hh := (div_le_div_of_nonneg_right hinside hq.le).trans hsum
  rw [sub_div, div_self (ne_of_gt hq)] at hh
  linarith

/-- The denominator is the larger acceptance probability, and the bound is sharp. -/
theorem conditional_totalVariation (p q : FiniteReportLaw S) (accepted : Finset S)
    (hp : 0 < eventMass p accepted) (hq : 0 < eventMass q accepted) :
    (condition p accepted hp).totalVariation (condition q accepted hq) ≤
      min 1 (p.totalVariation q / max (eventMass p accepted) (eventMass q accepted)) := by
  apply le_min (totalVariation_le_one _ _)
  by_cases hle : eventMass p accepted ≤ eventMass q accepted
  · rw [max_eq_right hle]
    exact conditional_bound_of_le p q accepted hp hq hle
  · rw [max_eq_left (le_of_not_ge hle), totalVariation_symm (condition p accepted hp)]
    simpa only [totalVariation_symm q p] using
      conditional_bound_of_le q p accepted hq hp (le_of_not_ge hle)

/-- Separate numerator and denominator certificates imply a valid clipped interval. -/
theorem conditional_mean_interval (numerator denominator estimateN estimateD errorN errorD : ℝ)
    (hn : 0 ≤ numerator) (hnd : numerator ≤ denominator)
    (hen : |numerator - estimateN| ≤ errorN)
    (hed : |denominator - estimateD| ≤ errorD) (hguard : errorD < estimateD) :
    max 0 ((estimateN - errorN) / (estimateD + errorD)) ≤ numerator / denominator ∧
      numerator / denominator ≤ min 1 ((estimateN + errorN) / (estimateD - errorD)) := by
  have hdn := le_trans (abs_nonneg _) hed
  obtain ⟨hnlo, hnhi⟩ := abs_le.mp hen
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hed
  have hpos : 0 < denominator := by linarith
  have hlo : 0 < estimateD - errorD := sub_pos.mpr hguard
  have hhi : 0 < estimateD + errorD := by linarith
  constructor
  · apply max_le (div_nonneg hn hpos.le)
    apply (div_le_div_iff₀ hhi hpos).mpr
    calc
      (estimateN - errorN) * denominator ≤ numerator * denominator :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ ≤ numerator * (estimateD + errorD) :=
        mul_le_mul_of_nonneg_left (by linarith) hn
  · apply le_min ((div_le_one hpos).mpr hnd)
    apply (div_le_div_iff₀ hpos hlo).mpr
    calc
      numerator * (estimateD - errorD) ≤ numerator * denominator :=
        mul_le_mul_of_nonneg_left (by linarith) hn
      _ ≤ (estimateN + errorN) * denominator :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le

noncomputable def sharpSource : FiniteReportLaw (Fin 3) where
  mass := ![1 / 10, 0, 9 / 10]
  mass_nonneg := by intro state; fin_cases state <;> norm_num
  mass_sum := by norm_num [Fin.sum_univ_succ]

noncomputable def sharpTarget : FiniteReportLaw (Fin 3) where
  mass := ![1 / 10, 1 / 10, 8 / 10]
  mass_nonneg := by intro state; fin_cases state <;> norm_num
  mass_sum := by norm_num [Fin.sum_univ_succ]

theorem sharpSource_acceptance : eventMass sharpSource {0, 1} = 1 / 10 := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [eventMass, sharpSource, Fin.sum_univ_succ, h21]

theorem sharpTarget_acceptance : eventMass sharpTarget {0, 1} = 1 / 5 := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [eventMass, sharpTarget, Fin.sum_univ_succ, h21]

/-- Two accepted states and one rejected state attain the amplification bound. -/
theorem sharp_amplification : sharpSource.totalVariation sharpTarget = 1 / 10 ∧
    (condition sharpSource {0, 1} (by rw [sharpSource_acceptance]; norm_num)).totalVariation
      (condition sharpTarget {0, 1} (by rw [sharpTarget_acceptance]; norm_num)) =
        sharpSource.totalVariation sharpTarget /
          max (eventMass sharpSource {0, 1}) (eventMass sharpTarget {0, 1}) ∧
    sharpSource.totalVariation sharpTarget /
      max (eventMass sharpSource {0, 1}) (eventMass sharpTarget {0, 1}) = 1 / 2 := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [totalVariation, condition, eventMass, sharpSource, sharpTarget,
    Fin.sum_univ_succ, h21]

end Descent.Portability.ConditionalErrorCertificate
