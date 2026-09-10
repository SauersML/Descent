/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Analysis.Convex.StdSimplex

assert_below Descent.Decision Descent.Program

/-!
Sharp finite-law expectation ranges under linear observation constraints.
Compactness gives attained endpoints; mixtures fill the entire interval.
Dual inequalities certify endpoints without relying on optimizer convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteMetricIdentification

open scoped BigOperators

variable {S O : Type*} [Fintype S]

noncomputable def pairing (f p : S → ℝ) : ℝ := ∑ state, f state * p state

theorem pairing_add (f p q : S → ℝ) : pairing f (p + q) = pairing f p + pairing f q := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_smul (f p : S → ℝ) (a : ℝ) : pairing f (a • p) = a * pairing f p := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro state _
  ring

theorem continuous_pairing (f : S → ℝ) : Continuous (pairing f) :=
  continuous_finset_sum _ (fun state _ ↦ continuous_const.mul (continuous_apply state))

noncomputable def feasible (observe : O → S → ℝ) (observed : O → ℝ) : Set (S → ℝ) :=
  stdSimplex ℝ S ∩ {p | ∀ observation, pairing (observe observation) p = observed observation}

theorem feasible_compact (observe : O → S → ℝ) (observed : O → ℝ) :
    IsCompact (feasible observe observed) := by
  apply (isCompact_stdSimplex S).inter_right
  convert isClosed_iInter (fun observation ↦
    isClosed_eq (continuous_pairing (observe observation))
      (continuous_const : Continuous (fun _ : S → ℝ ↦ observed observation))) using 1
  ext p
  simp

theorem feasible_convex (observe : O → S → ℝ) (observed : O → ℝ) :
    Convex ℝ (feasible observe observed) := by
  intro p hp q hq a b ha hb hab
  constructor
  · exact convex_stdSimplex ℝ S hp.1 hq.1 ha hb hab
  · intro observation
    rw [pairing_add, pairing_smul, pairing_smul, hp.2 observation, hq.2 observation]
    rw [← add_mul, hab, one_mul]

/-- The exact identified set is a closed interval with both endpoint laws attained. -/
theorem sharp_metric_interval (observe : O → S → ℝ) (observed : O → ℝ)
    (hne : (feasible observe observed).Nonempty) (metric : S → ℝ) :
    ∃ lower ∈ feasible observe observed, ∃ upper ∈ feasible observe observed,
      pairing metric '' feasible observe observed =
        Set.Icc (pairing metric lower) (pairing metric upper) := by
  obtain ⟨lower, hlower, hmin⟩ := (feasible_compact observe observed).exists_isMinOn hne
    (continuous_pairing metric).continuousOn
  obtain ⟨upper, hupper, hmax⟩ := (feasible_compact observe observed).exists_isMaxOn hne
    (continuous_pairing metric).continuousOn
  refine ⟨lower, hlower, upper, hupper, ?_⟩
  ext value
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hmin hp, hmax hp⟩
  · intro hv
    have horder : pairing metric lower ≤ pairing metric upper := hmin hupper
    by_cases heq : pairing metric lower = pairing metric upper
    · have hz : pairing metric lower = value := by rcases hv with ⟨hlo, hhi⟩; linarith
      exact ⟨lower, hlower, hz⟩
    · have hdiff : 0 < pairing metric upper - pairing metric lower :=
        sub_pos.mpr (lt_of_le_of_ne horder heq)
      let t := (value - pairing metric lower) /
        (pairing metric upper - pairing metric lower)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hv.1) hdiff.le
      have ht1 : t ≤ 1 := (div_le_one hdiff).mpr (by linarith [hv.2])
      refine ⟨(1 - t) • lower + t • upper,
        feasible_convex observe observed hlower hupper (sub_nonneg.mpr ht1) ht0 (by ring), ?_⟩
      rw [pairing_add, pairing_smul, pairing_smul]
      dsimp only [t]
      field_simp
      ring

section Dual

variable [Fintype O]

/-- A feasible upper dual certificate bounds every compatible report law. -/
theorem dual_upper (observe : O → S → ℝ) (observed : O → ℝ)
    (metric : S → ℝ) (certificate : O → ℝ)
    (hcertificate : ∀ state, metric state ≤ ∑ observation,
      certificate observation * observe observation state)
    (p : S → ℝ) (hp : p ∈ feasible observe observed) :
    pairing metric p ≤ pairing certificate observed := by
  calc
    pairing metric p ≤ ∑ state,
        (∑ observation, certificate observation * observe observation state) * p state := by
      exact Finset.sum_le_sum (fun state _ ↦
        mul_le_mul_of_nonneg_right (hcertificate state) (hp.1.1 state))
    _ = ∑ observation, certificate observation * pairing (observe observation) p := by
      simp only [pairing, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = pairing certificate observed := by
      change (∑ observation, certificate observation * pairing (observe observation) p) =
        ∑ observation, certificate observation * observed observation
      apply Finset.sum_congr rfl
      intro observation _
      rw [hp.2 observation]

theorem dual_lower (observe : O → S → ℝ) (observed : O → ℝ)
    (metric : S → ℝ) (certificate : O → ℝ)
    (hcertificate : ∀ state, (∑ observation,
      certificate observation * observe observation state) ≤ metric state)
    (p : S → ℝ) (hp : p ∈ feasible observe observed) :
    pairing certificate observed ≤ pairing metric p := by
  calc
    pairing certificate observed =
        ∑ observation, certificate observation * pairing (observe observation) p := by
      change (∑ observation, certificate observation * observed observation) =
        ∑ observation, certificate observation * pairing (observe observation) p
      apply Finset.sum_congr rfl
      intro observation _
      rw [hp.2 observation]
    _ = ∑ state,
        (∑ observation, certificate observation * observe observation state) * p state := by
      simp only [pairing, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ ≤ pairing metric p := by
      exact Finset.sum_le_sum (fun state _ ↦
        mul_le_mul_of_nonneg_right (hcertificate state) (hp.1.1 state))

end Dual

end Descent.Portability.FiniteMetricIdentification
