/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialLabelFisher

assert_below Descent.Decision Descent.Program

/-!
The exact label-cost threshold follows from Fisher information under the actual
partial-observation experiment. Strictly increasing or decreasing information
per cost selects full or zero labeling; at the threshold every fraction ties.
The assumptions are the report's known event rate, Gaussian null, and additive
observation and label costs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialLabelAssayDesign

open scoped NNReal
open MeasureTheory ProbabilityTheory PartialLabelExperiment PartialLabelFisher

/-- Fisher information per observation cost under the actual revealed-data law. -/
noncomputable def informationPerCost (η : ℝ) (v : ℝ≥0) (c₀ c₁ q : ℝ) : ℝ :=
  (∫ o, (deriv (fun θ ↦ Real.log (observationDensity q η v θ o)) 0) ^ 2
    ∂observationLaw q η v 0) / (c₀ + q * c₁)

/-- The variance-normalized scalar design objective derived from that experiment. -/
noncomputable def designRate (η c₀ c₁ q : ℝ) : ℝ :=
  (η ^ 2 + q * η * (1 - η)) / (c₀ + q * c₁)

/-- The operational objective equals the closed design formula divided by noise variance. -/
theorem informationPerCost_eq (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c₀ c₁ q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    informationPerCost η v c₀ c₁ q = designRate η c₀ c₁ q / v := by
  rw [informationPerCost, partial_fisher_information q η hq hη v hv, designRate]
  ring

/-- Observation costs are strictly positive at every feasible label fraction. -/
theorem cost_pos (c₀ c₁ q : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁) (hq : 0 ≤ q) :
    0 < c₀ + q * c₁ := add_pos_of_pos_of_nonneg hc₀ (mul_nonneg hq hc₁)

/-- Exact finite comparison: the direction of improvement does not depend on the label fraction. -/
theorem designRate_difference (η c₀ c₁ q₁ q₂ : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    designRate η c₀ c₁ q₂ - designRate η c₀ c₁ q₁ =
      η * (q₂ - q₁) * ((1 - η) * c₀ - η * c₁) /
        ((c₀ + q₁ * c₁) * (c₀ + q₂ * c₁)) := by
  have h₁ := (cost_pos c₀ c₁ q₁ hc₀ hc₁ hq₁).ne'
  have h₂ := (cost_pos c₀ c₁ q₂ hc₀ hc₁ hq₂).ne'
  unfold designRate
  field_simp
  ring

/-- The report's relative-cost inequality is exactly the positive comparison coefficient. -/
theorem full_label_threshold (η c₀ c₁ : ℝ) (hη : 0 < η) (hc₀ : 0 < c₀) :
    c₁ / c₀ < (1 - η) / η ↔ 0 < (1 - η) * c₀ - η * c₁ := by
  rw [div_lt_div_iff₀ hc₀ hη]
  constructor <;> intro h <;> nlinarith

/-- Below the label-cost threshold the actual information per cost strictly increases. -/
theorem full_label_strictly_optimal (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁)
    (hc : c₁ / c₀ < (1 - η) / η) (q : ℝ) (hq : 0 ≤ q ∧ q < 1) :
    informationPerCost η v c₀ c₁ q < informationPerCost η v c₀ c₁ 1 := by
  rw [informationPerCost_eq η hη v hv c₀ c₁ q ⟨hq.1, hq.2.le⟩,
    informationPerCost_eq η hη v hv c₀ c₁ 1 ⟨by norm_num, le_refl _⟩]
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < v by exact_mod_cast
    (pos_iff_ne_zero.mpr hv : 0 < v))).mpr
  apply sub_pos.mp
  rw [designRate_difference η c₀ c₁ q 1 hc₀ hc₁ hq.1 (by norm_num)]
  exact div_pos (mul_pos (mul_pos hη.1 (sub_pos.mpr hq.2))
    ((full_label_threshold η c₀ c₁ hη.1 hc₀).mp hc))
    (mul_pos (cost_pos _ _ _ hc₀ hc₁ hq.1) (cost_pos _ _ _ hc₀ hc₁ (by norm_num)))

/-- Above the label-cost threshold buying no labels is strictly optimal. -/
theorem no_label_strictly_optimal (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁)
    (hc : (1 - η) / η < c₁ / c₀) (q : ℝ) (hq : 0 < q ∧ q ≤ 1) :
    informationPerCost η v c₀ c₁ q < informationPerCost η v c₀ c₁ 0 := by
  rw [informationPerCost_eq η hη v hv c₀ c₁ q ⟨hq.1.le, hq.2⟩,
    informationPerCost_eq η hη v hv c₀ c₁ 0 ⟨le_refl _, by norm_num⟩]
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < v by exact_mod_cast
    (pos_iff_ne_zero.mpr hv : 0 < v))).mpr
  apply sub_neg.mp
  rw [designRate_difference η c₀ c₁ 0 q hc₀ hc₁ (le_refl _) hq.1.le]
  have hh : (1 - η) * c₀ - η * c₁ < 0 := by
    have hh := (div_lt_div_iff₀ hη.1 hc₀).mp hc
    nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hη.1 (by simpa using hq.1)) hh)
    (mul_pos (cost_pos _ _ _ hc₀ hc₁ (le_refl _)) (cost_pos _ _ _ hc₀ hc₁ hq.1.le))

/-- At the exact cost threshold every feasible label fraction has identical information per cost. -/
theorem all_fractions_tie (η : ℝ) (hη : 0 < η ∧ η < 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁)
    (hc : c₁ / c₀ = (1 - η) / η) (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    informationPerCost η v c₀ c₁ q = informationPerCost η v c₀ c₁ 0 := by
  rw [informationPerCost_eq η hη v hv c₀ c₁ q hq,
    informationPerCost_eq η hη v hv c₀ c₁ 0 ⟨le_refl _, by norm_num⟩]
  congr 1
  apply sub_eq_zero.mp
  rw [designRate_difference η c₀ c₁ 0 q hc₀ hc₁ (le_refl _) hq.1]
  have hh : (1 - η) * c₀ - η * c₁ = 0 := by
    have hh := (div_eq_div_iff hc₀.ne' hη.1.ne').mp hc
    nlinarith
  rw [hh, mul_zero, zero_div]

end Descent.Portability.PartialLabelAssayDesign
