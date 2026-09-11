/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RareEventInformationLaw
import Descent.Portability.IIDAverageLaw

assert_below Descent.Decision Descent.Program

/-!
The report's marked and erased estimators under the actual M-observation product
experiment. Their means are derived at every effect size, and their null
variances have the stated distinct powers of event probability. Square
integrability and independence are proved for the actual sampling law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RareEventSampleLaw

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory RareEventInformationLaw IIDAverageLaw

/-- The observed-event inverse-probability statistic. -/
noncomputable def markedEstimate (η : ℝ) (zy : Bool × ℝ) : ℝ :=
  if zy.1 then zy.2 / η else 0

/-- The inverse-probability statistic using only the phenotype. -/
noncomputable def erasedEstimate (η : ℝ) (zy : Bool × ℝ) : ℝ := zy.2 / η

/-- The marked statistic is measurable in the actual observation. -/
theorem markedEstimate_measurable (η : ℝ) : Measurable (markedEstimate η) :=
  Measurable.ite ((measurableSet_singleton true).preimage measurable_fst)
    (measurable_snd.div_const η) measurable_const

/-- The erased statistic is measurable and does not use the event coordinate. -/
theorem erasedEstimate_measurable (η : ℝ) : Measurable (erasedEstimate η) :=
  measurable_snd.div_const η

/-- Integrability under each conditional Gaussian gives integrability under the actual mixture. -/
theorem experiment_integrable (η : ℝ) (v : ℝ≥0) (θ : ℝ) (f : Bool × ℝ → ℝ)
    (hf : Measurable f) (h0 : Integrable (fun y ↦ f (false, y)) (gaussianReal 0 v))
    (h1 : Integrable (fun y ↦ f (true, y)) (gaussianReal θ v)) :
    Integrable f (experimentLaw η v θ) := by
  have hi0 : Integrable f ((gaussianReal 0 v).map (fun y ↦ (false, y))) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mpr h0
  have hi1 : Integrable f ((gaussianReal θ v).map (fun y ↦ (true, y))) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mpr h1
  exact (hi0.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hi1.smul_measure ENNReal.ofReal_ne_top)

/-- The actual marked statistic is square integrable at every effect size. -/
theorem markedEstimate_memLp (η : ℝ) (v : ℝ≥0) (θ : ℝ) :
    MemLp (markedEstimate η) 2 (experimentLaw η v θ) := by
  apply (memLp_two_iff_integrable_sq (markedEstimate_measurable η).aestronglyMeasurable).mpr
  apply experiment_integrable η v θ _ ((markedEstimate_measurable η).pow_const 2)
  · simp [markedEstimate]
  · simpa [markedEstimate, div_eq_mul_inv, mul_comm] using
      ((memLp_id_gaussianReal (μ := θ) (v := v) 2).const_mul (1 / η)).integrable_sq

/-- The actual erased statistic is square integrable at every effect size. -/
theorem erasedEstimate_memLp (η : ℝ) (v : ℝ≥0) (θ : ℝ) :
    MemLp (erasedEstimate η) 2 (experimentLaw η v θ) := by
  apply (memLp_two_iff_integrable_sq (erasedEstimate_measurable η).aestronglyMeasurable).mpr
  apply experiment_integrable η v θ _ ((erasedEstimate_measurable η).pow_const 2)
  all_goals
    simpa [erasedEstimate, div_eq_mul_inv, mul_comm] using
      ((memLp_id_gaussianReal (μ := _) (v := v) 2).const_mul (1 / η)).integrable_sq

/-- Exact marked mean as an integral under the actual experiment probability law. -/
theorem markedEstimate_mean (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0) (θ : ℝ) :
    (∫ zy, markedEstimate η zy ∂experimentLaw η v θ) = θ := by
  rw [← experimentExpectation_eq_integral η ⟨hη.1.le, hη.2⟩ v θ
    (fun z y ↦ markedEstimate η (z, y)) (markedEstimate_measurable η)]
  · exact marked_estimator_unbiased η hη.1.ne' v θ
  · simp [markedEstimate]
  · exact ((memLp_id_gaussianReal (μ := θ) (v := v) 2).integrable one_le_two).div_const η

/-- Exact erased mean as an integral under the same experiment probability law. -/
theorem erasedEstimate_mean (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0) (θ : ℝ) :
    (∫ zy, erasedEstimate η zy ∂experimentLaw η v θ) = θ := by
  rw [← experimentExpectation_eq_integral η ⟨hη.1.le, hη.2⟩ v θ
    (fun z y ↦ erasedEstimate η (z, y)) (erasedEstimate_measurable η)]
  · exact erased_estimator_unbiased η hη.1.ne' v θ
  all_goals
    exact ((memLp_id_gaussianReal (μ := _) (v := v) 2).integrable one_le_two).div_const η

/-- Actual one-observation marked variance at the null. -/
theorem markedEstimate_variance (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0) :
    variance (markedEstimate η) (experimentLaw η v 0) = (v : ℝ) / η := by
  letI := experimentLaw_probability η ⟨hη.1.le, hη.2⟩ v 0
  rw [variance_eq_sub (markedEstimate_memLp η v 0), markedEstimate_mean η hη v 0]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply]
  rw [← experimentExpectation_eq_integral η ⟨hη.1.le, hη.2⟩ v 0
    (fun z y ↦ markedEstimate η (z, y) ^ 2) ((markedEstimate_measurable η).pow_const 2)]
  · exact marked_estimator_null_second_moment η hη.1.ne' v
  · simp [markedEstimate]
  · simpa [markedEstimate, div_eq_mul_inv, mul_comm] using
      ((memLp_id_gaussianReal (μ := 0) (v := v) 2).const_mul (1 / η)).integrable_sq

/-- Actual one-observation erased variance at the null. -/
theorem erasedEstimate_variance (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0) :
    variance (erasedEstimate η) (experimentLaw η v 0) = (v : ℝ) / η ^ 2 := by
  letI := experimentLaw_probability η ⟨hη.1.le, hη.2⟩ v 0
  rw [variance_eq_sub (erasedEstimate_memLp η v 0), erasedEstimate_mean η hη v 0]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply]
  rw [← experimentExpectation_eq_integral η ⟨hη.1.le, hη.2⟩ v 0
    (fun z y ↦ erasedEstimate η (z, y) ^ 2) ((erasedEstimate_measurable η).pow_const 2)]
  · exact erased_estimator_null_second_moment η v
  all_goals
    simpa [erasedEstimate, div_eq_mul_inv, mul_comm] using
      ((memLp_id_gaussianReal (μ := 0) (v := v) 2).const_mul (1 / η)).integrable_sq

/-- The actual M-observation marked estimator is unbiased for every effect size. -/
theorem marked_sample_unbiased (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0) (θ : ℝ)
    (M : ℕ) (hM : 0 < M) :
    (∫ x, average (markedEstimate η) M x
      ∂Measure.pi (fun _ : Fin M ↦ experimentLaw η v θ)) = θ := by
  letI := experimentLaw_probability η ⟨hη.1.le, hη.2⟩ v θ
  rw [average_integral _ _ ((markedEstimate_memLp η v θ).integrable one_le_two) M hM,
    markedEstimate_mean η hη v θ]

/-- The actual M-observation erased estimator is unbiased for every effect size. -/
theorem erased_sample_unbiased (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0) (θ : ℝ)
    (M : ℕ) (hM : 0 < M) :
    (∫ x, average (erasedEstimate η) M x
      ∂Measure.pi (fun _ : Fin M ↦ experimentLaw η v θ)) = θ := by
  letI := experimentLaw_probability η ⟨hη.1.le, hη.2⟩ v θ
  rw [average_integral _ _ ((erasedEstimate_memLp η v θ).integrable one_le_two) M hM,
    erasedEstimate_mean η hη v θ]

/-- Exact finite-sample null variance with genotype events observed. -/
theorem marked_sample_variance (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0)
    (M : ℕ) (hM : 0 < M) :
    variance (average (markedEstimate η) M)
      (Measure.pi (fun _ : Fin M ↦ experimentLaw η v 0)) = (v : ℝ) / ((M : ℝ) * η) := by
  letI := experimentLaw_probability η ⟨hη.1.le, hη.2⟩ v 0
  rw [average_variance _ _ (markedEstimate_memLp η v 0) M hM, markedEstimate_variance η hη v]
  ring

/-- Exact finite-sample null variance when the estimator observes phenotypes only. -/
theorem erased_sample_variance (η : ℝ) (hη : 0 < η ∧ η ≤ 1) (v : ℝ≥0)
    (M : ℕ) (hM : 0 < M) :
    variance (average (erasedEstimate η) M)
      (Measure.pi (fun _ : Fin M ↦ experimentLaw η v 0)) = (v : ℝ) / ((M : ℝ) * η ^ 2) := by
  letI := experimentLaw_probability η ⟨hη.1.le, hη.2⟩ v 0
  rw [average_variance _ _ (erasedEstimate_memLp η v 0) M hM, erasedEstimate_variance η hη v]
  ring

end Descent.Portability.RareEventSampleLaw
