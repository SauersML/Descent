/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimulationDemographyLaw
import Descent.Portability.SimulationAccuracy

assert_below Descent.Decision Descent.Program

/-!
The actual phenoA baseline in the default serial and grid simulations. Centering
is across demes, before source-dependent oversampling weights the individual
cohort. Its boundedness supplies the hypothesis used by the intercept theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimulationBaselineLaw

open FiniteReportLaw SourceDesignLaw

noncomputable def epsilon : ℝ := 1 / 1000000000000

theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]

noncomputable def serialRaw (deme : Fin 10) : ℝ :=
  (7 / 5) * ((deme.val : ℝ) / (9 + epsilon) - 1 / 2)

noncomputable def serial (deme : Fin 10) : ℝ :=
  serialRaw deme - (∑ d : Fin 10, serialRaw d) / 10

/-- Centering includes the 1e-12 denominator in the original deme coordinate. -/
theorem serial_closed (deme : Fin 10) :
    serial deme = (7 / 5) * (((deme.val : ℝ) - 9 / 2) / (9 + epsilon)) := by
  norm_num [serial, serialRaw, epsilon, Fin.sum_univ_succ]
  ring

theorem serial_bounds (deme : Fin 10) : -(7 / 10 : ℝ) ≤ serial deme ∧ serial deme ≤ 7 / 10 := by
  rw [serial_closed]
  have hlow : (0 : ℝ) ≤ deme.val := Nat.cast_nonneg _
  have hhigh : (deme.val : ℝ) ≤ 9 := by exact_mod_cast (show deme.val ≤ 9 by omega)
  norm_num [epsilon]
  constructor <;> nlinarith

theorem serial_sum_zero : ∑ deme : Fin 10, serial deme = 0 := by
  simp only [serial, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

noncomputable def gridRaw (deme : Fin 36) : ℝ :=
  (7 / 5) * (((((deme.val / 6 : ℕ) : ℝ) / 5 + ((deme.val % 6 : ℕ) : ℝ) / 5) / 2) - 1 / 2)

noncomputable def grid (deme : Fin 36) : ℝ :=
  gridRaw deme - (∑ d : Fin 36, gridRaw d) / 36

private theorem gridRaw_sum_zero : ∑ d : Fin 36, gridRaw d = 0 := by
  let f : ℕ → ℝ := fun d ↦
    (7 / 5) * (((((d / 6 : ℕ) : ℝ) / 5 + ((d % 6 : ℕ) : ℝ) / 5) / 2) - 1 / 2)
  change (∑ d : Fin 36, f d.val) = 0
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [f, Finset.sum_range_succ]

theorem grid_closed (deme : Fin 36) : grid deme = gridRaw deme := by
  rw [grid, gridRaw_sum_zero]
  ring

theorem grid_bounds (deme : Fin 36) : -(7 / 10 : ℝ) ≤ grid deme ∧ grid deme ≤ 7 / 10 := by
  rw [grid_closed]
  have hr : (deme.val / 6 : ℕ) ≤ 5 := by omega
  have hc : (deme.val % 6 : ℕ) ≤ 5 := by omega
  have hr' : ((deme.val / 6 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hr
  have hc' : ((deme.val % 6 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hc
  have hr0 : (0 : ℝ) ≤ (deme.val / 6 : ℕ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (deme.val % 6 : ℕ) := Nat.cast_nonneg _
  unfold gridRaw
  constructor <;> linarith

theorem grid_sum_zero : ∑ deme : Fin 36, grid deme = 0 := by
  simp_rw [grid_closed]
  exact gridRaw_sum_zero

/-- Oversampling changes the baseline's cohort mean, despite the exact
zero mean across demes. The selected source receives 4750 additional rows. -/
theorem weighted_baseline_sum {demes : ℕ} (source : Fin demes) (baseline : Fin demes → ℝ)
    (hcentered : ∑ deme, baseline deme = 0) :
    ∑ deme, (sampleSize source deme : ℝ) * baseline deme = 4750 * baseline source := by
  classical
  have hsize (deme : Fin demes) : (sampleSize source deme : ℝ) =
      250 + if deme = source then 4750 else 0 := by
    unfold sampleSize
    split_ifs <;> norm_num
  simp_rw [hsize, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcentered]
  simp

/-- This is the baseline expectation under the actual source-dependent deme
sampling weights. It is generally not zero; the intercept solve must retain it. -/
theorem weighted_baseline_mean {demes : ℕ} (source : Fin demes) (baseline : Fin demes → ℝ)
    (hcentered : ∑ deme, baseline deme = 0) :
    (∑ deme, (sampleSize source deme : ℝ) * baseline deme) /
        (SimulationDemographyLaw.cohortSize demes : ℝ) =
      (4750 / (SimulationDemographyLaw.cohortSize demes : ℝ)) * baseline source := by
  rw [weighted_baseline_sum source baseline hcentered]
  ring

end Descent.Portability.SimulationBaselineLaw
