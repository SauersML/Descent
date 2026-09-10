/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEWeakLimit

assert_below Descent.Decision Descent.Program

/-!
The sparse balanced phase has a degenerate weak limit even under exact variance
normalization. An explicit finite-experiment bound is uniform in the jump size:
only the expected number of nonzero blocks controls bounded test observables.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEVanishingLaw

open scoped BigOperators BoundedContinuousFunction Topology
open Filter MeasureTheory Foundations HWEInteractionLaw BalancedHWEInteraction
open IndependentShiftOperator FiniteIndependentMoments BalancedHWEWeakLimit

/-- Every change of a bounded observable requires a nonzero block. -/
theorem sample_observable_bound {m N : ℕ} (a : ℝ) (f : Observable)
    (sample : Fin N → Fin m → DiploidGenotype) :
    |f (rowScore a sample) - f 0| ≤ 2 * ‖f‖ * ∑ j, blockCode (sample j) ^ 2 := by
  classical
  by_cases hzero : ∀ j, blockCode (sample j) = 0
  · simp only [rowScore, hzero, mul_zero, Finset.sum_const_zero, sub_self,
      abs_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · obtain ⟨j, hj⟩ := not_forall.mp hzero
    have hsq : blockCode (sample j) ^ 2 = 1 := by
      rcases blockCode_values (sample j) with h | h | h
      · exact (hj h).elim
      · rw [h]; norm_num
      · rw [h]; norm_num
    have hcount : 1 ≤ ∑ i, blockCode (sample i) ^ 2 := by
      rw [← hsq]
      exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (blockCode (sample i))) (Finset.mem_univ j)
    calc
      _ ≤ 2 * ‖f‖ := by simpa only [Real.dist_eq] using f.dist_le_two_norm _ 0
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hcount

/-- Finite-sample error bound, uniform over every possible jump amplitude. -/
theorem observable_error_bound (m N : ℕ) (a : ℝ) (f : Observable) :
    |(rowLaw m N).expectation (fun sample ↦ f (rowScore a sample)) - f 0| ≤
      2 * ‖f‖ * ((N : ℝ) * (1 / 2 : ℝ) ^ m) := by
  let p := rowLaw m N
  have hd : p.expectation (fun sample ↦ f (rowScore a sample)) - f 0 =
      ∑ sample, p.mass sample * (f (rowScore a sample) - f 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, p.mass_sum,
      one_mul, FiniteReportLaw.expectation]
  have hcount : p.expectation (fun sample ↦ ∑ j, blockCode (sample j) ^ 2) =
      (N : ℝ) * (1 / 2 : ℝ) ^ m := by
    dsimp only [p, rowLaw]
    rw [independent_sum_mean
      (fun _ : Fin N ↦ blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness))
      (fun _ x ↦ blockCode x ^ 2)]
    simp only [blockCode_second_moment, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  change |p.expectation _ - f 0| ≤ _
  rw [hd, ← hcount]
  calc
    _ ≤ ∑ sample, |p.mass sample * (f (rowScore a sample) - f 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ sample, p.mass sample * (2 * ‖f‖ * ∑ j, blockCode (sample j) ^ 2) := by
      apply Finset.sum_le_sum
      intro sample _
      rw [abs_mul, abs_of_nonneg (p.mass_nonneg sample)]
      exact mul_le_mul_of_nonneg_left (sample_observable_bound a f sample) (p.mass_nonneg _)
    _ = _ := by
      simp only [FiniteReportLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sample _
      ring_nf

/-- The jump size supplied by the original unit-variance standardization. -/
noncomputable def unitAmplitude (m N : ℕ) : ℝ := Real.sqrt 2 ^ m / Real.sqrt N

/-- The original HWE interaction statistic equals the normalized signed-block report. -/
theorem original_standardization (m N : ℕ)
    (sample : Fin N → Fin m → DiploidGenotype) :
    (∑ j, interaction (fun _ : Fin m ↦ HardyWeinbergModel.witness) (sample j)) /
      Real.sqrt N = rowScore (unitAmplitude m N) sample := by
  simp only [interaction_eq, Fintype.card_fin, rowScore, unitAmplitude,
    Finset.sum_div, div_mul_eq_mul_div]

private theorem expectation_scale {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (c : ℝ) (g : α → ℝ) : p.expectation (fun x ↦ c * g x) = c * p.expectation g := by
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Every positive-order normalized row is centered under the actual genotype law. -/
theorem normalized_mean (m N : ℕ) (hm : 0 < m) :
    (rowLaw m N).expectation (rowScore (unitAmplitude m N)) = 0 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  change (independentLaw (fun _ : Fin N ↦ blockLaw
    (fun _ : Fin m ↦ HardyWeinbergModel.witness))).expectation
    (fun sample ↦ ∑ j, unitAmplitude m N * blockCode (sample j)) = 0
  rw [independent_sum_mean
    (fun _ : Fin N ↦ blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness))
    (fun _ x ↦ unitAmplitude m N * blockCode x)]
  simp only [expectation_scale, blockCode_mean, mul_zero, Finset.sum_const_zero]

/-- The complete normalized row has exactly unit second moment at every positive size. -/
theorem normalized_second_moment (m N : ℕ) (hm : 0 < m) (hN : 0 < N) :
    (rowLaw m N).expectation (fun sample ↦ rowScore (unitAmplitude m N) sample ^ 2) = 1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have ha : unitAmplitude m N ^ 2 = (2 : ℝ) ^ m / N := by
    rw [unitAmplitude, div_pow, ← pow_mul, mul_comm m 2, pow_mul,
      Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg N)]
  change (independentLaw (fun _ : Fin N ↦ blockLaw
    (fun _ : Fin m ↦ HardyWeinbergModel.witness))).expectation
    (fun sample ↦ (∑ j, unitAmplitude m N * blockCode (sample j)) ^ 2) = 1
  rw [independent_sum_second
    (fun _ : Fin N ↦ blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness))
    (fun _ x ↦ unitAmplitude m N * blockCode x) (by
    intro j
    rw [expectation_scale, blockCode_mean, mul_zero])]
  simp only [mul_pow]
  simp_rw [expectation_scale, blockCode_second_moment]
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ha]
  have hn : (N : ℝ) ≠ 0 := by positivity
  calc
    _ = (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m := by field_simp
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The weak-zero phase needs no restriction on the size of a surviving jump. -/
theorem vanishing_observable_limit (N : ℕ → ℕ) (a : ℕ → ℝ)
    (hrare : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds 0))
    (f : Observable) :
    Tendsto (fun m ↦ (rowLaw m (N m)).expectation
      (fun sample ↦ f (rowScore (a m) sample))) atTop (nhds (f 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ ↦ abs_nonneg _)
    (fun m ↦ observable_error_bound m (N m) (a m) f)
  simpa only [mul_zero] using tendsto_const_nhds.mul hrare

/-- The real report distribution for arbitrary balanced row sizes and jump amplitudes. -/
noncomputable def rowProbability (m N : ℕ) (a : ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (rowLaw m N) (rowScore a), inferInstance⟩

/-- Actual weak convergence to the point mass at zero throughout the sparse phase. -/
theorem vanishing_weak_convergence (N : ℕ → ℕ) (a : ℕ → ℝ)
    (hrare : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds 0)) :
    Tendsto (fun m ↦ rowProbability m (N m) (a m)) atTop
      (nhds (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun m ↦ ∫ x, f x ∂finiteMeasure (rowLaw m (N m)) (rowScore (a m)))
    atTop (nhds (∫ x, f x ∂Measure.dirac 0))
  simp only [integral_finiteMeasure, integral_dirac]
  exact vanishing_observable_limit N a hrare f

end Descent.Portability.BalancedHWEVanishingLaw
