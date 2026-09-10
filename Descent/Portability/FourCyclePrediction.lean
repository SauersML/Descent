/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StationaryPoissonLaw
import Descent.Portability.ContinuousMemoryLaw
import Descent.Portability.FiniteProductExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

assert_below Descent.Decision Descent.Program

/-!
A concrete four-state counterexample to identifying stale-score loss with optimal
transported-predictor risk. Both generator exponentials are derived from their
linear differential equations, rather than assigning a correlation curve.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Matrix.Norms.Operator

namespace Descent.Portability.FourCyclePrediction

open MatrixOperatorBridge ControlledCoarseGraining ContinuousMemoryLaw
open FiniteHorizonLoss MarkovCoarseGraining MarkovPoissonLaw StationaryPoissonLaw
open InterleavedMutationExponential

noncomputable def directed : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 1, 0, 0; 0, -1, 1, 0; 0, 0, -1, 1; 1, 0, 0, -1]

noncomputable def reversible : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 1 / 2, 0, 1 / 2; 1 / 2, -1, 1 / 2, 0;
    0, 1 / 2, -1, 1 / 2; 1 / 2, 0, 1 / 2, -1]

noncomputable def cosineDecay (time : ℝ) : ℝ := Real.exp (-time) * Real.cos time
noncomputable def sineDecay (time : ℝ) : ℝ := Real.exp (-time) * Real.sin time

noncomputable def directedOrbit (time : ℝ) : Fin 4 → ℝ :=
  ![cosineDecay time, -sineDecay time, -cosineDecay time, sineDecay time]

noncomputable def reversibleOrbit (time : ℝ) : Fin 4 → ℝ :=
  ![Real.exp (-time), 0, -Real.exp (-time), 0]

noncomputable def mode : Fin 4 → ℝ := ![1, 0, -1, 0]

theorem cosineDecay_derivative (time : ℝ) :
    HasDerivAt cosineDecay (-cosineDecay time - sineDecay time) time := by
  have h := (((hasDerivAt_neg time).exp).mul (Real.hasDerivAt_cos time))
  convert h using 1
  simp [cosineDecay, sineDecay]
  ring

theorem sineDecay_derivative (time : ℝ) :
    HasDerivAt sineDecay (cosineDecay time - sineDecay time) time := by
  have h := (((hasDerivAt_neg time).exp).mul (Real.hasDerivAt_sin time))
  convert h using 1
  simp [cosineDecay, sineDecay]
  ring

theorem directedOrbit_derivative (time : ℝ) :
    HasDerivAt directedOrbit (directed *ᵥ directedOrbit time) time := by
  apply hasDerivAt_pi.mpr
  intro state
  fin_cases state
  · simpa [directedOrbit, directed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
      cosineDecay_derivative time
  · simpa [directedOrbit, directed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, add_comm] using (sineDecay_derivative time).neg
  · simpa [directedOrbit, directed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, add_comm] using (cosineDecay_derivative time).neg
  · simpa [directedOrbit, directed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg] using sineDecay_derivative time

theorem reversibleOrbit_derivative (time : ℝ) :
    HasDerivAt reversibleOrbit (reversible *ᵥ reversibleOrbit time) time := by
  apply hasDerivAt_pi.mpr
  intro state
  fin_cases state
  · simpa [reversibleOrbit, reversible, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
      (hasDerivAt_neg time).exp
  · convert hasDerivAt_const time (0 : ℝ) using 1
    simp [reversibleOrbit, reversible, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simpa [reversibleOrbit, reversible, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
      ((hasDerivAt_neg time).exp).neg
  · convert hasDerivAt_const time (0 : ℝ) using 1
    simp [reversibleOrbit, reversible, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem orbit_eq_exp (generator : Matrix (Fin 4) (Fin 4) ℝ)
    (orbit : ℝ → Fin 4 → ℝ) (hderiv : ∀ time, HasDerivAt orbit (generator *ᵥ orbit time) time)
    (time : ℝ) : orbit time = NormedSpace.exp ℝ (time • generator) *ᵥ orbit 0 := by
  have hd (moment : ℝ) : HasDerivAt orbit
      ((0 : ℝ →L[ℝ] (Fin 4 → ℝ)) 0 + operator generator (orbit moment)) moment := by
    simpa using hderiv moment
  have h := hidden_expansion (0 : ℝ →L[ℝ] (Fin 4 → ℝ)) (operator generator)
    (fun _ ↦ 0) orbit continuous_const hd time
  simpa [hiddenIntegrand, evolution, ← operator_exp, ← operator_smul] using h

theorem directed_exponential_mode (time : ℝ) :
    NormedSpace.exp ℝ (time • directed) *ᵥ mode = directedOrbit time := by
  have h := orbit_eq_exp directed directedOrbit directedOrbit_derivative time
  simpa [directedOrbit, cosineDecay, sineDecay, mode] using h.symm

theorem reversible_exponential_mode (time : ℝ) :
    NormedSpace.exp ℝ (time • reversible) *ᵥ mode = reversibleOrbit time := by
  have h := orbit_eq_exp reversible reversibleOrbit reversibleOrbit_derivative time
  simpa [reversibleOrbit, mode] using h.symm

noncomputable def uniform : FiniteReportLaw (Fin 4) where
  mass _ := 1 / 4
  mass_nonneg _ := by norm_num
  mass_sum := by norm_num

noncomputable def directedKernel (source : Fin 4) : FiniteReportLaw (Fin 4) where
  mass target := (directed + 1) source target
  mass_nonneg target := by
    fin_cases source <;> fin_cases target <;> norm_num [directed, Matrix.one_apply]
  mass_sum := by
    fin_cases source <;> norm_num [directed, Matrix.one_apply, Fin.sum_univ_four]

noncomputable def reversibleKernel (source : Fin 4) : FiniteReportLaw (Fin 4) where
  mass target := (reversible + 1) source target
  mass_nonneg target := by
    fin_cases source <;> fin_cases target <;> norm_num [reversible, Matrix.one_apply]
  mass_sum := by
    fin_cases source <;> norm_num [reversible, Matrix.one_apply, Fin.sum_univ_four]

theorem directed_stationary : Stationary uniform directedKernel := by
  intro target
  fin_cases target <;>
    norm_num [uniform, directedKernel, directed, Matrix.one_apply, Fin.sum_univ_four]

theorem reversible_stationary : Stationary uniform reversibleKernel := by
  intro target
  fin_cases target <;>
    norm_num [uniform, reversibleKernel, reversible, Matrix.one_apply, Fin.sum_univ_four]

noncomputable def directedLaw (time : ℝ) : Fin 4 → FiniteReportLaw (Fin 4) :=
  stateLaw directedKernel 1 time

noncomputable def reversibleLaw (time : ℝ) : Fin 4 → FiniteReportLaw (Fin 4) :=
  stateLaw reversibleKernel 1 time

theorem directedLaw_stationary (time : ℝ) : Stationary uniform (directedLaw time) :=
  stationary_stateLaw uniform directedKernel directed_stationary 1 time

theorem reversibleLaw_stationary (time : ℝ) : Stationary uniform (reversibleLaw time) :=
  stationary_stateLaw uniform reversibleKernel reversible_stationary 1 time

theorem directedLaw_matrix (time : ℝ) (htime : 0 ≤ time) :
    kernelMatrix (directedLaw time) = NormedSpace.exp ℝ (time • directed) := by
  have h := stateLaw_matrix directedKernel 1 time htime
  have hgenerator : generator directedKernel 1 = directed := by
    change (1 : ℝ) • ((directed + 1) - 1) = directed
    simp
  simpa only [directedLaw, hgenerator] using h

theorem reversibleLaw_matrix (time : ℝ) (htime : 0 ≤ time) :
    kernelMatrix (reversibleLaw time) = NormedSpace.exp ℝ (time • reversible) := by
  have h := stateLaw_matrix reversibleKernel 1 time htime
  have hgenerator : generator reversibleKernel 1 = reversible := by
    change (1 : ℝ) • ((reversible + 1) - 1) = reversible
    simp
  simpa only [reversibleLaw, hgenerator] using h

noncomputable def report : Fin 4 → ℝ := Real.sqrt 2 • mode

theorem report_energy : energy uniform report = 1 := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [energy, FiniteHorizonLoss.inner, uniform, report, mode, Fin.sum_univ_succ]
  nlinarith

theorem directed_prediction (time : ℝ) (htime : 0 ≤ time) :
    predict (directedLaw time) report = Real.sqrt 2 • directedOrbit time := by
  change kernelMatrix (directedLaw time) *ᵥ (Real.sqrt 2 • mode) = _
  rw [directedLaw_matrix time htime, Matrix.mulVec_smul, directed_exponential_mode]

theorem reversible_prediction (time : ℝ) (htime : 0 ≤ time) :
    predict (reversibleLaw time) report = Real.sqrt 2 • reversibleOrbit time := by
  change kernelMatrix (reversibleLaw time) *ᵥ (Real.sqrt 2 • mode) = _
  rw [reversibleLaw_matrix time htime, Matrix.mulVec_smul, reversible_exponential_mode]

theorem directed_correlation (time : ℝ) (htime : 0 ≤ time) :
    inner uniform report (predict (directedLaw time) report) =
      Real.exp (-time) * Real.cos time := by
  rw [directed_prediction time htime]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [FiniteHorizonLoss.inner, uniform, report, mode, directedOrbit, Fin.sum_univ_succ, cosineDecay]
  ring_nf
  rw [hsqrt]
  ring

theorem reversible_correlation (time : ℝ) (htime : 0 ≤ time) :
    inner uniform report (predict (reversibleLaw time) report) = Real.exp (-time) := by
  rw [reversible_prediction time htime]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [FiniteHorizonLoss.inner, uniform, report, mode, reversibleOrbit, Fin.sum_univ_succ]
  ring_nf
  rw [hsqrt]
  ring

theorem directed_prediction_energy (time : ℝ) (htime : 0 ≤ time) :
    energy uniform (predict (directedLaw time) report) = Real.exp (-2 * time) := by
  rw [directed_prediction time htime]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htrig := Real.sin_sq_add_cos_sq time
  have hexp : Real.exp (-2 * time) = Real.exp (-time) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  simp [energy, FiniteHorizonLoss.inner, uniform, directedOrbit,
    cosineDecay, sineDecay, Fin.sum_univ_four]
  ring_nf
  rw [hsqrt]
  nlinarith [sq_nonneg (Real.exp (-time))]

theorem reversible_prediction_energy (time : ℝ) (htime : 0 ≤ time) :
    energy uniform (predict (reversibleLaw time) report) = Real.exp (-2 * time) := by
  rw [reversible_prediction time htime]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hexp : Real.exp (-2 * time) = Real.exp (-time) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  simp [energy, FiniteHorizonLoss.inner, uniform, reversibleOrbit, Fin.sum_univ_four]
  ring_nf
  rw [hsqrt]
  ring

/-- The directed cycle's frozen score rotates out of phase. -/
theorem directed_stale_risk (time : ℝ) (htime : 0 ≤ time) :
    risk uniform (directedLaw time) report report =
      2 - 2 * (Real.exp (-time) * Real.cos time) := by
  rw [stale_loss uniform _ (directedLaw_stationary time), report_energy,
    directed_correlation time htime]
  ring

/-- The reversible chain has the same instantaneous damping but no rotating phase. -/
theorem reversible_stale_risk (time : ℝ) (htime : 0 ≤ time) :
    risk uniform (reversibleLaw time) report report = 2 - 2 * Real.exp (-time) := by
  rw [stale_loss uniform _ (reversibleLaw_stationary time), report_energy,
    reversible_correlation time htime]
  ring

/-- Optimal transport removes the phase difference: both exact risks coincide. -/
theorem optimal_risks_equal (time : ℝ) (htime : 0 ≤ time) :
    risk uniform (directedLaw time) report (predict (directedLaw time) report) =
        1 - Real.exp (-2 * time) ∧
      risk uniform (reversibleLaw time) report (predict (reversibleLaw time) report) =
        1 - Real.exp (-2 * time) := by
  constructor
  · rw [optimal_prediction_risk uniform _ (directedLaw_stationary time), report_energy,
      directed_prediction_energy time htime]
  · rw [optimal_prediction_risk uniform _ (reversibleLaw_stationary time), report_energy,
      reversible_prediction_energy time htime]

/-- At half pi, the directed frozen score is strictly worse, despite equal optimal risk. -/
theorem stale_risks_differ_at_half_pi :
    risk uniform (directedLaw (Real.pi / 2)) report report = 2 ∧
      risk uniform (reversibleLaw (Real.pi / 2)) report report < 2 := by
  have ht : 0 ≤ Real.pi / 2 := le_of_lt (div_pos Real.pi_pos (by norm_num))
  rw [directed_stale_risk _ ht, reversible_stale_risk _ ht, Real.cos_pi_div_two]
  constructor
  · ring
  · linarith [Real.exp_pos (-(Real.pi / 2))]

end Descent.Portability.FourCyclePrediction
