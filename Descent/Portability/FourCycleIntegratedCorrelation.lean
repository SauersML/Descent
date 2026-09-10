/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FourCyclePrediction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

assert_below Descent.Decision Descent.Program

/-!
The actual one-sided integrated correlations of the two four-cycle experiments
are one half and one. Absolute integrability follows from the complex exponential
with negative real part. These integrals are not finite-horizon prediction risks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory

namespace Descent.Portability.FourCycleIntegratedCorrelation

open FourCyclePrediction FiniteHorizonLoss

private theorem decay_real_part (time : ℝ) :
    (Complex.exp (((-1 : ℂ) + Complex.I) * time)).re = cosineDecay time := by
  simp [Complex.exp_re, cosineDecay]

theorem cosineDecay_integrable : IntegrableOn cosineDecay (Set.Ioi 0) := by
  have h := (integrableOn_exp_mul_complex_Ioi
    (a := (-1 : ℂ) + Complex.I) (by norm_num) 0).re
  change IntegrableOn (fun time : ℝ ↦
    (Complex.exp (((-1 : ℂ) + Complex.I) * time)).re) (Set.Ioi 0) at h
  simpa only [decay_real_part] using h

theorem cosineDecay_integral : (∫ time in Set.Ioi (0 : ℝ), cosineDecay time) = 1 / 2 := by
  have hi := integrableOn_exp_mul_complex_Ioi
    (a := (-1 : ℂ) + Complex.I) (by norm_num) 0
  have h := integral_exp_mul_complex_Ioi (a := (-1 : ℂ) + Complex.I) (by norm_num) 0
  have hre := congrArg Complex.re h
  have hreal := integral_re hi
  change (∫ time in Set.Ioi (0 : ℝ),
    (Complex.exp (((-1 : ℂ) + Complex.I) * time)).re) =
      (∫ time in Set.Ioi (0 : ℝ), Complex.exp (((-1 : ℂ) + Complex.I) * time)).re at hreal
  rw [← hreal] at hre
  simp only [decay_real_part] at hre
  convert hre using 1
  norm_num [Complex.div_re, Complex.normSq]

/-- The directed chain's integrated stationary correlation is exactly one half. -/
theorem directed_integrated_correlation :
    (∫ time in Set.Ioi (0 : ℝ), FiniteHorizonLoss.inner uniform report
      (predict (directedLaw time) report)) = 1 / 2 := by
  apply Eq.trans _ cosineDecay_integral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time htime
  exact directed_correlation time (le_of_lt htime)

/-- The reversible chain's integrated stationary correlation is exactly one. -/
theorem reversible_integrated_correlation :
    (∫ time in Set.Ioi (0 : ℝ), FiniteHorizonLoss.inner uniform report
      (predict (reversibleLaw time) report)) = 1 := by
  apply Eq.trans _ integral_exp_neg_Ioi_zero
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time htime
  exact reversible_correlation time (le_of_lt htime)

end Descent.Portability.FourCycleIntegratedCorrelation
