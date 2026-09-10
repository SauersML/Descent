/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEWeakLimit
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

assert_below Descent.Decision Descent.Program

/-!
Every observable on a finite real report distribution is integrable, including
unbounded moment tests. Its measure integral and characteristic function agree
exactly with the original finite experiment sums.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAtomicReportMeasure

open scoped BigOperators
open MeasureTheory HWEInteractionLaw BalancedHWEWeakLimit

/-- Every observable is integrable for an actual finite atomic report distribution. -/
theorem finite_report_integrable {α E : Type*} [Fintype α] [NormedAddCommGroup E]
    (p : FiniteReportLaw α) (g : α → ℝ) (f : ℝ → E) :
    Integrable f (finiteMeasure p g) := by
  classical
  rw [finiteMeasure, Measure.sum_fintype]
  apply integrable_finset_sum_measure.mpr
  intro a _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Unbounded real test functions retain the exact finite-expectation formula. -/
theorem integral_finite_report {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (g : α → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂finiteMeasure p g = p.expectation (fun a ↦ f (g a)) := by
  have hf := finite_report_integrable p g f
  rw [finiteMeasure, integral_sum_measure hf]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (p.mass_nonneg _), smul_eq_mul,
    tsum_fintype, FiniteReportLaw.expectation]

/-- The characteristic function is exactly the finite experiment's complex exponential average. -/
theorem charFun_finite_report {α : Type*} [Fintype α]
    (p : FiniteReportLaw α) (g : α → ℝ) (t : ℝ) :
    charFun (finiteMeasure p g) t =
      complexExpectation p (fun a ↦ Complex.exp ((t * g a : ℝ) * Complex.I)) := by
  have hf := finite_report_integrable p g (fun x ↦ Complex.exp ((t * x : ℝ) * Complex.I))
  rw [charFun_apply_real]
  simp only [← Complex.ofReal_mul]
  rw [finiteMeasure, integral_sum_measure hf]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (p.mass_nonneg _), Complex.real_smul,
    tsum_fintype, complexExpectation]

end Descent.Portability.FiniteAtomicReportMeasure
