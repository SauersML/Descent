/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEInteractionLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

assert_below Descent.Decision Descent.Program

/-!
Finite report laws as genuine probability measures on their original sample
spaces. Product experiments retain the exact product measure and independence,
and arbitrary real observables retain their original finite expectations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteDiscreteMeasure

open scoped BigOperators
open MeasureTheory ProbabilityTheory HWEInteractionLaw

variable {α : Type*} [Fintype α] [MeasurableSpace α]

noncomputable def measure (p : FiniteReportLaw α) : Measure α :=
  Measure.sum (fun a ↦ ENNReal.ofReal (p.mass a) • Measure.dirac a)

instance measure_probability (p : FiniteReportLaw α) : IsProbabilityMeasure (measure p) := by
  constructor
  simp only [measure, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ p.mass_nonneg a), p.mass_sum]
  exact ENNReal.ofReal_one

variable [MeasurableSingletonClass α]

theorem measure_singleton (p : FiniteReportLaw α) (a : α) :
    measure p {a} = ENNReal.ofReal (p.mass a) := by
  classical
  simp [measure, Set.indicator_apply]

/-- Every real observable of this finite sample space is integrable. -/
theorem observable_integrable (p : FiniteReportLaw α) (f : α → ℝ) :
    Integrable f (measure p) := by
  classical
  rw [measure, Measure.sum_fintype]
  apply integrable_finset_sum_measure.mpr
  intro a _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_observable (p : FiniteReportLaw α) (f : α → ℝ) :
    ∫ a, f a ∂measure p = p.expectation f := by
  rw [measure, integral_sum_measure (observable_integrable p f)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (p.mass_nonneg _), smul_eq_mul,
    tsum_fintype, FiniteReportLaw.expectation]

/-- Event probabilities are the finite experiment's indicator expectations. -/
theorem real_event (p : FiniteReportLaw α) (s : Set α) :
    (measure p).real s = p.expectation (s.indicator (fun _ ↦ 1)) := by
  rw [← integral_observable, integral_indicator (Set.toFinite s).measurableSet]
  simp

/-- The independent finite experiment is exactly the product of its coordinate measures. -/
theorem independent_measure {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → FiniteReportLaw α) :
    measure (independentLaw p) = Measure.pi (fun i ↦ measure (p i)) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [measure_singleton, ← Set.univ_pi_singleton x, Measure.pi_pi]
  simp only [measure_singleton, independentLaw]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (p i).mass_nonneg (x i))

/-- Independence needed by concentration theorems is derived from the actual finite sample law. -/
theorem independent_observables {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → FiniteReportLaw α) (f : I → α → ℝ) :
    iIndepFun (fun i x ↦ f i (x i)) (measure (independentLaw p)) := by
  rw [independent_measure]
  exact iIndepFun_pi (fun i ↦ (measurable_of_finite (f i)).aemeasurable)

end Descent.Portability.FiniteDiscreteMeasure
