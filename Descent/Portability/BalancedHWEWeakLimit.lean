/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEOperatorLimit
import Mathlib.Probability.Distributions.Poisson
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

assert_below Descent.Decision Descent.Program

/-!
An actual compound-Poisson probability measure is constructed by drawing a
Poisson(1) number of independent fair unit signs. Its bounded-observable
integrals are identified with the operator limit of the actual critical HWE
experiment, yielding weak convergence of probability measures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEWeakLimit

open scoped BigOperators BoundedContinuousFunction Topology ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory
open HWEInteractionLaw BalancedHWEInteraction IndependentShiftOperator BalancedHWEOperatorLimit

noncomputable local instance : NormedRing Operator := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing Operator :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- The probability measure of a real report from a finite experiment. -/
noncomputable def finiteMeasure {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (g : α → ℝ) : Measure ℝ :=
  Measure.sum (fun a ↦ ENNReal.ofReal (p.mass a) • Measure.dirac (g a))

instance finiteMeasure_probability {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (g : α → ℝ) : IsProbabilityMeasure (finiteMeasure p g) := by
  constructor
  simp only [finiteMeasure, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ p.mass_nonneg a), p.mass_sum]
  exact ENNReal.ofReal_one

/-- The measure-theoretic integral agrees exactly with the finite report expectation. -/
theorem integral_finiteMeasure {α : Type*} [Fintype α] (p : FiniteReportLaw α)
    (g : α → ℝ) (f : Observable) :
    ∫ x, f x ∂finiteMeasure p g = p.expectation (fun a ↦ f (g a)) := by
  have hf := f.integrable (finiteMeasure p g)
  rw [finiteMeasure, integral_sum_measure hf]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (p.mass_nonneg _),
    smul_eq_mul, tsum_fintype, FiniteReportLaw.expectation]

/-- A fair sign law, with no genotype approximation involved. -/
noncomputable def signLaw : FiniteReportLaw Bool where
  mass _ := 1 / 2
  mass_nonneg _ := by norm_num
  mass_sum := by norm_num

def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- A fixed number of independent fair signs, as a real probability measure. -/
noncomputable def walkMeasure (k : ℕ) : Measure ℝ :=
  finiteMeasure (independentLaw (fun _ : Fin k ↦ signLaw))
    (fun signs ↦ ∑ i, signValue (signs i))

instance walkMeasure_probability (k : ℕ) : IsProbabilityMeasure (walkMeasure k) := by
  dsimp only [walkMeasure]
  infer_instance

theorem sign_shift_eq_jump : shift signLaw signValue = jump := by
  ext f x
  rw [shift_apply, jump_apply]
  simp [FiniteReportLaw.expectation, signLaw, signValue, sub_eq_add_neg]
  ring

theorem integral_walkMeasure (k : ℕ) (f : Observable) :
    ∫ x, f x ∂walkMeasure k = (jump ^ k) f 0 := by
  rw [walkMeasure, integral_finiteMeasure, ← sign_shift_eq_jump, shift_pow_sample]
  simp only [zero_add]

/-- Compound Poisson with unit rate and fair unit marks. This is a normalized
probability measure, not a formal characteristic exponent. -/
noncomputable def compoundPoisson : Measure ℝ :=
  Measure.sum (fun k : ℕ ↦ ENNReal.ofReal (poissonPMFReal 1 k) • walkMeasure k)

instance compoundPoisson_probability : IsProbabilityMeasure compoundPoisson := by
  constructor
  simp only [compoundPoisson, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ poissonPMFReal_nonneg)
    (poissonPMFRealSum 1).summable, (poissonPMFRealSum 1).tsum_eq]
  exact ENNReal.ofReal_one

/-- The actual compound-Poisson integral is the same normalized series as the operator limit. -/
theorem integral_compoundPoisson (f : Observable) :
    ∫ x, f x ∂compoundPoisson = (NormedSpace.exp ℝ (jump - 1)) f 0 := by
  have hf := f.integrable compoundPoisson
  rw [compoundPoisson, integral_sum_measure hf, limiting_poisson_series]
  apply tsum_congr
  intro k
  rw [integral_smul_measure, integral_walkMeasure, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  simp only [poissonPMFReal, NNReal.coe_one, one_pow, mul_one, smul_eq_mul]

/-- Probability measures of the original critical HWE genotype reports. -/
noncomputable def criticalProbability (m : ℕ) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (rowLaw m (2 ^ m)) (rowScore 1), inferInstance⟩

noncomputable def compoundPoissonProbability : ProbabilityMeasure ℝ :=
  ⟨compoundPoisson, inferInstance⟩

/-- The actual balanced HWE disjoint array converges weakly to a nondegenerate
compound-Poisson probability law at N=2^m. No Gaussian or Lévy theorem is assumed. -/
theorem critical_weak_convergence :
    Tendsto criticalProbability atTop (nhds compoundPoissonProbability) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun m ↦ ∫ x, f x ∂finiteMeasure (rowLaw m (2 ^ m)) (rowScore 1))
    atTop (nhds (∫ x, f x ∂compoundPoisson))
  simp only [integral_finiteMeasure, integral_compoundPoisson]
  exact critical_bounded_observable_limit f

end Descent.Portability.BalancedHWEWeakLimit
