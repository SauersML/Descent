/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Poisson
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Descent.Layer

assert_below Descent.Decision Descent.Program

/-!
The actual Poisson count law on the real line, including zero intensity, and its
characteristic function derived from the normalized Poisson probability series.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PoissonRealCharacteristic

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory BoundedContinuousFunction

noncomputable def poissonReal (r : ℝ≥0) : Measure ℝ :=
  Measure.sum (fun k : ℕ ↦ ENNReal.ofReal (poissonPMFReal r k) • Measure.dirac (k : ℝ))

instance poissonReal_probability (r : ℝ≥0) : IsProbabilityMeasure (poissonReal r) := by
  constructor
  simp only [poissonReal, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ poissonPMFReal_nonneg)
    (poissonPMFRealSum r).summable, (poissonPMFRealSum r).tsum_eq]
  exact ENNReal.ofReal_one

noncomputable def poissonProbability (r : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨poissonReal r, inferInstance⟩

/-- The normalized Poisson generating series evaluated on the unit circle. -/
theorem poisson_series (r : ℝ≥0) (t : ℝ) :
    HasSum (fun k : ℕ ↦ (poissonPMFReal r k : ℂ) *
      Complex.exp ((t : ℂ) * (k : ℂ) * Complex.I))
      (Complex.exp ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1))) := by
  have hs : HasSum (fun k : ℕ ↦ ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ^ k /
      (k.factorial : ℂ)) (Complex.exp ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp ℂ _
  have hw := hs.mul_left (Complex.exp (-(r : ℂ)))
  convert hw using 1
  · funext k
    have he : (t : ℂ) * (k : ℂ) * Complex.I = (k : ℂ) * ((t : ℂ) * Complex.I) := by ring
    rw [he, Complex.exp_nat_mul]
    simp only [poissonPMFReal]
    push_cast
    rw [mul_pow]
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

/-- Characteristic function of the actual atomic Poisson probability measure. -/
theorem charFun_poisson (r : ℝ≥0) (t : ℝ) :
    charFun (poissonReal r) t =
      Complex.exp ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  have hf := (innerProbChar t).integrable (poissonReal r)
  rw [charFun_eq_integral_innerProbChar, poissonReal, integral_sum_measure hf]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal poissonPMFReal_nonneg, Complex.real_smul]
  convert (poisson_series r t).tsum_eq using 1
  congr 1
  funext k
  simp only [innerProbChar_apply, RCLike.inner_apply, Complex.ofReal_mul]
  congr 2

end Descent.Portability.PoissonRealCharacteristic
