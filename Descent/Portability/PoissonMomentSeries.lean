/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompoundPoissonMarkLaw

assert_below Descent.Decision Descent.Program

/-!
Exact Poisson first and second factorial moment series, including zero intensity.
The formulas follow from the actual normalized probabilities and a one-step
factorial recurrence. They supply summability for compound-Poisson fourth moments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PoissonMomentSeries

open scoped BigOperators NNReal
open ProbabilityTheory

/-- The count-weighted Poisson probability shifts by exactly one index. -/
theorem poisson_count_recurrence (r : ℝ≥0) (k : ℕ) :
    poissonPMFReal r (k + 1) * ((k + 1 : ℕ) : ℝ) = (r : ℝ) * poissonPMFReal r k := by
  simp only [poissonPMFReal, Nat.factorial_succ, pow_succ, Nat.cast_mul]
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
  field_simp

/-- Actual first Poisson moment as a convergent series. -/
theorem poisson_first (r : ℝ≥0) :
    HasSum (fun k : ℕ ↦ poissonPMFReal r k * (k : ℝ)) (r : ℝ) := by
  have ht : HasSum (fun k : ℕ ↦ poissonPMFReal r (k + 1) * ((k + 1 : ℕ) : ℝ))
      (r : ℝ) := by
    simpa only [poisson_count_recurrence, mul_one] using (poissonPMFRealSum r).mul_left (r : ℝ)
  have hh := (hasSum_nat_add_iff
    (f := fun k : ℕ ↦ poissonPMFReal r k * (k : ℝ)) 1).mp ht
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero] using hh

/-- Actual second factorial Poisson moment as a convergent series. -/
theorem poisson_second_factorial (r : ℝ≥0) :
    HasSum (fun k : ℕ ↦ poissonPMFReal r k * (k : ℝ) * ((k : ℝ) - 1)) ((r : ℝ) ^ 2) := by
  have he (k : ℕ) : poissonPMFReal r (k + 1) * ((k + 1 : ℕ) : ℝ) *
      (((k + 1 : ℕ) : ℝ) - 1) = (r : ℝ) * (poissonPMFReal r k * (k : ℝ)) := by
    rw [poisson_count_recurrence]
    push_cast
    ring
  have ht : HasSum (fun k : ℕ ↦ poissonPMFReal r (k + 1) * ((k + 1 : ℕ) : ℝ) *
      (((k + 1 : ℕ) : ℝ) - 1)) ((r : ℝ) ^ 2) := by
    simpa only [he, pow_two] using (poisson_first r).mul_left (r : ℝ)
  have hh := (hasSum_nat_add_iff
    (f := fun k : ℕ ↦ poissonPMFReal r k * (k : ℝ) * ((k : ℝ) - 1)) 1).mp ht
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, add_zero] using hh

/-- Every required linear combination of these factorial moments is summable exactly. -/
theorem poisson_quadratic (r : ℝ≥0) (a b : ℝ) :
    HasSum (fun k : ℕ ↦ poissonPMFReal r k *
      (a * (k : ℝ) + b * (k : ℝ) * ((k : ℝ) - 1)))
      (a * (r : ℝ) + b * (r : ℝ) ^ 2) := by
  have hh := ((poisson_first r).mul_left a).add ((poisson_second_factorial r).mul_left b)
  convert hh using 1
  funext k
  ring

end Descent.Portability.PoissonMomentSeries
