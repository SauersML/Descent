/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianHermiteLaw
import Mathlib.GroupTheory.Perm.Fin

assert_below Descent.Decision Descent.Program

/-!
The report's three-locus order-erasure direction. Its quadratic density
coefficient has zero Gaussian mean and exact squared Gaussian norm eighteen.
These integral identities do not by themselves establish a density remainder
or a relative-entropy asymptotic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ThreeLocusInformation

open MeasureTheory GaussianHermiteLaw GaussianCovarianceSeparation
open scoped BigOperators Matrix

def direction : Matrix (Fin 3) (Fin 3) ℝ := ![![0, 1, -2], ![1, 0, 1], ![-2, 1, 0]]

def degrees : Fin 6 → Fin 3 → Fin 3 :=
  ![![2, 2, 0], ![2, 0, 2], ![0, 2, 2], ![2, 1, 1], ![1, 2, 1], ![1, 1, 2]]

def coefficients : Fin 6 → ℝ := ![1, 1, 1, -1, -1, -1]

theorem degrees_injective : Function.Injective degrees := by decide

noncomputable def statistic (x : Fin 3 → ℝ) : ℝ := tensorCombination degrees coefficients x

theorem statistic_second_moment :
    (∫ x, statistic x ^ 2 ∂productGaussian (Fin 3)) = 18 := by
  simp only [statistic]
  rw [tensorCombination_squared_integral degrees degrees_injective]
  norm_num [degrees, coefficients, hermiteWeight, Fin.sum_univ_succ, Fin.prod_univ_succ,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]

theorem statistic_mean : (∫ x, statistic x ∂productGaussian (Fin 3)) = 0 := by
  have hi (i : Fin 6) : Integrable (tensorHermite (degrees i)) (productGaussian (Fin 3)) := by
    have hh := tensor_pair_integrable (degrees i) (fun _ ↦ 0)
    simpa [tensorHermite, hermite, hermitePolynomial] using hh
  have hz (i : Fin 6) : (∫ x, tensorHermite (degrees i) x ∂productGaussian (Fin 3)) = 0 := by
    have hh := tensor_inner (degrees i) (fun _ ↦ 0)
    have hn : degrees i ≠ fun _ ↦ 0 := by fin_cases i <;> decide
    simpa [tensorHermite, hermite, hermitePolynomial, hn] using hh
  unfold statistic tensorCombination
  rw [integral_finset_sum Finset.univ (fun i _ ↦ (hi i).const_mul (coefficients i))]
  simp only [integral_const_mul, hz, mul_zero, Finset.sum_const_zero]

def permuted (A : Matrix (Fin 3) (Fin 3) ℝ) (π : Equiv.Perm (Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦ A (π i) (π j)

noncomputable def densitySecondCoefficient (x : Fin 3 → ℝ) : ℝ :=
  (1 / 6 : ℝ) * ∑ π : Equiv.Perm (Fin 3),
    (Matrix.trace (direction * direction) / 4 -
      quadraticValue (permuted (direction * direction) π) x / 2 +
      quadraticValue (permuted direction π) x ^ 2 / 8)

theorem permutations_three (f : Equiv.Perm (Fin 3) → ℝ) :
    (∑ π, f π) = f 1 + f (Equiv.swap 0 1) + f (Equiv.swap 0 2) + f (Equiv.swap 1 2) +
      f (Equiv.swap 0 1 * Equiv.swap 1 2) + f (Equiv.swap 1 2 * Equiv.swap 0 1) := by
  have henum : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  rw [henum]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem direction_square : direction * direction = ![![5, -2, 1], ![-2, 2, -2], ![1, -2, 5]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [direction, Matrix.mul_apply, Fin.sum_univ_succ]

theorem direction_trace_square : Matrix.trace (direction * direction) = 12 := by
  norm_num [direction, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

theorem direction_symmetric (i j : Fin 3) : direction i j = direction j i := by
  fin_cases i <;> fin_cases j <;> norm_num [direction]

theorem direction_nonzero : direction ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A 0 1) h
  norm_num [direction] at hh

theorem direction_permutation_average (i j : Fin 3) :
    (1 / 6 : ℝ) * ∑ π : Equiv.Perm (Fin 3), permuted direction π i j = 0 := by
  rw [permutations_three]
  have htwo : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [direction, permuted, Equiv.swap_apply_def, Equiv.Perm.mul_apply, htwo,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

set_option maxHeartbeats 1600000 in
theorem densitySecondCoefficient_eq_statistic (x : Fin 3 → ℝ) :
    densitySecondCoefficient x = statistic x := by
  unfold densitySecondCoefficient
  rw [direction_square, permutations_three]
  norm_num [direction, Matrix.trace, Matrix.diag, Matrix.mul_apply, quadraticValue, permuted,
    statistic, tensorCombination, tensorHermite, hermite, hermitePolynomial,
    degrees, coefficients, Fin.sum_univ_succ, Fin.prod_univ_succ, Equiv.swap_apply_def,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Equiv.Perm.mul_apply, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
  ring

theorem density_coefficient_mean :
    (∫ x, densitySecondCoefficient x ∂productGaussian (Fin 3)) = 0 := by
  simpa only [densitySecondCoefficient_eq_statistic] using statistic_mean

theorem density_coefficient_second_moment :
    (∫ x, densitySecondCoefficient x ^ 2 ∂productGaussian (Fin 3)) = 18 := by
  simpa only [densitySecondCoefficient_eq_statistic] using statistic_second_moment

end Descent.Portability.ThreeLocusInformation
