/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

assert_below Descent.Decision Descent.Program

/-!
# The one-deme stationary low-order system

This module formalises the linear algebra of NOTE1 §3: the affine system (14) whose unique
solution is the recurrent-biallelic one-deme stationary low-order vector, its determinant
identity (15), and the identification of the corpus closed form (16) with the solution of
that system.

`stationaryMatrix c theta rho` is the four-by-four matrix `B` of NOTE1 (14) in the
coordinate order `(H, DD, Dz, pi2)`, and `stationaryForcing theta` is the vector `b` of the
same equation. `det_stationaryMatrix` is NOTE1 (15): the determinant is exactly
`(c + 2 theta)` times the corpus polynomial `oneDemeLDStationaryDenominator`, with no sign
correction; since that polynomial is strictly positive on the physical rate domain and
coalescence is strictly positive, the determinant is strictly positive and the system has a
unique solution.

`oneDemeStationaryVector` reads the corpus closed form `oneDemeStationaryLowOrderLDState` in
the same coordinate order. `oneDemeStationaryVector_solves` shows it satisfies `B w + b = 0`,
derived from the corpus theorem `oneDemeStationaryLowOrderLDState_equations` rather than
reproved, and `oneDemeStationaryVector_eq_neg_inv_mulVec` turns that into the closed
inversion `w = -B⁻¹ b` of NOTE1 (16). Together these say the corpus stationary state is not a
fitted table but the unique solution of an explicitly invertible linear system.

What is NOT proved in this module: the Cesàro argument of NOTE1 Theorem 3, which needs the
time average of a bounded orbit of the affine flow, and therefore the realizability of the
stationary vector. That argument depends on a microscopic approximation for the augmented
one-deme generator and on the closedness of the one-deme realization body, neither of which
is available here; the linear algebra above is the part that stands on its own.

## Empirical status

None. The bodies here are algebra: a four-by-four determinant expanded by cofactors, and the
solution of a linear system whose coefficients are the rate parameters. No measurement on any
population bears on a determinant identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.StationaryRealization

open Descent.Coalescent

noncomputable section

/-- The matrix `B` of NOTE1 (14), in the coordinate order `(H, DD, Dz, pi2)`: the
homogeneous part of the one-deme recurrent-biallelic low-order system at coalescence rate
`c`, scaled mutation `theta` and recombination `rho`. -/
def stationaryMatrix (c theta rho : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-(c + 2 * theta), 0, 0, 0;
     0, -(3 * c + rho + 4 * theta), c, c;
     0, 4 * c, -(5 * c + rho / 2 + 4 * theta), 0;
     theta / 2, 0, c, -(2 * c + 4 * theta)]

/-- The affine forcing vector `b` of NOTE1 (14): mutation influx into the heterozygosity
coordinate and nothing else. -/
def stationaryForcing (theta : ℝ) : Fin 4 → ℝ := ![theta, 0, 0, 0]

/-- The matrix of NOTE1 (14) at the rates of a one-deme rate law. -/
def oneDemeStationaryMatrix (rates : ManyDemeLDRates 1) : Matrix (Fin 4) (Fin 4) ℝ :=
  stationaryMatrix (rates.coalescence 0) (rates.mutation 0) (rates.recombination 0)

/-- **NOTE1 (15).** The determinant of the one-deme system matrix is exactly
`(c + 2 theta)` times the corpus stationary denominator, with no sign correction. -/
theorem det_stationaryMatrix (rates : ManyDemeLDRates 1) :
    (oneDemeStationaryMatrix rates).det
      = (rates.coalescence 0 + 2 * rates.mutation 0)
        * oneDemeLDStationaryDenominator rates := by
  simp only [oneDemeStationaryMatrix, stationaryMatrix, oneDemeLDStationaryDenominator,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ]
  norm_num
  ring

/-- The determinant of NOTE1 (14) is strictly positive on the physical rate domain, so the
stationary system has exactly one solution. -/
theorem det_stationaryMatrix_pos (rates : ManyDemeLDRates 1) :
    0 < (oneDemeStationaryMatrix rates).det := by
  rw [det_stationaryMatrix]
  have hc := rates.coalescence_pos 0
  have ht := rates.mutation_nonneg 0
  exact mul_pos (by linarith) (oneDemeLDStationaryDenominator_pos rates)

/-- The one-deme system matrix is invertible on the physical rate domain. -/
theorem isUnit_det_stationaryMatrix (rates : ManyDemeLDRates 1) :
    IsUnit (oneDemeStationaryMatrix rates).det :=
  (det_stationaryMatrix_pos rates).ne'.isUnit

/-- The corpus closed-form stationary state of NOTE1 (16), read in the coordinate order
`(H, DD, Dz, pi2)` of NOTE1 (14). -/
def oneDemeStationaryVector (rates : ManyDemeLDRates 1) : Fin 4 → ℝ :=
  ![oneDemeStationaryLowOrderLDState rates (some (.H 0 0)),
    oneDemeStationaryLowOrderLDState rates (some (.DD 0 0)),
    oneDemeStationaryLowOrderLDState rates (some (.Dz 0 0 0)),
    oneDemeStationaryLowOrderLDState rates (some (.pi2 0 0 0 0))]

/-- The corpus closed form solves the affine system NOTE1 (14). This is a restatement of the
corpus theorem `oneDemeStationaryLowOrderLDState_equations` in matrix form, not a second
verification of the closed form. -/
theorem oneDemeStationaryVector_solves (rates : ManyDemeLDRates 1) :
    (oneDemeStationaryMatrix rates).mulVec (oneDemeStationaryVector rates)
      + stationaryForcing (rates.mutation 0) = 0 := by
  obtain ⟨heterozygosity, linkage, cross, joint⟩ :=
    oneDemeStationaryLowOrderLDState_equations rates
  funext i
  fin_cases i <;>
    simp [oneDemeStationaryMatrix, stationaryMatrix, stationaryForcing,
      oneDemeStationaryVector, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    linarith

/-- **NOTE1 (16).** The corpus stationary state is the unique solution `-B⁻¹ b` of the
affine system (14): the closed form is an inversion, not a fit. -/
theorem oneDemeStationaryVector_eq_neg_inv_mulVec (rates : ManyDemeLDRates 1) :
    oneDemeStationaryVector rates
      = -((oneDemeStationaryMatrix rates)⁻¹.mulVec
          (stationaryForcing (rates.mutation 0))) := by
  have hinv : (oneDemeStationaryMatrix rates)⁻¹ * oneDemeStationaryMatrix rates = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_stationaryMatrix rates)
  have hsolve : (oneDemeStationaryMatrix rates).mulVec (oneDemeStationaryVector rates)
      = -stationaryForcing (rates.mutation 0) :=
    eq_neg_of_add_eq_zero_left (oneDemeStationaryVector_solves rates)
  calc oneDemeStationaryVector rates
      = ((oneDemeStationaryMatrix rates)⁻¹ * oneDemeStationaryMatrix rates).mulVec
          (oneDemeStationaryVector rates) := by
        rw [hinv, Matrix.one_mulVec]
    _ = (oneDemeStationaryMatrix rates)⁻¹.mulVec
          ((oneDemeStationaryMatrix rates).mulVec (oneDemeStationaryVector rates)) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = -((oneDemeStationaryMatrix rates)⁻¹.mulVec
          (stationaryForcing (rates.mutation 0))) := by
        rw [hsolve, Matrix.mulVec_neg]

end

end Descent.Portability.StationaryRealization
