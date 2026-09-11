/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

`stationary_mem_of_orbit_mem` is the Cesàro argument of NOTE1 Theorem 3, in general form: if
a convex closed bounded set contains the forward orbit of a solution of the affine system
`w' = B w + b` with `B` invertible, then it contains the stationary point `-B⁻¹ b`. The proof
is the one indicated in the note, with no subsequence extraction. The time average over
`[0, T]` lies in the set because the set is convex and closed and the average of an
integrable function into a convex closed set stays there; the fundamental theorem of calculus
turns the affine equation into `B (average) + b = (w T - w 0)/T`; the orbit is bounded because
it stays in a bounded set, so the right side tends to zero and the averages converge to
`-B⁻¹ b`, which the set contains because it is closed.

`oneDemeStationaryVector_mem_of_orbit_mem` is NOTE1 Theorem 3 for the corpus vector: any
convex closed bounded set containing a forward orbit of the one-deme system (14) contains the
corpus stationary state. In the intended application that set is the one-deme realization
body intersected with the coordinates of (14), and the orbit is supplied by NOTE1 Theorem 1
from a microscopic approximation of the augmented one-deme generator.

What is NOT proved in this module: that such an orbit exists for the corpus generator. That
needs a microscopic approximation for the augmented one-deme generator, the closedness and
boundedness of the one-deme realization body, and the derivative of the matrix-exponential
orbit; none of those is available here. The hypothesis is therefore stated explicitly rather
than discharged, and the theorem is exactly as strong as the orbit it is given.

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

/-- The three-by-three minor of NOTE1 (14) left after deleting the heterozygosity row and
column. The heterozygosity row of `B` has a single nonzero entry, so the whole determinant
is carried by this minor. -/
def stationaryMinor (c theta rho : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(3 * c + rho + 4 * theta), c, c;
     4 * c, -(5 * c + rho / 2 + 4 * theta), 0;
     0, c, -(2 * c + 4 * theta)]

/-- Deleting the heterozygosity row and column of NOTE1 (14) leaves the stated minor. -/
theorem submatrix_stationaryMatrix (c theta rho : ℝ) :
    (stationaryMatrix c theta rho).submatrix Fin.succ (Fin.succAbove 0)
      = stationaryMinor c theta rho := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Cofactor expansion of NOTE1 (14) along the heterozygosity row: only one term survives. -/
theorem det_stationaryMatrix_eq_minor (c theta rho : ℝ) :
    (stationaryMatrix c theta rho).det
      = -(c + 2 * theta) * (stationaryMinor c theta rho).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, submatrix_stationaryMatrix]
  simp [stationaryMatrix] <;> ring

/-- The minor of NOTE1 (14) has determinant exactly minus the corpus stationary
denominator. -/
theorem det_stationaryMinor (rates : ManyDemeLDRates 1) :
    (stationaryMinor (rates.coalescence 0) (rates.mutation 0)
        (rates.recombination 0)).det
      = -oneDemeLDStationaryDenominator rates := by
  simp [stationaryMinor, Matrix.det_fin_three, oneDemeLDStationaryDenominator] <;> ring

/-- **NOTE1 (15).** The determinant of the one-deme system matrix is exactly
`(c + 2 theta)` times the corpus stationary denominator, with no sign correction. -/
theorem det_stationaryMatrix (rates : ManyDemeLDRates 1) :
    (oneDemeStationaryMatrix rates).det
      = (rates.coalescence 0 + 2 * rates.mutation 0)
        * oneDemeLDStationaryDenominator rates := by
  rw [oneDemeStationaryMatrix, det_stationaryMatrix_eq_minor, det_stationaryMinor]
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
      oneDemeStationaryVector] <;>
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

section CesaroLimit

open scoped Matrix.Norms.Operator

/-- **The Cesàro step of NOTE1 Theorem 3.** If a convex, closed, bounded set contains the
whole forward orbit of a solution of the affine system `w' = B w + b` with invertible `B`,
then it contains the stationary point `-B⁻¹ b`. No subsequence extraction is needed: the time
averages themselves converge to the stationary point.
Assumes: `K` convex, closed and bounded; `B` invertible; `w` differentiable everywhere with
the stated derivative; the forward orbit inside `K`. -/
theorem stationary_mem_of_orbit_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set (ι → ℝ)) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKbdd : Bornology.IsBounded K) (B : Matrix ι ι ℝ) (hB : IsUnit B.det) (b : ι → ℝ)
    (w : ℝ → ι → ℝ) (hw : ∀ t, HasDerivAt w (B.mulVec (w t) + b) t)
    (hmem : ∀ t, 0 ≤ t → w t ∈ K) :
    -(B⁻¹.mulVec b) ∈ K := by
  have hcont : Continuous w :=
    continuous_iff_continuousAt.mpr fun t ↦ (hw t).continuousAt
  have hmulcont : Continuous fun t ↦ B.mulVec (w t) := by
    have hcomp :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin B)).continuous.comp hcont
    simpa using hcomp
  have hleft : ∀ x : ι → ℝ, B⁻¹.mulVec (B.mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  have hid : ∀ T : ℝ,
      B.mulVec (∫ t in (0 : ℝ)..T, w t) + T • b = w T - w 0 := by
    intro T
    have hftc : ∫ t in (0 : ℝ)..T, (B.mulVec (w t) + b) = w T - w 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hw x)
        ((hmulcont.add continuous_const).intervalIntegrable 0 T)
    have hsplit : ∫ t in (0 : ℝ)..T, (B.mulVec (w t) + b)
        = B.mulVec (∫ t in (0 : ℝ)..T, w t) + T • b := by
      rw [intervalIntegral.integral_add (hmulcont.intervalIntegrable 0 T)
        (continuous_const.intervalIntegrable 0 T)]
      congr 1
      · have hcomm := (LinearMap.toContinuousLinearMap
          (Matrix.mulVecLin B)).intervalIntegral_comp_comm (hcont.intervalIntegrable 0 T)
        simpa using hcomm
      · rw [intervalIntegral.integral_const, sub_zero]
    rw [← hsplit, hftc]
  have havg : ∀ T : ℝ, 0 < T → (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) ∈ K := by
    intro T hT
    have huioc : Set.uIoc (0 : ℝ) T = Set.Ioc 0 T := Set.uIoc_of_le hT.le
    have hvol : MeasureTheory.volume (Set.uIoc (0 : ℝ) T) ≠ 0 := by
      rw [huioc, Real.volume_Ioc, sub_zero, Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hT
    have hvolfin : MeasureTheory.volume (Set.uIoc (0 : ℝ) T) ≠ ⊤ := by
      rw [huioc, Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) T)), w x ∈ K := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      rw [huioc] at hx
      exact hmem x hx.1.le
    have hint : MeasureTheory.IntegrableOn w (Set.uIoc (0 : ℝ) T) :=
      intervalIntegrable_iff.mp (hcont.intervalIntegrable 0 T)
    have hrw : (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) = ⨍ t in (0 : ℝ)..T, w t := by
      rw [interval_average_eq, sub_zero]
    rw [hrw]
    exact hKconv.set_average_mem hKclosed hvol hvolfin hae hint
  obtain ⟨bound, hbound⟩ := isBounded_iff_forall_norm_le.mp hKbdd
  have hdiff : ∀ T : ℝ, 0 < T →
      (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) - -(B⁻¹.mulVec b)
        = B⁻¹.mulVec (T⁻¹ • (w T - w 0)) := by
    intro T hT
    have hTne : (T : ℝ) ≠ 0 := hT.ne'
    have hkey : B.mulVec (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) + b = T⁻¹ • (w T - w 0) := by
      have hscale : B.mulVec (T⁻¹ • ∫ t in (0 : ℝ)..T, w t)
          = T⁻¹ • B.mulVec (∫ t in (0 : ℝ)..T, w t) := Matrix.mulVec_smul _ _ _
      have hsolve : B.mulVec (∫ t in (0 : ℝ)..T, w t) = w T - w 0 - T • b := by
        rw [← hid T]
        abel
      rw [hscale, hsolve, smul_sub, smul_smul, inv_mul_cancel₀ hTne, one_smul]
      abel
    calc (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) - -(B⁻¹.mulVec b)
        = B⁻¹.mulVec (B.mulVec (T⁻¹ • ∫ t in (0 : ℝ)..T, w t)) + B⁻¹.mulVec b := by
          rw [hleft, sub_neg_eq_add]
      _ = B⁻¹.mulVec (B.mulVec (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) + b) :=
          (Matrix.mulVec_add _ _ _).symm
      _ = B⁻¹.mulVec (T⁻¹ • (w T - w 0)) := by rw [hkey]
  have hnormbound : ∀ T : ℝ, 0 < T →
      ‖(T⁻¹ • ∫ t in (0 : ℝ)..T, w t) - -(B⁻¹.mulVec b)‖
        ≤ ‖B⁻¹‖ * (T⁻¹ * (2 * bound)) := by
    intro T hT
    rw [hdiff T hT]
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hT.le)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hT.le)
    have hwT : ‖w T‖ ≤ bound := hbound _ (hmem T hT.le)
    have hw0 : ‖w 0‖ ≤ bound := hbound _ (hmem 0 le_rfl)
    calc ‖w T - w 0‖ ≤ ‖w T‖ + ‖w 0‖ := norm_sub_le _ _
      _ ≤ 2 * bound := by linarith
  have hzero : Filter.Tendsto
      (fun T : ℝ ↦ (T⁻¹ • ∫ t in (0 : ℝ)..T, w t) - -(B⁻¹.mulVec b))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (a := fun T : ℝ ↦ ‖B⁻¹‖ * (T⁻¹ * (2 * bound))) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
      exact hnormbound T hT
    · have hscaled := (tendsto_inv_atTop_zero.mul_const (2 * bound)).const_mul ‖B⁻¹‖
      simpa using hscaled
  have hconst : Filter.Tendsto (fun _ : ℝ ↦ -(B⁻¹.mulVec b)) Filter.atTop
      (nhds (-(B⁻¹.mulVec b))) := tendsto_const_nhds
  have hlimit := hzero.add hconst
  rw [zero_add] at hlimit
  refine hKclosed.mem_of_tendsto (hlimit.congr fun T ↦ by abel) ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  exact havg T hT

/-- **NOTE1 Theorem 3.** Any convex closed bounded set containing a whole forward orbit of the
one-deme affine system (14) contains the corpus stationary low-order vector. In the intended
application the set is the one-deme realization body read in the coordinates of (14) and the
orbit is supplied by the invariance theorem, so this says the ancestral stationary boundary
has a common haplotype realization. Assumes: the orbit is given. -/
theorem oneDemeStationaryVector_mem_of_orbit_mem (rates : ManyDemeLDRates 1)
    (K : Set (Fin 4 → ℝ)) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKbdd : Bornology.IsBounded K) (w : ℝ → Fin 4 → ℝ)
    (hw : ∀ t, HasDerivAt w ((oneDemeStationaryMatrix rates).mulVec (w t)
      + stationaryForcing (rates.mutation 0)) t)
    (hmem : ∀ t, 0 ≤ t → w t ∈ K) :
    oneDemeStationaryVector rates ∈ K := by
  rw [oneDemeStationaryVector_eq_neg_inv_mulVec]
  exact stationary_mem_of_orbit_mem K hKconv hKclosed hKbdd (oneDemeStationaryMatrix rates)
    (isUnit_det_stationaryMatrix rates) (stationaryForcing (rates.mutation 0)) w hw hmem

end CesaroLimit

end

end Descent.Portability.StationaryRealization
