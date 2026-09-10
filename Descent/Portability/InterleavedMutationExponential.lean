/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.InterleavedMutationMeasurability
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

assert_below Descent.Decision Descent.Program

/-!
Exact matrix exponential representation of the chronological mutation law.
The Poisson proposal mixture equals the exponential of its physical generator;
this removes the artificial null-proposal intensity from the resulting law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.InterleavedMutationExponential

open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue ProbabilityTheory
open InterleavedMutationLaw InterleavedMutationMeasurability
open scoped NNReal Matrix.Norms.Operator

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def kernelMatrix (kernel : S → FiniteReportLaw S) : Matrix S S ℝ :=
  fun source target ↦ (kernel source).mass target

theorem propagate_mass (kernel : S → FiniteReportLaw S) (count : ℕ) (source target : S) :
    (ExactFiniteHistoryLaw.propagate (pointMass source) (fun _ ↦ kernel) count).mass target =
      (kernelMatrix kernel ^ count) source target := by
  induction count generalizing target with
  | zero => simp [ExactFiniteHistoryLaw.propagate, pointMass, Matrix.one_apply, eq_comm]
  | succ count ih =>
      change (∑ middle, _ * (kernel middle).mass target) = _
      simp_rw [ih]
      rw [pow_succ, Matrix.mul_apply]
      rfl

theorem poisson_matrix_series (parameter : ℝ≥0) (matrix : Matrix S S ℝ)
    (source target : S) :
    (∑' count, poissonPMFReal parameter count * (matrix ^ count) source target) =
      Real.exp (-(parameter : ℝ)) *
        (NormedSpace.exp ℝ ((parameter : ℝ) • matrix)) source target := by
  have hs : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • (((parameter : ℝ) • matrix) ^ power)) :=
    NormedSpace.expSeries_summable' ((parameter : ℝ) • matrix)
  rw [NormedSpace.exp_eq_tsum]
  dsimp only
  rw [tsum_apply hs, tsum_apply (Pi.summable.mp hs source), ← tsum_mul_left]
  apply tsum_congr
  intro count
  rw [smul_pow]
  simp only [Matrix.smul_apply, smul_eq_mul, poissonPMFReal]
  ring

theorem scalar_identity_exp (scalar : ℝ) :
    NormedSpace.exp ℝ (scalar • (1 : Matrix S S ℝ)) =
      Real.exp scalar • (1 : Matrix S S ℝ) := by
  have hid : scalar • (1 : Matrix S S ℝ) = Matrix.diagonal (fun _ ↦ scalar) := by
    ext source target
    by_cases h : source = target <;> simp [h]
  rw [hid, Matrix.exp_diagonal]
  ext source target
  by_cases h : source = target <;> simp [h, Real.exp_eq_exp_ℝ]

/-- Poisson uniformization gives the exact exponential of `λ(K−I)`. -/
theorem poisson_matrix_exponential (parameter : ℝ≥0) (matrix : Matrix S S ℝ)
    (source target : S) :
    (∑' count, poissonPMFReal parameter count * (matrix ^ count) source target) =
      (NormedSpace.exp ℝ ((parameter : ℝ) • (matrix - 1))) source target := by
  rw [poisson_matrix_series]
  have hdecomp : (parameter : ℝ) • (matrix - 1) =
      (-(parameter : ℝ)) • (1 : Matrix S S ℝ) + (parameter : ℝ) • matrix := by
    simp only [smul_sub, neg_smul]
    abel
  have hcomm : Commute ((-(parameter : ℝ)) • (1 : Matrix S S ℝ))
      ((parameter : ℝ) • matrix) :=
    (Commute.one_left _).smul_left _
  rw [hdecomp, Matrix.exp_add_of_commute ℝ _ _ hcomm, scalar_identity_exp,
    smul_mul_assoc, one_mul]
  rfl

variable {n count : ℕ}

noncomputable def physicalGenerator (branches : Fin count → Branch n) :
    Matrix (SiteState n) (SiteState n) ℝ :=
  ∑ index, ((branches index).exposure : ℝ) •
    (kernelMatrix (mutationKernel (branches index)) - 1)

theorem generator_matrix (branches : Fin count → Branch n) :
    (proposalParameter branches : ℝ) • (kernelMatrix (intervalKernel branches) - 1) =
      physicalGenerator branches := by
  ext source target
  have h := interval_generator branches source (fun output ↦ if output = target then 1 else 0)
  simpa [physicalGenerator, kernelMatrix, expectation, Matrix.one_apply, Matrix.sum_apply,
    eq_comm] using h

/-- The catalogue-preserving interval law equals a finite matrix exponential,
not merely a kernel whose infinitesimal generator has the desired rates. -/
theorem interval_matrix_exponential (branches : Fin count → Branch n)
    (source target : SiteState n) :
    (intervalLaw branches source).mass target =
      (NormedSpace.exp ℝ (physicalGenerator branches)) source target := by
  change (∑' proposals, poissonPMFReal _ proposals *
    (ExactFiniteHistoryLaw.propagate (pointMass source)
      (fun _ ↦ intervalKernel branches) proposals).mass target) = _
  simp_rw [propagate_mass]
  rw [poisson_matrix_exponential, generator_matrix]

theorem physicalGenerator_scale (templates : Fin count → Branch n)
    (rates : Fin count → ℝ≥0) (duration : ℝ≥0) :
    physicalGenerator (replaceExposure templates (fun index ↦ duration * rates index)) =
      (duration : ℝ) • physicalGenerator (replaceExposure templates rates) := by
  simp only [physicalGenerator, replaceExposure, NNReal.coe_mul, Finset.smul_sum, smul_smul]
  rfl

/-- Subdividing an interval leaves the entire ordered-catalogue law invariant.
Both pieces use the same active clades and per-branch mutation rates. -/
theorem interval_compose (templates : Fin count → Branch n) (rates : Fin count → ℝ≥0)
    (first second : ℝ≥0) (source : SiteState n) :
    (intervalLaw (replaceExposure templates (fun index ↦ first * rates index)) source).bind
        (intervalLaw (replaceExposure templates (fun index ↦ second * rates index))) =
      intervalLaw (replaceExposure templates (fun index ↦ (first + second) * rates index))
        source := by
  apply FiniteReportLaw.ext
  intro target
  change (∑ middle, _ * _) = _
  simp_rw [interval_matrix_exponential, physicalGenerator_scale]
  rw [← Matrix.mul_apply, NNReal.coe_add, add_smul,
    Matrix.exp_add_of_commute ℝ _ _
      (((Commute.refl (physicalGenerator (replaceExposure templates rates))).smul_left
        (first : ℝ)).smul_right (second : ℝ))]

end Descent.Portability.InterleavedMutationExponential
