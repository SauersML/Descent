/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.WholeGenomeMutationSemigroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

assert_below Descent.Decision Descent.Program

/-!
A finite product of coordinate mutation semigroups has the sum of lifted
coordinate generators. The common duration is retained until after this
whole-state exponential is formed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteProductExponential

open scoped Matrix.Norms.Operator

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A differentiable finite matrix semigroup is identified by its generator. -/
theorem semigroup_eq_exponential (evolution : ℝ → Matrix S S ℝ)
    (generator : Matrix S S ℝ) (hzero : evolution 0 = 1)
    (hadd : ∀ first second, evolution (first + second) = evolution first * evolution second)
    (hderiv : HasDerivAt evolution generator 0) (time : ℝ) :
    evolution time = NormedSpace.exp ℝ (time • generator) := by
  have hd (time : ℝ) : HasDerivAt evolution (evolution time * generator) time := by
    have hd0 : HasDerivAt evolution generator (time - time) := by simpa using hderiv
    have hh := hd0.scomp (h := fun x : ℝ ↦ x - time) time ((hasDerivAt_id time).sub_const time)
    simp only [one_smul] at hh
    have hm := (hasDerivAt_const time (evolution time)).mul hh
    simp only [zero_mul, zero_add] at hm
    have heq : (fun x ↦ evolution time * evolution (x - time)) = evolution := by
      funext x
      rw [← hadd]
      congr 1
      ring
    change HasDerivAt (fun x ↦ evolution time * evolution (x - time))
      (evolution time * generator) time at hm
    rwa [heq] at hm
  have hproduct (time : ℝ) : HasDerivAt
      (fun x ↦ evolution x * NormedSpace.exp ℝ ((-x) • generator)) 0 time := by
    have hexp := (hasDerivAt_exp_smul_const' generator (-time)).scomp time
      (hasDerivAt_neg time)
    have hp := (hd time).mul hexp
    simpa only [Function.comp_def, Pi.mul_apply, neg_one_smul, mul_neg, mul_assoc,
      add_neg_cancel] using hp
  have hconst := is_const_of_deriv_eq_zero
    (fun time ↦ (hproduct time).differentiableAt) (fun time ↦ (hproduct time).deriv) time 0
  simp only [hzero, neg_zero, zero_smul, NormedSpace.exp_zero, mul_one] at hconst
  have hcancel : NormedSpace.exp ℝ ((-time) • generator) *
      NormedSpace.exp ℝ (time • generator) = 1 := by
    rw [← Matrix.exp_add_of_commute ℝ _ _
      (((Commute.refl generator).smul_left (-time)).smul_right time)]
    simp only [← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]
  calc
    evolution time = evolution time *
        (NormedSpace.exp ℝ ((-time) • generator) *
          NormedSpace.exp ℝ (time • generator)) := by rw [hcancel, mul_one]
    _ = NormedSpace.exp ℝ (time • generator) := by rw [← mul_assoc, hconst, one_mul]

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def productMatrix (matrices : I → Matrix S S ℝ) :
    Matrix (I → S) (I → S) ℝ :=
  fun source target ↦ ∏ index, matrices index (source index) (target index)

omit [DecidableEq S] in
theorem productMatrix_mul (first second : I → Matrix S S ℝ) :
    productMatrix first * productMatrix second =
      productMatrix (fun index ↦ first index * second index) := by
  ext source target
  change (∑ middle : I → S, (∏ index, first index (source index) (middle index)) *
      ∏ index, second index (middle index) (target index)) =
    ∏ index, ∑ value, first index (source index) value * second index value (target index)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index value ↦
    first index (source index) value * second index value (target index))).symm

theorem productMatrix_one : productMatrix (fun _ : I ↦ (1 : Matrix S S ℝ)) = 1 := by
  ext source target
  have h := congrArg (fun law : FiniteReportLaw (I → S) ↦ law.mass target)
    (WholeGenomeMutationSemigroup.independent_pointMass source)
  simpa [productMatrix, WholeGenomeMutationSemigroup.independentLaw,
    FiniteReportLaw.pointMass, Matrix.one_apply, eq_comm] using h

noncomputable def productEvolution (generators : I → Matrix S S ℝ) (time : ℝ) :
    Matrix (I → S) (I → S) ℝ :=
  productMatrix (fun index ↦ NormedSpace.exp ℝ (time • generators index))

theorem productEvolution_add (generators : I → Matrix S S ℝ) (first second : ℝ) :
    productEvolution generators (first + second) =
      productEvolution generators first * productEvolution generators second := by
  rw [productEvolution, productEvolution, productEvolution, productMatrix_mul]
  congr 1
  funext index
  rw [add_smul, Matrix.exp_add_of_commute ℝ _ _
    (((Commute.refl (generators index)).smul_left first).smul_right second)]

noncomputable def productGenerator (generators : I → Matrix S S ℝ) :
    Matrix (I → S) (I → S) ℝ :=
  fun source target ↦ ∑ index,
    (∏ other ∈ Finset.univ.erase index, (1 : Matrix S S ℝ) (source other) (target other)) *
      generators index (source index) (target index)

theorem productEvolution_deriv_zero (generators : I → Matrix S S ℝ) :
    HasDerivAt (productEvolution generators) (productGenerator generators) 0 := by
  apply hasDerivAt_pi.mpr
  intro source
  apply hasDerivAt_pi.mpr
  intro target
  have hd (index : I) : HasDerivAt
      (fun time : ℝ ↦ (NormedSpace.exp ℝ (time • generators index))
        (source index) (target index)) (generators index (source index) (target index)) 0 := by
    have h := hasDerivAt_exp_smul_const (generators index) (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp h (source index)) (target index)
  have hprod := HasDerivAt.fun_finset_prod (u := Finset.univ) (fun index _ ↦ hd index)
  simpa [productEvolution, productMatrix, productGenerator, zero_smul,
    NormedSpace.exp_zero, smul_eq_mul] using hprod

/-- Coordinate independence at fixed duration becomes one exact whole-state
matrix exponential, with all coordinate mutation channels retained. -/
theorem productEvolution_exponential (generators : I → Matrix S S ℝ) (time : ℝ) :
    productEvolution generators time = NormedSpace.exp ℝ (time • productGenerator generators) := by
  apply semigroup_eq_exponential _ _ _ (productEvolution_add generators)
    (productEvolution_deriv_zero generators)
  simpa [productEvolution] using (productMatrix_one (I := I) (S := S))

open Coalescent.FiniteGenomeAncestry GenealogyGenotypeLaw OrderedMutationCatalogue
open StoppedGenotypeLaw AncestralEpochGenotypeLaw InterleavedMutationLaw
open InterleavedMutationMeasurability InterleavedMutationExponential
open scoped NNReal

variable {D L n : ℕ}

noncomputable def genomeGenerator (state : State D L n) (rate : ℝ≥0) :
    Matrix (WholeGenome L n) (WholeGenome L n) ℝ :=
  productGenerator (fun locus ↦
    physicalGenerator (replaceExposure (intervalTemplates state locus) (fun _ ↦ rate)))

/-- The actual product site mutation kernel at a common duration equals one
whole-genome exponential. Averaging the duration therefore retains the
cross-locus dependence induced by that common ancestry clock. -/
theorem intervalGenome_exponential (state : State D L n) (rate duration : ℝ≥0)
    (source target : WholeGenome L n) :
    (intervalGenomeKernel state rate duration source).mass target =
      (NormedSpace.exp ℝ ((duration : ℝ) • genomeGenerator state rate)) source target := by
  change (∏ locus, (stateIntervalLaw state locus rate duration (source locus)).mass
    (target locus)) = _
  simp only [stateIntervalLaw, Real.toNNReal_coe]
  simp_rw [interval_matrix_exponential]
  have hg (locus : Fin L) :
      physicalGenerator
        (replaceExposure (intervalTemplates state locus) (fun _ ↦ rate * duration)) =
        (duration : ℝ) • physicalGenerator
          (replaceExposure (intervalTemplates state locus) (fun _ ↦ rate)) := by
    simpa only [mul_comm] using
      physicalGenerator_scale (intervalTemplates state locus) (fun _ ↦ rate) duration
  simp_rw [hg]
  exact congrArg (fun matrix : Matrix (WholeGenome L n) (WholeGenome L n) ℝ ↦ matrix source target)
    (productEvolution_exponential (fun locus ↦ physicalGenerator
      (replaceExposure (intervalTemplates state locus) (fun _ ↦ rate))) duration)

end Descent.Portability.FiniteProductExponential
