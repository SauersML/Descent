/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralMicroscopicFloorLimit

assert_below Descent.Decision Descent.Program

/-!
# Continuity at time zero of the neutral semigroup

NOTE1 §4.2a: continuity at `t = 0` follows first for each finite polynomial space and then for all
continuous functions by density and contraction.  This module proves it.

The dual propagator is continuous at time zero in operator norm
(`tendsto_norm_matrixExponential_sub_one`).  A polynomial observable and its image under the
neutral polynomial semigroup are one combination of configuration moments and of the dual
propagator (`NeutralMicroscopicFloorLimit.coe_polynomialSubspace_eq_dotProduct`,
`NeutralMicroscopicFloorLimit.coe_neutralPolynomialSemigroup_eq_dotProduct`).  So `T_t f` differs
from `f` in sup norm by at most the coefficient mass times `‖e^{tQ} - 1‖` times the feature bound
(`abs_dotProduct_propagator_sub_le`, `norm_neutralPolynomialSemigroup_sub_le`), and `T_t f → f` as
`t → 0` (`tendsto_neutralPolynomialSemigroup_zero`).  The extended semigroup contracts sup norms
and the polynomial observables are dense, so `T_t g → g` in sup norm for every continuous
observable `g` (`tendsto_neutralSemigroupExtension_zero`).  Integrated against the neutral Markov
kernels, `∫ g dK_t → g` uniformly in the state
(`tendstoUniformly_integral_neutralMarkovKernel_zero`).

## Empirical status

None.  The bodies here are analysis of matrix exponentials of supplied rates and of continuous
observables on the frequency simplex, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralFellerContinuity

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup NeutralPolynomialPositivity
  PartialHaplotypeMicroscopicApproximation PolynomialFellerExtension
  NeutralMicroscopicEulerLimit NeutralMicroscopicFloorLimit
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

/-- **The matrix exponential is continuous at time zero in operator norm.** -/
theorem tendsto_norm_matrixExponential_sub_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    Tendsto (fun t : ℝ ↦ ‖matrixExponential A t - 1‖) (𝓝 0) (𝓝 0) := by
  have hcont : Continuous fun t : ℝ ↦ NormedSpace.exp ℝ (t • A) :=
    (NormedSpace.exp_continuous (𝕂 := ℝ)).comp (continuous_id.smul continuous_const)
  have hconv := tendsto_iff_norm_sub_tendsto_zero.mp (hcont.tendsto 0)
  simp only [← matrixExponential_eq_normedSpace_exp, matrixExponential_zero] at hconv
  exact hconv

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- A combination of configuration moments moves under the dual propagator by at most the
coefficient mass times the operator distance of the propagator from the identity times the
feature bound. -/
theorem abs_dotProduct_propagator_sub_le (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (c : BudgetConfiguration Deme Locus Allele capacity → ℝ) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) :
    |c ⬝ᵥ (matrixExponential (dualGenerator rates capacity) t *ᵥ budgetMomentFeature capacity x)
        - c ⬝ᵥ budgetMomentFeature capacity x|
      ≤ (∑ η, |c η|)
        * (‖matrixExponential (dualGenerator rates capacity) t - 1‖
          * featureBound rates capacity) := by
  have hvec : ‖matrixExponential (dualGenerator rates capacity) t
          *ᵥ budgetMomentFeature capacity x - budgetMomentFeature capacity x‖
      ≤ ‖matrixExponential (dualGenerator rates capacity) t - 1‖ * featureBound rates capacity := by
    have hsplit : matrixExponential (dualGenerator rates capacity) t
          *ᵥ budgetMomentFeature capacity x - budgetMomentFeature capacity x
        = (matrixExponential (dualGenerator rates capacity) t - 1)
          *ᵥ budgetMomentFeature capacity x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hsplit]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (norm_budgetMomentFeature_le rates capacity x) (norm_nonneg _))
  rw [← dotProduct_sub]
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun η _ ↦ ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ η).trans hvec

/-- The neutral polynomial semigroup moves a polynomial observable in sup norm by at most the mass
of its support coefficients times the operator distance of the dual propagator from the identity
times the feature bound. -/
theorem norm_neutralPolynomialSemigroup_sub_le (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0)
    (f : PolynomialSubspace Deme Locus Allele) :
    ‖(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
        - (f : C(FrequencyState Deme Locus Allele, ℝ))‖
      ≤ (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
        * (‖matrixExponential (dualGenerator rates (supportBudget ℓ₀ (representative f))) t - 1‖
          * featureBound rates (supportBudget ℓ₀ (representative f))) := by
  refine (ContinuousMap.norm_le _ (mul_nonneg (Finset.sum_nonneg fun η _ ↦ abs_nonneg _)
    (mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec rates _ ξ).1)))).mpr fun x ↦ ?_
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs,
    congrFun (coe_neutralPolynomialSemigroup_eq_dotProduct rates ℓ₀ hap₀ t f) x,
    congrFun (coe_polynomialSubspace_eq_dotProduct ℓ₀ f) x]
  exact abs_dotProduct_propagator_sub_le rates _ _ t x

/-- **Continuity at time zero on polynomial observables.**  For every polynomial observable `f`,
`T_t f → f` in sup norm as `t → 0`. -/
theorem tendsto_neutralPolynomialSemigroup_zero (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (f : PolynomialSubspace Deme Locus Allele) :
    Tendsto
      (fun t : ℝ≥0 ↦
        (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ)))
      (𝓝 0) (𝓝 (f : C(FrequencyState Deme Locus Allele, ℝ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ≥0 ↦ (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
      * (‖matrixExponential (dualGenerator rates (supportBudget ℓ₀ (representative f))) t - 1‖
        * featureBound rates (supportBudget ℓ₀ (representative f)))) (𝓝 0) (𝓝 0) := by
    have h := (((tendsto_norm_matrixExponential_sub_one
      (dualGenerator rates (supportBudget ℓ₀ (representative f)))).comp
      (NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero)).mul_const
      (featureBound rates (supportBudget ℓ₀ (representative f)))).const_mul
      (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
    rwa [zero_mul, mul_zero] at h
  exact squeeze_zero (fun t ↦ norm_nonneg _)
    (fun t ↦ norm_neutralPolynomialSemigroup_sub_le rates ℓ₀ hap₀ t f) hlim

/-- **NOTE1 §4.2a, continuity at time zero.**  For every continuous observable `g`, the extended
neutral semigroup satisfies `T_t g → g` in sup norm as `t → 0`: the polynomial observables are
dense and every `T_t` contracts sup norms. -/
theorem tendsto_neutralSemigroupExtension_zero (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    Tendsto (fun t : ℝ≥0 ↦ neutralSemigroupExtension rates ℓ₀ hap₀ t g) (𝓝 0) (𝓝 g) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨f, hf⟩ := dense_polynomialSubspace.denseRange_val.exists_dist_lt g hε3
  filter_upwards [Metric.tendsto_nhds.mp (tendsto_neutralPolynomialSemigroup_zero rates ℓ₀ hap₀ f)
    (ε / 3) hε3] with t ht
  have hext : dist (neutralSemigroupExtension rates ℓ₀ hap₀ t g)
      (neutralSemigroupExtension rates ℓ₀ hap₀ t (f : C(FrequencyState Deme Locus Allele, ℝ)))
        ≤ dist g (f : C(FrequencyState Deme Locus Allele, ℝ)) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact denseExtension_norm_le _ dense_polynomialSubspace _ _ _
  have hcoe : neutralSemigroupExtension rates ℓ₀ hap₀ t (f : C(FrequencyState Deme Locus Allele, ℝ))
      = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ)) :=
    denseExtension_coe _ dense_polynomialSubspace _ _ f
  rw [hcoe] at hext
  have hfg : dist (f : C(FrequencyState Deme Locus Allele, ℝ)) g < ε / 3 := by
    rwa [dist_comm]
  calc dist (neutralSemigroupExtension rates ℓ₀ hap₀ t g) g
      ≤ dist (neutralSemigroupExtension rates ℓ₀ hap₀ t g)
          (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
        + dist (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
            : C(FrequencyState Deme Locus Allele, ℝ)) (f : C(FrequencyState Deme Locus Allele, ℝ))
        + dist (f : C(FrequencyState Deme Locus Allele, ℝ)) g := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add (hext.trans_lt hf) ht) hfg
    _ = ε := by ring

/-- **Continuity at time zero of the neutral Markov kernels.**  For every continuous observable
`g`, `∫ g dK_t(x, ·) → g(x)` uniformly in the state as `t → 0`. -/
theorem tendstoUniformly_integral_neutralMarkovKernel_zero (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    TendstoUniformly (fun (t : ℝ≥0) x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x)) ⇑g
      (𝓝 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp (tendsto_neutralSemigroupExtension_zero rates ℓ₀ hap₀ g)
    ε hε] with t ht x
  rw [integral_neutralMarkovKernel, dist_comm]
  exact (ContinuousMap.dist_apply_le_dist x).trans_lt ht

end

end Descent.Portability.NeutralFellerContinuity
