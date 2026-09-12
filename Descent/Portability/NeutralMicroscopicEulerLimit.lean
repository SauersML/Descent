/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralPolynomialPositivity
import Descent.Portability.EulerInvariantSet
import Descent.Portability.FellerMarkovKernel

assert_below Descent.Decision Descent.Program

/-!
# The Euler limit of the neutral microscopic kernel

NOTE1 §4.2a identifies the neutral polynomial semigroup as the limit of the physical microscopic
kernel along `N` steps of size `t/N`.  This module proves it, and carries the limit to every
continuous observable and to the neutral Markov kernels.

Kernel powers against Euler products.  For a `MicroscopicApproximation` of a matrix `A` on a
feature `φ`, the coordinates of `φ` pushed through `n` kernel steps of size `h` differ from
`(1 + hA)^n φ` by at most `n (1 + h‖A‖)^n h ε(h)`, uniformly in the state
(`norm_kernelPower_sub_euler_le`).  This is the telescoping estimate NOTE1 (5) with the kernel
acting on observables instead of moment vectors: kernel iterates are linear over finite
combinations (`iterate_apply_sum`) and contract uniform distances.  At `h = t/N` the bound is
`t e^{t‖A‖} ε(t/N)` (`norm_kernelPower_sub_euler_le_exp`), and the Euler products converge to
`e^{tA}`, so every fixed combination of feature coordinates converges uniformly in the state
(`tendstoUniformly_kernelPower_dotProduct`).

The neutral model.  The budget-moment feature is bounded on states
(`norm_budgetMomentFeature_le`), so the neutral microscopic approximation of
`PartialHaplotypeMicroscopicApproximation` sends every combination of configuration moments to
the same combination of the dual propagator (`tendstoUniformly_kernelPower_momentPolynomial`).
Through its support budget, a polynomial observable is such a combination
(`supportCoefficients`), and the neutral polynomial semigroup is the same combination of the dual
propagator.  Hence `K_{t/N}^N f → T_t f` uniformly for every polynomial observable
(`tendstoUniformly_neutralPolynomialSemigroup`).

All continuous observables.  The semigroup is positive and fixes the constants, so it contracts
sup norms (`norm_neutralPolynomialSemigroup_le`) and extends continuously to `C(X)`
(`neutralSemigroupExtension`); the kernel powers converge uniformly to the extension on every
continuous observable (`tendstoUniformly_neutralSemigroupExtension`).  The Riesz kernels of the
extension are Markov kernels (`neutralMarkovKernel`, `isMarkovKernel_neutralMarkovKernel`) that
integrate every continuous observable to the extension (`integral_neutralMarkovKernel`), represent
the polynomial semigroup (`integral_neutralMarkovKernel_polynomial`), and compose by
`K_{s+t} = K_t ∘ₖ K_s` (`neutralMarkovKernel_add`).  So the microscopic chain converges in law to
the neutral diffusion, uniformly in the initial state: `K_{t/N}^N g → ∫ g dK_t` uniformly for
every continuous observable `g` (`tendstoUniformly_integral_neutralMarkovKernel`).

Scope.  The limit is along `N` steps of size `t/N` at a fixed `t > 0`.  The floor form
`K_h^{⌊t/h⌋}` as `h ↓ 0` is not proved here, and at `t = 0` the approximation does not constrain
the kernel family, so no statement is made.

## Empirical status

None.  The bodies here are analysis of finite mixture kernels and matrix exponentials of supplied
rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralMicroscopicEulerLimit

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup NeutralPolynomialPositivity
  PartialHaplotypeMicroscopicStages PartialHaplotypeMicroscopicApproximation FiniteMixtureKernel
  PolynomialFellerExtension FellerMarkovKernel EulerInvariantSet
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

/-! ## Kernel powers against Euler products -/

section Abstract

variable {B X ι : Type*} [Fintype B] [Fintype ι]

/-- The kernel action is linear over finite combinations of observables. -/
theorem apply_sum (K : FiniteMixtureKernel B X) (c : ι → ℝ) (s : ι → X → ℝ) (x : X) :
    K.apply (fun y ↦ ∑ j, c j * s j y) x = ∑ j, c j * K.apply (s j) x := by
  simp only [FiniteMixtureKernel.apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- Iterates of the kernel action are linear over finite combinations of observables. -/
theorem iterate_apply_sum (K : FiniteMixtureKernel B X) (n : ℕ) (c : ι → ℝ) (s : ι → X → ℝ)
    (x : X) :
    K.apply^[n] (fun y ↦ ∑ j, c j * s j y) x = ∑ j, c j * K.apply^[n] (s j) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [show K.apply^[n] (fun y ↦ ∑ j, c j * s j y)
        = fun y ↦ ∑ j, c j * K.apply^[n] (s j) y from funext ih]
    exact apply_sum K c (fun j ↦ K.apply^[n] (s j)) x

variable {φ : X → ι → ℝ} {A : Matrix ι ι ℝ}

/-- **The telescoping estimate for kernel powers.**  After `n` kernel steps of size `h`, the
coordinates of the feature differ from the Euler product `(1 + hA)^n` applied to the feature by
at most `n (1 + h‖A‖)^n h ε(h)`, uniformly in the state. -/
theorem norm_kernelPower_sub_euler_le [DecidableEq ι]
    (M : MicroscopicApproximation (B := B) φ A) (h : ℝ) (hh : 0 < h) (n : ℕ) (x : X) :
    ‖(fun i ↦ (M.kernel h).apply^[n] (fun y ↦ φ y i) x) - ((1 + h • A) ^ n) *ᵥ φ x‖
      ≤ (n : ℝ) * (1 + h * ‖A‖) ^ n * (h * M.error h) := by
  have hb : (1 : ℝ) ≤ 1 + h * ‖A‖ := by
    have := mul_nonneg hh.le (norm_nonneg A)
    linarith
  have hstepnn : 0 ≤ h * M.error h := mul_nonneg hh.le (M.error_nonneg h)
  have hstep : ∀ i y, |(M.kernel h).apply (fun y ↦ φ y i) y - ((1 + h • A) *ᵥ φ y) i|
      ≤ h * M.error h := by
    intro i y
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, ← sub_sub]
    exact M.expansion h hh y i
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hlin : ∀ i, (M.kernel h).apply^[n] (fun y ↦ ((1 + h • A) *ᵥ φ y) i) x
        = ((1 + h • A) *ᵥ fun j ↦ (M.kernel h).apply^[n] (fun y ↦ φ y j) x) i := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      exact iterate_apply_sum (M.kernel h) n (fun j ↦ (1 + h • A) i j) (fun j y ↦ φ y j) x
    have hsplit : (fun i ↦ (M.kernel h).apply^[n + 1] (fun y ↦ φ y i) x)
          - ((1 + h • A) ^ (n + 1)) *ᵥ φ x
        = (fun i ↦ (M.kernel h).apply^[n] ((M.kernel h).apply fun y ↦ φ y i) x
            - (M.kernel h).apply^[n] (fun y ↦ ((1 + h • A) *ᵥ φ y) i) x)
          + (1 + h • A) *ᵥ ((fun i ↦ (M.kernel h).apply^[n] (fun y ↦ φ y i) x)
            - ((1 + h • A) ^ n) *ᵥ φ x) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Function.iterate_succ_apply, hlin]
      ring
    have hfirst : ‖fun i ↦ (M.kernel h).apply^[n] ((M.kernel h).apply fun y ↦ φ y i) x
        - (M.kernel h).apply^[n] (fun y ↦ ((1 + h • A) *ᵥ φ y) i) x‖ ≤ h * M.error h :=
      (pi_norm_le_iff_of_nonneg hstepnn).mpr fun i ↦ by
        rw [Real.norm_eq_abs]
        exact iterate_apply_sub_le (M.kernel h) n _ _ _ (hstep i) x
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add hfirst (norm_euler_step_le A h hh.le _)).trans ?_
    calc h * M.error h + (1 + h * ‖A‖)
            * ‖(fun i ↦ (M.kernel h).apply^[n] (fun y ↦ φ y i) x) - ((1 + h • A) ^ n) *ᵥ φ x‖
        ≤ h * M.error h + (1 + h * ‖A‖) * ((n : ℝ) * (1 + h * ‖A‖) ^ n * (h * M.error h)) :=
          add_le_add_left (mul_le_mul_of_nonneg_left (ih x) (by linarith)) _
      _ = (h * M.error h) * (1 + (n : ℝ) * (1 + h * ‖A‖) ^ (n + 1)) := by ring
      _ ≤ (h * M.error h) * (((n : ℝ) + 1) * (1 + h * ‖A‖) ^ (n + 1)) := by
          have hone : (1 : ℝ) ≤ (1 + h * ‖A‖) ^ (n + 1) := one_le_pow₀ hb
          have hgap : 1 + (n : ℝ) * (1 + h * ‖A‖) ^ (n + 1)
              ≤ ((n : ℝ) + 1) * (1 + h * ‖A‖) ^ (n + 1) := by nlinarith
          exact mul_le_mul_of_nonneg_left hgap hstepnn
      _ = ((n + 1 : ℕ) : ℝ) * (1 + h * ‖A‖) ^ (n + 1) * (h * M.error h) := by
          push_cast
          ring

/-- At the step size `t/N`, after `N` steps, the telescoping bound is at most
`t e^{t‖A‖} ε(t/N)`. -/
theorem norm_kernelPower_sub_euler_le_exp [DecidableEq ι]
    (M : MicroscopicApproximation (B := B) φ A) (t : ℝ) (ht : 0 < t) (N : ℕ) (hN : 0 < N)
    (x : X) :
    ‖(fun i ↦ (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ φ y i) x)
        - ((1 + (t / (N : ℝ)) • A) ^ N) *ᵥ φ x‖
      ≤ t * Real.exp (t * ‖A‖) * M.error (t / (N : ℝ)) := by
  have hh : 0 < t / (N : ℝ) := div_pos ht (by exact_mod_cast hN)
  have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnn : (0 : ℝ) ≤ 1 + (t / (N : ℝ)) * ‖A‖ := by
    have := mul_nonneg hh.le (norm_nonneg A)
    linarith
  have hle : 1 + (t / (N : ℝ)) * ‖A‖ ≤ Real.exp ((t / (N : ℝ)) * ‖A‖) := by
    have := Real.add_one_le_exp ((t / (N : ℝ)) * ‖A‖)
    linarith
  have hexpb : (1 + (t / (N : ℝ)) * ‖A‖) ^ N ≤ Real.exp (t * ‖A‖) := by
    calc (1 + (t / (N : ℝ)) * ‖A‖) ^ N
        ≤ (Real.exp ((t / (N : ℝ)) * ‖A‖)) ^ N := pow_le_pow_left₀ hnn hle N
      _ = Real.exp ((N : ℝ) * ((t / (N : ℝ)) * ‖A‖)) :=
          (Real.exp_nat_mul ((t / (N : ℝ)) * ‖A‖) N).symm
      _ = Real.exp (t * ‖A‖) := by
          congr 1
          field_simp
  refine (norm_kernelPower_sub_euler_le M (t / (N : ℝ)) hh N x).trans ?_
  have hNt : (N : ℝ) * (t / (N : ℝ)) = t := by field_simp
  have hcollapse : (N : ℝ) * (1 + (t / (N : ℝ)) * ‖A‖) ^ N * ((t / (N : ℝ)) * M.error (t / N))
      = t * (1 + (t / (N : ℝ)) * ‖A‖) ^ N * M.error (t / (N : ℝ)) := by
    calc (N : ℝ) * (1 + (t / (N : ℝ)) * ‖A‖) ^ N * ((t / (N : ℝ)) * M.error (t / N))
        = ((N : ℝ) * (t / (N : ℝ))) * (1 + (t / (N : ℝ)) * ‖A‖) ^ N * M.error (t / (N : ℝ)) := by
          ring
      _ = t * (1 + (t / (N : ℝ)) * ‖A‖) ^ N * M.error (t / (N : ℝ)) := by rw [hNt]
  rw [hcollapse]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexpb ht.le) (M.error_nonneg _)

/-- **The Euler limit of kernel powers.**  For a microscopic approximation of `A` on a bounded
feature `φ`, a fixed combination of feature coordinates pushed through `N` kernel steps of size
`t/N` converges uniformly in the state to the same combination of `e^{tA} φ`. -/
theorem tendstoUniformly_kernelPower_dotProduct [DecidableEq ι]
    (M : MicroscopicApproximation (B := B) φ A) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (c : ι → ℝ)
    (t : ℝ) (ht : 0 < t) :
    TendstoUniformly (fun (N : ℕ) x ↦ (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ c ⬝ᵥ φ y) x)
      (fun x ↦ c ⬝ᵥ (matrixExponential A t *ᵥ φ x)) atTop := by
  have hnorm : Tendsto (fun N : ℕ ↦ ‖(1 + (t / (N : ℝ)) • A) ^ N - matrixExponential A t‖)
      atTop (𝓝 0) := by
    have hconv := tendsto_iff_norm_sub_tendsto_zero.mp
      (BanachEulerExponential.euler_tends_exp (t • A))
    rw [← matrixExponential_eq_normedSpace_exp] at hconv
    refine hconv.congr fun N ↦ ?_
    rw [smul_smul, div_eq_mul_inv, mul_comm (N : ℝ)⁻¹ t]
  have herr : Tendsto (fun N : ℕ ↦ M.error (t / (N : ℝ))) atTop (𝓝 0) := by
    refine M.error_tendsto.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat t, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact Set.mem_Ioi.mpr (div_pos ht (by exact_mod_cast hN))
  have hδ : Tendsto (fun N : ℕ ↦ (∑ i, |c i|) * (t * Real.exp (t * ‖A‖) * M.error (t / (N : ℝ))
      + ‖(1 + (t / (N : ℝ)) • A) ^ N - matrixExponential A t‖ * C)) atTop (𝓝 0) := by
    have hlim := ((herr.const_mul (t * Real.exp (t * ‖A‖))).add (hnorm.mul_const C)).const_mul
      (∑ i, |c i|)
    rwa [mul_zero, zero_mul, add_zero, mul_zero] at hlim
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [eventually_gt_atTop 0, (tendsto_order.1 hδ).2 ε hε] with N hN hδN x
  refine lt_of_le_of_lt ?_ hδN
  have hlin : (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ c ⬝ᵥ φ y) x
      = c ⬝ᵥ fun i ↦ (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ φ y i) x := by
    simp only [dotProduct]
    exact iterate_apply_sum _ N c (fun i y ↦ φ y i) x
  have hsplit : (fun i ↦ (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ φ y i) x)
        - matrixExponential A t *ᵥ φ x
      = ((fun i ↦ (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ φ y i) x)
          - ((1 + (t / (N : ℝ)) • A) ^ N) *ᵥ φ x)
        + ((1 + (t / (N : ℝ)) • A) ^ N - matrixExponential A t) *ᵥ φ x := by
    rw [Matrix.sub_mulVec]
    abel
  have hvec : ‖(fun i ↦ (M.kernel (t / (N : ℝ))).apply^[N] (fun y ↦ φ y i) x)
        - matrixExponential A t *ᵥ φ x‖
      ≤ t * Real.exp (t * ‖A‖) * M.error (t / (N : ℝ))
        + ‖(1 + (t / (N : ℝ)) • A) ^ N - matrixExponential A t‖ * C := by
    rw [hsplit]
    refine (norm_add_le _ _).trans
      (add_le_add (norm_kernelPower_sub_euler_le_exp M t ht N hN x) ?_)
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (hφ x) (norm_nonneg _))
  beta_reduce
  rw [dist_comm, Real.dist_eq, hlin, ← dotProduct_sub]
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ i).trans hvec

end Abstract

/-! ## The neutral model -/

section Neutral

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- The budget-moment feature is bounded on states by the summed Taylor constant. -/
theorem norm_budgetMomentFeature_le (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele) :
    ‖budgetMomentFeature capacity x‖ ≤ featureBound rates capacity := by
  have hnn : 0 ≤ featureBound rates capacity :=
    Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec rates capacity ξ).1
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun ξ ↦ ?_
  have hspec := momentBound_spec rates capacity ξ
  rw [Real.norm_eq_abs]
  exact ((hspec.2.2 x.1 0 (abs_state_le_one x) (fun _ ↦ by norm_num) 0 le_rfl
    zero_le_one).1).trans hspec.2.1

/-- **The neutral Euler limit on configuration moments.**  Every combination of the
budget-respecting configuration moments, pushed through `N` neutral microscopic steps of size
`t/N`, converges uniformly in the state to the same combination of the dual propagator applied to
the state's moments. -/
theorem tendstoUniformly_kernelPower_momentPolynomial (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (c : BudgetConfiguration Deme Locus Allele capacity → ℝ) (t : ℝ)
    (ht : 0 < t) :
    TendstoUniformly
      (fun (N : ℕ) x ↦ (neutralMicroscopicKernel rates (t / (N : ℝ))).apply^[N]
        (fun y ↦ c ⬝ᵥ budgetMomentFeature capacity y) x)
      (fun x ↦ c ⬝ᵥ (matrixExponential (dualGenerator rates capacity) t
        *ᵥ budgetMomentFeature capacity x)) atTop :=
  tendstoUniformly_kernelPower_dotProduct (neutralMicroscopicApproximation rates capacity)
    (featureBound rates capacity) (norm_budgetMomentFeature_le rates capacity) c t ht

/-- The coefficients of a polynomial over the configurations of its support budget. -/
def supportCoefficients (ℓ₀ : Locus) (p : FrequencyPolynomial Deme Locus Allele) :
    BudgetConfiguration Deme Locus Allele (supportBudget ℓ₀ p) → ℝ :=
  fun η ↦ ∑ β ∈ p.support, if monomialConfiguration ℓ₀ β = η.1 then coeff β p else 0

/-- **NOTE1 §4.2a, the microscopic limit of the polynomial semigroup.**  For every polynomial
observable `f` and every `t > 0`, the neutral microscopic kernel iterated `N` times at step size
`t/N` converges uniformly to the neutral polynomial semigroup `T_t f`. -/
theorem tendstoUniformly_neutralPolynomialSemigroup (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (ht : 0 < t)
    (f : PolynomialSubspace Deme Locus Allele) :
    TendstoUniformly
      (fun (N : ℕ) ↦ (neutralMicroscopicKernel rates ((t : ℝ) / (N : ℝ))).apply^[N]
        ⇑(f : C(FrequencyState Deme Locus Allele, ℝ)))
      ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
      atTop := by
  have hf : ⇑(f : C(FrequencyState Deme Locus Allele, ℝ))
      = fun y ↦ supportCoefficients ℓ₀ (representative f)
          ⬝ᵥ budgetMomentFeature (supportBudget ℓ₀ (representative f)) y := by
    funext y
    conv_lhs => rw [← polynomialFunction_representative f]
    rw [polynomialFunction_apply, eval_eq_dotProduct ℓ₀ _ _
      (withinBudget_supportBudget ℓ₀ (representative f)) y]
    rfl
  have hT : ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
        : C(FrequencyState Deme Locus Allele, ℝ))
      = fun x ↦ supportCoefficients ℓ₀ (representative f)
          ⬝ᵥ (matrixExponential (dualGenerator rates (supportBudget ℓ₀ (representative f))) t
            *ᵥ budgetMomentFeature (supportBudget ℓ₀ (representative f)) x) := by
    funext x
    rw [neutralPolynomialSemigroup_apply, momentFunctional_eq_dotProduct rates ℓ₀ t x _ _
      (withinBudget_supportBudget ℓ₀ (representative f))]
    rfl
  rw [hf, hT]
  exact tendstoUniformly_kernelPower_momentPolynomial rates _ _ t (NNReal.coe_pos.mpr ht)

/-- The neutral polynomial semigroup contracts sup norms. -/
theorem norm_neutralPolynomialSemigroup_le (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0)
    (f : PolynomialSubspace Deme Locus Allele) :
    ‖(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))‖
      ≤ ‖(f : C(FrequencyState Deme Locus Allele, ℝ))‖ :=
  norm_le_of_nonneg_of_map_unit (PolynomialSubspace Deme Locus Allele).subtype
    ((PolynomialSubspace Deme Locus Allele).subtype ∘ₗ neutralPolynomialSemigroup rates ℓ₀ hap₀ t)
    ⟨1, one_mem_polynomialSubspace⟩ rfl (neutralPolynomialSemigroup_one rates ℓ₀ hap₀ t)
    (neutralPolynomialSemigroup_nonneg rates ℓ₀ hap₀ t) f

/-- The neutral semigroup extended continuously from the polynomial observables to all
continuous observables. -/
def neutralSemigroupExtension (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    C(FrequencyState Deme Locus Allele, ℝ) →L[ℝ] C(FrequencyState Deme Locus Allele, ℝ) :=
  denseExtension (PolynomialSubspace Deme Locus Allele) dense_polynomialSubspace
    (neutralPolynomialSemigroup rates ℓ₀ hap₀ t)
    (norm_neutralPolynomialSemigroup_le rates ℓ₀ hap₀ t)

/-- **The microscopic limit on every continuous observable.**  For every continuous observable
`g` and every `t > 0`, the neutral microscopic kernel iterated `N` times at step size `t/N`
converges uniformly to the extended neutral semigroup applied to `g`. -/
theorem tendstoUniformly_neutralSemigroupExtension (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (ht : 0 < t)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    TendstoUniformly
      (fun (N : ℕ) ↦ (neutralMicroscopicKernel rates ((t : ℝ) / (N : ℝ))).apply^[N] ⇑g)
      ⇑(neutralSemigroupExtension rates ℓ₀ hap₀ t g) atTop :=
  tendstoUniformly_iterate_extension _ dense_polynomialSubspace _ _
    (fun N : ℕ ↦ neutralMicroscopicKernel rates ((t : ℝ) / (N : ℝ))) (fun N ↦ N)
    (tendstoUniformly_neutralPolynomialSemigroup rates ℓ₀ hap₀ t ht) g

/-- The extended neutral semigroup is positive. -/
theorem neutralSemigroupExtension_nonneg (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (g : C(FrequencyState Deme Locus Allele, ℝ))
    (hg : 0 ≤ g) : 0 ≤ neutralSemigroupExtension rates ℓ₀ hap₀ t g :=
  denseExtension_nonneg _ dense_polynomialSubspace _ (norm_neutralPolynomialSemigroup_le rates ℓ₀
    hap₀ t) one_mem_polynomialSubspace (neutralPolynomialSemigroup_one rates ℓ₀ hap₀ t) g hg

/-- The extended neutral semigroup fixes the constant observable. -/
theorem neutralSemigroupExtension_one (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    neutralSemigroupExtension rates ℓ₀ hap₀ t 1 = 1 :=
  denseExtension_one _ dense_polynomialSubspace _ (norm_neutralPolynomialSemigroup_le rates ℓ₀
    hap₀ t) one_mem_polynomialSubspace (neutralPolynomialSemigroup_one rates ℓ₀ hap₀ t)

/-- **The neutral Markov kernel** at time `t`: the Riesz kernel of the extended neutral
semigroup. -/
def neutralMarkovKernel (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele) :=
  markovKernel (neutralSemigroupExtension rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_nonneg rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_one rates ℓ₀ hap₀ t)

/-- The neutral kernels are Markov kernels. -/
theorem isMarkovKernel_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    IsMarkovKernel (neutralMarkovKernel rates ℓ₀ hap₀ t) :=
  isMarkovKernel_markovKernel _ _ _

/-- The neutral kernel integrates every continuous observable to the extended semigroup. -/
theorem integral_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (x : FrequencyState Deme Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x)
      = neutralSemigroupExtension rates ℓ₀ hap₀ t g x :=
  integral_markovKernel _ _ _ x g

/-- The neutral kernel represents the neutral polynomial semigroup. -/
theorem integral_neutralMarkovKernel_polynomial (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0)
    (x : FrequencyState Deme Locus Allele) (f : PolynomialSubspace Deme Locus Allele) :
    ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x)
      = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
          : C(FrequencyState Deme Locus Allele, ℝ)) x := by
  rw [integral_neutralMarkovKernel, neutralSemigroupExtension, denseExtension_coe]

/-- **The neutral Markov semigroup law.**  The neutral kernels compose by
`K_{s+t} = K_t ∘ₖ K_s`. -/
theorem neutralMarkovKernel_add (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (s t : ℝ≥0) :
    neutralMarkovKernel rates ℓ₀ hap₀ (s + t)
      = neutralMarkovKernel rates ℓ₀ hap₀ t ∘ₖ neutralMarkovKernel rates ℓ₀ hap₀ s :=
  markovKernel_add (fun t ↦ neutralSemigroupExtension rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_nonneg rates ℓ₀ hap₀) (neutralSemigroupExtension_one rates ℓ₀ hap₀)
    (denseExtension_add _ dense_polynomialSubspace (neutralPolynomialSemigroup rates ℓ₀ hap₀)
      (norm_neutralPolynomialSemigroup_le rates ℓ₀ hap₀)
      (neutralPolynomialSemigroup_add rates ℓ₀ hap₀))
    s t

/-- **NOTE1 §4.2a, convergence in law.**  For every `t > 0` and every continuous observable `g`,
the neutral microscopic chain run for `N` steps of size `t/N` has `K_{t/N}^N g` converging
uniformly in the initial state to the integral of `g` against the neutral Markov kernel. -/
theorem tendstoUniformly_integral_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (ht : 0 < t)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    TendstoUniformly
      (fun (N : ℕ) ↦ (neutralMicroscopicKernel rates ((t : ℝ) / (N : ℝ))).apply^[N] ⇑g)
      (fun x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x)) atTop := by
  have hlim : (fun x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x))
      = ⇑(neutralSemigroupExtension rates ℓ₀ hap₀ t g) :=
    funext fun x ↦ integral_neutralMarkovKernel rates ℓ₀ hap₀ t x g
  rw [hlim]
  exact tendstoUniformly_neutralSemigroupExtension rates ℓ₀ hap₀ t ht g

end Neutral

end

end Descent.Portability.NeutralMicroscopicEulerLimit
