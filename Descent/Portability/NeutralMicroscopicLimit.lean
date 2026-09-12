/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralPolynomialSemigroup
import Descent.Portability.PartialHaplotypeMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# The neutral microscopic chain converges to the neutral diffusion

NOTE1 §4.2a derives the neutral Markov semigroup from physical microscopic kernels through the
uniform Euler limit `K_h^{⌊t/h⌋} f → T_t f`.  This module proves that limit for the neutral
microscopic kernel of `PartialHaplotypeMicroscopicApproximation` and builds the Markov kernels
from it.

The feature limit.  For a `MicroscopicApproximation` of a matrix `A` whose features are bounded,
the Euler iterates of its kernels converge to the semigroup on the features,
`K_h^{⌊t/h⌋} φ → e^{tA} φ`, uniformly in the state as `h ↓ 0`
(`tendstoUniformly_iterate_feature`).  The proof is the telescoping estimate NOTE1 (5) on
observables.  If one kernel step moves every feature coordinate by a matrix `P` up to `δ`, and
`‖P^k‖ ≤ C` for `k < n`, then `n` steps move it by `P^n` up to `n C δ`
(`abs_iterate_apply_sub_pow_mulVec_le`): a kernel contracts uniform distances and acts on a
combination of features through its coefficients (`apply_dotProduct`).  The matrix is
`P = e^{hA}`, so `P^k = e^{khA}` is bounded by the maximum of `‖e^{sA}‖` over `[0, t]`, and
`δ = h ε(h) + ‖e^{hA} - 1 - hA‖ M`, where `‖e^{hA} - 1 - hA‖ = o(h)` is the derivative of the
exponential at zero.  The grid time `h ⌊t/h⌋` tends to `t`.  Linear combinations of features
converge as well (`tendstoUniformly_iterate_dotProduct`).

The neutral instance.  On configuration moments the neutral microscopic chain converges to the
dual semigroup, `K_h^{⌊t/h⌋} H_ξ → (e^{tQ} H)_ξ`
(`tendstoUniformly_iterate_momentPolynomial`).  A polynomial observable is a coefficient vector
dotted with the configuration moments of a budget containing its monomials, and its image under
the neutral polynomial semigroup is the same vector dotted with the evolved moments, so the chain
converges to the semigroup on every polynomial observable
(`tendstoUniformly_iterate_neutralPolynomialSemigroup`).

The kernels.  `PolynomialFellerExtension.markov_of_euler_tendstoUniformly` turns the uniform
Euler limit into positivity, constant preservation and contraction; `FellerMarkovKernel` builds
Markov kernels from the extended operators; and
`PolynomialFellerExtension.euler_tendstoUniformly_extension` carries the limit to every
continuous observable (`exists_markovKernel_of_euler_tendstoUniformly`).  For every neutral model
there are Markov kernels that compose by `K_{s+t} = K_t ∘ₖ K_s`, have the neutral diffusion
generator on configuration moments, and are the uniform limit of the microscopic chain on every
continuous observable (`exists_neutralMarkovKernel_tendstoUniformly`).  Positivity comes from the
Euler limit alone; `NeutralPolynomialPositivity` proves it through the realization body instead.

Scope.  The limit is taken along the grid `⌊t/h⌋` for the kernels of
`PartialHaplotypeMicroscopicApproximation`, with rates constant in time; no rate of convergence
is stated.

## Empirical status

None.  The bodies here are analysis: telescoping estimates for finite mixture kernels, limits of
matrix exponentials, and integrals against kernels built from a supplied operator, so no
measurement on any population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralMicroscopicLimit

open Filter Topology MeasureTheory ProbabilityTheory MvPolynomial
open Descent.Coalescent FiniteMixtureKernel PolynomialFellerExtension FellerKernelRepresentation
  FellerMarkovKernel PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup NeutralFellerGenerator NeutralMomentSemigroup
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

/-! ## The Euler limit on features -/

section Feature

variable {ι B Y : Type*} [Fintype ι] [Fintype B]

/-- A kernel acts on a linear combination of feature coordinates through its coefficients. -/
theorem apply_dotProduct (K : FiniteMixtureKernel B Y) (c : ι → ℝ) (φ : Y → ι → ℝ) (x : Y) :
    K.apply (fun y ↦ c ⬝ᵥ φ y) x = c ⬝ᵥ fun i ↦ K.apply (fun y ↦ φ y i) x := by
  simp only [FiniteMixtureKernel.apply, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- Iterating a kernel on a linear combination of feature coordinates acts through the
coefficients. -/
theorem iterate_apply_dotProduct (K : FiniteMixtureKernel B Y) (c : ι → ℝ) (φ : Y → ι → ℝ)
    (n : ℕ) (x : Y) :
    K.apply^[n] (fun y ↦ c ⬝ᵥ φ y) x = c ⬝ᵥ fun i ↦ K.apply^[n] (fun y ↦ φ y i) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hfun : K.apply^[n] (fun y ↦ c ⬝ᵥ φ y)
        = fun y ↦ c ⬝ᵥ fun i ↦ K.apply^[n] (fun z ↦ φ z i) y := funext ih
    rw [Function.iterate_succ_apply', hfun, apply_dotProduct]
    congr 1
    funext i
    rw [Function.iterate_succ_apply']

variable [DecidableEq ι]

/-- **The telescoping estimate on observables.**  If one kernel step moves every feature
coordinate by the matrix `P` up to `δ`, and `‖P^k‖ ≤ C` for every `k < n`, then `n` kernel steps
move every feature coordinate by `P^n` up to `n C δ`. -/
theorem abs_iterate_apply_sub_pow_mulVec_le (K : FiniteMixtureKernel B Y) (φ : Y → ι → ℝ)
    (P : Matrix ι ι ℝ) (δ C : ℝ)
    (hδ : ∀ x i, |K.apply (fun y ↦ φ y i) x - (P *ᵥ φ x) i| ≤ δ) (n : ℕ)
    (hC : ∀ k < n, ‖P ^ k‖ ≤ C) (x : Y) (i : ι) :
    |K.apply^[n] (fun y ↦ φ y i) x - (P ^ n *ᵥ φ x) i| ≤ n * C * δ := by
  have key : ∀ m, m ≤ n → ∀ x i,
      |K.apply^[m] (fun y ↦ φ y i) x - (P ^ m *ᵥ φ x) i| ≤ m * C * δ := by
    intro m
    induction m with
    | zero =>
      intro _ x i
      simp
    | succ m ih =>
      intro hm x i
      have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ x i)
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.lt_of_lt_of_le m.succ_pos hm))
      have hmix : K.apply (fun y ↦ (P ^ m *ᵥ φ y) i) x
          = (P ^ m *ᵥ fun j ↦ K.apply (fun y ↦ φ y j) x) i :=
        apply_dotProduct K (fun j ↦ (P ^ m) i j) φ x
      have hsplit : K.apply^[m + 1] (fun y ↦ φ y i) x - (P ^ (m + 1) *ᵥ φ x) i
          = (K.apply (K.apply^[m] fun y ↦ φ y i) x - K.apply (fun y ↦ (P ^ m *ᵥ φ y) i) x)
            + (P ^ m *ᵥ ((fun j ↦ K.apply (fun y ↦ φ y j) x) - P *ᵥ φ x)) i := by
        rw [Function.iterate_succ_apply', hmix, pow_succ, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_sub, Pi.sub_apply]
        ring
      have hfirst : |K.apply (K.apply^[m] fun y ↦ φ y i) x
          - K.apply (fun y ↦ (P ^ m *ᵥ φ y) i) x| ≤ m * C * δ :=
        K.apply_sub_le _ _ _ (fun y ↦ ih (Nat.le_of_succ_le hm) y i) x
      have hvec : ‖(fun j ↦ K.apply (fun y ↦ φ y j) x) - P *ᵥ φ x‖ ≤ δ :=
        (pi_norm_le_iff_of_nonneg hδ0).mpr fun j ↦ by
          rw [Pi.sub_apply, Real.norm_eq_abs]
          exact hδ x j
      have hsecond : |(P ^ m *ᵥ ((fun j ↦ K.apply (fun y ↦ φ y j) x) - P *ᵥ φ x)) i|
          ≤ C * δ := by
        rw [← Real.norm_eq_abs]
        refine (norm_le_pi_norm _ i).trans ((Matrix.linfty_opNorm_mulVec _ _).trans ?_)
        exact mul_le_mul (hC m (Nat.lt_of_succ_le hm)) hvec (norm_nonneg _) hC0
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      calc |K.apply (K.apply^[m] fun y ↦ φ y i) x - K.apply (fun y ↦ (P ^ m *ᵥ φ y) i) x|
            + |(P ^ m *ᵥ ((fun j ↦ K.apply (fun y ↦ φ y j) x) - P *ᵥ φ x)) i|
          ≤ m * C * δ + C * δ := add_le_add hfirst hsecond
        _ = ((m + 1 : ℕ) : ℝ) * C * δ := by push_cast; ring
  exact key n le_rfl x i

/-- **The microscopic chain converges to the semigroup on features.**  For a microscopic
approximation of `A` whose features are bounded by `M`, the Euler iterates `K_h^{⌊t/h⌋}` of its
kernels converge to `e^{tA}` on the features, uniformly in the state, as `h ↓ 0`. -/
theorem tendstoUniformly_iterate_feature (φ : Y → ι → ℝ) (A : Matrix ι ι ℝ)
    (approx : MicroscopicApproximation (B := B) φ A) (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ)
    (ht : 0 ≤ t) :
    TendstoUniformly (fun h x i ↦ (approx.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x)
      (fun x ↦ matrixExponential A t *ᵥ φ x) (𝓝[>] 0) := by
  have hEcont : Continuous fun s : ℝ ↦ NormedSpace.exp ℝ (s • A) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hEcont.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, ht⟩)
  have hderiv : Tendsto (fun h : ℝ ↦ ‖h⁻¹ • (NormedSpace.exp ℝ (h • A) - 1) - A‖) (𝓝[>] 0)
      (𝓝 0) := by
    have h0 := (hasDerivAt_exp_smul_const A (0 : ℝ)).tendsto_slope_zero
    simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h0
    have h1 := (tendsto_sub_nhds_zero_iff.mpr h0).mono_left
      (nhdsWithin_mono (0 : ℝ) fun h hh ↦ Set.mem_compl_singleton_iff.mpr (ne_of_gt hh))
    exact tendsto_zero_iff_norm_tendsto_zero.mp h1
  have hgrid : Tendsto (fun h : ℝ ↦ (⌊t / h⌋₊ : ℝ) * h) (𝓝[>] 0) (𝓝 t) := by
    have hlow : Tendsto (fun h : ℝ ↦ t - h) (𝓝 0) (𝓝 (t - 0)) :=
      (continuous_sub_left t).tendsto 0
    rw [sub_zero] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hfloor := (div_lt_iff₀ (show (0 : ℝ) < h from hh)).mp (Nat.lt_floor_add_one (t / h))
      rw [add_mul, one_mul] at hfloor
      linarith
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (le_div_iff₀ (show (0 : ℝ) < h from hh)).mp
        (Nat.floor_le (div_nonneg ht (le_of_lt hh)))
  have hexp : Tendsto (fun h : ℝ ↦
      ‖NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) - NormedSpace.exp ℝ (t • A)‖) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((hEcont.tendsto t).comp hgrid)
  have hbound : Tendsto (fun h : ℝ ↦
      C * t * (approx.error h + ‖h⁻¹ • (NormedSpace.exp ℝ (h • A) - 1) - A‖ * M)
        + ‖NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) - NormedSpace.exp ℝ (t • A)‖ * M)
      (𝓝[>] 0) (𝓝 0) := by
    have h := ((approx.error_tendsto.add (hderiv.mul_const M)).const_mul (C * t)).add
      (hexp.mul_const M)
    simpa only [zero_mul, add_zero, mul_zero] using h
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, hbound.eventually (gt_mem_nhds hε)] with h hh hlt x
  have hh0 : (0 : ℝ) < h := hh
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  have hn : (⌊t / h⌋₊ : ℝ) * h ≤ t :=
    (le_div_iff₀ hh0).mp (Nat.floor_le (div_nonneg ht hh0.le))
  have hpow : ∀ k : ℕ,
      NormedSpace.exp ℝ (h • A) ^ k = NormedSpace.exp ℝ (((k : ℝ) * h) • A) := fun k ↦ by
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hpowle : ∀ k < ⌊t / h⌋₊, ‖NormedSpace.exp ℝ (h • A) ^ k‖ ≤ C := fun k hk ↦ by
    rw [hpow k]
    refine hC _ ⟨mul_nonneg (Nat.cast_nonneg k) hh0.le, ?_⟩
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.le) hh0.le).trans hn
  obtain ⟨r, hr⟩ : ∃ r, r = ‖h⁻¹ • (NormedSpace.exp ℝ (h • A) - 1) - A‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact norm_nonneg _
  have hrem : ‖NormedSpace.exp ℝ (h • A) - 1 - h • A‖ = h * r := by
    have hsmul : NormedSpace.exp ℝ (h • A) - 1 - h • A
        = h • (h⁻¹ • (NormedSpace.exp ℝ (h • A) - 1) - A) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hh0.ne', one_smul]
    rw [hsmul, norm_smul, Real.norm_eq_abs, abs_of_pos hh0, hr]
  have hstep : ∀ y j, |(approx.kernel h).apply (fun z ↦ φ z j) y
      - (NormedSpace.exp ℝ (h • A) *ᵥ φ y) j| ≤ h * approx.error h + h * r * M := by
    intro y j
    have hsplit : (approx.kernel h).apply (fun z ↦ φ z j) y
          - (NormedSpace.exp ℝ (h • A) *ᵥ φ y) j
        = ((approx.kernel h).apply (fun z ↦ φ z j) y - φ y j - h * (A *ᵥ φ y) j)
          + -((NormedSpace.exp ℝ (h • A) - 1 - h • A) *ᵥ φ y) j := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add (approx.expansion h hh0 y j) ?_)
    rw [abs_neg, ← Real.norm_eq_abs, ← hrem]
    exact (norm_le_pi_norm _ j).trans ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)))
  have hiter : ∀ i, |(approx.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x
      - (NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) *ᵥ φ x) i|
        ≤ C * t * (approx.error h + r * M) := by
    intro i
    rw [← hpow]
    refine (abs_iterate_apply_sub_pow_mulVec_le (approx.kernel h) φ _ _ C hstep _ hpowle x
      i).trans ?_
    calc (⌊t / h⌋₊ : ℝ) * C * (h * approx.error h + h * r * M)
        = C * ((⌊t / h⌋₊ : ℝ) * h) * (approx.error h + r * M) := by ring
      _ ≤ C * t * (approx.error h + r * M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC0)
          (add_nonneg (approx.error_nonneg h) (mul_nonneg hr0 hM0))
  have hfar : ‖matrixExponential A t *ᵥ φ x
      - NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) *ᵥ φ x‖
        ≤ ‖NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) - NormedSpace.exp ℝ (t • A)‖ * M := by
    rw [matrixExponential_eq_normedSpace_exp, ← Matrix.sub_mulVec, norm_sub_rev]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _))
  have hnear : ‖NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) *ᵥ φ x
      - (fun i ↦ (approx.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x)‖
        ≤ C * t * (approx.error h + r * M) := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hC0 ht)
      (add_nonneg (approx.error_nonneg h) (mul_nonneg hr0 hM0)))).mpr fun i ↦ ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
    exact hiter i
  rw [← hr] at hlt
  rw [dist_eq_norm]
  calc ‖matrixExponential A t *ᵥ φ x
        - (fun i ↦ (approx.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x)‖
      ≤ ‖matrixExponential A t *ᵥ φ x - NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) *ᵥ φ x‖
        + ‖NormedSpace.exp ℝ (((⌊t / h⌋₊ : ℝ) * h) • A) *ᵥ φ x
          - (fun i ↦ (approx.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

/-- **Linear combinations of features converge.**  For a microscopic approximation of `A` whose
features are bounded, `K_h^{⌊t/h⌋} (c ⬝ φ) → c ⬝ e^{tA} φ` uniformly in the state as `h ↓ 0`. -/
theorem tendstoUniformly_iterate_dotProduct (φ : Y → ι → ℝ) (A : Matrix ι ι ℝ)
    (approx : MicroscopicApproximation (B := B) φ A) (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ)
    (ht : 0 ≤ t) (c : ι → ℝ) :
    TendstoUniformly (fun h ↦ (approx.kernel h).apply^[⌊t / h⌋₊] fun y ↦ c ⬝ᵥ φ y)
      (fun x ↦ c ⬝ᵥ (matrixExponential A t *ᵥ φ x)) (𝓝[>] 0) := by
  let L : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v ↦ c ⬝ᵥ v
      map_add' := fun u v ↦ by simp only [dotProduct_add]
      map_smul' := fun a v ↦ by simp only [dotProduct_smul, RingHom.id_apply] }
  have huc : UniformContinuous fun v : ι → ℝ ↦ c ⬝ᵥ v :=
    (LinearMap.toContinuousLinearMap L).uniformContinuous
  have hfun : (fun h ↦ (approx.kernel h).apply^[⌊t / h⌋₊] fun y ↦ c ⬝ᵥ φ y)
      = fun h ↦ (fun v : ι → ℝ ↦ c ⬝ᵥ v)
          ∘ fun x i ↦ (approx.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x :=
    funext fun h ↦ funext fun x ↦ iterate_apply_dotProduct (approx.kernel h) c φ _ x
  rw [hfun]
  exact huc.comp_tendstoUniformly (tendstoUniformly_iterate_feature φ A approx M hM t ht)

end Feature

/-! ## Markov kernels from the Euler limit -/

section Kernel

variable {Y B : Type*} [Fintype B] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace.PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **NOTE1 §4.2a through the Euler limit.**  If the Euler iterates of finite mixture kernels
converge uniformly to a semigroup of linear operators on a dense subspace containing the
constants, then there are Markov kernels that compose by `K_{s+t} = K_t ∘ₖ K_s`, represent the
semigroup, and are the uniform limit of the iterates on every continuous observable. -/
theorem exists_markovKernel_of_euler_tendstoUniformly (V : Submodule ℝ C(Y, ℝ))
    (hV : Dense (V : Set C(Y, ℝ))) (h1 : (1 : C(Y, ℝ)) ∈ V) (T : ℝ≥0 → V →ₗ[ℝ] V)
    (hsemi : ∀ s t, T (s + t) = T s ∘ₗ T t) (K : ℝ → FiniteMixtureKernel B Y)
    (hlim : ∀ (t : ℝ≥0) (f : V), TendstoUniformly
      (fun h ↦ (K h).apply^[⌊(t : ℝ) / h⌋₊] ⇑(f : C(Y, ℝ))) ⇑(T t f : C(Y, ℝ)) (𝓝[>] 0)) :
    ∃ P : ℝ≥0 → Kernel Y Y, (∀ t, IsMarkovKernel (P t)) ∧ (∀ s t, P (s + t) = P t ∘ₖ P s) ∧
      (∀ t y (f : V), ∫ z, (f : C(Y, ℝ)) z ∂(P t y) = (T t f : C(Y, ℝ)) y) ∧
      ∀ (t : ℝ≥0) (g : C(Y, ℝ)), TendstoUniformly
        (fun h ↦ (K h).apply^[⌊(t : ℝ) / h⌋₊] ⇑g) (fun y ↦ ∫ z, g z ∂(P t y)) (𝓝[>] 0) := by
  have hmarkov := fun t ↦ markov_of_euler_tendstoUniformly V h1 (T t) K t (hlim t)
  have hT : ∀ t (f : V), ‖(T t f : C(Y, ℝ))‖ ≤ ‖(f : C(Y, ℝ))‖ := fun t ↦ (hmarkov t).2.2
  have hS : ∀ t g, 0 ≤ g → 0 ≤ denseExtension V hV (T t) (hT t) g := fun t ↦
    denseExtension_nonneg V hV (T t) (hT t) h1 (hmarkov t).2.1
  have hS1 : ∀ t, denseExtension V hV (T t) (hT t) 1 = 1 := fun t ↦
    denseExtension_one V hV (T t) (hT t) h1 (hmarkov t).2.1
  refine ⟨fun t ↦ markovKernel (denseExtension V hV (T t) (hT t)) (hS t) (hS1 t),
    fun t ↦ isMarkovKernel_markovKernel _ _ _,
    fun s t ↦ markovKernel_add (fun t ↦ denseExtension V hV (T t) (hT t)) hS hS1
      (denseExtension_add V hV T hT hsemi) s t,
    fun t y f ↦ integral_kernelMeasure_denseExtension V hV h1 (T t) (hT t) (hmarkov t).2.1 y f,
    fun t g ↦ ?_⟩
  have hext := euler_tendstoUniformly_extension V hV h1 (T t) K t (hlim t) g
  have htarget : ⇑(denseExtension V hV (T t) (hT t) g)
      = fun y ↦ ∫ z, g z ∂(markovKernel (denseExtension V hV (T t) (hT t)) (hS t) (hS1 t) y) :=
    funext fun y ↦ (integral_markovKernel _ _ _ y g).symm
  rw [htarget] at hext
  exact hext

end Kernel

/-! ## The neutral model -/

section Neutral

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The neutral microscopic chain converges on configuration moments.**  The Euler iterates of
`neutralMicroscopicKernel` carry every budget-respecting configuration moment to the dual
semigroup, `K_h^{⌊t/h⌋} H_ξ → (e^{tQ} H)_ξ`, uniformly in the state as `h ↓ 0`. -/
theorem tendstoUniformly_iterate_momentPolynomial (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    TendstoUniformly
      (fun h ↦ (neutralMicroscopicKernel rates h).apply^[⌊t / h⌋₊]
        fun y ↦ eval y.1 (momentPolynomial ξ.1))
      (fun x ↦ (matrixExponential (dualGenerator rates capacity) t *ᵥ momentVector capacity x) ξ)
      (𝓝[>] 0) := by
  obtain ⟨M, hM⟩ := (isCompact_univ :
      IsCompact (Set.univ : Set (FrequencyState Deme Locus Allele))).exists_bound_of_continuousOn
    (continuous_budgetMomentFeature capacity).continuousOn
  have h := tendstoUniformly_iterate_dotProduct (budgetMomentFeature capacity)
    (dualGenerator rates capacity) (neutralMicroscopicApproximation rates capacity) M
    (fun x ↦ hM x (Set.mem_univ x)) t ht (Pi.single ξ 1)
  simp only [single_dotProduct, one_mul] at h
  exact h

/-- **The neutral microscopic chain converges to the neutral polynomial semigroup.**  For every
polynomial observable `f`, `K_h^{⌊t/h⌋} f → T_t f` uniformly in the state as `h ↓ 0`. -/
theorem tendstoUniformly_iterate_neutralPolynomialSemigroup
    (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (t : ℝ≥0) (f : PolynomialSubspace Deme Locus Allele) :
    TendstoUniformly
      (fun h ↦ (neutralMicroscopicKernel rates h).apply^[⌊(t : ℝ) / h⌋₊]
        ⇑(f : C(FrequencyState Deme Locus Allele, ℝ)))
      ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
      (𝓝[>] 0) := by
  have key : ∀ capacity : Locus → ℕ,
      (∀ β ∈ (representative f).support, WithinBudget capacity (monomialConfiguration ℓ₀ β)) →
      TendstoUniformly
        (fun h ↦ (neutralMicroscopicKernel rates h).apply^[⌊(t : ℝ) / h⌋₊]
          ⇑(f : C(FrequencyState Deme Locus Allele, ℝ)))
        ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
        (𝓝[>] 0) := by
    intro capacity hp
    obtain ⟨M, hM⟩ := (isCompact_univ :
        IsCompact (Set.univ : Set (FrequencyState Deme Locus Allele))).exists_bound_of_continuousOn
      (continuous_budgetMomentFeature capacity).continuousOn
    have hobs : ⇑(f : C(FrequencyState Deme Locus Allele, ℝ)) = fun y ↦
        (fun η : BudgetConfiguration Deme Locus Allele capacity ↦
          ∑ β ∈ (representative f).support,
            if monomialConfiguration ℓ₀ β = η.1 then coeff β (representative f) else 0)
          ⬝ᵥ budgetMomentFeature capacity y := by
      funext y
      rw [← polynomialFunction_representative f, polynomialFunction_apply]
      exact eval_eq_dotProduct ℓ₀ capacity _ hp y
    have hsemigroup : ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f :
        C(FrequencyState Deme Locus Allele, ℝ)) = fun x ↦
        (fun η : BudgetConfiguration Deme Locus Allele capacity ↦
          ∑ β ∈ (representative f).support,
            if monomialConfiguration ℓ₀ β = η.1 then coeff β (representative f) else 0)
          ⬝ᵥ (matrixExponential (dualGenerator rates capacity) t
            *ᵥ budgetMomentFeature capacity x) := by
      funext x
      rw [neutralPolynomialSemigroup_apply]
      exact momentFunctional_eq_dotProduct rates ℓ₀ t x capacity _ hp
    rw [hobs, hsemigroup]
    exact tendstoUniformly_iterate_dotProduct (budgetMomentFeature capacity)
      (dualGenerator rates capacity) (neutralMicroscopicApproximation rates capacity) M
      (fun x ↦ hM x (Set.mem_univ x)) t t.2 _
  exact key (fun _ ↦ ∑ β ∈ (representative f).support, Multiset.card (monomialConfiguration ℓ₀ β))
    fun β hβ _ ↦ (Multiset.countP_le_card _ _).trans (Finset.single_le_sum
      (f := fun β ↦ Multiset.card (monomialConfiguration ℓ₀ β)) (fun _ _ ↦ Nat.zero_le _) hβ)

/-- **The neutral diffusion is the limit of the microscopic chain.**  For every neutral model
there are Markov kernels on the frequency states that compose by `K_{s+t} = K_t ∘ₖ K_s`, whose
generator on budget-respecting configuration moments is the neutral diffusion generator of
NOTE1 (19), and that are the uniform limit of the neutral microscopic chain on every continuous
observable: `K_h^{⌊t/h⌋} g → ∫ g dK_t(x, ·)` uniformly in `x` as `h ↓ 0`. -/
theorem exists_neutralMarkovKernel_tendstoUniformly (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) :
    ∃ K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele),
      (∀ t, IsMarkovKernel (K t)) ∧ (∀ s t, K (s + t) = K t ∘ₖ K s) ∧
      (∀ t x (ξ : BudgetConfiguration Deme Locus Allele capacity),
        HasDerivWithinAt
          (fun s : ℝ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(K s.toNNReal x))
          (∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x))
          (Set.Ici 0) t) ∧
      ∀ (t : ℝ≥0) (g : C(FrequencyState Deme Locus Allele, ℝ)),
        TendstoUniformly (fun h ↦ (neutralMicroscopicKernel rates h).apply^[⌊(t : ℝ) / h⌋₊] ⇑g)
          (fun x ↦ ∫ y, g y ∂(K t x)) (𝓝[>] 0) := by
  obtain ⟨K, hK, hsg, hrep, hlim⟩ := exists_markovKernel_of_euler_tendstoUniformly
    (PolynomialSubspace Deme Locus Allele) dense_polynomialSubspace one_mem_polynomialSubspace
    (neutralPolynomialSemigroup rates ℓ₀ hap₀) (neutralPolynomialSemigroup_add rates ℓ₀ hap₀)
    (neutralMicroscopicKernel rates)
    (tendstoUniformly_iterate_neutralPolynomialSemigroup rates ℓ₀ hap₀)
  haveI : ∀ t, IsMarkovKernel (K t) := hK
  exact ⟨K, hK, hsg, fun t x ξ ↦ hasDerivWithinAt_integral_momentPolynomial rates capacity K
    (fun t x ξ ↦ (hrep t x _).trans
      (neutralPolynomialSemigroup_momentPolynomial rates ℓ₀ hap₀ capacity t ξ x)) t x ξ, hlim⟩

end Neutral

end

end Descent.Portability.NeutralMicroscopicLimit
