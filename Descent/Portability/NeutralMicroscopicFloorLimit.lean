/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralMicroscopicEulerLimit

assert_below Descent.Decision Descent.Program

/-!
# The floor form of the neutral microscopic limit

NOTE1 §4.2a states the microscopic limit as `h ↓ 0` with `⌊t/h⌋` kernel steps of size `h`, which
is also the hypothesis of `PolynomialFellerExtension.markov_of_euler_tendstoUniformly`.
`NeutralMicroscopicEulerLimit` proves the limit along `N` steps of size `t/N`; this module proves
the floor form.

Euler products with a varying step count.  In a complete normed algebra, `(1 + (u/N) a)^N`
converges to `exp(v a)` whenever `N → ∞` and `u → v` (`varying_euler_tends_exp`), by dominated
convergence of the binomial series, as `RealVaryingEuler` does for real numbers.  The step count
`N = ⌊t/h⌋` diverges and the elapsed time `N h` tends to `t` as `h ↓ 0` (`tendsto_floor_div`,
`tendsto_floor_div_mul`), so the Euler products `(1 + hA)^⌊t/h⌋` converge to `e^{tA}`
(`tendsto_norm_euler_floor_sub`).

Kernel powers.  Since `⌊t/h⌋ h ≤ t`, after `⌊t/h⌋` steps the telescoping estimate of
`NeutralMicroscopicEulerLimit` is at most `t e^{t‖A‖} ε(h)`
(`norm_kernelPower_sub_euler_le_floor`).  A fixed combination of feature coordinates is within the
combined coefficient mass of the vector error (`abs_kernelPower_dotProduct_sub_le`), so it
converges uniformly in the state (`tendstoUniformly_kernelPower_floor_dotProduct`).

The neutral model.  A polynomial observable and its image under the neutral polynomial semigroup
are one combination of configuration moments and of the dual propagator
(`coe_polynomialSubspace_eq_dotProduct`, `coe_neutralPolynomialSemigroup_eq_dotProduct`).  Hence
`K_h^{⌊t/h⌋} f → T_t f` uniformly as `h ↓ 0`
(`tendstoUniformly_neutralPolynomialSemigroup_floor`).  This discharges the hypothesis of
`markov_of_euler_tendstoUniformly`, which derives positivity, constant preservation and the
contraction bound of the neutral polynomial semigroup from the microscopic kernel alone
(`neutralPolynomialSemigroup_markov_of_euler`).  Through `euler_tendstoUniformly_extension`,
`K_h^{⌊t/h⌋} g → ∫ g dK_t` uniformly for every continuous observable `g`
(`tendstoUniformly_integral_neutralMarkovKernel_floor`).

Scope.  The time `t > 0` is fixed.

## Empirical status

None.  The bodies here are analysis of finite mixture kernels, binomial series and matrix
exponentials of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralMicroscopicFloorLimit

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup NeutralPolynomialPositivity
  PartialHaplotypeMicroscopicApproximation FiniteMixtureKernel PolynomialFellerExtension
  NeutralMicroscopicEulerLimit
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

/-! ## Euler products with a varying step count -/

/-- **The varying Euler limit in a complete normed algebra.**  If the step counts `N` diverge and
the numerators `u` converge to `v`, then `(1 + (u/N) a)^N` converges to `exp(v a)`. -/
theorem varying_euler_tends_exp {E α : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    [CompleteSpace E] {l : Filter α} (N : α → ℕ) (u : α → ℝ) (v : ℝ) (a : E)
    (hN : Tendsto N l atTop) (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun m ↦ (1 + (u m / (N m : ℝ)) • a) ^ N m) l (𝓝 (NormedSpace.exp ℝ (v • a))) := by
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m in l, |u m| ≤ C := by
    refine ⟨|v| + 1, by positivity, ?_⟩
    filter_upwards [hu.eventually (Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1))]
      with m hm
    have hm' : |u m - v| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hm
    obtain ⟨h1, h2⟩ := abs_lt.mp hm'
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [le_abs_self v, neg_abs_le v]
  have hsum : Summable fun k : ℕ ↦ ‖((k.factorial : ℝ)⁻¹) • (C • a) ^ k‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (C • a)
  have hdom : ∀ᶠ m in l, ∀ k : ℕ, ‖(((N m).choose k : ℝ) / (N m : ℝ) ^ k * u m ^ k) • a ^ k‖
      ≤ ‖((k.factorial : ℝ)⁻¹) • (C • a) ^ k‖ := by
    filter_upwards [hbound, hN.eventually (eventually_gt_atTop 0)] with m hm hmN k
    have hL : ‖(((N m).choose k : ℝ) / (N m : ℝ) ^ k * u m ^ k) • a ^ k‖
        = ((N m).choose k : ℝ) / (N m : ℝ) ^ k * |u m| ^ k * ‖a ^ k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ ((N m).choose k : ℝ) / (N m : ℝ) ^ k by positivity)]
    have hR : ‖((k.factorial : ℝ)⁻¹) • (C • a) ^ k‖
        = (k.factorial : ℝ)⁻¹ * C ^ k * ‖a ^ k‖ := by
      rw [smul_pow, smul_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hC k))]
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (BanachEulerExponential.coefficient_bound (N m) k hmN)
      (pow_le_pow_left₀ (abs_nonneg _) hm k) (by positivity) (by positivity)) (norm_nonneg _)
  have hlim : Tendsto
      (fun m ↦ ∑' k : ℕ, (((N m).choose k : ℝ) / (N m : ℝ) ^ k * u m ^ k) • a ^ k) l
      (𝓝 (∑' k : ℕ, ((k.factorial : ℝ)⁻¹ * v ^ k) • a ^ k)) :=
    tendsto_tsum_of_dominated_convergence hsum
      (fun k ↦ (((BanachEulerExponential.coefficient_limit k).comp hN).mul
        (hu.pow k)).smul_const (a ^ k)) hdom
  have hexp : (∑' k : ℕ, ((k.factorial : ℝ)⁻¹ * v ^ k) • a ^ k)
      = NormedSpace.exp ℝ (v • a) := by
    rw [NormedSpace.exp_eq_tsum]
    exact tsum_congr fun k ↦ by rw [smul_pow, smul_smul]
  rw [hexp] at hlim
  refine hlim.congr fun m ↦ ?_
  have hsmul : (u m / (N m : ℝ)) • a = (N m : ℝ)⁻¹ • (u m • a) := by
    rw [smul_smul, div_eq_mul_inv, mul_comm]
  rw [hsmul, BanachEulerExponential.euler_eq_series]
  exact tsum_congr fun k ↦ by rw [smul_pow, smul_smul]

/-- The number of steps `⌊t/h⌋` diverges as the step size decreases to zero. -/
theorem tendsto_floor_div (t : ℝ) (ht : 0 < t) :
    Tendsto (fun h : ℝ ↦ ⌊t / h⌋₊) (𝓝[>] 0) atTop := by
  refine (tendsto_nat_floor_atTop.comp
    ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop ht)).congr fun h ↦ ?_
  simp only [Function.comp_apply, div_eq_mul_inv]

/-- The elapsed time `⌊t/h⌋ h` converges to `t` as the step size decreases to zero. -/
theorem tendsto_floor_div_mul (t : ℝ) (ht : 0 < t) :
    Tendsto (fun h : ℝ ↦ (⌊t / h⌋₊ : ℝ) * h) (𝓝[>] 0) (𝓝 t) := by
  have hlow : Tendsto (fun h : ℝ ↦ t - h) (𝓝[>] 0) (𝓝 t) := by
    have h0 : Tendsto (fun h : ℝ ↦ t - h) (𝓝 0) (𝓝 (t - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := Set.mem_Ioi.mp hh
    calc t - h = (t / h - 1) * h := by rw [sub_mul, div_mul_cancel₀ t hpos.ne', one_mul]
      _ ≤ (⌊t / h⌋₊ : ℝ) * h :=
          mul_le_mul_of_nonneg_right (Nat.sub_one_lt_floor (t / h)).le hpos.le
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := Set.mem_Ioi.mp hh
    exact (le_div_iff₀ hpos).mp (Nat.floor_le (div_nonneg ht.le hpos.le))

/-- **The Euler products at `⌊t/h⌋` steps converge to the matrix exponential** as the step size
decreases to zero. -/
theorem tendsto_norm_euler_floor_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun h : ℝ ↦ ‖(1 + h • A) ^ ⌊t / h⌋₊ - matrixExponential A t‖) (𝓝[>] 0)
      (𝓝 0) := by
  have hconv := tendsto_iff_norm_sub_tendsto_zero.mp
    (varying_euler_tends_exp (fun h : ℝ ↦ ⌊t / h⌋₊) (fun h ↦ (⌊t / h⌋₊ : ℝ) * h) t A
      (tendsto_floor_div t ht) (tendsto_floor_div_mul t ht))
  rw [← matrixExponential_eq_normedSpace_exp] at hconv
  refine hconv.congr' ?_
  filter_upwards [(tendsto_floor_div t ht).eventually (eventually_gt_atTop 0)] with h hn
  rw [mul_div_cancel_left₀ h (Nat.cast_ne_zero.mpr hn.ne')]

/-! ## Kernel powers at `⌊t/h⌋` steps -/

section Abstract

variable {B X ι : Type*} [Fintype B] [Fintype ι] {φ : X → ι → ℝ} {A : Matrix ι ι ℝ}

/-- After `⌊t/h⌋` kernel steps of size `h`, the coordinates of the feature differ from the Euler
product applied to the feature by at most `t e^{t‖A‖} ε(h)`, uniformly in the state. -/
theorem norm_kernelPower_sub_euler_le_floor [DecidableEq ι]
    (M : MicroscopicApproximation (B := B) φ A) (t : ℝ) (ht : 0 ≤ t) (h : ℝ) (hh : 0 < h)
    (x : X) :
    ‖(fun i ↦ (M.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ φ y i) x)
        - ((1 + h • A) ^ ⌊t / h⌋₊) *ᵥ φ x‖
      ≤ t * Real.exp (t * ‖A‖) * M.error h := by
  have hnh : (⌊t / h⌋₊ : ℝ) * h ≤ t :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht hh.le))
  have hnn : (0 : ℝ) ≤ 1 + h * ‖A‖ := by
    have := mul_nonneg hh.le (norm_nonneg A)
    linarith
  have hle : 1 + h * ‖A‖ ≤ Real.exp (h * ‖A‖) := by
    have := Real.add_one_le_exp (h * ‖A‖)
    linarith
  have hexpb : (1 + h * ‖A‖) ^ ⌊t / h⌋₊ ≤ Real.exp (t * ‖A‖) := by
    calc (1 + h * ‖A‖) ^ ⌊t / h⌋₊ ≤ (Real.exp (h * ‖A‖)) ^ ⌊t / h⌋₊ :=
          pow_le_pow_left₀ hnn hle _
      _ = Real.exp ((⌊t / h⌋₊ : ℝ) * (h * ‖A‖)) := (Real.exp_nat_mul (h * ‖A‖) _).symm
      _ ≤ Real.exp (t * ‖A‖) := by
          rw [Real.exp_le_exp, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hnh (norm_nonneg A)
  refine (norm_kernelPower_sub_euler_le M h hh _ x).trans ?_
  calc (⌊t / h⌋₊ : ℝ) * (1 + h * ‖A‖) ^ ⌊t / h⌋₊ * (h * M.error h)
      = ((⌊t / h⌋₊ : ℝ) * h) * (1 + h * ‖A‖) ^ ⌊t / h⌋₊ * M.error h := by ring
    _ ≤ t * Real.exp (t * ‖A‖) * M.error h :=
        mul_le_mul_of_nonneg_right (mul_le_mul hnh hexpb (pow_nonneg hnn _) ht)
          (M.error_nonneg h)

/-- A combination of feature coordinates pushed through kernel powers is within the coefficient
mass times the vector error against a comparison matrix `P`, plus the distance from `P` to the
target matrix `E` on a bounded feature. -/
theorem abs_kernelPower_dotProduct_sub_le (K : FiniteMixtureKernel B X) (n : ℕ)
    (P E : Matrix ι ι ℝ) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (c : ι → ℝ) (x : X) :
    |K.apply^[n] (fun y ↦ c ⬝ᵥ φ y) x - c ⬝ᵥ (E *ᵥ φ x)|
      ≤ (∑ i, |c i|)
        * (‖(fun i ↦ K.apply^[n] (fun y ↦ φ y i) x) - P *ᵥ φ x‖ + ‖P - E‖ * C) := by
  have hlin : K.apply^[n] (fun y ↦ c ⬝ᵥ φ y) x
      = c ⬝ᵥ fun i ↦ K.apply^[n] (fun y ↦ φ y i) x := by
    simp only [dotProduct]
    exact iterate_apply_sum K n c (fun i y ↦ φ y i) x
  have hvec : ‖(fun i ↦ K.apply^[n] (fun y ↦ φ y i) x) - E *ᵥ φ x‖
      ≤ ‖(fun i ↦ K.apply^[n] (fun y ↦ φ y i) x) - P *ᵥ φ x‖ + ‖P - E‖ * C := by
    have hsplit : (fun i ↦ K.apply^[n] (fun y ↦ φ y i) x) - E *ᵥ φ x
        = ((fun i ↦ K.apply^[n] (fun y ↦ φ y i) x) - P *ᵥ φ x) + (P - E) *ᵥ φ x := by
      rw [Matrix.sub_mulVec]
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add_left ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (hφ x) (norm_nonneg _))) _)
  rw [hlin, ← dotProduct_sub]
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ i).trans hvec

/-- **The floor form of the Euler limit of kernel powers.**  For a microscopic approximation of
`A` on a bounded feature, a fixed combination of feature coordinates pushed through `⌊t/h⌋`
kernel steps of size `h` converges uniformly in the state to the same combination of
`e^{tA} φ` as `h ↓ 0`. -/
theorem tendstoUniformly_kernelPower_floor_dotProduct [DecidableEq ι]
    (M : MicroscopicApproximation (B := B) φ A) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (c : ι → ℝ)
    (t : ℝ) (ht : 0 < t) :
    TendstoUniformly (fun (h : ℝ) x ↦ (M.kernel h).apply^[⌊t / h⌋₊] (fun y ↦ c ⬝ᵥ φ y) x)
      (fun x ↦ c ⬝ᵥ (matrixExponential A t *ᵥ φ x)) (𝓝[>] 0) := by
  have hδ : Tendsto (fun h : ℝ ↦ (∑ i, |c i|) * (t * Real.exp (t * ‖A‖) * M.error h
      + ‖(1 + h • A) ^ ⌊t / h⌋₊ - matrixExponential A t‖ * C)) (𝓝[>] 0) (𝓝 0) := by
    have hlim := ((M.error_tendsto.const_mul (t * Real.exp (t * ‖A‖))).add
      ((tendsto_norm_euler_floor_sub A t ht).mul_const C)).const_mul (∑ i, |c i|)
    rwa [mul_zero, zero_mul, add_zero, mul_zero] at hlim
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.1 hδ).2 ε hε] with h hh hδh x
  refine lt_of_le_of_lt ?_ hδh
  rw [dist_comm, Real.dist_eq]
  refine (abs_kernelPower_dotProduct_sub_le (M.kernel h) ⌊t / h⌋₊ ((1 + h • A) ^ ⌊t / h⌋₊)
    (matrixExponential A t) C hφ c x).trans ?_
  exact mul_le_mul_of_nonneg_left (add_le_add_right
    (norm_kernelPower_sub_euler_le_floor M t ht.le h (Set.mem_Ioi.mp hh) x) _)
    (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)

end Abstract

/-! ## The neutral model -/

section Neutral

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- A polynomial observable is the combination of the configuration moments of its support
budget by its support coefficients. -/
theorem coe_polynomialSubspace_eq_dotProduct (ℓ₀ : Locus)
    (f : PolynomialSubspace Deme Locus Allele) :
    ⇑(f : C(FrequencyState Deme Locus Allele, ℝ))
      = fun y ↦ supportCoefficients ℓ₀ (representative f)
          ⬝ᵥ budgetMomentFeature (supportBudget ℓ₀ (representative f)) y := by
  funext y
  conv_lhs => rw [← polynomialFunction_representative f]
  rw [polynomialFunction_apply, eval_eq_dotProduct ℓ₀ _ _
    (withinBudget_supportBudget ℓ₀ (representative f)) y]
  rfl

/-- The neutral polynomial semigroup sends a polynomial observable to the same combination of the
dual propagator applied to the configuration moments. -/
theorem coe_neutralPolynomialSemigroup_eq_dotProduct (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0)
    (f : PolynomialSubspace Deme Locus Allele) :
    ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
      = fun x ↦ supportCoefficients ℓ₀ (representative f)
          ⬝ᵥ (matrixExponential (dualGenerator rates (supportBudget ℓ₀ (representative f))) t
            *ᵥ budgetMomentFeature (supportBudget ℓ₀ (representative f)) x) := by
  funext x
  rw [neutralPolynomialSemigroup_apply, momentFunctional_eq_dotProduct rates ℓ₀ t x _ _
    (withinBudget_supportBudget ℓ₀ (representative f))]
  rfl

/-- **NOTE1 §4.2a, the microscopic limit in floor form.**  For every polynomial observable `f` and
every `t > 0`, the neutral microscopic kernel iterated `⌊t/h⌋` times at step size `h` converges
uniformly to the neutral polynomial semigroup `T_t f` as `h ↓ 0`. -/
theorem tendstoUniformly_neutralPolynomialSemigroup_floor (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (ht : 0 < t)
    (f : PolynomialSubspace Deme Locus Allele) :
    TendstoUniformly
      (fun h : ℝ ↦ (neutralMicroscopicKernel rates h).apply^[⌊(t : ℝ) / h⌋₊]
        ⇑(f : C(FrequencyState Deme Locus Allele, ℝ)))
      ⇑(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ))
      (𝓝[>] 0) := by
  rw [coe_polynomialSubspace_eq_dotProduct ℓ₀ f,
    coe_neutralPolynomialSemigroup_eq_dotProduct rates ℓ₀ hap₀ t f]
  exact tendstoUniformly_kernelPower_floor_dotProduct (neutralMicroscopicApproximation rates _)
    (featureBound rates _) (norm_budgetMomentFeature_le rates _) _ t (NNReal.coe_pos.mpr ht)

/-- **Positivity through the microscopic approximation.**  The floor-form limit discharges the
hypothesis of `markov_of_euler_tendstoUniformly`: the neutral polynomial semigroup is positive,
fixes the constants and contracts sup norms, derived from the microscopic kernel alone. -/
theorem neutralPolynomialSemigroup_markov_of_euler (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (ht : 0 < t) :
    (∀ f : PolynomialSubspace Deme Locus Allele,
        0 ≤ (f : C(FrequencyState Deme Locus Allele, ℝ))
          → 0 ≤ (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
            : C(FrequencyState Deme Locus Allele, ℝ)))
      ∧ (neutralPolynomialSemigroup rates ℓ₀ hap₀ t ⟨1, one_mem_polynomialSubspace⟩
          : C(FrequencyState Deme Locus Allele, ℝ)) = 1
      ∧ ∀ f : PolynomialSubspace Deme Locus Allele,
          ‖(neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
            : C(FrequencyState Deme Locus Allele, ℝ))‖
            ≤ ‖(f : C(FrequencyState Deme Locus Allele, ℝ))‖ :=
  markov_of_euler_tendstoUniformly _ one_mem_polynomialSubspace _
    (fun h : ℝ ↦ neutralMicroscopicKernel rates h) t
    (tendstoUniformly_neutralPolynomialSemigroup_floor rates ℓ₀ hap₀ t ht)

/-- **NOTE1 §4.2a, convergence in law in floor form.**  For every `t > 0` and every continuous
observable `g`, the neutral microscopic chain run for `⌊t/h⌋` steps of size `h` has
`K_h^{⌊t/h⌋} g` converging uniformly in the initial state to the integral of `g` against the
neutral Markov kernel as `h ↓ 0`. -/
theorem tendstoUniformly_integral_neutralMarkovKernel_floor
    (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (t : ℝ≥0) (ht : 0 < t) (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    TendstoUniformly
      (fun h : ℝ ↦ (neutralMicroscopicKernel rates h).apply^[⌊(t : ℝ) / h⌋₊] ⇑g)
      (fun x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x)) (𝓝[>] 0) := by
  have hlim : (fun x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x))
      = ⇑(neutralSemigroupExtension rates ℓ₀ hap₀ t g) :=
    funext fun x ↦ integral_neutralMarkovKernel rates ℓ₀ hap₀ t x g
  rw [hlim]
  exact euler_tendstoUniformly_extension _ dense_polynomialSubspace one_mem_polynomialSubspace _
    (fun h : ℝ ↦ neutralMicroscopicKernel rates h) t
    (tendstoUniformly_neutralPolynomialSemigroup_floor rates ℓ₀ hap₀ t ht) g

end Neutral

end

end Descent.Portability.NeutralMicroscopicFloorLimit
