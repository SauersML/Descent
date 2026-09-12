/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Portability.MultinomialJetCertificate

assert_below Descent.Decision Descent.Program

/-!
# The forward generator of the checked-exchange model

The spec is `ANCESTRAL_LOCALITY.md` §4.1 and §7.1, from the research note "Ancestral locality" of
11 September 2026.  For the finite genome space `H = {0,1}^V` and resampling rate `c = 1`, the
diffusion generator (7.1),

  `L F(p) = (c/2) Σ_{x,y} p_x (1{x=y} - p_y) ∂_{xy} F(p)`
    `+ Σ_{i→j} r_ij Σ_z (R_{K_ij}(p)(z) - p_z) ∂_z F(p)`,

is the limit of the finite-population chain (4.5) on the `N`-generation scale.

The objects.  `forwardGenerator G c p F` is (7.1), with the resampling half written through the
corpus operator `MultinomialMomentExpansion.resamplingOperator`, which is
`(1/2) Σ_{x,y} (p_x 1{x=y} - p_x p_y) ∂_x ∂_y F(p)`.  `forwardDrift G p` is the drift field
`Σ_{i→j} r_ij (R_{K_ij}(p) - p)`, and `forwardGenerator_one` separates the two halves at `c = 1`.
One generation of (4.5) draws `N` offspring independently from `Q_N(p)`
(`CompatibilityNeutrality.finitePopulationLaw`).  Their type counts follow the multinomial census
law `FiniteReproductiveKernel.multinomialLaw`, and `nextGenerationMean G N p F` is the expected
value of the polynomial `F` at the census proportions `P' = Z / N`, written as the finite census
sum that `nextGenerationMean_eq_expectation` identifies with that expectation once `R ≤ N`.

The drift.  `Q_N(p) = p + D(p) / N` exactly, with `D = forwardDrift G p`
(`finitePopulationLaw_eq_add_drift`), so `N (F(Q_N(p)) - F(p)) → Σ_z D_z ∂_z F(p)` for every
polynomial (`tendsto_mul_eval_line_sub`, by induction on the polynomial).

The resampling.  For a monomial `x^b` the census moment is exact,
`E (Z/N)^b = N^{-|b|} Σ_{j ≤ b} S(b,j) (N)_{|j|} q^j`
(`MultinomialMomentExpansion.expectation_monomial_eq`), and it splits by degree
(`MultinomialMomentExpansion.sum_subIndices_split`).  The descending factorial ratio obeys
`(N)_k / N^k → 1` and `N ((N)_k / N^k - 1) → -C(k,2)` (`tendsto_descFactorial_div_pow_expansion`);
the Stirling terms one degree down give the diagonal half of the resampling operator; and the
terms at least two degrees down vanish on the `N`-generation scale, for a fixed finite type space
(`tendsto_mul_lowOrderStirlingSum_div_pow`).  Hence `N (E[P'^b] - p^b) → L p^b`
(`tendsto_nextGenerationMean_monomialPolynomial`), and by linearity
`N · E[F(P') - F(p)] → L F(p)` for every polynomial `F` (`tendsto_nextGenerationMean`).

The two moments.  The first moment has the drift as its limit, `N E[P'_z - p_z] → D_z`
(`tendsto_nextGenerationMean_X`), and the centered second moment has the covariance as its limit,
`N E[(P'_x - p_x)(P'_y - p_y)] → p_x (1{x=y} - p_y)` (`tendsto_nextGenerationMean_covariance`).
Every centered moment of order three has limit zero (`tendsto_nextGenerationMean_centeredCube`).

Scope.  The resampling rate is `c = 1` and the genome space is `{0,1}^V` for a finite `V`.  The
statement is the one-generation expansion at a fixed population `p`; the convergence of the chain
to a diffusion process and the sampling duality (7.5) are not proved here.  The module sits in
the portability layer because the multinomial moment identities it uses do; the checked-exchange
model is imported from `Descent.Pangenome.AncestralLocality`.

## Empirical status

None.  The bodies here are algebra and limits of finite census sums of polynomials in supplied
rates and population frequencies, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralForwardGenerator

open Filter Topology MvPolynomial
open Descent.Pangenome.AncestralLocality Descent.Portability.FiniteReproductiveKernel
  Descent.Portability.MultinomialMomentExpansion Descent.Portability.MultinomialDriftStage
  Descent.Portability.MultinomialJetCertificate

noncomputable section

/-! ## Descending factorial ratios -/

/-- **The descending factorial ratio to first order.**  As `N → ∞`, `(N)_k / N^k → 1` and
`N ((N)_k / N^k - 1) → -C(k, 2)`. -/
theorem tendsto_descFactorial_div_pow_expansion (k : ℕ) :
    Tendsto (fun N : ℕ ↦ (N.descFactorial k : ℝ) / (N : ℝ) ^ k) atTop (𝓝 1)
      ∧ Tendsto (fun N : ℕ ↦ (N : ℝ) * ((N.descFactorial k : ℝ) / (N : ℝ) ^ k - 1)) atTop
        (𝓝 (-(k.choose 2 : ℝ))) := by
  induction k with
  | zero =>
    have h0 : Nat.choose 0 2 = 0 := rfl
    simp only [Nat.descFactorial_zero, Nat.cast_one, pow_zero, div_one, sub_self, mul_zero, h0,
      Nat.cast_zero, neg_zero]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  | succ k ih =>
    have hone : Tendsto (fun N : ℕ ↦ 1 - (k : ℝ) * (N : ℝ)⁻¹) atTop (𝓝 1) := by
      have h := (tendsto_inverse_atTop_nhds_zero_nat.const_mul (k : ℝ)).const_sub (1 : ℝ)
      rwa [mul_zero, sub_zero] at h
    have hratio : ∀ᶠ N : ℕ in atTop, (N.descFactorial k : ℝ) / (N : ℝ) ^ k
          * (1 - (k : ℝ) * (N : ℝ)⁻¹)
        = (N.descFactorial (k + 1) : ℝ) / (N : ℝ) ^ (k + 1) := by
      filter_upwards [eventually_ne_atTop 0] with N hN
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      rw [cast_descFactorial_succ, pow_succ]
      field_simp
    have hscaled : ∀ᶠ N : ℕ in atTop, (N : ℝ) * ((N.descFactorial k : ℝ) / (N : ℝ) ^ k - 1)
          - (k : ℝ) * ((N.descFactorial k : ℝ) / (N : ℝ) ^ k)
        = (N : ℝ) * ((N.descFactorial (k + 1) : ℝ) / (N : ℝ) ^ (k + 1) - 1) := by
      filter_upwards [hratio, eventually_ne_atTop 0] with N hN hN0
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
      rw [← hN]
      field_simp
      ring
    refine ⟨?_, ?_⟩
    · have h := ih.1.mul hone
      rw [one_mul] at h
      exact h.congr' hratio
    · have h := ih.2.sub (ih.1.const_mul (k : ℝ))
      have hvalue : -(((k + 1).choose 2 : ℕ) : ℝ) = -(k.choose 2 : ℝ) - (k : ℝ) * 1 := by
        rw [Nat.cast_choose_two, Nat.cast_choose_two]
        push_cast
        ring
      rw [hvalue]
      exact h.congr' hscaled

/-! ## Polynomials along a line -/

section Line

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] in
/-- A first partial derivative of a coordinate, evaluated, is the indicator of that
coordinate. -/
theorem eval_pderiv_X_eq_ite (p : H → ℝ) (z n : H) :
    eval p (pderiv z (X n : MvPolynomial H ℝ)) = if z = n then 1 else 0 := by
  by_cases hz : z = n
  · rw [hz, pderiv_X_self, map_one, if_pos rfl]
  · rw [pderiv_X_of_ne (Ne.symm hz), map_zero, if_neg hz]

omit [DecidableEq H] in
/-- A monomial evaluates to the product of the coordinate powers. -/
theorem eval_monomialPolynomial_eq_prod (x : H → ℝ) (b : H → ℕ) :
    eval x (monomialPolynomial b) = ∏ a, x a ^ b a := by
  simp only [monomialPolynomial, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ fun i ↦ pow_zero (x i)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]

/-- **The product rule on a coordinate.**  The first partial derivatives of `F · X_n`, paired with
a direction `D`, split as `Σ_z D_z ∂_z(F X_n)(p) = (Σ_z D_z ∂_z F(p)) p_n + F(p) D_n`. -/
theorem sum_mul_eval_pderiv_mul_X (p D : H → ℝ) (F : MvPolynomial H ℝ) (n : H) :
    ∑ z, D z * eval p (pderiv z (F * X n))
      = (∑ z, D z * eval p (pderiv z F)) * p n + eval p F * D n := by
  have hterm : ∀ z, D z * eval p (pderiv z (F * X n))
      = D z * eval p (pderiv z F) * p n + eval p F * (if z = n then D z else 0) := by
    intro z
    rw [pderiv_mul, map_add, map_mul, map_mul, eval_X, eval_pderiv_X_eq_ite]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun z _ ↦ hterm z, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ n)]

/-- **The drift is the derivative along the line.**  For every polynomial `F`, moving the point
`p` by `D / N` changes `F` by `(1/N) Σ_z D_z ∂_z F(p)` to first order:
`N (F(p + D/N) - F(p)) → Σ_z D_z ∂_z F(p)`. -/
theorem tendsto_mul_eval_line_sub (p D : H → ℝ) (F : MvPolynomial H ℝ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (eval (fun z ↦ p z + (N : ℝ)⁻¹ * D z) F - eval p F)) atTop
      (𝓝 (∑ z, D z * eval p (pderiv z F))) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, sub_self, mul_zero, pderiv_C, map_zero, Finset.sum_const_zero]
    exact tendsto_const_nhds
  | add F₁ F₂ h₁ h₂ =>
    simp only [map_add, add_sub_add_comm, mul_add, Finset.sum_add_distrib]
    exact h₁.add h₂
  | mul_X F n hF =>
    have hline : Tendsto (fun N : ℕ ↦ p n + (N : ℝ)⁻¹ * D n) atTop (𝓝 (p n)) := by
      have h := (tendsto_inverse_atTop_nhds_zero_nat.mul_const (D n)).const_add (p n)
      rwa [zero_mul, add_zero] at h
    have hunit : Tendsto (fun N : ℕ ↦ (N : ℝ) * (N : ℝ)⁻¹ * D n) atTop (𝓝 (D n)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with N hN
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN), one_mul]
    have hfun : (fun N : ℕ ↦ (N : ℝ) * (eval (fun z ↦ p z + (N : ℝ)⁻¹ * D z) (F * X n)
          - eval p (F * X n)))
        = fun N : ℕ ↦ (N : ℝ) * (eval (fun z ↦ p z + (N : ℝ)⁻¹ * D z) F - eval p F)
            * (p n + (N : ℝ)⁻¹ * D n) + eval p F * ((N : ℝ) * (N : ℝ)⁻¹ * D n) := by
      funext N
      simp only [map_mul, eval_X]
      ring
    rw [hfun, sum_mul_eval_pderiv_mul_X]
    exact (hF.mul hline).add (hunit.const_mul (eval p F))

end Line

/-! ## The forward generator and one generation of (4.5) -/

section Model

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The drift field of (7.1), `Σ_{i → j} r_ij (R_{K_ij}(p) - p)`. -/
def forwardDrift (G : CheckingGraph V) (p : (V → Bool) → ℝ) (z : V → Bool) : ℝ :=
  ∑ e ∈ G.edges, G.rate e * (reproduce (exchangeKernel e.1 e.2) p z - p z)

/-- **The forward generator (7.1)** at resampling rate `c`: `c` times the resampling operator
`(1/2) Σ_{x,y} p_x (1{x=y} - p_y) ∂_{xy} F(p)`, plus the checked-exchange drift
`Σ_{i→j} r_ij Σ_z (R_{K_ij}(p)(z) - p_z) ∂_z F(p)`. -/
def forwardGenerator (G : CheckingGraph V) (c : ℝ) (p : (V → Bool) → ℝ)
    (F : MvPolynomial (V → Bool) ℝ) : ℝ :=
  c * resamplingOperator p F
    + ∑ e ∈ G.edges, G.rate e
      * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z F)

/-- The offspring law `Q_N(p)` of (4.5) as a probability law on genomes, once `R ≤ N`. -/
def offspringLaw (G : CheckingGraph V) (N : ℕ) (hN : G.totalRate ≤ N)
    (p : FiniteReportLaw (V → Bool)) : FiniteReportLaw (V → Bool) where
  mass := finitePopulationLaw G N p.mass
  mass_nonneg := finitePopulationLaw_nonneg G N hN p.mass p.mass_nonneg
  mass_sum := sum_finitePopulationLaw G N p.mass p.mass_sum

/-- **One generation of the finite population (4.5).**  The expected value of a polynomial
observable `F` at the census proportions of `N` offspring drawn independently from `Q_N(p)`,
as a finite sum over censuses weighted by the multinomial law. -/
def nextGenerationMean (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (F : MvPolynomial (V → Bool) ℝ) : ℝ :=
  ∑ counts : Counts (V → Bool) N, (Nat.multinomial Finset.univ counts.val : ℝ)
    * (∏ z, finitePopulationLaw G N p z ^ counts.val z)
    * eval (fun z ↦ (counts.val z : ℝ) / N) F

/-- Once `R ≤ N`, the census sum is the expectation under the multinomial census law of `N`
offspring from `Q_N(p)`. -/
theorem nextGenerationMean_eq_expectation (G : CheckingGraph V) (N : ℕ)
    (hN : G.totalRate ≤ N) (p : FiniteReportLaw (V → Bool)) (F : MvPolynomial (V → Bool) ℝ) :
    nextGenerationMean G N p.mass F
      = (multinomialLaw (offspringLaw G N hN p) N).expectation
          (fun counts ↦ eval (fun z ↦ (counts.val z : ℝ) / N) F) :=
  rfl

/-- **The finite-population law is a drift step**: `Q_N(p) = p + D(p) / N`, with `D` the drift
field of (7.1). -/
theorem finitePopulationLaw_eq_add_drift (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (z : V → Bool) :
    finitePopulationLaw G N p z = p z + (N : ℝ)⁻¹ * forwardDrift G p z := by
  simp only [finitePopulationLaw, forwardDrift, CheckingGraph.totalRate, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- At resampling rate one the generator is the resampling operator plus the drift field
paired with the first partial derivatives. -/
theorem forwardGenerator_one (G : CheckingGraph V) (p : (V → Bool) → ℝ)
    (F : MvPolynomial (V → Bool) ℝ) :
    forwardGenerator G 1 p F
      = resamplingOperator p F + ∑ z, forwardDrift G p z * eval p (pderiv z F) := by
  rw [forwardGenerator, one_mul]
  congr 1
  simp only [forwardDrift, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The generator is additive in the observable. -/
theorem forwardGenerator_add (G : CheckingGraph V) (c : ℝ) (p : (V → Bool) → ℝ)
    (F₁ F₂ : MvPolynomial (V → Bool) ℝ) :
    forwardGenerator G c p (F₁ + F₂) = forwardGenerator G c p F₁ + forwardGenerator G c p F₂ := by
  have hdrift : ∑ e ∈ G.edges, G.rate e
        * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z (F₁ + F₂))
      = ∑ e ∈ G.edges, G.rate e
          * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z F₁)
        + ∑ e ∈ G.edges, G.rate e
          * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z F₂) := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  rw [forwardGenerator, forwardGenerator, forwardGenerator, resamplingOperator_add, hdrift]
  ring

/-- The generator is homogeneous in the observable. -/
theorem forwardGenerator_smul (G : CheckingGraph V) (c : ℝ) (p : (V → Bool) → ℝ) (a : ℝ)
    (F : MvPolynomial (V → Bool) ℝ) :
    forwardGenerator G c p (a • F) = a * forwardGenerator G c p F := by
  have hdrift : ∑ e ∈ G.edges, G.rate e
        * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z (a • F))
      = a * ∑ e ∈ G.edges, G.rate e
          * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z F) := by
    simp only [Derivation.map_smul, smul_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
    ring
  rw [forwardGenerator, forwardGenerator, resamplingOperator_smul, hdrift]
  ring

/-- One generation's expectation is additive in the observable. -/
theorem nextGenerationMean_add (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (F₁ F₂ : MvPolynomial (V → Bool) ℝ) :
    nextGenerationMean G N p (F₁ + F₂)
      = nextGenerationMean G N p F₁ + nextGenerationMean G N p F₂ := by
  simp only [nextGenerationMean, map_add, mul_add, Finset.sum_add_distrib]

/-- One generation's expectation is homogeneous in the observable. -/
theorem nextGenerationMean_smul (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ) (a : ℝ)
    (F : MvPolynomial (V → Bool) ℝ) :
    nextGenerationMean G N p (a • F) = a * nextGenerationMean G N p F := by
  simp only [nextGenerationMean, smul_eval, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ## The expansion on the `N`-generation scale -/

/-- **The higher-order terms vanish.**  For a fixed finite type space, the Stirling-weighted
census moments at least two degrees below a monomial contribute nothing on the `N`-generation
scale: `N · lowOrderStirlingSum(Q_N(p), N, b) / N^{|b|} → 0`. -/
theorem tendsto_mul_lowOrderStirlingSum_div_pow (G : CheckingGraph V)
    (p : FiniteReportLaw (V → Bool)) (b : (V → Bool) → ℕ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * lowOrderStirlingSum (finitePopulationLaw G N p.mass) N b
        / (N : ℝ) ^ (∑ a, b a)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N : ℕ ↦ totalStirlingWeight b * (N : ℝ)⁻¹) atTop (𝓝 0) := by
    have h := tendsto_inverse_atTop_nhds_zero_nat.const_mul (totalStirlingWeight b)
    rwa [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop ⌈G.totalRate⌉₊] with N hR
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (lowOrderStirlingSum_nonneg (offspringLaw G N (Nat.ceil_le.mp hR) p) N b))
      (pow_nonneg (Nat.cast_nonneg N) _)
  · filter_upwards [eventually_ge_atTop ⌈G.totalRate⌉₊, eventually_ge_atTop 1] with N hR hN1
    have hbound := lowOrderStirlingSum_mul_sq_le (offspringLaw G N (Nat.ceil_le.mp hR) p) N hN1 b
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [div_le_iff₀ (pow_pos hNpos _)]
    calc (N : ℝ) * lowOrderStirlingSum (finitePopulationLaw G N p.mass) N b
        = lowOrderStirlingSum (finitePopulationLaw G N p.mass) N b * (N : ℝ) ^ 2 * (N : ℝ)⁻¹ := by
          rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hNpos.ne']
          ring
      _ ≤ totalStirlingWeight b * (N : ℝ) ^ (∑ a, b a) * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr hNpos.le)
      _ = totalStirlingWeight b * (N : ℝ)⁻¹ * (N : ℝ) ^ (∑ a, b a) := by ring

/-- **The expansion on a monomial.**  `N (E[P'^b] - p^b) → L p^b` for the census proportions
`P'` of one generation of (4.5) from a population `p`, with `L` the generator (7.1) at `c = 1`. -/
theorem tendsto_nextGenerationMean_monomialPolynomial (G : CheckingGraph V)
    (p : FiniteReportLaw (V → Bool)) (b : (V → Bool) → ℕ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (nextGenerationMean G N p.mass (monomialPolynomial b)
        - eval p.mass (monomialPolynomial b)))
      atTop (𝓝 (forwardGenerator G 1 p.mass (monomialPolynomial b))) := by
  have hqlim : Tendsto (fun N : ℕ ↦ finitePopulationLaw G N p.mass) atTop (𝓝 p.mass) := by
    refine tendsto_pi_nhds.mpr fun z ↦ ?_
    simp only [finitePopulationLaw_eq_add_drift]
    have h := (tendsto_inverse_atTop_nhds_zero_nat.mul_const (forwardDrift G p.mass z)).const_add
      (p.mass z)
    rwa [zero_mul, add_zero] at h
  have hcont : Continuous fun x : (V → Bool) → ℝ ↦ firstOrderStirlingSum x b := by
    unfold firstOrderStirlingSum
    exact continuous_finset_sum _ fun j _ ↦ continuous_const.mul
      (continuous_finset_prod _ fun a _ ↦ (continuous_apply a).pow (j a))
  have hfirst : Tendsto (fun N : ℕ ↦ (N : ℝ) * (N.descFactorial (∑ a, b a - 1) : ℝ)
        / (N : ℝ) ^ (∑ a, b a) * firstOrderStirlingSum (finitePopulationLaw G N p.mass) b)
      atTop (𝓝 (firstOrderStirlingSum p.mass b)) := by
    rcases Nat.eq_zero_or_pos (∑ a, b a) with hb0 | hb0
    · simp only [firstOrderStirlingSum_of_sum_eq_zero _ b hb0, mul_zero]
      exact tendsto_const_nhds
    · obtain ⟨m, hm⟩ : ∃ m, ∑ a, b a = m + 1 := ⟨∑ a, b a - 1, by omega⟩
      have hratio : Tendsto (fun N : ℕ ↦ (N : ℝ) * (N.descFactorial (∑ a, b a - 1) : ℝ)
          / (N : ℝ) ^ (∑ a, b a)) atTop (𝓝 1) := by
        refine (tendsto_descFactorial_div_pow_expansion m).1.congr' ?_
        filter_upwards [eventually_ne_atTop 0] with N hN
        have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        rw [hm, Nat.add_sub_cancel, pow_succ, mul_comm ((N : ℝ) ^ m), mul_div_mul_left _ _ hNr]
      have h := hratio.mul ((hcont.tendsto p.mass).comp hqlim)
      rw [one_mul] at h
      exact h
  have hdrift : Tendsto (fun N : ℕ ↦ (N : ℝ)
        * (∏ a, finitePopulationLaw G N p.mass a ^ b a - ∏ a, p.mass a ^ b a)) atTop
      (𝓝 (∑ z, forwardDrift G p.mass z * eval p.mass (pderiv z (monomialPolynomial b)))) := by
    have h := tendsto_mul_eval_line_sub p.mass (forwardDrift G p.mass) (monomialPolynomial b)
    simp only [eval_monomialPolynomial_eq_prod] at h
    simpa only [finitePopulationLaw_eq_add_drift] using h
  have hdiag := tendsto_descFactorial_div_pow_expansion (∑ a, b a)
  have hlow := tendsto_mul_lowOrderStirlingSum_div_pow G p b
  have hidentity : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * (N.descFactorial (∑ a, b a - 1) : ℝ) / (N : ℝ) ^ (∑ a, b a)
          * firstOrderStirlingSum (finitePopulationLaw G N p.mass) b
        + (N.descFactorial (∑ a, b a) : ℝ) / (N : ℝ) ^ (∑ a, b a)
          * ((N : ℝ) * (∏ a, finitePopulationLaw G N p.mass a ^ b a - ∏ a, p.mass a ^ b a))
        + (N : ℝ) * ((N.descFactorial (∑ a, b a) : ℝ) / (N : ℝ) ^ (∑ a, b a) - 1)
          * ∏ a, p.mass a ^ b a
        + (N : ℝ) * lowOrderStirlingSum (finitePopulationLaw G N p.mass) N b
          / (N : ℝ) ^ (∑ a, b a)
      = (N : ℝ) * (nextGenerationMean G N p.mass (monomialPolynomial b)
          - eval p.mass (monomialPolynomial b)) := by
    filter_upwards [eventually_ge_atTop ⌈G.totalRate⌉₊] with N hR
    have hmean : nextGenerationMean G N p.mass (monomialPolynomial b)
        = (∑ j ∈ subIndices b, stirlingWeight b j * (N.descFactorial (∑ a, j a) : ℝ)
          * ∏ a, finitePopulationLaw G N p.mass a ^ j a) / (N : ℝ) ^ (∑ a, b a) := by
      rw [nextGenerationMean_eq_expectation G N (Nat.ceil_le.mp hR) p]
      simp only [eval_monomialPolynomial_eq_prod]
      exact expectation_monomial_eq (offspringLaw G N (Nat.ceil_le.mp hR) p) N b
    rw [hmean, sum_subIndices_split, eval_monomialPolynomial_eq_prod]
    ring
  have hlim := ((hfirst.add (hdiag.1.mul hdrift)).add
    (hdiag.2.mul_const (∏ a, p.mass a ^ b a))).add hlow
  have hvalue : forwardGenerator G 1 p.mass (monomialPolynomial b)
      = firstOrderStirlingSum p.mass b
        + 1 * ∑ z, forwardDrift G p.mass z * eval p.mass (pderiv z (monomialPolynomial b))
        + -(((∑ a, b a).choose 2 : ℕ) : ℝ) * ∏ a, p.mass a ^ b a + 0 := by
    rw [forwardGenerator_one, resamplingOperator_monomialPolynomial, monomialFirstOrder]
    ring
  rw [hvalue]
  exact hlim.congr' hidentity

/-- **(7.1) is the diffusion generator of the finite-population chain (4.5).**  For every
polynomial observable `F` and every population `p`, one generation of `N` offspring from
`Q_N(p)` changes the expected value of `F` by `L F(p) / N` to first order:
`N · E[F(P') - F(p)] → L F(p)` as `N → ∞`, with `L` the generator (7.1) at `c = 1`. -/
theorem tendsto_nextGenerationMean (G : CheckingGraph V) (p : FiniteReportLaw (V → Bool))
    (F : MvPolynomial (V → Bool) ℝ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (nextGenerationMean G N p.mass F - eval p.mass F)) atTop
      (𝓝 (forwardGenerator G 1 p.mass F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmono : monomial u a = a • monomialPolynomial ⇑u := by
      rw [monomialPolynomial, Finsupp.equivFunOnFinite_symm_coe, smul_monomial, smul_eq_mul,
        mul_one]
    have hfun : (fun N : ℕ ↦ (N : ℝ) * (nextGenerationMean G N p.mass (monomial u a)
          - eval p.mass (monomial u a)))
        = fun N : ℕ ↦ a * ((N : ℝ) * (nextGenerationMean G N p.mass (monomialPolynomial ⇑u)
          - eval p.mass (monomialPolynomial ⇑u))) := by
      funext N
      rw [hmono, nextGenerationMean_smul, smul_eval]
      ring
    rw [hfun, hmono, forwardGenerator_smul]
    exact (tendsto_nextGenerationMean_monomialPolynomial G p ⇑u).const_mul a
  | add F₁ F₂ h₁ h₂ =>
    have hfun : (fun N : ℕ ↦ (N : ℝ) * (nextGenerationMean G N p.mass (F₁ + F₂)
          - eval p.mass (F₁ + F₂)))
        = fun N : ℕ ↦ (N : ℝ) * (nextGenerationMean G N p.mass F₁ - eval p.mass F₁)
          + (N : ℝ) * (nextGenerationMean G N p.mass F₂ - eval p.mass F₂) := by
      funext N
      rw [nextGenerationMean_add, map_add]
      ring
    rw [hfun, forwardGenerator_add]
    exact h₁.add h₂

/-- **The first moment.**  `N E[P'_z - p_z] → D_z`: on the `N`-generation scale the mean change
of a genome frequency is the drift field of (7.1). -/
theorem tendsto_nextGenerationMean_X (G : CheckingGraph V) (p : FiniteReportLaw (V → Bool))
    (z : V → Bool) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (nextGenerationMean G N p.mass (X z) - p.mass z)) atTop
      (𝓝 (forwardDrift G p.mass z)) := by
  have hvalue : forwardGenerator G 1 p.mass (X z) = forwardDrift G p.mass z := by
    rw [forwardGenerator_one, resamplingOperator_X, zero_add]
    simp only [eval_pderiv_X_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have h := tendsto_nextGenerationMean G p (X z)
  rwa [eval_X, hvalue] at h

/-- **The second moment.**  `N E[(P'_x - p_x)(P'_y - p_y)] → p_x (1{x=y} - p_y)`: on the
`N`-generation scale the centered second moment of the genome frequencies is the Wright–Fisher
covariance of (7.1). -/
theorem tendsto_nextGenerationMean_covariance (G : CheckingGraph V)
    (p : FiniteReportLaw (V → Bool)) (x y : V → Bool) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)
        * nextGenerationMean G N p.mass ((X x - C (p.mass x)) * (X y - C (p.mass y))))
      atTop (𝓝 ((if x = y then p.mass x else 0) - p.mass x * p.mass y)) := by
  have heval : eval p.mass ((X x - C (p.mass x)) * (X y - C (p.mass y))) = 0 := by
    simp only [map_mul, map_sub, eval_X, eval_C, sub_self, mul_zero]
  have hdrift : ∀ z,
      eval p.mass (pderiv z ((X x - C (p.mass x)) * (X y - C (p.mass y)))) = 0 := by
    intro z
    simp only [pderiv_mul, map_add, map_mul, map_sub, eval_X, eval_C, sub_self, mul_zero,
      zero_mul, add_zero]
  have hresampling : resamplingOperator p.mass ((X x - C (p.mass x)) * (X y - C (p.mass y)))
      = (if x = y then p.mass x else 0) - p.mass x * p.mass y := by
    rw [← resamplingOperator_X_mul_X p.mass x y, resamplingOperator_mul, resamplingOperator_mul]
    simp only [map_sub, eval_X, eval_C, sub_self, zero_mul, pderiv_C, sub_zero,
      resamplingOperator_X, mul_zero, zero_add]
  have hvalue : forwardGenerator G 1 p.mass ((X x - C (p.mass x)) * (X y - C (p.mass y)))
      = (if x = y then p.mass x else 0) - p.mass x * p.mass y := by
    rw [forwardGenerator_one, hresampling]
    simp only [hdrift, mul_zero, Finset.sum_const_zero, add_zero]
  have h := tendsto_nextGenerationMean G p ((X x - C (p.mass x)) * (X y - C (p.mass y)))
  rw [heval, hvalue] at h
  simpa only [sub_zero] using h

/-- **The higher moments vanish.**  `N E[(P'_x - p_x)(P'_y - p_y)(P'_w - p_w)] → 0`: on the
`N`-generation scale every centered moment of order three has limit zero, because (7.1) is a
second-order operator and every first and second partial derivative of a product of three
centered coordinates vanishes at `p`. -/
theorem tendsto_nextGenerationMean_centeredCube (G : CheckingGraph V)
    (p : FiniteReportLaw (V → Bool)) (x y w : V → Bool) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * nextGenerationMean G N p.mass
        ((X x - C (p.mass x)) * (X y - C (p.mass y)) * (X w - C (p.mass w)))) atTop (𝓝 0) := by
  have heval : eval p.mass
      ((X x - C (p.mass x)) * (X y - C (p.mass y)) * (X w - C (p.mass w))) = 0 := by
    simp only [map_mul, map_sub, eval_X, eval_C, sub_self, mul_zero]
  have hvalue : forwardGenerator G 1 p.mass
      ((X x - C (p.mass x)) * (X y - C (p.mass y)) * (X w - C (p.mass w))) = 0 := by
    rw [forwardGenerator_one, resamplingOperator_mul]
    simp only [pderiv_mul, map_add, map_mul, map_sub, eval_X, eval_C, sub_self, mul_zero,
      zero_mul, add_zero, zero_add, zero_div, Finset.sum_const_zero]
  have h := tendsto_nextGenerationMean G p
    ((X x - C (p.mass x)) * (X y - C (p.mass y)) * (X w - C (p.mass w)))
  rw [heval, hvalue] at h
  simpa only [sub_zero] using h

end Model

end

end Descent.Portability.AncestralForwardGenerator
