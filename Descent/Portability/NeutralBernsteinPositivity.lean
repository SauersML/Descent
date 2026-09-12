/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralPolynomialSemigroup
import Descent.Portability.MultinomialMomentExpansion

assert_below Descent.Decision Descent.Program

/-!
# Positivity of the neutral polynomial semigroup, and the complete neutral Markov semigroup

This module proves the positivity step of NOTE1 §4.2a and assembles the complete neutral Markov
semigroup with no hypotheses left. Substochasticity of the dual semigroup only makes the moment
functional nonnegative on monomials; a polynomial that is nonnegative on the frequency states can
have negative coefficients. The step from monomials to all nonnegative polynomial observables is
a Bernstein argument on the product of simplices.

Bernstein polynomials. `bernsteinPolynomial N p` weights the monomial `x^z` of every census `z` of
`N` draws per deme by the multinomial coefficients and by the value of `p` at the census
proportions `z / N`, which are states (`censusPoint_mem`). A linear functional that is
nonnegative on monomials is therefore nonnegative on the Bernstein polynomial of a nonnegative
`p` (`map_bernsteinPolynomial`). On states the Bernstein polynomial of `p` agrees with an explicit
combination of the Bernstein moments of the monomials of `p` (`eval_bernsteinPolynomial`), and the
Bernstein moment of `x^α` is the product over demes of the exact multinomial power moments of
`MultinomialMomentExpansion.expectation_monomial_eq` (`eval_bernsteinMoment`). Expanded, it is a
finite combination of monomials whose index set does not depend on `N`
(`bernsteinMoment_eq_sum`), with coefficients `S(α, j) (N)_{|j|} / N^{|α|}` that tend to `1` at
`j = α` and to `0` below it (`tendsto_descFactorial_div_pow`, `tendsto_bernsteinCoefficient`).
Hence the functional of the Bernstein moment of `x^α` tends to the functional of `x^α`
(`tendsto_map_bernsteinMoment`).

Positivity. `nonneg_of_monomial_nonneg`: a linear functional on frequency polynomials that
vanishes on the polynomials vanishing on all states and is nonnegative on every monomial is
nonnegative on every polynomial that is nonnegative on the states, because it is the limit of its
values on Bernstein polynomials. Applied to the moment functional of the dual chain
(`NeutralPolynomialSemigroup.momentFunctional_eq_zero_of_vanishing`,
`momentFunctional_monomial_nonneg`) this gives `neutralPolynomialSemigroup_nonneg`.

The complete neutral semigroup. `exists_neutralMarkovKernel_semigroup` discharges every hypothesis
of `NeutralFellerGenerator.exists_markovKernel_neutralGenerator` with the constructed polynomial
semigroup: for neutral rates, a locus and a haplotype, there are Markov kernels on the
frequency states that represent the polynomial semigroup, compose by `K_{s+t} = K_t ∘ₖ K_s`, and
have the neutral diffusion generator `neutralGenerator` on every budget-respecting configuration
moment, `d/dt ∫ H_ξ dK_t(x, ·) = ∫ (neutralGenerator H_ξ) dK_t(x, ·)`.

Scope. Rates are constant in time and mutation is symmetric, as in `PartialHaplotypeDualGenerator`.
The generator is identified on configuration moments; its closure on `C(X)` is not described.

## Empirical status

None. The bodies here are analysis on polynomials: multinomial census sums, limits of descending
factorial ratios and matrix exponentials of a supplied rate table, so no measurement on any
population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralBernsteinPositivity

open MvPolynomial Filter Topology ProbabilityTheory MeasureTheory Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup FiniteReproductiveKernel
  MultinomialMomentExpansion
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ### Censuses of the demes -/

/-- The census vectors of `N` draws in every deme. -/
def censusFinset (N : ℕ) : Finset (Deme → FullHaplotype Locus Allele → ℕ) :=
  Fintype.piFinset fun _ ↦ Finset.piAntidiag Finset.univ N

/-- The monomial exponent of a census: `z i h` copies of haplotype `h` in deme `i`. -/
def censusExponent (z : Deme → FullHaplotype Locus Allele → ℕ) :
    FrequencyVariable Deme Locus Allele →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun c ↦ z c.1 c.2

/-- The census proportions `z / N` as a frequency vector. -/
def censusPoint (N : ℕ) (z : Deme → FullHaplotype Locus Allele → ℕ) :
    FrequencyVariable Deme Locus Allele → ℝ :=
  fun c ↦ (z c.1 c.2 : ℝ) / N

/-- The census proportions of `N ≥ 1` draws per deme form a state. -/
theorem censusPoint_mem (N : ℕ) (hN : 1 ≤ N) (z : Deme → FullHaplotype Locus Allele → ℕ)
    (hz : z ∈ censusFinset N) : censusPoint N z ∈ frequencySimplex Deme Locus Allele := by
  have hsum : ∀ i, ∑ h, z i h = N := fun i ↦
    (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hz i)).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun c ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), fun i ↦ ?_⟩
  simp only [censusPoint, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hNpos.ne']
  exact_mod_cast hsum i

/-- A monomial evaluates to the product over demes and haplotypes of coordinate powers. -/
theorem eval_monomial_one (y : FrequencyVariable Deme Locus Allele → ℝ)
    (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    eval y (monomial β 1) = ∏ i, ∏ h, y (i, h) ^ β (i, h) := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, Fintype.prod_prod_type]

/-- The monomial of a census exponent is the product of the coordinate powers of the census. -/
theorem monomial_censusExponent (z : Deme → FullHaplotype Locus Allele → ℕ) :
    monomial (censusExponent z) (1 : ℝ) = ∏ i, ∏ h, X (i, h) ^ z i h := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _,
    Fintype.prod_prod_type]
  simp only [censusExponent, Finsupp.coe_equivFunOnFinite_symm]

/-! ### Bernstein polynomials and their exact moments -/

/-- The Bernstein polynomial of `p` with `N` draws in every deme. -/
def bernsteinPolynomial (N : ℕ) (p : FrequencyPolynomial Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ z ∈ censusFinset N, C ((∏ i, (Nat.multinomial Finset.univ (z i) : ℝ))
    * eval (censusPoint N z) p) * monomial (censusExponent z) 1

/-- The exact Bernstein moment polynomial of `x^α`: in every deme, the Stirling-weighted
descending-factorial moments of the multinomial census. -/
def bernsteinMoment (N : ℕ) (α : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∏ i, ∑ j ∈ subIndices fun h ↦ α (i, h),
    C (stirlingWeight (fun h ↦ α (i, h)) j * (N.descFactorial (∑ h, j h) : ℝ)
        / (N : ℝ) ^ (∑ h, α (i, h)))
      * ∏ h, X (i, h) ^ j h

/-- A linear functional applied to a Bernstein polynomial is the census combination of the
functional on monomials. -/
theorem map_bernsteinPolynomial (Λ : FrequencyPolynomial Deme Locus Allele →ₗ[ℝ] ℝ) (N : ℕ)
    (p : FrequencyPolynomial Deme Locus Allele) :
    Λ (bernsteinPolynomial N p)
      = ∑ z ∈ censusFinset N, ((∏ i, (Nat.multinomial Finset.univ (z i) : ℝ))
          * eval (censusPoint N z) p) * Λ (monomial (censusExponent z) 1) := by
  simp only [bernsteinPolynomial, map_sum, C_mul', map_smul, smul_eq_mul]

/-- **The Bernstein moment on states.** At a state, the Bernstein moment of `x^α` is the census
sum of the monomial of `α` at the census proportions against the census monomials. -/
theorem eval_bernsteinMoment (N : ℕ) (x : FrequencyState Deme Locus Allele)
    (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    eval x.1 (bernsteinMoment N β)
      = ∑ z ∈ censusFinset N, (∏ i, (Nat.multinomial Finset.univ (z i) : ℝ))
          * eval (censusPoint N z) (monomial β 1)
          * eval x.1 (monomial (censusExponent z) 1) := by
  have hsplit : ∀ z : Deme → FullHaplotype Locus Allele → ℕ,
      (∏ i, (Nat.multinomial Finset.univ (z i) : ℝ)) * eval (censusPoint N z) (monomial β 1)
          * eval x.1 (monomial (censusExponent z) 1)
        = ∏ i, ((Nat.multinomial Finset.univ (z i) : ℝ) * ∏ h, x.1 (i, h) ^ z i h)
            * ∏ h, ((z i h : ℝ) / N) ^ β (i, h) := by
    intro z
    rw [eval_monomial_one, eval_monomial_one]
    simp only [censusPoint, censusExponent, Finsupp.coe_equivFunOnFinite_symm,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by ring
  have hprod : ∑ z ∈ censusFinset N,
      ∏ i, ((Nat.multinomial Finset.univ (z i) : ℝ) * ∏ h, x.1 (i, h) ^ z i h)
        * ∏ h, ((z i h : ℝ) / N) ^ β (i, h)
      = ∏ i, ∑ j ∈ Finset.piAntidiag Finset.univ N,
          ((Nat.multinomial Finset.univ j : ℝ) * ∏ h, x.1 (i, h) ^ j h)
            * ∏ h, ((j h : ℝ) / N) ^ β (i, h) :=
    (Finset.prod_univ_sum (fun _ : Deme ↦ Finset.piAntidiag Finset.univ N)
      (fun i (j : FullHaplotype Locus Allele → ℕ) ↦
        ((Nat.multinomial Finset.univ j : ℝ) * ∏ h, x.1 (i, h) ^ j h)
          * ∏ h, ((j h : ℝ) / N) ^ β (i, h))).symm
  rw [Finset.sum_congr rfl fun z _ ↦ hsplit z, hprod]
  simp only [bernsteinMoment, map_prod, map_sum, map_mul, eval_C, map_pow, eval_X]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hexp := expectation_monomial_eq (stateLaw x i) N fun h ↦ β (i, h)
  calc ∑ j ∈ subIndices fun h ↦ β (i, h), stirlingWeight (fun h ↦ β (i, h)) j
          * (N.descFactorial (∑ h, j h) : ℝ) / (N : ℝ) ^ (∑ h, β (i, h))
          * ∏ h, x.1 (i, h) ^ j h
      = (∑ j ∈ subIndices fun h ↦ β (i, h), stirlingWeight (fun h ↦ β (i, h)) j
          * (N.descFactorial (∑ h, j h) : ℝ) * ∏ h, (stateLaw x i).mass h ^ j h)
          / (N : ℝ) ^ (∑ h, β (i, h)) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ ↦ by simp only [stateLaw]; ring
    _ = (multinomialLaw (stateLaw x i) N).expectation
          (fun counts ↦ ∏ h, ((counts.val h : ℝ) / N) ^ β (i, h)) := hexp.symm
    _ = ∑ j ∈ Finset.piAntidiag Finset.univ N,
          ((Nat.multinomial Finset.univ j : ℝ) * ∏ h, x.1 (i, h) ^ j h)
            * ∏ h, ((j h : ℝ) / N) ^ β (i, h) := by
        simp only [FiniteReportLaw.expectation, multinomialLaw_mass]
        exact Finset.sum_coe_sort (Finset.piAntidiag Finset.univ N)
          (fun j ↦ ((Nat.multinomial Finset.univ j : ℝ) * ∏ h, x.1 (i, h) ^ j h)
            * ∏ h, ((j h : ℝ) / N) ^ β (i, h))

/-- **The Bernstein identity on states.** At a state, the Bernstein polynomial of `p` is the
combination of the Bernstein moments of the monomials of `p`. -/
theorem eval_bernsteinPolynomial (N : ℕ) (x : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) :
    eval x.1 (bernsteinPolynomial N p)
      = ∑ β ∈ p.support, coeff β p * eval x.1 (bernsteinMoment N β) := by
  have hpoint : ∀ z : Deme → FullHaplotype Locus Allele → ℕ, eval (censusPoint N z) p
      = ∑ β ∈ p.support, coeff β p * eval (censusPoint N z) (monomial β 1) := by
    intro z
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun β _ ↦ by rw [eval_monomial, eval_monomial, one_mul]
  simp only [bernsteinPolynomial, map_sum, map_mul, eval_C, hpoint, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [eval_bernsteinMoment, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ ↦ by ring

/-- The Bernstein moment of `x^α` as a finite combination of monomials, over an index set that
does not depend on `N`. -/
theorem bernsteinMoment_eq_sum (N : ℕ) (α : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    bernsteinMoment N α
      = ∑ J ∈ Fintype.piFinset fun i ↦ subIndices fun h ↦ α (i, h),
          C (∏ i, stirlingWeight (fun h ↦ α (i, h)) (J i)
              * (N.descFactorial (∑ h, J i h) : ℝ) / (N : ℝ) ^ (∑ h, α (i, h)))
            * monomial (censusExponent J) 1 := by
  rw [bernsteinMoment, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun J _ ↦ ?_
  rw [Finset.prod_mul_distrib, map_prod, monomial_censusExponent]

/-! ### Limits of the Bernstein coefficients -/

/-- `(N)_k / N^m` tends to one when `k = m` and to zero when `k < m`. -/
theorem tendsto_descFactorial_div_pow (k m : ℕ) (hkm : k ≤ m) :
    Tendsto (fun N : ℕ ↦ (N.descFactorial k : ℝ) / (N : ℝ) ^ m) atTop
      (𝓝 (if k = m then 1 else 0)) := by
  split_ifs with hk
  · subst hk
    have hlow : Tendsto (fun N : ℕ ↦ (1 - (k : ℝ) / N) ^ k) atTop (𝓝 1) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))).pow k
      simpa only [sub_zero, one_pow] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (k + 1)] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_pos k).trans_le hN
      have h1 : ((N + 1 - k : ℕ) : ℝ) ^ k ≤ (N.descFactorial k : ℝ) := by
        exact_mod_cast Nat.pow_sub_le_descFactorial N k
      have h2 : (N : ℝ) - k ≤ ((N + 1 - k : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith
      have h3 : (0 : ℝ) ≤ (N : ℝ) - k := by
        have : (k : ℝ) ≤ N := by exact_mod_cast (Nat.le_succ k).trans hN
        linarith
      calc (1 - (k : ℝ) / N) ^ k = ((N : ℝ) - k) ^ k / (N : ℝ) ^ k := by
            rw [one_sub_div hNpos.ne', div_pow]
        _ ≤ (N.descFactorial k : ℝ) / (N : ℝ) ^ k :=
            div_le_div_of_nonneg_right ((pow_le_pow_left₀ h3 h2 k).trans h1) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.descFactorial_le_pow N k
  · have hlt : k < m := lt_of_le_of_ne hkm hk
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat 1) ?_ ?_
    · exact Filter.Eventually.of_forall fun N ↦ by positivity
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hbound : (N.descFactorial k : ℝ) ≤ (N : ℝ) ^ (m - 1) := by
        exact_mod_cast (Nat.descFactorial_le_pow N k).trans (Nat.pow_le_pow_right hN (by omega))
      calc (N.descFactorial k : ℝ) / (N : ℝ) ^ m ≤ (N : ℝ) ^ (m - 1) / (N : ℝ) ^ m :=
            div_le_div_of_nonneg_right hbound (by positivity)
        _ = 1 / N := by
            rw [div_eq_div_iff (by positivity) hNpos.ne', one_mul, ← pow_succ,
              Nat.sub_add_cancel (by omega)]

/-- The Bernstein coefficient `S(b, j) (N)_{|j|} / N^{|b|}` of a sub-multi-index `j ≤ b` tends
to one at `j = b` and to zero below it. -/
theorem tendsto_bernsteinCoefficient (b j : FullHaplotype Locus Allele → ℕ)
    (hj : j ∈ subIndices b) :
    Tendsto (fun N : ℕ ↦ stirlingWeight b j * (N.descFactorial (∑ h, j h) : ℝ)
        / (N : ℝ) ^ (∑ h, b h)) atTop (𝓝 (if j = b then 1 else 0)) := by
  have hle : ∀ h, j h ≤ b h := fun h ↦
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hj h))
  have hsum : ∑ h, j h ≤ ∑ h, b h := Finset.sum_le_sum fun h _ ↦ hle h
  have htend := (tendsto_descFactorial_div_pow _ _ hsum).const_mul (stirlingWeight b j)
  simp only [mul_div_assoc] at htend ⊢
  split_ifs with hjb
  · subst hjb
    have hw : stirlingWeight j j = 1 := by
      simp [stirlingWeight, Nat.stirlingSecond_self]
    simpa only [hw, if_pos rfl, mul_one, one_mul] using htend
  · have hne : ∑ h, j h ≠ ∑ h, b h := fun heq ↦ hjb (funext fun h ↦
      (Finset.sum_eq_sum_iff_of_le fun h _ ↦ hle h).mp heq h (Finset.mem_univ h))
    simpa only [hne, if_false, mul_zero] using htend

/-- A linear functional of the Bernstein moment of `x^α` tends to the functional of `x^α`. -/
theorem tendsto_map_bernsteinMoment (Λ : FrequencyPolynomial Deme Locus Allele →ₗ[ℝ] ℝ)
    (α : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    Tendsto (fun N : ℕ ↦ Λ (bernsteinMoment N α)) atTop (𝓝 (Λ (monomial α 1))) := by
  simp only [bernsteinMoment_eq_sum, map_sum, C_mul', map_smul, smul_eq_mul]
  have hlim : ∀ J ∈ Fintype.piFinset fun i ↦ subIndices fun h ↦ α (i, h),
      Tendsto (fun N : ℕ ↦ (∏ i, stirlingWeight (fun h ↦ α (i, h)) (J i)
          * (N.descFactorial (∑ h, J i h) : ℝ) / (N : ℝ) ^ (∑ h, α (i, h)))
            * Λ (monomial (censusExponent J) 1)) atTop
        (𝓝 ((if J = fun i h ↦ α (i, h) then 1 else 0) * Λ (monomial (censusExponent J) 1))) := by
    intro J hJ
    refine Tendsto.mul_const _ ?_
    have hprod := tendsto_finset_prod Finset.univ fun i _ ↦
      tendsto_bernsteinCoefficient (fun h ↦ α (i, h)) (J i) (Fintype.mem_piFinset.mp hJ i)
    have hind : ∏ i, (if J i = (fun h ↦ α (i, h)) then (1 : ℝ) else 0)
        = if J = fun i h ↦ α (i, h) then 1 else 0 := by
      split_ifs with hJα
      · exact Finset.prod_eq_one fun i _ ↦ by simp [hJα]
      · obtain ⟨i, hi⟩ : ∃ i, J i ≠ fun h ↦ α (i, h) := by
          by_contra hc
          push_neg at hc
          exact hJα (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [← hind]
    exact hprod
  have hexpo : censusExponent (fun i h ↦ α (i, h)) = α :=
    Finsupp.ext fun c ↦ by simp [censusExponent]
  have hmem : (fun i h ↦ α (i, h)) ∈ Fintype.piFinset fun i ↦ subIndices fun h ↦ α (i, h) :=
    Fintype.mem_piFinset.mpr fun i ↦ Fintype.mem_piFinset.mpr fun h ↦
      Finset.mem_range.mpr (Nat.lt_succ_self _)
  have htarget : ∑ J ∈ Fintype.piFinset fun i ↦ subIndices fun h ↦ α (i, h),
      (if J = fun i h ↦ α (i, h) then (1 : ℝ) else 0) * Λ (monomial (censusExponent J) 1)
        = Λ (monomial α 1) := by
    rw [Finset.sum_eq_single (fun i h ↦ α (i, h))]
    · rw [if_pos rfl, one_mul, hexpo]
    · intro J _ hne
      rw [if_neg hne, zero_mul]
    · intro hnot
      exact absurd hmem hnot
  rw [← htarget]
  exact tendsto_finset_sum _ hlim

/-! ### Positivity -/

/-- **Positivity from monomial moments.** A linear functional on frequency polynomials that
vanishes on the polynomials vanishing on the states and is nonnegative on every monomial is
nonnegative on every polynomial that is nonnegative on the states. -/
theorem nonneg_of_monomial_nonneg (Λ : FrequencyPolynomial Deme Locus Allele →ₗ[ℝ] ℝ)
    (hvan : ∀ p : FrequencyPolynomial Deme Locus Allele,
      (∀ y : FrequencyState Deme Locus Allele, eval y.1 p = 0) → Λ p = 0)
    (hmono : ∀ β : FrequencyVariable Deme Locus Allele →₀ ℕ, 0 ≤ Λ (monomial β 1))
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ y : FrequencyState Deme Locus Allele, 0 ≤ eval y.1 p) : 0 ≤ Λ p := by
  have hbern : ∀ N : ℕ, Λ (bernsteinPolynomial N p)
      = ∑ β ∈ p.support, coeff β p * Λ (bernsteinMoment N β) := by
    intro N
    have h := hvan (bernsteinPolynomial N p
      - ∑ β ∈ p.support, C (coeff β p) * bernsteinMoment N β) fun y ↦ by
        rw [map_sub, eval_bernsteinPolynomial, map_sum]
        simp only [map_mul, eval_C, sub_self]
    rw [map_sub, sub_eq_zero, map_sum] at h
    rw [h]
    simp only [C_mul', map_smul, smul_eq_mul]
  have hnonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ Λ (bernsteinPolynomial N p) := by
    intro N hN
    rw [map_bernsteinPolynomial]
    exact Finset.sum_nonneg fun z hz ↦ mul_nonneg
      (mul_nonneg (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
        (hp ⟨_, censusPoint_mem N hN z hz⟩)) (hmono _)
  have hp_sum : Λ p = ∑ β ∈ p.support, coeff β p * Λ (monomial β 1) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    have hmono' : monomial β (coeff β p) = coeff β p • monomial β (1 : ℝ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmono', map_smul, smul_eq_mul]
  have hlim : Tendsto (fun N : ℕ ↦ Λ (bernsteinPolynomial N p)) atTop (𝓝 (Λ p)) := by
    simp only [hbern]
    rw [hp_sum]
    exact tendsto_finset_sum _ fun β _ ↦ (tendsto_map_bernsteinMoment Λ β).const_mul _
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, hnonneg⟩)

/-- **The neutral polynomial semigroup is positive.** It maps nonnegative polynomial observables
to nonnegative polynomial observables. -/
theorem neutralPolynomialSemigroup_nonneg (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (f : PolynomialSubspace Deme Locus Allele)
    (hf : 0 ≤ (f : C(FrequencyState Deme Locus Allele, ℝ))) :
    0 ≤ (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
      : C(FrequencyState Deme Locus Allele, ℝ)) := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  rw [ContinuousMap.zero_apply, neutralPolynomialSemigroup_apply]
  refine nonneg_of_monomial_nonneg (momentFunctional rates ℓ₀ t x)
    (momentFunctional_eq_zero_of_vanishing rates ℓ₀ hap₀ t x)
    (momentFunctional_monomial_nonneg rates ℓ₀ t (NNReal.coe_nonneg t) x) _ fun y ↦ ?_
  have hy := ContinuousMap.le_def.mp hf y
  rw [ContinuousMap.zero_apply, ← polynomialFunction_representative f] at hy
  exact hy

/-- **NOTE1 §4.2a, the complete neutral Markov semigroup.** For neutral rates, a locus and a
haplotype, there are Markov kernels on the frequency states that represent the neutral polynomial
semigroup, compose by `K_{s+t} = K_t ∘ₖ K_s`, and have the neutral diffusion generator on every
budget-respecting configuration moment. No hypothesis is assumed. -/
theorem exists_neutralMarkovKernel_semigroup (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) :
    ∃ K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele),
      (∀ t, IsMarkovKernel (K t)) ∧
      (∀ t x (f : PolynomialSubspace Deme Locus Allele),
        ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂(K t x)
          = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
              : C(FrequencyState Deme Locus Allele, ℝ)) x) ∧
      (∀ s t, K (s + t) = K t ∘ₖ K s) ∧
      ∀ t x (ξ : BudgetConfiguration Deme Locus Allele capacity),
        HasDerivWithinAt
          (fun s : ℝ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(K s.toNNReal x))
          (∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x))
          (Set.Ici 0) t :=
  exists_markovKernel_neutralGenerator rates capacity (neutralPolynomialSemigroup rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_one rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_nonneg rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_add rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_momentPolynomial rates ℓ₀ hap₀ capacity)

end

end Descent.Portability.NeutralBernsteinPositivity
