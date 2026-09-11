/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralMomentSemigroup

assert_below Descent.Decision Descent.Program

/-!
# The neutral polynomial semigroup

This module constructs the polynomial semigroup that NOTE1 §4.2a defines "by its finite matrix
exponential" on material-bounded invariant spaces, as a genuine family of linear operators on the
polynomial observables of the frequency state, and proves its algebraic properties. It
discharges the `hdual`, `hT1` and `hsemi` hypotheses of
`NeutralFellerGenerator.exists_markovKernel_neutralGenerator`; positivity is the companion module
`NeutralPolynomialPositivity`.

Monomials as configurations. The monomial `x^β` in the haplotype frequencies is the moment of the
configuration `monomialConfiguration ℓ₀ β` of fully retained haplotypes
(`momentPolynomial_monomialConfiguration`), and every configuration respects its
`cardinalityBudget`.

The moment functional. `monomialMoment rates ℓ₀ t x β` runs the dual semigroup `e^{tQ}` of
`PartialHaplotypeDualSemigroup` on the cardinality budget of `β` and reads it at the configuration
of `β`; it does not depend on the budget (`monomialMoment_eq_budget`). `momentFunctional` extends
it linearly from the monomial basis. Evaluated through any budget containing the monomials of a
polynomial, both the functional and evaluation at a state are dot products with one coefficient
vector (`momentFunctional_eq_dotProduct`, `eval_eq_dotProduct`). Since `e^{tQ}` respects the
relations among configuration moments (`NeutralMomentSemigroup.vecMul_matrixExponential_mem`),
the functional vanishes on polynomials that vanish on every state
(`momentFunctional_eq_zero_of_vanishing`), so it depends only on the polynomial function
(`momentFunctional_congr`). On a configuration moment it is the dual semigroup,
`Λ_{t,x}(H_η) = (e^{tQ} H(x))_η` (`momentFunctional_momentPolynomial`), and it composes in time
(`momentFunctional_add`).

The semigroup. `momentEvolution rates ℓ₀ t` sends `x^β` to `Σ_η (e^{tQ})_{β η} H_η`, and evaluating
it at a state is the moment functional (`eval_momentEvolution`). `neutralPolynomialSemigroup
rates ℓ₀ hap₀ t` acts on the polynomial observables through any representing polynomial. It is
linear, fixes the constant observable (`neutralPolynomialSemigroup_one`), obeys
`T_{s+t} = T_s T_t` (`neutralPolynomialSemigroup_add`), and acts on budget-respecting
configuration moments as the dual semigroup (`neutralPolynomialSemigroup_momentPolynomial`). The
moment functional is nonnegative on every monomial at every nonnegative time
(`momentFunctional_monomial_nonneg`), because `e^{tQ}` is substochastic and configuration moments
are nonnegative on states.

Scope. A locus `ℓ₀` and a haplotype `hap₀` are explicit arguments. Positivity of the operators on
all nonnegative polynomial observables is not proved here; it needs the Pólya-type
representation of the companion module, not only nonnegativity on monomials.

## Empirical status

None. The bodies here are linear algebra on polynomials: matrix exponentials of a supplied rate
table read against configuration moments of per-deme probability vectors, so no measurement on
any population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralPolynomialSemigroup

open MvPolynomial Descent.Coalescent PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup NeutralFellerGenerator
  NeutralMomentSemigroup
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ### Monomials as configurations of full haplotypes -/

/-- The budget letting every locus carry as many copies as a configuration has carriers. -/
def cardinalityBudget (ξ : Multiset (PartialType Deme Locus Allele)) : Locus → ℕ :=
  fun _ ↦ Multiset.card ξ

/-- Every configuration respects its cardinality budget. -/
theorem withinBudget_cardinalityBudget (ξ : Multiset (PartialType Deme Locus Allele)) :
    WithinBudget (cardinalityBudget ξ) ξ :=
  fun _ ↦ Multiset.countP_le_card _

/-- The configuration of fully retained haplotypes whose moment is the monomial `x^β`. -/
def monomialConfiguration (ℓ₀ : Locus) (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    Multiset (PartialType Deme Locus Allele) :=
  ∑ c, Multiset.replicate (β c) (fullType c.1 c.2 ℓ₀)

/-- The marginal polynomial of a fully retained haplotype is its frequency coordinate. -/
theorem marginalPolynomial_fullType (i : Deme) (hap : FullHaplotype Locus Allele) (ℓ₀ : Locus) :
    marginalPolynomial (fullType i hap ℓ₀) = X (i, hap) := by
  have hfilter : Finset.univ.filter (Satisfies (fullType (Deme := Deme) i hap ℓ₀).allele)
      = {hap} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      funext ℓ
      rcases hk ℓ with h | h
      · exact absurd h (by simp [fullType])
      · exact (Option.some.inj h).symm
    · rintro rfl ℓ
      exact Or.inr rfl
  simp only [marginalPolynomial, assignmentPolynomial, hfilter, Finset.sum_singleton]
  rfl

/-- The moment polynomial of the configuration of `β` is the monomial `x^β`. -/
theorem momentPolynomial_monomialConfiguration (ℓ₀ : Locus)
    (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    momentPolynomial (monomialConfiguration ℓ₀ β) = monomial β 1 := by
  have hadd : ∀ ξ ζ : Multiset (PartialType Deme Locus Allele),
      momentPolynomial (ξ + ζ) = momentPolynomial ξ * momentPolynomial ζ := fun ξ ζ ↦ by
    simp only [momentPolynomial, Multiset.map_add, Multiset.prod_add]
  have hrep : ∀ (n : ℕ) (τ : PartialType Deme Locus Allele),
      momentPolynomial (Multiset.replicate n τ) = marginalPolynomial τ ^ n := fun n τ ↦ by
    simp only [momentPolynomial, Multiset.map_replicate, Multiset.prod_replicate]
  have hstep : ∀ s : Finset (FrequencyVariable Deme Locus Allele),
      momentPolynomial (∑ c ∈ s, Multiset.replicate (β c) (fullType c.1 c.2 ℓ₀))
        = ∏ c ∈ s, X c ^ β c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [momentPolynomial]
    | insert c s hc ih =>
      simp only [Finset.sum_insert hc, Finset.prod_insert hc, hadd, ih, hrep,
        marginalPolynomial_fullType, Prod.mk.eta]
  rw [monomialConfiguration, hstep, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]

/-! ### The moment functional -/

/-- The dual moment of the monomial `x^β` at time `t` and state `x`: the dual semigroup, run on the
cardinality budget of the configuration of `β`, read at that configuration. -/
def monomialMoment (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) (β : FrequencyVariable Deme Locus Allele →₀ ℕ) : ℝ :=
  (matrixExponential (dualGenerator rates (cardinalityBudget (monomialConfiguration ℓ₀ β))) t
      *ᵥ momentVector _ x) ⟨monomialConfiguration ℓ₀ β, withinBudget_cardinalityBudget _⟩

/-- The dual moment of a monomial is the same under every budget containing its configuration. -/
theorem monomialMoment_eq_budget (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) (β : FrequencyVariable Deme Locus Allele →₀ ℕ)
    (capacity : Locus → ℕ) (h : WithinBudget capacity (monomialConfiguration ℓ₀ β)) :
    monomialMoment rates ℓ₀ t x β
      = (matrixExponential (dualGenerator rates capacity) t *ᵥ momentVector capacity x)
          ⟨_, h⟩ := by
  have h1 := matrixExponential_mulVec_budget rates
    (cardinalityBudget (monomialConfiguration ℓ₀ β))
    (fun ℓ ↦ max (cardinalityBudget (monomialConfiguration ℓ₀ β) ℓ) (capacity ℓ))
    (fun _ ↦ le_max_left _ _) t x ⟨_, withinBudget_cardinalityBudget _⟩
  have h2 := matrixExponential_mulVec_budget rates capacity
    (fun ℓ ↦ max (cardinalityBudget (monomialConfiguration ℓ₀ β) ℓ) (capacity ℓ))
    (fun _ ↦ le_max_right _ _) t x ⟨_, h⟩
  rw [monomialMoment, ← h1, ← h2]

/-- The moment functional at time `t` and state `x`, extended linearly from the monomials. -/
def momentFunctional (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele →ₗ[ℝ] ℝ :=
  (basisMonomials (FrequencyVariable Deme Locus Allele) ℝ).constr ℝ
    (monomialMoment rates ℓ₀ t x)

/-- On a monomial the moment functional is the dual moment of the monomial. -/
theorem momentFunctional_monomial (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    momentFunctional rates ℓ₀ t x (monomial β 1) = monomialMoment rates ℓ₀ t x β := by
  have h := (basisMonomials (FrequencyVariable Deme Locus Allele) ℝ).constr_basis ℝ
    (monomialMoment rates ℓ₀ t x) β
  simpa only [coe_basisMonomials] using h

/-- A vector over budget-respecting configurations, extended by zero to all configurations. -/
def extendByZero {capacity : Locus → ℕ}
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (ξ : Multiset (PartialType Deme Locus Allele)) : ℝ := by
  classical
  exact if h : WithinBudget capacity ξ then v ⟨ξ, h⟩ else 0

/-- Dotting a vector with indicator coefficients reads the vector at the indicated
configurations. -/
theorem indicatorCoefficients_dotProduct (capacity : Locus → ℕ) {ι : Type*} (s : Finset ι)
    (ξ : ι → Multiset (PartialType Deme Locus Allele)) (r : ι → ℝ)
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ) :
    (fun η : BudgetConfiguration Deme Locus Allele capacity ↦
        ∑ j ∈ s, if ξ j = η.1 then r j else 0) ⬝ᵥ v
      = ∑ j ∈ s, r j * extendByZero v (ξ j) := by
  simp only [dotProduct, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [extendByZero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨ξ j, h⟩]
    · simp
    · intro η _ hne
      exact if_neg fun heq ↦ hne (Subtype.ext heq.symm)
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [mul_zero]
    exact Finset.sum_eq_zero fun η _ ↦ if_neg fun (heq : ξ j = η.1) ↦ h (heq ▸ η.2)

/-- Through a budget containing the monomials of a polynomial, evaluation at a state is a dot
product of one coefficient vector with the configuration moments. -/
theorem eval_eq_dotProduct (ℓ₀ : Locus) (capacity : Locus → ℕ)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β))
    (y : FrequencyState Deme Locus Allele) :
    eval y.1 p
      = (fun η : BudgetConfiguration Deme Locus Allele capacity ↦
          ∑ β ∈ p.support, if monomialConfiguration ℓ₀ β = η.1 then coeff β p else 0)
        ⬝ᵥ momentVector capacity y := by
  rw [indicatorCoefficients_dotProduct]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun β hβ ↦ ?_
  rw [extendByZero, dif_pos (hp β hβ)]
  simp only [momentVector, momentPolynomial_monomialConfiguration, eval_monomial, one_mul]

/-- Through a budget containing the monomials of a polynomial, the moment functional is the same
coefficient vector dotted with the evolved configuration moments. -/
theorem momentFunctional_eq_dotProduct (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (t : ℝ) (x : FrequencyState Deme Locus Allele) (capacity : Locus → ℕ)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β)) :
    momentFunctional rates ℓ₀ t x p
      = (fun η : BudgetConfiguration Deme Locus Allele capacity ↦
          ∑ β ∈ p.support, if monomialConfiguration ℓ₀ β = η.1 then coeff β p else 0)
        ⬝ᵥ (matrixExponential (dualGenerator rates capacity) t *ᵥ momentVector capacity x) := by
  rw [indicatorCoefficients_dotProduct]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun β hβ ↦ ?_
  have hmono : monomial β (coeff β p) = coeff β p • monomial β (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, map_smul, momentFunctional_monomial, smul_eq_mul, extendByZero, dif_pos (hp β hβ),
    monomialMoment_eq_budget rates ℓ₀ t x β capacity (hp β hβ)]

/-- **The moment functional is well defined on polynomial functions.** It vanishes on every
polynomial that vanishes on all states. -/
theorem momentFunctional_eq_zero_of_vanishing (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ y : FrequencyState Deme Locus Allele, eval y.1 p = 0) :
    momentFunctional rates ℓ₀ t x p = 0 := by
  have hwithin : ∀ β ∈ p.support, WithinBudget
      (fun _ ↦ ∑ β ∈ p.support, Multiset.card (monomialConfiguration ℓ₀ β))
      (monomialConfiguration ℓ₀ β) := fun β hβ _ ↦
    (Multiset.countP_le_card _).trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hβ)
  have hmem : (fun η : BudgetConfiguration Deme Locus Allele
        (fun _ ↦ ∑ β ∈ p.support, Multiset.card (monomialConfiguration ℓ₀ β)) ↦
          ∑ β ∈ p.support, if monomialConfiguration ℓ₀ β = η.1 then coeff β p else 0)
      ∈ vanishingCombinations
        (fun _ ↦ ∑ β ∈ p.support, Multiset.card (monomialConfiguration ℓ₀ β)) := fun y ↦
    (eval_eq_dotProduct ℓ₀ _ p hwithin y).symm.trans (hp y)
  rw [momentFunctional_eq_dotProduct rates ℓ₀ t x _ p hwithin, Matrix.dotProduct_mulVec]
  exact vecMul_matrixExponential_mem rates hap₀ _ t _ hmem x

/-- The moment functional depends only on the polynomial function. -/
theorem momentFunctional_congr (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ) (x : FrequencyState Deme Locus Allele)
    (p q : FrequencyPolynomial Deme Locus Allele) (h : polynomialFunction p = polynomialFunction q) :
    momentFunctional rates ℓ₀ t x p = momentFunctional rates ℓ₀ t x q := by
  rw [← sub_eq_zero, ← map_sub]
  refine momentFunctional_eq_zero_of_vanishing rates ℓ₀ hap₀ t x _ fun y ↦ ?_
  have hy := congrArg (fun φ : C(FrequencyState Deme Locus Allele, ℝ) ↦ φ y) h
  simp only [polynomialFunction_apply] at hy
  rw [map_sub, hy, sub_self]

/-- **On a configuration moment the moment functional is the dual semigroup:**
`Λ_{t,x}(H_η) = (e^{tQ} H(x))_η` for every budget containing `η`. -/
theorem momentFunctional_momentPolynomial (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ) (x : FrequencyState Deme Locus Allele)
    (capacity : Locus → ℕ) (η : BudgetConfiguration Deme Locus Allele capacity) :
    momentFunctional rates ℓ₀ t x (momentPolynomial η.1)
      = (matrixExponential (dualGenerator rates capacity) t *ᵥ momentVector capacity x) η := by
  have hle : ∀ ℓ, capacity ℓ ≤ capacity ℓ + ∑ β ∈ (momentPolynomial η.1).support,
      Multiset.card (monomialConfiguration ℓ₀ β) := fun ℓ ↦ Nat.le_add_right _ _
  have hwithin : ∀ β ∈ (momentPolynomial η.1).support, WithinBudget
      (fun ℓ ↦ capacity ℓ + ∑ β ∈ (momentPolynomial η.1).support,
        Multiset.card (monomialConfiguration ℓ₀ β))
      (monomialConfiguration ℓ₀ β) := fun β hβ ℓ ↦
    (Multiset.countP_le_card _).trans
      ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hβ).trans (Nat.le_add_left _ _))
  have hmem : (fun ζ : BudgetConfiguration Deme Locus Allele
        (fun ℓ ↦ capacity ℓ + ∑ β ∈ (momentPolynomial η.1).support,
          Multiset.card (monomialConfiguration ℓ₀ β)) ↦
          ∑ β ∈ (momentPolynomial η.1).support,
            if monomialConfiguration ℓ₀ β = ζ.1 then coeff β (momentPolynomial η.1) else 0)
        - Pi.single ⟨η.1, withinBudget_of_capacity_le hle η.2⟩ 1
      ∈ vanishingCombinations _ := fun y ↦ by
    rw [sub_dotProduct, single_dotProduct, one_mul,
      ← eval_eq_dotProduct ℓ₀ _ (momentPolynomial η.1) hwithin y]
    simp only [momentVector, sub_self]
  have hzero := vecMul_matrixExponential_mem rates hap₀ _ t _ hmem x
  rw [← Matrix.dotProduct_mulVec, sub_dotProduct, single_dotProduct, one_mul, sub_eq_zero,
    ← momentFunctional_eq_dotProduct rates ℓ₀ t x _ (momentPolynomial η.1) hwithin] at hzero
  rw [hzero, matrixExponential_mulVec_budget rates capacity _ hle t x η]

/-- The moment functional is nonnegative on every monomial at every nonnegative time: the dual
semigroup is substochastic and configuration moments are nonnegative on states. -/
theorem momentFunctional_monomial_nonneg (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (t : ℝ) (ht : 0 ≤ t) (x : FrequencyState Deme Locus Allele)
    (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    0 ≤ momentFunctional rates ℓ₀ t x (monomial β 1) := by
  rw [momentFunctional_monomial, monomialMoment]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun η _ ↦ mul_nonneg
    ((matrixExponential_substochastic _ (killingGenerator_dualGenerator rates _) t ht).entry_nonneg
      _ _)
    (momentVector_nonneg _ x η)

/-! ### The polynomial evolution -/

/-- The dual evolution of polynomials at time `t`: the monomial `x^β` is sent to
`Σ_η (e^{tQ})_{β η} H_η` on the cardinality budget of `β`. -/
def momentEvolution (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ) :
    FrequencyPolynomial Deme Locus Allele →ₗ[ℝ] FrequencyPolynomial Deme Locus Allele :=
  (basisMonomials (FrequencyVariable Deme Locus Allele) ℝ).constr ℝ fun β ↦
    ∑ η, C (matrixExponential (dualGenerator rates
        (cardinalityBudget (monomialConfiguration ℓ₀ β))) t
      ⟨monomialConfiguration ℓ₀ β, withinBudget_cardinalityBudget _⟩ η) * momentPolynomial η.1

/-- On a monomial the dual evolution is the corresponding row of the dual semigroup. -/
theorem momentEvolution_monomial (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (β : FrequencyVariable Deme Locus Allele →₀ ℕ) :
    momentEvolution rates ℓ₀ t (monomial β 1)
      = ∑ η, C (matrixExponential (dualGenerator rates
          (cardinalityBudget (monomialConfiguration ℓ₀ β))) t
        ⟨monomialConfiguration ℓ₀ β, withinBudget_cardinalityBudget _⟩ η)
          * momentPolynomial η.1 := by
  have h := (basisMonomials (FrequencyVariable Deme Locus Allele) ℝ).constr_basis ℝ
    (fun β ↦ ∑ η, C (matrixExponential (dualGenerator rates
        (cardinalityBudget (monomialConfiguration ℓ₀ β))) t
      ⟨monomialConfiguration ℓ₀ β, withinBudget_cardinalityBudget _⟩ η)
        * momentPolynomial η.1) β
  simpa only [coe_basisMonomials] using h

/-- Evaluating the dual evolution of a polynomial at a state is the moment functional. -/
theorem eval_momentEvolution (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) (p : FrequencyPolynomial Deme Locus Allele) :
    eval x.1 (momentEvolution rates ℓ₀ t p) = momentFunctional rates ℓ₀ t x p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  have hmono : monomial β (coeff β p) = coeff β p • monomial β (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, momentEvolution_monomial, momentFunctional_monomial, smul_eq_mul,
    smul_eq_C_mul, map_mul, eval_C, map_sum]
  congr 1
  simp only [map_mul, eval_C, monomialMoment, Matrix.mulVec, dotProduct, momentVector]

/-- The moment functional composes in time with the dual evolution. -/
theorem momentFunctional_add (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (s t : ℝ) (x : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) :
    momentFunctional rates ℓ₀ (s + t) x p
      = momentFunctional rates ℓ₀ s x (momentEvolution rates ℓ₀ t p) := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  have hmono : monomial β (coeff β p) = coeff β p • monomial β (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, map_smul, momentFunctional_monomial, momentEvolution_monomial]
  congr 1
  rw [map_sum]
  simp only [C_mul', map_smul, smul_eq_mul,
    momentFunctional_momentPolynomial rates ℓ₀ hap₀ s x]
  have hexp : matrixExponential
        (dualGenerator rates (cardinalityBudget (monomialConfiguration ℓ₀ β))) (s + t)
      = matrixExponential
          (dualGenerator rates (cardinalityBudget (monomialConfiguration ℓ₀ β))) t
        * matrixExponential
          (dualGenerator rates (cardinalityBudget (monomialConfiguration ℓ₀ β))) s := by
    rw [matrixExponential_eq_normedSpace_exp, matrixExponential_eq_normedSpace_exp,
      matrixExponential_eq_normedSpace_exp, add_comm s t, add_smul,
      Matrix.exp_add_of_commute ℝ _ _ (((Commute.refl _).smul_left t).smul_right s)]
  rw [monomialMoment, hexp, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]

/-! ### The semigroup on polynomial observables -/

/-- A polynomial representing a polynomial observable, chosen once and for all. -/
def representative (f : PolynomialSubspace Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  Classical.choose f.2

/-- The chosen representative has the observable as its polynomial function. -/
theorem polynomialFunction_representative (f : PolynomialSubspace Deme Locus Allele) :
    polynomialFunction (representative f) = f :=
  Classical.choose_spec f.2

/-- Polynomial functions of sums are sums of polynomial functions. -/
theorem polynomialFunction_add (p q : FrequencyPolynomial Deme Locus Allele) :
    polynomialFunction (p + q) = polynomialFunction p + polynomialFunction q :=
  ContinuousMap.ext fun x ↦ by simp [polynomialFunction_apply]

/-- Polynomial functions of scalar multiples are scalar multiples of polynomial functions. -/
theorem polynomialFunction_smul (c : ℝ) (p : FrequencyPolynomial Deme Locus Allele) :
    polynomialFunction (c • p) = c • polynomialFunction p :=
  ContinuousMap.ext fun x ↦ by simp [polynomialFunction_apply, smul_eq_C_mul]

/-- **The neutral polynomial semigroup** at time `t`: a polynomial observable is sent to the
polynomial observable of the dual evolution of a polynomial representing it. -/
def neutralPolynomialSemigroup (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    PolynomialSubspace Deme Locus Allele →ₗ[ℝ] PolynomialSubspace Deme Locus Allele where
  toFun f := ⟨polynomialFunction (momentEvolution rates ℓ₀ t (representative f)),
    polynomialFunction_mem _⟩
  map_add' f g := by
    refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
    simp only [Submodule.coe_add, ContinuousMap.add_apply, polynomialFunction_apply,
      eval_momentEvolution]
    rw [← map_add]
    refine momentFunctional_congr rates ℓ₀ hap₀ t x _ _ ?_
    rw [polynomialFunction_add, polynomialFunction_representative,
      polynomialFunction_representative, polynomialFunction_representative, Submodule.coe_add]
  map_smul' c f := by
    refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
    simp only [Submodule.coe_smul, ContinuousMap.smul_apply, polynomialFunction_apply,
      eval_momentEvolution, RingHom.id_apply, smul_eq_mul]
    rw [← smul_eq_mul, ← map_smul]
    refine momentFunctional_congr rates ℓ₀ hap₀ t x _ _ ?_
    rw [polynomialFunction_smul, polynomialFunction_representative,
      polynomialFunction_representative, Submodule.coe_smul]

/-- The semigroup evaluates a polynomial observable through the moment functional of its
representative. -/
theorem neutralPolynomialSemigroup_apply (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (f : PolynomialSubspace Deme Locus Allele)
    (x : FrequencyState Deme Locus Allele) :
    (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f : C(FrequencyState Deme Locus Allele, ℝ)) x
      = momentFunctional rates ℓ₀ t x (representative f) :=
  eval_momentEvolution rates ℓ₀ t x _

/-- **The dual representation.** On a budget-respecting configuration moment the semigroup is
the dual semigroup `e^{tQ}` of NOTE1 (20). -/
theorem neutralPolynomialSemigroup_momentPolynomial (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) (t : ℝ≥0)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) (x : FrequencyState Deme Locus Allele) :
    (neutralPolynomialSemigroup rates ℓ₀ hap₀ t
        ⟨polynomialFunction (momentPolynomial ξ.1), polynomialFunction_mem _⟩ :
          C(FrequencyState Deme Locus Allele, ℝ)) x
      = (matrixExponential (dualGenerator rates capacity) t
          *ᵥ fun η ↦ polynomialFunction (momentPolynomial η.1) x) ξ := by
  rw [neutralPolynomialSemigroup_apply,
    momentFunctional_congr rates ℓ₀ hap₀ t x _ (momentPolynomial ξ.1)
      (polynomialFunction_representative _),
    momentFunctional_momentPolynomial rates ℓ₀ hap₀ t x capacity ξ]
  rfl

/-- **The semigroup fixes the constant observable.** The empty configuration has no dual
transitions, so its row of `e^{tQ}` is the identity row. -/
theorem neutralPolynomialSemigroup_one (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    (neutralPolynomialSemigroup rates ℓ₀ hap₀ t ⟨1, one_mem_polynomialSubspace⟩ :
        C(FrequencyState Deme Locus Allele, ℝ)) = 1 := by
  refine ContinuousMap.ext fun x ↦ ?_
  have hone : polynomialFunction (1 : FrequencyPolynomial Deme Locus Allele) = 1 :=
    ContinuousMap.ext fun y ↦ by simp [polynomialFunction_apply]
  have hmono : (1 : FrequencyPolynomial Deme Locus Allele) = monomial 0 1 := by
    rw [← C_1, C_apply]
  have hzero : monomialConfiguration ℓ₀ (0 : FrequencyVariable Deme Locus Allele →₀ ℕ) = 0 := by
    simp [monomialConfiguration]
  rw [neutralPolynomialSemigroup_apply,
    momentFunctional_congr rates ℓ₀ hap₀ t x _ 1
      ((polynomialFunction_representative _).trans hone.symm),
    hmono, momentFunctional_monomial, monomialMoment,
    matrixExponential_mulVec_apply_of_row_zero _ _ _ _ fun column ↦ by
      simp [dualGenerator, jumpRate, exitRate, dualTransitions, hzero]]
  simp [momentVector, momentPolynomial_monomialConfiguration, eval_monomial]

/-- **The semigroup law** `T_{s+t} = T_s T_t`. -/
theorem neutralPolynomialSemigroup_add (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (s t : ℝ≥0) :
    neutralPolynomialSemigroup rates ℓ₀ hap₀ (s + t)
      = neutralPolynomialSemigroup rates ℓ₀ hap₀ s ∘ₗ neutralPolynomialSemigroup rates ℓ₀ hap₀ t := by
  refine LinearMap.ext fun f ↦ Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  rw [LinearMap.comp_apply, neutralPolynomialSemigroup_apply, neutralPolynomialSemigroup_apply,
    NNReal.coe_add, momentFunctional_add rates ℓ₀ hap₀]
  exact momentFunctional_congr rates ℓ₀ hap₀ s x _ _ (polynomialFunction_representative _).symm

end

end Descent.Portability.NeutralPolynomialSemigroup
