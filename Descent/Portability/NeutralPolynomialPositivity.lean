/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralPolynomialSemigroup
import Descent.Portability.PartialHaplotypeMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# Positivity of the neutral polynomial semigroup

NOTE1 §4.2a derives positivity of the polynomial semigroup from the physical microscopic kernels.
This module proves it.  `PartialHaplotypeMicroscopicApproximation` builds a microscopic
approximation of the dual generator on the budget-moment feature, so NOTE1 Theorem 1 keeps the
realization body invariant: at every nonnegative time, `e^{tQ} H(x)` is the moment vector of a
finitely supported probability law on frequency states
(`PartialHaplotypeMicroscopicApproximation.dualPropagator_mem_realizationBody`).  The moment
functional of `NeutralPolynomialSemigroup` is a coefficient vector dotted with `e^{tQ} H(x)`, and
evaluation at a state is the same coefficient vector dotted with that state's moments.  Hence the
moment functional of a polynomial is the law's average of the polynomial
(`exists_momentFunctional_eq_average`), it is nonnegative on every polynomial that is nonnegative
on states (`momentFunctional_nonneg`), and the neutral polynomial semigroup is positive
(`neutralPolynomialSemigroup_nonneg`).

With constant preservation, the semigroup law and the dual representation of
`NeutralPolynomialSemigroup`, every hypothesis of
`NeutralFellerGenerator.exists_markovKernel_neutralGenerator` is now proved.  The neutral Markov
kernels of NOTE1 §4.2a therefore exist for every neutral model: they represent the polynomial
semigroup, compose by `K_{s+t} = K_t ∘ₖ K_s`, and have the neutral diffusion generator on
configuration moments (`exists_neutralMarkovKernel`).

Scope.  A locus `ℓ₀` and a haplotype `hap₀` are explicit arguments, as in
`NeutralPolynomialSemigroup`.

## Empirical status

None.  The bodies here are algebra: dot products of coefficient vectors with moment vectors of
finitely supported laws on supplied frequency states, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralPolynomialPositivity

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralMomentSemigroup NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  FiniteMixtureKernel RealizationBody
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- The budget carrying the monomials of a polynomial: every locus may carry as many copies as the
configurations of its monomials have carriers in total. -/
def supportBudget (ℓ₀ : Locus) (p : FrequencyPolynomial Deme Locus Allele) : Locus → ℕ :=
  fun _ ↦ ∑ β ∈ p.support, Multiset.card (monomialConfiguration ℓ₀ β)

/-- The configuration of every monomial of a polynomial respects the support budget. -/
theorem withinBudget_supportBudget (ℓ₀ : Locus) (p : FrequencyPolynomial Deme Locus Allele) :
    ∀ β ∈ p.support, WithinBudget (supportBudget ℓ₀ p) (monomialConfiguration ℓ₀ β) :=
  fun β hβ _ ↦ (Multiset.countP_le_card _ _).trans
    (Finset.single_le_sum (f := fun β ↦ Multiset.card (monomialConfiguration ℓ₀ β))
      (fun _ _ ↦ Nat.zero_le _) hβ)

/-- **The moment functional is a law average.**  At a nonnegative time, the moment functional of
a polynomial is the average of the polynomial over the atoms of a finitely supported probability
law on frequency states. -/
theorem exists_momentFunctional_eq_average (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (t : ℝ) (ht : 0 ≤ t) (x : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) :
    ∃ w : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele (supportBudget ℓ₀ p)) + 1)
        → ℝ,
      ∃ point : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele (supportBudget ℓ₀ p)) + 1)
          → FrequencyState Deme Locus Allele,
        (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1
          ∧ momentFunctional rates ℓ₀ t x p = ∑ k, w k * eval (point k).1 p := by
  obtain ⟨w, point, hw, hsum, hfeature⟩ := exists_law_of_mem_realizationBody _ _
    (dualPropagator_mem_realizationBody rates (supportBudget ℓ₀ p) x t ht)
  refine ⟨w, point, hw, hsum, ?_⟩
  rw [momentFunctional_eq_dotProduct rates ℓ₀ t x _ p (withinBudget_supportBudget ℓ₀ p)]
  change _ ⬝ᵥ (matrixExponential (dualGenerator rates (supportBudget ℓ₀ p)) t
    *ᵥ budgetMomentFeature (supportBudget ℓ₀ p) x) = _
  rw [← hfeature, featureVector, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [dotProduct_smul, smul_eq_mul,
    eval_eq_dotProduct ℓ₀ _ p (withinBudget_supportBudget ℓ₀ p) (point k)]
  rfl

/-- **The moment functional is positive.**  At a nonnegative time the moment functional is
nonnegative on every polynomial that is nonnegative on the frequency states. -/
theorem momentFunctional_nonneg (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus) (t : ℝ)
    (ht : 0 ≤ t) (x : FrequencyState Deme Locus Allele) (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ y : FrequencyState Deme Locus Allele, 0 ≤ eval y.1 p) :
    0 ≤ momentFunctional rates ℓ₀ t x p := by
  obtain ⟨w, point, hw, _, havg⟩ := exists_momentFunctional_eq_average rates ℓ₀ t ht x p
  rw [havg]
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hw k) (hp (point k))

/-- **The neutral polynomial semigroup is positive.**  It carries every nonnegative polynomial
observable to a nonnegative polynomial observable. -/
theorem neutralPolynomialSemigroup_nonneg (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) (f : PolynomialSubspace Deme Locus Allele)
    (hf : 0 ≤ (f : C(FrequencyState Deme Locus Allele, ℝ))) :
    0 ≤ (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f :
      C(FrequencyState Deme Locus Allele, ℝ)) := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  rw [ContinuousMap.zero_apply, neutralPolynomialSemigroup_apply]
  refine momentFunctional_nonneg rates ℓ₀ t t.2 x (representative f) fun y ↦ ?_
  have hy := ContinuousMap.le_def.mp hf y
  rw [ContinuousMap.zero_apply, ← polynomialFunction_representative f,
    polynomialFunction_apply] at hy
  exact hy

/-- **NOTE1 §4.2a, assembled.**  For every neutral model there are Markov kernels on the
frequency states that represent the neutral polynomial semigroup, compose by
`K_{s+t} = K_t ∘ₖ K_s`, and whose generator on budget-respecting configuration moments is the
neutral diffusion generator of NOTE1 (19). -/
theorem exists_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) :
    ∃ K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele),
      (∀ t, IsMarkovKernel (K t)) ∧
      (∀ t x (f : PolynomialSubspace Deme Locus Allele),
        ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂(K t x)
          = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f :
              C(FrequencyState Deme Locus Allele, ℝ)) x) ∧
      (∀ s t, K (s + t) = K t ∘ₖ K s) ∧
      ∀ t x (ξ : BudgetConfiguration Deme Locus Allele capacity),
        HasDerivWithinAt
          (fun s : ℝ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(K s.toNNReal x))
          (∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x))
          (Set.Ici 0) t :=
  exists_markovKernel_neutralGenerator rates capacity (neutralPolynomialSemigroup rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_one rates ℓ₀ hap₀) (neutralPolynomialSemigroup_nonneg rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_add rates ℓ₀ hap₀)
    (fun t ξ x ↦ neutralPolynomialSemigroup_momentPolynomial rates ℓ₀ hap₀ capacity t ξ x)

end

end Descent.Portability.NeutralPolynomialPositivity
