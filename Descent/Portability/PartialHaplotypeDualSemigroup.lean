/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualGenerator
import Descent.Portability.SubstochasticGeneratorSemigroup
import Descent.Portability.StationaryHaplotypeRealization
import Mathlib.Analysis.ODE.Gronwall

assert_below Descent.Decision Descent.Program

/-!
# The finite partial-haplotype dual semigroup

This module formalizes NOTE1 (20).  The budget-respecting configurations of (18) form a finite
state space, and the dual transitions of (19) define a generator `Q` on it: the total jump rate
into each configuration off the diagonal, minus the total exit rate on the diagonal.  The exit
rate includes absorption into the cemetery, so `Q` is a killing generator in the sense of
`Descent.Portability.SubstochasticGeneratorSemigroup`, and its exact matrix exponential is
substochastic at every nonnegative time.

The generator identity (19) becomes a matrix identity: `Q` applied to the vector of configuration
moments of any per-deme haplotype laws is the neutral diffusion generator applied to the moment
polynomial, evaluated at those laws (`dualGenerator_mulVec_configurationMoment`).  The identity
uses that every dual transition from a budget-respecting configuration lands in the state space
or in the cemetery.

The likelihood representation (20) is a uniqueness theorem for the linear system `v' = Q v`.
Take any family of expectation functionals over per-deme haplotype laws whose expected
configuration moments have, on `[0, ∞)`, right derivative equal to the expected generator: the
forward moment equation of the diffusion.  By the matrix identity the expected moment vector
solves `v' = Q v`; the exact orbit `e^{tQ} v(0)` solves the same system; and a Lipschitz linear
vector field has at most one solution with a given initial value.  Hence the expected moment
vector is `e^{tQ} v(0)` at every `t ≥ 0` (`expectedMomentVector_eq_matrixExponential`).

Scope.  The forward moment equation is a hypothesis on the expectation family; it is not derived
here from a constructed diffusion process, whose construction is NOTE1 §4.2a.  Changing
demographic histories, splits and admixture pulses are not composed here.

## Empirical status

None.  The bodies here are algebra: a matrix exponential of a supplied rate table and linear
functionals of supplied laws, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeDualSemigroup

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator SubstochasticGeneratorSemigroup
open Descent.Coalescent Descent.Foundations MvPolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- The budget-respecting configurations of (18): the state space of the dual chain. -/
abbrev BudgetConfiguration (Deme Locus : Type*) (Allele : Locus → Type*)
    (capacity : Locus → ℕ) :=
  {ξ : Multiset (PartialType Deme Locus Allele) // WithinBudget capacity ξ}

/-- There are finitely many budget-respecting configurations. -/
noncomputable instance instFintypeBudgetConfiguration (capacity : Locus → ℕ) :
    Fintype (BudgetConfiguration Deme Locus Allele capacity) :=
  (withinBudget_finite capacity).fintype

/-- The total rate of the dual transitions from one configuration into another. -/
def jumpRate (rates : NeutralRates Deme Locus Allele)
    (ξ η : Multiset (PartialType Deme Locus Allele)) : ℝ :=
  ((dualTransitions rates ξ).map fun transition ↦
    if transition.2 = some η then transition.1 else 0).sum

/-- The total rate of all dual transitions out of a configuration, the cemetery included. -/
def exitRate (rates : NeutralRates Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) : ℝ :=
  ((dualTransitions rates ξ).map Prod.fst).sum

/-- **The dual generator `Q` of NOTE1 (20)** on the budget-respecting state space: jump rates
off the diagonal and minus the total exit rate, cemetery included, on the diagonal. -/
def dualGenerator (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fun ξ η ↦ jumpRate rates ξ.1 η.1 - if ξ = η then exitRate rates ξ.1 else 0

/-- Summing a target indicator over the budget-respecting configurations gives the value at the
target, or zero at the cemetery, when every proper target respects the budget. -/
theorem sum_target_indicator (capacity : Locus → ℕ)
    (target : Option (Multiset (PartialType Deme Locus Allele)))
    (htarget : ∀ η, target = some η → WithinBudget capacity η)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ) :
    ∑ η : BudgetConfiguration Deme Locus Allele capacity,
        (if target = some η.1 then value η.1 else 0) = target.elim 0 value := by
  cases target with
  | none => simp
  | some ζ =>
    rw [Finset.sum_eq_single ⟨ζ, htarget ζ rfl⟩]
    · simp
    · intro η _ hne
      refine if_neg fun heq ↦ hne (Subtype.ext ?_)
      exact (Option.some.inj heq).symm
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot

/-- **The dual generator acts through the dual transitions.**  For a budget-respecting
configuration `ξ` and any table of values `w`, `Σ_η Q_{ξη} w(η)` is the sum over the dual
transitions of the rate times `w(target) − w(ξ)`, with `w(†) = 0`. -/
theorem dualGenerator_mulVec (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (dualGenerator rates capacity).mulVec (fun η ↦ value η.1) ξ
      = ((dualTransitions rates ξ.1).map fun transition ↦
          transition.1 * (transition.2.elim 0 value - value ξ.1)).sum := by
  have hjump : ∀ η : BudgetConfiguration Deme Locus Allele capacity,
      jumpRate rates ξ.1 η.1 * value η.1
        = ((dualTransitions rates ξ.1).map fun transition ↦
            if transition.2 = some η.1 then transition.1 * value η.1 else 0).sum := by
    intro η
    rw [jumpRate, ← Multiset.sum_map_mul_right]
    congr 1
    exact Multiset.map_congr rfl fun transition _ ↦ by rw [ite_mul, zero_mul]
  have hswap : ∑ η : BudgetConfiguration Deme Locus Allele capacity,
        ((dualTransitions rates ξ.1).map fun transition ↦
            if transition.2 = some η.1 then transition.1 * value η.1 else 0).sum
      = ((dualTransitions rates ξ.1).map fun transition ↦
          ∑ η : BudgetConfiguration Deme Locus Allele capacity,
            if transition.2 = some η.1 then transition.1 * value η.1 else 0).sum := by
    simp only [Finset.sum_eq_multiset_sum]
    exact Multiset.sum_map_sum_map _ _
  have hexit : exitRate rates ξ.1 * value ξ.1
      = ((dualTransitions rates ξ.1).map fun transition ↦ transition.1 * value ξ.1).sum := by
    rw [exitRate, ← Multiset.sum_map_mul_right]
  simp only [Matrix.mulVec, dotProduct, dualGenerator, sub_mul, Finset.sum_sub_distrib, hjump,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hswap, hexit, ← Multiset.sum_map_sub]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun transition htransition ↦ ?_)
  have htarget := dualTransitions_withinBudget rates capacity ξ.1 ξ.2 transition htransition
  rw [show (∑ η : BudgetConfiguration Deme Locus Allele capacity,
        if transition.2 = some η.1 then transition.1 * value η.1 else 0)
      = transition.2.elim 0 (fun ζ ↦ transition.1 * value ζ) from
    sum_target_indicator capacity transition.2 htarget fun ζ ↦ transition.1 * value ζ]
  rcases transition with ⟨rate, _ | ζ⟩ <;> simp only [Option.elim] <;> ring

/-- **The dual generator is a killing generator.**  Its off-diagonal entries are sums of
nonnegative rates, and every row sums to minus the rate of absorption into the cemetery. -/
theorem killingGenerator_dualGenerator (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) : KillingGenerator (dualGenerator rates capacity) where
  metzler := by
    intro ξ η hne
    have hentry : dualGenerator rates capacity ξ η = jumpRate rates ξ.1 η.1 := by
      simp [dualGenerator, hne]
    rw [hentry, jumpRate]
    refine Multiset.sum_nonneg fun r hr ↦ ?_
    obtain ⟨transition, htransition, rfl⟩ := Multiset.mem_map.mp hr
    split_ifs
    · exact dualTransitions_rate_nonneg rates ξ.1 transition htransition
    · exact le_rfl
  rowSum_nonpos := by
    intro ξ
    have hrow := dualGenerator_mulVec rates capacity (fun _ ↦ 1) ξ
    simp only [Matrix.mulVec, dotProduct, mul_one] at hrow
    rw [hrow]
    refine le_trans (Multiset.sum_map_le_sum_map _ (fun _ ↦ (0 : ℝ))
      fun transition htransition ↦ ?_) (by simp)
    have hrate : 0 ≤ transition.1 := dualTransitions_rate_nonneg rates ξ.1 _ htransition
    rcases transition with ⟨rate, _ | ζ⟩
    · simp only [Option.elim] at hrate ⊢
      nlinarith [hrate]
    · simp only [Option.elim, sub_self, mul_zero, le_refl]

/-- The exact dual propagator `e^{tQ}` is substochastic at every nonnegative time. -/
theorem dualPropagator_substochastic (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (time : ℝ) (htime : 0 ≤ time) :
    SubstochasticMatrix (matrixExponential (dualGenerator rates capacity) time) :=
  matrixExponential_substochastic _ (killingGenerator_dualGenerator rates capacity) time htime

/-- **NOTE1 (19) in matrix form.**  The dual generator applied to the vector of configuration
moments of per-deme haplotype laws is the neutral generator applied to the moment polynomial,
evaluated at those laws. -/
theorem dualGenerator_mulVec_configurationMoment (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (dualGenerator rates capacity).mulVec (fun η ↦ configurationMoment law η.1) ξ
      = eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)) := by
  rw [dualGenerator_mulVec, neutralGenerator_configurationMoment]

/-- The vector of expected configuration moments at time `s` over the budget-respecting
configurations. -/
def expectedMomentVector (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) : BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun ξ ↦ expectationAt s fun law ↦ configurationMoment law ξ.1

/-- The expected generator of a configuration moment is the dual generator applied to the
expected moment vector. -/
theorem expectedGenerator_eq_mulVec (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (expectationAt s fun law ↦
        eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
      = (dualGenerator rates capacity).mulVec
          (expectedMomentVector capacity expectationAt s) ξ := by
  have hpoint : (fun law ↦ eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
      = ∑ η, dualGenerator rates capacity ξ η • fun law ↦ configurationMoment law η.1 := by
    funext law
    rw [← dualGenerator_mulVec_configurationMoment rates capacity law ξ]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [hpoint, ExpFunctional.eval_sum]
  simp only [ExpFunctional.smul_eval, Matrix.mulVec, dotProduct, expectedMomentVector]

/-- **NOTE1 (20): the finite likelihood representation.**  Suppose the expected configuration
moments of a family of expectation functionals over per-deme haplotype laws satisfy the forward
moment equation on `[0, ∞)`: their right derivative is the expected neutral generator of the
moment polynomial.  Then at every time `t ≥ 0` the expected moment vector over the
budget-respecting configurations is `e^{tQ}` applied to its initial value. -/
theorem expectedMomentVector_eq_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        (Set.Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) :
    expectedMomentVector capacity expectationAt t
      = (matrixExponential (dualGenerator rates capacity) t).mulVec
          (expectedMomentVector capacity expectationAt 0) := by
  have hmoment : ∀ s ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (expectedMomentVector capacity expectationAt)
        ((dualGenerator rates capacity).mulVec (expectedMomentVector capacity expectationAt s))
        (Set.Ici 0) s := by
    intro s hs
    refine hasDerivWithinAt_pi.mpr fun ξ ↦ ?_
    rw [← expectedGenerator_eq_mulVec]
    exact hforward ξ s hs
  have horbit : ∀ s : ℝ, HasDerivAt
      (fun r ↦ (matrixExponential (dualGenerator rates capacity) r).mulVec
        (expectedMomentVector capacity expectationAt 0))
      ((dualGenerator rates capacity).mulVec
        ((matrixExponential (dualGenerator rates capacity) s).mulVec
          (expectedMomentVector capacity expectationAt 0))) s :=
    fun s ↦ StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec _ _ s
  have hlip : LipschitzWith
      ‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin (dualGenerator rates capacity))‖₊
      fun w : BudgetConfiguration Deme Locus Allele capacity → ℝ ↦
        (dualGenerator rates capacity).mulVec w := by
    have h := (LinearMap.toContinuousLinearMap
      (Matrix.mulVecLin (dualGenerator rates capacity))).lipschitz
    rwa [LinearMap.coe_toContinuousLinearMap', Matrix.coe_mulVecLin] at h
  have hunique := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ w ↦ (dualGenerator rates capacity).mulVec w) (s := fun _ ↦ Set.univ)
    (a := 0) (b := t)
    (fun _ _ ↦ hlip.lipschitzOnWith)
    (fun s hs ↦ (hmoment s hs.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
    (fun s hs ↦ (hmoment s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (fun _ _ ↦ Set.mem_univ _)
    (fun s _ ↦ (horbit s).continuousAt.continuousWithinAt)
    (fun s _ ↦ (horbit s).hasDerivWithinAt)
    (fun _ _ ↦ Set.mem_univ _)
    (by simp only [matrixExponential_zero, Matrix.one_mulVec])
  exact hunique ⟨ht, le_rfl⟩

end

end Descent.Portability.PartialHaplotypeDualSemigroup
