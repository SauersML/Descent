/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralStateTangency

assert_below Descent.Decision Descent.Program

/-!
# The dual semigroup respects the relations among configuration moments

This module carries NOTE1 §4.2a from formal configuration vectors to functions of the state.
Configuration moments `H_ξ` are linearly dependent as functions of the multi-deme haplotype
frequencies, so the finite matrix exponential of the dual generator `Q` of
`PartialHaplotypeDualSemigroup` can only define an operator on polynomial functions if it
respects every linear relation among the moments. That is proved here, together with the
independence of the construction from the chosen material budget.

Vanishing combinations. `momentVector capacity x` is the vector of budget-respecting
configuration moments at the state `x`, and `vanishingCombinations capacity` is the subspace of
coefficient vectors `a` with `a ⬝ H(x) = 0` at every state. By NOTE1 (19) in matrix form the
generator of the combination `Σ_η a_η H_η` is `(a Q) ⬝ H` on states
(`eval_neutralGenerator_combination`), and by the tangency theorem of `NeutralStateTangency`
the dual generator therefore preserves vanishing combinations (`vecMul_dualGenerator_mem`). The
finite Taylor sums of the exponential preserve them term by term, and the exponential is their
limit, so `vecMul_matrixExponential_mem`: `a e^{tQ}` vanishes on states whenever `a` does.

Budget independence. For budgets `c ≤ c'` the inclusion `budgetInclusion c c'` of the
configurations intertwines the dual generators (`budgetInclusion_mul_dualGenerator`): every
dual transition from a configuration within `c` lands within `c` or in the cemetery. Hence it
intertwines the exponentials (`budgetInclusion_mul_matrixExponential`), and the evolved moment
of a configuration is the same under every budget that contains it
(`matrixExponential_mulVec_budget`). Configuration moments are nonnegative on states
(`momentVector_nonneg`).

Scope. This module supplies the invariance and budget independence of the dual semigroup; the
polynomial operators built from it, their positivity, and the kernel semigroup are assembled
downstream.

## Empirical status

None. The bodies here are linear algebra: matrix exponentials of a supplied rate table acting on
vectors of polynomial values at per-deme probability vectors, so no measurement on any
population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralMomentSemigroup

open MvPolynomial Filter Topology Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  NeutralFellerGenerator NeutralStateTangency

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ### Vanishing combinations of configuration moments -/

/-- The configuration moments of a state over the budget-respecting configurations. -/
def momentVector (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun η ↦ eval x.1 (momentPolynomial η.1)

/-- The coefficient vectors whose combination of configuration moments vanishes on every
state. -/
def vanishingCombinations (capacity : Locus → ℕ) :
    Submodule ℝ (BudgetConfiguration Deme Locus Allele capacity → ℝ) where
  carrier := {a | ∀ x : FrequencyState Deme Locus Allele, a ⬝ᵥ momentVector capacity x = 0}
  add_mem' ha hb x := by rw [add_dotProduct, ha x, hb x, add_zero]
  zero_mem' x := zero_dotProduct _
  smul_mem' c _ ha x := by rw [smul_dotProduct, ha x, smul_zero]

/-- NOTE1 (19) on coefficient vectors: on states, the neutral generator of a combination of
configuration moments is the combination of the dual-generator rows. -/
theorem eval_neutralGenerator_combination (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (a : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (x : FrequencyState Deme Locus Allele) :
    eval x.1 (neutralGenerator rates (∑ η, C (a η) * momentPolynomial η.1))
      = (a ᵥ* dualGenerator rates capacity) ⬝ᵥ momentVector capacity x := by
  have hCmul : ∀ (r : ℝ) (p : FrequencyPolynomial Deme Locus Allele),
      neutralGenerator rates (C r * p) = C r * neutralGenerator rates p := by
    intro r p
    have hL : neutralGenerator rates (C r) = 0 := by
      simp [neutralGenerator, demeSecondOrder, pderiv_C]
    have hl : halfCovariance rates (C r) p = 0 := by
      simp [halfCovariance, demeCovarianceForm, pderiv_C]
    have hr : halfCovariance rates p (C r) = 0 := by
      simp [halfCovariance, demeCovarianceForm, pderiv_C]
    rw [neutralGenerator_mul, hL, hl, hr]
    ring
  rw [← Matrix.dotProduct_mulVec, ← neutralGeneratorAddHom_apply, map_sum, map_sum, dotProduct]
  refine Finset.sum_congr rfl fun η _ ↦ ?_
  rw [neutralGeneratorAddHom_apply, hCmul, map_mul, eval_C]
  exact congrArg (a η * ·)
    (polynomialFunction_neutralGenerator_momentPolynomial rates capacity η x)

/-- The dual generator carries vanishing combinations to vanishing combinations: this is the
tangency of the neutral generator to the states. -/
theorem vecMul_dualGenerator_mem (rates : NeutralRates Deme Locus Allele)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ)
    (a : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (ha : a ∈ vanishingCombinations capacity) :
    a ᵥ* dualGenerator rates capacity ∈ vanishingCombinations capacity := by
  intro x
  rw [← eval_neutralGenerator_combination]
  refine eval_neutralGenerator_of_vanishing rates hap₀ _ (fun y ↦ ?_) x
  have hy := ha y
  simpa only [map_sum, map_mul, eval_C, dotProduct, momentVector] using hy

/-- **The dual semigroup respects the relations among configuration moments.** If a
combination of configuration moments vanishes on every state, so does its image under
`e^{tQ}`. -/
theorem vecMul_matrixExponential_mem (rates : NeutralRates Deme Locus Allele)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) (t : ℝ)
    (a : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (ha : a ∈ vanishingCombinations capacity) :
    a ᵥ* matrixExponential (dualGenerator rates capacity) t
      ∈ vanishingCombinations capacity := by
  have hpow : ∀ n : ℕ,
      a ᵥ* dualGenerator rates capacity ^ n ∈ vanishingCombinations capacity := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, Matrix.vecMul_one] using ha
    | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul]
      exact vecMul_dualGenerator_mem rates hap₀ capacity _ ih
  have hsum : ∀ n : ℕ, a ᵥ* matrixExponentialPartialSum (dualGenerator rates capacity) t n
      ∈ vanishingCombinations capacity := by
    intro n
    induction n with
    | zero =>
      simpa only [matrixExponentialPartialSum, Finset.range_zero, Finset.sum_empty,
        Matrix.vecMul_zero] using (vanishingCombinations capacity).zero_mem
    | succ n ih =>
      rw [matrixExponentialPartialSum, Finset.sum_range_succ, Matrix.vecMul_add]
      refine Submodule.add_mem _ ih ?_
      rw [smul_pow, Matrix.vecMul_smul, Matrix.vecMul_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hpow n))
  intro x
  have hcont : Continuous fun M : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ ↦
        a ⬝ᵥ (M *ᵥ momentVector capacity x) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have hlim := (hcont.tendsto _).comp
    (matrixExponentialPartialSum_tendsto (dualGenerator rates capacity) t)
  rw [← Matrix.dotProduct_mulVec]
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n ↦ ?_)
  show 0 = a ⬝ᵥ
    (matrixExponentialPartialSum (dualGenerator rates capacity) t n *ᵥ momentVector capacity x)
  rw [Matrix.dotProduct_mulVec]
  exact (hsum n x).symm

/-! ### Independence of the material budget -/

/-- A budget-respecting configuration respects every larger budget. -/
theorem withinBudget_of_capacity_le {capacity capacity' : Locus → ℕ}
    (hle : ∀ ℓ, capacity ℓ ≤ capacity' ℓ) {ξ : Multiset (PartialType Deme Locus Allele)}
    (h : WithinBudget capacity ξ) : WithinBudget capacity' ξ :=
  fun ℓ ↦ (h ℓ).trans (hle ℓ)

/-- The inclusion of the configurations within one budget among those within another, as a
rectangular zero-one matrix. -/
def budgetInclusion (capacity capacity' : Locus → ℕ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity') ℝ :=
  fun ξ η ↦ if ξ.1 = η.1 then 1 else 0

/-- Applying the budget inclusion to a vector reads the vector at the included configuration. -/
theorem budgetInclusion_mulVec (capacity capacity' : Locus → ℕ)
    (hle : ∀ ℓ, capacity ℓ ≤ capacity' ℓ)
    (v : BudgetConfiguration Deme Locus Allele capacity' → ℝ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (budgetInclusion capacity capacity' *ᵥ v) ξ
      = v ⟨ξ.1, withinBudget_of_capacity_le hle ξ.2⟩ := by
  simp only [Matrix.mulVec, dotProduct, budgetInclusion, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨ξ.1, withinBudget_of_capacity_le hle ξ.2⟩]
  · simp
  · intro η _ hne
    exact if_neg fun h ↦ hne (Subtype.ext h.symm)
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- The budget inclusion intertwines the dual generators: every dual transition from a
configuration within the smaller budget lands within it or in the cemetery. -/
theorem budgetInclusion_mul_dualGenerator (rates : NeutralRates Deme Locus Allele)
    (capacity capacity' : Locus → ℕ) (hle : ∀ ℓ, capacity ℓ ≤ capacity' ℓ) :
    budgetInclusion capacity capacity' * dualGenerator rates capacity'
      = dualGenerator rates capacity * budgetInclusion capacity capacity' := by
  ext ξ η
  have hleft : (budgetInclusion capacity capacity' * dualGenerator rates capacity') ξ η
      = dualGenerator rates capacity' ⟨ξ.1, withinBudget_of_capacity_le hle ξ.2⟩ η := by
    simp only [Matrix.mul_apply, budgetInclusion, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single ⟨ξ.1, withinBudget_of_capacity_le hle ξ.2⟩]
    · simp
    · intro ζ _ hne
      exact if_neg fun h ↦ hne (Subtype.ext h.symm)
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  rw [hleft]
  simp only [Matrix.mul_apply, budgetInclusion, mul_ite, mul_one, mul_zero]
  by_cases hη : WithinBudget capacity η.1
  · rw [Finset.sum_eq_single ⟨η.1, hη⟩]
    · rw [if_pos rfl]
      simp only [dualGenerator, Subtype.ext_iff]
    · intro ζ _ hne
      exact if_neg fun h ↦ hne (Subtype.ext h)
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [Finset.sum_eq_zero fun ζ _ ↦ if_neg fun h ↦ hη (h ▸ ζ.2)]
    have hne : (⟨ξ.1, withinBudget_of_capacity_le hle ξ.2⟩ :
        BudgetConfiguration Deme Locus Allele capacity') ≠ η := fun h ↦ hη (h ▸ ξ.2)
    simp only [dualGenerator]
    rw [if_neg hne, sub_zero, jumpRate]
    refine Multiset.sum_eq_zero fun r hr ↦ ?_
    obtain ⟨transition, htransition, rfl⟩ := Multiset.mem_map.mp hr
    exact if_neg fun htarget ↦
      hη (dualTransitions_withinBudget rates capacity ξ.1 ξ.2 transition htransition η.1 htarget)

/-- The budget inclusion intertwines the dual semigroups. -/
theorem budgetInclusion_mul_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (capacity capacity' : Locus → ℕ) (hle : ∀ ℓ, capacity ℓ ≤ capacity' ℓ) (t : ℝ) :
    budgetInclusion capacity capacity' * matrixExponential (dualGenerator rates capacity') t
      = matrixExponential (dualGenerator rates capacity) t
          * budgetInclusion capacity capacity' :=
  matrixExponential_intertwines _ _ _
    (budgetInclusion_mul_dualGenerator rates capacity capacity' hle) t

/-- **Budget independence.** The evolved moment of a configuration is the same under every
budget that contains it. -/
theorem matrixExponential_mulVec_budget (rates : NeutralRates Deme Locus Allele)
    (capacity capacity' : Locus → ℕ) (hle : ∀ ℓ, capacity ℓ ≤ capacity' ℓ) (t : ℝ)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (matrixExponential (dualGenerator rates capacity') t *ᵥ momentVector capacity' x)
        ⟨ξ.1, withinBudget_of_capacity_le hle ξ.2⟩
      = (matrixExponential (dualGenerator rates capacity) t *ᵥ momentVector capacity x) ξ := by
  have h := congrArg (fun M ↦ (M *ᵥ momentVector capacity' x) ξ)
    (budgetInclusion_mul_matrixExponential rates capacity capacity' hle t)
  simp only [← Matrix.mulVec_mulVec] at h
  rw [budgetInclusion_mulVec capacity capacity' hle] at h
  have hmoment : budgetInclusion capacity capacity' *ᵥ momentVector capacity' x
      = momentVector capacity x := by
    funext ζ
    rw [budgetInclusion_mulVec capacity capacity' hle]
    rfl
  rw [hmoment] at h
  exact h

/-- Configuration moments are nonnegative on the frequency states. -/
theorem momentVector_nonneg (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele)
    (η : BudgetConfiguration Deme Locus Allele capacity) : 0 ≤ momentVector capacity x η := by
  simp only [momentVector]
  rw [← lawPoint_stateLaw x, eval_momentPolynomial, configurationMoment]
  refine Multiset.prod_nonneg fun r hr ↦ ?_
  obtain ⟨τ, _, rfl⟩ := Multiset.mem_map.mp hr
  rw [marginalFrequency]
  exact Finset.sum_nonneg fun hap _ ↦ (stateLaw x τ.deme).mass_nonneg hap

end

end Descent.Portability.NeutralMomentSemigroup
