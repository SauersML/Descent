/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditAllocationCoordinate

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14, finite-contrast allocation.
The shared design objective is the actual maximum of reciprocal variance
contributions. A computed dual lower bound uses the exact capped coordinate
minimizers. Feasible designs and simplex multipliers with active-contrast
and budget complementarity conditions certify a global optimum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAuditDesign

open scoped BigOperators

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- Expected labeling cost of one independent Bernoulli audit. -/
noncomputable def spending (c p : ι → ℝ) : ℝ := ∑ i, c i * p i

/-- The allowed probability box and expected labeling budget. -/
def Feasible (floor c : ι → ℝ) (B : ℝ) (p : ι → ℝ) : Prop :=
  (∀ i, p i ∈ Set.Icc (floor i) 1) ∧ spending c p ≤ B

/-- Worst-case variance for one tolerance-normalized contrast. -/
noncomputable def rowVariance (a : J → ι → ℝ) (p : ι → ℝ) (j : J) : ℝ := ∑ i, a j i / p i

/-- The common-audit worst-contrast variance objective. -/
noncomputable def worstVariance (a : J → ι → ℝ) (p : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (rowVariance a p)

/-- One simplex-weighted variance contribution per audit unit. -/
noncomputable def contribution (a : J → ι → ℝ) (η : J → ℝ) (i : ι) : ℝ := ∑ j, η j * a j i

/-- The exact dual bound, evaluated by the proved clipped square-root coordinate formula. -/
noncomputable def dualBound (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (λ : ℝ) : ℝ :=
  -λ * B + ∑ i, AuditAllocationCoordinate.objective (contribution a η i) (λ * c i)
    (AuditAllocationCoordinate.choice (contribution a η i) (λ * c i) (floor i))

/-- Every contrast variance is bounded by the actual maximum objective. -/
theorem row_le_worst (a : J → ι → ℝ) (p : ι → ℝ) (j : J) :
    rowVariance a p j ≤ worstVariance a p :=
  Finset.le_sup' (f := rowVariance a p) (Finset.mem_univ j)

/-- Nonnegative simplex weights preserve nonnegative variance contributions. -/
theorem contribution_nonneg (a : J → ι → ℝ) (η : J → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hη : ∀ j, 0 ≤ η j) (i : ι) :
    0 ≤ contribution a η i := Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hη j) (ha j i))

/-- The column-weighted reciprocal sum is the same shared contrast variance combination. -/
theorem weighted_identity (a : J → ι → ℝ) (η : J → ℝ) (p : ι → ℝ) :
    (∑ i, contribution a η i / p i) = ∑ j, η j * rowVariance a p j := by
  simp only [contribution, rowVariance, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  exact Finset.sum_comm

/-- Every simplex combination of contrasts is below the maximum contrast variance. -/
theorem weighted_le_worst (a : J → ι → ℝ) (η : J → ℝ) (p : ι → ℝ)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) :
    (∑ j, η j * rowVariance a p j) ≤ worstVariance a p := by
  calc
    _ ≤ ∑ j, η j * worstVariance a p := Finset.sum_le_sum
      (fun j _ ↦ mul_le_mul_of_nonneg_left (row_le_worst a p j) (hη j))
    _ = worstVariance a p := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The Lagrangian separates exactly into the weighted variance and the budget term. -/
theorem lagrangian_identity (a : J → ι → ℝ) (η : J → ℝ) (c p : ι → ℝ) (λ B : ℝ) :
    -λ * B + (∑ i, AuditAllocationCoordinate.objective (contribution a η i) (λ * c i) (p i)) =
      (∑ j, η j * rowVariance a p j) + λ * (spending c p - B) := by
  simp only [AuditAllocationCoordinate.objective, Finset.sum_add_distrib, weighted_identity,
    mul_assoc, ← Finset.mul_sum, spending]
  ring

/-- Every valid dual choice gives a certified lower bound for every feasible audit allocation. -/
theorem weak_duality (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (λ : ℝ) (p : ι → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) (hλ : 0 ≤ λ)
    (hp : Feasible floor c B p) : dualBound a floor c B η λ ≤ worstVariance a p := by
  unfold dualBound
  calc
    _ ≤ -λ * B + ∑ i, AuditAllocationCoordinate.objective (contribution a η i) (λ * c i) (p i) := by
      apply add_le_add_left
      exact Finset.sum_le_sum (fun i _ ↦ AuditAllocationCoordinate.choice_minimum
        (contribution a η i) (λ * c i) (floor i) (p i)
        (contribution_nonneg a η ha hη i) (mul_nonneg hλ (hc i)) (hf i) (hp.1 i))
    _ = (∑ j, η j * rowVariance a p j) + λ * (spending c p - B) :=
      lagrangian_identity a η c p λ B
    _ ≤ worstVariance a p := by
      have hb : λ * (spending c p - B) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hλ (sub_nonpos.mpr hp.2)
      linarith [weighted_le_worst a η p hη hsum]

/-- Multipliers supported on active contrasts make the variance averaging bound an equality. -/
theorem active_weighted_eq (a : J → ι → ℝ) (η : J → ℝ) (p : ι → ℝ)
    (hsum : ∑ j, η j = 1)
    (hactive : ∀ j, η j ≠ 0 → rowVariance a p j = worstVariance a p) :
    (∑ j, η j * rowVariance a p j) = worstVariance a p := by
  calc
    _ = ∑ j, η j * worstVariance a p := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : η j = 0
      · simp only [hz, zero_mul]
      · rw [hactive j hz]
    _ = worstVariance a p := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Coordinate minimization and complementarity produce an exact primal-dual value match. -/
theorem certificate_equality (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (λ : ℝ) (p : ι → ℝ) (hsum : ∑ j, η j = 1)
    (hchoice : ∀ i, p i =
      AuditAllocationCoordinate.choice (contribution a η i) (λ * c i) (floor i))
    (hactive : ∀ j, η j ≠ 0 → rowVariance a p j = worstVariance a p)
    (hbudget : λ * (spending c p - B) = 0) :
    dualBound a floor c B η λ = worstVariance a p := by
  unfold dualBound
  simp_rw [← hchoice]
  rw [lagrangian_identity, active_weighted_eq a η p hsum hactive, hbudget, add_zero]

/-- The explicit certificate proves optimality against every feasible competing allocation. -/
theorem certified_optimum (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (λ : ℝ) (p : ι → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) (hλ : 0 ≤ λ)
    (hp : Feasible floor c B p)
    (hchoice : ∀ i, p i =
      AuditAllocationCoordinate.choice (contribution a η i) (λ * c i) (floor i))
    (hactive : ∀ j, η j ≠ 0 → rowVariance a p j = worstVariance a p)
    (hbudget : λ * (spending c p - B) = 0) :
    IsMinOn (worstVariance a) {q | Feasible floor c B q} p := by
  intro q hq
  rw [← certificate_equality a floor c B η λ p hsum hchoice hactive hbudget]
  exact weak_duality a floor c B η λ q ha hf hc hη hsum hλ hq

end Descent.Portability.FiniteAuditDesign
