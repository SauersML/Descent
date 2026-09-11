/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAuditDesign
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14: the finite shared-contrast audit
program is convex and has an attained optimum. Positive probability floors
ensure continuity of the actual reciprocal objective on the compact design
set. No optimizer status or supplied optimality hypothesis is used for the
existence statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAuditDesignConvexity

open FiniteAuditDesign
open scoped BigOperators

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- Expected cost is continuous in all audit probabilities. -/
theorem continuous_spending (c : ι → ℝ) : Continuous (spending c) :=
  continuous_finset_sum _ (fun i _ ↦ continuous_const.mul (continuous_apply i))

/-- Expected cost respects convex combinations exactly. -/
theorem spending_mix (c p q : ι → ℝ) (α β : ℝ) :
    spending c (α • p + β • q) = α * spending c p + β * spending c q := by
  simp only [spending, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- The probability box intersected with the expected-budget halfspace is compact. -/
theorem feasible_compact (floor c : ι → ℝ) (B : ℝ) :
    IsCompact {p | Feasible floor c B p} := by
  have he : {p | Feasible floor c B p} =
      Set.Icc floor (fun _ : ι ↦ (1 : ℝ)) ∩ {p | spending c p ≤ B} := by
    ext p
    simp only [Feasible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, Pi.le_def,
      forall_and]
  rw [he]
  exact isCompact_Icc.inter_right (isClosed_le (continuous_spending c) continuous_const)

/-- The design constraints form a convex set, including budgets at the feasibility boundary. -/
theorem feasible_convex (floor c : ι → ℝ) (B : ℝ) :
    Convex ℝ {p | Feasible floor c B p} := by
  intro p hp q hq α β hα hβ hsum
  constructor
  · intro i
    change floor i ≤ α * p i + β * q i ∧ α * p i + β * q i ≤ 1
    constructor
    · have hl := add_le_add (mul_le_mul_of_nonneg_left (hp.1 i).1 hα)
        (mul_le_mul_of_nonneg_left (hq.1 i).1 hβ)
      rwa [← add_mul, hsum, one_mul] at hl
    · have hu := add_le_add (mul_le_mul_of_nonneg_left (hp.1 i).2 hα)
        (mul_le_mul_of_nonneg_left (hq.1 i).2 hβ)
      nlinarith [hu]
  · rw [spending_mix]
    have hh := add_le_add (mul_le_mul_of_nonneg_left hp.2 hα)
      (mul_le_mul_of_nonneg_left hq.2 hβ)
    rwa [← add_mul, hsum, one_mul] at hh

/-- The reciprocal variance contribution satisfies Jensen's inequality on positive probabilities. -/
theorem reciprocal_jensen (A x y α β : ℝ) (hA : 0 ≤ A) (hx : 0 < x) (hy : 0 < y)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β = 1) :
    A / (α * x + β * y) ≤ α * (A / x) + β * (A / y) := by
  let z := α * x + β * y
  have hz : 0 < z := by
    rcases eq_or_lt_of_le hα with he | he
    · have ha : α = 0 := he.symm
      have hb : β = 1 := by linarith
      simpa [z, ha, hb] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos he hx) (mul_nonneg hβ hy.le)
  have he : x * y * z * (α / x + β / y - 1 / z) = α * β * (x - y) ^ 2 := by
    have hb : β = 1 - α := by linarith
    field_simp [hx.ne', hy.ne', hz.ne']
    dsimp [z]
    rw [hb]
    ring
  have hn : 0 ≤ α * β * (x - y) ^ 2 := by positivity
  have hden : 0 < x * y * z := by positivity
  have hh : 1 / z ≤ α / x + β / y := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh hA
  dsimp [z] at hm
  convert hm using 1 <;> ring

/-- The actual max-contrast objective is convex on the feasible positive-probability design set. -/
theorem objective_convex (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) :
    ConvexOn ℝ {p | Feasible floor c B p} (worstVariance a) := by
  refine ⟨feasible_convex floor c B, ?_⟩
  intro p hp q hq α β hα hβ hsum
  change worstVariance a (α • p + β • q) ≤ α * worstVariance a p + β * worstVariance a q
  apply Finset.sup'_le
  intro j _
  calc
    rowVariance a (α • p + β • q) j ≤ α * rowVariance a p j + β * rowVariance a q j := by
      simp only [rowVariance, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ ↦ reciprocal_jensen (a j i) (p i) (q i) α β
        (ha j i) ((hf i).trans_le (hp.1 i).1) ((hf i).trans_le (hq.1 i).1) hα hβ hsum)
    _ ≤ α * worstVariance a p + β * worstVariance a q :=
      add_le_add (mul_le_mul_of_nonneg_left (row_le_worst a p j) hα)
        (mul_le_mul_of_nonneg_left (row_le_worst a q j) hβ)

/-- Positive floors keep every reciprocal denominator away from zero on the feasible set. -/
theorem objective_continuous (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (hf : ∀ i, 0 < floor i) : ContinuousOn (worstVariance a) {p | Feasible floor c B p} := by
  apply ContinuousOn.finset_sup'_apply
  intro j _
  apply continuousOn_finset_sum
  intro i _
  exact continuousOn_const.div (continuous_apply i).continuousOn
    (fun p hp ↦ ne_of_gt ((hf i).trans_le (hp.1 i).1))

/-- Every nonempty feasible audit design has a genuine attained minimum. -/
theorem optimum_exists (a : J → ι → ℝ) (floor c : ι → ℝ) (B : ℝ)
    (hf : ∀ i, 0 < floor i) (hne : {p | Feasible floor c B p}.Nonempty) :
    ∃ p, Feasible floor c B p ∧ IsMinOn (worstVariance a) {q | Feasible floor c B q} p :=
  (feasible_compact floor c B).exists_isMinOn hne (objective_continuous a floor c B hf)

end Descent.Portability.FiniteAuditDesignConvexity
