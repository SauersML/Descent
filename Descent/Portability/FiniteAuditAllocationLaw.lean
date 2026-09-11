/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAuditStrongDuality

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14: the attained finite-library dual
forces each primal coordinate to minimize its Lagrangian term. A positive
budget multiplier gives a unique coordinate minimizer and hence the exact
clipped square-root allocation, rather than only a sufficient certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAuditAllocationLaw

open FiniteAuditDesign AuditVarianceGeometry
open scoped BigOperators

/-- Positive cost makes the clipped square root the unique coordinate optimum. -/
theorem positive_multiplier_unique (A b floor p : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hf : 0 < floor) (hp : p ∈ Set.Icc floor 1)
    (heq : AuditAllocationCoordinate.objective A b p =
      AuditAllocationCoordinate.objective A b (clip floor 1 (Real.sqrt (A / b)))) :
    p = clip floor 1 (Real.sqrt (A / b)) := by
  let s := Real.sqrt (A / b)
  let r := clip floor 1 s
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : b * s ^ 2 = A := by
    dsimp [s]
    rw [Real.sq_sqrt (div_nonneg hA hb.le)]
    exact mul_div_cancel₀ A hb.ne'
  have hr : 0 < r := hf.trans_le (clip_mem floor 1 s (hp.1.trans hp.2)).1
  have hpp : 0 < p := hf.trans_le hp.1
  have hn : 0 ≤ (p - r) * (r - s) := by
    have hh := clip_normal floor 1 s p hp
    change (p - r) * (s - r) ≤ 0 at hh
    nlinarith
  have hsecond : 0 ≤ b * (r + s) * ((p - r) * (r - s)) :=
    mul_nonneg (mul_nonneg hb.le (add_nonneg hr.le hs)) hn
  have hd := AuditAllocationCoordinate.objective_difference A b p r hpp.ne' hr.ne'
  have hz : AuditAllocationCoordinate.objective A b p -
      AuditAllocationCoordinate.objective A b r = 0 := sub_eq_zero.mpr heq
  rw [hz, mul_zero, ← hsq] at hd
  have hexpand : (p - r) * (b * p * r - b * s ^ 2) =
      b * r * (p - r) ^ 2 + b * (r + s) * ((p - r) * (r - s)) := by ring
  rw [hexpand] at hd
  have hbr : 0 < b * r := mul_pos hb hr
  have hzero : (p - r) ^ 2 = 0 := by nlinarith [sq_nonneg (p - r)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- Zero primal-dual gap forces equality at every separate coordinate minimum. -/
theorem coordinate_optimality (a : J → ι → ℝ) (floor c p : ι → ℝ)
    (B : ℝ) (η : J → ℝ) (lam : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) (hlam : 0 ≤ lam)
    (hp : Feasible floor c B p) (hdual : dualBound a floor c B η lam = worstVariance a p)
    (i : ι) :
    AuditAllocationCoordinate.objective (contribution a η i) (lam * c i) (p i) =
      AuditAllocationCoordinate.objective (contribution a η i) (lam * c i)
        (AuditAllocationCoordinate.choice (contribution a η i) (lam * c i) (floor i)) := by
  classical
  let f (i : ι) := AuditAllocationCoordinate.objective (contribution a η i) (lam * c i)
  let q (i : ι) := AuditAllocationCoordinate.choice (contribution a η i) (lam * c i) (floor i)
  have hg (i : ι) : 0 ≤ f i (p i) - f i (q i) := sub_nonneg.mpr
    (AuditAllocationCoordinate.choice_minimum _ _ _ _
      (contribution_nonneg a η ha hη i) (mul_nonneg hlam (hc i)) (hf i) (hp.1 i))
  have hb : lam * (spending c p - B) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr hp.2)
  have hw := weighted_le_worst a η p hη hsum
  have he := lagrangian_identity a η c p lam B
  change -lam * B + ∑ i, f i (p i) = _ at he
  change -lam * B + ∑ i, f i (q i) = worstVariance a p at hdual
  have hz : (∑ i, (f i (p i) - f i (q i))) = 0 := by
    apply le_antisymm
    · rw [Finset.sum_sub_distrib]
      linarith
    · exact Finset.sum_nonneg (fun i _ ↦ hg i)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hg i)).mp hz i (Finset.mem_univ i)
  exact sub_eq_zero.mp hi

/-- Every zero-gap primal allocation obeys the square-root rule at a positive multiplier. -/
theorem allocation_formula (a : J → ι → ℝ) (floor c p : ι → ℝ)
    (B : ℝ) (η : J → ℝ) (lam : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 < c i)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) (hlam : 0 < lam)
    (hp : Feasible floor c B p) (hdual : dualBound a floor c B η lam = worstVariance a p)
    (i : ι) : p i = clip (floor i) 1 (Real.sqrt (contribution a η i / (lam * c i))) := by
  have he := coordinate_optimality a floor c p B η lam ha hf (fun i ↦ (hc i).le)
    hη hsum hlam.le hp hdual i
  have hb : 0 < lam * c i := mul_pos hlam (hc i)
  rw [AuditAllocationCoordinate.choice, if_neg hb.ne'] at he
  exact positive_multiplier_unique _ _ _ _ (contribution_nonneg a η ha hη i) hb
    (hf i) (hp.1 i) he

/-- Strict feasibility constructs exact primal-dual optimizers obeying the allocation law. -/
theorem attained_allocation_law (a : J → ι → ℝ) (floor c p₀ : ι → ℝ) (B : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 < c i)
    (hp₀ : ∀ i, p₀ i ∈ Set.Icc (floor i) 1) (hbudget : spending c p₀ < B) :
    ∃ (p : ι → ℝ) (η : J → ℝ) (lam : ℝ),
      Feasible floor c B p ∧ IsMinOn (worstVariance a) {q | Feasible floor c B q} p ∧
      (∀ j, 0 ≤ η j) ∧ (∑ j, η j) = 1 ∧ 0 ≤ lam ∧
      dualBound a floor c B η lam = worstVariance a p ∧
      lam * (spending c p - B) = 0 ∧
      (∀ j, η j ≠ 0 → rowVariance a p j = worstVariance a p) ∧
      (0 < lam → ∀ i, p i =
        clip (floor i) 1 (Real.sqrt (contribution a η i / (lam * c i)))) := by
  obtain ⟨p, η, lam, hp, hmin, hη, hsum, hlam, hdual, hcomp, hactive⟩ :=
    FiniteAuditStrongDuality.attained_strong_duality a floor c p₀ B ha hf
      (fun i ↦ (hc i).le) hp₀ hbudget
  refine ⟨p, η, lam, hp, hmin, hη, hsum, hlam, hdual, hcomp, hactive, ?_⟩
  intro hpos i
  exact allocation_formula a floor c p B η lam ha hf hc hη hsum hpos hp hdual i

end Descent.Portability.FiniteAuditAllocationLaw
