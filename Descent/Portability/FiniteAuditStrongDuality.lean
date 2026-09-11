/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAuditEpigraph

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 14, finite-library version. Strict
expected-budget feasibility produces an attained primal optimum and actual
attaining dual multipliers. Their weights sum to one because the epigraph
coordinate is unrestricted. The exact coordinate minimum then proves zero
duality gap for the explicit dual objective already used by audit certificates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAuditStrongDuality

open FiniteAuditDesign FiniteAuditDesignConvexity FiniteAuditEpigraph
open scoped BigOperators

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- The finite epigraph constraints expand to their budget and common-variance terms. -/
theorem constraint_sum (a : J → ι → ℝ) (c p : ι → ℝ) (B t : ℝ) (d : Option J → ℝ) :
    (∑ j, d j * constraint a c B j (p, t)) =
      d none * (spending c p - B) +
      (∑ j, d (some j) * rowVariance a p j) - t * ∑ j, d (some j) := by
  rw [Fintype.sum_option]
  simp only [constraint, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

/-- Slater separation supplies multipliers at the actual attained finite-audit primal optimum. -/
theorem epigraph_multipliers (a : J → ι → ℝ) (floor c p p₀ : ι → ℝ) (B : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i)
    (hp : Feasible floor c B p)
    (hmin : IsMinOn (worstVariance a) {q | Feasible floor c B q} p)
    (hp₀ : ∀ i, p₀ i ∈ Set.Icc (floor i) 1) (hbudget : spending c p₀ < B) :
    ∃ d : Option J → ℝ, (∀ j, 0 ≤ d j) ∧
      (∀ q ∈ domain floor, worstVariance a p ≤ q.2 + ∑ j, d j * constraint a c B j q) ∧
      (∀ j, d j * constraint a c B j (p, worstVariance a p) = 0) := by
  apply FiniteSlaterMultipliers.exists_multipliers (domain floor)
    (fun x : (ι → ℝ) × ℝ ↦ x.2) (constraint a c B) (p, worstVariance a p)
    (FiniteAuditEpigraph.objective_convex floor) (constraint_convex a floor c B ha hf)
  · exact hp.1
  · intro j
    cases j with
    | none => exact sub_nonpos.mpr hp.2
    | some j => exact sub_nonpos.mpr (row_le_worst a p j)
  · intro x hx hg
    have hfeas : Feasible floor c B x.1 := ⟨hx, sub_nonpos.mp (hg none)⟩
    have hu : worstVariance a x.1 ≤ x.2 := by
      apply Finset.sup'_le
      intro j _
      exact sub_nonpos.mp (hg (some j))
    exact (hmin hfeas).trans hu
  · exact slater_point a floor c p₀ B hp₀ hbudget

/-- Free epigraph variation forces the contrast multipliers to be genuine simplex weights. -/
theorem multipliers_sum_one (a : J → ι → ℝ) (floor c p : ι → ℝ) (B : ℝ)
    (d : Option J → ℝ) (hp : ∀ i, p i ∈ Set.Icc (floor i) 1)
    (hL : ∀ q ∈ domain floor, worstVariance a p ≤ q.2 + ∑ j, d j * constraint a c B j q)
    (hcomp : ∀ j, d j * constraint a c B j (p, worstVariance a p) = 0) :
    (∑ j, d (some j)) = 1 := by
  have hb : d none * (spending c p - B) = 0 := hcomp none
  have he : (∑ j, d (some j) * rowVariance a p j) =
      worstVariance a p * ∑ j, d (some j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hc : d (some j) * (rowVariance a p j - worstVariance a p) = 0 := hcomp (some j)
    nlinarith
  have hl := hL (p, worstVariance a p - 1) hp
  have hr := hL (p, worstVariance a p + 1) hp
  rw [constraint_sum, hb, zero_add, he] at hl hr
  dsimp only at hl hr
  nlinarith

/-- Strict budget feasibility yields both optimizers and an attained exact dual value. -/
theorem attained_strong_duality (a : J → ι → ℝ) (floor c p₀ : ι → ℝ) (B : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hp₀ : ∀ i, p₀ i ∈ Set.Icc (floor i) 1) (hbudget : spending c p₀ < B) :
    ∃ (p : ι → ℝ) (η : J → ℝ) (lam : ℝ),
      Feasible floor c B p ∧ IsMinOn (worstVariance a) {q | Feasible floor c B q} p ∧
      (∀ j, 0 ≤ η j) ∧ (∑ j, η j) = 1 ∧ 0 ≤ lam ∧
      dualBound a floor c B η lam = worstVariance a p ∧
      lam * (spending c p - B) = 0 ∧
      (∀ j, η j ≠ 0 → rowVariance a p j = worstVariance a p) := by
  classical
  obtain ⟨p, hp, hmin⟩ := FiniteAuditDesignConvexity.optimum_exists a floor c B hf
    ⟨p₀, hp₀, hbudget.le⟩
  obtain ⟨d, hd, hL, hcomp⟩ := epigraph_multipliers a floor c p p₀ B ha hf hp hmin hp₀ hbudget
  let η (j : J) := d (some j)
  let lam := d none
  have hη (j : J) : 0 ≤ η j := hd (some j)
  have hsum : (∑ j, η j) = 1 := multipliers_sum_one a floor c p B d hp.1 hL hcomp
  have hlam : 0 ≤ lam := hd none
  have hdual : dualBound a floor c B η lam = worstVariance a p := by
    apply le_antisymm (weak_duality a floor c B η lam p ha hf hc hη hsum hlam hp)
    let q (i : ι) := AuditAllocationCoordinate.choice (contribution a η i) (lam * c i) (floor i)
    have hq : ∀ i, q i ∈ Set.Icc (floor i) 1 := fun i ↦
      AuditAllocationCoordinate.choice_mem _ _ _ ((hp₀ i).1.trans (hp₀ i).2)
    have hl := hL (q, 0) hq
    rw [constraint_sum] at hl
    simp only [mul_zero, zero_mul, sub_zero, zero_add, Prod.snd] at hl
    have he : dualBound a floor c B η lam =
        (∑ j, η j * rowVariance a q j) + lam * (spending c q - B) :=
      lagrangian_identity a η c q lam B
    rw [he]
    change worstVariance a p ≤ _ at hl
    dsimp only [η, lam]
    linarith
  refine ⟨p, η, lam, hp, hmin, hη, hsum, hlam, hdual, hcomp none, ?_⟩
  intro j hj
  have hh : η j * (rowVariance a p j - worstVariance a p) = 0 := hcomp (some j)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hj)

end Descent.Portability.FiniteAuditStrongDuality
