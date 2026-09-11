/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditRangeCaps

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16: numerical optimization error is
priced in the final statistical radius. A feasible primal allocation and
valid explicit dual multipliers bound the true optimum on both sides.
Their gap yields a proved additive radius certificate, so an inner optimizer
need not be treated as exact merely because it reports success.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditDesignNumericalCertificate

open FiniteAuditDesign BernsteinTailBound AuditRangeCaps

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- The independently certified difference between a primal value and a dual lower bound. -/
noncomputable def dualGap (a : J → ι → ℝ) (floor c p : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (lam : ℝ) : ℝ := worstVariance a p - dualBound a floor c B η lam

/-- Every valid positive-probability variance objective is nonnegative. -/
theorem worst_nonneg (a : J → ι → ℝ) (p : ι → ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hp : ∀ i, 0 < p i) : 0 ≤ worstVariance a p := by
  obtain ⟨j⟩ := ‹Nonempty J›
  exact (Finset.sum_nonneg (fun i _ ↦ div_nonneg (ha j i) (hp i).le)).trans (row_le_worst a p j)

/-- The radius perturbation is at most the square root of twice exponent times variance error. -/
theorem radius_error (M v v' x e : ℝ) (hv : 0 ≤ v) (hx : 0 ≤ x) (he : 0 ≤ e)
    (happrox : v' ≤ v + e) :
    radius M v' x ≤ radius M v x + Real.sqrt (2 * e * x) := by
  have hmono : Real.sqrt (2 * v' * x) ≤ Real.sqrt (2 * (v + e) * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have ha := Real.sq_sqrt (by positivity : 0 ≤ 2 * v * x)
  have hb := Real.sq_sqrt (by positivity : 0 ≤ 2 * e * x)
  have hc := Real.sq_sqrt (by positivity : 0 ≤ 2 * (v + e) * x)
  have hs : Real.sqrt (2 * (v + e) * x) ≤
      Real.sqrt (2 * v * x) + Real.sqrt (2 * e * x) := by
    nlinarith [Real.sqrt_nonneg (2 * v * x), Real.sqrt_nonneg (2 * e * x),
      Real.sqrt_nonneg (2 * (v + e) * x),
      mul_nonneg (Real.sqrt_nonneg (2 * v * x)) (Real.sqrt_nonneg (2 * e * x))]
  unfold radius
  linarith

/-- The dual certificate bounds variance error against every feasible competitor. -/
theorem certified_variance_error (a : J → ι → ℝ) (floor c p : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (lam : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) (hlam : 0 ≤ lam)
    (hp : Feasible floor c B p) :
    0 ≤ dualGap a floor c p B η lam ∧ ∀ q, Feasible floor c B q →
      worstVariance a p ≤ worstVariance a q + dualGap a floor c p B η lam := by
  constructor
  · exact sub_nonneg.mpr (weak_duality a floor c B η lam p ha hf hc hη hsum hlam hp)
  · intro q hq
    have hh := weak_duality a floor c B η lam q ha hf hc hη hsum hlam hq
    unfold dualGap
    linarith

/-- A checked primal-dual gap bounds confidence-radius error at every fixed range cap. -/
theorem certified_radius_error (a : J → ι → ℝ) (floor c p : ι → ℝ) (B : ℝ)
    (η : J → ℝ) (lam M x : ℝ)
    (ha : ∀ j i, 0 ≤ a j i) (hf : ∀ i, 0 < floor i) (hc : ∀ i, 0 ≤ c i)
    (hη : ∀ j, 0 ≤ η j) (hsum : ∑ j, η j = 1) (hlam : 0 ≤ lam) (hx : 0 ≤ x)
    (hp : Feasible floor c B p) (q : ι → ℝ) (hq : Feasible floor c B q) :
    radius M (worstVariance a p) x ≤ radius M (worstVariance a q) x +
      Real.sqrt (2 * dualGap a floor c p B η lam * x) := by
  have hh := certified_variance_error a floor c p B η lam ha hf hc hη hsum hlam hp
  exact radius_error M (worstVariance a q) (worstVariance a p) x _
    (worst_nonneg a q ha (fun i ↦ (hf i).trans_le (hq.1 i).1)) hx hh.1 (hh.2 q hq)

end Descent.Portability.AuditDesignNumericalCertificate
