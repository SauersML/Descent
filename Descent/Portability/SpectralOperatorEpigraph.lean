/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OperatorSlaterMultipliers
import Descent.Portability.FiniteAuditEpigraph
import Descent.Portability.SpectralAuditDesign

assert_below Descent.Decision Descent.Program

/-!
The actual operator epigraph of the spectral audit design. Its quadratic
constraints are derived from reciprocal sampling variances. A positive
correction-space dimension makes the operator inequality equivalent to the
largest-eigenvalue epigraph; a strict budget point gives uniform operator
Slater slack. All hypotheses of the separation theorem are instantiated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralOperatorEpigraph

open FiniteAuditDesign FiniteAuditDesignConvexity FiniteAuditEpigraph
open AuditCovarianceSpectrum SpectralAuditDesign OperatorPositiveCone
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual covariance minus the free epigraph scalar times the identity. -/
noncomputable def operatorResidual (κ : ι → ℝ) (u : ι → E) (x : (ι → ℝ) × ℝ) :
    E →L[ℝ] E :=
  (covariance (fun i ↦ κ i / x.1 i) u).toContinuousLinearMap -
    x.2 • ContinuousLinearMap.id ℝ E

/-- The operator residual is exactly the directional audit variance minus the scalar bound. -/
theorem residual_quadratic (κ : ι → ℝ) (u : ι → E) (x : (ι → ℝ) × ℝ) (v : E) :
    inner ℝ v (operatorResidual κ u x v) =
      (∑ i, κ i / x.1 i * (inner ℝ v (u i)) ^ 2) - x.2 * ‖v‖ ^ 2 := by
  change inner ℝ v (covariance (fun i ↦ κ i / x.1 i) u v - x.2 • v) = _
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, quadratic]

/-- Every directional operator constraint is convex on the positive probability box. -/
theorem residual_convex (κ floor : ι → ℝ) (u : ι → E)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (v : E) :
    ConvexOn ℝ (domain floor) (fun x ↦ inner ℝ v (operatorResidual κ u x v)) := by
  refine ⟨domain_convex floor, ?_⟩
  intro x hx y hy a b ha hb hab
  have hsum : (∑ i, κ i / (a * x.1 i + b * y.1 i) * (inner ℝ v (u i)) ^ 2) ≤
      a * (∑ i, κ i / x.1 i * (inner ℝ v (u i)) ^ 2) +
      b * (∑ i, κ i / y.1 i * (inner ℝ v (u i)) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right
      (reciprocal_jensen (κ i) (x.1 i) (y.1 i) a b (hκ i)
        ((hf i).trans_le (hx i).1) ((hf i).trans_le (hy i).1) ha hb hab)
      (sq_nonneg (inner ℝ v (u i)))
    nlinarith
  simp only [residual_quadratic]
  change (∑ i, κ i / (a * x.1 i + b * y.1 i) * (inner ℝ v (u i)) ^ 2) -
    (a * x.2 + b * y.2) * ‖v‖ ^ 2 ≤
    a * ((∑ i, κ i / x.1 i * (inner ℝ v (u i)) ^ 2) - x.2 * ‖v‖ ^ 2) +
    b * ((∑ i, κ i / y.1 i * (inner ℝ v (u i)) ^ 2) - y.2 * ‖v‖ ^ 2)
  nlinarith

/-- In positive dimension the operator inequality is exactly the spectral epigraph condition. -/
theorem residual_feasible_iff (κ : ι → ℝ) (u : ι → E) (p : ι → ℝ) (t : ℝ)
    (hd : 0 < Module.finrank ℝ E) :
    Nonnegative (-operatorResidual κ u (p, t)) ↔ objective κ u p ≤ t := by
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := largest_attained (fun i ↦ κ i / p i) u hd
    have hh := h v
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, residual_quadratic,
      Prod.fst, Prod.snd, hv, one_pow, mul_one] at hh
    rw [he] at hh
    exact (neg_nonneg.mp hh) |> sub_nonpos.mp
  · intro h v
    have hq := quadratic_le (fun i ↦ κ i / p i) u v
    have ht := mul_le_mul_of_nonneg_right h (sq_nonneg ‖v‖)
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, residual_quadratic,
      Prod.fst, Prod.snd]
    change 0 ≤ -((∑ i, κ i / p i * (inner ℝ v (u i)) ^ 2) - t * ‖v‖ ^ 2)
    change (∑ i, κ i / p i * (inner ℝ v (u i)) ^ 2) ≤ objective κ u p * ‖v‖ ^ 2 at hq
    linarith

/-- Increasing the variance bound by one gives uniform positive operator slack. -/
theorem strict_operator_point (κ : ι → ℝ) (u : ι → E) (p : ι → ℝ) :
    StrictPositive (-operatorResidual κ u (p, objective κ u p + 1)) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro v
  have hh := quadratic_le (fun i ↦ κ i / p i) u v
  simp only [ContinuousLinearMap.neg_apply, inner_neg_right, residual_quadratic,
    Prod.fst, Prod.snd, one_mul]
  change (∑ i, κ i / p i * (inner ℝ v (u i)) ^ 2) ≤ objective κ u p * ‖v‖ ^ 2 at hh
  nlinarith

/-- Actual scalar and operator multipliers exist at the attained spectral audit optimum. -/
theorem epigraph_multipliers (κ floor c p p₀ : ι → ℝ) (u : ι → E) (B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hf : ∀ i, 0 < floor i) (hd : 0 < Module.finrank ℝ E)
    (hp : Feasible floor c B p)
    (hmin : IsMinOn (objective κ u) {q | Feasible floor c B q} p)
    (hp₀ : ∀ i, p₀ i ∈ Set.Icc (floor i) 1) (hbudget : spending c p₀ < B) :
    ∃ (lam : ℝ) (R : (E →L[ℝ] E) →L[ℝ] ℝ), 0 ≤ lam ∧
      (∀ A, Nonnegative A → 0 ≤ R A) ∧
      (∀ x ∈ domain floor, objective κ u p ≤ x.2 +
        lam * (spending c x.1 - B) + R (operatorResidual κ u x)) ∧
      lam * (spending c p - B) = 0 ∧ R (operatorResidual κ u (p, objective κ u p)) = 0 := by
  apply OperatorSlaterMultipliers.exists_multipliers (domain floor)
    (fun x : (ι → ℝ) × ℝ ↦ x.2) (fun x ↦ spending c x.1 - B)
    (operatorResidual κ u) (p, objective κ u p)
    (FiniteAuditEpigraph.objective_convex floor)
    (FiniteAuditEpigraph.constraint_convex (fun _ : Unit ↦ fun _ : ι ↦ (0 : ℝ))
      floor c B (fun _ _ ↦ le_refl 0) hf none) (residual_convex κ floor u hκ hf)
    hp.1 (sub_nonpos.mpr hp.2)
    ((residual_feasible_iff κ u p (objective κ u p) hd).mpr (le_refl _))
  · intro x hx hg hH
    have hfeas : Feasible floor c B x.1 := ⟨hx, sub_nonpos.mp hg⟩
    exact (hmin hfeas).trans ((residual_feasible_iff κ u x.1 x.2 hd).mp hH)
  · exact ⟨(p₀, objective κ u p₀ + 1), hp₀, sub_neg.mpr hbudget,
      strict_operator_point κ u p₀⟩

/-- The operator functional expands into covariance and free-scalar contributions. -/
theorem functional_residual (κ : ι → ℝ) (u : ι → E) (p : ι → ℝ) (t : ℝ)
    (R : (E →L[ℝ] E) →L[ℝ] ℝ) :
    R (operatorResidual κ u (p, t)) =
      R ((covariance (fun i ↦ κ i / p i) u).toContinuousLinearMap) -
        t * R (ContinuousLinearMap.id ℝ E) := by
  simp only [operatorResidual, map_sub, map_smul, smul_eq_mul]

/-- Free epigraph variation forces the positive operator functional to have unit identity value. -/
theorem functional_normalized (κ floor c p : ι → ℝ) (u : ι → E) (B lam : ℝ)
    (R : (E →L[ℝ] E) →L[ℝ] ℝ) (hp : ∀ i, p i ∈ Set.Icc (floor i) 1)
    (hL : ∀ x ∈ domain floor, objective κ u p ≤ x.2 +
      lam * (spending c x.1 - B) + R (operatorResidual κ u x))
    (hb : lam * (spending c p - B) = 0)
    (hR : R (operatorResidual κ u (p, objective κ u p)) = 0) :
    R (ContinuousLinearMap.id ℝ E) = 1 := by
  have hl := hL (p, objective κ u p - 1) hp
  have hr := hL (p, objective κ u p + 1) hp
  simp only [Prod.fst, Prod.snd, hb, add_zero, functional_residual] at hl hr
  rw [functional_residual] at hR
  nlinarith

end Descent.Portability.SpectralOperatorEpigraph
