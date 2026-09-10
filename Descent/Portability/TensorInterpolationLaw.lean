/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CrossCoordinateRigidityLaw
import Descent.Portability.DiploidBernsteinLaw
import Mathlib.Data.Fin.Tuple.Basic

assert_below Descent.Decision Descent.Program

/-!
Exact tensor interpolation on arbitrary rectangular coordinate domains. The
finite tensor representation is derived from one-coordinate interpolation,
then specialized to the explicit three-point quadratic Lagrange basis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TensorInterpolationLaw

/-- Successive coordinate interpolation gives one exact tensor formula. -/
theorem tensor_interpolation (n : ℕ) (S : Fin n → Set ℝ)
    (node : Fin n → Fin 3 → ℝ) (hnode : ∀ i k, node i k ∈ S i)
    (weight : Fin n → ℝ → Fin 3 → ℝ) (F : (Fin n → ℝ) → ℝ)
    (hcoord : ∀ p, (∀ i, p i ∈ S i) → ∀ i,
      F p = ∑ k : Fin 3, weight i (p i) k * F (Function.update p i (node i k)))
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ S i) :
    F p = ∑ g : Fin n → Fin 3, (∏ i, weight i (p i) (g i)) * F (fun i ↦ node i (g i)) := by
  induction n with
  | zero =>
    have hg : ∀ g : Fin 0 → Fin 3, (fun i ↦ node i (g i)) = p :=
      fun _ ↦ Subsingleton.elim _ _
    simp_rw [hg]
    simp
  | succ n ih =>
    have hsub (k : Fin 3) : F (Fin.cons (node 0 k) (Fin.tail p)) =
        ∑ g : Fin n → Fin 3, (∏ i, weight i.succ (p i.succ) (g i)) *
          F (Fin.cons (node 0 k) (fun i ↦ node i.succ (g i))) := by
      apply ih (fun i ↦ S i.succ) (fun i ↦ node i.succ) (fun i l ↦ hnode i.succ l)
        (fun i ↦ weight i.succ) (fun q ↦ F (Fin.cons (node 0 k) q))
      · intro q hq i
        have hfull : ∀ j : Fin (n + 1), (Fin.cons (node 0 k) q : Fin (n + 1) → ℝ) j ∈ S j := by
          intro j
          cases j using Fin.cases with
          | zero => simpa using hnode 0 k
          | succ j => simpa using hq j
        simpa only [Fin.cons_succ, Fin.cons_update] using
          hcoord (Fin.cons (node 0 k) q) hfull i.succ
      · exact fun i ↦ hp i.succ
    have hhead : F p = ∑ k : Fin 3, weight 0 (p 0) k *
        F (Fin.cons (node 0 k) (Fin.tail p)) := by
      have h := hcoord p hp 0
      have hu (k : Fin 3) : Function.update p 0 (node 0 k) =
          Fin.cons (node 0 k) (Fin.tail p) := by
        simpa only [Fin.cons_self_tail] using
          (Fin.update_cons_zero (x := p 0) (p := Fin.tail p) (z := node 0 k))
      simpa only [hu] using h
    rw [hhead]
    simp_rw [hsub, Finset.mul_sum]
    rw [← Fintype.sum_prod_type (fun kg : Fin 3 × (Fin n → Fin 3) ↦
      weight 0 (p 0) kg.1 * ((∏ i, weight i.succ (p i.succ) (kg.2 i)) *
        F (Fin.cons (node 0 kg.1) (fun i ↦ node i.succ (kg.2 i)))))]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin 3))
    rintro ⟨k, g⟩
    have hg : (fun i : Fin (n + 1) ↦ node i ((Fin.cons k g : Fin (n + 1) → Fin 3) i)) =
        Fin.cons (node 0 k) (fun i ↦ node i.succ (g i)) := by
      funext i
      cases i using Fin.cases <;> simp
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [hg]
    ring

/-- The explicit Lagrange basis for three distinct real nodes. -/
noncomputable def lagrange (q : Fin 3 → ℝ) (x : ℝ) (k : Fin 3) : ℝ :=
  if k.val = 0 then (x - q 1) * (x - q 2) / ((q 0 - q 1) * (q 0 - q 2))
  else if k.val = 1 then (x - q 0) * (x - q 2) / ((q 1 - q 0) * (q 1 - q 2))
  else (x - q 0) * (x - q 1) / ((q 2 - q 0) * (q 2 - q 1))

/-- Every scalar quadratic is exactly reproduced by its three sampled values. -/
theorem lagrange_quadratic (q : Fin 3 → ℝ) (hq : Function.Injective q)
    (A B C x : ℝ) :
    A + B * x + C * x ^ 2 =
      ∑ k : Fin 3, lagrange q x k * (A + B * q k + C * (q k) ^ 2) := by
  have h01 : q 0 - q 1 ≠ 0 := sub_ne_zero.mpr (hq.ne (by decide))
  have h02 : q 0 - q 2 ≠ 0 := sub_ne_zero.mpr (hq.ne (by decide))
  have h12 : q 1 - q 2 ≠ 0 := sub_ne_zero.mpr (hq.ne (by decide))
  have h10 : q 1 - q 0 ≠ 0 := sub_ne_zero.mpr (hq.ne (by decide))
  have h20 : q 2 - q 0 ≠ 0 := sub_ne_zero.mpr (hq.ne (by decide))
  have h21 : q 2 - q 1 ≠ 0 := sub_ne_zero.mpr (hq.ne (by decide))
  norm_num [Fin.sum_univ_succ, lagrange]
  field_simp
  ring

/-- Separate quadraticity on a box determines the complete function from 3^n node values. -/
theorem separately_quadratic_tensor (n : ℕ) (S : Fin n → Set ℝ)
    (node : Fin n → Fin 3 → ℝ) (hnode : ∀ i k, node i k ∈ S i)
    (hinj : ∀ i, Function.Injective (node i)) (F : (Fin n → ℝ) → ℝ)
    (hquad : ∀ p, (∀ i, p i ∈ S i) → ∀ i, ∃ A B C : ℝ,
      ∀ t ∈ S i, F (Function.update p i t) = A + B * t + C * t ^ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ S i) :
    F p = ∑ g : Fin n → Fin 3, (∏ i, lagrange (node i) (p i) (g i)) *
      F (fun i ↦ node i (g i)) := by
  apply tensor_interpolation n S node hnode (fun i ↦ lagrange (node i)) F _ p hp
  intro q hq i
  obtain ⟨A, B, C, hpoly⟩ := hquad q hq i
  have hqval : F q = A + B * q i + C * q i ^ 2 := by
    simpa only [Function.update_eq_self] using hpoly (q i) (hq i)
  rw [hqval, lagrange_quadratic (node i) (hinj i) A B C (q i)]
  apply Finset.sum_congr rfl
  intro k _
  rw [hpoly (node i k) (hnode i k)]

/-- Power coefficients of the explicit three-node Lagrange basis. -/
noncomputable def lagrangeCoefficient (q : Fin 3 → ℝ) (k degree : Fin 3) : ℝ :=
  let a : Fin 3 := if k.val = 0 then 1 else 0
  let b : Fin 3 := if k.val = 2 then 1 else 2
  let den := (q k - q a) * (q k - q b)
  if degree.val = 0 then q a * q b / den
  else if degree.val = 1 then -(q a + q b) / den else 1 / den

theorem lagrange_power_expansion (q : Fin 3 → ℝ) (x : ℝ) (k : Fin 3) :
    lagrange q x k = ∑ degree : Fin 3, lagrangeCoefficient q k degree * x ^ degree.val := by
  fin_cases k <;> norm_num [lagrange, lagrangeCoefficient, Fin.sum_univ_succ] <;>
    simp only [div_eq_mul_inv, mul_inv_rev] <;> ring_nf
  rfl

/-- Explicit global monomial coefficients computed solely from the in-box node values. -/
noncomputable def interpolatedCoefficients {D : Type*} [Fintype D] [DecidableEq D]
    (node : D → Fin 3 → ℝ) (values : (D → Fin 3) → ℝ) (degree : D → Fin 3) : ℝ :=
  ∑ g, values g * ∏ i, lagrangeCoefficient (node i) (g i) (degree i)

/-- The local-node tensor interpolant is a global tensor quadratic with explicit coefficients. -/
theorem tensor_lagrange_polynomial {D : Type*} [Fintype D] [DecidableEq D]
    (node : D → Fin 3 → ℝ) (values : (D → Fin 3) → ℝ) (p : D → ℝ) :
    (∑ g : D → Fin 3, (∏ i, lagrange (node i) (p i) (g i)) * values g) =
      DiploidBernsteinLaw.tensorQuadratic (interpolatedCoefficients node values) p := by
  simp_rw [lagrange_power_expansion, Fintype.prod_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold DiploidBernsteinLaw.tensorQuadratic interpolatedCoefficients
  apply Finset.sum_congr rfl
  intro degree _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_mul_distrib]
  ring

/-- Separate quadraticity on an open box yields one globally defined polynomial extension.
The coefficients use interior nodes; no access to the boundary points 0, 1/2, or 1 is assumed. -/
theorem separately_quadratic_polynomial (n : ℕ) (S : Fin n → Set ℝ)
    (node : Fin n → Fin 3 → ℝ) (hnode : ∀ i k, node i k ∈ S i)
    (hinj : ∀ i, Function.Injective (node i)) (F : (Fin n → ℝ) → ℝ)
    (hquad : ∀ p, (∀ i, p i ∈ S i) → ∀ i, ∃ A B C : ℝ,
      ∀ t ∈ S i, F (Function.update p i t) = A + B * t + C * t ^ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ S i) :
    F p = DiploidBernsteinLaw.tensorQuadratic
      (interpolatedCoefficients node (fun g ↦ F (fun i ↦ node i (g i)))) p := by
  rw [separately_quadratic_tensor n S node hnode hinj F hquad p hp,
    tensor_lagrange_polynomial]

/-- A separately quadratic mean surface specified only on a box has a fixed diploid realization. -/
theorem separately_quadratic_diploid_realization (n : ℕ) (S : Fin n → Set ℝ)
    (node : Fin n → Fin 3 → ℝ) (hnode : ∀ i k, node i k ∈ S i)
    (hinj : ∀ i, Function.Injective (node i)) (F : (Fin n → ℝ) → ℝ)
    (hquad : ∀ p, (∀ i, p i ∈ S i) → ∀ i, ∃ A B C : ℝ,
      ∀ t ∈ S i, F (Function.update p i t) = A + B * t + C * t ^ 2) :
    ∃ f : (Fin n → Fin 3) → ℝ, ∀ p, (∀ i, p i ∈ S i) →
      F p = DiploidEffectLaw.phenotypeMean f p := by
  refine ⟨DiploidBernsteinLaw.realizingMap (interpolatedCoefficients node
    (fun g ↦ F (fun i ↦ node i (g i)))), ?_⟩
  intro p hp
  rw [DiploidBernsteinLaw.realizingMap_mean]
  exact separately_quadratic_polynomial n S node hnode hinj F hquad p hp

end Descent.Portability.TensorInterpolationLaw
