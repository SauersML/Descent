/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
# Transport of the complete interaction response

Theorem 1 of *Beyond Ancestry Tags*. Coefficients are indexed by subsets,
not by additive regression slopes. The polynomial translation and its inverse
hold without a distributional assumption. Their interpretation as regression
coefficients requires a separate projection theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
open MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The squarefree exponent belonging to a subset of loci. -/
noncomputable def subsetExponent (S : Finset I) : I →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

@[simp] lemma subsetExponent_apply (S : Finset I) (i : I) :
    subsetExponent S i = if i ∈ S then 1 else 0 := by
  classical
  simp [subsetExponent, Finsupp.finset_sum_apply, Finsupp.single_apply]

lemma subsetExponent_injective : Function.Injective (subsetExponent (I := I)) := by
  intro S T h
  ext i
  have hi := congrArg (fun e : I →₀ ℕ => e i) h
  simp only [subsetExponent_apply] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-- The full multilinear polynomial, in coordinates relative to its center. -/
noncomputable def responsePolynomial (a : Finset I → ℝ) : MvPolynomial I ℝ :=
  ∑ S, C (a S) * ∏ i ∈ S, X i

lemma squarefree_monomial (S : Finset I) :
    (∏ i ∈ S, X i : MvPolynomial I ℝ) = monomial (subsetExponent S) 1 := by
  simpa [subsetExponent, X] using
    (monomial_sum_one (R := ℝ) S (fun i => Finsupp.single i 1)).symm

@[simp] lemma coefficient_response (a : Finset I → ℝ) (S : Finset I) :
    coeff (subsetExponent S) (responsePolynomial a) = a S := by
  simp only [responsePolynomial, coeff_sum, coeff_C_mul, squarefree_monomial,
    coeff_monomial]
  simp [subsetExponent_injective.eq_iff]

lemma responsePolynomial_injective :
    Function.Injective (responsePolynomial (I := I)) := by
  intro a b h
  funext S
  simpa using congrArg (coeff (subsetExponent S)) h

/-- Substitution by `X + δ` on the entire polynomial algebra. -/
noncomputable def shiftPolynomial (δ : I → ℝ) : MvPolynomial I ℝ →+* MvPolynomial I ℝ :=
  eval₂Hom C (fun i => X i + C (δ i))

@[simp] lemma shiftPolynomial_C (δ : I → ℝ) (r : ℝ) :
    shiftPolynomial δ (C r) = C r := by simp [shiftPolynomial]

@[simp] lemma shiftPolynomial_X (δ : I → ℝ) (i : I) :
    shiftPolynomial δ (X i) = X i + C (δ i) := by simp [shiftPolynomial]

theorem shiftPolynomial_comp (δ ε : I → ℝ) :
    (shiftPolynomial ε).comp (shiftPolynomial δ) = shiftPolynomial (δ + ε) := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp
  · intro i; simp [Pi.add_apply, map_add]; ring

@[simp] theorem shiftPolynomial_zero : shiftPolynomial (0 : I → ℝ) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro i <;> simp

/-- The explicit all-order interaction transport formula. -/
noncomputable def transport (p q : I → ℝ) (a : Finset I → ℝ) (S : Finset I) : ℝ :=
  ∑ T, if S ⊆ T then a T * ∏ j ∈ T \ S, (q j - p j) else 0

lemma shift_product (δ : I → ℝ) (T : Finset I) :
    shiftPolynomial δ (∏ i ∈ T, X i) =
      ∑ S : Finset I, if S ⊆ T then
        C (∏ j ∈ T \ S, δ j) * ∏ i ∈ S, X i else 0 := by
  rw [map_prod]
  simp only [shiftPolynomial_X]
  rw [Finset.prod_add]
  have hp : T.powerset = Finset.univ.filter (fun S => S ⊆ T) := by ext; simp
  rw [hp, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp [map_prod, mul_comm]

/-- Translating the explicit coefficients really translates the response polynomial. -/
theorem response_transport (p q : I → ℝ) (a : Finset I → ℝ) :
    responsePolynomial (transport p q a) = shiftPolynomial (q - p) (responsePolynomial a) := by
  classical
  simp only [responsePolynomial, map_sum, map_mul, shiftPolynomial_C, shift_product,
    transport, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp [map_mul, Pi.sub_apply, mul_assoc]

/-- Direct recentering agrees with any intermediate recentering. -/
theorem transport_comp (p q r : I → ℝ) (a : Finset I → ℝ) :
    transport q r (transport p q a) = transport p r a := by
  apply responsePolynomial_injective
  rw [response_transport, response_transport, response_transport]
  change ((shiftPolynomial (r - q)).comp (shiftPolynomial (q - p))) _ = _
  rw [shiftPolynomial_comp]
  congr 2
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

@[simp] theorem transport_self (p : I → ℝ) (a : Finset I → ℝ) : transport p p a = a := by
  apply responsePolynomial_injective
  rw [response_transport, sub_self, shiftPolynomial_zero, RingHom.id_apply]

theorem transport_inverse (p q : I → ℝ) (a : Finset I → ℝ) :
    transport q p (transport p q a) = a := by rw [transport_comp, transport_self]

/-- Pointwise response invariance, for all real sequence coordinates. -/
theorem evaluate_transport (p q x : I → ℝ) (a : Finset I → ℝ) :
    eval (x - q) (responsePolynomial (transport p q a)) =
      eval (x - p) (responsePolynomial a) := by
  rw [response_transport]
  have h : (eval (x - q)).comp (shiftPolynomial (q - p)) = eval (x - p) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i; simp [Pi.sub_apply]
  exact RingHom.congr_fun h _

end Descent.Portability.ArchaicPrediction
