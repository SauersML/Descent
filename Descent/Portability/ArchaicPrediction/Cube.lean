/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Transport

assert_below Descent.Decision Descent.Program

/-!
# Finite independent-allele probability model

The expectations here are actual sums over all binary sequences. Their
factorization is proved, not postulated as an orthogonality assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def allele (b : Bool) : ℝ := if b then 1 else 0

noncomputable def cubeWeight (p : I → ℝ) (x : I → Bool) : ℝ :=
  ∏ i, if x i then p i else 1 - p i

noncomputable def cubeMean (p : I → ℝ) (f : (I → Bool) → ℝ) : ℝ :=
  ∑ x, cubeWeight p x * f x

theorem cubeWeight_nonneg (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (x : I → Bool) : 0 ≤ cubeWeight p x := by
  apply Finset.prod_nonneg
  intro i _
  split <;> linarith [(hp i).1, (hp i).2]

/-- Independence as a factorization of finite sums over all binary states. -/
theorem cubeMean_product (p : I → ℝ) (f : I → Bool → ℝ) :
    cubeMean p (fun x => ∏ i, f i (x i)) =
      ∏ i, ((1 - p i) * f i false + p i * f i true) := by
  simp only [cubeMean, cubeWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if b then p i else 1 - p i) * f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fintype.sum_bool, add_comm]

@[simp] theorem cubeMean_one (p : I → ℝ) : cubeMean p (fun _ => 1) = 1 := by
  simpa using cubeMean_product p (fun _ _ => 1)

@[simp] theorem cubeWeight_sum (p : I → ℝ) : ∑ x, cubeWeight p x = 1 := by
  simpa [cubeMean] using cubeMean_one p

lemma cubeMean_add (p : I → ℝ) (f g : (I → Bool) → ℝ) :
    cubeMean p (fun x => f x + g x) = cubeMean p f + cubeMean p g := by
  simp [cubeMean, mul_add, Finset.sum_add_distrib]

lemma cubeMean_smul (p : I → ℝ) (c : ℝ) (f : (I → Bool) → ℝ) :
    cubeMean p (fun x => c * f x) = c * cubeMean p f := by
  simp [cubeMean, Finset.mul_sum, mul_left_comm]

lemma cubeMean_sum {J : Type*} [Fintype J] (p : I → ℝ) (f : J → (I → Bool) → ℝ) :
    cubeMean p (fun x => ∑ j, f j x) = ∑ j, cubeMean p (f j) := by
  simp only [cubeMean, Finset.mul_sum]
  exact Finset.sum_comm

/-- Centered squarefree basis, including the constant for the empty subset. -/
noncomputable def centeredCharacter (p : I → ℝ) (S : Finset I) (x : I → Bool) : ℝ :=
  ∏ i ∈ S, (allele (x i) - p i)

lemma centeredCharacter_univ (p : I → ℝ) (S : Finset I) (x : I → Bool) :
    centeredCharacter p S x = ∏ i, if i ∈ S then allele (x i) - p i else 1 := by
  simp [centeredCharacter, Finset.prod_ite_mem]

/-- Orthogonality and squared norms for the product Bernoulli distribution. -/
theorem centered_orthogonality (p : I → ℝ) (S T : Finset I) :
    cubeMean p (fun x => centeredCharacter p S x * centeredCharacter p T x) =
      if S = T then ∏ i ∈ S, p i * (1 - p i) else 0 := by
  simp_rw [centeredCharacter_univ, ← Finset.prod_mul_distrib]
  rw [cubeMean_product p (fun i b =>
    (if i ∈ S then allele b - p i else 1) * (if i ∈ T then allele b - p i else 1))]
  have hf (i : I) :
      (1 - p i) * ((if i ∈ S then allele false - p i else 1) *
        (if i ∈ T then allele false - p i else 1)) +
      p i * ((if i ∈ S then allele true - p i else 1) *
        (if i ∈ T then allele true - p i else 1)) =
      if i ∈ S then (if i ∈ T then p i * (1 - p i) else 0)
      else (if i ∈ T then 0 else 1) := by
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, allele] <;> ring
  simp_rw [hf]
  by_cases h : S = T
  · subst T
    simp +contextual [Finset.prod_ite_mem]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra he
      apply h
      ext i
      exact not_not.mp (not_exists.mp he i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-- Parseval for the independent-allele centered basis. -/
theorem centered_parseval (p : I → ℝ) (a : Finset I → ℝ) :
    cubeMean p (fun x => (∑ S, a S * centeredCharacter p S x) ^ 2) =
      ∑ S, a S ^ 2 * ∏ i ∈ S, p i * (1 - p i) := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [cubeMean_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [cubeMean_sum]
  simp_rw [show ∀ T x, a S * centeredCharacter p S x * (a T * centeredCharacter p T x) =
      (a S * a T) * (centeredCharacter p S x * centeredCharacter p T x) by intros; ring]
  simp_rw [cubeMean_smul, centered_orthogonality]
  simp [mul_ite, pow_two]

end Descent.Portability.ArchaicPrediction
