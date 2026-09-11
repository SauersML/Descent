/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Cube
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

assert_below Descent.Decision Descent.Program

/-!
# The complete homolog-exchange phase spectrum

Binary signs encode one homologue; complementing every sign exchanges the
homologues. Completeness below is proved for every response on the finite cube,
then restricted to invariant responses. No low interaction degree is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def phaseCharacter (S : Finset I) (x : I → Bool) : ℝ :=
  ∏ i ∈ S, (2 * allele (x i) - 1)

def homologSwap (x : I → Bool) : I → Bool := fun i => !(x i)

@[simp] lemma homologSwap_involutive (x : I → Bool) : homologSwap (homologSwap x) = x := by
  funext i; simp [homologSwap]

lemma phaseCharacter_univ (S : Finset I) (x : I → Bool) :
    phaseCharacter S x = ∏ i, if i ∈ S then 2 * allele (x i) - 1 else 1 := by
  simp [phaseCharacter, Finset.prod_ite_mem]

theorem phaseCharacter_swap (S : Finset I) (x : I → Bool) :
    phaseCharacter S (homologSwap x) = (-1 : ℝ) ^ S.card * phaseCharacter S x := by
  have h (i : I) : 2 * allele (homologSwap x i) - 1 = -(2 * allele (x i) - 1) := by
    cases hi : x i <;> simp [homologSwap, allele, hi]
  simp only [phaseCharacter, h, Finset.prod_neg_distrib]

theorem phase_orthogonality (S T : Finset I) :
    cubeMean (fun _ : I => 1 / 2) (fun x => phaseCharacter S x * phaseCharacter T x) =
      if S = T then 1 else 0 := by
  simp_rw [phaseCharacter_univ, ← Finset.prod_mul_distrib]
  rw [cubeMean_product (fun _ => 1 / 2) (fun i b =>
    (if i ∈ S then 2 * allele b - 1 else 1) *
    (if i ∈ T then 2 * allele b - 1 else 1))]
  have hf (i : I) :
      (1 - (1 : ℝ) / 2) * ((if i ∈ S then 2 * allele false - 1 else 1) *
        (if i ∈ T then 2 * allele false - 1 else 1)) +
      (1 : ℝ) / 2 * ((if i ∈ S then 2 * allele true - 1 else 1) *
        (if i ∈ T then 2 * allele true - 1 else 1)) =
      if (i ∈ S ↔ i ∈ T) then 1 else 0 := by
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> norm_num [hS, hT, allele]
  simp_rw [hf]
  by_cases h : S = T
  · subst T; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra he
      exact h (Finset.ext fun i => not_not.mp (not_exists.mp he i))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Evaluation of a complete phase-character coefficient vector. -/
noncomputable def phaseExpansion : (Finset I → ℝ) →ₗ[ℝ] ((I → Bool) → ℝ) where
  toFun a x := ∑ S, a S * phaseCharacter S x
  map_add' a b := by funext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by funext x; simp [Finset.mul_sum, mul_assoc]

theorem phase_coefficient (a : Finset I → ℝ) (S : Finset I) :
    cubeMean (fun _ : I => 1 / 2) (fun x => phaseCharacter S x * phaseExpansion a x) = a S := by
  simp only [phaseExpansion, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  rw [cubeMean_sum]
  simp_rw [show ∀ T x, phaseCharacter S x * (a T * phaseCharacter T x) =
    a T * (phaseCharacter S x * phaseCharacter T x) by intros; ring]
  simp_rw [cubeMean_smul, phase_orthogonality]
  simp

theorem phaseExpansion_injective : Function.Injective (phaseExpansion (I := I)) := by
  intro a b h
  funext S
  have := congrArg (fun f => cubeMean (fun _ : I => 1 / 2)
    (fun x => phaseCharacter S x * f x)) h
  simpa only [phase_coefficient] using this

/-- Every function on the cube has a unique full character expansion. -/
theorem phase_expansion_exists_unique (F : (I → Bool) → ℝ) :
    ∃! a : Finset I → ℝ, phaseExpansion a = F := by
  have hd : Module.finrank ℝ (Finset I → ℝ) = Module.finrank ℝ ((I → Bool) → ℝ) := by
    simp [Module.finrank_pi, Fintype.card_finset, Fintype.card_fun]
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := phaseExpansion)).mp phaseExpansion_injective
  obtain ⟨a, ha⟩ := hs F
  exact ⟨a, ha, fun b hb => phaseExpansion_injective (hb.trans ha.symm)⟩

/-- Theorem 4: invariant responses have exactly zero odd-order coefficients. -/
theorem invariant_phase_expansion (F : (I → Bool) → ℝ)
    (hF : ∀ x, F (homologSwap x) = F x) :
    ∃! a : Finset I → ℝ, phaseExpansion a = F ∧ ∀ S, Odd S.card → a S = 0 := by
  obtain ⟨a, ha, hu⟩ := phase_expansion_exists_unique F
  have hswap : phaseExpansion (fun S => (-1 : ℝ) ^ S.card * a S) = F := by
    funext x
    calc
      _ = phaseExpansion a (homologSwap x) := by
        simp only [phaseExpansion, LinearMap.coe_mk, AddHom.coe_mk, phaseCharacter_swap]
        apply Finset.sum_congr rfl; intros; ring
      _ = F x := by rw [ha, hF]
  have hcoeff := phaseExpansion_injective (hswap.trans ha.symm)
  refine ⟨a, ⟨ha, ?_⟩, fun b hb => hu b hb.1⟩
  intro S hS
  have he := congrFun hcoeff S
  rw [hS.neg_one_pow] at he
  linarith

/-- Uniform phase Parseval, before removing the constant coefficient. -/
theorem phase_parseval (a : Finset I → ℝ) :
    cubeMean (fun _ : I => 1 / 2) (fun x => phaseExpansion a x ^ 2) = ∑ S, a S ^ 2 := by
  simp only [phaseExpansion, LinearMap.coe_mk, AddHom.coe_mk, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  rw [cubeMean_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [cubeMean_sum]
  simp_rw [show ∀ T x, a S * phaseCharacter S x * (a T * phaseCharacter T x) =
    (a S * a T) * (phaseCharacter S x * phaseCharacter T x) by intros; ring]
  simp_rw [cubeMean_smul, phase_orthogonality]
  simp

end Descent.Portability.ArchaicPrediction
