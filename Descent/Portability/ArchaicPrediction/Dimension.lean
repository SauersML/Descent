/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Factorial
import Descent.Portability.ArchaicPrediction.Phase

assert_below Descent.Decision Descent.Program

/-!
# Sizes of response panels and phase spectra

The polynomial-sized assay panel and the exponential phase space have
different dimensions. These counts are consequences of the specified degree
restriction and homolog-exchange symmetry, respectively.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Theorem 3's exact number of measured degree-limited sequence states. -/
theorem factorial_panel_card (d : ℕ) :
    (Finset.univ.filter (fun S : Finset I => S.card ≤ d)).card =
      ∑ j ∈ Finset.range (d + 1), (Fintype.card I).choose j := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Finset I)) (Finset.range (d + 1)) Finset.card
  have hs (j : ℕ) : Finset.univ.filter (fun S : Finset I => S.card = j) =
      (Finset.univ : Finset I).powersetCard j := by ext; simp
  simp only [hs, Finset.card_powersetCard, Finset.card_univ] at hf
  simpa only [Finset.mem_range, Nat.lt_succ_iff] using hf.symm

def toggleLocus (i : I) (S : Finset I) : Finset I :=
  if i ∈ S then S.erase i else insert i S

lemma toggleLocus_involutive (i : I) (S : Finset I) :
    toggleLocus i (toggleLocus i S) = S := by
  by_cases h : i ∈ S <;> simp [toggleLocus, h]

lemma toggleLocus_parity (i : I) (S : Finset I) :
    Even (toggleLocus i S).card ↔ ¬ Even S.card := by
  by_cases h : i ∈ S
  · have hp : 0 < S.card := Finset.card_pos.mpr ⟨i, h⟩
    simp only [toggleLocus, if_pos h, Finset.card_erase_of_mem h,
      even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  · simp only [toggleLocus, if_neg h, Finset.card_insert_of_notMem h,
      even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega

def evenOddSubsetEquiv (i : I) :
    {S : Finset I // Even S.card} ≃ {S : Finset I // ¬ Even S.card} where
  toFun S := ⟨toggleLocus i S.val, by rw [toggleLocus_parity]; exact not_not.mpr S.property⟩
  invFun S := ⟨toggleLocus i S.val, (toggleLocus_parity i S.val).mpr S.property⟩
  left_inv S := by apply Subtype.ext; exact toggleLocus_involutive i S.val
  right_inv S := by apply Subtype.ext; exact toggleLocus_involutive i S.val

/-- Half the subsets are even; these are exactly the independent phase modes. -/
theorem phase_mode_count (i : I) :
    Fintype.card {S : Finset I // Even S.card} = 2 ^ (Fintype.card I - 1) := by
  have he := Fintype.card_congr (evenOddSubsetEquiv i)
  have hc := Fintype.card_subtype_compl (fun S : Finset I => Even S.card)
  rw [Fintype.card_finset] at hc
  have hp : 0 < Fintype.card I := by
    letI : Nonempty I := ⟨i⟩
    exact Fintype.card_pos
  have hpow : 2 ^ Fintype.card I = 2 ^ (Fintype.card I - 1) * 2 := by
    conv_lhs => rw [show Fintype.card I = (Fintype.card I - 1) + 1 by omega]
    rw [pow_succ]
  omega

/-- Removing the constant leaves exactly the dosage-invisible phase modes. -/
theorem nonconstant_phase_mode_count (i : I) :
    ((Finset.univ.filter (fun S : Finset I => Even S.card)).erase ∅).card =
      2 ^ (Fintype.card I - 1) - 1 := by
  rw [Finset.card_erase_of_mem (by simp)]
  have he : (Finset.univ.filter (fun S : Finset I => Even S.card)).card =
      Fintype.card {S : Finset I // Even S.card} := (Fintype.card_subtype _).symm
  rw [he, phase_mode_count i]

end Descent.Portability.ArchaicPrediction
