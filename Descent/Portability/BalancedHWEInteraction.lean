/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEInteractionLaw
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

assert_below Descent.Decision Descent.Program

/-!
The balanced HWE interaction has an exact sparse signed law, derived from the
full independent genotype experiment. Its atom at zero and two equal nonzero
atoms yield the critical disjoint-interaction mechanism directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWEInteraction

open scoped BigOperators
open Foundations HWEInteractionLaw

/-- Centered balanced diploid dosage, retaining its heterozygote zero. -/
def code : DiploidGenotype → ℝ
  | .homRef => -1
  | .het => 0
  | .homAlt => 1

/-- This sparse coordinate is exactly the existing standardized genotype divided by √2. -/
theorem standardized_coordinate (g : DiploidGenotype) :
    HardyWeinbergModel.witness.standardizedGenotype g = Real.sqrt 2 * code g := by
  have hv : HardyWeinbergModel.witness.genotypeVariance = 1 / 2 := by
    rw [HardyWeinbergModel.genotypeVariance_eq]
    norm_num [HardyWeinbergModel.witness, HardyWeinbergModel.refFreq]
  rw [HardyWeinbergModel.standardizedGenotype, hv, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one, div_div_eq_mul_div]
  cases g <;> norm_num [code, HardyWeinbergModel.centeredAltAlleleCount,
    HardyWeinbergModel.witness, HardyWeinbergModel.expectedAltAlleleCount_eq,
    altAlleleCount, Core.Genotype.dosage]

noncomputable def blockCode {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → DiploidGenotype) : ℝ :=
  ∏ i, code (x i)

/-- Exact relation between the sparse block and the original standardized HWE monomial. -/
theorem interaction_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → DiploidGenotype) :
    interaction (fun _ : ι ↦ HardyWeinbergModel.witness) x =
      Real.sqrt 2 ^ Fintype.card ι * blockCode x := by
  simp only [interaction, standardized_coordinate, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, blockCode]

/-- Every realized block lies at one of the three claimed atoms. -/
theorem blockCode_values {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → DiploidGenotype) :
    blockCode x = 0 ∨ blockCode x = 1 ∨ blockCode x = -1 := by
  have hc : blockCode x ^ 3 = blockCode x := by
    simp only [blockCode, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> norm_num [code]
  have hz : blockCode x * (blockCode x - 1) * (blockCode x + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- The signed block mean vanishes at every positive interaction order. -/
theorem blockCode_mean {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (blockLaw (fun _ : ι ↦ HardyWeinbergModel.witness)).expectation blockCode = 0 := by
  change (independentLaw (fun _ : ι ↦ locusLaw HardyWeinbergModel.witness)).expectation
    (fun x ↦ ∏ i, code (x i)) = 0
  rw [expectation_independent_product]
  have hmean : (locusLaw HardyWeinbergModel.witness).expectation code = 0 := by
    rw [FiniteReportLaw.expectation, Core.Genotype.sum_univ]
    norm_num [locusLaw, HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
      HardyWeinbergModel.witness, code]
  simp only [hmean]
  simp

/-- Nonzero block probability is exactly 2 to the minus interaction order. -/
theorem blockCode_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (blockLaw (fun _ : ι ↦ HardyWeinbergModel.witness)).expectation
      (fun x ↦ blockCode x ^ 2) = (1 / 2 : ℝ) ^ Fintype.card ι := by
  simp only [blockCode, ← Finset.prod_pow]
  rw [blockLaw, expectation_independent_product
    (fun _ : ι ↦ locusLaw HardyWeinbergModel.witness) (fun _ g ↦ code g ^ 2)]
  have hsecond : (locusLaw HardyWeinbergModel.witness).expectation
      (fun g ↦ code g ^ 2) = 1 / 2 := by
    rw [FiniteReportLaw.expectation, Core.Genotype.sum_univ]
    norm_num [locusLaw, HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
      HardyWeinbergModel.witness, code]
  simp only [hsecond, Finset.prod_const, Finset.card_univ]

/-- Exact pushforward formula for every real observable of one block. This
identifies all three atom masses, rather than only checking selected moments. -/
theorem blockCode_law {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : ℝ → ℝ) :
    (blockLaw (fun _ : ι ↦ HardyWeinbergModel.witness)).expectation
      (fun x ↦ f (blockCode x)) =
      (1 - (1 / 2 : ℝ) ^ Fintype.card ι) * f 0 +
        ((1 / 2 : ℝ) ^ Fintype.card ι / 2) * (f 1 + f (-1)) := by
  let p := blockLaw (fun _ : ι ↦ HardyWeinbergModel.witness)
  have hpoint : ∀ x : ι → DiploidGenotype, f (blockCode x) =
      f 0 + ((f 1 - f (-1)) / 2) * blockCode x +
        ((f 1 + f (-1)) / 2 - f 0) * blockCode x ^ 2 := by
    intro x
    rcases blockCode_values x with h | h | h <;> rw [h] <;> ring
  simp_rw [hpoint]
  have hmean : p.expectation blockCode = 0 := blockCode_mean
  have hsecond : p.expectation (fun x ↦ blockCode x ^ 2) =
      (1 / 2 : ℝ) ^ Fintype.card ι := blockCode_second_moment
  change (∑ x, p.mass x * _) = _
  simp only [mul_add, Finset.sum_add_distrib]
  have hc : (∑ x, p.mass x * f 0) = f 0 := by rw [← Finset.sum_mul, p.mass_sum, one_mul]
  have hlinear : (∑ x, p.mass x * (((f 1 - f (-1)) / 2) * blockCode x)) = 0 := by
    simp_rw [mul_left_comm (p.mass _) ((f 1 - f (-1)) / 2)]
    rw [← Finset.mul_sum]
    change _ * p.expectation blockCode = 0
    rw [hmean, mul_zero]
  have hquadratic : (∑ x, p.mass x *
      (((f 1 + f (-1)) / 2 - f 0) * blockCode x ^ 2)) =
      ((f 1 + f (-1)) / 2 - f 0) * (1 / 2 : ℝ) ^ Fintype.card ι := by
    simp_rw [mul_left_comm (p.mass _) ((f 1 + f (-1)) / 2 - f 0)]
    rw [← Finset.mul_sum]
    change _ * p.expectation (fun x ↦ blockCode x ^ 2) = _
    rw [hsecond]
  rw [hc, hlinear, hquadratic]
  ring

/-- The exact single-block characteristic function includes the heterozygote atom. -/
theorem block_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (a t : ℝ) :
    complexExpectation (blockLaw (fun _ : ι ↦ HardyWeinbergModel.witness))
      (fun x ↦ Complex.exp ((t * (a * blockCode x) : ℝ) * Complex.I)) =
      (1 + (1 / 2 : ℝ) ^ Fintype.card ι * (Real.cos (t * a) - 1) : ℝ) := by
  apply Complex.ext
  · rw [characteristic_re, blockCode_law (fun z ↦ Real.cos (t * (a * z)))]
    simp only [mul_zero, Real.cos_zero, mul_one, mul_neg, Real.cos_neg, Complex.ofReal_re]
    ring
  · rw [characteristic_im, blockCode_law (fun z ↦ Real.sin (t * (a * z)))]
    simp only [mul_zero, Real.sin_zero, mul_one, mul_neg, Real.sin_neg, Complex.ofReal_im]
    ring

/-- Independent disjoint blocks retain every sampled genotype. -/
noncomputable def rowLaw (m N : ℕ) : FiniteReportLaw (Fin N → Fin m → DiploidGenotype) :=
  independentLaw (fun _ : Fin N ↦ blockLaw
    (fun _ : Fin m ↦ HardyWeinbergModel.witness))

/-- The sum of normalized sparse block contributions. -/
noncomputable def rowScore {m N : ℕ} (a : ℝ)
    (x : Fin N → Fin m → DiploidGenotype) : ℝ := ∑ j, a * blockCode (x j)

/-- Exact finite-array characteristic function of the genuine independent HWE experiment. -/
theorem row_characteristic (m N : ℕ) (hm : 0 < m) (a t : ℝ) :
    complexExpectation (rowLaw m N)
      (fun x ↦ Complex.exp ((t * rowScore a x : ℝ) * Complex.I)) =
      ((1 + (1 / 2 : ℝ) ^ m * (Real.cos (t * a) - 1)) ^ N : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  change complexExpectation (independentLaw (fun _ : Fin N ↦ blockLaw
      (fun _ : Fin m ↦ HardyWeinbergModel.witness)))
    (fun x ↦ Complex.exp ((t * ∑ j, a * blockCode (x j) : ℝ) * Complex.I)) = _
  rw [characteristic_independent_sum
    (fun _ : Fin N ↦ blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness))
    (fun _ x ↦ a * blockCode x) t]
  simp only [block_characteristic, Fintype.card_fin, Finset.prod_const,
    Finset.card_univ, Complex.ofReal_pow]

/-- At N=2^m, the original standardization makes every nonzero block exactly ±1. -/
theorem critical_standardization (m : ℕ)
    (x : Fin (2 ^ m) → Fin m → DiploidGenotype) :
    (∑ j, interaction (fun _ : Fin m ↦ HardyWeinbergModel.witness) (x j)) /
      Real.sqrt (2 ^ m : ℕ) = rowScore 1 x := by
  have hs : Real.sqrt (2 ^ m : ℕ) = Real.sqrt 2 ^ m := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [hs]
  simp only [interaction_eq, Fintype.card_fin, ← Finset.mul_sum, rowScore, one_mul]
  have hn : Real.sqrt 2 ^ m ≠ 0 := pow_ne_zero _ (by positivity)
  exact mul_div_cancel_left₀ _ hn

/-- A fixed threshold strictly between zero and one detects every nonzero critical block. -/
theorem block_jump_probability (m : ℕ) (hm : 0 < m) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness)).expectation
      (fun x ↦ if τ < |blockCode x| then 1 else 0) = (1 / 2 : ℝ) ^ m := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [blockCode_law (fun z ↦ if τ < |z| then 1 else 0)]
  simp only [abs_zero, not_lt.mpr hτ0.le, if_false, abs_one, hτ1, if_true,
    abs_neg, Fintype.card_fin]
  ring

/-- The critical HWE block law cannot satisfy an order-uniform tilted-tail bound. -/
theorem no_uniform_tilted_tail_constant (C τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ¬ ∀ m : ℕ, 0 < m →
      (blockLaw (fun _ : Fin m ↦ HardyWeinbergModel.witness)).expectation
        (fun x ↦ if τ < |blockCode x| then 1 else 0) ≤
          C * (1 / 2 : ℝ) ^ m / (τ ^ 2 * Real.sqrt m) := by
  intro h
  have hlim := Blindness.no_macroscopic_interaction_limit C τ hτ0.ne'
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ C / (τ ^ 2 * Real.sqrt m) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hb := h m hm
    rw [block_jump_probability m hm τ hτ0 hτ1] at hb
    have hp : 0 < (1 / 2 : ℝ) ^ m := by positivity
    have heq : C * (1 / 2 : ℝ) ^ m / (τ ^ 2 * Real.sqrt m) =
        (C / (τ ^ 2 * Real.sqrt m)) * (1 / 2 : ℝ) ^ m := by ring
    rw [heq] at hb
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [one_mul] using hb)
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim hevent
  norm_num at hbad

/-- Critical balanced Fourier limit, with no Gaussian approximation hypothesis. -/
theorem critical_characteristic_limit (t : ℝ) :
    Filter.Tendsto (fun m : ℕ ↦
      (1 + (1 / 2 : ℝ) ^ m * (Real.cos t - 1)) ^ (2 ^ m))
      Filter.atTop (nhds (Real.exp (Real.cos t - 1))) := by
  have h := (Real.tendsto_one_add_div_pow_exp (Real.cos t - 1)).comp
    (Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
  apply h.congr
  intro m
  dsimp only [Function.comp_apply]
  have hp : (1 / 2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ)⁻¹ := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  rw [hp]
  congr 2
  ring

/-- No centered Gaussian characteristic function has this critical limit,
including a Gaussian with zero variance. -/
theorem critical_limit_not_gaussian (variance : ℝ) :
    ¬ (∀ t : ℝ, Real.exp (Real.cos t - 1) = Real.exp (-variance * t ^ 2 / 2)) := by
  intro h
  have hperiod := h (2 * Real.pi)
  rw [Real.cos_two_pi, sub_self, Real.exp_zero] at hperiod
  have hz : -variance * (2 * Real.pi) ^ 2 / 2 = 0 :=
    (Real.exp_eq_one_iff _).mp hperiod.symm
  have hvar : variance = 0 := by
    have hp : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
    have heq : variance * (2 * Real.pi) ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp heq).resolve_right hp
  have hhalf := h Real.pi
  rw [Real.cos_pi, hvar] at hhalf
  norm_num at hhalf

end Descent.Portability.BalancedHWEInteraction
