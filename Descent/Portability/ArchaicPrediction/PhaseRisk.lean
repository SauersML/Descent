/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Moments
import Mathlib.Analysis.SpecialFunctions.Sigmoid

assert_below Descent.Decision Descent.Program

/-!
# Pairwise phase information does not identify nonlinear risk

Theorem 6 is an explicit four-locus construction. Each row is a distinct
unordered phase represented by a positive first homologue sign. Both models
are uniform on four rows. Their probabilities are hypothetical model values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators

def plusPhases : Fin 4 → Fin 4 → Bool :=
  ![![true, true, true, true], ![true, true, false, false],
    ![true, false, true, false], ![true, false, false, true]]

def minusPhases : Fin 4 → Fin 4 → Bool :=
  ![![true, false, true, true], ![true, true, false, true],
    ![true, true, true, false], ![true, false, false, false]]

noncomputable def phaseSign (x : Fin 4 → Bool) (i : Fin 4) : ℝ := 2 * allele (x i) - 1

noncomputable def fourLogit (x : Fin 4 → Bool) : ℝ :=
  -3 + 2 * (phaseSign x 0 * phaseSign x 1 + phaseSign x 2 * phaseSign x 3)

theorem parity_phase_representatives :
    Function.Injective plusPhases ∧ Function.Injective minusPhases ∧
      (∀ h, plusPhases h 0 = true) ∧ (∀ h, minusPhases h 0 = true) := by decide

theorem dosage_ignores_phase (x : Fin 4 → Bool) (i : Fin 4) :
    allele (x i) + allele (homologSwap x i) = 1 := by
  cases h : x i <;> norm_num [homologSwap, allele, h]

theorem four_pairwise_moments (i j : Fin 4) (hij : i ≠ j) :
    (∑ h, phaseSign (plusPhases h) i * phaseSign (plusPhases h) j) / 4 = 0 ∧
    (∑ h, phaseSign (minusPhases h) i * phaseSign (minusPhases h) j) / 4 = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, plusPhases, minusPhases, phaseSign, allele] at *

theorem four_mean_logit :
    (∑ h, fourLogit (plusPhases h)) / 4 = -3 ∧
    (∑ h, fourLogit (minusPhases h)) / 4 = -3 := by
  norm_num [Fin.sum_univ_succ, fourLogit, plusPhases, minusPhases, phaseSign, allele,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

theorem four_risk_formulas :
    (∑ h, Real.sigmoid (fourLogit (plusPhases h))) / 4 =
      (Real.sigmoid 1 + Real.sigmoid (-7)) / 2 ∧
    (∑ h, Real.sigmoid (fourLogit (minusPhases h))) / 4 = Real.sigmoid (-3) := by
  norm_num [Fin.sum_univ_succ, fourLogit, plusPhases, minusPhases, phaseSign, allele,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  constructor <;> ring

/-- Strict separation of the two exact risks, with a rational separating value. -/
theorem four_risks_separated :
    Real.sigmoid (-3) < 1 / 4 ∧
      (1 : ℝ) / 4 < (Real.sigmoid 1 + Real.sigmoid (-7)) / 2 := by
  constructor
  · have he : 3 < Real.exp 3 := by
      have h := Real.add_one_le_exp (3 : ℝ)
      linarith
    rw [Real.sigmoid_def]
    norm_num only [neg_neg]
    have hd : 4 < 1 + Real.exp 3 := by linarith
    simpa only [one_div] using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hd)
  · have hp := Real.sigmoid_pos (-7)
    have hhalf := Real.sigmoid_lt (show (0 : ℝ) < 1 by norm_num)
    rw [Real.sigmoid_zero] at hhalf
    norm_num at hhalf
    linarith

/-- Theorem 6: a single summary-based calibrator cannot be correct for both
phase distributions, since their input pairwise summaries and mean logits agree. -/
theorem pairwise_phase_risk_not_identified :
    (∑ h, Real.sigmoid (fourLogit (plusPhases h))) / 4 ≠
      (∑ h, Real.sigmoid (fourLogit (minusPhases h))) / 4 := by
  rw [four_risk_formulas.1, four_risk_formulas.2]
  exact ne_of_gt (four_risks_separated.1.trans four_risks_separated.2)

noncomputable def fourRiskCenter : ℝ :=
  (Real.sigmoid 1 + Real.sigmoid (-7) + 2 * Real.sigmoid (-3)) / 4
noncomputable def fourRiskPairCoefficient : ℝ := (Real.sigmoid 1 - Real.sigmoid (-7)) / 4
noncomputable def fourRiskParityCoefficient : ℝ :=
  (Real.sigmoid 1 + Real.sigmoid (-7) - 2 * Real.sigmoid (-3)) / 4

/-- The link induces a fourth-order phase coefficient from a degree-two logit. -/
theorem four_risk_expansion (x : Fin 4 → Bool) :
    Real.sigmoid (fourLogit x) = fourRiskCenter + fourRiskPairCoefficient *
      (phaseSign x 0 * phaseSign x 1 + phaseSign x 2 * phaseSign x 3) +
        fourRiskParityCoefficient * phaseCharacter Finset.univ x := by
  have hfin : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    norm_num [fourLogit, phaseSign, phaseCharacter, Fin.prod_univ_succ, allele,
      hfin, h₀, h₁, h₂, h₃, fourRiskCenter, fourRiskPairCoefficient, fourRiskParityCoefficient] <;> ring

/-- Matching pairwise moments leaves precisely the parity contribution to risk. -/
theorem four_risk_from_parity {H : Type*} [Fintype H]
    (w : H → ℝ) (z : H → Fin 4 → Bool) (hw : ∑ h, w h = 1)
    (h₀₁ : weightedMean w (fun h => phaseSign (z h) 0 * phaseSign (z h) 1) = 0)
    (h₂₃ : weightedMean w (fun h => phaseSign (z h) 2 * phaseSign (z h) 3) = 0) :
    weightedMean w (fun h => Real.sigmoid (fourLogit (z h))) = fourRiskCenter +
      fourRiskParityCoefficient * weightedMean w (fun h => phaseCharacter Finset.univ (z h)) := by
  simp_rw [four_risk_expansion, weightedMean_add, weightedMean_scale,
    weightedMean_add, weightedMean_const w hw, h₀₁, h₂₃]
  ring

/-- The exact pair-moment risk interval in the four-locus example. The endpoint
laws are `minusPhases` and `plusPhases`, whose moments and risks are proved above. -/
theorem four_pair_moment_risk_bounds {H : Type*} [Fintype H]
    (w : H → ℝ) (z : H → Fin 4 → Bool) (hw : ∑ h, w h = 1) (hpos : ∀ h, 0 ≤ w h)
    (h₀₁ : weightedMean w (fun h => phaseSign (z h) 0 * phaseSign (z h) 1) = 0)
    (h₂₃ : weightedMean w (fun h => phaseSign (z h) 2 * phaseSign (z h) 3) = 0) :
    weightedMean w (fun h => Real.sigmoid (fourLogit (z h))) ∈
      Set.Icc (Real.sigmoid (-3)) ((Real.sigmoid 1 + Real.sigmoid (-7)) / 2) := by
  rw [four_risk_from_parity w z hw h₀₁ h₂₃]
  have ht := abs_le.mp (phase_moment_abs_le_one w hw hpos z Finset.univ)
  have hp := four_risks_separated.1.trans four_risks_separated.2
  dsimp [fourRiskCenter, fourRiskParityCoefficient]
  constructor <;> nlinarith

end Descent.Portability.ArchaicPrediction
