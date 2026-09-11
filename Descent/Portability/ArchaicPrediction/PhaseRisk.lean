/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Phase
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

theorem four_pairwise_moments (i j : Fin 4) (hij : i ≠ j) :
    (∑ h, phaseSign (plusPhases h) i * phaseSign (plusPhases h) j) / 4 = 0 ∧
    (∑ h, phaseSign (minusPhases h) i * phaseSign (minusPhases h) j) / 4 = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, plusPhases, minusPhases, phaseSign, allele] at *

theorem four_mean_logit :
    (∑ h, fourLogit (plusPhases h)) / 4 = -3 ∧
    (∑ h, fourLogit (minusPhases h)) / 4 = -3 := by
  norm_num [Fin.sum_univ_succ, fourLogit, plusPhases, minusPhases, phaseSign, allele]

theorem four_risk_formulas :
    (∑ h, Real.sigmoid (fourLogit (plusPhases h))) / 4 =
      (Real.sigmoid 1 + Real.sigmoid (-7)) / 2 ∧
    (∑ h, Real.sigmoid (fourLogit (minusPhases h))) / 4 = Real.sigmoid (-3) := by
  norm_num [Fin.sum_univ_succ, fourLogit, plusPhases, minusPhases, phaseSign, allele]
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
    apply (inv_lt_iff₀ (show 0 < 1 + Real.exp 3 by positivity)).mpr
    linarith
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

end Descent.Portability.ArchaicPrediction
