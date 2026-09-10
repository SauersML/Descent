/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# Transport a source-selected threshold and evaluate the actual decision rule

Confusion cells are expectations of threshold events under the supplied law.
An explicit source F1 optimum is deployed unchanged to a target population.
Its clinical ranking reverses when the relative false-positive cost changes.
This supplies a complete finite pipeline witness, not the paper's confusion
matrices or an application-independent recommendation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ThresholdPolicyTransport

open Foundations

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

noncomputable section

variable {Ω : Type*}

/-- Confusion probabilities computed from outcomes and a deployed decision rule. -/
def decisionCells (E : ExpFunctional Ω) (predict outcome : Ω → Bool) : ConfusionMatrix where
  tp := E (fun ω ↦ if predict ω && outcome ω then 1 else 0)
  fp := E (fun ω ↦ if predict ω && !outcome ω then 1 else 0)
  tn := E (fun ω ↦ if !predict ω && !outcome ω then 1 else 0)
  fn := E (fun ω ↦ if !predict ω && outcome ω then 1 else 0)
  tp_nonneg := E.nonneg_eval _ (by intro ω; split <;> norm_num)
  fp_nonneg := E.nonneg_eval _ (by intro ω; split <;> norm_num)
  tn_nonneg := E.nonneg_eval _ (by intro ω; split <;> norm_num)
  fn_nonneg := E.nonneg_eval _ (by intro ω; split <;> norm_num)
  mass_one := by
    rw [← E.add_eval, ← E.add_eval, ← E.add_eval]
    have h : (fun ω ↦ if predict ω && outcome ω then (1 : ℝ) else 0) +
        (fun ω ↦ if predict ω && !outcome ω then 1 else 0) +
        (fun ω ↦ if !predict ω && !outcome ω then 1 else 0) +
        (fun ω ↦ if !predict ω && outcome ω then 1 else 0) = (fun _ ↦ 1) := by
      funext ω
      cases hp : predict ω <;> cases hy : outcome ω <;> simp [hp, hy]
    rw [h, E.const_one]

/-- The cutoff is fixed before target evaluation. Equality is classified positive. -/
def thresholdCells (E : ExpFunctional Ω) (score : Ω → ℝ) (outcome : Ω → Bool)
    (cutoff : ℝ) : ConfusionMatrix :=
  decisionCells E (fun ω ↦ decide (cutoff ≤ score ω)) outcome

/-- Undefined F1 stays undefined instead of being assigned a numeric value. -/
def f1 (c : ConfusionMatrix) : Option ℝ :=
  if 0 < 2 * c.tp + c.fp + c.fn then
    some (2 * c.tp / (2 * c.tp + c.fp + c.fn)) else none

/-- False-negative cost is the unit of loss; lambda is false-positive cost. -/
def decisionLoss (c : ConfusionMatrix) (lambda : ℝ) : ℝ := c.fn + lambda * c.fp

def sourceLaw : ExpFunctional (Fin 4) :=
  weightedExp ![2 / 5, 1 / 10, 1 / 10, 2 / 5]
    (by intro i; fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_four])

def targetLaw : ExpFunctional (Fin 4) :=
  weightedExp ![1 / 10, 2 / 5, 2 / 5, 1 / 10]
    (by intro i; fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_four])

def score : Fin 4 → ℝ := ![3, 1, 2, 0]
def disease : Fin 4 → Bool := ![true, true, false, false]

/-- Cutoffs 0 through 4 represent every distinct decision rule for this score.
The selected source cutoff, 1, has F1=10/11 and maximizes source F1. -/
theorem source_f1_optimum :
    f1 (thresholdCells sourceLaw score disease 1) = some (10 / 11) ∧
      ∀ i : Fin 5, ∃ value : ℝ,
        f1 (thresholdCells sourceLaw score disease (i : ℝ)) = some value ∧
          value ≤ 10 / 11 := by
  constructor
  · norm_num [f1, thresholdCells, decisionCells, sourceLaw, score, disease,
      weightedExp_apply, Fin.sum_univ_four]
  · intro i
    fin_cases i <;>
      norm_num [f1, thresholdCells, decisionCells, sourceLaw, score, disease,
        weightedExp_apply, Fin.sum_univ_four]

/-- The exact same selected rule has a different target confusion matrix.
Prevalence is unchanged in this witness; distribution shift alone suffices. -/
theorem transported_operating_point :
    (thresholdCells sourceLaw score disease 1).prevalence = 1 / 2 ∧
      (thresholdCells targetLaw score disease 1).prevalence = 1 / 2 ∧
      (thresholdCells sourceLaw score disease 1).precision = 5 / 6 ∧
      (thresholdCells targetLaw score disease 1).precision = 5 / 9 ∧
      (thresholdCells sourceLaw score disease 1).recallRate = 1 ∧
      (thresholdCells targetLaw score disease 1).recallRate = 1 ∧
      f1 (thresholdCells targetLaw score disease 1) = some (5 / 7) := by
  norm_num [ConfusionMatrix.prevalence, ConfusionMatrix.precision,
    ConfusionMatrix.recallRate, f1, thresholdCells, decisionCells,
    sourceLaw, targetLaw, score, disease, weightedExp_apply, Fin.sum_univ_four]

/-- The source-selected threshold wins when false positives are inexpensive and
loses when they are expensive, on the same target data. -/
theorem clinical_ranking_reverses :
    decisionLoss (thresholdCells targetLaw score disease 1) (1 / 4) <
      decisionLoss (thresholdCells targetLaw score disease 3) (1 / 4) ∧
    decisionLoss (thresholdCells targetLaw score disease 3) 2 <
      decisionLoss (thresholdCells targetLaw score disease 1) 2 := by
  norm_num [decisionLoss, thresholdCells, decisionCells, targetLaw,
    score, disease, weightedExp_apply, Fin.sum_univ_four]

/-- Exact application-dependent break-even cost for the two target rules. -/
theorem clinical_choice_iff (lambda : ℝ) :
    decisionLoss (thresholdCells targetLaw score disease 1) lambda ≤
      decisionLoss (thresholdCells targetLaw score disease 3) lambda ↔ lambda ≤ 1 := by
  norm_num [decisionLoss, thresholdCells, decisionCells, targetLaw,
    score, disease, weightedExp_apply, Fin.sum_univ_four]
  constructor <;> intro h <;> linarith

end

end Descent.Portability.ThresholdPolicyTransport
