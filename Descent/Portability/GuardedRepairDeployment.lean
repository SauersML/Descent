/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HardBudgetAuditGuard

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability's deployed hard-budget repair. A rejected
selection returns exactly the baseline; an accepted selection uses the
original certified continuous repair. Under the same actual joint law,
the probability of deploying a correction with negative expected frame
gain is at most the original audit error budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GuardedRepairDeployment

open MeasureTheory Matrix DecisionLossContrasts GramSafeRepair GramAuditGeometry
open CertifiedFrameRepair JointAuditExperiment HardBudgetAuditGuard

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The deployed coefficient vector, returning the baseline when the whole audit is aborted. -/
noncomputable def coefficient (w f : ι → ℝ) (φ : ι → κ → ℝ) (ε : ℝ)
    (p q c : ι → ℝ) (hard : ℝ) (z : ι → ℝ × ℝ) : κ → ℝ := by
  classical
  exact if Proceed c hard (requests z) then
    repair (gram w φ) (estimate w f φ (observations p q z)) ε else 0

/-- The actual expected frame gain of the guarded deployed coefficient. -/
noncomputable def deployedGain (μ : ι → Measure ℝ) (w f : ι → ℝ) (φ : ι → κ → ℝ)
    (ε : ℝ) (p q c : ι → ℝ) (hard : ℝ) (z : ι → ℝ × ℝ) : ℝ :=
  frameRisk μ w f - frameRisk μ w (predict f φ (coefficient w f φ ε p q c hard z))

/-- An aborted audit returns the original predictions exactly. -/
theorem abort_prediction (w f : ι → ℝ) (φ : ι → κ → ℝ) (ε : ℝ)
    (p q c : ι → ℝ) (hard : ℝ) (z : ι → ℝ × ℝ) (hz : ¬ Proceed c hard (requests z)) :
    predict f φ (coefficient w f φ ε p q c hard z) = f := by
  rw [coefficient, if_neg hz]
  funext i
  simp only [predict, dotProduct_zero, add_zero]

/-- An aborted audit changes expected loss by exactly zero. -/
theorem abort_gain (μ : ι → Measure ℝ) (w f : ι → ℝ) (φ : ι → κ → ℝ) (ε : ℝ)
    (p q c : ι → ℝ) (hard : ℝ) (z : ι → ℝ × ℝ) (hz : ¬ Proceed c hard (requests z)) :
    deployedGain μ w f φ ε p q c hard z = 0 := by
  rw [deployedGain, abort_prediction w f φ ε p q c hard z hz, sub_self]

/-- On proceeding, deployed expected gain is exactly the original audit-certified gain. -/
theorem proceed_gain (μ : ι → Measure ℝ) (w f : ι → ℝ) (φ : ι → κ → ℝ) (ε : ℝ)
    (p q c : ι → ℝ) (hard : ℝ) (z : ι → ℝ × ℝ) (hz : Proceed c hard (requests z)) :
    deployedGain μ w f φ ε p q c hard z = improvement μ w f φ ε (observations p q z) := by
  rw [deployedGain, coefficient, if_pos hz]
  rfl

/-- Negative deployed expected gain implies that an issued repair certificate was false. -/
theorem harm_implies_false_certificate (μ : ι → Measure ℝ) (w f : ι → ℝ)
    (φ : ι → κ → ℝ) (ε : ℝ) (p q c : ι → ℝ) (hard : ℝ) (z : ι → ℝ × ℝ)
    (hharm : deployedGain μ w f φ ε p q c hard z < 0) :
    Proceed c hard (requests z) ∧ ¬ Certificate μ w f φ ε (observations p q z) := by
  by_cases hz : Proceed c hard (requests z)
  · refine ⟨hz, ?_⟩
    intro hc
    have hn := (sq_nonneg (max 0 (signal (gram w φ)
      (estimate w f φ (observations p q z)) - ε))).trans hc.1
    rw [proceed_gain μ w f φ ε p q c hard z hz] at hharm
    exact not_lt_of_ge hn hharm
  · rw [abort_gain μ w f φ ε p q c hard z hz] at hharm
    exact (lt_irrefl 0 hharm).elim

/-- The guarded procedure has negative expected gain with probability at most delta. -/
theorem harm_probability [Nonempty ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (gram w φ).PosDef)
    (L U p q lo hi c : ι → ℝ) (hard δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (jointLaw μ p).real {z | deployedGain μ w f φ (auditRadius w φ hG L U p q lo hi δ)
      p q c hard z < 0} ≤ δ := by
  letI := joint_probability μ p (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  exact (measureReal_mono (show
    {z | deployedGain μ w f φ (auditRadius w φ hG L U p q lo hi δ) p q c hard z < 0} ⊆
    {z | Proceed c hard (requests z) ∧
      ¬ Certificate μ w f φ (auditRadius w φ hG L U p q lo hi δ) (observations p q z)}
    from fun z hz ↦ harm_implies_false_certificate μ w f φ _ p q c hard z hz)).trans
    (guarded_repair_certificate μ w f φ hG L U p q lo hi c hard δ hδ hp hq hs hm)

end Descent.Portability.GuardedRepairDeployment
