/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HardBudgetAuditGuard
import Mathlib.Probability.ConditionalProbability

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the conditional-on-proceeding consequence of
Corollary 26. Conditioning changes the probability statement: the general
bound is delta divided by one minus the abort bound. The denominator is
proved strictly positive, and the statement concerns the actual normalized
conditional probability measure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalGuardError

open MeasureTheory ProbabilityTheory JointAuditExperiment HardBudgetAuditGuard
open BernoulliBudgetLaw IndependentContrastLaw CertifiedFrameRepair

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual conditional measure obeys the sharp general amplification from an abort bound. -/
theorem conditional_error (μ : Measure Ω) [IsProbabilityMeasure μ] (good bad : Set Ω)
    (hgood : MeasurableSet good) (δ δB : ℝ) (hδ : 0 ≤ δ) (hδB : δB < 1)
    (hbad : μ.real (good ∩ bad) ≤ δ) (habort : μ.real goodᶜ ≤ δB) :
    IsProbabilityMeasure (cond μ good) ∧ (cond μ good).real bad ≤ δ / (1 - δB) := by
  have hadd := measureReal_add_measureReal_compl (μ := μ) hgood
  have hone : μ.real Set.univ = 1 := by simp [measureReal_def]
  rw [hone] at hadd
  have hlower : 1 - δB ≤ μ.real good := by linarith
  have hpos : 0 < μ.real good := (sub_pos.mpr hδB).trans_le hlower
  have hnz : μ good ≠ 0 := by
    intro hz
    simp only [measureReal_def, hz, ENNReal.toReal_zero] at hpos
    linarith
  refine ⟨cond_isProbabilityMeasure hnz, ?_⟩
  change ((cond μ good) bad).toReal ≤ _
  rw [cond_apply hgood μ bad, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (μ.real good)⁻¹ * μ.real (good ∩ bad) ≤ δ / (1 - δB)
  calc
    _ = μ.real (good ∩ bad) / μ.real good := by ring
    _ ≤ δ / μ.real good := div_le_div_of_nonneg_right hbad hpos.le
    _ ≤ δ / (1 - δB) := div_le_div_of_nonneg_left hδ (sub_pos.mpr hδB) hlower

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]

/-- The pre-outcome budget gate is a measurable event in the explicit experiment. -/
theorem proceed_measurable (c : ι → ℝ) (hard : ℝ) :
    MeasurableSet {z : ι → ℝ × ℝ | Proceed c hard (requests z)} := by
  unfold Proceed contrast requests
  apply measurableSet_le
  · fun_prop
  · exact measurable_const

/-- Conditioning the repair certificate on proceeding gives the amplified error bound. -/
theorem conditional_repair_certificate
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (DecisionLossContrasts.gram w φ).PosDef)
    (L U p q lo hi c : ι → ℝ) (hard δ δB : ℝ)
    (hδ : 0 < δ ∧ δ < 1) (hδB : 0 < δB ∧ δB < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i)
    (hbudget : contrast c p + BernsteinTailBound.radius (maxCost c) (costVariance c p)
      (Real.log (1 / δB)) ≤ hard) :
    (cond (jointLaw μ p) {z | Proceed c hard (requests z)}).real
      {z | ¬ Certificate μ w f φ (auditRadius w φ hG L U p q lo hi δ) (observations p q z)} ≤
        δ / (1 - δB) := by
  letI := joint_probability μ p (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  have hbad := guarded_repair_certificate μ w f φ hG L U p q lo hi c hard δ hδ hp hq hs hm
  have habort := joint_abort_probability μ p c hard δB
    (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩) hc hδB hbudget
  exact (conditional_error (jointLaw μ p) {z | Proceed c hard (requests z)}
    {z | ¬ Certificate μ w f φ (auditRadius w φ hG L U p q lo hi δ) (observations p q z)}
    (proceed_measurable c hard) δ δB hδ.1.le hδB.2 hbad habort).2

end Descent.Portability.ConditionalGuardError
