/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BernoulliBudgetLaw
import Descent.Portability.CertifiedFrameRepair

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Corollary 26: draw the full proposed selection,
check its cost before outcomes are requested, and either keep the entire
audit or abort it. The guard preserves the original unconditional error
bound by an event inclusion under the explicit joint selection/outcome law.
The retained baseline carries no unproved new certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HardBudgetAuditGuard

open MeasureTheory JointAuditExperiment BernoulliBudgetLaw IndependentContrastLaw
open SharedAuditCompletion CertifiedFrameRepair

variable {ι : Type*} [Fintype ι]

/-- The entire proposed audit proceeds exactly when its precomputed cost fits. -/
def Proceed (c : ι → ℝ) (hard : ℝ) (a : ι → ℝ) : Prop := contrast c a ≤ hard

/-- The requests actually performed: every proposed request, or none of them. -/
noncomputable def performed (c : ι → ℝ) (hard : ℝ) (a : ι → ℝ) : ι → ℝ := by
  classical
  exact if Proceed c hard a then a else 0

/-- On proceeding, every original selection indicator is retained exactly. -/
theorem performed_on_proceed (c a : ι → ℝ) (hard : ℝ) (ha : Proceed c hard a) :
    performed c hard a = a := by simp only [performed, if_pos ha]

/-- An oversized proposed audit requests no outcomes at all. -/
theorem performed_on_abort (c a : ι → ℝ) (hard : ℝ) (ha : hard < contrast c a) :
    performed c hard a = 0 := by
  simp only [performed, Proceed, if_neg (not_le.mpr ha)]

/-- The procedure never exceeds the hard budget, pointwise in the proposed selection. -/
theorem spending_le_hard (c a : ι → ℝ) (hard : ℝ) (hhard : 0 ≤ hard) :
    contrast c (performed c hard a) ≤ hard := by
  by_cases ha : Proceed c hard a
  · rw [performed_on_proceed c a hard ha]
    exact ha
  · simp only [performed, if_neg ha, contrast, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact hhard

/-- Budget selection is a function of the coins alone, before any outcome information is used. -/
theorem same_requests_same_guard (c : ι → ℝ) (hard : ℝ) (z z' : ι → ℝ × ℝ)
    (hz : requests z = requests z') :
    performed c hard (requests z) = performed c hard (requests z') := by rw [hz]

/-- Retaining or suppressing a proposed binary request keeps it a binary request. -/
theorem performed_binary (c a : ι → ℝ) (hard : ℝ) (ha : ∀ i, a i = 0 ∨ a i = 1) :
    ∀ i, performed c hard a i = 0 ∨ performed c hard a i = 1 := by
  intro i
  unfold performed
  split_ifs
  · exact ha i
  · exact Or.inl rfl

/-- A false certificate after proceeding is a failure of the original unmodified audit. -/
theorem guarded_failure_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q c : ι → ℝ) (hard : ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (bad : Set (ι → ℝ)) :
    (jointLaw μ p).real {z | Proceed c hard (requests z) ∧ observations p q z ∈ bad} ≤
      (frameLaw μ p q).real bad := by
  letI := joint_probability μ p hp
  exact (measureReal_mono (show
    {z | Proceed c hard (requests z) ∧ observations p q z ∈ bad} ⊆
      (observations p q) ⁻¹' bad from fun _ hz ↦ hz.2)).trans
    (observation_failure_le μ p q hp bad)

/-- The proposed selection is measurable as a function of the joint experiment. -/
theorem requests_measurable : Measurable (requests : (ι → ℝ × ℝ) → ι → ℝ) :=
  measurable_pi_lambda _ (fun i ↦ measurable_fst.comp (measurable_pi_apply i))

/-- The abort-probability statement holds under the full joint audit experiment. -/
theorem joint_abort_probability [Nonempty ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p c : ι → ℝ) (hard δ : ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hc : ∀ i, 0 ≤ c i) (hδ : 0 < δ ∧ δ < 1)
    (hbudget : contrast c p + BernsteinTailBound.radius (maxCost c) (costVariance c p)
      (Real.log (1 / δ)) ≤ hard) :
    (jointLaw μ p).real {z | ¬ Proceed c hard (requests z)} ≤ δ := by
  letI := requestFrame_probability p hp
  have hh := Measure.le_map_apply (μ := jointLaw μ p) requests_measurable.aemeasurable
    {a | hard < contrast c a}
  rw [requests_map μ p hp] at hh
  have hr := ENNReal.toReal_mono (measure_ne_top (requestFrame p) _) hh
  have he : {z | ¬ Proceed c hard (requests z)} = requests ⁻¹' {a | hard < contrast c a} := by
    ext z
    simp only [Proceed, Set.mem_setOf_eq, Set.mem_preimage, not_le]
  rw [he]
  exact hr.trans (abort_probability c p hard δ hp hc hδ hbudget)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The actual continuous-repair certificate retains its original unconditional error budget. -/
theorem guarded_repair_certificate [Nonempty ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (φ : ι → κ → ℝ) (hG : (DecisionLossContrasts.gram w φ).PosDef)
    (L U p q lo hi c : ι → ℝ) (hard δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (jointLaw μ p).real {z | Proceed c hard (requests z) ∧
      ¬ Certificate μ w f φ (auditRadius w φ hG L U p q lo hi δ) (observations p q z)} ≤ δ := by
  exact (guarded_failure_le μ p q c hard (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
    {a | ¬ Certificate μ w f φ (auditRadius w φ hG L U p q lo hi δ) a}).trans
    (false_certificate_probability μ w f φ hG L U p q lo hi δ hδ hp hq hs hm)

end Descent.Portability.HardBudgetAuditGuard
