/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PairedMedianOfMeans
import Descent.Portability.LossExplainabilitySeparation

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, the explicit 2,500-label calculation following
Proposition 25. For every member of the changing-tail experiment, twenty-five
blocks of one hundred iid labels give the same positive paired-gain certificate
with failure probability at most five percent. The tail parameter is not an
audit inclusion probability; it only changes the outcome distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TailRepairCertification

open MeasureTheory ProbabilityTheory PairedGainTailExperiment PairedMedianOfMeans

/-- The explicit iid label study contains twenty-five blocks of one hundred paired observations. -/
noncomputable def studyLaw (p : ℝ) : Measure (Fin 25 → Fin 100 → Bool × Fin 3) :=
  Measure.pi (fun _ : Fin 25 ↦ Measure.pi (fun _ : Fin 100 ↦ jointLaw p))

/-- The study's paired median-of-means estimate. -/
noncomputable def estimatedGain (p : ℝ) : (Fin 25 → Fin 100 → Bool × Fin 3) → ℝ :=
  estimate (improvement (Real.sqrt p)⁻¹) 12 100

/-- Its confidence radius uses the proved gain variance six, uniformly in the tail parameter. -/
noncomputable def confidenceRadius : ℝ := 2 * Real.sqrt (6 / 100 : ℝ)

/-- The numerical radius is strictly below 0.49; this is exact real arithmetic. -/
theorem radius_lt : confidenceRadius < 49 / 100 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6 / 100)
  have hn := Real.sqrt_nonneg (6 / 100 : ℝ)
  unfold confidenceRadius
  nlinarith

/-- The exponential failure bound for twenty-five blocks is below five percent. -/
theorem exponential_bound : Real.exp (-(25 : ℝ) / 8) ≤ 1 / 20 := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 8) 8
  have he : (20 : ℝ) ≤ Real.exp (25 / 8) := by
    apply le_trans _ hh
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [show -(25 : ℝ) / 8 = -(25 / 8) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20) he

/-- The actual study estimate has the same confidence bound for every valid tail parameter. -/
theorem study_confidence (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    (studyLaw p).real {z | confidenceRadius < |estimatedGain p z - 5 / 4|} ≤ 1 / 20 := by
  letI := joint_probability p ⟨hp.1.le, hp.2⟩
  have ht := paired_tail (jointLaw p) (improvement (Real.sqrt p)⁻¹)
    (measurable_of_countable _) (joint_memLp p ⟨hp.1.le, hp.2⟩ _) 12 100 (by norm_num) 6
    (le_of_eq (exact_moment_packet p hp).2.2)
  rw [(exact_moment_packet p hp).2.1] at ht
  have ht' : (studyLaw p).real {z | confidenceRadius < |estimatedGain p z - 5 / 4|} ≤
      Real.exp (-(25 : ℝ) / 8) := by
    simpa only [studyLaw, estimatedGain, confidenceRadius, show 2 * 12 + 1 = 25 by omega,
      Nat.cast_ofNat] using ht
  exact ht'.trans exponential_bound

/-- The reported lower bound is positive and below true gain with at least 95 percent confidence. -/
theorem positive_repair_certificate (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    (studyLaw p).real {z | ¬ (0 < estimatedGain p z - confidenceRadius ∧
      estimatedGain p z - confidenceRadius ≤
        ∫ ω, improvement (Real.sqrt p)⁻¹ ω ∂jointLaw p)} ≤ 1 / 20 := by
  letI := joint_probability p ⟨hp.1.le, hp.2⟩
  letI : IsProbabilityMeasure (studyLaw p) := by unfold studyLaw; infer_instance
  rw [(exact_moment_packet p hp).2.1]
  apply (measureReal_mono (show
    {z | ¬ (0 < estimatedGain p z - confidenceRadius ∧
      estimatedGain p z - confidenceRadius ≤ 5 / 4)} ⊆
    {z | confidenceRadius < |estimatedGain p z - 5 / 4|} from ?_)).trans (study_confidence p hp)
  intro z hz
  change confidenceRadius < |estimatedGain p z - 5 / 4|
  apply lt_of_not_ge
  intro he
  obtain ⟨hlo, hhi⟩ := abs_le.mp he
  exact hz ⟨by linarith [radius_lt], by linarith⟩

end Descent.Portability.TailRepairCertification
