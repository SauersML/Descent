/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RareEventInformationLaw
import Descent.Portability.IIDAverageLaw

assert_below Descent.Decision Descent.Program

/-!
The actual marked sample has a common no-event restriction at every effect size.
Its mass is (1-η)^M. A two-point prior therefore gives a finite-sample Bayes
squared-error floor for every measurable estimator. Risk is extended nonnegative
so the theorem also covers estimators whose squared error is not integrable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RareEventAbsenceRisk

open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory RareEventInformationLaw

/-- A single observation with no occurrence of the named genotype event. -/
def absent : Set (Bool × ℝ) := {zy | zy.1 = false}

/-- The actual independent marked experiment with M observations. -/
noncomputable def sampleLaw (η : ℝ) (v : ℝ≥0) (θ : ℝ) (M : ℕ) :
    Measure (Fin M → Bool × ℝ) := Measure.pi (fun _ ↦ experimentLaw η v θ)

/-- The measurable event that all sampled genotype-event marks are absent. -/
def noEvents (M : ℕ) : Set (Fin M → Bool × ℝ) := Set.univ.pi (fun _ ↦ absent)

/-- The absence event is observable in the marked experiment. -/
theorem absent_measurable : MeasurableSet absent :=
  (measurableSet_singleton false).preimage measurable_fst

/-- Restricted to an absent event, the experiment has a parameter-free Gaussian law. -/
theorem experiment_absent_restriction (η : ℝ) (v : ℝ≥0) (θ : ℝ) :
    (experimentLaw η v θ).restrict absent =
      ENNReal.ofReal (1 - η) • (gaussianReal 0 v).map (fun y ↦ (false, y)) := by
  rw [experimentLaw, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    Measure.restrict_map (by fun_prop) absent_measurable,
    Measure.restrict_map (by fun_prop) absent_measurable]
  simp [absent]

/-- Exact probability of one absent mark under the original experiment. -/
theorem experiment_absent_mass (η : ℝ) (v : ℝ≥0) (θ : ℝ) :
    experimentLaw η v θ absent = ENNReal.ofReal (1 - η) := by
  rw [← Measure.restrict_apply_univ, experiment_absent_restriction]
  simp [Measure.map_apply (by fun_prop : Measurable (fun y : ℝ ↦ (false, y)))
    MeasurableSet.univ]

/-- All parameter values induce exactly the same restricted full sample law on no events. -/
theorem sample_noEvents_restriction (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (v : ℝ≥0) (θ : ℝ) (M : ℕ) :
    (sampleLaw η v θ M).restrict (noEvents M) =
      (sampleLaw η v 0 M).restrict (noEvents M) := by
  letI := experimentLaw_probability η hη v θ
  letI := experimentLaw_probability η hη v 0
  unfold sampleLaw noEvents
  rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  simp_rw [experiment_absent_restriction]

/-- The actual finite-sample probability of receiving no genotype events. -/
theorem sample_noEvents_mass (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (v : ℝ≥0) (θ : ℝ) (M : ℕ) :
    sampleLaw η v θ M (noEvents M) = ENNReal.ofReal ((1 - η) ^ M) := by
  letI := experimentLaw_probability η hη v θ
  rw [sampleLaw, noEvents, Measure.pi_pi]
  simp only [experiment_absent_mass, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (sub_nonneg.mpr hη.2)]

/-- Extended squared-error risk, retaining infinite risk rather than totalizing its integral. -/
noncomputable def squaredRisk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((T x - θ) ^ 2) ∂μ

/-- Any common submeasure of two experiments creates a two-point squared-error floor. -/
theorem common_submeasure_risk {Ω : Type*} [MeasurableSpace Ω]
    (μ ν ρ : Measure Ω) (hμ : ρ ≤ μ) (hν : ρ ≤ ν)
    (T : Ω → ℝ) (hT : Measurable T) (B : ℝ) :
    ENNReal.ofReal (B ^ 2) * ρ Set.univ ≤
      ENNReal.ofReal (1 / 2 : ℝ) * (squaredRisk μ T B + squaredRisk ν T (-B)) := by
  have hh : ENNReal.ofReal (2 * B ^ 2) * ρ Set.univ ≤
      squaredRisk μ T B + squaredRisk ν T (-B) := by
    calc
      _ = ∫⁻ _ : Ω, ENNReal.ofReal (2 * B ^ 2) ∂ρ := (lintegral_const _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal ((T x - B) ^ 2) +
          ENNReal.ofReal ((T x - (-B)) ^ 2) ∂ρ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg (T x)]
      _ = squaredRisk ρ T B + squaredRisk ρ T (-B) := by
        exact lintegral_add_left (by fun_prop) _
      _ ≤ _ := add_le_add (lintegral_mono' hμ (le_refl _))
        (lintegral_mono' hν (le_refl _))
  have he : ENNReal.ofReal (B ^ 2) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * B ^ 2) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  rw [he, mul_assoc]
  exact mul_le_mul_left' hh _

/-- Exact finite-sample Bayes risk floor under the report's symmetric two-point prior. -/
theorem no_events_bayes_floor (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (v : ℝ≥0) (M : ℕ) (B : ℝ) (T : (Fin M → Bool × ℝ) → ℝ) (hT : Measurable T) :
    ENNReal.ofReal (B ^ 2 * (1 - η) ^ M) ≤ ENNReal.ofReal (1 / 2 : ℝ) *
      (squaredRisk (sampleLaw η v B M) T B + squaredRisk (sampleLaw η v (-B) M) T (-B)) := by
  let ρ := (sampleLaw η v 0 M).restrict (noEvents M)
  have hp : ρ ≤ sampleLaw η v B M := by
    rw [show ρ = (sampleLaw η v B M).restrict (noEvents M) from
      (sample_noEvents_restriction η hη v B M).symm]
    exact Measure.restrict_le_self
  have hn : ρ ≤ sampleLaw η v (-B) M := by
    rw [show ρ = (sampleLaw η v (-B) M).restrict (noEvents M) from
      (sample_noEvents_restriction η hη v (-B) M).symm]
    exact Measure.restrict_le_self
  have hh := common_submeasure_risk _ _ ρ hp hn T hT B
  have hm : ρ Set.univ = ENNReal.ofReal ((1 - η) ^ M) := by
    dsimp only [ρ]
    rw [Measure.restrict_apply_univ, sample_noEvents_mass η hη v 0 M]
  rw [hm, ← ENNReal.ofReal_mul (sq_nonneg B)] at hh
  exact hh

end Descent.Portability.RareEventAbsenceRisk
