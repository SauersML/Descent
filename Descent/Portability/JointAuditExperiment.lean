/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SharedAuditCompletion
import Mathlib.MeasureTheory.Measure.Prod

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability's explicit joint audit experiment. Each unit
has an independent Bernoulli request and an independent outcome. The product
experiment retains the selection coins, which are necessary for the hard
budget guard. Its augmented-observation pushforward is proved equal to the
law used in the already checked confidence and repair theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.JointAuditExperiment

open MeasureTheory AugmentedAuditLaw BoundedAuditCompletion SharedAuditCompletion

/-- The actual Bernoulli request law on zero and one. -/
noncomputable def requestLaw (p : ℝ) : Measure ℝ := endpointLaw 0 1 p

/-- The request and outcome for one audit unit are independent. -/
noncomputable def unitLaw (μ : Measure ℝ) (p : ℝ) : Measure (ℝ × ℝ) := (requestLaw p).prod μ

/-- The augmented observation, retaining the actual selection coin as its first input. -/
noncomputable def augmented (p q : ℝ) (z : ℝ × ℝ) : ℝ := q + z.1 * (z.2 - q) / p

/-- The transformation from the joint experiment to the reported observation is measurable. -/
theorem augmented_measurable (p q : ℝ) : Measurable (augmented p q) := by
  unfold augmented
  fun_prop

/-- Valid Bernoulli request rates give an actual probability law. -/
theorem request_probability (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : IsProbabilityMeasure (requestLaw p) :=
  endpointLaw_probability 0 1 p (by norm_num) hp

/-- The joint request/outcome law is normalized. -/
theorem unit_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) : IsProbabilityMeasure (unitLaw μ p) := by
  letI := request_probability p hp
  unfold unitLaw
  infer_instance

/-- The explicit coin/outcome experiment has exactly the previously used augmented-audit law. -/
theorem unit_map_augmented (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ) :
    (unitLaw μ p).map (augmented p q) = auditLaw μ p q := by
  unfold unitLaw requestLaw endpointLaw upperMass
  simp only [sub_zero, div_one]
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ (augmented_measurable p q)]
  simp only [Measure.map_smul, Measure.dirac_prod]
  rw [Measure.map_map (augmented_measurable p q) measurable_prodMk_left,
    Measure.map_map (augmented_measurable p q) measurable_prodMk_left]
  have hzero : augmented p q ∘ Prod.mk 0 = fun _ : ℝ ↦ q := by
    funext y
    simp only [Function.comp_apply, augmented, zero_mul, zero_div, add_zero]
  have hone : augmented p q ∘ Prod.mk 1 = observed p q := by
    funext y
    simp only [Function.comp_apply, augmented, one_mul, observed]
  rw [hzero, hone, Measure.map_const, measure_univ, one_smul]
  rfl

variable {ι : Type*} [Fintype ι]

/-- The full independent experiment keeps all request coins and outcomes. -/
noncomputable def jointLaw (μ : ι → Measure ℝ) (p : ι → ℝ) : Measure (ι → ℝ × ℝ) :=
  Measure.pi (fun i ↦ unitLaw (μ i) (p i))

/-- The complete augmented observation vector produced by the explicit experiment. -/
noncomputable def observations (p q : ι → ℝ) (z : ι → ℝ × ℝ) : ι → ℝ :=
  fun i ↦ augmented (p i) (q i) (z i)

/-- The proposed request vector is available before observing any outcomes. -/
def requests (z : ι → ℝ × ℝ) : ι → ℝ := fun i ↦ (z i).1

/-- The actual product law of all proposed requests. -/
noncomputable def requestFrame (p : ι → ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun i ↦ requestLaw (p i))

/-- The observation vector is measurable. -/
theorem observations_measurable (p q : ι → ℝ) : Measurable (observations p q) := by
  exact measurable_pi_lambda _ (fun i ↦ (augmented_measurable (p i) (q i)).comp
    (measurable_pi_apply i))

/-- Valid request rates normalize the full coin/outcome experiment. -/
theorem joint_probability (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : IsProbabilityMeasure (jointLaw μ p) := by
  letI (i : ι) := unit_probability (μ i) (p i) (hp i)
  unfold jointLaw
  infer_instance

/-- The pushforward connects retained selection coins to the existing audit theorems. -/
theorem observations_map (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (jointLaw μ p).map (observations p q) = frameLaw μ p q := by
  letI (i : ι) := unit_probability (μ i) (p i) (hp i)
  letI (i : ι) : IsProbabilityMeasure ((unitLaw (μ i) (p i)).map (augmented (p i) (q i))) :=
    Measure.isProbabilityMeasure_map (augmented_measurable (p i) (q i)).aemeasurable
  unfold jointLaw observations
  rw [Measure.pi_map_pi (fun i ↦ (augmented_measurable (p i) (q i)).aemeasurable)]
  simp only [unit_map_augmented, frameLaw]

/-- Forgetting outcomes leaves exactly the independent Bernoulli request law. -/
theorem requests_map (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (jointLaw μ p).map requests = requestFrame p := by
  letI (i : ι) := unit_probability (μ i) (p i) (hp i)
  letI (i : ι) : IsProbabilityMeasure ((unitLaw (μ i) (p i)).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  unfold jointLaw requests
  rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
  simp only [unitLaw, Measure.map_fst_prod, measure_univ, one_smul, requestFrame]

/-- Arbitrary audit failure sets transfer to the joint experiment with no larger probability. -/
theorem observation_failure_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (bad : Set (ι → ℝ)) :
    (jointLaw μ p).real ((observations p q) ⁻¹' bad) ≤ (frameLaw μ p q).real bad := by
  letI := frameLaw_probability μ p q hp
  have hh := Measure.le_map_apply (μ := jointLaw μ p) (observations_measurable p q).aemeasurable bad
  rw [observations_map μ p q hp] at hh
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

end Descent.Portability.JointAuditExperiment
