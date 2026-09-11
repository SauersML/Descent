/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PairedGainTailExperiment
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 3. The context predictor is identified
with the actual conditional expectation under the six-outcome experiment.
Its explained-loss variance fraction tends to zero while both the actual
paired gain and its variance stay fixed. No undefined risk subtraction or
assumed conditional-moment identity is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LossExplainabilitySeparation

open MeasureTheory ProbabilityTheory PairedGainTailExperiment Filter
open scoped Topology

/-- The information revealed by the binary context, before observing the noise atom. -/
def contextSigma : MeasurableSpace (Bool × Fin 3) :=
  (inferInstance : MeasurableSpace Bool).comap Prod.fst

/-- Conditional expectation under this product experiment is actual noise integration. -/
theorem conditional_context (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : Bool × Fin 3 → ℝ) :
    (fun z ↦ ∫ n, f (z.1, n) ∂noiseLaw p) =ᵐ[jointLaw p]
      (jointLaw p)[f | contextSigma] := by
  letI := context_probability
  letI := noise_probability p hp
  letI := joint_probability p hp
  have hm : contextSigma ≤ (inferInstance : MeasurableSpace (Bool × Fin 3)) :=
    measurable_fst.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq hm Integrable.of_finite
  · intro s _ _
    exact Integrable.of_finite.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have ht' : MeasurableSet (Prod.fst ⁻¹' t : Set (Bool × Fin 3)) :=
      measurable_fst ht
    rw [← integral_indicator ht', ← integral_indicator ht']
    rw [jointLaw, integral_prod _ Integrable.of_finite, integral_prod _ Integrable.of_finite]
    apply integral_congr_ae
    filter_upwards [] with w
    change (∫ n, (Prod.fst ⁻¹' t).indicator
      (fun z : Bool × Fin 3 ↦ ∫ v, f (z.1, v) ∂noiseLaw p) (w, n) ∂noiseLaw p) =
      ∫ n, (Prod.fst ⁻¹' t).indicator f (w, n) ∂noiseLaw p
    by_cases hw : w ∈ t
    · simp [Set.indicator, hw]
    · simp [Set.indicator, hw]
  · have hfst : @Measurable (Bool × Fin 3) Bool contextSigma inferInstance Prod.fst :=
      measurable_iff_comap_le.mpr le_rfl
    have hg := (measurable_of_countable (fun w ↦ ∫ n, f (w, n) ∂noiseLaw p)).comp hfst
    exact hg.stronglyMeasurable.aestronglyMeasurable

/-- The explicit baseline-loss predictor is the genuine context conditional expectation. -/
theorem loss_conditional_expectation (p a : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (fun z : Bool × Fin 3 ↦ correction z.1 ^ 2 + p * a ^ 2) =ᵐ[jointLaw p]
      (jointLaw p)[loss a | contextSigma] := by
  simpa only [conditional_loss p a hp] using conditional_context p hp (loss a)

/-- Exactly one unit of squared-loss variance is predictable from the context. -/
theorem predictable_variance (p a : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    Var[(jointLaw p)[loss a | contextSigma]; jointLaw p] = 1 := by
  letI := joint_probability p hp
  rw [← variance_congr (loss_conditional_expectation p a hp),
    variance_eq_sub (joint_memLp p hp _)]
  simp only [Pi.pow_apply, joint_integral p hp, correction, Bool.false_eq_true, ↓reduceIte]
  ring

/-- The actual explained fraction, with its actual conditional expectation in the numerator. -/
noncomputable def explainedFraction (p : ℝ) : ℝ :=
  Var[(jointLaw p)[loss (Real.sqrt p)⁻¹ | contextSigma]; jointLaw p] /
    Var[loss (Real.sqrt p)⁻¹; jointLaw p]

/-- The exact fraction is one over five plus the reciprocal rare-event probability. -/
theorem explained_fraction (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    explainedFraction p = 1 / (5 + 1 / p) := by
  rw [explainedFraction, predictable_variance p _ ⟨hp.1.le, hp.2⟩,
    (exact_moment_packet p hp).1]

/-- A nonsingular expression exposes the limit at zero without extending the experiment there. -/
theorem explained_fraction_continuous_form (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    explainedFraction p = p / (5 * p + 1) := by
  rw [explained_fraction p hp]
  field_simp [hp.1.ne']

/-- Individual-loss explainability tends to zero through valid positive experiment parameters. -/
theorem explained_fraction_tendsto_zero :
    Tendsto explainedFraction (𝓝[Set.Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
  have ht : Tendsto (fun p : ℝ ↦ p / (5 * p + 1)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun p : ℝ ↦ p / (5 * p + 1)) 0 := by
      apply ContinuousAt.div continuousAt_id
      · fun_prop
      · norm_num
    simpa using hc.tendsto
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (explained_fraction_continuous_form p hp).symm

/-- The complete theorem packet keeps the useful repair and comparison variance fixed. -/
theorem separation (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    IsProbabilityMeasure (jointLaw p) ∧
    explainedFraction p = 1 / (5 + 1 / p) ∧
    (∫ z, improvement (Real.sqrt p)⁻¹ z ∂jointLaw p) = 5 / 4 ∧
    Var[improvement (Real.sqrt p)⁻¹; jointLaw p] = 6 := by
  exact ⟨joint_probability p ⟨hp.1.le, hp.2⟩, explained_fraction p hp,
    (exact_moment_packet p hp).2⟩

end Descent.Portability.LossExplainabilitySeparation
