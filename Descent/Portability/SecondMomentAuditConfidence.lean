/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.VectorAuditConfidence
import Descent.Portability.AuditCovarianceSpectrum
import Mathlib.Analysis.InnerProductSpace.Trace

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 24. The independent augmented audit
has an exactly computed mean squared vector error. Actual residual second
moments bound its covariance trace and give a Markov confidence ball. No
bounded support, fourth moment, or assumed concentration inequality is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SecondMomentAuditConfidence

open MeasureTheory ProbabilityTheory AugmentedAuditLaw SharedAuditCompletion
open IndependentContrastLaw VectorAuditConfidence
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The audit variance can be written using the residual second moment alone. -/
theorem audit_variance_residual (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : MemLp (fun y : ℝ ↦ y) 2 μ) :
    Var[fun y : ℝ ↦ y; auditLaw μ p q] =
      (∫ y, (y - q) ^ 2 ∂μ) / p - ((∫ y, y ∂μ) - q) ^ 2 := by
  have he := affine_second μ 1 (-q) hY
  simp only [one_mul, one_pow, ← sub_eq_add_neg] at he
  rw [audit_variance μ p q hp hY, variance_eq_sub hY, he]
  simp only [Pi.pow_apply]
  field_simp [hp.1.ne']
  ring

/-- A genuine residual second-moment bound controls the prospective audit variance. -/
theorem audit_variance_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (p q e : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hY : MemLp (fun y : ℝ ↦ y) 2 μ)
    (he : (∫ y, (y - q) ^ 2 ∂μ) ≤ e ^ 2) :
    Var[fun y : ℝ ↦ y; auditLaw μ p q] ≤ e ^ 2 / p := by
  rw [audit_variance_residual μ p q hp hY]
  exact (sub_le_self _ (sq_nonneg _)).trans (div_le_div_of_nonneg_right he hp.1.le)

/-- Parseval's identity in the real coordinates used by the audit. -/
theorem coordinates_sq {α : Type*} [Fintype α] (b : OrthonormalBasis α ℝ E) (v : E) :
    (∑ j, (inner ℝ (b j) v) ^ 2) = ‖v‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right v

/-- Every directional estimation error has a finite second moment. -/
theorem direction_memLp (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (u : ι → E) (a : E) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    MemLp (fun z ↦ inner ℝ a (error μ u z)) 2 (frameLaw μ p q) := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  have hc := contrast_memLp (fun i ↦ auditLaw (μ i) (p i) (q i))
    (fun i ↦ audit_memLp (μ i) (p i) (q i) (hY i)) (fun i ↦ inner ℝ a (u i))
  simpa only [directional_error, Pi.sub_apply] using
    hc.sub (memLp_const (∑ i, inner ℝ a (u i) * ∫ y, y ∂μ i))

/-- The directional second moment is the actual contrast variance. -/
theorem direction_second (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (u : ι → E) (a : E) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    (∫ z, (inner ℝ a (error μ u z)) ^ 2 ∂frameLaw μ p q) =
      ∑ i, (inner ℝ a (u i)) ^ 2 * Var[fun y : ℝ ↦ y; auditLaw (μ i) (p i) (q i)] := by
  letI (i : ι) := auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  have hc := contrast_memLp (fun i ↦ auditLaw (μ i) (p i) (q i))
    (fun i ↦ audit_memLp (μ i) (p i) (q i) (hY i)) (fun i ↦ inner ℝ a (u i))
  have hv := variance_eq_integral hc.aemeasurable
  change Var[contrast (fun i ↦ inner ℝ a (u i)); frameLaw μ p q] =
    ∫ z, (contrast (fun i ↦ inner ℝ a (u i)) z -
      ∫ x, contrast (fun i ↦ inner ℝ a (u i)) x ∂frameLaw μ p q) ^ 2 ∂frameLaw μ p q at hv
  rw [frame_contrast_mean μ p q _ hp hY] at hv
  simp only [directional_error]
  rw [← hv]
  exact contrast_variance _ (fun i ↦ audit_memLp (μ i) (p i) (q i) (hY i)) _

/-- The actual squared vector error is integrable, even for unbounded outcomes. -/
theorem error_sq_integrable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (u : ι → E) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    Integrable (fun z ↦ ‖error μ u z‖ ^ 2) (frameLaw μ p q) := by
  let b := stdOrthonormalBasis ℝ E
  have he : (fun z ↦ ‖error μ u z‖ ^ 2) =
      fun z ↦ ∑ j, (inner ℝ (b j) (error μ u z)) ^ 2 := by
    funext z
    exact (coordinates_sq b _).symm
  rw [he]
  exact integrable_finset_sum _ (fun j _ ↦ (direction_memLp μ p q u (b j) hp hY).integrable_sq)

/-- The complete vector mean squared error is the exact covariance trace. -/
theorem error_second (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : ι → ℝ) (u : ι → E) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    (∫ z, ‖error μ u z‖ ^ 2 ∂frameLaw μ p q) =
      ∑ i, Var[fun y : ℝ ↦ y; auditLaw (μ i) (p i) (q i)] * ‖u i‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  have he : (fun z ↦ ‖error μ u z‖ ^ 2) =
      fun z ↦ ∑ j, (inner ℝ (b j) (error μ u z)) ^ 2 := by
    funext z
    exact (coordinates_sq b _).symm
  rw [he, integral_finset_sum]
  · simp only [direction_second μ p q u _ hp hY]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, coordinates_sq b (u i), mul_comm]
  · intro j _
    exact (direction_memLp μ p q u (b j) hp hY).integrable_sq

/-- The computable covariance trace envelope; coefficients include normalization and whitening. -/
noncomputable def traceBound (p e : ι → ℝ) (u : ι → E) : ℝ :=
  ∑ i, e i ^ 2 / p i * ‖u i‖ ^ 2

/-- This envelope is literally the trace of the stated sum of outer products. -/
theorem covariance_trace (p e : ι → ℝ) (u : ι → E) :
    LinearMap.trace ℝ E (AuditCovarianceSpectrum.covariance (fun i ↦ e i ^ 2 / p i) u) =
      traceBound p e u := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [AuditCovarianceSpectrum.quadratic]
  rw [Finset.sum_comm]
  unfold traceBound
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, coordinates_sq b (u i)]

/-- Residual moment bounds imply the trace bound for the actual joint audit error. -/
theorem error_second_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q e : ι → ℝ) (u : ι → E) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (he : ∀ i, (∫ y, (y - q i) ^ 2 ∂μ i) ≤ e i ^ 2) :
    (∫ z, ‖error μ u z‖ ^ 2 ∂frameLaw μ p q) ≤ traceBound p e u := by
  rw [error_second μ p q u hp hY]
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right
    (audit_variance_le (μ i) (p i) (q i) (e i) (hp i) (hY i) (he i)) (sq_nonneg _))

/-- Markov confidence with the variance-zero case retained. -/
theorem norm_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → E) (T δ : ℝ) (hδ : 0 < δ)
    (hi : Integrable (fun z ↦ ‖f z‖ ^ 2) μ) (hT : (∫ z, ‖f z‖ ^ 2 ∂μ) ≤ T) :
    μ.real {z | Real.sqrt (T / δ) < ‖f z‖} ≤ δ := by
  have hT₀ : 0 ≤ T := (integral_nonneg (fun z ↦ sq_nonneg ‖f z‖)).trans hT
  rcases eq_or_lt_of_le hT₀ with hzero | hpos
  · subst T
    have hz := (integral_eq_zero_iff_of_nonneg (fun z ↦ sq_nonneg ‖f z‖) hi).mp
      (le_antisymm hT (integral_nonneg (fun z ↦ sq_nonneg ‖f z‖)))
    have hempty : {z | Real.sqrt (0 / δ) < ‖f z‖} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with z hz
      have hn : ‖f z‖ = 0 := sq_eq_zero_iff.mp hz
      apply propext
      change (Real.sqrt (0 / δ) < ‖f z‖) ↔ False
      simp [hn]
    rw [measureReal_congr hempty, measureReal_empty]
    exact hδ.le
  · have hm := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun z ↦ sq_nonneg ‖f z‖)) hi (T / δ)
    have htail : μ.real {z | T / δ ≤ ‖f z‖ ^ 2} ≤ δ := by
      have hd : 0 < T / δ := div_pos hpos hδ
      have he : T / δ * δ = T := div_mul_cancel₀ _ hδ.ne'
      nlinarith
    apply (measureReal_mono (show {z | Real.sqrt (T / δ) < ‖f z‖} ⊆
      {z | T / δ ≤ ‖f z‖ ^ 2} from ?_)).trans htail
    intro z hz
    change Real.sqrt (T / δ) < ‖f z‖ at hz
    change T / δ ≤ ‖f z‖ ^ 2
    have hs := Real.sq_sqrt (div_nonneg hT₀ hδ.le)
    nlinarith [Real.sqrt_nonneg (T / δ), norm_nonneg (f z)]

/-- The actual independent audit has a uniform confidence ball using only second moments. -/
theorem confidence (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p q e : ι → ℝ) (u : ι → E) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i))
    (he : ∀ i, (∫ y, (y - q i) ^ 2 ∂μ i) ≤ e i ^ 2) :
    (frameLaw μ p q).real {z | Real.sqrt (traceBound p e u / δ) < ‖error μ u z‖} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  exact norm_markov (frameLaw μ p q) (error μ u) _ δ hδ
    (error_sq_integrable μ p q u hp hY) (error_second_le μ p q e u hp hY he)

end Descent.Portability.SecondMomentAuditConfidence
