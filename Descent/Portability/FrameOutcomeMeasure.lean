/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMixtureRepair

assert_below Descent.Decision Descent.Program

/-!
An actual joint probability law for a weighted target frame and its outcome
kernels. A draw chooses a frame row and then draws its outcome. Integrals of
squared prediction loss agree exactly with the frame-risk sums used by the
repair theory, so subgroup mixture transport applies to those actual risks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FrameOutcomeMeasure

open MeasureTheory DecisionLossContrasts FiniteMixtureRepair
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The joint law that fixes one target row and samples its actual outcome kernel. -/
noncomputable def rowLaw (μ : ι → Measure ℝ) (i : ι) : Measure (ι × ℝ) :=
  (μ i).map (fun y ↦ (i, y))

/-- The joint law of a weighted target row and its phenotype. -/
noncomputable def frameLaw (μ : ι → Measure ℝ) (w : ι → ℝ) : Measure (ι × ℝ) :=
  mixture w (rowLaw μ)

/-- Pointwise squared prediction loss on the joint row-outcome space. -/
noncomputable def loss (f : ι → ℝ) (z : ι × ℝ) : ℝ := (z.2 - f z.1) ^ 2

/-- Fixing the frame row preserves the outcome kernel's probability normalization. -/
theorem row_probability (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    IsProbabilityMeasure (rowLaw μ i) := by
  constructor
  rw [rowLaw, Measure.map_apply (measurable_const.prodMk measurable_id) MeasurableSet.univ]
  simp

/-- Nonnegative normalized target weights define a genuine joint probability law. -/
theorem frame_probability (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    IsProbabilityMeasure (frameLaw μ w) := by
  letI (i : ι) := row_probability μ i
  exact mixture_probability w (rowLaw μ) hw hsum

/-- Every fixed frame prediction has a measurable loss function. -/
theorem loss_measurable (f : ι → ℝ) : Measurable (loss f) := by
  have hf : Measurable f := measurable_of_countable f
  exact (measurable_snd.sub (hf.comp measurable_fst)).pow_const 2

/-- The row-conditional squared loss is integrable from an actual phenotype second moment. -/
theorem row_loss_integrable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) (i : ι) :
    Integrable (loss f) (rowLaw μ i) := by
  apply (integrable_map_measure (loss_measurable f).aestronglyMeasurable
    (measurable_const.prodMk measurable_id).aemeasurable).mpr
  exact ((hY i).sub (memLp_const (f i))).integrable_sq

/-- Both weighted-frame risk and joint-law risk are finite for square-integrable outcomes. -/
theorem frame_loss_integrable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    Integrable (loss f) (frameLaw μ w) :=
  mixture_integrable w (rowLaw μ) (loss f) (row_loss_integrable μ f hY)

/-- The actual joint-law expected loss is exactly the frame-risk expression. -/
theorem expected_loss (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    (∫ z, loss f z ∂frameLaw μ w) = frameRisk μ w f := by
  rw [frameLaw, mixture_integral w (rowLaw μ) (loss f) hw (row_loss_integrable μ f hY)]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowLaw, integral_map (measurable_const.prodMk measurable_id).aemeasurable
    (loss_measurable f).aestronglyMeasurable]
  rfl

/-- The joint-law paired gain agrees with the two separate actual weighted-frame risks. -/
theorem expected_gain (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (w f d : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hY : ∀ i, MemLp (fun y : ℝ ↦ y) 2 (μ i)) :
    FiniteMixtureRepair.gain (frameLaw μ w) Prod.snd (fun z ↦ f z.1) (fun z ↦ d z.1) =
      frameRisk μ w f - frameRisk μ w (fun i ↦ f i + d i) := by
  change (∫ z, loss f z ∂frameLaw μ w) -
    (∫ z, loss (fun i ↦ f i + d i) z ∂frameLaw μ w) = _
  rw [expected_loss μ w f hw hY, expected_loss μ w (fun i ↦ f i + d i) hw hY]

end Descent.Portability.FrameOutcomeMeasure
