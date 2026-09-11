/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAmplitudeMixture

assert_below Descent.Decision Descent.Program

/-!
The derived square-biased amplitude mixture is constructed as an actual probability
measure. Its bounded-test characterization is upgraded to weak convergence of the
original genotype experiment's probability measures, including the balanced K=0 case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEAmplitudeWeakLimit

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw
open HWEHomozygoteLimit HWEAmplitudeMixture BalancedHWEWeakLimit RademacherArrayWeakLimit

/-- Convex combination of two actual real probability measures. -/
noncomputable def blend (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (μ ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal (1 - w) • (μ : Measure ℝ) + ENNReal.ofReal w • (ν : Measure ℝ), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hw1) hw0]
    simp⟩

/-- Exact integral of a bounded test under the convex mixture. -/
theorem integral_blend (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (μ ν : ProbabilityMeasure ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(blend w hw0 hw1 μ ν : Measure ℝ)) =
      (1 - w) * (∫ x, f x ∂(μ : Measure ℝ)) + w * (∫ x, f x ∂(ν : Measure ℝ)) := by
  change (∫ x, f x ∂(ENNReal.ofReal (1 - w) • (μ : Measure ℝ) +
    ENNReal.ofReal w • (ν : Measure ℝ))) = _
  rw [integral_add_measure
    ((f.integrable (μ : Measure ℝ)).smul_measure ENNReal.ofReal_ne_top)
    ((f.integrable (ν : Measure ℝ)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr hw1),
    ENNReal.toReal_ofReal hw0, smul_eq_mul]

/-- A scaled lognormal law as the actual continuous image of N(0,4K). -/
noncomputable def lognormal (K : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  (centeredGaussian (4 * K)).map
    (show AEMeasurable (fun x : ℝ ↦ c * Real.exp (-x)) _ by fun_prop)

theorem integral_lognormal (K : ℝ≥0) (c : ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(lognormal K c : Measure ℝ)) =
      ∫ x, f (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K) := by
  change (∫ x, f x ∂Measure.map (fun x : ℝ ↦ c * Real.exp (-x))
    (gaussianReal 0 (4 * K))) = _
  exact integral_map (by fun_prop) f.continuous.aestronglyMeasurable

/-- Fair signed lognormal component, including its degenerate balanced case. -/
noncomputable def signedLognormal (K : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  blend (1 / 2) (by norm_num) (by norm_num) (lognormal K c) (lognormal K (-c))

theorem weight_bounds (K : ℝ≥0) :
    0 ≤ Real.exp (-4 * (K : ℝ)) ∧ Real.exp (-4 * (K : ℝ)) ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) K.coe_nonneg

/-- The complete tilted amplitude limit: atom at zero plus the signed lognormal law. -/
noncomputable def amplitudeLimit (K : ℝ≥0) (c : ℝ) : ProbabilityMeasure ℝ :=
  blend (Real.exp (-4 * (K : ℝ))) (weight_bounds K).1 (weight_bounds K).2
    ⟨Measure.dirac 0, inferInstance⟩ (signedLognormal K c)

/-- Its integral is exactly the previously derived bounded-test limit. -/
theorem integral_amplitudeLimit (K : ℝ≥0) (c : ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(amplitudeLimit K c : Measure ℝ)) =
      (1 - Real.exp (-4 * (K : ℝ))) * f 0 + Real.exp (-4 * (K : ℝ)) *
        (((∫ x, f (c * Real.exp (-x)) ∂gaussianReal 0 (4 * K)) +
        (∫ x, f (-c * Real.exp (-x)) ∂gaussianReal 0 (4 * K))) / 2) := by
  simp only [amplitudeLimit, signedLognormal, integral_blend, ProbabilityMeasure.coe_mk,
    integral_dirac,
    integral_lognormal]
  ring

/-- The actual finite-genotype amplitude distribution. -/
noncomputable def amplitudeProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (c : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i)))
    (fun x ↦ c * normalized h x), inferInstance⟩

/-- Weak convergence of the original square-biased HWE genotype amplitude laws. -/
theorem amplitude_weak_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (c : ℝ) :
    Tendsto (fun m ↦ amplitudeProbability (h (m + 1)) (h0 (m + 1)) (h1 (m + 1)) c)
      atTop (𝓝 (amplitudeLimit K c)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun m ↦ ∫ x, f x ∂finiteMeasure
    (independentLaw (fun i ↦ squareBiasedLocus (h (m + 1) i)
      (h0 (m + 1) i) (h1 (m + 1) i))) (fun x ↦ c * normalized (h (m + 1)) x))
    atTop (𝓝 (∫ x, f x ∂(amplitudeLimit K c : Measure ℝ)))
  simp only [integral_finiteMeasure, integral_amplitudeLimit]
  exact amplitude_mixture_limit h h0 h1 ε hcap hε K hK f c

end Descent.Portability.HWEAmplitudeWeakLimit
