/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAbsoluteMomentLimit
import Descent.Portability.FiniteL1WeakStability

assert_below Descent.Decision Descent.Program

/-!
The actual square-biased block interaction divided by sqrt(N) has the stated
critical-window amplitude limit when N/2^m tends to a positive finite intensity.
The varying normalization is handled through a proved L1 stability theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWECriticalAmplitudeLimit

open scoped BigOperators Topology NNReal
open Filter MeasureTheory Foundations HWEInteractionLaw BalancedHWEWeakLimit
open HWEHomozygoteLimit HWEAmplitudeWeakLimit HWEAbsoluteMomentLimit FiniteL1WeakStability

/-- Critical interaction intensity, exactly N times the balanced nonzero probability. -/
noncomputable def intensity (m N : ℕ) : ℝ := (N : ℝ) / 2 ^ m

/-- Exact square-root normalization of the balanced block magnitude. -/
theorem sqrt_two_pow (m : ℕ) : Real.sqrt ((2 : ℝ) ^ m) = Real.sqrt 2 ^ m := by
  have he : (Real.sqrt 2 ^ m) ^ 2 = (2 : ℝ) ^ m := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← he, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]

/-- The exact critical scaling identity for the original genotype interaction. -/
theorem scaling_identity (m N : ℕ) (h : Fin m → HardyWeinbergModel)
    (x : Fin m → DiploidGenotype) :
    interaction h x / Real.sqrt (N : ℝ) =
      (1 / Real.sqrt (intensity m N)) * normalized h x := by
  have hd : Real.sqrt 2 ^ m ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [intensity, Real.sqrt_div (Nat.cast_nonneg N), sqrt_two_pow, one_div_div,
    normalized, Fintype.card_fin]
  symm
  calc
    _ = (interaction h x * Real.sqrt 2 ^ m) / (Real.sqrt (N : ℝ) * Real.sqrt 2 ^ m) := by
      ring
    _ = _ := mul_div_mul_right _ _ hd

/-- The actual square-biased distribution of a summand in the N-block normalized score. -/
noncomputable def criticalProbability (m N : ℕ) (h : Fin m → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    ProbabilityMeasure ℝ :=
  reportProbability (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i)))
    (fun x ↦ interaction h x / Real.sqrt (N : ℝ))

/-- The full square-biased critical-window amplitude law with the actual varying block count. -/
theorem critical_amplitude_weak_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (N : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hN : Tendsto (fun m ↦ intensity m (N m)) atTop (𝓝 r)) :
    Tendsto (fun m ↦ criticalProbability (m + 1) (N (m + 1)) (h (m + 1))
      (h0 (m + 1)) (h1 (m + 1))) atTop (𝓝 (amplitudeLimit K (1 / Real.sqrt r))) := by
  have ha : Tendsto (fun m ↦ 1 / Real.sqrt (intensity (m + 1) (N (m + 1)))) atTop
      (𝓝 (1 / Real.sqrt r)) := by
    exact tendsto_const_nhds.div
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (hN.comp (tendsto_add_atTop_nat 1))) (Real.sqrt_pos.mpr hr).ne'
  have hB := (absolute_moment_limit h h0 h1 ε hcap hε K hK).comp
    (tendsto_add_atTop_nat 1)
  have hz := amplitude_weak_limit h h0 h1 ε hcap hε K hK (1 / Real.sqrt r)
  have hc := varying_scale_limit
    (fun m ↦ independentLaw (fun i ↦ squareBiasedLocus (h (m + 1) i)
      (h0 (m + 1) i) (h1 (m + 1) i)))
    (fun m x ↦ normalized (h (m + 1)) x) _ _ ha _ hB _ hz
  simpa only [criticalProbability, scaling_identity] using hc

end Descent.Portability.HWECriticalAmplitudeLimit
