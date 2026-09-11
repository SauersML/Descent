/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RademacherParityConditioning

assert_below Descent.Decision Descent.Program

/-!
Conditioning an infinitesimal weighted fair-sign row on either product sign has
the same Gaussian weak limit. This proves the conditional form of asymptotic
parity independence, including zero limiting variance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RademacherParityWeakLimit

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory HWEInteractionLaw BalancedHWEWeakLimit
open RademacherArrayWeakLimit RademacherParityLaw RademacherParityConditioning
open FiniteAtomicReportMeasure SecondMomentTightness TightCharacteristicConvergence

/-- A nonempty row conditioned on its realized product sign. -/
noncomputable def conditionalProbability (m : ℕ) (a : Fin (m + 1) → ℝ)
    (b : Bool) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (law b) (weightedSum a), inferInstance⟩

/-- The exact restriction bound supplies tightness for both conditional experiments. -/
theorem conditional_rows_tight (a : (m : ℕ) → Fin m → ℝ) (s : ℝ)
    (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 s)) (b : Bool) :
    IsTightMeasureSet (Set.range (fun m ↦
      (conditionalProbability m (a (m + 1)) b : Measure ℝ))) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hs).exists_norm_le
  apply tight_of_second_moment_bound (fun m ↦ conditionalProbability m (a (m + 1)) b)
    (2 * max 0 B) (by positivity)
  · intro m
    exact finite_report_integrable _ _ _
  · intro m
    change (∫ x : ℝ, x ^ 2 ∂finiteMeasure (law b) (weightedSum (a (m + 1)))) ≤ _
    rw [integral_finite_report]
    apply (second_moment_bound b (a (m + 1))).trans
    have hh := ((le_abs_self _).trans (hB _ ⟨m + 1, rfl⟩)).trans (le_max_right 0 B)
    linarith

/-- Either conditional parity class has the full Gaussian limit of the unconditioned row. -/
theorem conditional_gaussian_limit (a : (m : ℕ) → Fin m → ℝ) (ε : ℕ → ℝ)
    (ha : ∀ m i, |a m i| ≤ ε m) (hε : Tendsto ε atTop (𝓝 0)) (s : ℝ≥0)
    (hs : Tendsto (fun m ↦ ∑ i, a m i ^ 2) atTop (𝓝 (s : ℝ))) (b : Bool) :
    Tendsto (fun m ↦ conditionalProbability m (a (m + 1)) b) atTop
      (𝓝 (centeredGaussian s)) := by
  apply weak_convergence_of_tight_characteristic _ (centeredGaussian s)
  · have ht := (isTightMeasureSet_singleton (μ := (centeredGaussian s : Measure ℝ))).union
      (conditional_rows_tight a s hs b)
    simpa only [Set.singleton_union] using ht
  · intro t
    have hg : charFun (gaussianReal 0 s) t = (Real.exp (-(t ^ 2 * (s : ℝ) / 2)) : ℂ) := by
      rw [charFun_gaussianReal]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
        Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_mul]
      congr 1
      ring
    have hu : Tendsto (fun m ↦ complexExpectation (independentLaw (fun _ : Fin m ↦ signLaw))
        (fun x ↦ Complex.exp ((t * weightedSum (a m) x : ℝ) * Complex.I))) atTop
        (𝓝 (Real.exp (-(t ^ 2 * (s : ℝ) / 2)) : ℂ)) := by
      simpa only [row_characteristic] using
        (CosineArrayLimit.cosine_product_limit a ε ha hε s hs t).ofReal
    have hm := (mixed_characteristic_limit a ε ha hε t).const_mul (signValue b : ℂ)
    have hc := (hu.add hm).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun m ↦ charFun (finiteMeasure (law b) (weightedSum (a (m + 1)))) t)
      atTop (𝓝 (charFun (gaussianReal 0 s) t))
    rw [hg]
    simpa only [charFun_finite_report, complexExpectation_law, Function.comp_def,
      mul_zero, add_zero] using hc

end Descent.Portability.RademacherParityWeakLimit
