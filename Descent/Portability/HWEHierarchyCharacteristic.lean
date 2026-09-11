/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHierarchyGenerator
import Descent.Portability.HWECriticalScoreCharacteristic

assert_below Descent.Decision Descent.Program

/-!
The original HWE score characteristic limit at every polynomial adjustment of
critical block intensity. Divergence of the actual number of blocks follows
from the stated scaling, and the finite square-bias identity supplies the
independent-array generator directly from the original genotype experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHierarchyCharacteristic

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw
open HWEPolynomialLayerScale HWEHierarchyGenerator HWEKernelTruncation
open HWECriticalGenerator HWECriticalScoreCharacteristic

/-- Exponential growth dominates any real polynomial adjustment. -/
theorem exponential_adjustment_diverges (α : ℝ) :
    Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m / (m : ℝ) ^ α) atTop atTop := by
  have hh := (tendsto_exp_mul_div_rpow_atTop α (Real.log 2)
    (Real.log_pos (by norm_num))).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hh.congr'
  filter_upwards with m
  simp only [Function.comp_def, mul_comm (Real.log 2) (m : ℝ), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The report's positive polynomially adjusted intensity forces actual block counts to infinity. -/
theorem polynomial_block_count_diverges (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) :
    Tendsto (fun m : ℕ ↦ (N m : ℝ)) atTop atTop := by
  apply (hN.pos_mul_atTop hC (exponential_adjustment_diverges α)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hp : (m : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hm) α).ne'
  have htwo : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  dsimp only [adjustedIntensity, HWECriticalAmplitudeLimit.intensity]
  field_simp

/-- The original centered summand has the complete derived count-layer generator. -/
theorem original_generator_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (t : ℝ) :
    Tendsto (fun m : ℕ ↦ (N (m + 1) : ℂ) *
      (complexExpectation (blockLaw (fun _ : Fin (m + 1) ↦ h (m + 1)))
        (fun x ↦ Complex.exp ((t * summand (fun _ : Fin (m + 1) ↦ h (m + 1))
          (N (m + 1)) x : ℝ) * Complex.I)) - 1)) atTop
            (𝓝 (seriesGenerator κ α C t)) := by
  have hh := (full_generator_limit h h0 h1 κ hκ hf N α C hC hN t).comp
    (tendsto_add_atTop_nat 1)
  apply hh.congr'
  filter_upwards [((polynomial_block_count_diverges N α C hC hN).comp
    (tendsto_add_atTop_nat 1)).eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  change (0 : ℝ) < (N (m + 1) : ℝ) at hm
  exact finite_generator _ (fun _ ↦ h0 _) (fun _ ↦ h1 _) _ (by exact_mod_cast hm) t

/-- Full characteristic convergence for the actual sampled HWE score under hierarchy scaling. -/
theorem hierarchy_characteristic_limit (h : ℕ → HardyWeinbergModel)
    (h0 : ∀ m, 0 < (h m).altFreq) (h1 : ∀ m, (h m).altFreq < 1) (κ : ℝ) (hκ : κ ≠ 0)
    (hf : ∀ᶠ m in atTop, (h m).altFreq - 1 / 2 = κ / Real.sqrt (m : ℝ))
    (N : ℕ → ℕ) (α C : ℝ) (hC : 0 < C)
    (hN : Tendsto (fun m : ℕ ↦ adjustedIntensity m (N m) α) atTop (𝓝 C)) (t : ℝ) :
    Tendsto (fun m : ℕ ↦ charFun
      (scoreProbability (fun _ : Fin (m + 1) ↦ h (m + 1)) (N (m + 1)) : Measure ℝ) t)
        atTop (𝓝 (Complex.exp (seriesGenerator κ α C t))) := by
  have hh := ComplexArrayPowerLimit.power_limit (fun m ↦ N (m + 1))
    ((polynomial_block_count_diverges N α C hC hN).comp (tendsto_add_atTop_nat 1)) _ _
    (original_generator_limit h h0 h1 κ hκ hf N α C hC hN t)
  simpa only [score_characteristic] using hh

end Descent.Portability.HWEHierarchyCharacteristic
