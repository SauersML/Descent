/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWECriticalAmplitudeLimit
import Descent.Portability.FiniteSquareBiasCharacteristic

assert_below Descent.Decision Descent.Program

/-!
The original HWE block characteristic generator converges to the integral of the
compensated kernel against the derived critical amplitude mixture. Divergence of
the block count and the square-bias identity are derived from the actual inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWECriticalGenerator

open scoped BigOperators Topology NNReal BoundedContinuousFunction
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw BalancedHWEWeakLimit
open HWECriticalAmplitudeLimit HWEAmplitudeWeakLimit CompensatedCharacteristicKernel
open FiniteSquareBiasCharacteristic

/-- A positive finite critical intensity forces the number of blocks to diverge. -/
theorem block_count_diverges (N : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hN : Tendsto (fun m ↦ intensity m (N m)) atTop (𝓝 r)) :
    Tendsto (fun m ↦ (N m : ℝ)) atTop atTop := by
  have hp : Tendsto (fun m ↦ (2 : ℝ) ^ m) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
  have he (m : ℕ) : intensity m (N m) * (2 : ℝ) ^ m = (N m : ℝ) :=
    div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))
  simpa only [he] using hN.pos_mul_atTop hr hp

/-- The original normalized HWE summand, using the actual number of blocks. -/
noncomputable def summand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (N : ℕ) (x : ι → DiploidGenotype) : ℝ :=
  interaction h x / Real.sqrt (N : ℝ)

/-- Original centering is preserved by the actual row normalization. -/
theorem summand_centered {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → HardyWeinbergModel) (N : ℕ) : (blockLaw h).expectation (summand h N) = 0 := by
  have he : (blockLaw h).expectation (summand h N) =
      (blockLaw h).expectation (interaction h) / Real.sqrt (N : ℝ) := by
    simp only [FiniteReportLaw.expectation, summand, Finset.sum_div, mul_div_assoc]
  rw [he, interaction_mean_zero, zero_div]

/-- Square bias of the normalized summand is exactly the product of the tilted locus laws. -/
theorem actual_square_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (N : ℕ) (hN : 0 < N) (x : ι → DiploidGenotype) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).mass x =
      (N : ℝ) * (blockLaw h).mass x * summand h N x ^ 2 := by
  rw [squareBiasedBlock_mass, summand, div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Exact finite characteristic generator for the original HWE summand. -/
theorem finite_generator {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    complexExpectation (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i)))
      (fun x ↦ kernel t (summand h N x)) = (N : ℂ) *
        (complexExpectation (blockLaw h)
          (fun x ↦ Complex.exp ((t * summand h N x : ℝ) * Complex.I)) - 1) := by
  exact square_bias_identity _ _ _ N (actual_square_bias h h0 h1 N hN)
    (summand_centered h N) t

/-- The complex kernel integral is exactly its expectation under the finite genotype experiment. -/
theorem integral_critical_kernel (m N : ℕ) (h : Fin m → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (t : ℝ) :
    (∫ y, kernel t y ∂(criticalProbability m N h h0 h1 : Measure ℝ)) =
      complexExpectation (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i)))
        (fun x ↦ kernel t (summand h N x)) := by
  change (∫ y, kernel t y ∂finiteMeasure _ (summand h N)) = _
  have hi := (kernel t).integrable (finiteMeasure
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))) (summand h N))
  rw [finiteMeasure, integral_sum_measure hi]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
    (FiniteReportLaw.mass_nonneg _ _), Complex.real_smul, tsum_fintype, complexExpectation]

/-- The limiting characteristic generator is computed from the derived amplitude law. -/
theorem generator_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (N : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hN : Tendsto (fun m ↦ intensity m (N m)) atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun m ↦ (N (m + 1) : ℂ) *
      (complexExpectation (blockLaw (h (m + 1)))
        (fun x ↦ Complex.exp ((t * summand (h (m + 1)) (N (m + 1)) x : ℝ) *
          Complex.I)) - 1)) atTop
      (𝓝 (∫ y, kernel t y ∂(amplitudeLimit K (1 / Real.sqrt r) : Measure ℝ))) := by
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (critical_amplitude_weak_limit h h0 h1 ε hcap hε K hK N r hr hN) (kernel t)
  simp only [integral_critical_kernel] at hw
  apply hw.congr'
  filter_upwards [((block_count_diverges N r hr hN).comp
    (tendsto_add_atTop_nat 1)).eventually (eventually_gt_atTop (0 : ℝ))] with m hm
  change (0 : ℝ) < (N (m + 1) : ℝ) at hm
  exact finite_generator _ (h0 _) (h1 _) _ (by exact_mod_cast hm) t

end Descent.Portability.HWECriticalGenerator
