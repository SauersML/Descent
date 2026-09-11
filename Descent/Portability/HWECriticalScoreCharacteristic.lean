/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWECriticalGenerator
import Descent.Portability.ComplexArrayPowerLimit

assert_below Descent.Decision Descent.Program

/-!
The original score is the sum of independently sampled HWE interaction blocks,
normalized by sqrt(N). Its characteristic function converges to the exponential
of the generator derived from the actual square-biased critical amplitude law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWECriticalScoreCharacteristic

open scoped BigOperators Topology NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw BalancedHWEWeakLimit
open HWECriticalAmplitudeLimit HWECriticalGenerator HWEAmplitudeWeakLimit
open CompensatedCharacteristicKernel FiniteAtomicReportMeasure FiniteIndependentMoments

/-- The original sum of N disjoint independently generated standardized HWE blocks. -/
noncomputable def score {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (N : ℕ) (x : Fin N → ι → DiploidGenotype) : ℝ :=
  ∑ j, summand h N (x j)

/-- Actual genotype sampling law of the normalized independent-block score. -/
noncomputable def scoreProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (N : ℕ) : ProbabilityMeasure ℝ :=
  ⟨finiteMeasure (independentLaw (fun _ : Fin N ↦ blockLaw h)) (score h N), inferInstance⟩

/-- Exact independent-block characteristic factorization. -/
theorem score_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel) (N : ℕ) (t : ℝ) :
    charFun (scoreProbability h N : Measure ℝ) t =
      (complexExpectation (blockLaw h)
        (fun x ↦ Complex.exp ((t * summand h N x : ℝ) * Complex.I))) ^ N := by
  rw [scoreProbability, ProbabilityMeasure.coe_mk, charFun_finite_report]
  change complexExpectation (independentLaw (fun _ : Fin N ↦ blockLaw h))
    (fun x ↦ Complex.exp ((t * ∑ j, summand h N (x j) : ℝ) * Complex.I)) = _
  rw [characteristic_independent_sum (fun _ : Fin N ↦ blockLaw h) (fun _ ↦ summand h N) t]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Every finite original score is centered. -/
theorem score_mean {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → HardyWeinbergModel) (N : ℕ) :
    (independentLaw (fun _ : Fin N ↦ blockLaw h)).expectation (score h N) = 0 := by
  unfold score
  rw [independent_sum_mean]
  simp only [summand_centered, Finset.sum_const_zero]

/-- Every nonempty normalized original score has exactly unit second moment. -/
theorem score_second {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (N : ℕ) (hN : 0 < N) :
    (independentLaw (fun _ : Fin N ↦ blockLaw h)).expectation
      (fun x ↦ score h N x ^ 2) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : (blockLaw h).expectation (fun x ↦ summand h N x ^ 2) = 1 / (N : ℝ) := by
    have he : (blockLaw h).expectation (fun x ↦ summand h N x ^ 2) =
        (blockLaw h).expectation (fun x ↦ interaction h x ^ 2) / (N : ℝ) := by
      simp only [FiniteReportLaw.expectation, summand, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg N), Finset.sum_div, mul_div_assoc]
    rw [he, interaction_second_moment h h0 h1]
  unfold score
  rw [independent_sum_second _ _ (fun _ ↦ summand_centered h N)]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_one_div_cancel hn

/-- The actual independent HWE score has the derived critical characteristic limit. -/
theorem score_characteristic_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ≥0)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 (K : ℝ)))
    (N : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hN : Tendsto (fun m ↦ intensity m (N m)) atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun m ↦ charFun (scoreProbability (h (m + 1)) (N (m + 1)) : Measure ℝ) t)
      atTop (𝓝 (Complex.exp
        (∫ y, kernel t y ∂(amplitudeLimit K (1 / Real.sqrt r) : Measure ℝ)))) := by
  have hh := ComplexArrayPowerLimit.power_limit (fun m ↦ N (m + 1))
    ((block_count_diverges N r hr hN).comp (tendsto_add_atTop_nat 1)) _ _
    (generator_limit h h0 h1 ε hcap hε K hK N r hr hN t)
  simpa only [score_characteristic] using hh

end Descent.Portability.HWECriticalScoreCharacteristic
