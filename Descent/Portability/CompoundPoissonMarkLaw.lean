/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PoissonRealCharacteristic
import Mathlib.MeasureTheory.Group.Convolution

assert_below Descent.Decision Descent.Program

/-!
A compound-Poisson distribution with arbitrary real probability marks is built
from the actual finite convolution laws and the normalized Poisson count law.
Its characteristic function is proved by summing the entire exponential series.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompoundPoissonMarkLaw

open scoped BigOperators NNReal MeasureTheory RealInnerProductSpace
open MeasureTheory ProbabilityTheory BoundedContinuousFunction

/-- The law of k independent marks added together. -/
noncomputable def markSum (μ : ProbabilityMeasure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => (μ : Measure ℝ) ∗ markSum μ k

instance markSum_probability (μ : ProbabilityMeasure ℝ) (k : ℕ) :
    IsProbabilityMeasure (markSum μ k) := by
  induction k with
  | zero => dsimp [markSum]; infer_instance
  | succ k ih =>
    letI := ih
    dsimp only [markSum]
    infer_instance

/-- Exact characteristic function of the independent finite mark sum. -/
theorem charFun_markSum (μ : ProbabilityMeasure ℝ) (k : ℕ) (t : ℝ) :
    charFun (markSum μ k) t = charFun (μ : Measure ℝ) t ^ k := by
  induction k with
  | zero => simp [markSum]
  | succ k ih => rw [markSum, charFun_conv, ih, pow_succ']

/-- The normalized count mixture defining a genuine compound-Poisson probability law. -/
noncomputable def compoundMeasure (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) : Measure ℝ :=
  Measure.sum (fun k : ℕ ↦ ENNReal.ofReal (poissonPMFReal r k) • markSum μ k)

instance compoundMeasure_probability (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) :
    IsProbabilityMeasure (compoundMeasure r μ) := by
  constructor
  simp only [compoundMeasure, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ poissonPMFReal_nonneg)
    (poissonPMFRealSum r).summable, (poissonPMFRealSum r).tsum_eq]
  exact ENNReal.ofReal_one

noncomputable def compoundProbability (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ := ⟨compoundMeasure r μ, inferInstance⟩

/-- The Poisson generating series at an arbitrary complex argument. -/
theorem poisson_generating_series (r : ℝ≥0) (z : ℂ) :
    HasSum (fun k : ℕ ↦ (poissonPMFReal r k : ℂ) * z ^ k)
      (Complex.exp ((r : ℂ) * (z - 1))) := by
  have hs : HasSum (fun k : ℕ ↦ ((r : ℂ) * z) ^ k / (k.factorial : ℂ))
      (Complex.exp ((r : ℂ) * z)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp ℂ _
  have hh := hs.mul_left (Complex.exp (-(r : ℂ)))
  convert hh using 1
  · funext k
    simp only [poissonPMFReal]
    push_cast
    rw [mul_pow]
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

/-- Characteristic function of the constructed arbitrary-mark compound-Poisson law. -/
theorem charFun_compoundMeasure (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (compoundMeasure r μ) t =
      Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
  have hi := (innerProbChar t).integrable (compoundMeasure r μ)
  rw [charFun_eq_integral_innerProbChar, compoundMeasure, integral_sum_measure hi]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal poissonPMFReal_nonneg,
    Complex.real_smul, ← charFun_eq_integral_innerProbChar, charFun_markSum]
  exact (poisson_generating_series r (charFun (μ : Measure ℝ) t)).tsum_eq

end Descent.Portability.CompoundPoissonMarkLaw
