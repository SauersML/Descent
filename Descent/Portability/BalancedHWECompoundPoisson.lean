/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEFiniteIntensity

assert_below Descent.Decision Descent.Program

/-!
The finite positive-intensity phase of the balanced disjoint HWE experiment has
an actual compound-Poisson weak limit. Intensity determines the Poisson count;
the original variance normalization determines the symmetric jump size.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWECompoundPoisson

open scoped BigOperators BoundedContinuousFunction Topology ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory Foundations HWEInteractionLaw BalancedHWEInteraction
open IndependentShiftOperator BalancedHWEOperatorLimit BalancedHWEJumpOperator
open BalancedHWEWeakLimit BalancedHWEVanishingLaw BalancedHWEFiniteIntensity

noncomputable local instance : NormedRing Operator := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing Operator :=
  NonUnitalSeminormedRing.toIsTopologicalRing
local instance : SMul Operator Operator := ⟨(· * ·)⟩
local instance : IsScalarTower ℝ Operator Operator :=
  IsScalarTower.right (R := ℝ) (A := Operator)

/-- A fixed number of independent fair marks of amplitude a. -/
noncomputable def scaledWalk (a : ℝ) (k : ℕ) : Measure ℝ :=
  finiteMeasure (independentLaw (fun _ : Fin k ↦ signLaw))
    (fun signs ↦ ∑ j, a * signValue (signs j))

instance scaledWalk_probability (a : ℝ) (k : ℕ) : IsProbabilityMeasure (scaledWalk a k) := by
  dsimp only [scaledWalk]
  infer_instance

theorem sign_shift (a : ℝ) : shift signLaw (fun b ↦ a * signValue b) = fairJump a := by
  ext f x
  rw [shift_apply, fairJump_apply]
  simp [FiniteReportLaw.expectation, signLaw, signValue, sub_eq_add_neg]
  ring

theorem integral_scaledWalk (a : ℝ) (k : ℕ) (f : Observable) :
    ∫ x, f x ∂scaledWalk a k = (fairJump a ^ k) f 0 := by
  rw [scaledWalk, integral_finiteMeasure, ← sign_shift, shift_pow_sample]
  simp only [zero_add]

/-- Poisson(r) many independent fair amplitude-a marks. -/
noncomputable def compoundMeasure (r : ℝ≥0) (a : ℝ) : Measure ℝ :=
  Measure.sum (fun k : ℕ ↦ ENNReal.ofReal (poissonPMFReal r k) • scaledWalk a k)

instance compoundMeasure_probability (r : ℝ≥0) (a : ℝ) :
    IsProbabilityMeasure (compoundMeasure r a) := by
  constructor
  simp only [compoundMeasure, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ poissonPMFReal_nonneg)
    (poissonPMFRealSum r).summable, (poissonPMFRealSum r).tsum_eq]
  exact ENNReal.ofReal_one

/-- Scalar compensation in the generator supplies exactly the Poisson normalization. -/
theorem exponential_compensation (r a : ℝ) :
    NormedSpace.exp ℝ (r • generator a) =
      Real.exp (-r) • NormedSpace.exp ℝ (r • fairJump a) := by
  have hscalar : NormedSpace.exp ℝ ((-r) • (1 : Operator)) =
      Real.exp (-r) • (1 : Operator) := by
    have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Operator) (-r)
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using h.symm
  have heq : r • generator a = r • fairJump a + (-r) • (1 : Operator) := by
    rw [generator, smul_sub, sub_eq_add_neg, neg_smul]
  rw [heq, NormedSpace.exp_add_of_commute (𝕂 := ℝ)
    ((Commute.one_right (r • fairJump a)).smul_right (-r)), hscalar,
    mul_smul_comm, mul_one]

/-- The genuine Poisson mixture has exactly the limiting operator expectation. -/
theorem integral_compoundMeasure (r : ℝ≥0) (a : ℝ) (f : Observable) :
    ∫ x, f x ∂compoundMeasure r a =
      (NormedSpace.exp ℝ ((r : ℝ) • generator a)) f 0 := by
  have hf := f.integrable (compoundMeasure r a)
  rw [compoundMeasure, integral_sum_measure hf, exponential_compensation]
  change _ = Real.exp (-(r : ℝ)) * ((NormedSpace.exp ℝ ((r : ℝ) • fairJump a)) f 0)
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    ((r : ℝ) • fairJump a)).map (observer f 0) (observer f 0).continuous
  have h := hs.mul_left (Real.exp (-(r : ℝ)))
  calc
    _ = ∑' k : ℕ, Real.exp (-(r : ℝ)) * (observer f 0)
        ((k.factorial : ℝ)⁻¹ • ((r : ℝ) • fairJump a) ^ k) := by
      apply tsum_congr
      intro k
      rw [integral_smul_measure, integral_scaledWalk,
        ENNReal.toReal_ofReal poissonPMFReal_nonneg]
      simp only [map_smul, smul_pow, observer_apply, smul_eq_mul, poissonPMFReal]
      ring
    _ = _ := h.tsum_eq

/-- The normalized compound-Poisson probability law, with both parameters explicit. -/
noncomputable def compoundProbability (r : ℝ≥0) (a : ℝ) : ProbabilityMeasure ℝ :=
  ⟨compoundMeasure r a, inferInstance⟩

/-- Weak convergence of actual balanced HWE reports for arbitrary finite Poisson intensity. -/
theorem finite_intensity_weak_convergence (N : ℕ → ℕ) (a : ℕ → ℝ) (r : ℝ≥0) (b : ℝ)
    (hN : Tendsto N atTop atTop)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds (r : ℝ)))
    (ha : Tendsto a atTop (nhds b)) :
    Tendsto (fun m ↦ rowProbability m (N m) (a m)) atTop
      (nhds (compoundProbability r b)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun m ↦ ∫ x, f x ∂finiteMeasure (rowLaw m (N m)) (rowScore (a m)))
    atTop (nhds (∫ x, f x ∂compoundMeasure r b))
  simp only [integral_finiteMeasure, integral_compoundMeasure]
  exact finite_intensity_observable_limit N a r b hN hr ha f

/-- Positive limiting jump intensity forces the actual number of blocks to diverge. -/
theorem row_size_tends_infinity (N : ℕ → ℕ) (r : ℝ) (hrpos : 0 < r)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds r)) :
    Tendsto N atTop atTop := by
  have hp : Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  apply tendsto_atTop.2
  intro B
  have hb : Tendsto (fun m : ℕ ↦ (B : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hp
  filter_upwards [hr.eventually (eventually_gt_nhds (by linarith : r / 2 < r)),
    hb.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < r / 2))] with m hm hmb
  by_contra h
  have hn : (N m : ℝ) ≤ B := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge h))
  have hle := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m)
  linarith

/-- Original standardization equals the reciprocal square root of jump intensity. -/
theorem unitAmplitude_eq_inverse_sqrt (m N : ℕ) :
    unitAmplitude m N = (Real.sqrt ((N : ℝ) * (1 / 2 : ℝ) ^ m))⁻¹ := by
  apply (sq_eq_sq₀ (show 0 ≤ unitAmplitude m N by unfold unitAmplitude; positivity)
    (show 0 ≤ (Real.sqrt ((N : ℝ) * (1 / 2 : ℝ) ^ m))⁻¹ by positivity)).mp
  rw [unitAmplitude, div_pow, inv_pow, ← pow_mul, mul_comm m 2, pow_mul,
    Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg N),
    Real.sq_sqrt (by positivity)]
  rw [mul_inv_rev, ← inv_pow]
  norm_num
  ring

/-- The full positive finite-intensity phase for the original variance-normalized HWE statistic. -/
theorem normalized_compoundPoisson_limit (N : ℕ → ℕ) (r : ℝ≥0) (hrpos : 0 < r)
    (hr : Tendsto (fun m ↦ (N m : ℝ) * (1 / 2 : ℝ) ^ m) atTop (nhds (r : ℝ))) :
    Tendsto (fun m ↦ rowProbability m (N m) (unitAmplitude m (N m))) atTop
      (nhds (compoundProbability r (Real.sqrt r)⁻¹)) := by
  have hrpos' : (0 : ℝ) < r := hrpos
  apply finite_intensity_weak_convergence
    N (fun m ↦ unitAmplitude m (N m)) r (Real.sqrt r)⁻¹
    (row_size_tends_infinity N r hrpos' hr) hr
  have hs := (Real.continuous_sqrt.tendsto r).comp hr
  simpa only [unitAmplitude_eq_inverse_sqrt] using hs.inv₀ (by positivity)

end Descent.Portability.BalancedHWECompoundPoisson
