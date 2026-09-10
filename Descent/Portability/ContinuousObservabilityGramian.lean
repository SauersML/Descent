/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ObservationAsymptotics
import Descent.Portability.DiscountedObservability

assert_below Descent.Decision Descent.Program

/-!
The continuous observation Gramian and its directional small-time law. A fixed
precision-square-root may be included in the supplied readout. This formalizes
the Gramian asymptotic, independently of constructing a white-noise probability
experiment whose Fisher information equals that Gramian.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Matrix.Norms.Operator Topology

namespace Descent.Portability.ContinuousObservabilityGramian

open Filter DynamicBlindness ObservationAsymptotics EvolutionaryObservability
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]

noncomputable def gramianIntegrand (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (time : ℝ) : Matrix S S ℝ :=
  (readout * NormedSpace.exp ℝ (time • generator)).transpose *
    (readout * NormedSpace.exp ℝ (time • generator))

noncomputable def continuousGramian (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (horizon : ℝ) : Matrix S S ℝ :=
  ∫ time in 0..horizon, gramianIntegrand readout generator time

theorem gramianIntegrand_continuous (readout : Matrix I S ℝ) (generator : Matrix S S ℝ) :
    Continuous (gramianIntegrand readout generator) := by
  have he : Continuous (fun time : ℝ ↦ NormedSpace.exp ℝ (time • generator)) :=
    continuous_iff_continuousAt.mpr fun time ↦
      (hasDerivAt_exp_smul_const generator time).continuousAt
  exact (continuous_const.matrix_mul he).matrix_transpose.matrix_mul
    (continuous_const.matrix_mul he)

/-- The integrand quadratic form is exactly the squared observation density. -/
theorem density_eq_quadratic (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (time : ℝ) :
    informationDensity readout generator direction time =
      direction ⬝ᵥ gramianIntegrand readout generator time *ᵥ direction := by
  have heq := forecastLoss_eq_quadratic
    (fun _ : Unit ↦ (readout * NormedSpace.exp ℝ (time • generator)).transpose)
    (fun _ ↦ (1 : ℝ)) direction
  simpa only [forecastLoss, gramian, Finset.univ_unique, Finset.sum_singleton,
    Matrix.transpose_transpose, one_mul, one_smul, informationDensity,
    gramianIntegrand, observation, Matrix.mulVec_mulVec] using heq

/-- Integration and the finite quadratic readout commute exactly. -/
theorem continuousGramian_quadratic (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (horizon : ℝ) :
    direction ⬝ᵥ continuousGramian readout generator horizon *ᵥ direction =
      ∫ time in 0..horizon, informationDensity readout generator direction time := by
  let linear : Matrix S S ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (DiscountedObservability.quadraticLinear direction)
  have heq := linear.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    ((gramianIntegrand_continuous readout generator).intervalIntegrable 0 horizon)
  simpa only [linear, LinearMap.coe_toContinuousLinearMap',
    DiscountedObservability.quadraticLinear, LinearMap.coe_mk, AddHom.coe_mk,
    continuousGramian, density_eq_quadratic] using heq.symm

/-- The directional continuous Gramian has the report's exact `T^(2r+1)` coefficient. -/
theorem gramian_directional_leading_limit (readout : Matrix I S ℝ)
    (generator : Matrix S S ℝ) (direction : S → ℝ) (order : ℕ)
    (hzero : ∀ earlier < order, readout *ᵥ (generator ^ earlier) *ᵥ direction = 0) :
    Tendsto (fun horizon : ℝ ↦
      (direction ⬝ᵥ continuousGramian readout generator horizon *ᵥ direction) /
        horizon ^ (2 * order + 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (visibleCoefficient readout generator direction order /
        ((order.factorial : ℝ) ^ 2 * (2 * order + 1 : ℕ)))) := by
  simpa only [continuousGramian_quadratic] using
    integrated_information_leading_limit readout generator direction order hzero

/-- A first visible derivative makes the asymptotic constant positive. -/
theorem leading_constant_pos (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (order : ℕ)
    (hvisible : readout *ᵥ (generator ^ order) *ᵥ direction ≠ 0) :
    0 < visibleCoefficient readout generator direction order /
      ((order.factorial : ℝ) ^ 2 * (2 * order + 1 : ℕ)) := by
  apply div_pos (visibleCoefficient_pos readout generator direction order hvisible)
  positivity

end Descent.Portability.ContinuousObservabilityGramian
