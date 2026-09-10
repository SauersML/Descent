/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DynamicBlindness
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.Decision Descent.Program

/-!
Exact leading-order small-time observation laws. Repeated differentiation and
L'Hopital's rule extract the first visible generator power with its factorial
coefficient; no nonzero leading term is assumed until identifying its order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Topology

namespace Descent.Portability.ObservationAsymptotics

open Filter DynamicBlindness

/-- The leading Taylor coefficient derived from a complete derivative jet. -/
theorem jet_leading_limit (jet : ℕ → ℝ → ℝ)
    (hderiv : ∀ order time, HasDerivAt (jet order) (jet (order + 1) time) time)
    (order : ℕ) (hzero : ∀ earlier < order, jet earlier 0 = 0) :
    Tendsto (fun time : ℝ ↦ jet 0 time / time ^ order) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (jet order 0 / (order.factorial : ℝ))) := by
  induction order generalizing jet with
  | zero =>
      simpa using (hderiv 0 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  | succ order ih =>
      have hnext : Tendsto (fun time : ℝ ↦ jet 1 time / time ^ order)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (jet (order + 1) 0 / (order.factorial : ℝ))) := by
        apply ih (fun index ↦ jet (index + 1)) (fun index time ↦ hderiv (index + 1) time)
        intro earlier hearlier
        exact hzero (earlier + 1) (by omega)
      have hratio : Tendsto
          (fun time : ℝ ↦ jet 1 time / ((order + 1 : ℕ) * time ^ order))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (jet (order + 1) 0 / ((order + 1).factorial : ℝ))) := by
        convert hnext.div_const (order + 1 : ℕ) using 1
        · funext time
          simp only [div_div]
          congr 1
          ring
        · rw [Nat.factorial_succ, Nat.cast_mul]
          simp only [div_div]
          congr 1
          ring
      have hfzero : Tendsto (jet 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hc : Tendsto (jet 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (jet 0 0)) :=
          (hderiv 0 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        simpa only [hzero 0 (Nat.zero_lt_succ order)] using hc
      have hgzero : Tendsto (fun time : ℝ ↦ time ^ (order + 1))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using ((hasDerivAt_id (0 : ℝ)).continuousAt.pow (order + 1)).tendsto.mono_left
          nhdsWithin_le_nhds
      apply HasDerivAt.lhopital_zero_nhdsGT
        (Eventually.of_forall (hderiv 0)) _ _ hfzero hgzero hratio
      · apply Eventually.of_forall
        intro time
        simpa using (hasDerivAt_id time).pow (order + 1)
      · filter_upwards [self_mem_nhdsWithin] with time htime
        exact mul_ne_zero (by positivity) (pow_ne_zero order (ne_of_gt htime))


/-- Integrating a power-order density contributes one additional time power. -/
theorem integral_power_limit (density : ℝ → ℝ) (hcontinuous : Continuous density)
    (order : ℕ) (coefficient : ℝ)
    (hlimit : Tendsto (fun time : ℝ ↦ density time / time ^ order)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds coefficient)) :
    Tendsto (fun horizon : ℝ ↦ (∫ time in 0..horizon, density time) / horizon ^ (order + 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (coefficient / (order + 1 : ℕ))) := by
  have hderiv (time : ℝ) : HasDerivAt (fun horizon ↦ ∫ moment in 0..horizon, density moment)
      (density time) time :=
    intervalIntegral.integral_hasDerivAt_right (hcontinuous.intervalIntegrable 0 time)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter hcontinuous.continuousAt
  have hfzero : Tendsto (fun horizon ↦ ∫ time in 0..horizon, density time)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [intervalIntegral.integral_same] using
      (hderiv 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgzero : Tendsto (fun time : ℝ ↦ time ^ (order + 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).continuousAt.pow (order + 1)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hratio : Tendsto (fun time : ℝ ↦ density time / ((order + 1 : ℕ) * time ^ order))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (coefficient / (order + 1 : ℕ))) := by
    convert hlimit.div_const (order + 1 : ℕ) using 1
    funext time
    simp only [div_div]
    congr 1
    ring
  apply HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hderiv) _ _ hfzero hgzero hratio
  · apply Eventually.of_forall
    intro time
    simpa using (hasDerivAt_id time).pow (order + 1)
  · filter_upwards [self_mem_nhdsWithin] with time htime
    exact mul_ne_zero (by positivity) (pow_ne_zero order (ne_of_gt htime))

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]

noncomputable def observationJet (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (report : I) (order : ℕ) (time : ℝ) : ℝ :=
  observation readout generator ((generator ^ order) *ᵥ direction) time report

theorem observationJet_derivative (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (report : I) (order : ℕ) (time : ℝ) :
    HasDerivAt (observationJet readout generator direction report order)
      (observationJet readout generator direction report (order + 1) time) time := by
  have hd := (ContinuousLinearMap.proj report).hasFDerivAt.comp_hasDerivAt time
    (observation_hasDerivAt readout generator ((generator ^ order) *ᵥ direction) time)
  simpa only [observationJet, Function.comp_def, ContinuousLinearMap.proj_apply,
    pow_succ', ← Matrix.mulVec_mulVec] using hd

/-- Each report coordinate has the exact leading visible-power coefficient. -/
theorem observation_leading_limit (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (order : ℕ)
    (hzero : ∀ earlier < order, readout *ᵥ (generator ^ earlier) *ᵥ direction = 0)
    (report : I) :
    Tendsto (fun time : ℝ ↦ observation readout generator direction time report / time ^ order)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((readout *ᵥ (generator ^ order) *ᵥ direction) report / (order.factorial : ℝ))) := by
  have hjet := jet_leading_limit (observationJet readout generator direction report)
    (observationJet_derivative readout generator direction report) order (by
      intro earlier hearlier
      simp only [observationJet, observation, zero_smul, NormedSpace.exp_zero,
        Matrix.one_mulVec, hzero earlier hearlier, Pi.zero_apply])
  simpa only [observationJet, pow_zero, Matrix.one_mulVec, observation, zero_smul,
    NormedSpace.exp_zero] using hjet


noncomputable def informationDensity (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (time : ℝ) : ℝ :=
  ∑ report, observation readout generator direction time report ^ 2

noncomputable def visibleCoefficient (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (order : ℕ) : ℝ :=
  ∑ report, (readout *ᵥ (generator ^ order) *ᵥ direction) report ^ 2

/-- Snapshot information density has exponent `2r` in a direction first visible at order `r`. -/
theorem density_leading_limit (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (order : ℕ)
    (hzero : ∀ earlier < order, readout *ᵥ (generator ^ earlier) *ᵥ direction = 0) :
    Tendsto (fun time : ℝ ↦
      informationDensity readout generator direction time / time ^ (2 * order))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (visibleCoefficient readout generator direction order /
        (order.factorial : ℝ) ^ 2)) := by
  have hsum := tendsto_finset_sum Finset.univ (fun report _ ↦
    (observation_leading_limit readout generator direction order hzero report).pow 2)
  simpa only [informationDensity, visibleCoefficient, Finset.sum_div, div_pow, ← pow_mul,
    Nat.mul_comm] using hsum

theorem informationDensity_continuous (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) : Continuous (informationDensity readout generator direction) := by
  apply continuous_finset_sum
  intro report _
  apply Continuous.pow
  apply continuous_iff_continuousAt.mpr
  intro time
  have hc := (observationJet_derivative readout generator direction report 0 time).continuousAt
  change ContinuousAt (fun moment ↦ observationJet readout generator direction report 0 moment)
    time at hc
  simpa only [observationJet, pow_zero, Matrix.one_mulVec] using hc

/-- Integrating the whitened observation density gives the continuous-observation
Gramian exponent `2r+1`, including the exact factorial and integration constants.
The readout may include a fixed noise-whitening operator. -/
theorem integrated_information_leading_limit (readout : Matrix I S ℝ)
    (generator : Matrix S S ℝ) (direction : S → ℝ) (order : ℕ)
    (hzero : ∀ earlier < order, readout *ᵥ (generator ^ earlier) *ᵥ direction = 0) :
    Tendsto (fun horizon : ℝ ↦
      (∫ time in 0..horizon, informationDensity readout generator direction time) /
        horizon ^ (2 * order + 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (visibleCoefficient readout generator direction order /
        ((order.factorial : ℝ) ^ 2 * (2 * order + 1 : ℕ)))) := by
  have hlimit := integral_power_limit (informationDensity readout generator direction)
    (informationDensity_continuous readout generator direction) (2 * order)
    (visibleCoefficient readout generator direction order / (order.factorial : ℝ) ^ 2)
    (density_leading_limit readout generator direction order hzero)
  simpa only [div_div] using hlimit

/-- A nonzero first visible derivative makes the displayed leading coefficient strictly positive. -/
theorem visibleCoefficient_pos (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (order : ℕ)
    (hvisible : readout *ᵥ (generator ^ order) *ᵥ direction ≠ 0) :
    0 < visibleCoefficient readout generator direction order := by
  have hexists : ∃ report, (readout *ᵥ (generator ^ order) *ᵥ direction) report ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hvisible (funext hnone)
  obtain ⟨report, hreport⟩ := hexists
  apply Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
  exact ⟨report, Finset.mem_univ report, sq_pos_of_ne_zero hreport⟩

end Descent.Portability.ObservationAsymptotics
