/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators

/-!
# Calibration against a varying family: the finite posterior-field core

This module formalizes the algebraic spine of continuum-indexed calibration without turning
analytic or literature claims into assumptions.  `Index` is a finite quadrature of the continuum
of populations, ancestries, environments, or time points, and `Covariate` is a finite genotype,
risk-score bin, or molecular context.  The key input is the posterior `posterior x t`: the weight
of index `t` after observing covariate `x`.  Refining the quadrature preserves every identity here.

The central result is an exact conditional bias--variance decomposition.  It has three immediate
consequences.

* Index-wise calibration energy is aggregate calibration energy plus a nonnegative drift defect.
* The posterior mean is aggregate-calibrated and attains the irreducible defect.
* Paying aggregate error cannot reduce the index-wise energy in the squared, posterior-weighted
  geometry.

This is the saturated finite form of Theorem 1 in the continuum program.  Measure-theoretic
disintegration, closed-range attainment, singular-value tails, extrapolation, and perturbation
theory are deliberately not asserted here.  They require additional analytic formalization, not
theorem-valued parameters.
-/

section PosteriorField

variable {Index Covariate : Type*} [Fintype Index] [Fintype Covariate]

/-- Conditional outcome averaged over the posterior distribution of the population index. -/
noncomputable def posteriorMean (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (x : Covariate) : ℝ :=
  ∑ t, posterior x t * conditional t x

/-- The population-specific part of conditional outcome that pooled calibration cannot see.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the centered part of the supplied
conditional field. -/
noncomputable def posteriorDrift (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (t : Index) (x : Covariate) : ℝ :=
  conditional t x - posteriorMean posterior conditional x

/-- Squared index-wise calibration violation, averaged over covariates and posterior indices. -/
noncomputable def indexWiseCalibrationEnergy (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor : Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    ∑ t, posterior x t * (conditional t x - predictor x) ^ 2

/-- Squared calibration violation after the index has been aggregated out. -/
noncomputable def aggregateCalibrationEnergy (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor : Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x * (posteriorMean posterior conditional x - predictor x) ^ 2

/-- Irreducible posterior-drift energy: conditional variance across indices at each covariate.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def calibrationDriftDefectSq (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    ∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2

/-- A posterior-weighted conditional residual has zero index mean. -/
theorem posteriorDrift_weighted_sum_eq_zero
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (x : Covariate) (hposterior : ∑ t, posterior x t = 1) :
    ∑ t, posterior x t * posteriorDrift posterior conditional t x = 0 := by
  unfold posteriorDrift
  calc
    (∑ t, posterior x t *
        (conditional t x - posteriorMean posterior conditional x)) =
        ∑ t, (posterior x t * conditional t x -
          posterior x t * posteriorMean posterior conditional x) := by
            apply Finset.sum_congr rfl
            intro t _
            ring
    _ =
        (∑ t, posterior x t * conditional t x) -
          (∑ t, posterior x t * posteriorMean posterior conditional x) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ t, posterior x t * conditional t x) -
          (∑ t, posterior x t) * posteriorMean posterior conditional x := by
            rw [← Finset.sum_mul]
    _ = posteriorMean posterior conditional x -
          (∑ t, posterior x t) * posteriorMean posterior conditional x := by
            rw [posteriorMean]
    _ = 0 := by rw [hposterior]; ring

/-- **Pointwise posterior bias--variance identity.**  At a fixed covariate, index-wise squared
error is conditional drift variance plus squared pooled error. -/
theorem posterior_bias_variance_decomposition
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor : Covariate → ℝ) (x : Covariate)
    (hposterior : ∑ t, posterior x t = 1) :
    (∑ t, posterior x t * (conditional t x - predictor x) ^ 2) =
      (∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2) +
        (posteriorMean posterior conditional x - predictor x) ^ 2 := by
  let m := posteriorMean posterior conditional x
  have hcenter : ∑ t, posterior x t * (conditional t x - m) = 0 := by
    simpa [m, posteriorDrift] using
      posteriorDrift_weighted_sum_eq_zero posterior conditional x hposterior
  have hcross :
      ∑ t, 2 * (posterior x t * (conditional t x - m) * (m - predictor x)) = 0 := by
    calc
      (∑ t, 2 * (posterior x t * (conditional t x - m) * (m - predictor x))) =
          2 * (m - predictor x) *
            (∑ t, posterior x t * (conditional t x - m)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              ring
      _ = 0 := by rw [hcenter]; ring
  have hconstant :
      ∑ t, posterior x t * (m - predictor x) ^ 2 = (m - predictor x) ^ 2 := by
    calc
      (∑ t, posterior x t * (m - predictor x) ^ 2) =
          (∑ t, posterior x t) * (m - predictor x) ^ 2 := by
            rw [← Finset.sum_mul]
      _ = (m - predictor x) ^ 2 := by rw [hposterior]; ring
  calc
    (∑ t, posterior x t * (conditional t x - predictor x) ^ 2) =
        ∑ t, posterior x t *
          ((conditional t x - m) + (m - predictor x)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            ring
    _ = ∑ t, (posterior x t * (conditional t x - m) ^ 2 +
          2 * (posterior x t * (conditional t x - m) * (m - predictor x)) +
          posterior x t * (m - predictor x) ^ 2) := by
            apply Finset.sum_congr rfl
            intro t _
            ring
    _ = (∑ t, posterior x t * (conditional t x - m) ^ 2) +
          (∑ t, 2 * (posterior x t * (conditional t x - m) * (m - predictor x))) +
          (∑ t, posterior x t * (m - predictor x) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ t, posterior x t * (conditional t x - m) ^ 2) +
          (m - predictor x) ^ 2 := by rw [hcross, hconstant]; ring
    _ = (∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2) +
          (posteriorMean posterior conditional x - predictor x) ^ 2 := by
            simp [m, posteriorDrift]

/-- **Global Pythagoras for varying conditionals.**  The complete index-wise violation is the
sum of the aggregate violation and the drift defect. -/
theorem indexWiseCalibrationEnergy_eq_driftDefect_add_aggregate
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (predictor : Covariate → ℝ)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    indexWiseCalibrationEnergy covariateWeight posterior conditional predictor =
      calibrationDriftDefectSq covariateWeight posterior conditional +
        aggregateCalibrationEnergy covariateWeight posterior conditional predictor := by
  unfold indexWiseCalibrationEnergy calibrationDriftDefectSq aggregateCalibrationEnergy
  simp_rw [posterior_bias_variance_decomposition posterior conditional predictor _ (hposterior _),
    mul_add, Finset.sum_add_distrib]

/-- Aggregate calibration energy is nonnegative for nonnegative covariate weights. -/
theorem aggregateCalibrationEnergy_nonneg (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor : Covariate → ℝ) (hweight : ∀ x, 0 ≤ covariateWeight x) :
    0 ≤ aggregateCalibrationEnergy covariateWeight posterior conditional predictor := by
  unfold aggregateCalibrationEnergy
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hweight x) (sq_nonneg _)

/-- The drift defect is a lower bound for every predictor's index-wise calibration energy. -/
theorem calibrationDriftDefectSq_le_indexWiseCalibrationEnergy
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (predictor : Covariate → ℝ)
    (hweight : ∀ x, 0 ≤ covariateWeight x)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    calibrationDriftDefectSq covariateWeight posterior conditional ≤
      indexWiseCalibrationEnergy covariateWeight posterior conditional predictor := by
  rw [indexWiseCalibrationEnergy_eq_driftDefect_add_aggregate _ _ _ _ hposterior]
  exact le_add_of_nonneg_right
    (aggregateCalibrationEnergy_nonneg covariateWeight posterior conditional predictor hweight)

/-- The posterior mean has zero aggregate calibration error. -/
@[simp] theorem aggregateCalibrationEnergy_posteriorMean
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) :
    aggregateCalibrationEnergy covariateWeight posterior conditional
      (posteriorMean posterior conditional) = 0 := by
  simp [aggregateCalibrationEnergy]

/-- **The obstruction is attained.**  The posterior-mean predictor has index-wise energy exactly
equal to the drift defect, while remaining perfectly aggregate-calibrated. -/
theorem indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    indexWiseCalibrationEnergy covariateWeight posterior conditional
      (posteriorMean posterior conditional) =
        calibrationDriftDefectSq covariateWeight posterior conditional := by
  rw [indexWiseCalibrationEnergy_eq_driftDefect_add_aggregate _ _ _ _ hposterior,
    aggregateCalibrationEnergy_posteriorMean, add_zero]

/-! ## Two-index law: prevalence heterogeneity times squared section width -/

/-- Posterior on two environments, with `q x` assigned to `true`. -/
noncomputable def twoIndexPosterior (q : Covariate → ℝ) (x : Covariate) (t : Bool) : ℝ :=
  if t then q x else 1 - q x

/-- Two environment-specific conditional fields. -/
noncomputable def twoIndexConditional (upper lower : Covariate → ℝ)
    (t : Bool) (x : Covariate) : ℝ :=
  if t then upper x else lower x

/-- The two-index posterior is normalized for every covariate, algebraically and without a
positivity assumption. -/
theorem twoIndexPosterior_sum_eq_one (q : Covariate → ℝ) (x : Covariate) :
    ∑ t, twoIndexPosterior q x t = 1 := by
  norm_num [twoIndexPosterior]

/-- The pooled conditional in a two-environment field. -/
theorem posteriorMean_twoIndex_eq (q upper lower : Covariate → ℝ) (x : Covariate) :
    posteriorMean (twoIndexPosterior q) (twoIndexConditional upper lower) x =
      q x * upper x + (1 - q x) * lower x := by
  norm_num [posteriorMean, twoIndexPosterior, twoIndexConditional]

/-- **Exact two-index drift law, pointwise.**  Conditional drift energy is posterior
heterogeneity `q(1-q)` times squared section width.  Thus a large difference between two
biological environments matters only to the extent that both environments remain posteriorly
plausible at the covariate. -/
theorem twoIndex_posteriorDriftEnergy_eq
    (q upper lower : Covariate → ℝ) (x : Covariate) :
    (∑ t, twoIndexPosterior q x t *
      posteriorDrift (twoIndexPosterior q) (twoIndexConditional upper lower) t x ^ 2) =
        q x * (1 - q x) * (upper x - lower x) ^ 2 := by
  unfold posteriorDrift
  simp_rw [posteriorMean_twoIndex_eq]
  norm_num [twoIndexPosterior, twoIndexConditional]
  ring

/-- **The only interior zero is no conditional drift.**  When both environments remain
posteriorly possible at a covariate, their local calibration defect vanishes exactly when their
conditional risks agree.  At `q = 0` or `q = 1` the index is instead determined by the covariate,
which is the other degeneracy. -/
theorem twoIndex_posteriorDriftEnergy_eq_zero_iff
    (q upper lower : Covariate → ℝ) (x : Covariate)
    (hq₀ : 0 < q x) (hq₁ : q x < 1) :
    ( ∑ t, twoIndexPosterior q x t *
      posteriorDrift (twoIndexPosterior q) (twoIndexConditional upper lower) t x ^ 2) = 0 ↔
        upper x = lower x := by
  rw [twoIndex_posteriorDriftEnergy_eq]
  constructor
  · intro h
    have hcoefficient : q x * (1 - q x) ≠ 0 :=
      ne_of_gt (mul_pos hq₀ (sub_pos.mpr hq₁))
    have hsquare : (upper x - lower x) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hcoefficient
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    rw [h]
    ring

/-- **Exact two-index drift law, globally.**  The full calibration obstruction integrates the
product of posterior heterogeneity and squared section width over biological covariates.  This
bridges the section geometry of functional descent to the `L²` calibration defect. -/
theorem twoIndex_calibrationDriftDefectSq_eq
    (covariateWeight q upper lower : Covariate → ℝ) :
    calibrationDriftDefectSq covariateWeight (twoIndexPosterior q)
      (twoIndexConditional upper lower) =
        ∑ x, covariateWeight x * q x * (1 - q x) * (upper x - lower x) ^ 2 := by
  unfold calibrationDriftDefectSq
  simp_rw [twoIndex_posteriorDriftEnergy_eq]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- **Sharp one-quarter bound.**  For nonnegative covariate weights, posterior uncertainty can
charge at most one quarter of the squared conditional separation.  The constant is independent of
the number or scale of covariates and cannot be improved, as the balanced theorem below shows. -/
theorem twoIndex_calibrationDriftDefectSq_le_quarter_widthEnergy
    (covariateWeight q upper lower : Covariate → ℝ)
    (hweight : ∀ x, 0 ≤ covariateWeight x) :
    calibrationDriftDefectSq covariateWeight (twoIndexPosterior q)
      (twoIndexConditional upper lower) ≤
        ∑ x, covariateWeight x * (1 / 4) * (upper x - lower x) ^ 2 := by
  rw [twoIndex_calibrationDriftDefectSq_eq]
  apply Finset.sum_le_sum
  intro x _
  have hposterior : q x * (1 - q x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (q x - 1 / 2)]
  calc
    covariateWeight x * q x * (1 - q x) * (upper x - lower x) ^ 2 =
        (covariateWeight x * (q x * (1 - q x))) * (upper x - lower x) ^ 2 := by
          ring
    _ ≤ (covariateWeight x * (1 / 4)) * (upper x - lower x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hposterior (hweight x)) (sq_nonneg _)
    _ = covariateWeight x * (1 / 4) * (upper x - lower x) ^ 2 := by ring

/-- **Balanced posteriors attain the one-quarter bound.**  Therefore `1/4` in the preceding
theorem is the exact permeability constant for two equally plausible biological environments. -/
theorem twoIndex_balanced_calibrationDriftDefectSq_eq_quarter_widthEnergy
    (covariateWeight upper lower : Covariate → ℝ) :
    calibrationDriftDefectSq covariateWeight
      (twoIndexPosterior (fun _ ↦ 1 / 2)) (twoIndexConditional upper lower) =
        ∑ x, covariateWeight x * (1 / 4) * (upper x - lower x) ^ 2 := by
  rw [twoIndex_calibrationDriftDefectSq_eq]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A weighted calibration moment after aggregating out the population index. -/
noncomputable def aggregateCalibrationMoment (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor kernel : Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    (posteriorMean posterior conditional x - predictor x) * kernel x

/-- The same calibration moment evaluated before the population index is aggregated out. -/
noncomputable def indexWiseCalibrationMoment (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor kernel : Covariate → ℝ) : ℝ :=
  ∑ t, ∑ x, covariateWeight x * posterior x t *
    (conditional t x - predictor x) * kernel x

/-- **Nested demands.**  The aggregate calibration moment is the sum of the index-wise moments.
Thus exact index-wise calibration implies exact aggregate calibration; these constraints are
nested rather than opposed. -/
theorem aggregateCalibrationMoment_eq_indexWiseCalibrationMoment
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (predictor kernel : Covariate → ℝ)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    aggregateCalibrationMoment covariateWeight posterior conditional predictor kernel =
      indexWiseCalibrationMoment covariateWeight posterior conditional predictor kernel := by
  unfold aggregateCalibrationMoment indexWiseCalibrationMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    covariateWeight x * (posteriorMean posterior conditional x - predictor x) * kernel x =
        (∑ t, covariateWeight x * posterior x t *
          (conditional t x - predictor x)) * kernel x := by
            congr 1
            rw [posteriorMean]
            calc
              covariateWeight x *
                  ((∑ t, posterior x t * conditional t x) - predictor x) =
                  covariateWeight x *
                    ((∑ t, posterior x t * conditional t x) -
                      (∑ t, posterior x t) * predictor x) := by rw [hposterior]; ring
              _ = ∑ t, covariateWeight x * posterior x t *
                    (conditional t x - predictor x) := by
                    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro t _
                    ring
    _ = ∑ t, covariateWeight x * posterior x t *
          (conditional t x - predictor x) * kernel x := by
            rw [← Finset.sum_mul]

end PosteriorField

end Calibrator
