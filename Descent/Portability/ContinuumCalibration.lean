/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

namespace Descent.Portability

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

/-- Reference evaluation: with no covariate weight there is no calibration energy to spend. -/
theorem aggregateCalibrationEnergy_at_zero_weight
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor : Covariate → ℝ) :
    aggregateCalibrationEnergy 0 posterior conditional predictor = 0 := by
  unfold aggregateCalibrationEnergy
  simp


/-- Irreducible posterior-drift energy: conditional variance across indices at each covariate.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def calibrationDriftDefectSq (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    ∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2

omit [Fintype Covariate] in
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

omit [Fintype Covariate] in
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

/-! ## Arbitrary finite families: drift is average pairwise disagreement -/

/-- Half the posterior-weighted squared disagreement between two independent draws of the
population index at a fixed covariate.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite quadratic form. -/
noncomputable def posteriorPairwiseDriftEnergy
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (x : Covariate) : ℝ :=
  (1 / 2) * ∑ s, posterior x s *
    ∑ t, posterior x t * (conditional s x - conditional t x) ^ 2

omit [Fintype Covariate] in
/-- **Pairwise representation of posterior variance.**  For an arbitrary finite family of
ancestries or environments, the local drift defect is exactly half the expected squared
conditional-risk difference between two independent posterior draws.  No ordering, reference
ancestry, or two-group reduction is required. -/
theorem posteriorPairwiseDriftEnergy_eq_posteriorDriftEnergy
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (x : Covariate) (hposterior : ∑ t, posterior x t = 1) :
    posteriorPairwiseDriftEnergy posterior conditional x =
      ∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2 := by
  let variance :=
    ∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2
  have hrow (s : Index) :
      (∑ t, posterior x t * (conditional s x - conditional t x) ^ 2) =
        variance + (posteriorMean posterior conditional x - conditional s x) ^ 2 := by
    calc
      (∑ t, posterior x t * (conditional s x - conditional t x) ^ 2) =
          ∑ t, posterior x t * (conditional t x - conditional s x) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ = variance +
          (posteriorMean posterior conditional x - conditional s x) ^ 2 := by
            simpa [variance] using
              posterior_bias_variance_decomposition posterior conditional
                (fun _ ↦ conditional s x) x hposterior
  have hrecenter :
      (∑ s, posterior x s *
        (posteriorMean posterior conditional x - conditional s x) ^ 2) = variance := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [posteriorDrift]
    ring
  unfold posteriorPairwiseDriftEnergy
  simp_rw [hrow, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hposterior, one_mul, hrecenter]
  ring

omit [Fintype Covariate] in
/-- Pairwise drift energy is nonnegative whenever the posterior weights are nonnegative.  No
normalization is needed for this order property. -/
theorem posteriorPairwiseDriftEnergy_nonneg
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (x : Covariate) (hnonnegative : ∀ t, 0 ≤ posterior x t) :
    0 ≤ posteriorPairwiseDriftEnergy posterior conditional x := by
  unfold posteriorPairwiseDriftEnergy
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro s _
    apply mul_nonneg (hnonnegative s)
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (hnonnegative t) (sq_nonneg _)

omit [Fintype Covariate] in
/-- **Support-aware zero-defect law.**  For a nonnegative normalized posterior, pairwise drift
energy vanishes exactly when conditional risks agree on the posterior support.  This is the sealed
boundary form of the result: zero-mass populations are deliberately invisible, but no positively
represented population can disagree without paying positive defect. -/
theorem posteriorPairwiseDriftEnergy_eq_zero_iff_on_support
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (x : Covariate) (hposterior : ∑ t, posterior x t = 1)
    (hnonnegative : ∀ t, 0 ≤ posterior x t) :
    posteriorPairwiseDriftEnergy posterior conditional x = 0 ↔
      ∀ s t, 0 < posterior x s → 0 < posterior x t →
        conditional s x = conditional t x := by
  constructor
  · intro henergy
    have hsum :
        (∑ t, posterior x t * posteriorDrift posterior conditional t x ^ 2) = 0 := by
      rw [← posteriorPairwiseDriftEnergy_eq_posteriorDriftEnergy
        posterior conditional x hposterior]
      exact henergy
    have hterm (t : Index) :
        posterior x t * posteriorDrift posterior conditional t x ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun u _ ↦ mul_nonneg (hnonnegative u) (sq_nonneg _))).mp hsum
          t (Finset.mem_univ t)
    have hdrift (t : Index) (ht : 0 < posterior x t) :
        posteriorDrift posterior conditional t x = 0 := by
      have hsquare : posteriorDrift posterior conditional t x ^ 2 = 0 :=
        (mul_eq_zero.mp (hterm t)).resolve_left (ne_of_gt ht)
      nlinarith [sq_nonneg (posteriorDrift posterior conditional t x)]
    intro s t hspos htpos
    have hs := hdrift s hspos
    have ht := hdrift t htpos
    simp only [posteriorDrift] at hs ht
    linarith
  · intro hinvariant
    have houter (s : Index) :
        posterior x s *
          (∑ t, posterior x t * (conditional s x - conditional t x) ^ 2) = 0 := by
      by_cases hs : posterior x s = 0
      · simp [hs]
      · have hspos : 0 < posterior x s :=
          lt_of_le_of_ne (hnonnegative s) (Ne.symm hs)
        have hinner :
            (∑ t, posterior x t * (conditional s x - conditional t x) ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro t _
          by_cases ht : posterior x t = 0
          · simp [ht]
          · have htpos : 0 < posterior x t :=
              lt_of_le_of_ne (hnonnegative t) (Ne.symm ht)
            rw [hinvariant s t hspos htpos]
            ring
        rw [hinner]
        ring
    have hsum :
        (∑ s, posterior x s *
          ∑ t, posterior x t * (conditional s x - conditional t x) ^ 2) = 0 := by
      exact Finset.sum_eq_zero (fun s _ ↦ houter s)
    unfold posteriorPairwiseDriftEnergy
    rw [hsum]
    ring

omit [Fintype Covariate] in
/-- **Interior zero-defect law.**  When every population or environment has positive posterior
mass, zero pairwise energy is equivalent to complete conditional invariance.  This is the strict
support corollary of `posteriorPairwiseDriftEnergy_eq_zero_iff_on_support`. -/
theorem posteriorPairwiseDriftEnergy_eq_zero_iff
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (x : Covariate) (hposterior : ∑ t, posterior x t = 1)
    (hpositive : ∀ t, 0 < posterior x t) :
    posteriorPairwiseDriftEnergy posterior conditional x = 0 ↔
      ∀ s t, conditional s x = conditional t x := by
  rw [posteriorPairwiseDriftEnergy_eq_zero_iff_on_support posterior conditional x
    hposterior (fun t ↦ le_of_lt (hpositive t))]
  constructor
  · intro h s t
    exact h s t (hpositive s) (hpositive t)
  · intro h s t _ _
    exact h s t

/-- The global pairwise drift energy, averaged over covariates.  This form exposes the defect as
an ensemble of ancestry-to-ancestry disagreements rather than deviations from a privileged pooled
mean.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def pairwiseCalibrationDriftEnergy
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x * posteriorPairwiseDriftEnergy posterior conditional x

/-- **General finite-family drift law.**  The calibration defect equals the posterior-weighted
average of all pairwise conditional disagreements.  The two-index `q(1-q)Δ²` law below is its
rank-one face. -/
theorem calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    calibrationDriftDefectSq covariateWeight posterior conditional =
      pairwiseCalibrationDriftEnergy covariateWeight posterior conditional := by
  unfold calibrationDriftDefectSq pairwiseCalibrationDriftEnergy
  apply Finset.sum_congr rfl
  intro x _
  rw [posteriorPairwiseDriftEnergy_eq_posteriorDriftEnergy posterior conditional x
    (hposterior x)]

/-- **Global support-aware zero-defect law.**  With nonnegative covariate and posterior weights,
the global pairwise defect vanishes exactly when conditional risks agree among every pair of
populations represented at each positively weighted covariate.  This identifies both sealing
boundaries explicitly: zero covariate mass seals a context, and zero posterior mass seals a
population within that context. -/
theorem pairwiseCalibrationDriftEnergy_eq_zero_iff_on_support
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (hweight : ∀ x, 0 ≤ covariateWeight x)
    (hposterior : ∀ x, ∑ t, posterior x t = 1)
    (hnonnegative : ∀ x t, 0 ≤ posterior x t) :
    pairwiseCalibrationDriftEnergy covariateWeight posterior conditional = 0 ↔
      ∀ x, 0 < covariateWeight x → ∀ s t,
        0 < posterior x s → 0 < posterior x t → conditional s x = conditional t x := by
  have hlocal_nonneg (x : Covariate) :
      0 ≤ posteriorPairwiseDriftEnergy posterior conditional x :=
    posteriorPairwiseDriftEnergy_nonneg posterior conditional x (hnonnegative x)
  constructor
  · intro hglobal x hx s t hs ht
    have hterm :
        covariateWeight x * posteriorPairwiseDriftEnergy posterior conditional x = 0 := by
      unfold pairwiseCalibrationDriftEnergy at hglobal
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ ↦ mul_nonneg (hweight y) (hlocal_nonneg y))).mp hglobal
          x (Finset.mem_univ x)
    have hlocal : posteriorPairwiseDriftEnergy posterior conditional x = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hx)
    exact (posteriorPairwiseDriftEnergy_eq_zero_iff_on_support
      posterior conditional x (hposterior x) (hnonnegative x)).mp hlocal s t hs ht
  · intro hinvariant
    unfold pairwiseCalibrationDriftEnergy
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : covariateWeight x = 0
    · simp [hx]
    · have hxpos : 0 < covariateWeight x :=
        lt_of_le_of_ne (hweight x) (Ne.symm hx)
      have hlocal : posteriorPairwiseDriftEnergy posterior conditional x = 0 :=
        (posteriorPairwiseDriftEnergy_eq_zero_iff_on_support
          posterior conditional x (hposterior x) (hnonnegative x)).mpr
            (hinvariant x hxpos)
      rw [hlocal]
      ring

/-- The calibration defect itself has the same exact support characterization, by the general
pairwise drift identity. -/
theorem calibrationDriftDefectSq_eq_zero_iff_on_support
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (hweight : ∀ x, 0 ≤ covariateWeight x)
    (hposterior : ∀ x, ∑ t, posterior x t = 1)
    (hnonnegative : ∀ x t, 0 ≤ posterior x t) :
    calibrationDriftDefectSq covariateWeight posterior conditional = 0 ↔
      ∀ x, 0 < covariateWeight x → ∀ s t,
        0 < posterior x s → 0 < posterior x t → conditional s x = conditional t x := by
  rw [calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
    covariateWeight posterior conditional hposterior]
  exact pairwiseCalibrationDriftEnergy_eq_zero_iff_on_support
    covariateWeight posterior conditional hweight hposterior hnonnegative

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

/-- The canonical equal weight used by binary calibration witnesses.  Keeping this as one
definition prevents equal-posterior constructions in downstream biological modules from drifting
into independent copies of the same quantity. -/
noncomputable def balancedBinaryWeight {Carrier : Type*} (_ : Carrier) : ℝ := 1 / 2

/-- Reference evaluation: the balanced weight is a half at every carrier point. -/
@[simp] theorem balancedBinaryWeight_at_reference_point {Carrier : Type*} (c : Carrier) :
    balancedBinaryWeight c = 1 / 2 := rfl


/-- Posterior on two environments, with `q x` assigned to `true`. -/
noncomputable def twoIndexPosterior (q : Covariate → ℝ) (x : Covariate) (t : Bool) : ℝ :=
  if t then q x else 1 - q x

/-- Two environment-specific conditional fields. -/
noncomputable def twoIndexConditional (upper lower : Covariate → ℝ)
    (t : Bool) (x : Covariate) : ℝ :=
  if t then upper x else lower x

omit [Fintype Covariate] in
/-- The two-index posterior is normalized for every covariate, algebraically and without a
positivity assumption. -/
theorem twoIndexPosterior_sum_eq_one (q : Covariate → ℝ) (x : Covariate) :
    ∑ t, twoIndexPosterior q x t = 1 := by
  norm_num [twoIndexPosterior]

omit [Fintype Covariate] in
/-- The pooled conditional in a two-environment field. -/
theorem posteriorMean_twoIndex_eq (q upper lower : Covariate → ℝ) (x : Covariate) :
    posteriorMean (twoIndexPosterior q) (twoIndexConditional upper lower) x =
      q x * upper x + (1 - q x) * lower x := by
  norm_num [posteriorMean, twoIndexPosterior, twoIndexConditional]

omit [Fintype Covariate] in
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

omit [Fintype Covariate] in
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

/-! ## Clinical thresholds: a crossing has a quantitative calibration price -/

/-- The binary action induced by a clinical risk threshold.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a deterministic decision rule. -/
noncomputable def thresholdDecision (cutoff risk : ℝ) : Bool :=
  if cutoff ≤ risk then true else false

/-- Risks on opposite sides of a clinical cutoff force opposite actions. -/
theorem thresholdDecision_ne_of_crossing {cutoff lower upper : ℝ}
    (hlower : lower < cutoff) (hupper : cutoff ≤ upper) :
    thresholdDecision cutoff lower ≠ thresholdDecision cutoff upper := by
  simp [thresholdDecision, not_le_of_gt hlower, hupper]

/-- **No ancestry-blind action is correct across a threshold crossing.**  If the lower-risk
environment lies below a clinical cutoff and the upper-risk environment lies above it, then every
single binary action disagrees with at least one environment.  This is the decision-theoretic
content hidden by pooled calibration. -/
theorem no_common_thresholdDecision_of_crossing {cutoff lower upper : ℝ}
    (hlower : lower < cutoff) (hupper : cutoff ≤ upper) (action : Bool) :
    action ≠ thresholdDecision cutoff lower ∨
      action ≠ thresholdDecision cutoff upper := by
  by_cases h : action = thresholdDecision cutoff lower
  · right
    intro heq
    exact thresholdDecision_ne_of_crossing hlower hupper (h.symm.trans heq)
  · exact Or.inl h

omit [Fintype Covariate] in
/-- **A threshold crossing with margin forces a positive drift price.**  If both environments
remain posteriorly possible and their risks lie at least `margin` below and above the cutoff,
then the local calibration defect is at least `q(1-q)(2 margin)²`.  This turns a clinical
decision margin into an exact lower bound on the probability-estimation obstruction. -/
theorem twoIndex_posteriorDriftEnergy_ge_thresholdMargin
    (q upper lower : Covariate → ℝ) (x : Covariate) (cutoff margin : ℝ)
    (hq₀ : 0 ≤ q x) (hq₁ : q x ≤ 1) (hmargin : 0 ≤ margin)
    (hlower : lower x ≤ cutoff - margin)
    (hupper : cutoff + margin ≤ upper x) :
    q x * (1 - q x) * (2 * margin) ^ 2 ≤
      ∑ t, twoIndexPosterior q x t *
        posteriorDrift (twoIndexPosterior q) (twoIndexConditional upper lower) t x ^ 2 := by
  rw [twoIndex_posteriorDriftEnergy_eq]
  have hcoefficient : 0 ≤ q x * (1 - q x) :=
    mul_nonneg hq₀ (sub_nonneg.mpr hq₁)
  have hgap : 2 * margin ≤ upper x - lower x := by linarith
  have hgap_nonneg : 0 ≤ upper x - lower x := le_trans hmargin (by linarith)
  have hsquare : (2 * margin) ^ 2 ≤ (upper x - lower x) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hsquare hcoefficient

omit [Fintype Covariate] in
/-- With positive posterior overlap and positive clinical margin, the threshold-crossing drift
price is strictly positive. -/
theorem twoIndex_posteriorDriftEnergy_pos_of_thresholdMargin
    (q upper lower : Covariate → ℝ) (x : Covariate) (cutoff margin : ℝ)
    (hq₀ : 0 < q x) (hq₁ : q x < 1) (hmargin : 0 < margin)
    (hlower : lower x ≤ cutoff - margin)
    (hupper : cutoff + margin ≤ upper x) :
    0 < ∑ t, twoIndexPosterior q x t *
      posteriorDrift (twoIndexPosterior q) (twoIndexConditional upper lower) t x ^ 2 := by
  have hlower_lt_upper : lower x < upper x := by linarith
  rw [twoIndex_posteriorDriftEnergy_eq]
  exact mul_pos (mul_pos hq₀ (sub_pos.mpr hq₁)) (sq_pos_of_pos (sub_pos.mpr hlower_lt_upper))

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

/-- Reference evaluation: with no covariate weight every index-wise moment vanishes. -/
theorem indexWiseCalibrationMoment_at_zero_weight
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (predictor : Covariate → ℝ) (kernel : Covariate → ℝ) :
    indexWiseCalibrationMoment 0 posterior conditional predictor kernel = 0 := by
  unfold indexWiseCalibrationMoment
  simp


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

end Descent.Portability
