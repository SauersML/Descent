/-
Copyright (c) 2026 Gnomon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gnomon contributors
-/
import Calibrator.ContinuumCalibrationProgram
import Calibrator.PGSCalibrationTheory
import Calibrator.UnifiedBiology

/-!
# Polygenic-score calibration over an ancestry continuum

The abstract index in `ContinuumCalibration` is here read as genetic ancestry, the covariate as a
genotype or score bin, the posterior as ancestry composition conditional on that covariate, and the
conditional field as ancestry-specific disease risk.  The resulting theorems distinguish pooled
calibration, ancestry-wise calibration, worst-ancestry error, and threshold utility without adding
an empirical assumption about any particular biobank.
-/

namespace Calibrator

section GeneralAncestryLaw

variable {Genotype Ancestry : Type*}
  [Fintype Genotype] [Fintype Ancestry]

/-- The irreducible ancestry-wise calibration floor, expressed in polygenic-score language.

Empirical status: NOT AN EMPIRICAL CLAIM -- this names an exact calibration functional. -/
noncomputable def polygenicCalibrationFloor
    (genotypeWeight : Genotype → ℝ)
    (ancestryPosterior : Genotype → Ancestry → ℝ)
    (ancestryRisk : Ancestry → Genotype → ℝ) : ℝ :=
  calibrationDriftDefectSq genotypeWeight ancestryPosterior ancestryRisk

/-- The polygenic calibration floor is exactly the continuum drift defect. -/
theorem polygenicCalibrationFloor_eq_driftDefectSq
    (genotypeWeight : Genotype → ℝ)
    (ancestryPosterior : Genotype → Ancestry → ℝ)
    (ancestryRisk : Ancestry → Genotype → ℝ) :
    polygenicCalibrationFloor genotypeWeight ancestryPosterior ancestryRisk =
      calibrationDriftDefectSq genotypeWeight ancestryPosterior ancestryRisk := by
  rfl

/-- The four exact laws needed to interpret continuum calibration as a polygenic-score
portability theorem. -/
structure PolygenicContinuumCalibrationLaw
    (genotypeWeight : Genotype → ℝ)
    (ancestryPosterior : Genotype → Ancestry → ℝ)
    (ancestryRisk : Ancestry → Genotype → ℝ) : Prop where
  /-- Ancestry-wise squared calibration error is pooled error plus an irreducible drift floor. -/
  ancestry_pythagoras :
    ∀ score,
      indexWiseCalibrationEnergy genotypeWeight ancestryPosterior ancestryRisk score =
        polygenicCalibrationFloor genotypeWeight ancestryPosterior ancestryRisk +
          aggregateCalibrationEnergy genotypeWeight ancestryPosterior ancestryRisk score
  /-- The posterior-mean score is pooled-calibrated and attains the ancestry-wise floor. -/
  pooled_score_attains_floor :
    indexWiseCalibrationEnergy genotypeWeight ancestryPosterior ancestryRisk
        (posteriorMean ancestryPosterior ancestryRisk) =
      polygenicCalibrationFloor genotypeWeight ancestryPosterior ancestryRisk
  /-- The floor is the weighted average of all pairwise ancestry-risk disagreements. -/
  floor_is_pairwise_disagreement :
    polygenicCalibrationFloor genotypeWeight ancestryPosterior ancestryRisk =
      pairwiseCalibrationDriftEnergy genotypeWeight ancestryPosterior ancestryRisk
  /-- Zero floor means risk invariance only on represented ancestry/genotype support. -/
  floor_eq_zero_iff_support_invariant :
    polygenicCalibrationFloor genotypeWeight ancestryPosterior ancestryRisk = 0 ↔
      ∀ x, 0 < genotypeWeight x → ∀ s t,
        0 < ancestryPosterior x s → 0 < ancestryPosterior x t →
          ancestryRisk s x = ancestryRisk t x

/-- **Polygenic continuum calibration theorem.**  Under normalized nonnegative ancestry
composition and nonnegative genotype weights, all four portability laws hold simultaneously. -/
theorem polygenicContinuumCalibrationLaw
    (genotypeWeight : Genotype → ℝ)
    (ancestryPosterior : Genotype → Ancestry → ℝ)
    (ancestryRisk : Ancestry → Genotype → ℝ)
    (hweight : ∀ x, 0 ≤ genotypeWeight x)
    (hposterior : ∀ x, ∑ t, ancestryPosterior x t = 1)
    (hnonnegative : ∀ x t, 0 ≤ ancestryPosterior x t) :
    PolygenicContinuumCalibrationLaw genotypeWeight ancestryPosterior ancestryRisk := by
  refine
    { ancestry_pythagoras := ?_
      pooled_score_attains_floor := ?_
      floor_is_pairwise_disagreement := ?_
      floor_eq_zero_iff_support_invariant := ?_ }
  · intro score
    rw [polygenicCalibrationFloor_eq_driftDefectSq]
    exact indexWiseCalibrationEnergy_eq_driftDefect_add_aggregate
      genotypeWeight ancestryPosterior ancestryRisk score hposterior
  · rw [polygenicCalibrationFloor_eq_driftDefectSq]
    exact indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq
      genotypeWeight ancestryPosterior ancestryRisk hposterior
  · rw [polygenicCalibrationFloor_eq_driftDefectSq]
    exact calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
      genotypeWeight ancestryPosterior ancestryRisk hposterior
  · rw [polygenicCalibrationFloor_eq_driftDefectSq]
    exact calibrationDriftDefectSq_eq_zero_iff_on_support
      genotypeWeight ancestryPosterior ancestryRisk hweight hposterior hnonnegative

/-- Any ancestry-aware predictor pays at least the pairwise-disagreement floor.  This combines
the Pythagorean lower bound with the ancestry-pair representation, eliminating the arbitrary
choice of a reference population. -/
theorem pairwiseAncestryDisagreement_le_indexWiseCalibration
    (genotypeWeight : Genotype → ℝ)
    (ancestryPosterior : Genotype → Ancestry → ℝ)
    (ancestryRisk : Ancestry → Genotype → ℝ)
    (score : Genotype → ℝ)
    (hweight : ∀ x, 0 ≤ genotypeWeight x)
    (hposterior : ∀ x, ∑ t, ancestryPosterior x t = 1) :
    pairwiseCalibrationDriftEnergy genotypeWeight ancestryPosterior ancestryRisk ≤
      indexWiseCalibrationEnergy genotypeWeight ancestryPosterior ancestryRisk score := by
  rw [← calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
    genotypeWeight ancestryPosterior ancestryRisk hposterior]
  exact calibrationDriftDefectSq_le_indexWiseCalibrationEnergy
    genotypeWeight ancestryPosterior ancestryRisk score hweight hposterior

end GeneralAncestryLaw

section BinaryDeploymentBoundary

/-- The aligned calibration witness and the persistence-only biological posterior expose the
same binary direction, despite reversing their argument roles. -/
theorem gaugeAlignedPredictor_eq_persistentOnlyDynamicsPosterior
    (persists : Bool) (x : Unit) :
    gaugeAlignedPredictor persists x =
      persistentOnlyDynamicsPosterior (0 : BinaryBiologicalState) persists := by
  cases persists <;>
    norm_num [gaugeAlignedPredictor, persistentOnlyDynamicsPosterior, binarySecondAnnotation]

/-- A binary-ancestry PGS deployment has two simultaneous boundaries: unequal representation
separates pooled calibration from worst-ancestry performance, while a clinical threshold crossed
by the ancestry-specific risks creates both positive calibration defect and positive decision
regret for either ancestry-blind action. -/
structure BinaryPolygenicDeploymentBoundary
    (q lower upper cutoff : ℝ) : Prop where
  pooled_mean_is_worst_ancestry_suboptimal :
    (upper - lower) / 2 <
      worstIndexError upper lower (q * upper + (1 - q) * lower)
  crossing_creates_positive_calibration_floor :
    0 < ∑ t, twoIndexPosterior (fun _ : Unit ↦ q) () t *
      posteriorDrift (twoIndexPosterior (fun _ : Unit ↦ q))
        (twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower)) t () ^ 2
  no_ancestry_blind_action_is_regret_free :
    ∀ action : Bool,
      0 < driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
        (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper)
          (fun _ : Unit ↦ lower) t ()) cutoff action

/-- **Binary polygenic deployment theorem.**  Representation imbalance and threshold crossing
are logically distinct and both persist with infinite sample size: the first is a norm mismatch,
the second is a decision boundary crossed by ancestry-specific risk. -/
theorem binaryPolygenicDeploymentBoundary
    (q lower upper cutoff : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hbalance : q ≠ 1 / 2)
    (hcutoff : cutoff < 1) (hlower : lower < cutoff) (hupper : cutoff < upper) :
    BinaryPolygenicDeploymentBoundary q lower upper cutoff := by
  have hwidth : lower < upper := hlower.trans hupper
  have hcrossing :=
    crossing_forces_defect_and_regret q lower upper cutoff hq₀ hq₁ hcutoff hlower hupper
  exact
    { pooled_mean_is_worst_ancestry_suboptimal :=
        worstIndexError_posteriorMean_gt_half_width q upper lower hq₀ hq₁ hbalance hwidth
      crossing_creates_positive_calibration_floor := hcrossing.1
      no_ancestry_blind_action_is_regret_free := hcrossing.2 }

/-! ## Recruitment objective matters -/

/-- **Worst-ancestry recruitment lower bound.**  With two positive stratum sample sizes, the
larger inverse sample size is at least the inverse penalty achieved by an equal split.  Unlike the
`L²(π)` allocation law, this worst-ancestry objective does not contain population prevalence. -/
theorem two_div_sum_le_max_reciprocal
    (n₀ n₁ : ℝ) (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) :
    2 / (n₀ + n₁) ≤ max (1 / n₀) (1 / n₁) := by
  have hsum : 0 < n₀ + n₁ := add_pos hn₀ hn₁
  rcases le_total n₀ n₁ with horder | horder
  · have hden : 2 * n₀ ≤ n₀ + n₁ := by linarith
    have hfrac : 2 / (n₀ + n₁) ≤ 2 / (2 * n₀) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hn₀) hden
    have heq : 2 / (2 * n₀) = 1 / n₀ := by
      field_simp
    rw [heq] at hfrac
    exact hfrac.trans (le_max_left _ _)
  · have hden : 2 * n₁ ≤ n₀ + n₁ := by linarith
    have hfrac : 2 / (n₀ + n₁) ≤ 2 / (2 * n₁) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hn₁) hden
    have heq : 2 / (2 * n₁) = 1 / n₁ := by
      field_simp
    rw [heq] at hfrac
    exact hfrac.trans (le_max_right _ _)

/-- Equal recruitment attains the worst-ancestry lower bound exactly. -/
theorem max_reciprocal_half_eq_two_div
    (total : ℝ) (htotal : 0 < total) :
    max (1 / (total / 2)) (1 / (total / 2)) = 2 / total := by
  rw [max_self]
  field_simp

end BinaryDeploymentBoundary

end Calibrator
