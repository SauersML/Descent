/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ThresholdPolicyTransport

assert_below Descent.Decision Descent.Program

/-!
# Metric agreement, binary feasibility, and decision order: converses

All statements concern the same score/outcome or confusion law. Their domains
exclude the undefined denominators. Binary feasibility constructs a normalized
confusion law, and decision dominance quantifies over every positive cost pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MetricOrderingClassification

open Foundations

noncomputable section

variable {Ω J L : Type*} [Fintype J] [Fintype L]

/-- Exact separation into affine-optimal error, slope error, and mean error. -/
theorem affine_mse_completed_square (P : DeploymentPopulation Ω J L) (w : J → ℝ)
    (hu : 0 < P.scoreVariance w) (a b : ℝ) :
    expMse P.E P.phenotype (P.recalibratedScore w a b) =
      P.outcomeVariance * (1 - P.r2 w) +
      P.scoreVariance w * (b - P.calibrationSlope w) ^ 2 +
      (P.E P.phenotype - a - b * P.E (P.score w)) ^ 2 := by
  rw [P.recalibrated_mse_eq]
  unfold DeploymentPopulation.r2 DeploymentPopulation.calibrationSlope
  rw [DeploymentPopulation.outcomeVariance_mul_one_sub_ratio
    P.outcomeVariance (P.predictiveCovariance w) (P.scoreVariance w)
    hu.ne' (P.predictiveCovariance_sq_le w)]
  field_simp
  ring

/-- Necessary and sufficient MSE comparison, including unequal outcome variance
and arbitrary calibration. The penalty is measured, not presumed to vanish. -/
theorem affine_mse_order_iff
    (P Q : DeploymentPopulation Ω J L) (w : J → ℝ)
    (hP : 0 < P.scoreVariance w) (hQ : 0 < Q.scoreVariance w)
    (aP bP aQ bQ : ℝ) :
    expMse P.E P.phenotype (P.recalibratedScore w aP bP) ≤
      expMse Q.E Q.phenotype (Q.recalibratedScore w aQ bQ) ↔
      P.scoreVariance w * (bP - P.calibrationSlope w) ^ 2 +
        (P.E P.phenotype - aP - bP * P.E (P.score w)) ^ 2 -
        (Q.scoreVariance w * (bQ - Q.calibrationSlope w) ^ 2 +
          (Q.E Q.phenotype - aQ - bQ * Q.E (Q.score w)) ^ 2) ≤
      Q.outcomeVariance * (1 - Q.r2 w) - P.outcomeVariance * (1 - P.r2 w) := by
  rw [affine_mse_completed_square P w hP, affine_mse_completed_square Q w hQ]
  constructor <;> intro h <;> linarith

/-- Equal outcome variance and individually optimal affine calibration force
the MSE ordering to be exactly the reverse of the squared-correlation ordering. -/
theorem calibrated_equal_variance_order_iff
    (P Q : DeploymentPopulation Ω J L) (w : J → ℝ)
    (hP : 0 < P.scoreVariance w) (hQ : 0 < Q.scoreVariance w)
    (hv : P.outcomeVariance = Q.outcomeVariance) (hvpos : 0 < P.outcomeVariance) :
    expMse P.E P.phenotype (P.bestAffineScore w) ≤
      expMse Q.E Q.phenotype (Q.bestAffineScore w) ↔ Q.r2 w ≤ P.r2 w := by
  rw [P.bestAffine_mse_eq w hP.ne', Q.bestAffine_mse_eq w hQ.ne', ← hv,
    mul_le_mul_iff_right₀ hvpos]
  constructor <;> intro h <;> linarith

/-- Construct every feasible prevalence/recall/FPR table. -/
def operatingLaw (pi r f : ℝ) (hpi : 0 ≤ pi ∧ pi ≤ 1)
    (hr : 0 ≤ r ∧ r ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1) : ConfusionMatrix where
  tp := pi * r
  fp := (1 - pi) * f
  tn := (1 - pi) * (1 - f)
  fn := pi * (1 - r)
  tp_nonneg := mul_nonneg hpi.1 hr.1
  fp_nonneg := mul_nonneg (sub_nonneg.mpr hpi.2) hf.1
  tn_nonneg := mul_nonneg (sub_nonneg.mpr hpi.2) (sub_nonneg.mpr hf.2)
  fn_nonneg := mul_nonneg hpi.1 (sub_nonneg.mpr hr.2)
  mass_one := by ring

/-- The constant-precision equation is equivalent to the unique required FPR. -/
theorem precision_eq_iff_fpr (pi p r f : ℝ)
    (hpi : 0 < pi) (hpi1 : pi < 1) (hp : 0 < p)
    (hr : 0 < r) (hf : 0 ≤ f) :
    pi * r / (pi * r + (1 - pi) * f) = p ↔
      f = pi * r * (1 - p) / ((1 - pi) * p) := by
  have hpic : 0 < 1 - pi := sub_pos.mpr hpi1
  have hd : 0 < pi * r + (1 - pi) * f := by positivity
  have he : 0 < (1 - pi) * p := by positivity
  rw [div_eq_iff hd.ne', eq_div_iff he.ne']
  constructor <;> intro h <;> nlinarith

/-- Exact feasible recall range for a nondegenerate constant precision.
This is a converse and an existence theorem, not just a particular example. -/
theorem constant_precision_feasible_iff (pi p r : ℝ)
    (hpi : 0 < pi) (hpi1 : pi < 1) (hp : 0 < p) (hp1 : p < 1) :
    (∃ f : ℝ, 0 ≤ f ∧ f ≤ 1 ∧ 0 < r ∧ r ≤ 1 ∧
      pi * r / (pi * r + (1 - pi) * f) = p) ↔
    0 < r ∧ r ≤ min 1 ((1 - pi) * p / (pi * (1 - p))) := by
  have hpic : 0 < 1 - pi := sub_pos.mpr hpi1
  have hpc : 0 < 1 - p := sub_pos.mpr hp1
  have hd : 0 < (1 - pi) * p := by positivity
  have he : 0 < pi * (1 - p) := by positivity
  constructor
  · rintro ⟨f, hf, hf1, hr, hr1, hpv⟩
    have hfe := (precision_eq_iff_fpr pi p r f hpi hpi1 hp hr hf).mp hpv
    refine ⟨hr, le_min hr1 ?_⟩
    rw [hfe, div_le_one hd] at hf1
    apply (le_div_iff₀ he).mpr
    nlinarith
  · rintro ⟨hr, hrange⟩
    let f := pi * r * (1 - p) / ((1 - pi) * p)
    have hf : 0 ≤ f := by dsimp [f]; positivity
    have hf1 : f ≤ 1 := by
      apply (div_le_one hd).mpr
      have h := (le_div_iff₀ he).mp (le_trans hrange (min_le_right _ _))
      nlinarith
    exact ⟨f, hf, hf1, hr, le_trans hrange (min_le_left _ _),
      (precision_eq_iff_fpr pi p r f hpi hpi1 hp hr hf).mpr rfl⟩

/-- Every feasible point is attained by an actual normalized confusion law.
`common_threshold_realizes` below realizes it with a binary score at cutoff 1/2. -/
theorem realizable_constant_precision (pi p r : ℝ)
    (hpi : 0 < pi) (hpi1 : pi < 1) (hp : 0 < p) (hp1 : p < 1)
    (hr : 0 < r) (hrange : r ≤ min 1 ((1 - pi) * p / (pi * (1 - p)))) :
    ∃ c : ConfusionMatrix, c.prevalence = pi ∧ c.recallRate = r ∧
      c.precision = p ∧ 0 < c.tp + c.fp := by
  obtain ⟨f, hf, hf1, _, hr1, hprecision⟩ :=
    (constant_precision_feasible_iff pi p r hpi hpi1 hp hp1).mpr ⟨hr, hrange⟩
  refine ⟨operatingLaw pi r f ⟨hpi.le, hpi1.le⟩ ⟨hr.le, hr1⟩ ⟨hf, hf1⟩, ?_⟩
  have hmargin : pi * r + pi * (1 - r) = pi := by ring
  change pi * r + pi * (1 - r) = pi ∧
    pi * r / (pi * r + pi * (1 - r)) = r ∧
    pi * r / (pi * r + (1 - pi) * f) = p ∧ 0 < pi * r + (1 - pi) * f
  refine ⟨hmargin, ?_, hprecision, ?_⟩
  · rw [hmargin]
    field_simp
  · have hpic : 0 < 1 - pi := sub_pos.mpr hpi1
    positivity

/-- Every normalized table is the law of a binary score and binary outcome. -/
def confusionLaw (c : ConfusionMatrix) : ExpFunctional (Bool × Bool) :=
  weightedExp (fun z ↦ if z.1 then (if z.2 then c.tp else c.fp)
    else (if z.2 then c.fn else c.tn))
    (by
      rintro ⟨a, b⟩
      cases a <;> cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact c.tn_nonneg
      · exact c.fn_nonneg
      · exact c.fp_nonneg
      · exact c.tp_nonneg)
    (by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
      linarith [c.mass_one])

/-- Realizability uses the same fixed threshold 1/2 for every feasible law.
Thus the feasibility theorem is about genuine thresholded scores, not free
numbers that might fail to be jointly attainable. -/
theorem common_threshold_realizes (c : ConfusionMatrix) :
    let realized := ThresholdPolicyTransport.thresholdCells (confusionLaw c)
      (fun z ↦ if z.1 then 1 else 0) (fun z ↦ z.2) (1 / 2)
    realized.tp = c.tp ∧ realized.fp = c.fp ∧ realized.tn = c.tn ∧ realized.fn = c.fn := by
  norm_num [ThresholdPolicyTransport.thresholdCells, ThresholdPolicyTransport.decisionCells,
    confusionLaw, weightedExp_apply, Fintype.sum_prod_type, Fintype.sum_bool]

/-- No worse for every positive cost pair iff neither error probability is
larger. The reverse implication derives coordinate dominance by varying costs. -/
theorem all_costs_dominance_iff (A B : ConfusionMatrix) :
    (∀ fpCost fnCost : ℝ, 0 < fpCost → 0 < fnCost →
      fpCost * A.fp + fnCost * A.fn ≤ fpCost * B.fp + fnCost * B.fn) ↔
      A.fp ≤ B.fp ∧ A.fn ≤ B.fn := by
  constructor
  · intro h
    constructor
    · by_contra hn
      have hd : 0 < A.fp - B.fp := sub_pos.mpr (lt_of_not_ge hn)
      let c := (|B.fn - A.fn| + 1) / (A.fp - B.fp)
      have hc : 0 < c := by dsimp [c]; positivity
      have hh := h c 1 hc (by norm_num)
      have he : c * (A.fp - B.fp) = |B.fn - A.fn| + 1 := by
        dsimp [c]
        field_simp
      nlinarith [le_abs_self (B.fn - A.fn)]
    · by_contra hn
      have hd : 0 < A.fn - B.fn := sub_pos.mpr (lt_of_not_ge hn)
      let c := (|B.fp - A.fp| + 1) / (A.fn - B.fn)
      have hc : 0 < c := by dsimp [c]; positivity
      have hh := h 1 c (by norm_num) hc
      have he : c * (A.fn - B.fn) = |B.fp - A.fp| + 1 := by
        dsimp [c]
        field_simp
      nlinarith [le_abs_self (B.fp - A.fp)]
  · rintro ⟨hfp, hfn⟩ fpCost fnCost hfpCost hfnCost
    exact add_le_add (mul_le_mul_of_nonneg_left hfp hfpCost.le)
      (mul_le_mul_of_nonneg_left hfn hfnCost.le)

end

end Descent.Portability.MetricOrderingClassification
