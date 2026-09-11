/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation
import Descent.Portability.ReportFiniteCalibrationLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real

assert_below Descent.Decision Descent.Program

/-!
# The individual-level report law of an admixture chronology

A one-way admixture history without drift, mutation or selection leaves a deterministic
haploid recipient whose two linked loci occupy exactly four genotype cells. Writing `p` for
the donor ancestry fraction shared by both loci and `C` for the normalised coupling
`D / (p * (1 - p))`, NOTE1 (31) gives the complete joint law of the pair (score, outcome).
This module defines that law as a `FiniteReportLaw (Bool × Bool)` and derives every entry of
the NOTE1 section 6.2 metric table from it.

The metric definitions are stated for an arbitrary report law on `Bool × Bool` rather than
only for the `(p, C)` cells, so finite-cohort and continuous-architecture modules can reuse
them. Where the corpus already fixes a metric the corpus declaration is used rather than
restated: `FiniteReportLaw.variance`, `covariance`, `squaredCorrelation`, `calibrationSlope`,
`meanSquaredError`, `binaryCaseMass`, `binaryAUCNumerator` and `binaryAUC` of
`ExactMetricEvaluation`, together with the half-credit tie convention of
`empiricalAUCComparison`. The definitions added here are the plain-valued calibration slope
and intercept, the population AUC ratio, the conditional outcome mean of a score cell, the
discrete calibration error, the affinely repaired Brier loss, the accuracy of a threshold
rule, and an extended-valued raw log loss.

Proved here: the four cell masses form a probability law; both marginal means equal `p`; both
variances equal `h = p * (1 - p)`; the covariance is `h * C`; the squared correlation is
`C ^ 2`; the calibration slope is `C` and the intercept `p * (1 - C)`; the conditional outcome
mean is `p * (1 - C) + C * s`, which is NOTE1 (32); the population AUC is `(1 + C) / 2`; the
Brier loss is `2 * h * (1 - C)`; the accuracy of any threshold strictly between zero and one
is `1 - 2 * h * (1 - C)`; the discrete calibration error is `2 * h * (1 - C)`; the repaired
Brier loss is `h * (1 - C ^ 2)`; both constraints of NOTE1 (34) hold; and the raw log loss is
the top element of the extended nonnegative reals whenever `0 < p < 1` and `C < 1`. The worked
table of NOTE1 section 6.2 at `p = 1 / 2` is checked at `C = 1 / 2` and at `C = 1`.

Not proved here: that a demographic history realises a given `(p, C)` pair. That is the
chronology side of the theorem, carried by `AdmixtureChronologyLaw` and
`AttainableChronologyCurve`. Nothing here asserts that any real scoring pipeline has this
two-locus law; the law is the stated model of NOTE1 section 6.1. Finite-cohort sampling from
this law is also out of scope and belongs to NOTE1 section 7.

## Empirical status

None. The bodies here are algebra: the four-cell admixture law is a stated mechanism with two
free parameters, and every theorem below is a polynomial identity in those parameters, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ChronologyReportLaw

noncomputable section

/-- The numeric value of one biallelic locus: one for the donor allele, zero for the
recipient allele. It is the allele value `ReportFiniteCalibrationLaw.allele` of the corpus. -/
def alleleValue (allele : Bool) : ℝ := ReportFiniteCalibrationLaw.allele allele

/-- The recipient allele contributes nothing. -/
@[simp] theorem alleleValue_false : alleleValue false = 0 := rfl

/-- The donor allele contributes one. -/
@[simp] theorem alleleValue_true : alleleValue true = 1 := rfl

/-- The score coordinate of an individual report: the left allele of NOTE1 section 6.1. -/
def scoreOf (report : Bool × Bool) : ℝ := alleleValue report.1

/-- The outcome coordinate of an individual report: the right allele of NOTE1 section 6.1. -/
def outcomeOf (report : Bool × Bool) : ℝ := alleleValue report.2

/-- The outcome viewed as a Boolean case indicator, the form the corpus binary AUC takes. -/
def caseOf (report : Bool × Bool) : Bool := report.2

/-- A recipient left allele scores zero whatever the right allele is. -/
@[simp] theorem scoreOf_false (allele : Bool) : scoreOf (false, allele) = 0 := rfl

/-- A donor left allele scores one whatever the right allele is. -/
@[simp] theorem scoreOf_true (allele : Bool) : scoreOf (true, allele) = 1 := rfl

/-- A recipient right allele is a zero outcome whatever the left allele is. -/
@[simp] theorem outcomeOf_false (allele : Bool) : outcomeOf (allele, false) = 0 := rfl

/-- A donor right allele is a unit outcome whatever the left allele is. -/
@[simp] theorem outcomeOf_true (allele : Bool) : outcomeOf (allele, true) = 1 := rfl

/-- The case indicator reads the right allele. -/
@[simp] theorem caseOf_mk (left right : Bool) : caseOf (left, right) = right := rfl

/-- The four cell masses of NOTE1 (31), as a function of the donor ancestry fraction `p` and
the normalised coupling `C`. The two concordant cells carry the independent product plus the
coupled excess `p * (1 - p) * C`; the two discordant cells share the deficit. -/
def chronologyMass (p C : ℝ) : Bool × Bool → ℝ
  | (false, false) => (1 - p) ^ 2 + p * (1 - p) * C
  | (false, true) => p * (1 - p) * (1 - C)
  | (true, false) => p * (1 - p) * (1 - C)
  | (true, true) => p ^ 2 + p * (1 - p) * C

/-- The doubly recipient cell. -/
@[simp] theorem chronologyMass_false_false (p C : ℝ) :
    chronologyMass p C (false, false) = (1 - p) ^ 2 + p * (1 - p) * C := rfl

/-- The recipient score with a donor outcome. -/
@[simp] theorem chronologyMass_false_true (p C : ℝ) :
    chronologyMass p C (false, true) = p * (1 - p) * (1 - C) := rfl

/-- The donor score with a recipient outcome. -/
@[simp] theorem chronologyMass_true_false (p C : ℝ) :
    chronologyMass p C (true, false) = p * (1 - p) * (1 - C) := rfl

/-- The doubly donor cell. -/
@[simp] theorem chronologyMass_true_true (p C : ℝ) :
    chronologyMass p C (true, true) = p ^ 2 + p * (1 - p) * C := rfl

/-- The complete individual-level law of NOTE1 (31) as a finite report law on the pair
(score, outcome). Nonnegativity uses `0 ≤ p ≤ 1` and `0 ≤ C ≤ 1`; the total mass is one for
every real `p` and `C`. -/
def chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    FiniteReportLaw (Bool × Bool) where
  mass := chronologyMass p C
  mass_nonneg := by
    have hprod : (0 : ℝ) ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
    have hgap : (0 : ℝ) ≤ 1 - C := by linarith
    rintro ⟨left, right⟩
    cases left <;> cases right <;>
      simp only [chronologyMass_false_false, chronologyMass_false_true,
        chronologyMass_true_false, chronologyMass_true_true]
    · exact add_nonneg (sq_nonneg _) (mul_nonneg hprod hC0)
    · exact mul_nonneg hprod hgap
    · exact mul_nonneg hprod hgap
    · exact add_nonneg (sq_nonneg _) (mul_nonneg hprod hC0)
  mass_sum := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, chronologyMass_false_false,
      chronologyMass_false_true, chronologyMass_true_false, chronologyMass_true_true]
    ring

/-- The masses of the chronology law are exactly the four cells. -/
@[simp] theorem chronologyLaw_mass (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (report : Bool × Bool) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).mass report = chronologyMass p C report := rfl

/-- Every expectation under a report law on two biallelic loci is the four-cell sum. -/
theorem expectation_cells (law : FiniteReportLaw (Bool × Bool)) (metric : Bool × Bool → ℝ) :
    law.expectation metric =
      law.mass (false, false) * metric (false, false) +
        law.mass (false, true) * metric (false, true) +
        law.mass (true, false) * metric (true, false) +
        law.mass (true, true) * metric (true, true) := by
  simp only [FiniteReportLaw.expectation, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The mean score is the donor ancestry fraction (NOTE1 section 6.1). -/
theorem expectation_scoreOf_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).expectation scoreOf = p := by
  simp [expectation_cells] <;> ring

/-- The mean outcome is the same donor ancestry fraction. -/
theorem expectation_outcomeOf_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).expectation outcomeOf = p := by
  simp [expectation_cells] <;> ring

/-- The mean outcome minus the mean score vanishes: the calibration gap of NOTE1 section 6.2
is exactly zero at every chronology. -/
theorem calibration_gap_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).expectation outcomeOf -
      (chronologyLaw p C hp0 hp1 hC0 hC1).expectation scoreOf = 0 := by
  rw [expectation_outcomeOf_chronologyLaw, expectation_scoreOf_chronologyLaw, sub_self]

/-- The score variance is `h = p * (1 - p)`. -/
theorem variance_scoreOf_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).variance scoreOf = p * (1 - p) := by
  simp [FiniteReportLaw.variance_eq_rawMoments, expectation_cells]
  ring

/-- The outcome variance is the same `h = p * (1 - p)`. -/
theorem variance_outcomeOf_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).variance outcomeOf = p * (1 - p) := by
  simp [FiniteReportLaw.variance_eq_rawMoments, expectation_cells]
  ring

/-- The score-outcome covariance is `h * C`: the coupling parameter is exactly the covariance
in units of the common variance. -/
theorem covariance_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).covariance scoreOf outcomeOf = p * (1 - p) * C := by
  simp [FiniteReportLaw.covariance_eq_rawMoments, expectation_cells]
  ring

/-- The population squared correlation is exactly `C ^ 2` (NOTE1 section 6.2). The
nondegeneracy premise `0 < p < 1` is what makes both variances positive, so the corpus
partial metric is defined. -/
theorem squaredCorrelation_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).squaredCorrelation scoreOf outcomeOf =
      some (C ^ 2) := by
  have hprod : (0 : ℝ) < p * (1 - p) := mul_pos hlow (by linarith)
  have hne : p * (1 - p) ≠ 0 := ne_of_gt hprod
  unfold FiniteReportLaw.squaredCorrelation
  rw [variance_scoreOf_chronologyLaw p C hp0 hp1 hC0 hC1,
    variance_outcomeOf_chronologyLaw p C hp0 hp1 hC0 hC1,
    covariance_chronologyLaw p C hp0 hp1 hC0 hC1, if_pos ⟨hprod, hprod⟩]
  congr 1
  rw [show (p * (1 - p) * C) ^ 2 = C ^ 2 * (p * (1 - p) * (p * (1 - p))) from by ring,
    mul_div_assoc, div_self (mul_ne_zero hne hne), mul_one]

/-- The least-squares calibration slope as a plain real number: the ratio the corpus
`FiniteReportLaw.calibrationSlope` wraps in its definedness branch. -/
def linearSlope (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  law.covariance scoreOf outcomeOf / law.variance scoreOf

/-- The least-squares calibration intercept: the mean outcome minus the slope times the mean
score. -/
def linearIntercept (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  law.expectation outcomeOf - linearSlope law * law.expectation scoreOf

/-- Assumes: the score is not almost surely constant. On that domain the corpus partial slope
is exactly the plain slope. -/
theorem calibrationSlope_eq_some_linearSlope (law : FiniteReportLaw (Bool × Bool))
    (hvar : 0 < law.variance scoreOf) :
    law.calibrationSlope scoreOf outcomeOf = some (linearSlope law) := by
  unfold FiniteReportLaw.calibrationSlope linearSlope
  rw [if_pos hvar]

/-- The calibration slope of the chronology law is the coupling parameter itself. -/
theorem linearSlope_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    linearSlope (chronologyLaw p C hp0 hp1 hC0 hC1) = C := by
  have hprod : (0 : ℝ) < p * (1 - p) := mul_pos hlow (by linarith)
  unfold linearSlope
  rw [variance_scoreOf_chronologyLaw p C hp0 hp1 hC0 hC1,
    covariance_chronologyLaw p C hp0 hp1 hC0 hC1, mul_comm (p * (1 - p)) C, mul_div_assoc,
    div_self (ne_of_gt hprod), mul_one]

/-- The corpus partial slope of the chronology law is `some C`. -/
theorem calibrationSlope_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).calibrationSlope scoreOf outcomeOf = some C := by
  have hprod : (0 : ℝ) < p * (1 - p) := mul_pos hlow (by linarith)
  have hvar : 0 < (chronologyLaw p C hp0 hp1 hC0 hC1).variance scoreOf := by
    rw [variance_scoreOf_chronologyLaw p C hp0 hp1 hC0 hC1]
    exact hprod
  rw [calibrationSlope_eq_some_linearSlope _ hvar,
    linearSlope_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh]

/-- The calibration intercept of the chronology law is `p * (1 - C)`. -/
theorem linearIntercept_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    linearIntercept (chronologyLaw p C hp0 hp1 hC0 hC1) = p * (1 - C) := by
  unfold linearIntercept
  rw [linearSlope_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    expectation_outcomeOf_chronologyLaw p C hp0 hp1 hC0 hC1,
    expectation_scoreOf_chronologyLaw p C hp0 hp1 hC0 hC1]
  ring

/-- The probability that the score takes a given allele value. -/
def scoreCellMass (law : FiniteReportLaw (Bool × Bool)) (allele : Bool) : ℝ :=
  law.expectation fun report ↦ if report.1 = allele then 1 else 0

/-- A score cell is the union of its two outcome cells. -/
theorem scoreCellMass_eq_cells (law : FiniteReportLaw (Bool × Bool)) (allele : Bool) :
    scoreCellMass law allele = law.mass (allele, false) + law.mass (allele, true) := by
  cases allele <;> simp [scoreCellMass, expectation_cells]

/-- The exact conditional outcome mean in one score cell: the joint mass of that cell with a
donor outcome divided by the mass of the cell. -/
def conditionalOutcomeMean (law : FiniteReportLaw (Bool × Bool)) (allele : Bool) : ℝ :=
  law.mass (allele, true) / scoreCellMass law allele

/-- NOTE1 (32): the conditional outcome mean is affine in the score, with slope the coupling
parameter and intercept `p * (1 - C)`. -/
theorem conditionalOutcomeMean_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (allele : Bool) :
    conditionalOutcomeMean (chronologyLaw p C hp0 hp1 hC0 hC1) allele =
      p * (1 - C) + C * alleleValue allele := by
  have hgap : (0 : ℝ) < 1 - p := by linarith
  unfold conditionalOutcomeMean
  cases allele
  · rw [scoreCellMass_eq_cells]
    simp only [chronologyLaw_mass, chronologyMass_false_false, chronologyMass_false_true,
      alleleValue_false]
    rw [show (1 - p) ^ 2 + p * (1 - p) * C + p * (1 - p) * (1 - C) = 1 - p from by ring,
      div_eq_iff (ne_of_gt hgap)]
    ring
  · rw [scoreCellMass_eq_cells]
    simp only [chronologyLaw_mass, chronologyMass_true_false, chronologyMass_true_true,
      alleleValue_true]
    rw [show p * (1 - p) * (1 - C) + (p ^ 2 + p * (1 - p) * C) = p from by ring,
      div_eq_iff (ne_of_gt hlow)]
    ring

/-- The case mass of the chronology law is the donor ancestry fraction. -/
theorem binaryCaseMass_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).binaryCaseMass caseOf = p := by
  simp [FiniteReportLaw.binaryCaseMass, expectation_cells]
  ring

/-- The unnormalised case-control ranking credit of the chronology law, with half credit for
ties, is `h * (1 + C) / 2`. -/
theorem binaryAUCNumerator_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).binaryAUCNumerator scoreOf caseOf =
      p * (1 - p) * (1 + C) / 2 := by
  norm_num [FiniteReportLaw.binaryAUCNumerator, expectation_cells,
    empiricalAUCComparison]
  ring

/-- Population AUC with half credit for ties: the corpus independent case-control numerator
divided by the product of the case and control masses. -/
def populationAUC (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  law.binaryAUCNumerator scoreOf caseOf /
    (law.binaryCaseMass caseOf * (1 - law.binaryCaseMass caseOf))

/-- Assumes: both outcome classes carry positive mass. On that domain the corpus partial AUC
is exactly the plain population AUC. -/
theorem binaryAUC_eq_some_populationAUC (law : FiniteReportLaw (Bool × Bool))
    (hcase : 0 < law.binaryCaseMass caseOf) (hcontrol : law.binaryCaseMass caseOf < 1) :
    law.binaryAUC scoreOf caseOf = some (populationAUC law) := by
  unfold populationAUC
  simp only [FiniteReportLaw.binaryAUC]
  rw [if_pos ⟨hcase, hcontrol⟩]

/-- The population AUC of the chronology law is `(1 + C) / 2` (NOTE1 section 6.2). -/
theorem populationAUC_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    populationAUC (chronologyLaw p C hp0 hp1 hC0 hC1) = (1 + C) / 2 := by
  have hprod : (0 : ℝ) < p * (1 - p) := mul_pos hlow (by linarith)
  unfold populationAUC
  rw [binaryAUCNumerator_chronologyLaw p C hp0 hp1 hC0 hC1,
    binaryCaseMass_chronologyLaw p C hp0 hp1 hC0 hC1, div_eq_iff (ne_of_gt hprod)]
  ring

/-- The raw Brier loss of the chronology law is `2 * h * (1 - C)`. -/
theorem meanSquaredError_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).meanSquaredError scoreOf outcomeOf =
      2 * (p * (1 - p)) * (1 - C) := by
  simp [FiniteReportLaw.meanSquaredError, expectation_cells]
  ring

/-- Accuracy of the rule that predicts the donor outcome exactly when the score exceeds a
threshold. -/
def thresholdAccuracy (law : FiniteReportLaw (Bool × Bool)) (threshold : ℝ) : ℝ :=
  law.expectation fun report ↦
    if threshold < scoreOf report then outcomeOf report else 1 - outcomeOf report

/-- Every threshold strictly between zero and one gives the same accuracy
`1 - 2 * h * (1 - C)` (NOTE1 section 6.2). -/
theorem thresholdAccuracy_chronologyLaw (p C threshold : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (ht0 : 0 < threshold) (ht1 : threshold < 1) :
    thresholdAccuracy (chronologyLaw p C hp0 hp1 hC0 hC1) threshold =
      1 - 2 * (p * (1 - p)) * (1 - C) := by
  have hbelow : ∀ x y : ℝ, (if threshold < (0 : ℝ) then x else y) = y :=
    fun x y ↦ if_neg (not_lt.mpr ht0.le)
  have habove : ∀ x y : ℝ, (if threshold < (1 : ℝ) then x else y) = x :=
    fun x y ↦ if_pos ht1
  unfold thresholdAccuracy
  simp [expectation_cells, hbelow, habove]
  ring

/-- Exact discrete calibration error: the mass-weighted distance between the conditional
outcome mean of each score cell and the score value of that cell. -/
def discreteECE (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  ∑ allele : Bool,
    scoreCellMass law allele * |conditionalOutcomeMean law allele - alleleValue allele|

/-- The discrete calibration error of the chronology law is `2 * h * (1 - C)`, numerically
equal to its Brier loss (NOTE1 section 6.2). -/
theorem discreteECE_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    discreteECE (chronologyLaw p C hp0 hp1 hC0 hC1) = 2 * (p * (1 - p)) * (1 - C) := by
  have hmean := conditionalOutcomeMean_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh
  have hrecipient : scoreCellMass (chronologyLaw p C hp0 hp1 hC0 hC1) false = 1 - p := by
    rw [scoreCellMass_eq_cells]
    simp only [chronologyLaw_mass, chronologyMass_false_false, chronologyMass_false_true]
    ring
  have hdonor : scoreCellMass (chronologyLaw p C hp0 hp1 hC0 hC1) true = p := by
    rw [scoreCellMass_eq_cells]
    simp only [chronologyLaw_mass, chronologyMass_true_false, chronologyMass_true_true]
    ring
  have hupper : p * (1 - C) + C * 1 - 1 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hC1)]
  have hlower : (0 : ℝ) ≤ p * (1 - C) + C * 0 - 0 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hC1)]
  unfold discreteECE
  rw [Fintype.sum_bool, hmean true, hmean false, hrecipient, hdonor]
  simp only [alleleValue_true, alleleValue_false]
  rw [abs_of_nonpos hupper, abs_of_nonneg hlower]
  ring

/-- Brier loss after the population-optimal affine repair of the score: the outcome variance
minus the explained part. -/
def repairedBrier (law : FiniteReportLaw (Bool × Bool)) : ℝ :=
  law.variance outcomeOf - law.covariance scoreOf outcomeOf ^ 2 / law.variance scoreOf

/-- The repaired Brier loss of the chronology law is `h * (1 - C ^ 2)`. -/
theorem repairedBrier_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    repairedBrier (chronologyLaw p C hp0 hp1 hC0 hC1) = p * (1 - p) * (1 - C ^ 2) := by
  have hprod : (0 : ℝ) < p * (1 - p) := mul_pos hlow (by linarith)
  unfold repairedBrier
  rw [variance_outcomeOf_chronologyLaw p C hp0 hp1 hC0 hC1,
    variance_scoreOf_chronologyLaw p C hp0 hp1 hC0 hC1,
    covariance_chronologyLaw p C hp0 hp1 hC0 hC1,
    show (p * (1 - p) * C) ^ 2 = p * (1 - p) * C ^ 2 * (p * (1 - p)) from by ring,
    mul_div_assoc, div_self (ne_of_gt hprod), mul_one]
  ring

/-- NOTE1 (34), first constraint: the squared calibration slope, and hence the squared
correlation, is determined by the AUC alone. -/
theorem linearSlope_sq_eq_auc_contrast (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    linearSlope (chronologyLaw p C hp0 hp1 hC0 hC1) ^ 2 =
      (2 * populationAUC (chronologyLaw p C hp0 hp1 hC0 hC1) - 1) ^ 2 := by
  rw [linearSlope_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    populationAUC_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh]
  ring

/-- NOTE1 (34), second constraint: the Brier loss is four times the variance times the AUC
deficit. -/
theorem meanSquaredError_eq_auc_deficit (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).meanSquaredError scoreOf outcomeOf =
      4 * (p * (1 - p)) * (1 - populationAUC (chronologyLaw p C hp0 hp1 hC0 hC1)) := by
  rw [meanSquaredError_chronologyLaw p C hp0 hp1 hC0 hC1,
    populationAUC_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh]
  ring

/-- The probability a hard zero-one score assigns to the outcome that was realised. -/
def reportedProbability (report : Bool × Bool) : ℝ :=
  if report.2 then scoreOf report else 1 - scoreOf report

/-- Negative log likelihood of one report in the extended nonnegative reals, taking the top
value at a zero predicted probability rather than silently truncating. -/
def extendedLogLoss (predicted : ℝ) : ENNReal :=
  if 0 < predicted then ENNReal.ofReal (-Real.log predicted) else ⊤

/-- Expected raw log loss of a report law, evaluated in the extended nonnegative reals. -/
def expectedLogLoss (law : FiniteReportLaw (Bool × Bool)) : ENNReal :=
  ∑ report, ENNReal.ofReal (law.mass report) * extendedLogLoss (reportedProbability report)

/-- The raw log loss of the chronology law diverges whenever the coupling is imperfect: the
cell with a donor score and a recipient outcome then has positive mass and zero predicted
probability, so the expected loss is the top element (NOTE1 section 6.2). -/
theorem expectedLogLoss_chronologyLaw_eq_top (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) (hloose : C < 1) :
    expectedLogLoss (chronologyLaw p C hp0 hp1 hC0 hC1) = ⊤ := by
  have hmass : (0 : ℝ) < p * (1 - p) * (1 - C) :=
    mul_pos (mul_pos hlow (by linarith)) (by linarith)
  have hzero : reportedProbability ((true, false) : Bool × Bool) = 0 := by
    simp [reportedProbability]
  have hloss : extendedLogLoss (reportedProbability ((true, false) : Bool × Bool)) = ⊤ := by
    rw [hzero]
    simp [extendedLogLoss]
  have hcell : ENNReal.ofReal ((chronologyLaw p C hp0 hp1 hC0 hC1).mass (true, false)) *
      extendedLogLoss (reportedProbability ((true, false) : Bool × Bool)) = ⊤ := by
    rw [hloss, chronologyLaw_mass, chronologyMass_true_false]
    exact ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hmass))
  refine top_le_iff.mp ?_
  rw [← hcell]
  exact Finset.single_le_sum
    (f := fun report ↦ ENNReal.ofReal ((chronologyLaw p C hp0 hp1 hC0 hC1).mass report) *
      extendedLogLoss (reportedProbability report))
    (fun report _ ↦ zero_le _) (Finset.mem_univ ((true, false) : Bool × Bool))

/-- The worked example of NOTE1 section 6.2 with `M = R = log 2` taken in the order migration
then recombination: half the target genome is donor derived and half the initial coupling
survives. -/
def halvedCouplingLaw : FiniteReportLaw (Bool × Bool) :=
  chronologyLaw (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The same demographic totals in the opposite order: the recipient is monomorphic while the
recombination happens, so the two loci arrive fully coupled. -/
def coupledLaw : FiniteReportLaw (Bool × Bool) :=
  chronologyLaw (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- NOTE1 section 6.2, the report table of the chronology law at an interior donor fraction:
squared correlation `C²`, AUC `(1 + C) / 2`, slope `C`, intercept `p (1 - C)`, Brier
`2h(1 - C)`, repaired Brier `h (1 - C²)`, accuracy `1 - 2h(1 - C)` at threshold one half, and
calibration error `2h(1 - C)`, where `h = p (1 - p)`. -/
theorem metric_values_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).squaredCorrelation scoreOf outcomeOf = some (C ^ 2) ∧
      populationAUC (chronologyLaw p C hp0 hp1 hC0 hC1) = (1 + C) / 2 ∧
        linearSlope (chronologyLaw p C hp0 hp1 hC0 hC1) = C ∧
          linearIntercept (chronologyLaw p C hp0 hp1 hC0 hC1) = p * (1 - C) ∧
            (chronologyLaw p C hp0 hp1 hC0 hC1).meanSquaredError scoreOf outcomeOf =
                2 * (p * (1 - p)) * (1 - C) ∧
              repairedBrier (chronologyLaw p C hp0 hp1 hC0 hC1) = p * (1 - p) * (1 - C ^ 2) ∧
                thresholdAccuracy (chronologyLaw p C hp0 hp1 hC0 hC1) (1 / 2) =
                    1 - 2 * (p * (1 - p)) * (1 - C) ∧
                  discreteECE (chronologyLaw p C hp0 hp1 hC0 hC1) =
                    2 * (p * (1 - p)) * (1 - C) :=
  ⟨squaredCorrelation_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    populationAUC_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    linearSlope_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    linearIntercept_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    meanSquaredError_chronologyLaw p C hp0 hp1 hC0 hC1,
    repairedBrier_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    thresholdAccuracy_chronologyLaw p C (1 / 2) hp0 hp1 hC0 hC1 (by norm_num) (by norm_num),
    discreteECE_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh⟩

/-- The first column of the NOTE1 section 6.2 table: squared correlation one quarter, AUC
three quarters, slope one half, intercept one quarter, Brier one quarter, repaired Brier three
sixteenths, accuracy three quarters, calibration error one quarter. -/
theorem metric_values_halvedCoupling :
    halvedCouplingLaw.squaredCorrelation scoreOf outcomeOf = some (1 / 4) ∧
      populationAUC halvedCouplingLaw = 3 / 4 ∧
        linearSlope halvedCouplingLaw = 1 / 2 ∧
          linearIntercept halvedCouplingLaw = 1 / 4 ∧
            halvedCouplingLaw.meanSquaredError scoreOf outcomeOf = 1 / 4 ∧
              repairedBrier halvedCouplingLaw = 3 / 16 ∧
                thresholdAccuracy halvedCouplingLaw (1 / 2) = 3 / 4 ∧
                  discreteECE halvedCouplingLaw = 1 / 4 := by
  obtain ⟨hcorrelation, hauc, hslope, hoffset, hbrier, hrepaired, haccuracy,
    hcalibration⟩ := metric_values_chronologyLaw (1 / 2) (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hcorrelation.trans (by norm_num), hauc.trans (by norm_num),
    hslope.trans (by norm_num), hoffset.trans (by norm_num), hbrier.trans (by norm_num),
    hrepaired.trans (by norm_num), haccuracy.trans (by norm_num),
    hcalibration.trans (by norm_num)⟩

/-- The second column of the NOTE1 section 6.2 table: a perfectly coupled pair of loci gives
squared correlation one, AUC one, slope one, intercept zero, and vanishing Brier, repaired
Brier and calibration error, with accuracy one. -/
theorem metric_values_coupled :
    coupledLaw.squaredCorrelation scoreOf outcomeOf = some 1 ∧
      populationAUC coupledLaw = 1 ∧
        linearSlope coupledLaw = 1 ∧
          linearIntercept coupledLaw = 0 ∧
            coupledLaw.meanSquaredError scoreOf outcomeOf = 0 ∧
              repairedBrier coupledLaw = 0 ∧
                thresholdAccuracy coupledLaw (1 / 2) = 1 ∧ discreteECE coupledLaw = 0 := by
  obtain ⟨hcorrelation, hauc, hslope, hoffset, hbrier, hrepaired, haccuracy,
    hcalibration⟩ := metric_values_chronologyLaw (1 / 2) 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hcorrelation.trans (by norm_num), hauc.trans (by norm_num),
    hslope.trans (by norm_num), hoffset.trans (by norm_num), hbrier.trans (by norm_num),
    hrepaired.trans (by norm_num), haccuracy.trans (by norm_num),
    hcalibration.trans (by norm_num)⟩

end

end Descent.Portability.ChronologyReportLaw
