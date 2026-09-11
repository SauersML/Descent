/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SublawReportCertificate
import Descent.Portability.PositiveRatioExpansion
import Descent.Portability.BellmanReportBounds

assert_below Descent.Decision Descent.Program

/-!
# Coupled numerator and definedness certification for the replica-domain compiler

Truncating the positive ratio expansion after finitely many replica coefficients leaves two
unresolved quantities that must be controlled together: the discarded numerator and the
discarded definedness mass. NOTE 2 section 5.2 observes that they are coupled, that the
discarded numerator never exceeds the discarded definedness mass, and that a single upper
bound on the latter therefore certifies the normalized metric.

`retainedNumerator` and `retainedMass` are NOTE 2 equation (16). `unresolvedNumerator` and
`unresolvedMass` are the two remainders, given here in closed form rather than as tails of a
series: the discarded numerator is the expectation of the metric itself damped by the
denominator deficit raised to the truncation order. `ratio_expectation_partition` and
`defined_mass_partition` prove that the retained and unresolved parts reconstitute the
metric expectation and the definedness probability exactly, with no approximation anywhere.

`unresolvedNumerator_le_unresolvedMass` is the coupling of NOTE 2 equation (17), and
`replica_certificate` is Theorem 4, NOTE 2 equation (18): with any tolerance dominating the
unresolved definedness mass and positive retained mass, the conditional expectation of the
metric on the defined event is enclosed by two explicit ratios of retained quantities. It is
obtained from `SublawReportCertificate.ratio_bounds` with value interval zero to one, which
is legitimate precisely because the metric is a bounded ratio. `certificate_width` is the
exact width claim of the same equation and `unresolvedMass_le_pow` is equation (19), the
geometric tolerance available when the denominator is bounded below on its defined event.

Scope: the population is a finite report law, so every expectation is a finite sum and no
convergence hypothesis is needed. The measure-theoretic form of the same certificate, over an
arbitrary probability measure, is not proved here; the expansion it would rest on is
`PositiveRatioExpansion.integral_ratioOnDefined_eq_tsum`. The polynomial-degree accounting of
NOTE 2 section 5.4, which counts the replicas each coefficient consumes, is also not
formalized: nothing here refers to how a coefficient is estimated.

## Empirical status

None. The bodies here are algebra: retained and unresolved quantities are finite sums fixed
by the report law and the two functionals, and every claim is an identity or an inequality
between them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReplicaDomainCertificate

open SublawReportCertificate PositiveRatioExpansion

/-- The partial sum of powers of the denominator deficit, scaled by the denominator, is the
definedness mass the first `terms` replica coefficients resolve. -/
theorem deficit_partial_sum (den : ℝ) (terms : ℕ) :
    (∑ power ∈ Finset.range terms, (1 - den) ^ power) * den = 1 - (1 - den) ^ terms := by
  have hmul := geom_sum_mul (1 - den) terms
  have hshift : (1 : ℝ) - den - 1 = -den := by ring
  rw [hshift] at hmul
  linarith

/-- **NOTE 2 equation (16), pointwise.** A ratio whose numerator is the denominator times the
ratio is the sum of its first `terms` expansion coefficients plus the ratio damped by the
denominator deficit raised to the truncation order. No positivity and no case split on a
vanishing denominator are needed: the identity is the telescoping of the partial geometric
sum. -/
theorem geometric_partition (den ratio : ℝ) (terms : ℕ) :
    ratio = (∑ power ∈ Finset.range terms, den * ratio * (1 - den) ^ power) +
      ratio * (1 - den) ^ terms := by
  have hpull : ∑ power ∈ Finset.range terms, den * ratio * (1 - den) ^ power =
      den * ratio * ∑ power ∈ Finset.range terms, (1 - den) ^ power :=
    (Finset.mul_sum _ _ _).symm
  have hkey : den * ratio * (∑ power ∈ Finset.range terms, (1 - den) ^ power) =
      ratio * (1 - (1 - den) ^ terms) := by
    rw [← deficit_partial_sum den terms]
    ring
  rw [hpull, hkey]
  ring

/-- The partial expansion of a numerator dominated by its denominator never exceeds the
definedness mass the same truncation resolves. -/
theorem partial_numerator_le (num den : ℝ) (hnum : 0 ≤ num) (hle : num ≤ den)
    (hden : den ≤ 1) (terms : ℕ) :
    ∑ power ∈ Finset.range terms, num * (1 - den) ^ power ≤ 1 - (1 - den) ^ terms := by
  have hnonneg : 0 ≤ ∑ power ∈ Finset.range terms, (1 - den) ^ power :=
    Finset.sum_nonneg fun power _ ↦ pow_nonneg (by linarith) power
  have hstep := mul_le_mul_of_nonneg_right hle hnonneg
  rw [← Finset.mul_sum, ← deficit_partial_sum den terms]
  linarith

variable {Report : Type*} [Fintype Report]

/-- A report statistic bounded above by a constant has expectation below that constant. -/
theorem expectation_le_const (law : FiniteReportLaw Report) (value : Report → ℝ) (bound : ℝ)
    (hbound : ∀ report, value report ≤ bound) : law.expectation value ≤ bound := by
  calc law.expectation value ≤ law.expectation (fun _ ↦ bound) :=
        BellmanReportBounds.expectation_mono law value (fun _ ↦ bound) hbound
    _ = bound := FiniteIndependentMoments.expectation_const law bound

/-- A nonnegative report statistic has nonnegative expectation. -/
theorem expectation_nonneg (law : FiniteReportLaw Report) (value : Report → ℝ)
    (hvalue : ∀ report, 0 ≤ value report) : 0 ≤ law.expectation value := by
  calc (0 : ℝ) = law.expectation (fun _ ↦ (0 : ℝ)) :=
        (FiniteIndependentMoments.expectation_const law 0).symm
    _ ≤ law.expectation value :=
        BellmanReportBounds.expectation_mono law (fun _ ↦ (0 : ℝ)) value hvalue

/-- The denominator times the metric recovers the numerator, including where the denominator
vanishes, since the numerator vanishes with it. -/
theorem den_mul_ratioOnDefined (num den : Report → ℝ) (hnum : ∀ report, 0 ≤ num report)
    (hle : ∀ report, num report ≤ den report) (report : Report) :
    den report * ratioOnDefined num den report = num report := by
  unfold ratioOnDefined
  split_ifs with hpos
  · have hne : den report ≠ 0 := ne_of_gt hpos
    field_simp
  · have hdenzero : den report = 0 :=
      le_antisymm (not_lt.mp hpos) (le_trans (hnum report) (hle report))
    have hnumzero : num report = 0 := by
      have hstep := hle report
      rw [hdenzero] at hstep
      exact le_antisymm hstep (hnum report)
    rw [hnumzero, mul_zero]

/-- **NOTE 2 equation (16).** The retained replica numerator: the first `terms` coefficients
of the positive ratio expansion, each a polynomial functional of the report law. -/
noncomputable def retainedNumerator (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (terms : ℕ) : ℝ :=
  ∑ power ∈ Finset.range terms,
    law.expectation (fun report ↦ num report * (1 - den report) ^ power)

/-- **NOTE 2 equation (16).** The definedness mass the first `terms` coefficients resolve. -/
noncomputable def retainedMass (law : FiniteReportLaw Report) (den : Report → ℝ)
    (terms : ℕ) : ℝ :=
  law.expectation (fun report ↦ 1 - (1 - den report) ^ terms)

/-- The numerator a truncation leaves unresolved, in closed form: the metric itself damped by
the denominator deficit raised to the truncation order. -/
noncomputable def unresolvedNumerator (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (terms : ℕ) : ℝ :=
  law.expectation (fun report ↦ ratioOnDefined num den report * (1 - den report) ^ terms)

/-- **NOTE 2 equation (17).** The definedness mass a truncation leaves unresolved. -/
noncomputable def unresolvedMass (law : FiniteReportLaw Report) (den : Report → ℝ)
    (terms : ℕ) : ℝ :=
  law.expectation (fun report ↦
    definedIndicator (fun other ↦ 0 < den other) report * (1 - den report) ^ terms)

/-- **NOTE 2 equation (16).** The exact expectation of the ratio metric is the retained
replica numerator plus the unresolved numerator, with no approximation. -/
theorem ratio_expectation_partition (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (hnum : ∀ report, 0 ≤ num report) (hle : ∀ report, num report ≤ den report) (terms : ℕ) :
    law.expectation (ratioOnDefined num den) =
      retainedNumerator law num den terms + unresolvedNumerator law num den terms := by
  simp only [retainedNumerator, unresolvedNumerator, FiniteReportLaw.expectation]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  rw [← Finset.mul_sum, ← mul_add]
  congr 1
  have hprod := den_mul_ratioOnDefined num den hnum hle report
  rw [← hprod]
  exact geometric_partition (den report) (ratioOnDefined num den report) terms

/-- **NOTE 2 equations (16) and (17).** The exact definedness probability is the retained
mass plus the unresolved mass. -/
theorem defined_mass_partition (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hden : ∀ report, 0 ≤ den report) (terms : ℕ) :
    law.expectation (definedIndicator (fun other ↦ 0 < den other)) =
      retainedMass law den terms + unresolvedMass law den terms := by
  simp only [retainedMass, unresolvedMass, FiniteReportLaw.expectation]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  rw [← mul_add]
  congr 1
  by_cases hpos : 0 < den report
  · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 1 := by
      simp [definedIndicator, hpos]
    rw [hindicator]
    ring
  · have hzero : den report = 0 := le_antisymm (not_lt.mp hpos) (hden report)
    have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 0 := by
      simp [definedIndicator, hpos]
    rw [hindicator, hzero]
    simp

/-- The definedness indicator is idle against the metric, which already reads as zero off the
defined event. -/
theorem defined_ratio_expectation (law : FiniteReportLaw Report) (num den : Report → ℝ) :
    law.expectation (fun report ↦ definedIndicator (fun other ↦ 0 < den other) report *
        ratioOnDefined num den report) =
      law.expectation (ratioOnDefined num den) := by
  simp only [FiniteReportLaw.expectation]
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  congr 1
  by_cases hpos : 0 < den report <;> simp [definedIndicator, ratioOnDefined, hpos]

/-- The retained replica numerator is nonnegative. -/
theorem retainedNumerator_nonneg (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (hnum : ∀ report, 0 ≤ num report) (hden : ∀ report, den report ≤ 1) (terms : ℕ) :
    0 ≤ retainedNumerator law num den terms :=
  Finset.sum_nonneg fun power _ ↦ expectation_nonneg law _ fun report ↦
    mul_nonneg (hnum report) (pow_nonneg (by linarith [hden report]) power)

/-- The retained replica numerator never exceeds the retained definedness mass, which is what
makes the value interval zero to one the right one for the normalized certificate. -/
theorem retainedNumerator_le_retainedMass (law : FiniteReportLaw Report)
    (num den : Report → ℝ) (hnum : ∀ report, 0 ≤ num report)
    (hle : ∀ report, num report ≤ den report) (hden : ∀ report, den report ≤ 1) (terms : ℕ) :
    retainedNumerator law num den terms ≤ retainedMass law den terms := by
  have hcollapse : retainedNumerator law num den terms =
      law.expectation (fun report ↦
        ∑ power ∈ Finset.range terms, num report * (1 - den report) ^ power) := by
    simp only [retainedNumerator, FiniteReportLaw.expectation]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun report _ ↦ (Finset.mul_sum _ _ _).symm
  rw [hcollapse, retainedMass]
  refine BellmanReportBounds.expectation_mono law _ _ fun report ↦ ?_
  exact partial_numerator_le (num report) (den report) (hnum report) (hle report)
    (hden report) terms

/-- The unresolved numerator is nonnegative. -/
theorem unresolvedNumerator_nonneg (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (hnum : ∀ report, 0 ≤ num report) (hden : ∀ report, den report ≤ 1) (terms : ℕ) :
    0 ≤ unresolvedNumerator law num den terms :=
  expectation_nonneg law _ fun report ↦
    mul_nonneg (ratioOnDefined_nonneg num den hnum report)
      (pow_nonneg (by linarith [hden report]) terms)

/-- The unresolved definedness mass is nonnegative. -/
theorem unresolvedMass_nonneg (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hden : ∀ report, den report ≤ 1) (terms : ℕ) : 0 ≤ unresolvedMass law den terms :=
  expectation_nonneg law _ fun report ↦
    mul_nonneg (definedIndicator_nonneg (fun other ↦ 0 < den other) report)
      (pow_nonneg (by linarith [hden report]) terms)

/-- **NOTE 2 equation (17).** The numerator a truncation discards never exceeds the
definedness mass it discards. This is the coupling that lets one tolerance certify both. -/
theorem unresolvedNumerator_le_unresolvedMass (law : FiniteReportLaw Report)
    (num den : Report → ℝ) (hle : ∀ report, num report ≤ den report)
    (hden : ∀ report, den report ≤ 1) (terms : ℕ) :
    unresolvedNumerator law num den terms ≤ unresolvedMass law den terms := by
  unfold unresolvedNumerator unresolvedMass
  refine BellmanReportBounds.expectation_mono law _ _ fun report ↦ ?_
  have hdeficit : (0 : ℝ) ≤ (1 - den report) ^ terms :=
    pow_nonneg (by linarith [hden report]) terms
  have hdominated : ratioOnDefined num den report ≤
      definedIndicator (fun other ↦ 0 < den other) report := by
    by_cases hpos : 0 < den report
    · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 1 := by
        simp [definedIndicator, hpos]
      rw [hindicator]
      exact ratioOnDefined_le_one num den hle report
    · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 0 := by
        simp [definedIndicator, hpos]
      have hmetric : ratioOnDefined num den report = 0 := by
        simp [ratioOnDefined, hpos]
      rw [hindicator, hmetric]
  exact mul_le_mul_of_nonneg_right hdominated hdeficit

/-- **NOTE 2 equation (18), Theorem 4.** The normalization-aware replica certificate: with a
tolerance dominating the unresolved definedness mass and positive retained mass, the
conditional expectation of the bounded ratio metric on the defined event is enclosed between
the retained numerator and the retained numerator increased by the tolerance, both over the
retained mass increased by the tolerance. Only retained quantities and the tolerance appear
in the bounds, so the enclosure is computable from finitely many replica coefficients. -/
theorem replica_certificate (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (hnum : ∀ report, 0 ≤ num report) (hle : ∀ report, num report ≤ den report)
    (hden : ∀ report, den report ≤ 1) (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass law den terms ≤ tolerance)
    (hretained : 0 < retainedMass law den terms) :
    retainedNumerator law num den terms / (retainedMass law den terms + tolerance) ≤
        conditionalExpectation law (fun other ↦ 0 < den other) (ratioOnDefined num den) ∧
      conditionalExpectation law (fun other ↦ 0 < den other) (ratioOnDefined num den) ≤
        (retainedNumerator law num den terms + tolerance) /
          (retainedMass law den terms + tolerance) := by
  have hdenNonneg : ∀ report, 0 ≤ den report := fun report ↦
    le_trans (hnum report) (hle report)
  have hretainedNonneg := retainedNumerator_nonneg law num den hnum hden terms
  have hretainedLe := retainedNumerator_le_retainedMass law num den hnum hle hden terms
  have hunresolvedNonneg := unresolvedNumerator_nonneg law num den hnum hden terms
  have hunresolvedLe := unresolvedNumerator_le_unresolvedMass law num den hle hden terms
  have hmassNonneg := unresolvedMass_nonneg law den hden terms
  obtain ⟨hlow, hhigh⟩ := ratio_bounds 0 1 (retainedMass law den terms)
    (retainedNumerator law num den terms) (unresolvedMass law den terms)
    (unresolvedNumerator law num den terms) tolerance hretained hmassNonneg htolerance
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hconditional : conditionalExpectation law (fun other ↦ 0 < den other)
      (ratioOnDefined num den) =
        (retainedNumerator law num den terms + unresolvedNumerator law num den terms) /
          (retainedMass law den terms + unresolvedMass law den terms) := by
    unfold conditionalExpectation
    rw [defined_ratio_expectation law num den,
      ratio_expectation_partition law num den hnum hle terms,
      defined_mass_partition law den hdenNonneg terms]
  rw [hconditional]
  exact ⟨by simpa using hlow, by simpa using hhigh⟩

/-- **NOTE 2 equation (18), width.** The certified interval has width exactly the tolerance
over the retained mass increased by the tolerance, and that width is nonnegative. -/
theorem certificate_width (law : FiniteReportLaw Report) (num den : Report → ℝ) (terms : ℕ)
    (tolerance : ℝ) (htolerance : 0 ≤ tolerance)
    (hretained : 0 < retainedMass law den terms) :
    (retainedNumerator law num den terms + tolerance) /
          (retainedMass law den terms + tolerance) -
        retainedNumerator law num den terms / (retainedMass law den terms + tolerance) =
      tolerance / (retainedMass law den terms + tolerance) ∧
    0 ≤ tolerance / (retainedMass law den terms + tolerance) := by
  constructor
  · rw [div_sub_div_same]
    congr 1
    ring
  · exact div_nonneg htolerance (by linarith)

/-- **NOTE 2 equation (19).** A denominator bounded below by a positive floor wherever it is
defined makes the unresolved definedness mass decay geometrically in the truncation order, so
the tolerance of the certificate can be taken to be that geometric bound. -/
theorem unresolvedMass_le_pow (law : FiniteReportLaw Report) (den : Report → ℝ)
    (denFloor : ℝ) (hfloorNonneg : 0 ≤ denFloor) (hfloorLeOne : denFloor ≤ 1)
    (hfloor : ∀ report, 0 < den report → denFloor ≤ den report)
    (hden : ∀ report, den report ≤ 1) (terms : ℕ) :
    unresolvedMass law den terms ≤ (1 - denFloor) ^ terms := by
  unfold unresolvedMass
  refine expectation_le_const law _ _ fun report ↦ ?_
  by_cases hpos : 0 < den report
  · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 1 := by
      simp [definedIndicator, hpos]
    rw [hindicator, one_mul]
    exact pow_le_pow_left₀ (by linarith [hden report])
      (by linarith [hfloor report hpos]) terms
  · have hindicator : definedIndicator (fun other ↦ 0 < den other) report = 0 := by
      simp [definedIndicator, hpos]
    rw [hindicator, zero_mul]
    exact pow_nonneg (by linarith) terms

end Descent.Portability.ReplicaDomainCertificate
