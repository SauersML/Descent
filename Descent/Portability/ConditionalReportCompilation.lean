/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw
import Descent.Portability.FiniteGeneticTransition
import Descent.Portability.SublawReportCertificate

assert_below Descent.Decision Descent.Program

/-!
# Compiling a nonlinear finite-cohort report from a genotype law and a report kernel

NOTE1 §4.3 compiles the complete reported experiment from two supplied objects: the law
`p` of the complete finite genotype input, and, conditional on each genotype, the law `R g`
of everything else the pipeline produces.  Equation (21) is then the mixture `p.bind R`,
already constructed in `Descent.Portability.ExactFiniteHistoryLaw`, and (22) is its law of
total expectation, already proved there as `FiniteReportLaw.expectation_bind`.  Neither is
restated here.

What this module adds is the two statements (22) and (23) actually need.  The first is the
polynomial-in-frequencies form of (22): when the genotype law is the independent sampling law
of a panel of chromosomes drawn from per-deme haplotype frequencies, the compiled expectation
is the explicit sum over genotypes of the conditional readout weighted by the product of the
sampled haplotype frequencies.  The independent product is the corpus law
`FiniteGeneticTransition.piLaw`, and the product weight is its mass formula.

The second is the conditional readout (23) for a partially defined metric.  Definedness and
the conditional mean are the corpus notions `SublawReportCertificate.definedIndicator` and
`SublawReportCertificate.conditionalExpectation`; nothing is redefined.  Under the positivity
premise of (23), the compiled definedness mass is positive and the compiled conditional mean
is the ratio of the `p`-weighted sums of the within-stratum defined metric mass and the
within-stratum definedness mass.  The sharper statement is that this ratio is the average of
the within-stratum conditional means weighted by each stratum's definedness mass, not by `p`
alone.

That weighting is exactly the non-identity NOTE1 §4.3 warns about, and it is exhibited here on
a two-genotype pipeline with a three-valued report.  One genotype reports an undefined value
half the time and the value zero otherwise; the other always reports one.  With genotype
weights one quarter and three quarters, the compiled conditional mean is six sevenths, while
the unweighted average of the two within-stratum conditional means is one half and the
`p`-expectation of the within-stratum conditional means is three quarters.  All three differ,
so an expected source-to-target ratio must be formed on each joint experiment before
averaging.

Scope.  The genotype space, the report space and the panel are finite, and the report kernel
is supplied rather than derived from demography.  Equation (22) is proved for the independent
panel sampling law; general non-independent genotype laws are covered only by the mixture form
(21).  The material-graded span of NOTE1 §4.1, in which those monomials live, is
`Descent.Portability.PartialHaplotypeCarrier`.

## Empirical status

None.  The bodies here are algebra: finite sums and one ratio of finite sums built from
supplied masses, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalReportCompilation

open SublawReportCertificate (definedIndicator conditionalExpectation)

noncomputable section

section Panel

variable {Deme Sample Haplotype Report : Type*} [Fintype Sample] [DecidableEq Sample]
variable [Fintype Haplotype] [Fintype Report]

/-- **NOTE1 (22) in the polynomial form.**  When the genotype input is an independently
sampled panel, each chromosome drawn from the haplotype frequencies of its own deme, the
compiled report expectation is the sum over genotypes of the conditional readout times the
product of the sampled haplotype frequencies. -/
theorem panel_compiled_expectation_eq_frequency_polynomial (deme : Sample → Deme)
    (frequency : Deme → FiniteReportLaw Haplotype)
    (report : (Sample → Haplotype) → FiniteReportLaw Report) (metric : Report → ℝ) :
    ((FiniteGeneticTransition.piLaw fun draw ↦ frequency (deme draw)).bind report).expectation
        metric
      = ∑ genotype : Sample → Haplotype,
          (∏ draw, (frequency (deme draw)).mass (genotype draw)) *
            (report genotype).expectation metric := by
  rw [FiniteReportLaw.expectation_bind]
  simp only [FiniteReportLaw.expectation, FiniteGeneticTransition.piLaw_mass]

end Panel

section Conditional

variable {Genotype Report : Type*} [Fintype Genotype] [Fintype Report]

/-- The compiled definedness mass is the `p`-weighted sum of the within-stratum definedness
masses. -/
theorem compiled_definedness_mass (p : FiniteReportLaw Genotype)
    (report : Genotype → FiniteReportLaw Report) (defined : Report → Prop)
    [DecidablePred defined] :
    (p.bind report).expectation (definedIndicator defined)
      = ∑ genotype, p.mass genotype *
          (report genotype).expectation (definedIndicator defined) := by
  rw [FiniteReportLaw.expectation_bind]
  rfl

/-- The compiled defined metric mass is the `p`-weighted sum of the within-stratum defined
metric masses. -/
theorem compiled_defined_metric_mass (p : FiniteReportLaw Genotype)
    (report : Genotype → FiniteReportLaw Report) (defined : Report → Prop)
    [DecidablePred defined] (metric : Report → ℝ) :
    (p.bind report).expectation (fun value ↦ definedIndicator defined value * metric value)
      = ∑ genotype, p.mass genotype * (report genotype).expectation
          (fun value ↦ definedIndicator defined value * metric value) := by
  rw [FiniteReportLaw.expectation_bind]
  rfl

/-- **NOTE1 (23).**  Under the positivity premise the compiled definedness mass is positive
and the compiled conditional mean is the ratio of the two `p`-weighted sums. -/
theorem compiled_conditionalExpectation_eq_pooled_ratio (p : FiniteReportLaw Genotype)
    (report : Genotype → FiniteReportLaw Report) (defined : Report → Prop)
    [DecidablePred defined] (metric : Report → ℝ)
    (hpooled : 0 < ∑ genotype, p.mass genotype *
      (report genotype).expectation (definedIndicator defined)) :
    0 < (p.bind report).expectation (definedIndicator defined) ∧
      conditionalExpectation (p.bind report) defined metric
        = (∑ genotype, p.mass genotype * (report genotype).expectation
              (fun value ↦ definedIndicator defined value * metric value))
          / ∑ genotype, p.mass genotype *
              (report genotype).expectation (definedIndicator defined) := by
  refine ⟨?_, ?_⟩
  · rw [compiled_definedness_mass]
    exact hpooled
  · unfold conditionalExpectation
    rw [compiled_definedness_mass, compiled_defined_metric_mass]

/-- **The compiled conditional mean is the definedness-weighted average of the within-stratum
conditional means.**  The weights are the products of the genotype mass and the stratum
definedness mass, not the genotype masses alone; this is the mechanism behind the non-identity
of NOTE1 §4.3. -/
theorem compiled_conditionalExpectation_eq_weighted_stratum_average
    (p : FiniteReportLaw Genotype) (report : Genotype → FiniteReportLaw Report)
    (defined : Report → Prop) [DecidablePred defined] (metric : Report → ℝ)
    (hstratum : ∀ genotype, 0 < (report genotype).expectation (definedIndicator defined))
    (hpooled : 0 < ∑ genotype, p.mass genotype *
      (report genotype).expectation (definedIndicator defined)) :
    conditionalExpectation (p.bind report) defined metric
      = ∑ genotype, (p.mass genotype *
            (report genotype).expectation (definedIndicator defined)
            / ∑ other, p.mass other *
              (report other).expectation (definedIndicator defined)) *
          conditionalExpectation (report genotype) defined metric := by
  have hpooled_ne : (∑ genotype, p.mass genotype *
      (report genotype).expectation (definedIndicator defined)) ≠ 0 := ne_of_gt hpooled
  have hterm : ∀ genotype : Genotype,
      (p.mass genotype * (report genotype).expectation (definedIndicator defined)
          / ∑ other, p.mass other *
            (report other).expectation (definedIndicator defined)) *
        conditionalExpectation (report genotype) defined metric
      = p.mass genotype * (report genotype).expectation
            (fun value ↦ definedIndicator defined value * metric value)
          / ∑ other, p.mass other *
            (report other).expectation (definedIndicator defined) := by
    intro genotype
    have hstratum_ne : (report genotype).expectation (definedIndicator defined) ≠ 0 :=
      ne_of_gt (hstratum genotype)
    unfold conditionalExpectation
    field_simp
    ring
  rw [Finset.sum_congr rfl fun genotype _ ↦ hterm genotype, ← Finset.sum_div]
  unfold conditionalExpectation
  rw [compiled_definedness_mass, compiled_defined_metric_mass]

end Conditional

section Example

/-- The two genotypes of the compiled example carry one quarter and three quarters of the
input mass. -/
def exampleGenotypeLaw : FiniteReportLaw (Fin 2) where
  mass := ![1 / 4, 3 / 4]
  mass_nonneg := by
    intro genotype
    fin_cases genotype <;> norm_num
  mass_sum := by
    norm_num [Fin.sum_univ_two]

/-- Report value `0` is the undefined outcome of the compiled example. -/
def exampleDefined : Fin 3 → Prop := fun value ↦ value ≠ 0

instance : DecidablePred exampleDefined := fun value ↦ inferInstanceAs (Decidable (value ≠ 0))

/-- The reported metric of the compiled example: the defined outcomes carry the values zero
and one, and the undefined outcome carries no value. -/
def exampleMetric : Fin 3 → ℝ := ![0, 0, 1]

/-- The first genotype reports the undefined outcome half the time and the value zero
otherwise. -/
def exampleHalfDefinedReport : FiniteReportLaw (Fin 3) where
  mass := ![1 / 2, 1 / 2, 0]
  mass_nonneg := by
    intro value
    fin_cases value <;> norm_num
  mass_sum := by
    norm_num [Fin.sum_univ_three]

/-- The second genotype always reports the value one. -/
def exampleCertainReport : FiniteReportLaw (Fin 3) where
  mass := ![0, 0, 1]
  mass_nonneg := by
    intro value
    fin_cases value <;> norm_num
  mass_sum := by
    norm_num [Fin.sum_univ_three]

/-- The report kernel of the compiled example. -/
def exampleReportKernel : Fin 2 → FiniteReportLaw (Fin 3) :=
  ![exampleHalfDefinedReport, exampleCertainReport]

/-- The compiled conditional mean of the example pipeline. -/
def examplePooledMean : ℝ :=
  conditionalExpectation (exampleGenotypeLaw.bind exampleReportKernel) exampleDefined
    exampleMetric

/-- The within-stratum conditional means of the example pipeline. -/
def exampleStratumMean (genotype : Fin 2) : ℝ :=
  conditionalExpectation (exampleReportKernel genotype) exampleDefined exampleMetric

/-- The two within-stratum conditional means of the example are zero and one. -/
theorem exampleStratumMean_values : exampleStratumMean 0 = 0 ∧ exampleStratumMean 1 = 1 := by
  constructor <;>
    norm_num [exampleStratumMean, conditionalExpectation, definedIndicator,
      FiniteReportLaw.expectation, exampleReportKernel, exampleHalfDefinedReport,
      exampleCertainReport, exampleDefined, exampleMetric, Fin.sum_univ_three]

/-- The compiled conditional mean of the example is six sevenths. -/
theorem examplePooledMean_eq : examplePooledMean = 6 / 7 := by
  norm_num [examplePooledMean, conditionalExpectation, definedIndicator,
    FiniteReportLaw.expectation, FiniteReportLaw.bind, exampleGenotypeLaw,
    exampleReportKernel, exampleHalfDefinedReport, exampleCertainReport, exampleDefined,
    exampleMetric, Fin.sum_univ_three, Fin.sum_univ_two]

/-- **The compiled conditional mean is not the unweighted average of the within-stratum
conditional means**; NOTE1 §4.3. -/
theorem examplePooledMean_ne_unweighted_average :
    examplePooledMean ≠ (exampleStratumMean 0 + exampleStratumMean 1) / 2 := by
  obtain ⟨hzero, hone⟩ := exampleStratumMean_values
  rw [examplePooledMean_eq, hzero, hone]
  norm_num

/-- **The compiled conditional mean is not the genotype-weighted average of the within-stratum
conditional means either**: the stratum weights carry the definedness mass as well. -/
theorem examplePooledMean_ne_expected_stratum_ratio :
    examplePooledMean ≠ exampleGenotypeLaw.expectation exampleStratumMean := by
  obtain ⟨hzero, hone⟩ := exampleStratumMean_values
  have hexpect : exampleGenotypeLaw.expectation exampleStratumMean = 3 / 4 := by
    rw [FiniteReportLaw.expectation]
    rw [Fin.sum_univ_two, hzero, hone]
    norm_num [exampleGenotypeLaw]
  rw [examplePooledMean_eq, hexpect]
  norm_num

end Example

end

end Descent.Portability.ConditionalReportCompilation
