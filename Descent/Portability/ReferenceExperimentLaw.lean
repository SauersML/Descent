/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MeiosisGameteLaw
import Descent.Portability.ExactMetricEvaluation
import Descent.Portability.ArchitectureEnvironmentRegion

assert_below Descent.Decision Descent.Program

/-!
# The reference experiment of NOTE2 section 9: the model and its source-side report law

NOTE2 section 9 executes one completely specified experiment end to end: two biallelic loci,
a frozen donor census of three genotypes, a target deme that passes through a one-individual
bottleneck, an architecture indicator of mean three fifths with an independent environment
indicator of mean two thirds, a fitness with epistasis, environmental dependence and frequency
dependence, and a deliberately small exact learner. This module defines that model in the
corpus vocabulary and evaluates its source-side report law exactly.

The model is carried by rational arithmetic, so every value below is decided by computation
in the kernel rather than approximated. The context masses are the corpus independent mixture
`ArchitectureEnvironmentRegion.cellWeight` at `(3/5, 2/3)`. A source draw picks a donor
uniformly from the frozen census, whose genotypes are pairs of corpus
`MeiosisGameteLaw.Haplotype`s, and draws its outcome with probability
`(2 + 3 u_A + u v + E u) / 10`. The learner fits a Laplace-smoothed risk to each carrier group
of each locus from two training draws, keeps the candidate with the lower Brier loss on one
held-out draw, and gives ties to the first locus. The population metrics of the frozen score
are the squared correlation, the calibration slope, the Brier loss and the accuracy of the
rule that predicts a case at a score of at least one half, all under the source population
law of the study context, and the study law over contexts, training data and validation data
is a corpus `RationalReportClosure.RationalReportLaw`.

Proved here: the source rows of the reference results, namely the probability `4051/6750`
that the population source squared correlation is defined, its weighted numerator
`41454281977/498841200000`, the weighted calibration slope numerator `197447/337500`, the
expected Brier loss `5972333/24300000` and the expected accuracy `418409/759375`.

Not formalized here: the target histories, their 220 architecture, environment and census
states, and the target rows of the section 9 table, which need the genetic evolution of the
target deme.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentLaw

open RationalReportClosure

/-! ## The reference genome and the frozen donor census -/

/-- The allele alphabet of both reference loci: one bit per site. -/
abbrev Allele (_ : Fin 2) : Type := Bool

/-- A reference genotype: an ordered pair of phased two-locus haplotypes, in the haplotype
vocabulary of `MeiosisGameteLaw`. -/
abbrev Genotype : Type :=
  MeiosisGameteLaw.Haplotype Allele × MeiosisGameteLaw.Haplotype Allele

/-- The frozen donor census of NOTE2 section 9, the genotypes `00/00`, `01/01` and `10/11`,
each written as the site bits of its two homologs. -/
def donor : Fin 3 → Genotype
  | 0 => (![false, false], ![false, false])
  | 1 => (![false, true], ![false, true])
  | 2 => (![true, false], ![true, true])

/-- The dominant allele indicator: the genotype carries allele one at the locus. -/
def carrier (genotype : Genotype) (locus : Fin 2) : Bool :=
  genotype.1 locus || genotype.2 locus

/-- A bit read as a rational number. -/
def bitValue (bit : Bool) : ℚ := if bit then 1 else 0

/-! ## The shared architecture and environment context -/

/-- NOTE2 section 9: the context masses of an architecture indicator with `Pr(A = 1) = 3/5`
and an independent environment indicator with `Pr(E = 1) = 2/3`. -/
def contextMass (context : Bool × Bool) : ℚ :=
  (if context.1 then 3 / 5 else 2 / 5) * (if context.2 then 2 / 3 else 1 / 3)

/-- The context law is the corpus independent mixture of NOTE2 (9) read at `(3/5, 2/3)`. -/
theorem contextMass_eq_cellWeight (context : Bool × Bool) :
    ((contextMass context : ℚ) : ℝ) =
      ArchitectureEnvironmentRegion.cellWeight (3 / 5) (2 / 3) context := by
  obtain ⟨architecture, environment⟩ := context
  cases architecture <;> cases environment <;>
    norm_num [contextMass, ArchitectureEnvironmentRegion.cellWeight]

theorem contextMass_nonneg : ∀ context, 0 ≤ contextMass context := by
  decide +kernel

/-! ## The source population and one source draw -/

/-- NOTE2 section 9: the source outcome probability `(2 + 3 u_A + u v + E u) / 10` of a
genotype, where `u_A` is the carrier indicator of the locus the architecture makes causal. -/
def sourceRisk (context : Bool × Bool) (genotype : Genotype) : ℚ :=
  (2 + 3 * bitValue (if context.1 then carrier genotype 1 else carrier genotype 0) +
      bitValue (carrier genotype 0) * bitValue (carrier genotype 1) +
      bitValue context.2 * bitValue (carrier genotype 0)) / 10

/-- The mass of one source draw: a donor chosen uniformly from the frozen census together
with its fresh conditional outcome. -/
def drawMass (context : Bool × Bool) (draw : Fin 3 × Bool) : ℚ :=
  1 / 3 * (if draw.2 then sourceRisk context (donor draw.1)
    else 1 - sourceRisk context (donor draw.1))

theorem drawMass_nonneg : ∀ context draw, 0 ≤ drawMass context draw := by
  decide +kernel

theorem drawMass_sum : ∀ context, ∑ draw, drawMass context draw = 1 := by
  decide +kernel

/-- The source population law of one context as a corpus rational report law. -/
def sourceLaw (context : Bool × Bool) : RationalReportLaw (Fin 3 × Bool) where
  mass := drawMass context
  mass_nonneg := drawMass_nonneg context
  mass_sum := drawMass_sum context

/-! ## The exact two-group learner -/

/-- Two training draws from the source census. -/
abbrev Training : Type := (Fin 3 × Bool) × (Fin 3 × Bool)

/-- Whether a draw falls in the carrier group `group` at `locus`. -/
def inGroup (locus : Fin 2) (group : Bool) (draw : Fin 3 × Bool) : Bool :=
  carrier (donor draw.1) locus == group

/-- NOTE2 section 9: the Laplace-smoothed risk that two training draws give the carrier group
`group` at `locus`, with one pseudocount for each outcome. -/
def groupRisk (training : Training) (locus : Fin 2) (group : Bool) : ℚ :=
  (bitValue (inGroup locus group training.1 && training.1.2) +
      bitValue (inGroup locus group training.2 && training.2.2) + 1) /
    (bitValue (inGroup locus group training.1) + bitValue (inGroup locus group training.2) + 2)

/-- The validation Brier loss of the candidate model at `locus` on one held-out draw. -/
def validationLoss (training : Training) (locus : Fin 2) (validation : Fin 3 × Bool) : ℚ :=
  (groupRisk training locus (carrier (donor validation.1) locus) - bitValue validation.2) ^ 2

/-- The selected locus: the second candidate only when its validation loss is strictly
lower, so ties select the first locus. -/
def selectedLocus (training : Training) (validation : Fin 3 × Bool) : Fin 2 :=
  if validationLoss training 1 validation < validationLoss training 0 validation then 1 else 0

/-- The frozen score that the selected model gives a genotype. -/
def fittedScore (training : Training) (validation : Fin 3 × Bool) (genotype : Genotype) : ℚ :=
  groupRisk training (selectedLocus training validation)
    (carrier genotype (selectedLocus training validation))

/-! ## Population metrics of a frozen score in the source population -/

/-- The variance of a donor score in the source population of one context. -/
def scoreVariance (context : Bool × Bool) (score : Fin 3 → ℚ) : ℚ :=
  (sourceLaw context).expectation (fun draw ↦ score draw.1 ^ 2) -
    (sourceLaw context).expectation (fun draw ↦ score draw.1) ^ 2

/-- The variance of the outcome in the source population of one context. -/
def outcomeVariance (context : Bool × Bool) : ℚ :=
  (sourceLaw context).expectation (fun draw ↦ bitValue draw.2 ^ 2) -
    (sourceLaw context).expectation (fun draw ↦ bitValue draw.2) ^ 2

/-- The covariance of a donor score with the outcome in the source population. -/
def scoreCovariance (context : Bool × Bool) (score : Fin 3 → ℚ) : ℚ :=
  (sourceLaw context).expectation (fun draw ↦ score draw.1 * bitValue draw.2) -
    (sourceLaw context).expectation (fun draw ↦ score draw.1) *
      (sourceLaw context).expectation (fun draw ↦ bitValue draw.2)

/-- The population squared correlation, defined exactly when both variances are positive. -/
def populationR2 (context : Bool × Bool) (score : Fin 3 → ℚ) : Option ℚ :=
  if 0 < scoreVariance context score ∧ 0 < outcomeVariance context then
    some (scoreCovariance context score ^ 2 /
      (scoreVariance context score * outcomeVariance context))
  else none

/-- The population calibration slope, defined exactly when the score varies. -/
def populationSlope (context : Bool × Bool) (score : Fin 3 → ℚ) : Option ℚ :=
  if 0 < scoreVariance context score then
    some (scoreCovariance context score / scoreVariance context score)
  else none

/-- The population Brier loss of a donor score. -/
def populationBrier (context : Bool × Bool) (score : Fin 3 → ℚ) : ℚ :=
  (sourceLaw context).expectation fun draw ↦ (score draw.1 - bitValue draw.2) ^ 2

/-- The population accuracy of the rule that predicts a case at a score of at least one
half. -/
def populationAccuracy (context : Bool × Bool) (score : Fin 3 → ℚ) : ℚ :=
  (sourceLaw context).expectation fun draw ↦ bitValue (decide (1 / 2 ≤ score draw.1) == draw.2)

/-! ## The source study law over contexts, training data and validation data -/

/-- A source study: the shared context, the two training draws and the validation draw. -/
abbrev SourceStudy : Type := (Bool × Bool) × Training × (Fin 3 × Bool)

/-- The mass of a source study: the context mass times three independent source draws. -/
def studyMass (study : SourceStudy) : ℚ :=
  contextMass study.1 * drawMass study.1 study.2.1.1 * drawMass study.1 study.2.1.2 *
    drawMass study.1 study.2.2

theorem studyMass_nonneg (study : SourceStudy) : 0 ≤ studyMass study :=
  mul_nonneg (mul_nonneg (mul_nonneg (contextMass_nonneg _) (drawMass_nonneg _ _))
    (drawMass_nonneg _ _)) (drawMass_nonneg _ _)

theorem studyMass_sum : ∑ study, studyMass study = 1 := by
  decide +kernel

/-- The study law of NOTE2 section 9 on the source side, as a corpus rational report law. -/
def studyLaw : RationalReportLaw SourceStudy where
  mass := studyMass
  mass_nonneg := studyMass_nonneg
  mass_sum := studyMass_sum

/-- The frozen score of every donor in a study. -/
def studyScore (study : SourceStudy) (index : Fin 3) : ℚ :=
  fittedScore study.2.1 study.2.2 (donor index)

/-- The population source squared correlation of a study. -/
def sourceR2 (study : SourceStudy) : Option ℚ := populationR2 study.1 (studyScore study)

/-- The population source calibration slope of a study. -/
def sourceSlope (study : SourceStudy) : Option ℚ := populationSlope study.1 (studyScore study)

/-- The probability under the study law that a partial report is defined. -/
def definedProbability (report : SourceStudy → Option ℚ) : ℚ :=
  studyLaw.expectation fun study ↦ bitValue (report study).isSome

/-- The weighted numerator of a partial report: undefined studies contribute nothing. -/
def weightedNumerator (report : SourceStudy → Option ℚ) : ℚ :=
  studyLaw.expectation fun study ↦ (report study).getD 0

/-- NOTE2 section 9: the population source squared correlation is defined with probability
`4051/6750`. -/
theorem source_r2_definedProbability : definedProbability sourceR2 = 4051 / 6750 := by
  decide +kernel

/-- NOTE2 section 9: the weighted numerator of the population source squared correlation. -/
theorem source_r2_weightedNumerator :
    weightedNumerator sourceR2 = 41454281977 / 498841200000 := by
  decide +kernel

/-- NOTE2 section 9: the weighted numerator of the population source calibration slope. -/
theorem source_slope_weightedNumerator : weightedNumerator sourceSlope = 197447 / 337500 := by
  decide +kernel

/-- NOTE2 section 9: the expected population source Brier loss. -/
theorem source_brier_expectation :
    studyLaw.expectation (fun study ↦ populationBrier study.1 (studyScore study)) =
      5972333 / 24300000 := by
  decide +kernel

/-- NOTE2 section 9: the expected population source accuracy. -/
theorem source_accuracy_expectation :
    studyLaw.expectation (fun study ↦ populationAccuracy study.1 (studyScore study)) =
      418409 / 759375 := by
  decide +kernel

end Descent.Portability.ReferenceExperimentLaw
