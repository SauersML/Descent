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
expected Brier loss `5972333/24300000` and the expected accuracy `418409/759375`. Beyond the
source side: the 18 learner atoms of every context; the target deme through its bottleneck
and growth generations under both migration histories, with its 55 census classes, 220
architecture, environment and census states per history, and 3960 shared-context states after
learner selection; and, for early migration, the probability
`371745151991563462629371512245851/2820650730645240044657068474368000`
that the population target squared correlation is defined.

The remaining target rows of the section 9 table, for both histories, are decided in
`ReferenceExperimentTable`, and the full-square range table is proved in
`ReferenceExperimentRegion`.

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

/-! ## Learner atoms -/

/-- The Laplace-smoothed risk alphabet of two training draws: `1/4, 1/3, 1/2, 2/3, 3/4`. -/
def riskValue : Fin 5 → ℚ
  | 0 => 1 / 4
  | 1 => 1 / 3
  | 2 => 1 / 2
  | 3 => 2 / 3
  | 4 => 3 / 4

/-- The alphabet index of the smoothed risk `(successes + 1) / (count + 2)`. -/
def riskIndex : ℕ → ℕ → Fin 5
  | 0, _ => 2
  | 1, 0 => 1
  | 1, _ => 3
  | 2, 0 => 0
  | 2, 1 => 2
  | _, _ => 4

/-- The number of training draws in the carrier group `group` at `locus`. -/
def groupCount (training : Training) (locus : Fin 2) (group : Bool) : ℕ :=
  (if inGroup locus group training.1 then 1 else 0) +
    (if inGroup locus group training.2 then 1 else 0)

/-- The number of training cases in the carrier group `group` at `locus`. -/
def groupSuccesses (training : Training) (locus : Fin 2) (group : Bool) : ℕ :=
  (if inGroup locus group training.1 && training.1.2 then 1 else 0) +
    (if inGroup locus group training.2 && training.2.2 then 1 else 0)

/-- The risk-alphabet index of the smoothed risk of a carrier group. -/
def groupRiskIndex (training : Training) (locus : Fin 2) (group : Bool) : Fin 5 :=
  riskIndex (groupCount training locus group) (groupSuccesses training locus group)

/-- The risk alphabet reproduces the Laplace-smoothed group risk of every training pair. -/
theorem riskValue_groupRiskIndex : ∀ (training : Training) (locus : Fin 2) (group : Bool),
    riskValue (groupRiskIndex training locus group) = groupRisk training locus group := by
  decide +kernel

/-- A learner atom: the selected locus and the risk indices of its two carrier groups. -/
abbrev LearnerAtom : Type := Fin 2 × Fin 5 × Fin 5

/-- The learner atom that two training draws and one validation draw select. -/
def learnerAtom (training : Training) (validation : Fin 3 × Bool) : LearnerAtom :=
  (selectedLocus training validation,
    groupRiskIndex training (selectedLocus training validation) false,
    groupRiskIndex training (selectedLocus training validation) true)

/-- The carrier indicator of a carrier type at a locus. -/
def carrierAt (locus : Fin 2) (types : Bool × Bool) : Bool :=
  if locus = 0 then types.1 else types.2

/-- The frozen score that a learner atom gives a carrier type. -/
def atomScore (atom : LearnerAtom) (types : Bool × Bool) : ℚ :=
  riskValue (if carrierAt atom.1 types then atom.2.2 else atom.2.1)

/-- The fitted score of every donor is the score of the selected learner atom. -/
theorem fittedScore_eq_atomScore : ∀ (training : Training) (validation : Fin 3 × Bool)
    (index : Fin 3), fittedScore training validation (donor index) =
      atomScore (learnerAtom training validation)
        (carrier (donor index) 0, carrier (donor index) 1) := by
  decide +kernel

/-- The mass of a learner atom in one context: the mass of the training and validation draws
that select it. -/
def atomMass (context : Bool × Bool) (atom : LearnerAtom) : ℚ :=
  ∑ draws : Training × (Fin 3 × Bool),
    if learnerAtom draws.1 draws.2 = atom then
      drawMass context draws.1.1 * drawMass context draws.1.2 * drawMass context draws.2
    else 0

/-- NOTE2 section 9: in every context the learner selects exactly 18 atoms with positive
mass. -/
theorem learnerAtom_count :
    ∀ context, (Finset.univ.filter fun atom ↦ 0 < atomMass context atom).card = 18 := by
  decide +kernel

/-! ## The target deme: meiosis, mutation, selection and migration -/

/-- The site bits of one haplotype at the two reference loci. -/
abbrev Bits : Type := Bool × Bool

/-- A reference individual: the site bits of its two homologs. -/
abbrev Individual : Type := Bits × Bits

/-- The corpus haplotype carried by two site bits. -/
def haplotypeOf (bits : Bits) : MeiosisGameteLaw.Haplotype Allele := ![bits.1, bits.2]

/-- The corpus genotype carried by an individual. -/
def genotypeOf (individual : Individual) : Genotype :=
  (haplotypeOf individual.1, haplotypeOf individual.2)

/-- The carrier type of an individual: its dominant indicators at locus zero and locus one. -/
def carrierType (individual : Individual) : Bool × Bool :=
  (carrier (genotypeOf individual) 0, carrier (genotypeOf individual) 1)

/-- The frozen donor census as individuals. -/
def donorCensus : List Individual :=
  [((false, false), (false, false)), ((false, true), (false, true)),
    ((true, false), (true, true))]

/-- The individuals of the donor census carry the corpus donor genotypes. -/
theorem donorCensus_genotypes : donorCensus.map genotypeOf = [donor 0, donor 1, donor 2] :=
  rfl

/-- The initial target census `00/01`, `00/11`. -/
def initialTargetCensus : List Individual :=
  [((false, false), (false, true)), ((false, false), (true, true))]

/-- NOTE2 (3) at one site: a transmitted bit arrives changed with probability `1/32`. -/
def siteMass (sent arrived : Bool) : ℚ := if sent == arrived then 31 / 32 else 1 / 32

/-- NOTE2 (3) for the reference genome: the gamete law of a parent whose meiosis starts on a
uniformly chosen homolog and switches homolog between the two loci with probability `switch`,
followed by independent site mutation. -/
def gameteMass (switch : ℚ) (parent : Individual) (gamete : Bits) : ℚ :=
  ∑ start : Bool, ∑ swapped : Bool, 1 / 2 * (if swapped then switch else 1 - switch) *
    siteMass (if start then parent.2.1 else parent.1.1) gamete.1 *
    siteMass (if start != swapped then parent.2.2 else parent.1.2) gamete.2

/-- The fraction of a census without allele one at locus zero, `rare_u` of NOTE2 section 9. -/
def rareFraction (census : List Individual) : ℚ :=
  (census.countP fun individual ↦ !(carrierType individual).1 : ℚ) / census.length

/-- NOTE2 section 9: the reproductive fitness `1 + u/3 + v/4 + (A + 1) u v / 2 + E (u + v) / 5
+ u rare_u / 7` of an individual in a census with rare fraction `rare`. -/
def fitness (context : Bool × Bool) (rare : ℚ) (individual : Individual) : ℚ :=
  1 + bitValue (carrierType individual).1 / 3 + bitValue (carrierType individual).2 / 4 +
    (bitValue context.1 + 1) * bitValue (carrierType individual).1 *
      bitValue (carrierType individual).2 / 2 +
    bitValue context.2 *
      (bitValue (carrierType individual).1 + bitValue (carrierType individual).2) / 5 +
    bitValue (carrierType individual).1 * rare / 7

/-- NOTE2 (4) and (5) within one deme: the gamete law of a census under fitness-weighted
choice of the parent. -/
def demeGameteMass (context : Bool × Bool) (switch : ℚ) (census : List Individual)
    (gamete : Bits) : ℚ :=
  (census.map fun parent ↦
      fitness context (rareFraction census) parent * gameteMass switch parent gamete).sum /
    (census.map fun parent ↦ fitness context (rareFraction census) parent).sum

/-- NOTE2 (5) for the target deme: each gamete comes from the frozen donor census with
probability `migration` and from the resident census otherwise. -/
def poolMass (context : Bool × Bool) (migration switch : ℚ) (resident : List Individual)
    (gamete : Bits) : ℚ :=
  migration * demeGameteMass context switch donorCensus gamete +
    (1 - migration) * demeGameteMass context switch resident gamete

/-- A migration history: the migration and switch probabilities of the bottleneck generation
and of the growth generation. -/
structure History where
  bottleneckMigration : ℚ
  bottleneckSwitch : ℚ
  growthMigration : ℚ
  growthSwitch : ℚ

/-- NOTE2 section 9: the early migration history, `(1/2, 1/4)` then `(0, 1/2)`. -/
def earlyMigration : History := ⟨1 / 2, 1 / 4, 0, 1 / 2⟩

/-- NOTE2 section 9: the late migration history, `(0, 1/2)` then `(1/2, 1/4)`. -/
def lateMigration : History := ⟨0, 1 / 2, 1 / 2, 1 / 4⟩

/-- NOTE2 (6) at census size one: the law of the bottleneck individual, two independent
gametes from the pool of the initial target census. -/
def bottleneckMass (history : History) (context : Bool × Bool) (individual : Individual) : ℚ :=
  poolMass context history.bottleneckMigration history.bottleneckSwitch initialTargetCensus
      individual.1 *
    poolMass context history.bottleneckMigration history.bottleneckSwitch initialTargetCensus
      individual.2

/-- NOTE2 (6) in the growth generation: the law of one offspring of the bottleneck individual
`parent`. -/
def offspringMass (history : History) (context : Bool × Bool)
    (parent individual : Individual) : ℚ :=
  poolMass context history.growthMigration history.growthSwitch [parent] individual.1 *
    poolMass context history.growthMigration history.growthSwitch [parent] individual.2

/-! ## The architecture, environment and census states -/

/-- The index of a site pair in `0, 1, 2, 3`. -/
def bitsIndex (bits : Bits) : ℕ := 2 * (if bits.1 then 1 else 0) + (if bits.2 then 1 else 0)

/-- The representative of an unordered genotype: the homologs in increasing order. -/
def sortIndividual (individual : Individual) : Individual :=
  if bitsIndex individual.1 ≤ bitsIndex individual.2 then individual
  else (individual.2, individual.1)

/-- The index of an individual in `0, …, 15`. -/
def individualIndex (individual : Individual) : ℕ :=
  4 * bitsIndex individual.1 + bitsIndex individual.2

/-- The census class of two ordered offspring: the unordered pair of their unordered
genotypes, represented by sorting. -/
def censusClass (offspring : Individual × Individual) : Individual × Individual :=
  if individualIndex (sortIndividual offspring.1) ≤ individualIndex (sortIndividual offspring.2)
  then (sortIndividual offspring.1, sortIndividual offspring.2)
  else (sortIndividual offspring.2, sortIndividual offspring.1)

/-- Whether a pair of individuals is the representative of its census class. -/
def isCensusClass (census : Individual × Individual) : Bool := censusClass census == census

/-- A growth census of two offspring over ten unordered genotypes has 55 classes. -/
theorem censusClass_count :
    (Finset.univ.filter fun census : Individual × Individual ↦
      isCensusClass census).card = 55 := by
  decide +kernel

/-- The mass of a growth census class in one context under one history. -/
def censusClassMass (history : History) (context : Bool × Bool)
    (census : Individual × Individual) : ℚ :=
  ∑ parent : Individual, bottleneckMass history context parent *
    ∑ offspring : Individual × Individual,
      if censusClass offspring = census then
        offspringMass history context parent offspring.1 *
          offspringMass history context parent offspring.2
      else 0

/-- Every census class carries positive mass once every bottleneck individual and every
offspring genotype do. Assumes: positivity of the bottleneck and offspring masses, which is
decided for both reference histories below. -/
theorem censusClassMass_pos (history : History) (context : Bool × Bool)
    (census : Individual × Individual) (hclass : isCensusClass census = true)
    (hbottleneck : ∀ parent, 0 < bottleneckMass history context parent)
    (hoffspring : ∀ parent individual, 0 < offspringMass history context parent individual) :
    0 < censusClassMass history context census := by
  have hrepresentative : censusClass census = census := beq_iff_eq.mp hclass
  have hinner : ∀ parent : Individual, 0 < ∑ offspring : Individual × Individual,
      if censusClass offspring = census then
        offspringMass history context parent offspring.1 *
          offspringMass history context parent offspring.2
      else 0 := by
    intro parent
    refine Finset.sum_pos' (fun offspring _ ↦ ?_) ⟨census, Finset.mem_univ _, ?_⟩
    · split_ifs
      · exact mul_nonneg (hoffspring _ _).le (hoffspring _ _).le
      · exact le_rfl
    · rw [if_pos hrepresentative]
      exact mul_pos (hoffspring _ _) (hoffspring _ _)
  exact Finset.sum_pos' (fun parent _ ↦ mul_nonneg (hbottleneck parent).le (hinner parent).le)
    ⟨census.1, Finset.mem_univ _, mul_pos (hbottleneck _) (hinner _)⟩

/-- NOTE2 section 9: a history whose bottleneck and offspring masses are positive carries all
55 census classes in each of the four contexts, 220 architecture, environment and census
states. Assumes: the two positivity facts, decided for both reference histories below. -/
theorem stateCount_of_pos (history : History)
    (hbottleneck : ∀ context parent, 0 < bottleneckMass history context parent)
    (hoffspring : ∀ context parent individual,
      0 < offspringMass history context parent individual) :
    (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) ↦
      isCensusClass state.2 = true ∧ 0 < censusClassMass history state.1 state.2).card =
      220 := by
  have hfilter : (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) ↦
      isCensusClass state.2 = true ∧ 0 < censusClassMass history state.1 state.2) =
      (Finset.univ : Finset (Bool × Bool)) ×ˢ
        (Finset.univ.filter fun census : Individual × Individual ↦ isCensusClass census) := by
    ext ⟨context, census⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨fun hstate ↦ hstate.1, fun hclass ↦
      ⟨hclass, censusClassMass_pos history context census hclass (hbottleneck context)
        (hoffspring context)⟩⟩
  rw [hfilter, Finset.card_product, censusClass_count]
  decide

theorem early_bottleneckMass_pos :
    ∀ context parent, 0 < bottleneckMass earlyMigration context parent := by
  decide +kernel

theorem early_offspringMass_pos :
    ∀ context parent individual, 0 < offspringMass earlyMigration context parent individual := by
  decide +kernel

theorem late_bottleneckMass_pos :
    ∀ context parent, 0 < bottleneckMass lateMigration context parent := by
  decide +kernel

theorem late_offspringMass_pos :
    ∀ context parent individual, 0 < offspringMass lateMigration context parent individual := by
  decide +kernel

/-- NOTE2 section 9: the early migration history has 220 architecture, environment and census
states. -/
theorem early_stateCount :
    (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) ↦
      isCensusClass state.2 = true ∧ 0 < censusClassMass earlyMigration state.1 state.2).card =
      220 :=
  stateCount_of_pos earlyMigration early_bottleneckMass_pos early_offspringMass_pos

/-- NOTE2 section 9: the late migration history has 220 architecture, environment and census
states. -/
theorem late_stateCount :
    (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) ↦
      isCensusClass state.2 = true ∧ 0 < censusClassMass lateMigration state.1 state.2).card =
      220 :=
  stateCount_of_pos lateMigration late_bottleneckMass_pos late_offspringMass_pos

/-- The learner atoms that some training and validation draws select. -/
def reachableAtoms : Finset LearnerAtom :=
  Finset.univ.image fun draws : Training × (Fin 3 × Bool) ↦ learnerAtom draws.1 draws.2

/-- In every context a learner atom carries positive mass exactly when some draws select it. -/
theorem atomMass_pos_iff :
    ∀ context atom, 0 < atomMass context atom ↔ atom ∈ reachableAtoms := by
  decide +kernel

/-- Exactly 18 learner atoms are reachable. -/
theorem reachableAtoms_card : reachableAtoms.card = 18 := by
  decide +kernel

/-- NOTE2 section 9: a history whose bottleneck and offspring masses are positive has 3960
shared-context states after learner selection, the 220 architecture, environment and census
states times the 18 learner atoms. Assumes: the two positivity facts, decided for both
reference histories above. -/
theorem contextStateCount_of_pos (history : History)
    (hbottleneck : ∀ context parent, 0 < bottleneckMass history context parent)
    (hoffspring : ∀ context parent individual,
      0 < offspringMass history context parent individual) :
    (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) × LearnerAtom ↦
      isCensusClass state.2.1 = true ∧
        0 < censusClassMass history state.1 state.2.1 * atomMass state.1 state.2.2).card =
      3960 := by
  have hfilter : (Finset.univ.filter
      fun state : (Bool × Bool) × (Individual × Individual) × LearnerAtom ↦
        isCensusClass state.2.1 = true ∧
          0 < censusClassMass history state.1 state.2.1 * atomMass state.1 state.2.2) =
      (Finset.univ : Finset (Bool × Bool)) ×ˢ
        ((Finset.univ.filter fun census : Individual × Individual ↦ isCensusClass census) ×ˢ
          reachableAtoms) := by
    ext ⟨context, census, atom⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hclass, hmass⟩
      exact ⟨hclass, (atomMass_pos_iff context atom).mp ((mul_pos_iff_of_pos_left
        (censusClassMass_pos history context census hclass (hbottleneck context)
          (hoffspring context))).mp hmass)⟩
    · rintro ⟨hclass, hatom⟩
      exact ⟨hclass, mul_pos (censusClassMass_pos history context census hclass
        (hbottleneck context) (hoffspring context)) ((atomMass_pos_iff context atom).mpr hatom)⟩
  rw [hfilter, Finset.card_product, Finset.card_product, censusClass_count, reachableAtoms_card]
  decide

/-- NOTE2 section 9: the early migration history has 3960 shared-context states. -/
theorem early_contextStateCount :
    (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) × LearnerAtom ↦
      isCensusClass state.2.1 = true ∧
        0 < censusClassMass earlyMigration state.1 state.2.1 * atomMass state.1 state.2.2).card =
      3960 :=
  contextStateCount_of_pos earlyMigration early_bottleneckMass_pos early_offspringMass_pos

/-- NOTE2 section 9: the late migration history has 3960 shared-context states. -/
theorem late_contextStateCount :
    (Finset.univ.filter fun state : (Bool × Bool) × (Individual × Individual) × LearnerAtom ↦
      isCensusClass state.2.1 = true ∧
        0 < censusClassMass lateMigration state.1 state.2.1 * atomMass state.1 state.2.2).card =
      3960 :=
  contextStateCount_of_pos lateMigration late_bottleneckMass_pos late_offspringMass_pos

/-! ## The terminal target law and the target reports -/

/-- A terminal target state reduced to what every target report reads: the carrier types of
the two members of the growth census, in draw order. -/
abbrev TerminalTypes : Type := (Bool × Bool) × (Bool × Bool)

/-- The law of the carrier type of one growth offspring of the bottleneck individual. -/
def growthTypeMass (history : History) (context : Bool × Bool) (parent : Individual)
    (types : Bool × Bool) : ℚ :=
  ∑ individual : Individual,
    if carrierType individual = types then offspringMass history context parent individual
    else 0

/-- NOTE2 (6) through both generations: the law of the terminal carrier types of the growth
census, summed over the bottleneck individual. -/
def terminalMass (history : History) (context : Bool × Bool) (terminal : TerminalTypes) : ℚ :=
  ∑ parent : Individual, bottleneckMass history context parent *
    growthTypeMass history context parent terminal.1 *
      growthTypeMass history context parent terminal.2

/-- The carrier types of a member of the terminal census. -/
def memberTypes (terminal : TerminalTypes) (member : Bool) : Bool × Bool :=
  if member then terminal.2 else terminal.1

/-- NOTE2 section 9: the target outcome probability `(2 + 3 u_A + u v + E v) / 10`. -/
def targetRisk (context : Bool × Bool) (types : Bool × Bool) : ℚ :=
  (2 + 3 * bitValue (if context.1 then types.2 else types.1) +
      bitValue types.1 * bitValue types.2 + bitValue context.2 * bitValue types.2) / 10

/-- The mass of one target population draw: a uniformly chosen member of the terminal census
together with its fresh conditional outcome. -/
def targetMass (context : Bool × Bool) (terminal : TerminalTypes) (state : Bool × Bool) : ℚ :=
  1 / 2 * (if state.2 then targetRisk context (memberTypes terminal state.1)
    else 1 - targetRisk context (memberTypes terminal state.1))

theorem targetMass_nonneg :
    ∀ context terminal state, 0 ≤ targetMass context terminal state := by
  decide +kernel

theorem targetMass_sum :
    ∀ context terminal, ∑ state, targetMass context terminal state = 1 := by
  decide +kernel

/-- The target population law of a terminal census as a corpus rational report law. -/
def targetLaw (context : Bool × Bool) (terminal : TerminalTypes) :
    RationalReportLaw (Bool × Bool) where
  mass := targetMass context terminal
  mass_nonneg := targetMass_nonneg context terminal
  mass_sum := targetMass_sum context terminal

section RationalMetrics

variable {State : Type} [Fintype State]

/-- The covariance of two rational statistics under a rational report law. -/
def rationalCovariance (law : RationalReportLaw State) (first second : State → ℚ) : ℚ :=
  law.expectation (fun state ↦ first state * second state) -
    law.expectation first * law.expectation second

/-- The squared Pearson correlation of a score with a binary outcome, defined exactly when
both variances are positive, as `FiniteReportLaw.squaredCorrelation` is. -/
def rationalR2 (law : RationalReportLaw State) (score : State → ℚ) (outcome : State → Bool) :
    Option ℚ :=
  if 0 < rationalCovariance law score score ∧
      0 < rationalCovariance law (fun state ↦ bitValue (outcome state))
        (fun state ↦ bitValue (outcome state)) then
    some (rationalCovariance law score (fun state ↦ bitValue (outcome state)) ^ 2 /
      (rationalCovariance law score score *
        rationalCovariance law (fun state ↦ bitValue (outcome state))
          (fun state ↦ bitValue (outcome state))))
  else none

end RationalMetrics

/-- The population target squared correlation of the frozen score of a learner atom on a
terminal census. -/
def targetR2 (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    Option ℚ :=
  rationalR2 (targetLaw context terminal)
    (fun state ↦ atomScore atom (memberTypes terminal state.1)) (fun state ↦ state.2)

/-- The expectation of a target report over the shared study context of one history: the
context, the learner atom that the source data select, and the terminal target census. -/
def historyReport (history : History)
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) : ℚ :=
  ∑ context, contextMass context * ∑ atom,
    if atomMass context atom = 0 then 0
    else atomMass context atom * ∑ terminal, terminalMass history context terminal *
      report context atom terminal

/-- NOTE2 section 9, early migration: the population target squared correlation is defined
with probability `371745151991563462629371512245851/2820650730645240044657068474368000`. -/
theorem early_target_r2_definedProbability :
    historyReport earlyMigration (fun context atom terminal ↦
      bitValue (targetR2 context atom terminal).isSome) =
      371745151991563462629371512245851 / 2820650730645240044657068474368000 := by
  decide +kernel

end Descent.Portability.ReferenceExperimentLaw
