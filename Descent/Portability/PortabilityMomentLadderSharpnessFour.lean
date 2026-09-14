/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndAscertainedWitness
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Degree

assert_below Descent.Decision Descent.Program

/-!
# The fourth rung of the moment ladder is sharp: degree three does not fix accuracy portability

`PortabilityMomentLadder.portabilityReport_eq_of_polynomialsAgreeAt_four` shows that two process
laws agreeing on every frequency polynomial of total degree at most four give one portability
report.  Every entry of the report but the squared-correlation portability is fixed at degree three
or below.  This module shows that degree three does not fix that entry, so the report needs rung
four.

The witness.  A source deme `false` and a target deme `true` carry one locus with three alleles
`0, 1, 2` (`TriallelicHaplotype`, `WitnessState`, `sum_triallelicHaplotype`).  At a parameter
`q ∈ [0, 1]` the target deme has the haplotype law `(q/2, (1 - q)/2, 1/2)` and the source deme the
law `(1/4, 1/4, 1/2)` (`lineSlope`, `lineIntercept`, `lineLaw`, `lineState`, `mass_lineLaw`).
Every haplotype frequency is affine in `q` (`lineState_apply`).  Two constant kernels draw `q` from
two finite laws: the first puts mass `1/2` on `1/4` and on `3/4`, the second `1/8, 3/4, 1/8` on
`0, 1/2, 1` (`firstLaw`, `secondLaw`, `integral_firstLaw`, `integral_secondLaw`, `firstKernel`,
`secondKernel`).  The moments of `q` agree through degree three, `1, 1/2, 5/16, 7/32`, and differ at
degree four, `41/256` against `44/256`.

Agreement through degree three.  A frequency polynomial evaluated along the line of states is the
polynomial in `q` obtained by substituting the affine coordinates (`lineCoordinate`,
`polynomialFunction_lineState`), of degree at most the total degree
(`natDegree_linePolynomial_le`).  Both laws integrate every polynomial in `q` of degree at most
three to one value, so the two kernels agree on every frequency polynomial of total degree at most
three (`polynomialsAgreeAt_three`).

The separation.  The score is the indicator of allele `0` and the outcome the indicator of allele
`1` (`alleleScore`, `alleleOutcome`).  Their covariance is `-p₀ p₁` and their variances are
`p₀ (1 - p₀)` and `p₁ (1 - p₁)` (`expectations_alleles`, `correlationNumerator_alleles`,
`correlationDenominator_alleles`).  In the target deme the correlation numerator is `q² (1 - q)²`
and the denominator `q (2 - q) (1 - q²)`, both of degree four (`correlationNumerator_target`,
`correlationDenominator_target`); the source deme has `1/16` and `9/16`
(`correlationNumerator_source`, `correlationDenominator_source`).  The expected target numerators
are `9/256` and `12/256` and the expected target denominators `105/256` and `108/256`, so the
squared correlations of expectations in the target are `3/35` and `1/9` (`integrals_firstKernel`,
`integrals_secondKernel`).  The squared-correlation portabilities are `27/35` and `1`
(`expectedPortability_firstKernel`, `expectedPortability_secondKernel`).

Sharpness.  The two Markov kernels agree on every frequency polynomial of total degree at most
three and have different squared-correlation portability
(`polynomialsAgreeAt_three_and_expectedPortability_ne`), so their portability reports differ for
every binary endpoint (`portabilityReport_ne`).  Agreement up to degree three does not force one
report (`not_forall_portabilityReport_eq_of_polynomialsAgreeAt_three`): no function of the degree-3
moments determines the report, and rung four of the ladder is sharp.

Scope.  The two process laws are constant kernels of finite laws on the state, not histories of
epochs, splits and pulses, and the witness has one locus with three alleles.  Whether two event
histories separate rung three from rung four is not settled here, and nor is the separation of
rungs two and three for the calibration intercepts.

## Empirical status

None.  The bodies here are finite sums of point masses, polynomial identities in one parameter and
rational arithmetic, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderSharpnessFour

open MeasureTheory ProbabilityTheory PartialHaplotypeDualGenerator NeutralFellerGenerator
  ReplicaMetricInstances EndToEndPortabilityLaw PortabilityMomentLadder EndToEndAscertainedWitness

noncomputable section

/-! ## The line of states -/

/-- The haplotypes of one locus with three alleles. -/
abbrev TriallelicHaplotype : Type := FullHaplotype Unit fun _ : Unit ↦ Fin 3

/-- The frequency states of a source deme `false` and a target deme `true` at one locus with three
alleles. -/
abbrev WitnessState : Type := FrequencyState Bool Unit fun _ : Unit ↦ Fin 3

/-- A sum over the haplotypes of one locus with three alleles is a sum over the alleles. -/
theorem sum_triallelicHaplotype (g : TriallelicHaplotype → ℝ) :
    ∑ hap, g hap = g (fun _ ↦ 0) + g (fun _ ↦ 1) + g (fun _ ↦ 2) :=
  (Fintype.sum_equiv (Equiv.funUnique Unit (Fin 3)) g (fun a ↦ g fun _ ↦ a)
    fun hap ↦ congrArg g (funext fun _ ↦ rfl)).trans (Fin.sum_univ_three _)

/-- The slope in the parameter of the frequency of each allele: `1/2, -1/2, 0` in the target deme
and `0` in the source deme. -/
def lineSlope (deme : Bool) : Fin 3 → ℝ :=
  if deme then ![1 / 2, -1 / 2, 0] else ![0, 0, 0]

/-- The intercept of the frequency of each allele: `0, 1/2, 1/2` in the target deme and
`1/4, 1/4, 1/2` in the source deme. -/
def lineIntercept (deme : Bool) : Fin 3 → ℝ :=
  if deme then ![0, 1 / 2, 1 / 2] else ![1 / 4, 1 / 4, 1 / 2]

/-- Every allele frequency along the line is nonnegative. -/
theorem lineMass_nonneg (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (deme : Bool) (a : Fin 3) :
    0 ≤ lineSlope deme a * q + lineIntercept deme a := by
  cases deme <;> fin_cases a <;> simp [lineSlope, lineIntercept] <;> linarith [hq.1, hq.2]

/-- The haplotype law of a deme at parameter `q`: `(q/2, (1 - q)/2, 1/2)` in the target deme and
`(1/4, 1/4, 1/2)` in the source deme. -/
def lineLaw (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (deme : Bool) : FiniteReportLaw TriallelicHaplotype where
  mass hap := lineSlope deme (hap ()) * q + lineIntercept deme (hap ())
  mass_nonneg hap := lineMass_nonneg q hq deme (hap ())
  mass_sum := by
    rw [sum_triallelicHaplotype]
    cases deme <;> simp [lineSlope, lineIntercept] <;> ring

/-- **The state at parameter `q`**: every deme carries its line law. -/
def lineState (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) : WitnessState :=
  stateOfLaws (lineLaw q hq)

/-- Every haplotype frequency along the line is affine in the parameter. -/
theorem lineState_apply (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (c : FrequencyVariable Bool Unit fun _ : Unit ↦ Fin 3) :
    (lineState q hq).1 c = lineSlope c.1 (c.2 ()) * q + lineIntercept c.1 (c.2 ()) :=
  rfl

/-- The haplotype law of a deme at the state of parameter `q` is its line law. -/
theorem stateLaw_lineState (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (deme : Bool) :
    stateLaw (lineState q hq) deme = lineLaw q hq deme :=
  stateLaw_stateOfLaws (lineLaw q hq) deme

/-- The masses of alleles `0` and `1` in the target and the source deme. -/
theorem mass_lineLaw (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    (lineLaw q hq true).mass (fun _ ↦ 0) = q / 2
      ∧ (lineLaw q hq true).mass (fun _ ↦ 1) = (1 - q) / 2
      ∧ (lineLaw q hq false).mass (fun _ ↦ 0) = 1 / 4
      ∧ (lineLaw q hq false).mass (fun _ ↦ 1) = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [lineLaw, lineSlope, lineIntercept] <;> ring

/-! ## The score, the outcome and their correlation -/

/-- The score: the indicator of allele `0`. -/
def alleleScore (hap : TriallelicHaplotype) : ℝ :=
  ![1, 0, 0] (hap ())

/-- The outcome: the indicator of allele `1`. -/
def alleleOutcome (hap : TriallelicHaplotype) : ℝ :=
  ![0, 1, 0] (hap ())

/-- The first and second moments of the score and the outcome are the masses of their alleles,
and the two indicators never both hold. -/
theorem expectations_alleles (law : FiniteReportLaw TriallelicHaplotype) :
    law.expectation alleleScore = law.mass (fun _ ↦ 0)
      ∧ law.expectation alleleOutcome = law.mass (fun _ ↦ 1)
      ∧ law.expectation (fun s ↦ alleleScore s ^ 2) = law.mass (fun _ ↦ 0)
      ∧ law.expectation (fun s ↦ alleleOutcome s ^ 2) = law.mass (fun _ ↦ 1)
      ∧ law.expectation (fun s ↦ alleleScore s * alleleOutcome s) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [FiniteReportLaw.expectation, sum_triallelicHaplotype] <;>
    simp [alleleScore, alleleOutcome]

/-- **The correlation numerator of the two allele indicators** is `16 (p₀ p₁)²`: their covariance
is `-p₀ p₁`. -/
theorem correlationNumerator_alleles (law : FiniteReportLaw TriallelicHaplotype) :
    correlationNumerator law alleleScore alleleOutcome
      = 16 * (law.mass (fun _ ↦ 0) * law.mass (fun _ ↦ 1)) ^ 2 := by
  obtain ⟨hscore, houtcome, -, -, hmixed⟩ := expectations_alleles law
  rw [correlationNumerator, FiniteReportLaw.covariance_eq_rawMoments, hmixed, hscore, houtcome]
  ring

/-- **The correlation denominator of the two allele indicators** is
`16 p₀ (1 - p₀) p₁ (1 - p₁)`. -/
theorem correlationDenominator_alleles (law : FiniteReportLaw TriallelicHaplotype) :
    correlationDenominator law alleleScore alleleOutcome
      = 16 * (law.mass (fun _ ↦ 0) * (1 - law.mass (fun _ ↦ 0))
        * (law.mass (fun _ ↦ 1) * (1 - law.mass (fun _ ↦ 1)))) := by
  obtain ⟨hscore, houtcome, hscoreSquare, houtcomeSquare, -⟩ := expectations_alleles law
  rw [correlationDenominator, FiniteReportLaw.variance_eq_rawMoments,
    FiniteReportLaw.variance_eq_rawMoments, hscoreSquare, houtcomeSquare, hscore, houtcome]
  ring

/-- **The target correlation numerator at parameter `q`** is `q² (1 - q)²`. -/
theorem correlationNumerator_target (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    correlationNumerator (stateLaw (lineState q hq) true) alleleScore alleleOutcome
      = q ^ 2 * (1 - q) ^ 2 := by
  obtain ⟨hzero, hone, -, -⟩ := mass_lineLaw q hq
  rw [stateLaw_lineState, correlationNumerator_alleles, hzero, hone]
  ring

/-- **The target correlation denominator at parameter `q`** is `q (2 - q) (1 - q²)`. -/
theorem correlationDenominator_target (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    correlationDenominator (stateLaw (lineState q hq) true) alleleScore alleleOutcome
      = q * (2 - q) * (1 - q ^ 2) := by
  obtain ⟨hzero, hone, -, -⟩ := mass_lineLaw q hq
  rw [stateLaw_lineState, correlationDenominator_alleles, hzero, hone]
  ring

/-- The source correlation numerator is `1/16` at every parameter. -/
theorem correlationNumerator_source (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    correlationNumerator (stateLaw (lineState q hq) false) alleleScore alleleOutcome = 1 / 16 := by
  obtain ⟨-, -, hzero, hone⟩ := mass_lineLaw q hq
  rw [stateLaw_lineState, correlationNumerator_alleles, hzero, hone]
  norm_num

/-- The source correlation denominator is `9/16` at every parameter. -/
theorem correlationDenominator_source (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    correlationDenominator (stateLaw (lineState q hq) false) alleleScore alleleOutcome
      = 9 / 16 := by
  obtain ⟨-, -, hzero, hone⟩ := mass_lineLaw q hq
  rw [stateLaw_lineState, correlationDenominator_alleles, hzero, hone]
  norm_num

/-- The correlation numerator of a deme is a continuous observable of the state. -/
theorem continuous_correlationNumerator (deme : Bool) :
    Continuous fun y : WitnessState ↦
      correlationNumerator (stateLaw y deme) alleleScore alleleOutcome := by
  have h : Continuous fun y : WitnessState ↦
      polynomialFunction (numeratorPolynomial deme alleleScore alleleOutcome) y :=
    (polynomialFunction _).continuous
  simpa only [polynomialFunction_numeratorPolynomial] using h

/-- The correlation denominator of a deme is a continuous observable of the state. -/
theorem continuous_correlationDenominator (deme : Bool) :
    Continuous fun y : WitnessState ↦
      correlationDenominator (stateLaw y deme) alleleScore alleleOutcome := by
  have h : Continuous fun y : WitnessState ↦
      polynomialFunction (denominatorPolynomial deme alleleScore alleleOutcome) y :=
    (polynomialFunction _).continuous
  simpa only [polynomialFunction_denominatorPolynomial] using h

/-! ## Two laws of the parameter -/

/-- The state at parameter `1/4`. -/
def quarterState : WitnessState := lineState (1 / 4) ⟨by norm_num, by norm_num⟩

/-- The state at parameter `3/4`. -/
def threeQuarterState : WitnessState := lineState (3 / 4) ⟨by norm_num, by norm_num⟩

/-- The state at parameter `0`. -/
def zeroState : WitnessState := lineState 0 ⟨le_rfl, zero_le_one⟩

/-- The state at parameter `1/2`. -/
def halfState : WitnessState := lineState (1 / 2) ⟨by norm_num, by norm_num⟩

/-- The state at parameter `1`. -/
def oneState : WitnessState := lineState 1 ⟨zero_le_one, le_rfl⟩

/-- The first law: parameter `1/4` or `3/4`, each with probability `1/2`. -/
def firstLaw : Measure WitnessState :=
  ENNReal.ofReal (1 / 2) • Measure.dirac quarterState
    + ENNReal.ofReal (1 / 2) • Measure.dirac threeQuarterState

/-- The second law: parameter `0`, `1/2` or `1`, with probabilities `1/8`, `3/4` and `1/8`. -/
def secondLaw : Measure WitnessState :=
  ENNReal.ofReal (1 / 8) • Measure.dirac zeroState
    + ENNReal.ofReal (3 / 4) • Measure.dirac halfState
    + ENNReal.ofReal (1 / 8) • Measure.dirac oneState

/-- A continuous observable integrates against a weighted point mass to the weighted value. -/
theorem integral_weightedDirac (w : ℝ) (hw : 0 ≤ w) (s : WitnessState) {f : WitnessState → ℝ}
    (hf : Continuous f) : ∫ y, f y ∂(ENNReal.ofReal w • Measure.dirac s) = w * f s := by
  rw [integral_smul_measure, integral_dirac' _ _ hf.stronglyMeasurable, ENNReal.toReal_ofReal hw,
    smul_eq_mul]

/-- A continuous observable is integrable against a weighted point mass. -/
theorem integrable_weightedDirac (w : ℝ) (s : WitnessState) {f : WitnessState → ℝ}
    (hf : Continuous f) : Integrable f (ENNReal.ofReal w • Measure.dirac s) :=
  (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A continuous observable integrates against the first law to its average at the parameters
`1/4` and `3/4`. -/
theorem integral_firstLaw {f : WitnessState → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂firstLaw = 1 / 2 * f quarterState + 1 / 2 * f threeQuarterState := by
  rw [firstLaw,
    integral_add_measure (integrable_weightedDirac _ _ hf) (integrable_weightedDirac _ _ hf),
    integral_weightedDirac (1 / 2) (by norm_num) quarterState hf,
    integral_weightedDirac (1 / 2) (by norm_num) threeQuarterState hf]

/-- A continuous observable integrates against the second law to its weighted values at the
parameters `0`, `1/2` and `1`. -/
theorem integral_secondLaw {f : WitnessState → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂secondLaw = 1 / 8 * f zeroState + 3 / 4 * f halfState + 1 / 8 * f oneState := by
  rw [secondLaw, integral_add_measure
      ((integrable_weightedDirac _ _ hf).add_measure (integrable_weightedDirac _ _ hf))
      (integrable_weightedDirac _ _ hf),
    integral_add_measure (integrable_weightedDirac _ _ hf) (integrable_weightedDirac _ _ hf),
    integral_weightedDirac (1 / 8) (by norm_num) zeroState hf,
    integral_weightedDirac (3 / 4) (by norm_num) halfState hf,
    integral_weightedDirac (1 / 8) (by norm_num) oneState hf]

/-- The first law is a probability measure. -/
instance isProbabilityMeasure_firstLaw : IsProbabilityMeasure firstLaw := by
  refine ⟨?_⟩
  simp only [firstLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

/-- The second law is a probability measure. -/
instance isProbabilityMeasure_secondLaw : IsProbabilityMeasure secondLaw := by
  refine ⟨?_⟩
  simp only [secondLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 / 8 by norm_num) (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 / 8 + 3 / 4 by norm_num)
      (show (0 : ℝ) ≤ 1 / 8 by norm_num)]
  norm_num

/-- The first process law: every state moves to a draw from the first law. -/
def firstKernel : Kernel WitnessState WitnessState :=
  Kernel.const _ firstLaw

/-- The second process law: every state moves to a draw from the second law. -/
def secondKernel : Kernel WitnessState WitnessState :=
  Kernel.const _ secondLaw

/-- The first process law is a Markov kernel. -/
instance isMarkovKernel_firstKernel : IsMarkovKernel firstKernel := by
  unfold firstKernel
  infer_instance

/-- The second process law is a Markov kernel. -/
instance isMarkovKernel_secondKernel : IsMarkovKernel secondKernel := by
  unfold secondKernel
  infer_instance

/-! ## Agreement through degree three -/

/-- The coordinates of the line of states as polynomials of degree at most one in the parameter. -/
def lineCoordinate (c : FrequencyVariable Bool Unit fun _ : Unit ↦ Fin 3) : Polynomial ℝ :=
  Polynomial.C (lineSlope c.1 (c.2 ())) * Polynomial.X + Polynomial.C (lineIntercept c.1 (c.2 ()))

/-- **A frequency polynomial along the line** is the polynomial in the parameter obtained by
substituting the affine coordinates. -/
theorem polynomialFunction_lineState (p : FrequencyPolynomial Bool Unit fun _ : Unit ↦ Fin 3)
    (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    polynomialFunction p (lineState q hq)
      = Polynomial.eval q (MvPolynomial.aeval lineCoordinate p) := by
  rw [polynomialFunction_apply]
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.aeval_C, Polynomial.algebraMap_eq,
      Polynomial.eval_C]
  | add p r hp hr => simp only [map_add, Polynomial.eval_add, hp, hr]
  | mul_X p c hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, Polynomial.eval_mul, hp,
      lineState_apply, lineCoordinate, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]

/-- **Substitution does not raise the degree**: the polynomial in the parameter has degree at most
the total degree of the frequency polynomial. -/
theorem natDegree_linePolynomial_le (p : FrequencyPolynomial Bool Unit fun _ : Unit ↦ Fin 3) :
    (MvPolynomial.aeval lineCoordinate p).natDegree ≤ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Polynomial.algebraMap_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun β hβ ↦ ?_
  have hlinear : ∀ c, (lineCoordinate c).natDegree ≤ 1 := fun _ ↦ Polynomial.natDegree_linear_le
  have hpower : ∀ c ∈ β.support, (lineCoordinate c ^ β c).natDegree ≤ β c := fun c _ ↦
    Polynomial.natDegree_pow_le.trans ((Nat.mul_le_mul le_rfl (hlinear c)).trans_eq (mul_one _))
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact (Finset.sum_le_sum hpower).trans (MvPolynomial.le_totalDegree hβ)

/-- **The two process laws agree on every frequency polynomial of total degree at most three.** -/
theorem polynomialsAgreeAt_three (x₁ x₂ : WitnessState) :
    PolynomialsAgreeAt 3 firstKernel secondKernel x₁ x₂ := by
  intro p hp
  have hdegree : (MvPolynomial.aeval lineCoordinate p).natDegree < 4 := by
    have h := (natDegree_linePolynomial_le p).trans hp
    omega
  have hcontinuous : Continuous fun y : WitnessState ↦ polynomialFunction p y :=
    (polynomialFunction p).continuous
  rw [firstKernel, secondKernel, Kernel.const_apply, Kernel.const_apply,
    integral_firstLaw hcontinuous, integral_secondLaw hcontinuous]
  simp only [quarterState, threeQuarterState, zeroState, halfState, oneState,
    polynomialFunction_lineState, Polynomial.eval_eq_sum_range' hdegree, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-! ## The separation -/

/-- **The expected correlation numerators and denominators under the first law**: `9/256` and
`105/256` in the target deme, `1/16` and `9/16` in the source deme. -/
theorem integrals_firstKernel (x : WitnessState) :
    ∫ y, correlationNumerator (stateLaw y true) alleleScore alleleOutcome ∂(firstKernel x)
        = 9 / 256
      ∧ ∫ y, correlationDenominator (stateLaw y true) alleleScore alleleOutcome ∂(firstKernel x)
        = 105 / 256
      ∧ ∫ y, correlationNumerator (stateLaw y false) alleleScore alleleOutcome ∂(firstKernel x)
        = 1 / 16
      ∧ ∫ y, correlationDenominator (stateLaw y false) alleleScore alleleOutcome ∂(firstKernel x)
        = 9 / 16 := by
  simp only [firstKernel, Kernel.const_apply]
  rw [integral_firstLaw (continuous_correlationNumerator true),
    integral_firstLaw (continuous_correlationDenominator true),
    integral_firstLaw (continuous_correlationNumerator false),
    integral_firstLaw (continuous_correlationDenominator false)]
  simp only [quarterState, threeQuarterState, correlationNumerator_target,
    correlationDenominator_target, correlationNumerator_source, correlationDenominator_source]
  norm_num

/-- **The expected correlation numerators and denominators under the second law**: `12/256` and
`108/256` in the target deme, `1/16` and `9/16` in the source deme. -/
theorem integrals_secondKernel (x : WitnessState) :
    ∫ y, correlationNumerator (stateLaw y true) alleleScore alleleOutcome ∂(secondKernel x)
        = 3 / 64
      ∧ ∫ y, correlationDenominator (stateLaw y true) alleleScore alleleOutcome ∂(secondKernel x)
        = 27 / 64
      ∧ ∫ y, correlationNumerator (stateLaw y false) alleleScore alleleOutcome ∂(secondKernel x)
        = 1 / 16
      ∧ ∫ y, correlationDenominator (stateLaw y false) alleleScore alleleOutcome ∂(secondKernel x)
        = 9 / 16 := by
  simp only [secondKernel, Kernel.const_apply]
  rw [integral_secondLaw (continuous_correlationNumerator true),
    integral_secondLaw (continuous_correlationDenominator true),
    integral_secondLaw (continuous_correlationNumerator false),
    integral_secondLaw (continuous_correlationDenominator false)]
  simp only [zeroState, halfState, oneState, correlationNumerator_target,
    correlationDenominator_target, correlationNumerator_source, correlationDenominator_source]
  norm_num

/-- **The squared-correlation portability under the first law is `27/35`.** -/
theorem expectedPortability_firstKernel (x : WitnessState) :
    expectedPortability firstKernel x false true alleleScore alleleOutcome = 27 / 35 := by
  obtain ⟨hnumerator, hdenominator, hsourceNumerator, hsourceDenominator⟩ :=
    integrals_firstKernel x
  rw [expectedPortability, hnumerator, hdenominator, hsourceNumerator, hsourceDenominator]
  norm_num

/-- **The squared-correlation portability under the second law is `1`.** -/
theorem expectedPortability_secondKernel (x : WitnessState) :
    expectedPortability secondKernel x false true alleleScore alleleOutcome = 1 := by
  obtain ⟨hnumerator, hdenominator, hsourceNumerator, hsourceDenominator⟩ :=
    integrals_secondKernel x
  rw [expectedPortability, hnumerator, hdenominator, hsourceNumerator, hsourceDenominator]
  norm_num

/-- **Degree three does not fix the squared-correlation portability.**  The two Markov kernels
agree, from any initial states, on every frequency polynomial of total degree at most three, and
give the score and the outcome different squared-correlation portability from the source deme
`false` to the target deme `true`. -/
theorem polynomialsAgreeAt_three_and_expectedPortability_ne (x₁ x₂ : WitnessState) :
    PolynomialsAgreeAt 3 firstKernel secondKernel x₁ x₂
      ∧ expectedPortability firstKernel x₁ false true alleleScore alleleOutcome
        ≠ expectedPortability secondKernel x₂ false true alleleScore alleleOutcome := by
  refine ⟨polynomialsAgreeAt_three x₁ x₂, ?_⟩
  rw [expectedPortability_firstKernel, expectedPortability_secondKernel]
  norm_num

/-- **The portability reports differ**: for every binary endpoint, the two process laws give the
score and the outcome different portability reports from the source deme `false` to the target
deme `true`. -/
theorem portabilityReport_ne (x₁ x₂ : WitnessState) (case : TriallelicHaplotype → Bool) :
    portabilityReport firstKernel x₁ false true alleleScore alleleOutcome case
      ≠ portabilityReport secondKernel x₂ false true alleleScore alleleOutcome case := fun h ↦
  (polynomialsAgreeAt_three_and_expectedPortability_ne x₁ x₂).2
    (congrArg PortabilityReport.accuracyPortability h)

/-- **Rung four is sharp: degree three does not fix the portability report.**  Agreement of two
Markov kernels on every frequency polynomial of total degree at most three does not force one
portability report, so no function of the degree-3 moments determines it. -/
theorem not_forall_portabilityReport_eq_of_polynomialsAgreeAt_three :
    ¬ ∀ (κ₁ κ₂ : Kernel WitnessState WitnessState) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
      (x₁ x₂ : WitnessState), PolynomialsAgreeAt 3 κ₁ κ₂ x₁ x₂ →
        ∀ (source target : Bool) (score outcome : TriallelicHaplotype → ℝ)
          (case : TriallelicHaplotype → Bool),
          portabilityReport κ₁ x₁ source target score outcome case
            = portabilityReport κ₂ x₂ source target score outcome case := fun h ↦
  portabilityReport_ne halfState halfState (fun _ ↦ true)
    (h firstKernel secondKernel halfState halfState (polynomialsAgreeAt_three halfState halfState)
      false true alleleScore alleleOutcome fun _ ↦ true)

end

end Descent.Portability.PortabilityMomentLadderSharpnessFour
