/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndGWASTrainingHistory

assert_below Descent.Decision Descent.Program

/-!
# The exact accuracy of a GWAS score trained on diploid individuals along a history

`EndToEndGWASTrainingHistory` carries a marginal-effect GWAS trained on haplotypes along a
demographic history at budget eight.  Polygenic scores are trained on diploid individuals.  This
module trains the GWAS on the gamete pairs of `EndToEndDiploidLaw` in the source deme, deploys the
score on the gamete pairs of the target deme, and carries both along a history at budget sixteen.

Gamete-pair masses.  At inbreeding coefficient `F` the mass of the ordered gamete pair `(a, b)` is
`(1 - F) p_a p_b` plus `F` times the probability that one haplotype drawn from `p` is `a = b`.  It
is a polynomial of total degree at most two in the haplotype frequencies (`pairMassPolynomial`,
`eval_pairMassPolynomial`, `totalDegree_pairMassPolynomial_le`).  Substituting it into a polynomial
in the pair masses evaluates that polynomial at the gamete-pair law
(`eval_bind₁_pairMassPolynomial`), and at most doubles its total degree (`totalDegree_bind₁_le`,
proved here from the monomial expansion).

The accumulators at a state.  The product, excess, pairing and target matrices of
`EndToEndGWASTrainingHistory` are polynomials of total degree at most four in the masses of any
finite law, the gamete-pair law included.  After substitution each has degree at most eight in the
haplotype frequencies of its deme, so every accumulator is a frequency polynomial of total degree
at most sixteen in the two demes jointly (`diploidTrainedPolynomial`,
`polynomialFunction_diploidTrainedPolynomial`, `totalDegree_diploidTrainedPolynomial_le`).  The
trained numerator and denominator of the gamete-pair laws of a state are sampling forms of three
such polynomials (`trainedNumerator_stateGenotypeLaw`, `trainedDenominator_stateGenotypeLaw`).

The law along a history.
* Under a Markov kernel whose budget-16 moments are a matrix `M`, the expected diploid trained
  numerator and denominator are sampling forms `a·v + b·v / n + c·v / (n (n − 1))` of written-out
  coefficient vectors, with `v = M · H₁₆(x₀)` (`momentDiploidAccumulator`,
  `integral_diploidTrainedNumerator_eq`, `integral_diploidTrainedDenominator_eq`).  The expected
  diploid trained accuracy is the rational function `momentDiploidTrainedAccuracy` of `v` and `n`
  (`expectedDiploidTrainedAccuracy_eq_moment`).
* The propagator is the chronological one along a history of epochs, splits and pulses, and the
  rate-history one along a rate path (`expectedDiploidTrainedAccuracy_historyEventKernel`,
  `expectedDiploidTrainedAccuracy_rateHistoryKernel`).
* Two event histories whose propagated budget-16 moments agree give equal expected diploid trained
  accuracy for every cohort size, genotype coding, outcome, source, target and choice of inbreeding
  coefficients (`expectedDiploidTrainedAccuracy_eq_of_moments_eq`).
* For additive score and outcome, the budget-eight diploid portability function of a rate history
  equals the haploid budget-four function of the same rate history
  (`diploidMomentPortability_diploidSum_rateHistoryKernel`).  `EndToEndDiploidHistoryLaw` states
  this for event histories.

Significance.  Training on diploid individuals keeps the finite-moment structure of the haploid
training law.  The accuracy of a score trained on genotypes, with any dominance or interaction
coding, is a rational function of finitely many history moments and of the cohort size.  The
budget doubles, and the inbreeding coefficients of the two demes enter the coefficients.

Scope.  The gamete pair is the one of `EndToEndDiploidLaw`: both gametes are drawn from the deme's
own haplotype law, and identity by descent is one whole-haplotype event with a coefficient supplied
per deme.  The genotype coding and the outcome are any real functions of the ordered gamete pair.
One training cohort per population, the unthresholded marginal GWAS, and the ratio-of-expectations
query.  The antitone and large-cohort statements of the haploid law are not restated at budget
sixteen.

## Empirical status

None.  The bodies are polynomial identities, finite sums against constructed laws and integrals of
polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndDiploidGWASTraining

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidLaw EndToEndDiploidHistoryLaw
  TrainingNoiseAccuracy FourCellCohortLaw EndToEndGWASTrainingLaw EndToEndGWASTrainingHistory
open scoped Matrix NNReal

noncomputable section

/-! ## Substituting the gamete-pair masses -/

/-- **Substitution multiplies the total degree by at most the degree of the substitutes.**  If
every substitute has total degree at most `d`, the substituted polynomial has total degree at most
`d` times the total degree of the original. -/
theorem totalDegree_bind₁_le {σ τ : Type*} (g : σ → MvPolynomial τ ℝ) (q : MvPolynomial σ ℝ)
    {d : ℕ} (hg : ∀ i, (g i).totalDegree ≤ d) :
    (bind₁ g q).totalDegree ≤ q.totalDegree * d := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm ↦ ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ i ∈ m.support, (g i ^ m i).totalDegree
      ≤ ∑ i ∈ m.support, m i * d :=
        Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans (Nat.mul_le_mul le_rfl (hg i))
    _ = (m.sum fun _ e ↦ e) * d := by simp only [Finsupp.sum, Finset.sum_mul]
    _ ≤ q.totalDegree * d := Nat.mul_le_mul (le_totalDegree hm) le_rfl

section Genotypes

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **The mass polynomial of a gamete pair** at inbreeding coefficient `F`: the product of the two
haplotype frequencies with weight `1 - F`, and the diagonal mass with weight `F`. -/
def pairMassPolynomial (F : ℝ) (pair : H × H) : MvPolynomial H ℝ :=
  C (1 - F) * (X pair.1 * X pair.2)
    + C F * expectationPolynomial fun haplotype ↦ if (haplotype, haplotype) = pair then 1 else 0

/-- **The mass polynomial evaluates to the mass of the gamete-pair law.** -/
theorem eval_pairMassPolynomial (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (pair : H × H) :
    eval law.mass (pairMassPolynomial F pair) = (inbredMating law F hF0 hF1).mass pair := by
  have hpoint : ∀ other : FiniteReportLaw (H × H),
      other.expectation (fun individual ↦ if individual = pair then 1 else 0) = other.mass pair :=
    fun other ↦ by simp [FiniteReportLaw.expectation, mul_ite]
  have hdiagonal : law.expectation
        (fun haplotype ↦ if (haplotype, haplotype) = pair then (1 : ℝ) else 0)
      = (law.pushforward fun haplotype ↦ (haplotype, haplotype)).mass pair := by
    rw [← hpoint, FiniteReportLaw.expectation_pushforward]
  simp only [pairMassPolynomial, map_add, map_mul, eval_C, eval_X, eval_expectationPolynomial,
    hdiagonal]
  change _ = ∑ identical, (FiniteDemographicSampling.bernoulli F hF0 hF1).mass identical
      * (cond identical (law.pushforward fun haplotype ↦ (haplotype, haplotype))
        (FiniteReproductiveKernel.independentMating law)).mass pair
  rw [Fintype.sum_bool]
  change _ = F * (law.pushforward fun haplotype ↦ (haplotype, haplotype)).mass pair
    + (1 - F) * (law.mass pair.1 * law.mass pair.2)
  ring

/-- The mass polynomial of a gamete pair has total degree at most two. -/
theorem totalDegree_pairMassPolynomial_le (F : ℝ) (pair : H × H) :
    (pairMassPolynomial F pair).totalDegree ≤ 2 := by
  have hproduct := totalDegree_mul (X pair.1 : MvPolynomial H ℝ) (X pair.2)
  have hleft := totalDegree_mul (C (1 - F)) (X pair.1 * X pair.2 : MvPolynomial H ℝ)
  have hdiagonal := totalDegree_expectationPolynomial_le fun haplotype : H ↦
    if (haplotype, haplotype) = pair then (1 : ℝ) else 0
  have hright := totalDegree_mul (C F) (expectationPolynomial fun haplotype : H ↦
    if (haplotype, haplotype) = pair then (1 : ℝ) else 0)
  rw [totalDegree_X, totalDegree_X] at hproduct
  rw [totalDegree_C] at hleft hright
  rw [pairMassPolynomial]
  exact (totalDegree_add _ _).trans (max_le (by omega) (by omega))

/-- **Substituting the pair masses evaluates at the gamete-pair law.**  A polynomial in the masses
of ordered gamete pairs, with the mass polynomials substituted, evaluates at a haplotype law to the
polynomial at the gamete-pair law formed from it. -/
theorem eval_bind₁_pairMassPolynomial (law : FiniteReportLaw H) (F : ℝ) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (q : MvPolynomial (H × H) ℝ) :
    eval law.mass (bind₁ (pairMassPolynomial F) q) = eval (inbredMating law F hF0 hF1).mass q := by
  have hsubstitution : eval law.mass (bind₁ (pairMassPolynomial F) q)
      = eval (fun pair ↦ eval law.mass (pairMassPolynomial F pair)) q :=
    eval₂Hom_bind₁ (RingHom.id ℝ) law.mass (pairMassPolynomial F) q
  have hmass : (fun pair ↦ eval law.mass (pairMassPolynomial F pair))
      = (inbredMating law F hF0 hF1).mass :=
    funext fun pair ↦ eval_pairMassPolynomial law F hF0 hF1 pair
  rw [hsubstitution, hmass]

end Genotypes

/-! ## The diploid accumulators as frequency polynomials of two demes -/

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {J : Type*} [Fintype J]

/-- **The diploid trained accumulator polynomial**: a source matrix and a target matrix of
polynomials in the gamete-pair masses, each substituted at the inbreeding coefficient of its deme,
read against each other as a frequency polynomial of the two demes. -/
def diploidTrainedPolynomial (source target : Deme) (inbreeding : Deme → ℝ)
    (sourceMatrix targetMatrix :
      J → J → MvPolynomial (FullHaplotype Locus Allele × FullHaplotype Locus Allele) ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  trainedPolynomial source target
    (fun i j ↦ bind₁ (pairMassPolynomial (inbreeding source)) (sourceMatrix i j))
    (fun i j ↦ bind₁ (pairMassPolynomial (inbreeding target)) (targetMatrix i j))

/-- At a state, the diploid trained polynomial reads the target matrix at the gamete-pair law of
the target deme against the source matrix at the gamete-pair law of the source deme. -/
theorem polynomialFunction_diploidTrainedPolynomial (source target : Deme)
    (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1)
    (sourceMatrix targetMatrix :
      J → J → MvPolynomial (FullHaplotype Locus Allele × FullHaplotype Locus Allele) ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction
        (diploidTrainedPolynomial source target inbreeding sourceMatrix targetMatrix) y
      = ∑ i, ∑ j, eval (stateGenotypeLaw y target inbreeding hF0 hF1).mass (targetMatrix i j)
          * eval (stateGenotypeLaw y source inbreeding hF0 hF1).mass (sourceMatrix i j) := by
  rw [diploidTrainedPolynomial, polynomialFunction_trainedPolynomial]
  simp only [stateGenotypeLaw,
    eval_bind₁_pairMassPolynomial (stateLaw y target) (inbreeding target) (hF0 target)
      (hF1 target),
    eval_bind₁_pairMassPolynomial (stateLaw y source) (inbreeding source) (hF0 source)
      (hF1 source)]

/-- **The diploid trained polynomial has total degree at most sixteen** when both matrices have
total degree at most four in the gamete-pair masses. -/
theorem totalDegree_diploidTrainedPolynomial_le (source target : Deme) (inbreeding : Deme → ℝ)
    (sourceMatrix targetMatrix :
      J → J → MvPolynomial (FullHaplotype Locus Allele × FullHaplotype Locus Allele) ℝ)
    (hsource : ∀ i j, (sourceMatrix i j).totalDegree ≤ 4)
    (htarget : ∀ i j, (targetMatrix i j).totalDegree ≤ 4) :
    (diploidTrainedPolynomial source target inbreeding sourceMatrix targetMatrix).totalDegree
      ≤ 16 := by
  have hsubstituted : ∀ (deme : Deme)
      (matrix : J → J → MvPolynomial (FullHaplotype Locus Allele × FullHaplotype Locus Allele) ℝ),
      (∀ i j, (matrix i j).totalDegree ≤ 4) → ∀ i j,
        (demePolynomial deme
          (bind₁ (pairMassPolynomial (inbreeding deme)) (matrix i j))).totalDegree ≤ 8 := by
    intro deme matrix hmatrix i j
    exact (totalDegree_rename_le _ _).trans
      ((totalDegree_bind₁_le _ _ (totalDegree_pairMassPolynomial_le _)).trans
        (Nat.mul_le_mul (hmatrix i j) (le_refl 2)))
  rw [diploidTrainedPolynomial, trainedPolynomial]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  have htargetDeme := hsubstituted target targetMatrix htarget i j
  have hsourceDeme := hsubstituted source sourceMatrix hsource i j
  exact (totalDegree_mul _ _).trans (by omega)

/-- **At a state, the diploid trained numerator is a sampling form of three polynomial
observables** of total degree at most sixteen: the GWAS is trained on the gamete-pair law of the
source deme and deployed on the gamete-pair law of the target deme. -/
theorem trainedNumerator_stateGenotypeLaw (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ}
    (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    trainedNumerator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (stateGenotypeLaw y target inbreeding hF0 hF1) size genotype outcome
      = samplingForm
          (polynomialFunction (diploidTrainedPolynomial source target inbreeding
            (weightProductPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (diploidTrainedPolynomial source target inbreeding
            (weightExcessPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (diploidTrainedPolynomial source target inbreeding
            (weightPairingPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y) size := by
  rw [trainedNumerator_eq _ _ hsize, correlationNumerator_linearScore]
  simp only [polynomialFunction_diploidTrainedPolynomial source target inbreeding hF0 hF1,
    eval_weightProductPolynomial, eval_weightExcessPolynomial, eval_weightPairingPolynomial,
    eval_numeratorMatrixPolynomial]

/-- **At a state, the diploid trained denominator is a sampling form of three polynomial
observables** of total degree at most sixteen. -/
theorem trainedDenominator_stateGenotypeLaw (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ}
    (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    trainedDenominator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (stateGenotypeLaw y target inbreeding hF0 hF1) size genotype outcome
      = samplingForm
          (polynomialFunction (diploidTrainedPolynomial source target inbreeding
            (weightProductPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (diploidTrainedPolynomial source target inbreeding
            (weightExcessPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (diploidTrainedPolynomial source target inbreeding
            (weightPairingPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y) size := by
  rw [trainedDenominator_eq _ _ hsize, correlationDenominator_linearScore]
  simp only [polynomialFunction_diploidTrainedPolynomial source target inbreeding hF0 hF1,
    eval_weightProductPolynomial, eval_weightExcessPolynomial, eval_weightPairingPolynomial,
    eval_denominatorMatrixPolynomial]

/-! ## The rational diploid trained accuracy -/

/-- **The rational diploid trained accumulator** of a budget-16 moment vector: the product, excess
and pairing coefficient vectors read against a target matrix, dotted with the moments, and combined
in the sampling form of the cohort size. -/
def momentDiploidAccumulator (ℓ₀ : Locus) (source target : Deme) (inbreeding : Deme → ℝ)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ)
    (targetMatrix :
      J → J → MvPolynomial (FullHaplotype Locus Allele × FullHaplotype Locus Allele) ℝ)
    (size : ℕ) (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 16) → ℝ) : ℝ :=
  samplingForm
    (budgetCoefficients ℓ₀ (fun _ ↦ 16) (diploidTrainedPolynomial source target inbreeding
      (weightProductPolynomial genotype outcome) targetMatrix) ⬝ᵥ v)
    (budgetCoefficients ℓ₀ (fun _ ↦ 16) (diploidTrainedPolynomial source target inbreeding
      (weightExcessPolynomial genotype outcome) targetMatrix) ⬝ᵥ v)
    (budgetCoefficients ℓ₀ (fun _ ↦ 16) (diploidTrainedPolynomial source target inbreeding
      (weightPairingPolynomial genotype outcome) targetMatrix) ⬝ᵥ v) size

/-- **The rational diploid trained accuracy** of a budget-16 moment vector and a cohort size: the
numerator accumulator over the denominator accumulator. -/
def momentDiploidTrainedAccuracy (ℓ₀ : Locus) (source target : Deme) (inbreeding : Deme → ℝ)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) (size : ℕ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 16) → ℝ) : ℝ :=
  momentDiploidAccumulator ℓ₀ source target inbreeding genotype outcome
      (numeratorMatrixPolynomial genotype outcome) size v
    / momentDiploidAccumulator ℓ₀ source target inbreeding genotype outcome
      (denominatorMatrixPolynomial genotype outcome) size v

/-- **The expected diploid trained accuracy of a kernel**: the expected target numerator of a GWAS
score trained on `size` gamete pairs of the source deme and deployed on the gamete pairs of the
target deme, over its expected target denominator, the expectations taken over the populations of
the kernel and the training cohort of each.  NOTE2 §6.2 query: a ratio of expectations. -/
def expectedDiploidTrainedAccuracy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1) (size : ℕ)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, trainedNumerator (stateGenotypeLaw y source inbreeding hF0 hF1)
      (stateGenotypeLaw y target inbreeding hF0 hF1) size genotype outcome ∂(κ x0))
    / ∫ y, trainedDenominator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (stateGenotypeLaw y target inbreeding hF0 hF1) size genotype outcome ∂(κ x0)

/-! ## Integrating against a kernel with budget-16 moments -/

section MomentKernel

variable (ℓ₀ : Locus)
  (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
  [IsMarkovKernel κ]
  (M : Matrix (BudgetConfiguration Deme Locus Allele (fun _ ↦ 16))
    (BudgetConfiguration Deme Locus Allele (fun _ ↦ 16)) ℝ)
  (hmoment : ∀ (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ 16)),
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
      = (M *ᵥ budgetMomentFeature (fun _ ↦ 16) x) ξ)

include hmoment

/-- **The expected diploid trained numerator under a kernel with budget-16 moments** is the
rational accumulator of the numerator matrix at the propagated moments. -/
theorem integral_diploidTrainedNumerator_eq (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedNumerator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (stateGenotypeLaw y target inbreeding hF0 hF1) size genotype outcome ∂(κ x0)
      = momentDiploidAccumulator ℓ₀ source target inbreeding genotype outcome
          (numeratorMatrixPolynomial genotype outcome) size
          (M *ᵥ budgetMomentFeature (fun _ ↦ 16) x0) := by
  simp only [trainedNumerator_stateGenotypeLaw source target inbreeding hF0 hF1 hsize genotype
    outcome]
  exact integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    (totalDegree_diploidTrainedPolynomial_le _ _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome))
    (totalDegree_diploidTrainedPolynomial_le _ _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome))
    (totalDegree_diploidTrainedPolynomial_le _ _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_numeratorMatrixPolynomial_le genotype outcome))

/-- **The expected diploid trained denominator under a kernel with budget-16 moments** is the
rational accumulator of the denominator matrix at the propagated moments. -/
theorem integral_diploidTrainedDenominator_eq (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    ∫ y, trainedDenominator (stateGenotypeLaw y source inbreeding hF0 hF1)
        (stateGenotypeLaw y target inbreeding hF0 hF1) size genotype outcome ∂(κ x0)
      = momentDiploidAccumulator ℓ₀ source target inbreeding genotype outcome
          (denominatorMatrixPolynomial genotype outcome) size
          (M *ᵥ budgetMomentFeature (fun _ ↦ 16) x0) := by
  simp only [trainedDenominator_stateGenotypeLaw source target inbreeding hF0 hF1 hsize genotype
    outcome]
  exact integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    (totalDegree_diploidTrainedPolynomial_le _ _ _ _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome))
    (totalDegree_diploidTrainedPolynomial_le _ _ _ _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome))
    (totalDegree_diploidTrainedPolynomial_le _ _ _ _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_denominatorMatrixPolynomial_le genotype outcome))

/-- **The expected diploid trained accuracy under a kernel with budget-16 moments** is the rational
diploid trained accuracy of the propagated moments. -/
theorem expectedDiploidTrainedAccuracy_eq_moment (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidTrainedAccuracy κ x0 source target inbreeding hF0 hF1 size genotype outcome
      = momentDiploidTrainedAccuracy ℓ₀ source target inbreeding genotype outcome size
          (M *ᵥ budgetMomentFeature (fun _ ↦ 16) x0) := by
  rw [expectedDiploidTrainedAccuracy,
    integral_diploidTrainedNumerator_eq ℓ₀ κ M hmoment x0 source target inbreeding hF0 hF1 hsize,
    integral_diploidTrainedDenominator_eq ℓ₀ κ M hmoment x0 source target inbreeding hF0 hF1
      hsize, momentDiploidTrainedAccuracy]

end MomentKernel

/-! ## The law along a history -/

/-- **The end-to-end diploid trained-accuracy law along a history of epochs, splits and pulses.**
The expected accuracy of a GWAS score trained on `size` gamete pairs of the source deme and
deployed on the gamete pairs of the target deme is the rational function
`momentDiploidTrainedAccuracy` of the chronological propagator applied to the budget-16 moments of
the initial state, and of `size`. -/
theorem expectedDiploidTrainedAccuracy_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (inbreeding : Deme → ℝ)
    (hF0 : ∀ other, 0 ≤ inbreeding other) (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ}
    (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidTrainedAccuracy (historyEventKernel ℓ₀ hap₀ events) x0 source target inbreeding
        hF0 hF1 size genotype outcome
      = momentDiploidTrainedAccuracy ℓ₀ source target inbreeding genotype outcome size
          (historyEventPropagator (fun _ ↦ 16) events *ᵥ budgetMomentFeature (fun _ ↦ 16) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedDiploidTrainedAccuracy_eq_moment ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 16) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 16) events) x0 source target
    inbreeding hF0 hF1 hsize genotype outcome

/-- **The end-to-end diploid trained-accuracy law along a rate history.**  The expected diploid
trained accuracy is the rational function `momentDiploidTrainedAccuracy` of the propagator of the
rate history applied to the budget-16 moments of the initial state, and of the cohort size. -/
theorem expectedDiploidTrainedAccuracy_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidTrainedAccuracy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 source
        target inbreeding hF0 hF1 size genotype outcome
      = momentDiploidTrainedAccuracy ℓ₀ source target inbreeding genotype outcome size
          (rateHistoryDualPropagator rates (fun _ ↦ 16) T
            *ᵥ budgetMomentFeature (fun _ ↦ 16) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedDiploidTrainedAccuracy_eq_moment ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous)
    (rateHistoryDualPropagator rates (fun _ ↦ 16) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 16)) x0 source
    target inbreeding hF0 hF1 hsize genotype outcome

/-- **Diploid trained accuracy sees the history only through finitely many moments.**  Two
histories, from two initial states, whose propagated budget-16 moments agree give equal expected
diploid trained accuracy for every cohort size, genotype coding, outcome, source, target and choice
of inbreeding coefficients. -/
theorem expectedDiploidTrainedAccuracy_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 16) first
        *ᵥ budgetMomentFeature (fun _ ↦ 16) x₁
      = historyEventPropagator (fun _ ↦ 16) second *ᵥ budgetMomentFeature (fun _ ↦ 16) x₂)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele × FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele × FullHaplotype Locus Allele → ℝ) :
    expectedDiploidTrainedAccuracy (historyEventKernel ℓ₀ hap₀ first) x₁ source target inbreeding
        hF0 hF1 size genotype outcome
      = expectedDiploidTrainedAccuracy (historyEventKernel ℓ₀ hap₀ second) x₂ source target
          inbreeding hF0 hF1 size genotype outcome := by
  rw [expectedDiploidTrainedAccuracy_historyEventKernel ℓ₀ hap₀ first x₁ source target inbreeding
      hF0 hF1 hsize,
    expectedDiploidTrainedAccuracy_historyEventKernel ℓ₀ hap₀ second x₂ source target inbreeding
      hF0 hF1 hsize, hmoments]

/-! ## The additive agreement along a rate history -/

/-- **The two budgets agree on additive observables along a rate history.**  For additive score and
outcome, the budget-eight diploid function of the budget-eight moments of a rate history equals the
haploid budget-four function of the budget-four moments of the same rate history, whatever the
inbreeding coefficients. -/
theorem diploidMomentPortability_diploidSum_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (source target : Deme) (inbreeding : Deme → ℝ) (hF0 : ∀ other, 0 ≤ inbreeding other)
    (hF1 : ∀ other, inbreeding other ≤ 1) (score outcome : FullHaplotype Locus Allele → ℝ) :
    diploidMomentPortability ℓ₀ source target inbreeding (diploidSum score) (diploidSum outcome)
        (rateHistoryDualPropagator rates (fun _ ↦ 8) T *ᵥ budgetMomentFeature (fun _ ↦ 8) x0)
      = momentPortability ℓ₀ source target score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ 4) T
            *ᵥ budgetMomentFeature (fun _ ↦ 4) x0) := by
  rw [← expectedDiploidPortability_rateHistoryKernel_budgetEight hT hcontinuous ℓ₀ hap₀ x0 source
    target inbreeding hF0 hF1, expectedDiploidPortability_rateHistoryKernel]

end History

end

end Descent.Portability.EndToEndDiploidGWASTraining
