/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDiploidGWASTraining
import Descent.Portability.EndToEndGWASCalibrationLaw

assert_below Descent.Decision Descent.Program

/-!
# A GWAS trained on a cohort pooled over several demes

`EndToEndGWASTrainingLaw`, `EndToEndGWASCalibrationLaw` and `EndToEndGWASTrainingHistory` train
the marginal-effect GWAS on individuals of one source deme.  This module trains it on a cohort
pooled over several demes and deploys the score in a target deme.

The pooled law.  The shares of the demes are a finite law `π` on the demes, so they are
nonnegative and sum to one.  An individual of the pooled cohort is drawn from deme `d` with
probability `π_d` and then from that deme's law (`mixtureLaw`, `mixtureLaw_mass`).  Its
expectations are the share-weighted deme expectations (`expectation_mixtureLaw`), and its
covariances obey the law of total covariance: the share-weighted within-deme covariance plus the
covariance, across demes, of the deme means (`covariance_mixtureLaw`, `variance_mixtureLaw`).  A
unit share pools nothing (`mixtureLaw_pointMass`).

The pooled marginal effect.  A GWAS on the pooled cohort estimates, without bias, the pooled
tag–outcome covariance `E_π c_d + B`: the share-weighted deme covariances plus the between-deme
term `B_j = Cov_π(μ_d(X_j), μ_d(Y))` (`betweenWeights`, `marginalWeights_mixtureLaw`).  The
per-locus regression slope `C(X_j, Y) / V(X_j)` (`marginalEffect`) of the pooled cohort is a ratio
of mixed moments, `(E_π[β_d V_d] + B_j) / (E_π V_d + Var_π μ_d(X_j))`, with `β_d` and `V_d` the
effect and the tag variance of deme `d` (`marginalEffect_mixtureLaw`,
`marginalEffect_mul_tagCovariance`).  It weights each deme effect by its share times its tag
variance and adds a term that no deme effect carries, so it is not the mixture `E_π β_d` of the
deme effects.  On two demes of share one half, in each of which the tag varies and does not covary
with the outcome, every deme effect is zero and the pooled effect is one half; the population
score trained on the pooled cohort has calibration slope zero in either deme
(`stratificationWitness`).

Deployment in a target law.  The expected target covariance of the pooled-trained score has no
sampling term and splits by deme: the share-weighted target covariance of the per-deme population
scores plus the target covariance of the between-deme score `∑_j B_j X_j`
(`covariance_linearScore_mixtureWeights`, `trainedCovariance_mixtureLaw`).  As the cohort grows,
the trained calibration slope tends to that covariance over the target variance of the pooled
population score (`tendsto_pooledTrainedCalibrationSlope`).  With two demes and weight `s` on the
target deme (`targetShare`, `expectation_targetShare`, `covariance_targetShare`), the pooled
marginal effects are the interpolation `(1 − s) c_source + s c_target` plus the stratification
term `s (1 − s) Δμ(X_j) Δμ(Y)`, and a unit weight on the target deme gives the target law
(`marginalWeights_twoDemeMixture`, `mixtureLaw_targetShare_one`).

Along a history.  At a state the pooled haplotype frequency `∑_d π_d x_d[h]` has degree one
(`pooledMassPolynomial`), so a polynomial in the haplotype frequencies read at the pooled
frequencies keeps its degree (`pooledPolynomial`, `eval_pooledPolynomial`,
`totalDegree_pooledPolynomial_le`).  The expected target covariance, variance, correlation
numerator and denominator of the pooled-trained score are frequency polynomials of total degree at
most four, six, eight and eight (`pooledCovariancePolynomial`, `pooledTrainedPolynomial`,
`totalDegree_pooledCovariancePolynomial_le`, `totalDegree_pooledTrainedPolynomial_le`,
`expectation_quadraticForm_pooledStateLaw`, `trainedCovariance_pooledStateLaw`,
`trainedVariance_pooledStateLaw`, `trainedNumerator_pooledStateLaw`,
`trainedDenominator_pooledStateLaw`).  So along epochs, splits and pulses, or along a rate history,
the calibration slope of expectations of the pooled-trained score in the target deme is the
rational function `momentPooledCalibrationSlope` of the propagated budget-6 moments and `n`, and
its accuracy is `momentPooledAccuracy` of the budget-8 moments
(`expectedPooledCalibrationSlope_historyEventKernel`, `expectedPooledAccuracy_historyEventKernel`,
`expectedPooledCalibrationSlope_rateHistoryKernel`, `expectedPooledAccuracy_rateHistoryKernel`).
Two histories with equal propagated moments give equal pooled slope and accuracy for every share,
target, tag set, outcome and cohort size (`expectedPooledCalibrationSlope_eq_of_moments_eq`,
`expectedPooledAccuracy_eq_of_moments_eq`).  The budgets are those of the one-deme laws, and a unit
share gives the one-deme trained accuracy (`expectedPooledAccuracy_pointMass`).

Significance.  A GWAS on a multi-ancestry cohort estimates a ratio of mixed moments that can be
carried entirely by the covariance of deme means, and demography reaches the calibration and
accuracy of the score it trains only through the same finitely many moments as a one-deme GWAS.

Scope.  Each individual of the cohort is drawn independently from the pooled law, so the number
of individuals from each deme is random; a cohort with fixed deme counts is not treated.  The
estimator is the marginal sample covariance on the pooled cohort, with no ancestry covariates, no
principal components and no per-deme meta-analysis.  The query is the ratio of expectations over
the cohort and the history.  The budgets are upper bounds from the degree count; that no smaller
budget suffices is not proved.  No sign is stated for the effect of the target weight on the
target slope.

## Empirical status

None.  The bodies are identities between finite sums over stipulated finite laws, integrals of
polynomials against Markov kernels and an explicit two-deme computation, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndMultiAncestryGWAS

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel NeutralRateHistoryRealization
  NeutralRateHistoryKernel ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiploidHistoryLaw
  TrainingNoiseAccuracy FourCellCohortLaw EndToEndGWASTrainingLaw EndToEndGWASTrainingHistory
  EndToEndGWASCalibrationLaw
open scoped Matrix NNReal

noncomputable section

/-! ## The pooled training law -/

section Pooling

variable {D Ω : Type*} [Fintype D] [Fintype Ω]

/-- **The pooled training law**: draw a deme with its share, then an individual from that deme's
law.  The shares are a finite law on the demes, so they are nonnegative and sum to one. -/
def mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω) :
    FiniteReportLaw Ω where
  mass individual := ∑ d, share.mass d * (laws d).mass individual
  mass_nonneg individual := Finset.sum_nonneg fun d _ ↦
    mul_nonneg (share.mass_nonneg d) ((laws d).mass_nonneg individual)
  mass_sum := by
    show ∑ individual, ∑ d, share.mass d * (laws d).mass individual = 1
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]

/-- The pooled mass of an individual is its share-weighted deme mass. -/
theorem mixtureLaw_mass (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (individual : Ω) :
    (mixtureLaw share laws).mass individual = ∑ d, share.mass d * (laws d).mass individual :=
  rfl

/-- **Expectation under the pooled law** is the share-weighted expectation of the deme
expectations. -/
theorem expectation_mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (value : Ω → ℝ) :
    (mixtureLaw share laws).expectation value
      = share.expectation fun d ↦ (laws d).expectation value := by
  simp only [FiniteReportLaw.expectation, mixtureLaw_mass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The law of total covariance for a pooled cohort.**  The pooled covariance of two observables
is the share-weighted within-deme covariance plus the covariance, across demes, of the deme
means. -/
theorem covariance_mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (first second : Ω → ℝ) :
    (mixtureLaw share laws).covariance first second
      = share.expectation (fun d ↦ (laws d).covariance first second)
        + share.covariance (fun d ↦ (laws d).expectation first)
          (fun d ↦ (laws d).expectation second) := by
  simp only [FiniteReportLaw.covariance_eq_rawMoments, expectation_mixtureLaw]
  simp only [FiniteReportLaw.expectation, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **The law of total variance for a pooled cohort.** -/
theorem variance_mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (value : Ω → ℝ) :
    (mixtureLaw share laws).variance value
      = share.expectation (fun d ↦ (laws d).variance value)
        + share.variance fun d ↦ (laws d).expectation value :=
  covariance_mixtureLaw share laws value value

/-- **A unit share pools nothing**: the pooled law of a point mass on a deme is that deme's
law. -/
theorem mixtureLaw_pointMass (deme : D) (laws : D → FiniteReportLaw Ω) :
    mixtureLaw (FiniteReportLaw.pointMass deme) laws = laws deme := by
  ext individual
  rw [mixtureLaw_mass, Finset.sum_eq_single deme]
  · simp [FiniteReportLaw.pointMass]
  · intro other _ hother
    simp [FiniteReportLaw.pointMass, hother]
  · intro hdeme
    exact absurd (Finset.mem_univ deme) hdeme

variable {J : Type*}

/-- **The between-deme marginal effects**: the covariance, across demes, of the deme mean of each
tag with the deme mean of the outcome. -/
def betweenWeights (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) : J → ℝ :=
  fun marker ↦ share.covariance
    (fun d ↦ (laws d).expectation fun individual ↦ genotype individual marker)
    (fun d ↦ (laws d).expectation outcome)

/-- **The pooled marginal effects** that a GWAS on the pooled cohort estimates: the share-weighted
within-deme marginal effects plus the between-deme effects. -/
theorem marginalWeights_mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J) :
    marginalWeights (mixtureLaw share laws) genotype outcome marker
      = share.expectation (fun d ↦ marginalWeights (laws d) genotype outcome marker)
        + betweenWeights share laws genotype outcome marker :=
  covariance_mixtureLaw share laws _ outcome

/-- **The per-locus marginal effect**: the regression slope of the outcome on one tag, the
tag–outcome covariance over the tag variance, read as zero where the tag is constant. -/
def marginalEffect (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (marker : J) : ℝ :=
  marginalWeights law genotype outcome marker / tagCovariance law genotype marker marker

/-- **An effect times its tag variance is the tag–outcome covariance.**  Where the tag variance
vanishes, Cauchy–Schwarz forces the covariance to vanish as well. -/
theorem marginalEffect_mul_tagCovariance (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (marker : J) :
    marginalEffect law genotype outcome marker * tagCovariance law genotype marker marker
      = marginalWeights law genotype outcome marker := by
  by_cases hzero : tagCovariance law genotype marker marker = 0
  · have hsquare := law.covariance_sq_le_variance_mul
      (fun individual ↦ genotype individual marker) outcome
    have hvariance : law.variance (fun individual ↦ genotype individual marker) = 0 := hzero
    rw [hvariance, zero_mul] at hsquare
    have hcovariance : marginalWeights law genotype outcome marker = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsquare (sq_nonneg _))
    rw [hzero, mul_zero, hcovariance]
  · exact div_mul_cancel₀ _ hzero

/-- **The pooled marginal effect is a ratio of mixed moments.**  It is the pooled covariance over
the pooled variance: the share-weighted deme effects, each times its tag variance, plus the
between-deme effect, over the share-weighted tag variances plus the variance, across demes, of the
tag means. -/
theorem marginalEffect_mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J) :
    marginalEffect (mixtureLaw share laws) genotype outcome marker
      = (share.expectation (fun d ↦ marginalEffect (laws d) genotype outcome marker
            * tagCovariance (laws d) genotype marker marker)
          + betweenWeights share laws genotype outcome marker)
        / (share.expectation (fun d ↦ tagCovariance (laws d) genotype marker marker)
          + share.variance fun d ↦
            (laws d).expectation fun individual ↦ genotype individual marker) := by
  simp only [marginalEffect_mul_tagCovariance]
  rw [marginalEffect, marginalWeights_mixtureLaw]
  congr 1
  exact variance_mixtureLaw share laws _

end Pooling

/-! ## Pooling creates an effect that no deme carries -/

section Witness

/-- The witness tag, on individuals labelled by a deme bit and a within-deme bit: the sum of the
two bits. -/
def witnessGenotype (individual : Bool × Bool) (_ : Unit) : ℝ :=
  (if individual.1 then 1 else 0) + if individual.2 then 1 else 0

/-- The witness outcome: the deme bit. -/
def witnessOutcome (individual : Bool × Bool) : ℝ :=
  if individual.1 then 1 else 0

/-- The witness law of deme `d`: mass one half on each within-deme bit, with deme bit `d`. -/
def witnessDemeLaw (d : Bool) : FiniteReportLaw (Bool × Bool) where
  mass individual := if individual.1 = d then 1 / 2 else 0
  mass_nonneg individual := by
    show 0 ≤ (if individual.1 = d then (1 / 2 : ℝ) else 0)
    split_ifs <;> norm_num
  mass_sum := by
    show ∑ individual : Bool × Bool, (if individual.1 = d then (1 / 2 : ℝ) else 0) = 1
    cases d <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The mass of the witness law of a deme. -/
theorem witnessDemeLaw_mass (d : Bool) (individual : Bool × Bool) :
    (witnessDemeLaw d).mass individual = if individual.1 = d then 1 / 2 else 0 :=
  rfl

/-- **Pooling creates an effect that no deme carries.**  Two demes of share one half.  In each deme
the tag varies, with variance one quarter, and does not covary with the outcome, so each deme
effect is zero and so is their mixture.  The deme means of the tag and of the outcome move
together, so the pooled GWAS weight is one quarter and the pooled marginal effect one half, which
differs from the mixture of the deme effects.  The population score trained on the pooled cohort
has calibration slope zero in either deme. -/
theorem stratificationWitness :
    (∀ d, tagCovariance (witnessDemeLaw d) witnessGenotype () () = 1 / 4)
      ∧ (∀ d, marginalWeights (witnessDemeLaw d) witnessGenotype witnessOutcome () = 0)
      ∧ (SamplingDesignLaw.uniform Bool).expectation
          (fun d ↦ marginalEffect (witnessDemeLaw d) witnessGenotype witnessOutcome ()) = 0
      ∧ marginalWeights (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw)
          witnessGenotype witnessOutcome () = 1 / 4
      ∧ marginalEffect (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw)
          witnessGenotype witnessOutcome () = 1 / 2
      ∧ marginalEffect (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw)
          witnessGenotype witnessOutcome ()
        ≠ (SamplingDesignLaw.uniform Bool).expectation
          (fun d ↦ marginalEffect (witnessDemeLaw d) witnessGenotype witnessOutcome ())
      ∧ ∀ d, populationCalibrationSlope
          (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw) (witnessDemeLaw d)
          witnessGenotype witnessOutcome = 0 := by
  have hvariance : ∀ d, tagCovariance (witnessDemeLaw d) witnessGenotype () () = 1 / 4 := by
    intro d
    cases d <;> norm_num [tagCovariance, FiniteReportLaw.covariance_eq_rawMoments,
      FiniteReportLaw.expectation, Fintype.sum_prod_type, Fintype.sum_bool, witnessDemeLaw_mass,
      witnessGenotype]
  have hweight : ∀ d,
      marginalWeights (witnessDemeLaw d) witnessGenotype witnessOutcome () = 0 := by
    intro d
    cases d <;> norm_num [marginalWeights, FiniteReportLaw.covariance_eq_rawMoments,
      FiniteReportLaw.expectation, Fintype.sum_prod_type, Fintype.sum_bool, witnessDemeLaw_mass,
      witnessGenotype, witnessOutcome]
  have hmixture : (SamplingDesignLaw.uniform Bool).expectation
      (fun d ↦ marginalEffect (witnessDemeLaw d) witnessGenotype witnessOutcome ()) = 0 := by
    simp only [marginalEffect, hweight, zero_div, FiniteReportLaw.expectation, mul_zero,
      Finset.sum_const_zero]
  have hpooledWeight : marginalWeights (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw)
      witnessGenotype witnessOutcome () = 1 / 4 := by
    norm_num [marginalWeights, FiniteReportLaw.covariance_eq_rawMoments,
      FiniteReportLaw.expectation, mixtureLaw_mass, SamplingDesignLaw.uniform,
      Fintype.sum_prod_type, Fintype.sum_bool, witnessDemeLaw_mass, witnessGenotype,
      witnessOutcome]
  have hpooledVariance : tagCovariance
      (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw) witnessGenotype () ()
      = 1 / 2 := by
    norm_num [tagCovariance, FiniteReportLaw.covariance_eq_rawMoments,
      FiniteReportLaw.expectation, mixtureLaw_mass, SamplingDesignLaw.uniform,
      Fintype.sum_prod_type, Fintype.sum_bool, witnessDemeLaw_mass, witnessGenotype]
  have heffect : marginalEffect (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw)
      witnessGenotype witnessOutcome () = 1 / 2 := by
    rw [marginalEffect, hpooledWeight, hpooledVariance]
    norm_num
  have hslope : ∀ d, populationCalibrationSlope
      (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw) (witnessDemeLaw d)
      witnessGenotype witnessOutcome = 0 := by
    intro d
    have hcovariance : (witnessDemeLaw d).covariance (linearScore witnessGenotype
        (marginalWeights (mixtureLaw (SamplingDesignLaw.uniform Bool) witnessDemeLaw)
          witnessGenotype witnessOutcome)) witnessOutcome = 0 := by
      rw [covariance_linearScore]
      exact Finset.sum_eq_zero fun marker _ ↦ mul_eq_zero_of_right _ (hweight d)
    rw [populationCalibrationSlope, hcovariance, zero_div]
  refine ⟨hvariance, hweight, hmixture, hpooledWeight, heffect, ?_, hslope⟩
  rw [heffect, hmixture]
  norm_num

end Witness

/-! ## The pooled-trained score in a target law -/

section Deployment

variable {D Ω J : Type*} [Fintype D] [Fintype Ω] [Fintype J]

/-- **The target covariance of the pooled population score splits by deme**: the share-weighted
target covariance of the per-deme population scores plus the target covariance of the
between-deme score `∑_j B_j X_j`. -/
theorem covariance_linearScore_mixtureWeights (share : FiniteReportLaw D)
    (laws : D → FiniteReportLaw Ω) (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    target.covariance
        (linearScore genotype (marginalWeights (mixtureLaw share laws) genotype outcome)) outcome
      = share.expectation (fun d ↦ target.covariance
          (linearScore genotype (marginalWeights (laws d) genotype outcome)) outcome)
        + target.covariance
          (linearScore genotype (betweenWeights share laws genotype outcome)) outcome := by
  simp only [covariance_linearScore, marginalWeights_mixtureLaw, add_mul, Finset.sum_add_distrib]
  congr 1
  simp only [FiniteReportLaw.expectation, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The expected target covariance of the pooled-trained score splits by deme** at every cohort
size `n ≥ 2`, with no sampling term. -/
theorem trainedCovariance_mixtureLaw (share : FiniteReportLaw D) (laws : D → FiniteReportLaw Ω)
    (target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    trainedCovariance (mixtureLaw share laws) target size genotype outcome
      = share.expectation (fun d ↦ target.covariance
          (linearScore genotype (marginalWeights (laws d) genotype outcome)) outcome)
        + target.covariance
          (linearScore genotype (betweenWeights share laws genotype outcome)) outcome := by
  rw [trainedCovariance_eq _ _ hsize, covariance_linearScore_mixtureWeights]

/-- **The large-cohort slope of the pooled-trained score.**  As the cohort grows, the trained
calibration slope in the target tends to the share-weighted target covariance of the per-deme
population scores plus that of the between-deme score, over the target variance of the pooled
population score. -/
theorem tendsto_pooledTrainedCalibrationSlope (share : FiniteReportLaw D)
    (laws : D → FiniteReportLaw Ω) (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    Tendsto (fun size : ℕ ↦
        trainedCalibrationSlope (mixtureLaw share laws) target size genotype outcome) atTop
      (𝓝 ((share.expectation (fun d ↦ target.covariance
            (linearScore genotype (marginalWeights (laws d) genotype outcome)) outcome)
          + target.covariance
            (linearScore genotype (betweenWeights share laws genotype outcome)) outcome)
        / target.variance
          (linearScore genotype (marginalWeights (mixtureLaw share laws) genotype outcome)))) := by
  have hlimit := tendsto_trainedCalibrationSlope (mixtureLaw share laws) target genotype outcome
  rwa [populationCalibrationSlope, covariance_linearScore_mixtureWeights] at hlimit

/-- **Two demes with weight `s` on the target deme**: the share law puts `s` on `true`, the target
deme, and `1 − s` on `false`, the source deme. -/
def targetShare (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : FiniteReportLaw Bool where
  mass b := cond b s (1 - s)
  mass_nonneg b := by
    cases b
    · exact sub_nonneg.mpr hs1
    · exact hs0
  mass_sum := by
    rw [Fintype.sum_bool]
    show s + (1 - s) = 1
    ring

/-- The expectation under the two-deme share. -/
theorem expectation_targetShare (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (value : Bool → ℝ) :
    (targetShare s hs0 hs1).expectation value = (1 - s) * value false + s * value true := by
  rw [FiniteReportLaw.expectation, Fintype.sum_bool]
  show s * value true + (1 - s) * value false = _
  ring

/-- The covariance across the two demes: `s (1 − s)` times the product of the differences. -/
theorem covariance_targetShare (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (first second : Bool → ℝ) :
    (targetShare s hs0 hs1).covariance first second
      = s * (1 - s) * (first true - first false) * (second true - second false) := by
  simp only [FiniteReportLaw.covariance_eq_rawMoments, expectation_targetShare]
  ring

/-- **The two-deme pooled marginal effects** with weight `s` on the target deme: the interpolation
`(1 − s) c_source + s c_target` of the deme effects plus the stratification term
`s (1 − s) Δμ(X_j) Δμ(Y)`. -/
theorem marginalWeights_twoDemeMixture (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J) :
    marginalWeights (mixtureLaw (targetShare s hs0 hs1) fun b ↦ cond b target source) genotype
        outcome marker
      = (1 - s) * marginalWeights source genotype outcome marker
        + s * marginalWeights target genotype outcome marker
        + s * (1 - s)
          * (target.expectation (fun individual ↦ genotype individual marker)
            - source.expectation fun individual ↦ genotype individual marker)
          * (target.expectation outcome - source.expectation outcome) := by
  simp only [marginalWeights_mixtureLaw, betweenWeights, expectation_targetShare,
    covariance_targetShare, cond_true, cond_false] <;> ring

/-- **A unit weight on the target deme pools nothing**: the pooled law is the target law. -/
theorem mixtureLaw_targetShare_one (source target : FiniteReportLaw Ω) :
    mixtureLaw (targetShare 1 zero_le_one le_rfl) (fun b ↦ cond b target source) = target := by
  ext individual
  rw [mixtureLaw_mass, Fintype.sum_bool]
  show 1 * target.mass individual + (1 - 1) * source.mass individual = target.mass individual
  ring

end Deployment

/-! ## The pooled cohort along a history -/

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

section Polynomials

/-- **The pooled haplotype frequency** `∑_d π_d x_d[h]`, a frequency polynomial of degree one. -/
def pooledMassPolynomial (share : FiniteReportLaw Deme) (hap : FullHaplotype Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ d, C (share.mass d) * X (d, hap)

/-- **A polynomial in the haplotype frequencies read at the pooled frequencies.** -/
def pooledPolynomial (share : FiniteReportLaw Deme)
    (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) : FrequencyPolynomial Deme Locus Allele :=
  bind₁ (pooledMassPolynomial share) p

/-- **At a state, a pooled polynomial evaluates at the pooled law** of the deme laws. -/
theorem eval_pooledPolynomial (share : FiniteReportLaw Deme)
    (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) (y : FrequencyState Deme Locus Allele) :
    eval y.1 (pooledPolynomial share p) = eval (mixtureLaw share (stateLaw y)).mass p := by
  have hsubstitution : eval y.1 (pooledPolynomial share p)
      = eval (fun hap ↦ eval y.1 (pooledMassPolynomial share hap)) p :=
    eval₂Hom_bind₁ (RingHom.id ℝ) y.1 (pooledMassPolynomial share) p
  have hmass : (fun hap ↦ eval y.1 (pooledMassPolynomial share hap))
      = (mixtureLaw share (stateLaw y)).mass :=
    funext fun hap ↦ by
      rw [pooledMassPolynomial, map_sum, mixtureLaw_mass]
      exact Finset.sum_congr rfl fun d _ ↦ by rw [map_mul, eval_C, eval_X]; rfl
  rw [hsubstitution, hmass]

/-- **Pooling does not raise the degree**: the pooled frequencies have degree one. -/
theorem totalDegree_pooledPolynomial_le (share : FiniteReportLaw Deme)
    (p : MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    (pooledPolynomial share p).totalDegree ≤ p.totalDegree := by
  have hmass : ∀ hap : FullHaplotype Locus Allele,
      (pooledMassPolynomial share hap).totalDegree ≤ 1 :=
    fun hap ↦ (totalDegree_finset_sum _ _).trans (Finset.sup_le fun d _ ↦
      (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]))
  exact (EndToEndDiploidGWASTraining.totalDegree_bind₁_le _ p hmass).trans_eq (mul_one _)

variable {J : Type*} [Fintype J]

/-- **The pooled trained polynomial**: a source matrix read at the pooled frequencies against a
target matrix read in the target deme. -/
def pooledTrainedPolynomial (share : FiniteReportLaw Deme) (target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ i, ∑ j, demePolynomial target (targetMatrix i j) * pooledPolynomial share (sourceMatrix i j)

/-- At a state, the pooled trained polynomial reads the target matrix in the target deme against
the source matrix in the pooled law. -/
theorem polynomialFunction_pooledTrainedPolynomial (share : FiniteReportLaw Deme) (target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (pooledTrainedPolynomial share target sourceMatrix targetMatrix) y
      = ∑ i, ∑ j, eval (stateLaw y target).mass (targetMatrix i j)
          * eval (mixtureLaw share (stateLaw y)).mass (sourceMatrix i j) := by
  simp only [polynomialFunction_apply, pooledTrainedPolynomial, map_sum, map_mul,
    eval_demePolynomial, eval_pooledPolynomial]

/-- **The pooled trained polynomial has total degree at most the sum of the degrees** of its
target and source matrices. -/
theorem totalDegree_pooledTrainedPolynomial_le (share : FiniteReportLaw Deme) (target : Deme)
    (sourceMatrix targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ) {a b : ℕ}
    (hsource : ∀ i j, (sourceMatrix i j).totalDegree ≤ a)
    (htarget : ∀ i j, (targetMatrix i j).totalDegree ≤ b) :
    (pooledTrainedPolynomial share target sourceMatrix targetMatrix).totalDegree ≤ b + a := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  have htargetDeme : (demePolynomial target (targetMatrix i j)).totalDegree ≤ b :=
    (totalDegree_rename_le _ _).trans (htarget i j)
  have hsourcePooled : (pooledPolynomial share (sourceMatrix i j)).totalDegree ≤ a :=
    (totalDegree_pooledPolynomial_le share _).trans (hsource i j)
  exact (totalDegree_mul _ _).trans (add_le_add htargetDeme hsourcePooled)

/-- **The pooled covariance polynomial** `∑_j C_t(X_j, Y) C_π(X_j, Y)`: the target marginal
effects read against the pooled ones. -/
def pooledCovariancePolynomial (share : FiniteReportLaw Deme) (target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ marker, demePolynomial target
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)
    * pooledPolynomial share
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)

/-- **The pooled covariance polynomial has total degree at most four.** -/
theorem totalDegree_pooledCovariancePolynomial_le (share : FiniteReportLaw Deme) (target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    (pooledCovariancePolynomial share target genotype outcome).totalDegree ≤ 4 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun marker _ ↦ ?_)
  have htargetDeme : (demePolynomial target
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)).totalDegree
      ≤ 2 :=
    (totalDegree_rename_le _ _).trans (totalDegree_covariancePolynomial_le _ outcome)
  have hsourcePooled : (pooledPolynomial share
      (covariancePolynomial (fun individual ↦ genotype individual marker) outcome)).totalDegree
      ≤ 2 :=
    (totalDegree_pooledPolynomial_le share _).trans (totalDegree_covariancePolynomial_le _ outcome)
  exact (totalDegree_mul _ _).trans (by omega)

end Polynomials

/-! ## The pooled accumulators at a state -/

section Accumulators

variable {J : Type*} [Fintype J]

/-- **At a state, a cohort expectation of a quadratic form in the pooled GWAS weights** is a
sampling form of three pooled trained polynomials, for any matrix of target polynomials. -/
theorem expectation_quadraticForm_pooledStateLaw (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ)
    (targetMatrix : J → J → MvPolynomial (FullHaplotype Locus Allele) ℝ)
    (y : FrequencyState Deme Locus Allele) :
    (cohortLaw (mixtureLaw share (stateLaw y)) size).expectation (fun sample ↦ ∑ i, ∑ j,
        eval (stateLaw y target).mass (targetMatrix i j)
          * (gwasWeights genotype outcome sample i * gwasWeights genotype outcome sample j))
      = samplingForm
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightProductPolynomial genotype outcome) targetMatrix) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightExcessPolynomial genotype outcome) targetMatrix) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightPairingPolynomial genotype outcome) targetMatrix) y) size := by
  rw [expectation_quadraticForm_gwasWeights _ hsize genotype outcome
    fun i j ↦ eval (stateLaw y target).mass (targetMatrix i j)]
  simp only [polynomialFunction_pooledTrainedPolynomial, eval_weightProductPolynomial,
    eval_weightExcessPolynomial, eval_weightPairingPolynomial]

/-- **At a state, the expected target covariance of the pooled-trained score** is a polynomial
observable of total degree at most four. -/
theorem trainedCovariance_pooledStateLaw (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    trainedCovariance (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype outcome
      = polynomialFunction (pooledCovariancePolynomial share target genotype outcome) y := by
  rw [trainedCovariance_eq _ _ hsize, covariance_linearScore]
  simp only [polynomialFunction_apply, pooledCovariancePolynomial, map_sum, map_mul,
    eval_demePolynomial, eval_pooledPolynomial, eval_covariancePolynomial]
  exact Finset.sum_congr rfl fun marker _ ↦ mul_comm _ _

/-- **At a state, the expected target variance of the pooled-trained score** is a sampling form of
three polynomial observables of total degree at most six. -/
theorem trainedVariance_pooledStateLaw (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    trainedVariance (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightProductPolynomial genotype outcome) (tagCovariancePolynomial genotype)) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightExcessPolynomial genotype outcome) (tagCovariancePolynomial genotype)) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightPairingPolynomial genotype outcome) (tagCovariancePolynomial genotype)) y)
          size := by
  simp only [trainedVariance, variance_linearScore_eq, ← eval_tagCovariancePolynomial]
  exact expectation_quadraticForm_pooledStateLaw share target hsize genotype outcome
    (tagCovariancePolynomial genotype) y

/-- **At a state, the expected target correlation numerator of the pooled-trained score** is a
sampling form of three polynomial observables of total degree at most eight. -/
theorem trainedNumerator_pooledStateLaw (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    trainedNumerator (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightProductPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightExcessPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightPairingPolynomial genotype outcome)
            (numeratorMatrixPolynomial genotype outcome)) y) size := by
  simp only [trainedNumerator, correlationNumerator_linearScore, ← eval_numeratorMatrixPolynomial]
  exact expectation_quadraticForm_pooledStateLaw share target hsize genotype outcome
    (numeratorMatrixPolynomial genotype outcome) y

/-- **At a state, the expected target correlation denominator of the pooled-trained score** is a
sampling form of three polynomial observables of total degree at most eight. -/
theorem trainedDenominator_pooledStateLaw (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) (y : FrequencyState Deme Locus Allele) :
    trainedDenominator (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype outcome
      = samplingForm
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightProductPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightExcessPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y)
          (polynomialFunction (pooledTrainedPolynomial share target
            (weightPairingPolynomial genotype outcome)
            (denominatorMatrixPolynomial genotype outcome)) y) size := by
  simp only [trainedDenominator, correlationDenominator_linearScore,
    ← eval_denominatorMatrixPolynomial]
  exact expectation_quadraticForm_pooledStateLaw share target hsize genotype outcome
    (denominatorMatrixPolynomial genotype outcome) y

end Accumulators

/-! ## The pooled metrics under a kernel -/

section Expected

variable {J : Type*} [Fintype J]

/-- **The calibration slope of expectations of the pooled-trained score** under a kernel: the
expected target covariance over the expected target variance, the expectations taken over the
populations of the kernel and the cohort drawn from the pooled law of each.  NOTE2 §6.2 query: a
ratio of expectations. -/
def expectedPooledCalibrationSlope
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (share : FiniteReportLaw Deme) (target : Deme)
    (size : ℕ) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, trainedCovariance (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype
      outcome ∂(κ x0))
    / ∫ y, trainedVariance (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype
        outcome ∂(κ x0)

/-- **The accuracy of expectations of the pooled-trained score** under a kernel: the expected
target correlation numerator over the expected denominator.  NOTE2 §6.2 query: a ratio of
expectations. -/
def expectedPooledAccuracy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (share : FiniteReportLaw Deme) (target : Deme)
    (size : ℕ) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (∫ y, trainedNumerator (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype
      outcome ∂(κ x0))
    / ∫ y, trainedDenominator (mixtureLaw share (stateLaw y)) (stateLaw y target) size genotype
        outcome ∂(κ x0)

/-- **The rational pooled calibration slope** of a budget-`n` moment vector and a cohort size: a
coefficient vector over a sampling form of coefficient vectors. -/
def momentPooledCalibrationSlope (ℓ₀ : Locus) (n : ℕ) (share : FiniteReportLaw Deme)
    (target : Deme) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) (size : ℕ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledCovariancePolynomial share target genotype outcome)
      ⬝ᵥ v)
    / samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightProductPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightExcessPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightPairingPolynomial genotype outcome) (tagCovariancePolynomial genotype)) ⬝ᵥ v) size

/-- **The rational pooled accuracy** of a budget-`n` moment vector and a cohort size: a ratio of
two sampling forms of coefficient vectors. -/
def momentPooledAccuracy (ℓ₀ : Locus) (n : ℕ) (share : FiniteReportLaw Deme) (target : Deme)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ)
    (size : ℕ) (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ n) → ℝ) : ℝ :=
  samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightProductPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightExcessPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightPairingPolynomial genotype outcome) (numeratorMatrixPolynomial genotype outcome))
        ⬝ᵥ v) size
    / samplingForm
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightProductPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightExcessPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v)
      (budgetCoefficients ℓ₀ (fun _ ↦ n) (pooledTrainedPolynomial share target
        (weightPairingPolynomial genotype outcome) (denominatorMatrixPolynomial genotype outcome))
        ⬝ᵥ v) size

/-- **Pooling at a unit share is training in that deme**: the pooled accuracy of expectations of a
point mass on a deme is the trained accuracy of `EndToEndGWASTrainingHistory`. -/
theorem expectedPooledAccuracy_pointMass
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (source target : Deme) (size : ℕ)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledAccuracy κ x0 (FiniteReportLaw.pointMass source) target size genotype outcome
      = expectedTrainedAccuracy κ x0 source target size genotype outcome := by
  simp only [expectedPooledAccuracy, expectedTrainedAccuracy, mixtureLaw_pointMass]

end Expected

section MomentKernel

variable {J : Type*} [Fintype J] (ℓ₀ : Locus) {n : ℕ}
  (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
  [IsMarkovKernel κ]
  (M : Matrix (BudgetConfiguration Deme Locus Allele (fun _ ↦ n))
    (BudgetConfiguration Deme Locus Allele (fun _ ↦ n)) ℝ)
  (hmoment : ∀ (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ n)),
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
      = (M *ᵥ budgetMomentFeature (fun _ ↦ n) x) ξ)

include ℓ₀ hmoment

/-- **The pooled slope under a kernel with budget-`n` moments**, `n ≥ 6`, is the rational pooled
slope of the propagated moments. -/
theorem expectedPooledCalibrationSlope_eq_momentPooledCalibrationSlope (hn : 6 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledCalibrationSlope κ x0 share target size genotype outcome
      = momentPooledCalibrationSlope ℓ₀ n share target genotype outcome size
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  have hcovariance := EndToEndCalibrationLaw.integral_eq_dotProduct_of_totalDegree_le ℓ₀ κ M
    hmoment _ ((totalDegree_pooledCovariancePolynomial_le share target genotype outcome).trans
      (by omega)) _
    (fun y ↦ (trainedCovariance_pooledStateLaw share target hsize genotype outcome y).symm) x0
  rw [expectedPooledCalibrationSlope, hcovariance]
  simp only [trainedVariance_pooledStateLaw share target hsize genotype outcome]
  rw [integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
    ((totalDegree_pooledTrainedPolynomial_le share target _ _
      (totalDegree_weightProductPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn)
    ((totalDegree_pooledTrainedPolynomial_le share target _ _
      (totalDegree_weightExcessPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn)
    ((totalDegree_pooledTrainedPolynomial_le share target _ _
      (totalDegree_weightPairingPolynomial_le genotype outcome)
      (totalDegree_tagCovariancePolynomial_le genotype)).trans hn)]
  rfl

/-- **The pooled accuracy under a kernel with budget-`n` moments**, `n ≥ 8`, is the rational
pooled accuracy of the propagated moments. -/
theorem expectedPooledAccuracy_eq_momentPooledAccuracy (hn : 8 ≤ n)
    (x0 : FrequencyState Deme Locus Allele) (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledAccuracy κ x0 share target size genotype outcome
      = momentPooledAccuracy ℓ₀ n share target genotype outcome size
          (M *ᵥ budgetMomentFeature (fun _ ↦ n) x0) := by
  simp only [expectedPooledAccuracy,
    trainedNumerator_pooledStateLaw share target hsize genotype outcome,
    trainedDenominator_pooledStateLaw share target hsize genotype outcome]
  rw [integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
      ((totalDegree_pooledTrainedPolynomial_le share target _ _
        (totalDegree_weightProductPolynomial_le genotype outcome)
        (totalDegree_numeratorMatrixPolynomial_le genotype outcome)).trans hn)
      ((totalDegree_pooledTrainedPolynomial_le share target _ _
        (totalDegree_weightExcessPolynomial_le genotype outcome)
        (totalDegree_numeratorMatrixPolynomial_le genotype outcome)).trans hn)
      ((totalDegree_pooledTrainedPolynomial_le share target _ _
        (totalDegree_weightPairingPolynomial_le genotype outcome)
        (totalDegree_numeratorMatrixPolynomial_le genotype outcome)).trans hn),
    integral_samplingForm_polynomialFunction ℓ₀ κ M hmoment x0 size _ _ _
      ((totalDegree_pooledTrainedPolynomial_le share target _ _
        (totalDegree_weightProductPolynomial_le genotype outcome)
        (totalDegree_denominatorMatrixPolynomial_le genotype outcome)).trans hn)
      ((totalDegree_pooledTrainedPolynomial_le share target _ _
        (totalDegree_weightExcessPolynomial_le genotype outcome)
        (totalDegree_denominatorMatrixPolynomial_le genotype outcome)).trans hn)
      ((totalDegree_pooledTrainedPolynomial_le share target _ _
        (totalDegree_weightPairingPolynomial_le genotype outcome)
        (totalDegree_denominatorMatrixPolynomial_le genotype outcome)).trans hn)]
  rfl

end MomentKernel

/-! ## The pooled law along histories -/

section Histories

variable {J : Type*} [Fintype J]

/-- **The pooled calibration slope along a history of epochs, splits and pulses.**  The slope of
expectations of a score trained by a GWAS on `n` haplotypes drawn from the pooled law of the
demes, with shares `π`, and deployed in the target deme, is the rational function
`momentPooledCalibrationSlope` of the chronological propagator applied to the budget-6 moments of
the initial state, and of `n`. -/
theorem expectedPooledCalibrationSlope_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledCalibrationSlope (historyEventKernel ℓ₀ hap₀ events) x0 share target size
        genotype outcome
      = momentPooledCalibrationSlope ℓ₀ 6 share target genotype outcome size
          (historyEventPropagator (fun _ ↦ 6) events *ᵥ budgetMomentFeature (fun _ ↦ 6) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedPooledCalibrationSlope_eq_momentPooledCalibrationSlope ℓ₀
    (historyEventKernel ℓ₀ hap₀ events) (historyEventPropagator (fun _ ↦ 6) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 6) events) le_rfl x0 share
    target hsize genotype outcome

/-- **The end-to-end multi-ancestry GWAS law along a history of epochs, splits and pulses.**  The
accuracy of expectations of a score trained by a GWAS on `n` haplotypes drawn from the pooled law
of the demes, with shares `π`, and deployed in the target deme, is the rational function
`momentPooledAccuracy` of the chronological propagator applied to the budget-8 moments of the
initial state, and of `n`. -/
theorem expectedPooledAccuracy_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (share : FiniteReportLaw Deme) (target : Deme)
    {size : ℕ} (hsize : 2 ≤ size) (genotype : FullHaplotype Locus Allele → J → ℝ)
    (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledAccuracy (historyEventKernel ℓ₀ hap₀ events) x0 share target size genotype
        outcome
      = momentPooledAccuracy ℓ₀ 8 share target genotype outcome size
          (historyEventPropagator (fun _ ↦ 8) events *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact expectedPooledAccuracy_eq_momentPooledAccuracy ℓ₀ (historyEventKernel ℓ₀ hap₀ events)
    (historyEventPropagator (fun _ ↦ 8) events)
    (integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ (fun _ ↦ 8) events) le_rfl x0 share
    target hsize genotype outcome

/-- **The pooled slope sees the history only through finitely many moments.**  Two histories, from
two initial states, whose propagated budget-6 moments agree give equal pooled calibration slope of
expectations for every share, target, cohort size, tag set and outcome. -/
theorem expectedPooledCalibrationSlope_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 6) first *ᵥ budgetMomentFeature (fun _ ↦ 6) x₁
      = historyEventPropagator (fun _ ↦ 6) second *ᵥ budgetMomentFeature (fun _ ↦ 6) x₂)
    (share : FiniteReportLaw Deme) (target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledCalibrationSlope (historyEventKernel ℓ₀ hap₀ first) x₁ share target size
        genotype outcome
      = expectedPooledCalibrationSlope (historyEventKernel ℓ₀ hap₀ second) x₂ share target size
          genotype outcome := by
  rw [expectedPooledCalibrationSlope_historyEventKernel ℓ₀ hap₀ first x₁ share target hsize,
    expectedPooledCalibrationSlope_historyEventKernel ℓ₀ hap₀ second x₂ share target hsize,
    hmoments]

/-- **The pooled accuracy sees the history only through finitely many moments**: the propagated
budget-8 moments. -/
theorem expectedPooledAccuracy_eq_of_moments_eq (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 8) first *ᵥ budgetMomentFeature (fun _ ↦ 8) x₁
      = historyEventPropagator (fun _ ↦ 8) second *ᵥ budgetMomentFeature (fun _ ↦ 8) x₂)
    (share : FiniteReportLaw Deme) (target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledAccuracy (historyEventKernel ℓ₀ hap₀ first) x₁ share target size genotype
        outcome
      = expectedPooledAccuracy (historyEventKernel ℓ₀ hap₀ second) x₂ share target size genotype
          outcome := by
  rw [expectedPooledAccuracy_historyEventKernel ℓ₀ hap₀ first x₁ share target hsize,
    expectedPooledAccuracy_historyEventKernel ℓ₀ hap₀ second x₂ share target hsize, hmoments]

/-- **The pooled calibration slope along a rate history** is the rational function
`momentPooledCalibrationSlope` of the propagator of the rate history applied to the budget-6
moments of the initial state, and of the cohort size. -/
theorem expectedPooledCalibrationSlope_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (share : FiniteReportLaw Deme) (target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledCalibrationSlope (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 share
        target size genotype outcome
      = momentPooledCalibrationSlope ℓ₀ 6 share target genotype outcome size
          (rateHistoryDualPropagator rates (fun _ ↦ 6) T
            *ᵥ budgetMomentFeature (fun _ ↦ 6) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedPooledCalibrationSlope_eq_momentPooledCalibrationSlope ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 6) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 6)) le_rfl x0
    share target hsize genotype outcome

/-- **The pooled accuracy along a rate history** is the rational function `momentPooledAccuracy`
of the propagator of the rate history applied to the budget-8 moments of the initial state, and
of the cohort size. -/
theorem expectedPooledAccuracy_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (share : FiniteReportLaw Deme) (target : Deme) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : FullHaplotype Locus Allele → J → ℝ) (outcome : FullHaplotype Locus Allele → ℝ) :
    expectedPooledAccuracy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 share target size
        genotype outcome
      = momentPooledAccuracy ℓ₀ 8 share target genotype outcome size
          (rateHistoryDualPropagator rates (fun _ ↦ 8) T
            *ᵥ budgetMomentFeature (fun _ ↦ 8) x0) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact expectedPooledAccuracy_eq_momentPooledAccuracy ℓ₀
    (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) (rateHistoryDualPropagator rates (fun _ ↦ 8) T)
    (integral_momentPolynomial_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ (fun _ ↦ 8)) le_rfl x0
    share target hsize genotype outcome

end Histories

end

end Descent.Portability.EndToEndMultiAncestryGWAS
