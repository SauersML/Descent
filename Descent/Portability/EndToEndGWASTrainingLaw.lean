/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FourCellCohortLaw
import Descent.Portability.PortabilityMasterTheorem
import Descent.Portability.ReplicaMetricInstances
import Descent.Portability.ScoreMomentLaw

assert_below Descent.Decision Descent.Program

/-!
# The exact accuracy of a score trained by a finite-sample GWAS

`PortabilityMasterTheorem` §7 and `EndToEndDeploymentLaw` train on population moments, and
`TrainingNoiseAccuracy` bounds a label-dependent learner.  This module gives the exact expected
deployed accuracy of a score whose weights are estimated from a finite training cohort.

The training procedure.  A cohort of `n` individuals is drawn independently from the source law
(`FourCellCohortLaw.cohortLaw`).  The marginal-effect GWAS estimates the weight of each tag `X_j`
as the unbiased sample covariance of the tag with the outcome, divisor `n − 1`
(`sampleCovariance`, `gwasWeights`).  This is the weight vector of clumping and thresholding with a
fixed tag set.  The plug-in estimator, divisor `n`, is the same vector times `(n − 1) / n`
(`plugInCovariance_eq`), and it gives the same accuracy (`plugInAccuracy_eq_trainedAccuracy`).

Exact finite-`n` moments.  For `n ≥ 2`:
* `E ĉ(f, g) = C_fg` (`expectation_sampleCovariance`), so `E ŵ_j = w_j = C(X_j, Y)`
  (`expectation_gwasWeights`);
* `E[ĉ(f, g) ĉ(h, k)] = C_fg C_hk + (K − C_fg C_hk) / n + (C_fh C_gk + C_fk C_gh) / (n (n − 1))`,
  with `K` the fourth central co-moment (`expectation_sampleCovariance_mul`).  So
  `E[ŵ_i ŵ_j] = w_i w_j + E_ij / n + P_ij / (n (n − 1))`, with the excess matrix
  `E_ij = K(X_i, Y, X_j, Y) − w_i w_j` and the pairing matrix `P_ij = C(X_i, X_j) V_Y + w_i w_j`
  (`expectation_gwasWeights_mul`).
The proof splits the sample covariance into a diagonal and an off-diagonal cohort sum
(`sampleCovariance_eq_diagonal_sub_offDiagonal`) and reads products of observables on the cohort
through independence (`expectation_prod_reading`).  The fourth co-moment is read off a cohort of
two: twice the expected product of two pair kernels, minus the three pairings
(`fourthCoMoment_eq_pairExpectation`).

Deployment.  The trained score `S_ŵ = ∑ ŵ_j X_j` is deployed in a target law.  The query is the
ratio of expectations of NOTE2 §6.2: the expected target correlation numerator `16 C_t(S_ŵ, Y)²`
over the expected denominator `16 V_t(S_ŵ) V_t(Y)` (`trainedNumerator`, `trainedDenominator`,
`trainedAccuracy`).  Both are sampling forms `a + b / n + c / (n (n − 1))` (`samplingForm`).  In
each, `a` is the accumulator of the population marginal score `S_w`, and `b` and `c` are the
excess and pairing matrices read against the target matrices `16 c_i c_j` and
`16 C_t(X_i, X_j) V_t(Y)` (`trainedNumerator_eq`, `trainedDenominator_eq`,
`expectation_quadraticForm_gwasWeights`).

Consequences.
* The excess quadratic form is a variance and the pairing form a sum of squares
  (`quadraticForm_weightExcess`, `quadraticForm_weightPairing`), so every coefficient is
  nonnegative.  Both accumulators decrease in `n` to their population values
  (`trainedNumerator_antitone`, `trainedDenominator_antitone`, `le_trainedNumerator`,
  `le_trainedDenominator`, `tendsto_trainedNumerator`, `tendsto_trainedDenominator`).
* The trained accuracy tends to the accuracy of the population marginal score
  (`tendsto_trainedAccuracy`).  It is not a factor times that accuracy.  It is the mediant
  `(a + ν_n) / (α + τ_n)` of the population accumulators and the noise terms, and it is at most the
  population value exactly when `ν_n α ≤ τ_n a` (`samplingForm_div_le_iff`).
* With a single tag the trained accuracy equals the population accuracy for every `n`
  (`trainedAccuracy_unique`): finite-sample deflation is an error of direction, not of scale.
* The accuracy is not monotone in `n`, and finite training can exceed the population value.  When
  the population marginal score is uncorrelated with the outcome in the target, the population
  accuracy is zero and every finite cohort gives positive accuracy
  (`populationAccuracy_lt_trainedAccuracy`).  A two-locus law with an interaction outcome satisfies
  the hypotheses (`trainingWitness_accuracy`), so there the accuracy decreases to zero as `n` grows.

Scope.  One draw from a finite law per individual, haploid when the law is a deme's haplotype law,
and the outcome is a function of the individual.  The estimator is the marginal sample covariance,
with no LD adjustment and no threshold selected on the training cohort.  The query is the ratio of
expectations over the training cohort; the expectation of each cohort's accuracy is not a rational
function of finitely many moments and is not stated.  The composition with a demographic history
is `EndToEndGWASTrainingHistory`.

## Empirical status

None.  The bodies here are identities between finite sums over a stipulated finite law and its
independent product, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndGWASTrainingLaw

open Filter Topology TrainingNoiseAccuracy ReplicaMetricInstances FourCellCohortLaw

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-! ## Reading observables on an independent cohort -/

/-- The corpus cohort law is the corpus independent product of its members' laws. -/
theorem cohortLaw_eq_independentLaw (law : FiniteReportLaw Ω) (size : ℕ) :
    cohortLaw law size = HWEInteractionLaw.independentLaw fun _ : Fin size ↦ law :=
  piLaw_eq_independentLaw _

/-- **Expectation is linear** in the observable. -/
theorem expectation_linear (law : FiniteReportLaw Ω) (a b : ℝ) (first second : Ω → ℝ) :
    law.expectation (fun individual ↦ a * first individual + b * second individual)
      = a * law.expectation first + b * law.expectation second := by
  simp only [FiniteReportLaw.expectation, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun individual _ ↦ by ring

/-- **Expectation is linear**, in the four-term form the second-moment computation uses. -/
theorem expectation_linear_four (law : FiniteReportLaw Ω) (a b c d : ℝ)
    (first second third fourth : Ω → ℝ) :
    law.expectation (fun individual ↦ a * first individual + b * second individual
        + c * third individual + d * fourth individual)
      = a * law.expectation first + b * law.expectation second + c * law.expectation third
        + d * law.expectation fourth := by
  simp only [FiniteReportLaw.expectation, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun individual _ ↦ by ring

/-- A constant factor comes out of the expectation. -/
theorem expectation_const_mul_observable (law : FiniteReportLaw Ω) (c : ℝ) (value : Ω → ℝ) :
    law.expectation (fun individual ↦ c * value individual) = c * law.expectation value := by
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun individual _ ↦ by ring

/-- An observable centered at its own expectation has expectation zero. -/
theorem expectation_sub_expectation (law : FiniteReportLaw Ω) (value : Ω → ℝ) :
    law.expectation (fun individual ↦ value individual - law.expectation value) = 0 := by
  simp only [FiniteReportLaw.expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    law.mass_sum, one_mul, sub_self]

/-- **Independent members factor every product reading.**  A product of observables, each read
on one member of a cohort, has expectation the product over members of the expectation of the
product of the observables read on that member. -/
theorem expectation_prod_reading (law : FiniteReportLaw Ω) {size : ℕ} {Reading : Type*}
    [Fintype Reading] (member : Reading → Fin size) (observable : Reading → Ω → ℝ) :
    (cohortLaw law size).expectation (fun sample ↦ ∏ r, observable r (sample (member r)))
      = ∏ t, law.expectation fun individual ↦
          ∏ r ∈ Finset.univ.filter (fun r ↦ member r = t), observable r individual := by
  have hfiber : ∀ sample : Fin size → Ω, ∏ r, observable r (sample (member r))
      = ∏ t, ∏ r ∈ Finset.univ.filter (fun r ↦ member r = t), observable r (sample t) := by
    intro sample
    rw [← Finset.prod_fiberwise Finset.univ member fun r ↦ observable r (sample (member r))]
    refine Finset.prod_congr rfl fun t _ ↦ Finset.prod_congr rfl fun r hr ↦ ?_
    simp only [(Finset.mem_filter.mp hr).2]
  simp only [hfiber]
  rw [cohortLaw_eq_independentLaw]
  exact HWEInteractionLaw.expectation_independent_product (fun _ ↦ law)
    fun t individual ↦ ∏ r ∈ Finset.univ.filter (fun r ↦ member r = t), observable r individual

/-- **An isolated centered reading averages a product to zero.**  If one reading is on a member
that no other reading uses, and its observable is centered, the product has expectation zero. -/
theorem expectation_prod_reading_eq_zero (law : FiniteReportLaw Ω) {size : ℕ}
    {Reading : Type*} [Fintype Reading] (member : Reading → Fin size)
    (observable : Reading → Ω → ℝ) (isolated : Reading)
    (hisolated : ∀ r, member r = member isolated → r = isolated)
    (hcentered : law.expectation (observable isolated) = 0) :
    (cohortLaw law size).expectation (fun sample ↦ ∏ r, observable r (sample (member r)))
      = 0 := by
  rw [expectation_prod_reading]
  refine Finset.prod_eq_zero (Finset.mem_univ (member isolated)) ?_
  have hfilter : Finset.univ.filter (fun r ↦ member r = member isolated) = {isolated} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hisolated r, fun hr ↦ congrArg member hr⟩
  simpa only [hfilter, Finset.prod_singleton] using hcentered

/-- Four readings, the last on a member none of the others reads, average to zero when the last
observable is centered. -/
theorem expectation_four_eq_zero (law : FiniteReportLaw Ω) {size : ℕ}
    (first second third last : Ω → ℝ) {i j k l : Fin size} (hi : i ≠ l) (hj : j ≠ l)
    (hk : k ≠ l) (hlast : law.expectation last = 0) :
    (cohortLaw law size).expectation (fun sample ↦
      first (sample i) * second (sample j) * third (sample k) * last (sample l)) = 0 := by
  have h := expectation_prod_reading_eq_zero law ![i, j, k, l] ![first, second, third, last] 3
    (fun r hr ↦ by fin_cases r <;> simp_all) hlast
  simp only [Fin.prod_univ_four] at h
  exact h

/-- Observables read on two distinct members of a cohort are independent. -/
theorem expectation_mul_of_ne (law : FiniteReportLaw Ω) {size : ℕ} (first second : Ω → ℝ)
    {i j : Fin size} (hij : i ≠ j) :
    (cohortLaw law size).expectation (fun sample ↦ first (sample i) * second (sample j))
      = law.expectation first * law.expectation second := by
  have hsplit : (fun sample : Fin size → Ω ↦ first (sample i) * second (sample j))
      = fun sample ↦ 1 * ((first (sample i) - law.expectation first) * second (sample j))
        + law.expectation first * second (sample j) := funext fun sample ↦ by ring
  have hcentered : (cohortLaw law size).expectation
      (fun sample ↦ (first (sample i) - law.expectation first) * second (sample j)) = 0 := by
    rw [cohortLaw_eq_independentLaw]
    exact FiniteIndependentMoments.cross_expectation_zero (fun _ ↦ law) i j hij
      (fun individual ↦ first individual - law.expectation first) second
      (expectation_sub_expectation law first)
  have hmean : (cohortLaw law size).expectation (fun sample ↦ second (sample j))
      = law.expectation second := by
    rw [cohortLaw_eq_independentLaw]
    exact FiniteIndependentMoments.coordinate_expectation (fun _ ↦ law) j second
  rw [hsplit, expectation_linear, hcentered, hmean]
  ring

/-! ## The sample covariance of a cohort -/

/-- The sample mean of an observable over a cohort sample. -/
def sampleMean {size : ℕ} (value : Ω → ℝ) (sample : Fin size → Ω) : ℝ :=
  (∑ member, value (sample member)) / size

/-- **The unbiased sample covariance** of two observables over a cohort sample: the sum of the
products of deviations from the sample means, divided by `n − 1`. -/
def sampleCovariance {size : ℕ} (first second : Ω → ℝ) (sample : Fin size → Ω) : ℝ :=
  (∑ member, (first (sample member) - sampleMean first sample)
      * (second (sample member) - sampleMean second sample)) / ((size : ℝ) - 1)

/-- The plug-in sample covariance of a cohort sample, divided by `n`. -/
def plugInCovariance {size : ℕ} (first second : Ω → ℝ) (sample : Fin size → Ω) : ℝ :=
  (∑ member, (first (sample member) - sampleMean first sample)
      * (second (sample member) - sampleMean second sample)) / size

/-- The plug-in sample covariance is the unbiased one times `(n − 1) / n`. -/
theorem plugInCovariance_eq {size : ℕ} (hsize : 2 ≤ size) (first second : Ω → ℝ)
    (sample : Fin size → Ω) :
    plugInCovariance first second sample
      = ((size : ℝ) - 1) / size * sampleCovariance first second sample := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hN1 : (size : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  unfold plugInCovariance sampleCovariance
  rw [eq_comm, div_mul_div_comm, mul_comm (size : ℝ), mul_div_mul_left _ _ hN1]

/-- The sum of products of deviations from the sample means, written with any centering
constants: the sum of products minus the product of sums over `n`. -/
theorem sum_deviation_mul_deviation {size : ℕ} (hsize : (size : ℝ) ≠ 0) (first second : Ω → ℝ)
    (a b : ℝ) (sample : Fin size → Ω) :
    ∑ member, (first (sample member) - sampleMean first sample)
        * (second (sample member) - sampleMean second sample)
      = ∑ member, (first (sample member) - a) * (second (sample member) - b)
        - (∑ member, (first (sample member) - a)) * (∑ member, (second (sample member) - b))
          / size := by
  simp only [sampleMean, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The product of two cohort sums is the diagonal sum plus the off-diagonal sum. -/
theorem sum_mul_sum_eq_diagonal_add_offDiagonal {size : ℕ} (first second : Fin size → ℝ) :
    (∑ n, first n) * (∑ m, second m)
      = ∑ n, first n * second n + ∑ n, ∑ m, if n = m then 0 else first n * second m := by
  rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hsplit : ∀ m, first n * second m
      = (if n = m then first n * second m else 0) + if n = m then 0 else first n * second m := by
    intro m
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun m _ ↦ hsplit m, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ n)]

/-- **The sample covariance splits into a diagonal and an off-diagonal cohort sum.**  On a cohort
of size `n ≥ 2`, for any centering constants `a` and `b`,
`ĉ(f, g) = n⁻¹ ∑ₙ (fₙ − a)(gₙ − b) − (n (n − 1))⁻¹ ∑_{n ≠ m} (fₙ − a)(g_m − b)`. -/
theorem sampleCovariance_eq_diagonal_sub_offDiagonal {size : ℕ} (hsize : 2 ≤ size)
    (first second : Ω → ℝ) (a b : ℝ) (sample : Fin size → Ω) :
    sampleCovariance first second sample
      = (size : ℝ)⁻¹ * ∑ n, (first (sample n) - a) * (second (sample n) - b)
        + -((size : ℝ) * ((size : ℝ) - 1))⁻¹
          * ∑ n, ∑ m, if n = m then 0 else (first (sample n) - a) * (second (sample m) - b) := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hN0 : (size : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN1 : (size : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [sampleCovariance, sum_deviation_mul_deviation hN0 first second a b sample,
    sum_mul_sum_eq_diagonal_add_offDiagonal]
  field_simp
  ring

/-! ## Expectations of cohort sums -/

/-- The expected diagonal sum of a cohort is the cohort size times the expectation. -/
theorem expectation_diagonal (law : FiniteReportLaw Ω) (size : ℕ) (value : Ω → ℝ) :
    (cohortLaw law size).expectation (fun sample ↦ ∑ n, value (sample n))
      = size * law.expectation value := by
  have hterm : ∀ n : Fin size, (cohortLaw law size).expectation (fun sample ↦ value (sample n))
      = law.expectation value := by
    intro n
    rw [cohortLaw_eq_independentLaw]
    exact FiniteIndependentMoments.coordinate_expectation (fun _ ↦ law) n value
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The expected off-diagonal sum of a cohort vanishes when the first observable is centered. -/
theorem expectation_offDiagonal (law : FiniteReportLaw Ω) (size : ℕ) (first second : Ω → ℝ)
    (hfirst : law.expectation first = 0) :
    (cohortLaw law size).expectation
        (fun sample ↦ ∑ n, ∑ m, if n = m then 0 else first (sample n) * second (sample m))
      = 0 := by
  rw [FiniteIndependentMoments.expectation_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [FiniteIndependentMoments.expectation_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  by_cases hnm : n = m
  · simp only [if_pos hnm]
    exact FiniteIndependentMoments.expectation_const _ 0
  · simp only [if_neg hnm]
    rw [cohortLaw_eq_independentLaw]
    exact FiniteIndependentMoments.cross_expectation_zero (fun _ ↦ law) n m hnm first second
      hfirst

/-- The expected product of two diagonal cohort sums is `n E[u v] + n (n − 1) E u E v`. -/
theorem expectation_diagonal_mul_diagonal (law : FiniteReportLaw Ω) (size : ℕ)
    (first second : Ω → ℝ) :
    (cohortLaw law size).expectation
        (fun sample ↦ (∑ n, first (sample n)) * ∑ k, second (sample k))
      = size * law.expectation (fun individual ↦ first individual * second individual)
        + size * (size - 1) * (law.expectation first * law.expectation second) := by
  have hterm : ∀ n k : Fin size, (cohortLaw law size).expectation
      (fun sample ↦ first (sample n) * second (sample k))
      = law.expectation first * law.expectation second
        + if n = k then law.expectation (fun individual ↦ first individual * second individual)
          - law.expectation first * law.expectation second else 0 := by
    intro n k
    by_cases hnk : n = k
    · subst hnk
      have hcoordinate : (cohortLaw law size).expectation
          (fun sample ↦ first (sample n) * second (sample n))
          = law.expectation (fun individual ↦ first individual * second individual) := by
        rw [cohortLaw_eq_independentLaw]
        exact FiniteIndependentMoments.coordinate_expectation (fun _ ↦ law) n
          fun individual ↦ first individual * second individual
      rw [if_pos rfl, hcoordinate]
      ring
    · rw [if_neg hnk, add_zero]
      exact expectation_mul_of_ne law first second hnk
  simp only [Finset.sum_mul_sum]
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, hterm, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring

/-- The expected product of a diagonal and an off-diagonal cohort sum vanishes when the
off-diagonal observables are centered. -/
theorem expectation_diagonal_mul_offDiagonal (law : FiniteReportLaw Ω) (size : ℕ)
    (first second third fourth : Ω → ℝ) (hthird : law.expectation third = 0)
    (hfourth : law.expectation fourth = 0) :
    (cohortLaw law size).expectation (fun sample ↦ (∑ n, first (sample n) * second (sample n))
        * ∑ k, ∑ l, if k = l then 0 else third (sample k) * fourth (sample l)) = 0 := by
  have hterm : ∀ n k l : Fin size, (cohortLaw law size).expectation (fun sample ↦
      if k = l then 0
      else first (sample n) * second (sample n) * third (sample k) * fourth (sample l)) = 0 := by
    intro n k l
    by_cases hkl : k = l
    · simp only [if_pos hkl]
      exact FiniteIndependentMoments.expectation_const _ 0
    simp only [if_neg hkl]
    by_cases hkn : k = n
    · subst hkn
      exact expectation_four_eq_zero law first second third fourth hkl hkl hkl hfourth
    · have h := expectation_four_eq_zero law first second fourth third (Ne.symm hkn)
        (Ne.symm hkn) (Ne.symm hkl) hthird
      simpa only [mul_comm, mul_assoc, mul_left_comm] using h
  have hexpand : ∀ sample : Fin size → Ω, (∑ n, first (sample n) * second (sample n))
      * (∑ k, ∑ l, if k = l then 0 else third (sample k) * fourth (sample l))
      = ∑ n, ∑ k, ∑ l, if k = l then 0
          else first (sample n) * second (sample n) * third (sample k) * fourth (sample l) := by
    intro sample
    simp only [Finset.sum_mul, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]
  simp only [hexpand]
  rw [FiniteIndependentMoments.expectation_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [FiniteIndependentMoments.expectation_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [FiniteIndependentMoments.expectation_sum]
  exact Finset.sum_eq_zero fun l _ ↦ hterm n k l

/-- The expected product of an off-diagonal and a diagonal cohort sum vanishes when the
off-diagonal observables are centered. -/
theorem expectation_offDiagonal_mul_diagonal (law : FiniteReportLaw Ω) (size : ℕ)
    (first second third fourth : Ω → ℝ) (hfirst : law.expectation first = 0)
    (hsecond : law.expectation second = 0) :
    (cohortLaw law size).expectation (fun sample ↦
        (∑ n, ∑ m, if n = m then 0 else first (sample n) * second (sample m))
          * ∑ k, third (sample k) * fourth (sample k)) = 0 := by
  have h := expectation_diagonal_mul_offDiagonal law size third fourth first second hfirst hsecond
  simpa only [mul_comm] using h

/-- The number of ordered pairs of distinct members of a cohort, times a constant. -/
theorem sum_offDiagonal_const (size : ℕ) (c : ℝ) :
    ∑ n : Fin size, ∑ m : Fin size, (if n = m then 0 else c) = size * (size - 1) * c := by
  have hrow : ∀ n : Fin size, ∑ m : Fin size, (if n = m then 0 else c) = (size - 1) * c := by
    intro n
    have hsplit : ∀ m : Fin size, (if n = m then 0 else c) = c - if n = m then c else 0 := by
      intro m
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun m _ ↦ hsplit m, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ n), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun n _ ↦ hrow n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The expected product of two off-diagonal cohort sums, the second with centered observables,
is `n (n − 1)` times the two pairings `E[u h] E[v k] + E[u k] E[v h]`. -/
theorem expectation_offDiagonal_mul_offDiagonal (law : FiniteReportLaw Ω) (size : ℕ)
    (first second third fourth : Ω → ℝ) (hthird : law.expectation third = 0)
    (hfourth : law.expectation fourth = 0) :
    (cohortLaw law size).expectation (fun sample ↦
        (∑ n, ∑ m, if n = m then 0 else first (sample n) * second (sample m))
          * ∑ k, ∑ l, if k = l then 0 else third (sample k) * fourth (sample l))
      = size * (size - 1)
        * (law.expectation (fun individual ↦ first individual * third individual)
            * law.expectation (fun individual ↦ second individual * fourth individual)
          + law.expectation (fun individual ↦ first individual * fourth individual)
            * law.expectation (fun individual ↦ second individual * third individual)) := by
  have hzero : ∀ n m k l : Fin size, k = l → (cohortLaw law size).expectation (fun sample ↦
      if k = l then 0
      else first (sample n) * second (sample m) * third (sample k) * fourth (sample l)) = 0 := by
    intro n m k l hkl
    simp only [if_pos hkl]
    exact FiniteIndependentMoments.expectation_const _ 0
  have hisolated : ∀ n m k l : Fin size, k ≠ n → k ≠ m → (cohortLaw law size).expectation
      (fun sample ↦ if k = l then 0
        else first (sample n) * second (sample m) * third (sample k) * fourth (sample l)) = 0 := by
    intro n m k l hkn hkm
    by_cases hkl : k = l
    · exact hzero n m k l hkl
    · simp only [if_neg hkl]
      have h := expectation_four_eq_zero law first second fourth third (Ne.symm hkn)
        (Ne.symm hkm) (Ne.symm hkl) hthird
      simpa only [mul_comm, mul_assoc, mul_left_comm] using h
  have hfree : ∀ n m k l : Fin size, l ≠ n → l ≠ m → (cohortLaw law size).expectation
      (fun sample ↦ if k = l then 0
        else first (sample n) * second (sample m) * third (sample k) * fourth (sample l)) = 0 := by
    intro n m k l hln hlm
    by_cases hkl : k = l
    · exact hzero n m k l hkl
    · simp only [if_neg hkl]
      exact expectation_four_eq_zero law first second third fourth (Ne.symm hln) (Ne.symm hlm)
        hkl hfourth
  have hrow : ∀ n m : Fin size, n ≠ m →
      ∑ k, ∑ l, (cohortLaw law size).expectation (fun sample ↦ if k = l then 0
        else first (sample n) * second (sample m) * third (sample k) * fourth (sample l))
      = law.expectation (fun individual ↦ first individual * third individual)
          * law.expectation (fun individual ↦ second individual * fourth individual)
        + law.expectation (fun individual ↦ first individual * fourth individual)
          * law.expectation (fun individual ↦ second individual * third individual) := by
    intro n m hnm
    rw [Finset.sum_eq_add_of_mem n m (Finset.mem_univ n) (Finset.mem_univ m) hnm
      fun k _ hk ↦ Finset.sum_eq_zero fun l _ ↦ hisolated n m k l hk.1 hk.2]
    rw [Finset.sum_eq_single m
        (fun l _ hlm ↦ by
          by_cases hln : l = n
          · exact hzero n m n l hln.symm
          · exact hfree n m n l hln hlm)
        (fun h ↦ absurd (Finset.mem_univ m) h),
      Finset.sum_eq_single n
        (fun l _ hln ↦ by
          by_cases hlm : l = m
          · exact hzero n m m l hlm.symm
          · exact hfree n m m l hln hlm)
        (fun h ↦ absurd (Finset.mem_univ n) h)]
    simp only [if_neg hnm, if_neg (Ne.symm hnm)]
    have hA : (fun sample : Fin size → Ω ↦
        first (sample n) * second (sample m) * third (sample n) * fourth (sample m))
        = fun sample ↦
          first (sample n) * third (sample n) * (second (sample m) * fourth (sample m)) :=
      funext fun sample ↦ by ring
    have hB : (fun sample : Fin size → Ω ↦
        first (sample n) * second (sample m) * third (sample m) * fourth (sample n))
        = fun sample ↦
          first (sample n) * fourth (sample n) * (second (sample m) * third (sample m)) :=
      funext fun sample ↦ by ring
    rw [hA, hB, expectation_mul_of_ne law (fun individual ↦ first individual * third individual)
        (fun individual ↦ second individual * fourth individual) hnm,
      expectation_mul_of_ne law (fun individual ↦ first individual * fourth individual)
        (fun individual ↦ second individual * third individual) hnm]
  have hexpand : ∀ sample : Fin size → Ω,
      (∑ n, ∑ m, if n = m then 0 else first (sample n) * second (sample m))
        * (∑ k, ∑ l, if k = l then 0 else third (sample k) * fourth (sample l))
      = ∑ n, ∑ m, ∑ k, ∑ l, if n = m then 0 else if k = l then 0
          else first (sample n) * second (sample m) * third (sample k) * fourth (sample l) := by
    intro sample
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    split_ifs <;> ring
  have hpair : ∀ n m : Fin size, (cohortLaw law size).expectation (fun sample ↦
      ∑ k, ∑ l, if n = m then 0 else if k = l then 0
        else first (sample n) * second (sample m) * third (sample k) * fourth (sample l))
      = if n = m then 0
        else law.expectation (fun individual ↦ first individual * third individual)
            * law.expectation (fun individual ↦ second individual * fourth individual)
          + law.expectation (fun individual ↦ first individual * fourth individual)
            * law.expectation (fun individual ↦ second individual * third individual) := by
    intro n m
    by_cases hnm : n = m
    · simp only [if_pos hnm, Finset.sum_const_zero]
      exact FiniteIndependentMoments.expectation_const _ 0
    · simp only [if_neg hnm]
      rw [FiniteIndependentMoments.expectation_sum]
      simp only [FiniteIndependentMoments.expectation_sum]
      exact hrow n m hnm
  simp only [hexpand]
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, hpair]
  exact sum_offDiagonal_const size _

/-! ## The exact first and second moments of sample covariances -/

/-- **The fourth central co-moment** `E[(f − E f)(g − E g)(h − E h)(k − E k)]` of four
observables. -/
def fourthCoMoment (law : FiniteReportLaw Ω) (first second third fourth : Ω → ℝ) : ℝ :=
  law.expectation fun individual ↦
    (first individual - law.expectation first) * (second individual - law.expectation second)
      * ((third individual - law.expectation third) * (fourth individual - law.expectation fourth))

/-- **The sample covariance is unbiased.**  On a cohort of size `n ≥ 2`, `E ĉ(f, g) = C_fg`. -/
theorem expectation_sampleCovariance (law : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (first second : Ω → ℝ) :
    (cohortLaw law size).expectation (sampleCovariance first second)
      = law.covariance first second := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hN0 : (size : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hsplit : sampleCovariance first second = fun sample : Fin size → Ω ↦
      (size : ℝ)⁻¹ * ∑ n, (first (sample n) - law.expectation first)
          * (second (sample n) - law.expectation second)
        + -((size : ℝ) * ((size : ℝ) - 1))⁻¹
          * ∑ n, ∑ m, if n = m then 0 else (first (sample n) - law.expectation first)
            * (second (sample m) - law.expectation second) :=
    funext fun sample ↦ sampleCovariance_eq_diagonal_sub_offDiagonal hsize first second _ _ sample
  rw [hsplit, expectation_linear,
    expectation_diagonal law size fun individual ↦
      (first individual - law.expectation first) * (second individual - law.expectation second),
    expectation_offDiagonal law size (fun individual ↦ first individual - law.expectation first)
      (fun individual ↦ second individual - law.expectation second)
      (expectation_sub_expectation law first),
    mul_zero, add_zero, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rfl

/-- **The exact second moment of two sample covariances.**  On a cohort of size `n ≥ 2`,
`E[ĉ(f, g) ĉ(h, k)] = C_fg C_hk + (K − C_fg C_hk) / n + (C_fh C_gk + C_fk C_gh) / (n (n − 1))`,
with `K` the fourth central co-moment of `f`, `g`, `h`, `k`. -/
theorem expectation_sampleCovariance_mul (law : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (first second third fourth : Ω → ℝ) :
    (cohortLaw law size).expectation (fun sample ↦
        sampleCovariance first second sample * sampleCovariance third fourth sample)
      = law.covariance first second * law.covariance third fourth
        + (fourthCoMoment law first second third fourth
          - law.covariance first second * law.covariance third fourth) / size
        + (law.covariance first third * law.covariance second fourth
          + law.covariance first fourth * law.covariance second third) / (size * (size - 1)) := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hN0 : (size : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN1 : (size : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hproduct : (fun sample : Fin size → Ω ↦
      sampleCovariance first second sample * sampleCovariance third fourth sample)
      = fun sample ↦ (size : ℝ)⁻¹ * (size : ℝ)⁻¹
            * ((∑ n, (first (sample n) - law.expectation first)
                * (second (sample n) - law.expectation second))
              * ∑ k, (third (sample k) - law.expectation third)
                * (fourth (sample k) - law.expectation fourth))
        + (size : ℝ)⁻¹ * -((size : ℝ) * ((size : ℝ) - 1))⁻¹
            * ((∑ n, (first (sample n) - law.expectation first)
                * (second (sample n) - law.expectation second))
              * ∑ k, ∑ l, if k = l then 0 else (third (sample k) - law.expectation third)
                * (fourth (sample l) - law.expectation fourth))
        + -((size : ℝ) * ((size : ℝ) - 1))⁻¹ * (size : ℝ)⁻¹
            * ((∑ n, ∑ m, if n = m then 0 else (first (sample n) - law.expectation first)
                * (second (sample m) - law.expectation second))
              * ∑ k, (third (sample k) - law.expectation third)
                * (fourth (sample k) - law.expectation fourth))
        + -((size : ℝ) * ((size : ℝ) - 1))⁻¹ * -((size : ℝ) * ((size : ℝ) - 1))⁻¹
            * ((∑ n, ∑ m, if n = m then 0 else (first (sample n) - law.expectation first)
                * (second (sample m) - law.expectation second))
              * ∑ k, ∑ l, if k = l then 0 else (third (sample k) - law.expectation third)
                * (fourth (sample l) - law.expectation fourth)) := by
    funext sample
    rw [sampleCovariance_eq_diagonal_sub_offDiagonal hsize first second (law.expectation first)
        (law.expectation second),
      sampleCovariance_eq_diagonal_sub_offDiagonal hsize third fourth (law.expectation third)
        (law.expectation fourth)]
    ring
  rw [hproduct, expectation_linear_four,
    expectation_diagonal_mul_diagonal law size
      (fun individual ↦ (first individual - law.expectation first)
        * (second individual - law.expectation second))
      (fun individual ↦ (third individual - law.expectation third)
        * (fourth individual - law.expectation fourth)),
    expectation_diagonal_mul_offDiagonal law size
      (fun individual ↦ first individual - law.expectation first)
      (fun individual ↦ second individual - law.expectation second)
      (fun individual ↦ third individual - law.expectation third)
      (fun individual ↦ fourth individual - law.expectation fourth)
      (expectation_sub_expectation law third) (expectation_sub_expectation law fourth),
    expectation_offDiagonal_mul_diagonal law size
      (fun individual ↦ first individual - law.expectation first)
      (fun individual ↦ second individual - law.expectation second)
      (fun individual ↦ third individual - law.expectation third)
      (fun individual ↦ fourth individual - law.expectation fourth)
      (expectation_sub_expectation law first) (expectation_sub_expectation law second),
    expectation_offDiagonal_mul_offDiagonal law size
      (fun individual ↦ first individual - law.expectation first)
      (fun individual ↦ second individual - law.expectation second)
      (fun individual ↦ third individual - law.expectation third)
      (fun individual ↦ fourth individual - law.expectation fourth)
      (expectation_sub_expectation law third) (expectation_sub_expectation law fourth)]
  simp only [FiniteReportLaw.covariance, fourthCoMoment]
  field_simp
  ring

/-- On a cohort of two, the sample covariance is the pair kernel `(f₀ − f₁)(g₀ − g₁) / 2`. -/
theorem sampleCovariance_two (first second : Ω → ℝ) (sample : Fin 2 → Ω) :
    sampleCovariance first second sample
      = (first (sample 0) - first (sample 1)) * (second (sample 0) - second (sample 1)) / 2 := by
  simp only [sampleCovariance, sampleMean, Fin.sum_univ_two, Nat.cast_ofNat]
  ring

/-- A cohort of two reads a pair observable as the double expectation. -/
theorem expectation_cohortLaw_two (law : FiniteReportLaw Ω) (credit : Ω → Ω → ℝ) :
    (cohortLaw law 2).expectation (fun sample ↦ credit (sample 0) (sample 1))
      = law.expectation fun first ↦ law.expectation fun second ↦ credit first second := by
  calc (cohortLaw law 2).expectation (fun sample ↦ credit (sample 0) (sample 1))
      = ∑ pair : Ω × Ω, law.mass pair.1 * (law.mass pair.2 * credit pair.1 pair.2) :=
        Fintype.sum_equiv (piFinTwoEquiv fun _ ↦ Ω) _ _ fun sample ↦ by
          rw [cohortLaw_mass, Fin.prod_univ_two, mul_assoc]
          rfl
    _ = law.expectation fun first ↦ law.expectation fun second ↦ credit first second := by
        simp only [Fintype.sum_prod_type, FiniteReportLaw.expectation, Finset.mul_sum]

/-- **The fourth co-moment from a cohort of two.**  `K(f, g, h, k)` is twice the expected product
of the pair kernels of `(f, g)` and `(h, k)` over two independent draws, minus the three pairings
`C_fg C_hk + C_fh C_gk + C_fk C_gh`. -/
theorem fourthCoMoment_eq_pairExpectation (law : FiniteReportLaw Ω)
    (first second third fourth : Ω → ℝ) :
    fourthCoMoment law first second third fourth
      = 2 * law.expectation (fun a ↦ law.expectation fun b ↦
          (first a - first b) * (second a - second b) / 2
            * ((third a - third b) * (fourth a - fourth b) / 2))
        - law.covariance first second * law.covariance third fourth
        - law.covariance first third * law.covariance second fourth
        - law.covariance first fourth * law.covariance second third := by
  have h := expectation_sampleCovariance_mul law (le_refl 2) first second third fourth
  simp only [sampleCovariance_two] at h
  rw [expectation_cohortLaw_two law fun a b ↦
    (first a - first b) * (second a - second b) / 2
      * ((third a - third b) * (fourth a - fourth b) / 2)] at h
  push_cast at h
  linarith

/-! ## The marginal-effect GWAS -/

section Training

variable {J : Type*} [Fintype J]

/-- **The marginal-effect GWAS.**  The weight of each tag is the unbiased sample covariance of the
tag with the outcome over the training cohort. -/
def gwasWeights {size : ℕ} (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (sample : Fin size → Ω) :
    J → ℝ :=
  fun marker ↦ sampleCovariance (fun individual ↦ genotype individual marker) outcome sample

/-- **The population marginal effects** a GWAS estimates: the covariance of each tag with the
outcome. -/
def marginalWeights (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    J → ℝ :=
  fun marker ↦ law.covariance (fun individual ↦ genotype individual marker) outcome

/-- **The excess matrix** `E_ij = K(X_i, Y, X_j, Y) − w_i w_j`: the covariance of the products
`(X_i − E X_i)(Y − E Y)` and `(X_j − E X_j)(Y − E Y)`. -/
def weightExcess (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (i j : J) : ℝ :=
  fourthCoMoment law (fun individual ↦ genotype individual i) outcome
      (fun individual ↦ genotype individual j) outcome
    - marginalWeights law genotype outcome i * marginalWeights law genotype outcome j

/-- **The pairing matrix** `P_ij = C(X_i, X_j) V_Y + w_i w_j`. -/
def weightPairing (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (i j : J) : ℝ :=
  law.covariance (fun individual ↦ genotype individual i) (fun individual ↦ genotype individual j)
      * law.variance outcome
    + marginalWeights law genotype outcome i * marginalWeights law genotype outcome j

/-- **The sampling form** `a + b / n + c / (n (n − 1))`, in which every finite-cohort expectation
of a quadratic form in the GWAS weights is written. -/
def samplingForm (population excess pairing : ℝ) (size : ℕ) : ℝ :=
  population + excess / size + pairing / (size * (size - 1))

/-- **The GWAS weights are unbiased**: `E ŵ_j = w_j`. -/
theorem expectation_gwasWeights (law : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (marker : J) :
    (cohortLaw law size).expectation (fun sample ↦ gwasWeights genotype outcome sample marker)
      = marginalWeights law genotype outcome marker :=
  expectation_sampleCovariance law hsize _ outcome

/-- **The exact second moments of the GWAS weights**:
`E[ŵ_i ŵ_j] = w_i w_j + E_ij / n + P_ij / (n (n − 1))`. -/
theorem expectation_gwasWeights_mul (law : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (i j : J) :
    (cohortLaw law size).expectation (fun sample ↦
        gwasWeights genotype outcome sample i * gwasWeights genotype outcome sample j)
      = samplingForm
          (marginalWeights law genotype outcome i * marginalWeights law genotype outcome j)
          (weightExcess law genotype outcome i j) (weightPairing law genotype outcome i j)
          size := by
  have h := expectation_sampleCovariance_mul law hsize (fun individual ↦ genotype individual i)
    outcome (fun individual ↦ genotype individual j) outcome
  rw [covariance_symmetric law outcome (fun individual ↦ genotype individual j)] at h
  exact h

/-- **Cohort expectations of quadratic forms in the GWAS weights** are sampling forms, with the
population, excess and pairing matrices read against the supplied matrix. -/
theorem expectation_quadraticForm_gwasWeights (law : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) (matrix : J → J → ℝ) :
    (cohortLaw law size).expectation (fun sample ↦ ∑ i, ∑ j, matrix i j
        * (gwasWeights genotype outcome sample i * gwasWeights genotype outcome sample j))
      = samplingForm
          (∑ i, ∑ j, matrix i j
            * (marginalWeights law genotype outcome i * marginalWeights law genotype outcome j))
          (∑ i, ∑ j, matrix i j * weightExcess law genotype outcome i j)
          (∑ i, ∑ j, matrix i j * weightPairing law genotype outcome i j) size := by
  have hterm : ∀ i j : J, (cohortLaw law size).expectation (fun sample ↦
      matrix i j * (gwasWeights genotype outcome sample i * gwasWeights genotype outcome sample j))
      = matrix i j
          * (marginalWeights law genotype outcome i * marginalWeights law genotype outcome j)
        + matrix i j * weightExcess law genotype outcome i j / size
        + matrix i j * weightPairing law genotype outcome i j / (size * (size - 1)) := by
    intro i j
    rw [expectation_const_mul_observable, expectation_gwasWeights_mul law hsize, samplingForm]
    ring
  rw [FiniteIndependentMoments.expectation_sum]
  simp only [FiniteIndependentMoments.expectation_sum, hterm, Finset.sum_add_distrib,
    ← Finset.sum_div, samplingForm]

/-! ## Deployment in a target law -/

/-- The target matrix of the correlation numerator, `16 c_i c_j`, with `c` the target marginal
effects. -/
def numeratorMatrix (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (i j : J) : ℝ :=
  16 * (marginalWeights target genotype outcome i * marginalWeights target genotype outcome j)

/-- The target matrix of the correlation denominator, `16 C_t(X_i, X_j) V_t(Y)`. -/
def denominatorMatrix (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (i j : J) : ℝ :=
  16 * (target.covariance (fun individual ↦ genotype individual i)
      (fun individual ↦ genotype individual j) * target.variance outcome)

/-- The correlation numerator of a linear score is a quadratic form in its weights. -/
theorem correlationNumerator_linearScore (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (weights : J → ℝ) :
    correlationNumerator target (linearScore genotype weights) outcome
      = ∑ i, ∑ j, numeratorMatrix target genotype outcome i j * (weights i * weights j) := by
  rw [correlationNumerator, covariance_linearScore, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [numeratorMatrix, marginalWeights]
  ring

/-- The correlation denominator of a linear score is a quadratic form in its weights. -/
theorem correlationDenominator_linearScore (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (weights : J → ℝ) :
    correlationDenominator target (linearScore genotype weights) outcome
      = ∑ i, ∑ j, denominatorMatrix target genotype outcome i j * (weights i * weights j) := by
  rw [correlationDenominator, variance_linearScore, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [denominatorMatrix]
  ring

/-- **The expected target correlation numerator of a GWAS score** trained on a cohort of `size`
individuals from the source law. -/
def trainedNumerator (source target : FiniteReportLaw Ω) (size : ℕ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    correlationNumerator target (linearScore genotype (gwasWeights genotype outcome sample))
      outcome

/-- **The expected target correlation denominator of a GWAS score** trained on a cohort of
`size` individuals from the source law. -/
def trainedDenominator (source target : FiniteReportLaw Ω) (size : ℕ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  (cohortLaw source size).expectation fun sample ↦
    correlationDenominator target (linearScore genotype (gwasWeights genotype outcome sample))
      outcome

/-- **The trained accuracy**: the expected target numerator over the expected target
denominator.  NOTE2 §6.2 query: a ratio of expectations over the training cohort. -/
def trainedAccuracy (source target : FiniteReportLaw Ω) (size : ℕ) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) : ℝ :=
  trainedNumerator source target size genotype outcome
    / trainedDenominator source target size genotype outcome

/-- **The trained numerator is a sampling form**: the numerator of the population marginal score,
plus the excess matrix read against `16 c cᵀ` over `n`, plus the pairing matrix read against it
over `n (n − 1)`. -/
theorem trainedNumerator_eq (source target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedNumerator source target size genotype outcome
      = samplingForm
          (correlationNumerator target
            (linearScore genotype (marginalWeights source genotype outcome)) outcome)
          (∑ i, ∑ j, numeratorMatrix target genotype outcome i j
            * weightExcess source genotype outcome i j)
          (∑ i, ∑ j, numeratorMatrix target genotype outcome i j
            * weightPairing source genotype outcome i j) size := by
  rw [trainedNumerator, correlationNumerator_linearScore]
  simp only [correlationNumerator_linearScore]
  exact expectation_quadraticForm_gwasWeights source hsize genotype outcome _

/-- **The trained denominator is a sampling form**, with the target matrix
`16 C_t(X_i, X_j) V_t(Y)`. -/
theorem trainedDenominator_eq (source target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedDenominator source target size genotype outcome
      = samplingForm
          (correlationDenominator target
            (linearScore genotype (marginalWeights source genotype outcome)) outcome)
          (∑ i, ∑ j, denominatorMatrix target genotype outcome i j
            * weightExcess source genotype outcome i j)
          (∑ i, ∑ j, denominatorMatrix target genotype outcome i j
            * weightPairing source genotype outcome i j) size := by
  rw [trainedDenominator, correlationDenominator_linearScore]
  simp only [correlationDenominator_linearScore]
  exact expectation_quadraticForm_gwasWeights source hsize genotype outcome _

/-- **The plug-in estimator gives the same accuracy.**  Weights estimated with divisor `n` are the
unbiased weights times `(n − 1) / n`, and the trained accuracy is quadratic in the weights in both
numerator and denominator. -/
theorem plugInAccuracy_eq_trainedAccuracy (source target : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    (cohortLaw source size).expectation (fun sample ↦ correlationNumerator target
          (linearScore genotype fun marker ↦
            plugInCovariance (fun individual ↦ genotype individual marker) outcome sample)
          outcome)
        / (cohortLaw source size).expectation (fun sample ↦ correlationDenominator target
          (linearScore genotype fun marker ↦
            plugInCovariance (fun individual ↦ genotype individual marker) outcome sample)
          outcome)
      = trainedAccuracy source target size genotype outcome := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hfactor : ((size : ℝ) - 1) / size ≠ 0 :=
    div_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  have hnumerator : ∀ sample : Fin size → Ω, correlationNumerator target
      (linearScore genotype fun marker ↦
        plugInCovariance (fun individual ↦ genotype individual marker) outcome sample) outcome
      = ((size : ℝ) - 1) / size * (((size : ℝ) - 1) / size)
        * correlationNumerator target (linearScore genotype (gwasWeights genotype outcome sample))
          outcome := by
    intro sample
    simp only [plugInCovariance_eq hsize, correlationNumerator_linearScore, gwasWeights,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hdenominator : ∀ sample : Fin size → Ω, correlationDenominator target
      (linearScore genotype fun marker ↦
        plugInCovariance (fun individual ↦ genotype individual marker) outcome sample) outcome
      = ((size : ℝ) - 1) / size * (((size : ℝ) - 1) / size)
        * correlationDenominator target
          (linearScore genotype (gwasWeights genotype outcome sample)) outcome := by
    intro sample
    simp only [plugInCovariance_eq hsize, correlationDenominator_linearScore, gwasWeights,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [hnumerator, hdenominator, expectation_const_mul_observable]
  rw [mul_div_mul_left _ _ (mul_self_ne_zero.mpr hfactor)]
  rfl

/-! ## The excess and pairing quadratic forms -/

/-- **The pairing quadratic form** is the source score variance times the outcome variance plus
the squared source covariance: `uᵀ P u = V(S_u) V_Y + C(S_u, Y)²`. -/
theorem quadraticForm_weightPairing (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (u : J → ℝ) :
    ∑ i, ∑ j, u i * u j * weightPairing law genotype outcome i j
      = law.variance (linearScore genotype u) * law.variance outcome
        + law.covariance (linearScore genotype u) outcome ^ 2 := by
  rw [variance_linearScore, covariance_linearScore, sq, Finset.sum_mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [weightPairing, marginalWeights]
  ring

/-- **The excess quadratic form is a variance**: `uᵀ E u` is the variance of
`(S_u − E S_u)(Y − E Y)`. -/
theorem quadraticForm_weightExcess (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (u : J → ℝ) :
    ∑ i, ∑ j, u i * u j * weightExcess law genotype outcome i j
      = law.variance (fun individual ↦
          (linearScore genotype u individual - law.expectation (linearScore genotype u))
            * (outcome individual - law.expectation outcome)) := by
  have hdeviation : ∀ individual, linearScore genotype u individual
      - law.expectation (linearScore genotype u)
      = ∑ i, u i * (genotype individual i - law.expectation fun other ↦ genotype other i) := by
    intro individual
    rw [expectation_linearScore]
    simp only [linearScore, mul_sub, Finset.sum_sub_distrib]
  have hsquare : law.expectation (fun individual ↦
      ((linearScore genotype u individual - law.expectation (linearScore genotype u))
        * (outcome individual - law.expectation outcome)) ^ 2)
      = ∑ i, ∑ j, u i * u j * fourthCoMoment law (fun individual ↦ genotype individual i)
          outcome (fun individual ↦ genotype individual j) outcome := by
    have hproduct : ∀ individual, ((linearScore genotype u individual
        - law.expectation (linearScore genotype u))
        * (outcome individual - law.expectation outcome)) ^ 2
        = ∑ i, ∑ j, u i * u j
          * ((genotype individual i - law.expectation fun other ↦ genotype other i)
            * (outcome individual - law.expectation outcome)
            * ((genotype individual j - law.expectation fun other ↦ genotype other j)
              * (outcome individual - law.expectation outcome))) := by
      intro individual
      rw [hdeviation, sq, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    simp only [hproduct]
    rw [FiniteIndependentMoments.expectation_sum]
    simp only [FiniteIndependentMoments.expectation_sum, expectation_const_mul_observable]
    rfl
  rw [FiniteReportLaw.variance_eq_rawMoments, hsquare]
  have hmean : law.expectation (fun individual ↦
      (linearScore genotype u individual - law.expectation (linearScore genotype u))
        * (outcome individual - law.expectation outcome))
      = ∑ i, u i * marginalWeights law genotype outcome i :=
    covariance_linearScore law genotype u outcome
  rw [hmean, sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [weightExcess]
  ring

/-- The excess quadratic form is nonnegative. -/
theorem quadraticForm_weightExcess_nonneg (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (u : J → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * u j * weightExcess law genotype outcome i j := by
  rw [quadraticForm_weightExcess]
  exact law.variance_nonneg _

/-- The pairing quadratic form is nonnegative. -/
theorem quadraticForm_weightPairing_nonneg (law : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (u : J → ℝ) :
    0 ≤ ∑ i, ∑ j, u i * u j * weightPairing law genotype outcome i j := by
  rw [quadraticForm_weightPairing]
  exact add_nonneg (mul_nonneg (law.variance_nonneg _) (law.variance_nonneg _)) (sq_nonneg _)

/-- A matrix read against the numerator matrix is sixteen times its quadratic form at the target
marginal effects. -/
theorem sum_numeratorMatrix_mul (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (matrix : J → J → ℝ) :
    ∑ i, ∑ j, numeratorMatrix target genotype outcome i j * matrix i j
      = 16 * ∑ i, ∑ j, marginalWeights target genotype outcome i
          * marginalWeights target genotype outcome j * matrix i j := by
  simp only [numeratorMatrix, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- A nonnegative quadratic form read against the numerator matrix is nonnegative. -/
theorem sum_numeratorMatrix_mul_nonneg (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (matrix : J → J → ℝ)
    (hmatrix : ∀ u : J → ℝ, 0 ≤ ∑ i, ∑ j, u i * u j * matrix i j) :
    0 ≤ ∑ i, ∑ j, numeratorMatrix target genotype outcome i j * matrix i j := by
  rw [sum_numeratorMatrix_mul]
  exact mul_nonneg (by norm_num) (hmatrix _)

/-- **A nonnegative quadratic form read against a covariance matrix is nonnegative.**  The
denominator matrix is `16 V_t(Y)` times the target tag covariance, which is the target
expectation of the rank-one forms of the centered tags. -/
theorem sum_denominatorMatrix_mul_nonneg (target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) (matrix : J → J → ℝ)
    (hmatrix : ∀ u : J → ℝ, 0 ≤ ∑ i, ∑ j, u i * u j * matrix i j) :
    0 ≤ ∑ i, ∑ j, denominatorMatrix target genotype outcome i j * matrix i j := by
  have hrewrite : ∑ i, ∑ j, denominatorMatrix target genotype outcome i j * matrix i j
      = 16 * target.variance outcome * target.expectation (fun individual ↦ ∑ i, ∑ j,
          (genotype individual i - target.expectation fun other ↦ genotype other i)
            * (genotype individual j - target.expectation fun other ↦ genotype other j)
            * matrix i j) := by
    rw [FiniteIndependentMoments.expectation_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [FiniteIndependentMoments.expectation_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hswap : (fun individual ↦
        (genotype individual i - target.expectation fun other ↦ genotype other i)
          * (genotype individual j - target.expectation fun other ↦ genotype other j)
          * matrix i j)
        = fun individual ↦ matrix i j
          * ((genotype individual i - target.expectation fun other ↦ genotype other i)
            * (genotype individual j - target.expectation fun other ↦ genotype other j)) :=
      funext fun individual ↦ mul_comm _ _
    rw [hswap, expectation_const_mul_observable]
    simp only [denominatorMatrix, FiniteReportLaw.covariance]
    ring
  rw [hrewrite]
  exact mul_nonneg (mul_nonneg (by norm_num) (target.variance_nonneg outcome))
    (ReplicaDomainCertificate.expectation_nonneg target _ fun individual ↦ hmatrix _)

/-! ## Monotonicity, limits and the exact form of the deflation -/

/-- A sampling form with nonnegative noise coefficients is at least its population term. -/
theorem le_samplingForm {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) {size : ℕ} (hsize : 2 ≤ size) :
    a ≤ samplingForm a b c size := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hexcess : 0 ≤ b / size := div_nonneg hb (by linarith)
  have hpairing : 0 ≤ c / (size * (size - 1)) :=
    div_nonneg hc (mul_nonneg (by linarith) (by linarith))
  unfold samplingForm
  linarith

/-- **A sampling form with nonnegative noise coefficients decreases in the cohort size.** -/
theorem samplingForm_antitone {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) {small large : ℕ}
    (hsmall : 2 ≤ small) (hle : small ≤ large) :
    samplingForm a b c large ≤ samplingForm a b c small := by
  have hs : (2 : ℝ) ≤ small := by exact_mod_cast hsmall
  have hl : (small : ℝ) ≤ large := by exact_mod_cast hle
  have hexcess : b / large ≤ b / small := div_le_div_of_nonneg_left hb (by linarith) hl
  have hpairing : c / (large * (large - 1)) ≤ c / (small * (small - 1)) :=
    div_le_div_of_nonneg_left hc (mul_pos (by linarith) (by linarith))
      (mul_le_mul hl (by linarith) (by linarith) (by linarith))
  unfold samplingForm
  linarith

/-- **A sampling form tends to its population term** as the cohort grows. -/
theorem tendsto_samplingForm (a b c : ℝ) :
    Tendsto (fun size : ℕ ↦ samplingForm a b c size) atTop (𝓝 a) := by
  have hgrowth : Tendsto (fun size : ℕ ↦ (size : ℝ) * ((size : ℝ) - 1)) atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_ge_atTop 2).mono fun size hsize ↦ by
      have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
      nlinarith) tendsto_natCast_atTop_atTop
  have hexcess := tendsto_const_div_atTop_nhds_zero_nat b
  have hpairing := (tendsto_const_nhds (x := c)).div_atTop hgrowth
  simpa only [samplingForm, add_zero] using (tendsto_const_nhds.add hexcess).add hpairing

/-- **The exact form of the finite-sample deflation.**  A ratio of sampling forms is at most the
ratio of the population terms exactly when the numerator noise times the population denominator
is at most the denominator noise times the population numerator: the ratio is the mediant of the
population ratio and the noise ratio. -/
theorem samplingForm_div_le_iff {a b c α β γ : ℝ} {size : ℕ} (hα : 0 < α)
    (hden : 0 < samplingForm α β γ size) :
    samplingForm a b c size / samplingForm α β γ size ≤ a / α
      ↔ (b / size + c / (size * (size - 1))) * α
        ≤ (β / size + γ / (size * (size - 1))) * a := by
  rw [div_le_div_iff₀ hden hα]
  unfold samplingForm
  constructor <;> intro h <;> linarith

/-- **The trained numerator decreases in the cohort size.** -/
theorem trainedNumerator_antitone (source target : FiniteReportLaw Ω) {small large : ℕ}
    (hsmall : 2 ≤ small) (hle : small ≤ large) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedNumerator source target large genotype outcome
      ≤ trainedNumerator source target small genotype outcome := by
  rw [trainedNumerator_eq source target (hsmall.trans hle),
    trainedNumerator_eq source target hsmall]
  exact samplingForm_antitone
    (sum_numeratorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightExcess_nonneg source genotype outcome))
    (sum_numeratorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightPairing_nonneg source genotype outcome)) hsmall hle

/-- **The trained denominator decreases in the cohort size.** -/
theorem trainedDenominator_antitone (source target : FiniteReportLaw Ω) {small large : ℕ}
    (hsmall : 2 ≤ small) (hle : small ≤ large) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    trainedDenominator source target large genotype outcome
      ≤ trainedDenominator source target small genotype outcome := by
  rw [trainedDenominator_eq source target (hsmall.trans hle),
    trainedDenominator_eq source target hsmall]
  exact samplingForm_antitone
    (sum_denominatorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightExcess_nonneg source genotype outcome))
    (sum_denominatorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightPairing_nonneg source genotype outcome)) hsmall hle

/-- **Finite training inflates the numerator**: it is at least the numerator of the population
marginal score. -/
theorem le_trainedNumerator (source target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    correlationNumerator target (linearScore genotype (marginalWeights source genotype outcome))
        outcome
      ≤ trainedNumerator source target size genotype outcome := by
  rw [trainedNumerator_eq source target hsize]
  exact le_samplingForm
    (sum_numeratorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightExcess_nonneg source genotype outcome))
    (sum_numeratorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightPairing_nonneg source genotype outcome)) hsize

/-- **Finite training inflates the denominator**: it is at least the denominator of the population
marginal score. -/
theorem le_trainedDenominator (source target : FiniteReportLaw Ω) {size : ℕ} (hsize : 2 ≤ size)
    (genotype : Ω → J → ℝ) (outcome : Ω → ℝ) :
    correlationDenominator target
        (linearScore genotype (marginalWeights source genotype outcome)) outcome
      ≤ trainedDenominator source target size genotype outcome := by
  rw [trainedDenominator_eq source target hsize]
  exact le_samplingForm
    (sum_denominatorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightExcess_nonneg source genotype outcome))
    (sum_denominatorMatrix_mul_nonneg target genotype outcome _
      (quadraticForm_weightPairing_nonneg source genotype outcome)) hsize

/-- **The trained numerator tends to the population marginal-score numerator.** -/
theorem tendsto_trainedNumerator (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    Tendsto (fun size : ℕ ↦ trainedNumerator source target size genotype outcome) atTop
      (𝓝 (correlationNumerator target
        (linearScore genotype (marginalWeights source genotype outcome)) outcome)) :=
  (tendsto_samplingForm _ _ _).congr' ((eventually_ge_atTop 2).mono fun _ hsize ↦
    (trainedNumerator_eq source target hsize genotype outcome).symm)

/-- **The trained denominator tends to the population marginal-score denominator.** -/
theorem tendsto_trainedDenominator (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ) :
    Tendsto (fun size : ℕ ↦ trainedDenominator source target size genotype outcome) atTop
      (𝓝 (correlationDenominator target
        (linearScore genotype (marginalWeights source genotype outcome)) outcome)) :=
  (tendsto_samplingForm _ _ _).congr' ((eventually_ge_atTop 2).mono fun _ hsize ↦
    (trainedDenominator_eq source target hsize genotype outcome).symm)

/-- **The trained accuracy tends to the accuracy of the population marginal score**, wherever that
score has a nonzero target denominator. -/
theorem tendsto_trainedAccuracy (source target : FiniteReportLaw Ω) (genotype : Ω → J → ℝ)
    (outcome : Ω → ℝ)
    (hdenominator : correlationDenominator target
      (linearScore genotype (marginalWeights source genotype outcome)) outcome ≠ 0) :
    Tendsto (fun size : ℕ ↦ trainedAccuracy source target size genotype outcome) atTop
      (𝓝 (correlationNumerator target
          (linearScore genotype (marginalWeights source genotype outcome)) outcome
        / correlationDenominator target
          (linearScore genotype (marginalWeights source genotype outcome)) outcome)) :=
  (tendsto_trainedNumerator source target genotype outcome).div
    (tendsto_trainedDenominator source target genotype outcome) hdenominator

/-- **With a single tag, finite training does not change the accuracy.**  The trained score is a
random multiple of the one tag, and both accumulators are quadratic in the weight. -/
theorem trainedAccuracy_unique [Unique J] (source target : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hsignal : marginalWeights source genotype outcome default ≠ 0) :
    trainedAccuracy source target size genotype outcome
      = correlationNumerator target
          (linearScore genotype (marginalWeights source genotype outcome)) outcome
        / correlationDenominator target
          (linearScore genotype (marginalWeights source genotype outcome)) outcome := by
  have hsecond : 0 < (cohortLaw source size).expectation (fun sample ↦
      gwasWeights genotype outcome sample default
        * gwasWeights genotype outcome sample default) := by
    rw [expectation_gwasWeights_mul source hsize]
    have hexcess := quadraticForm_weightExcess_nonneg source genotype outcome fun _ ↦ 1
    have hpairing := quadraticForm_weightPairing_nonneg source genotype outcome fun _ ↦ 1
    simp only [Fintype.sum_unique, one_mul] at hexcess hpairing
    exact (mul_self_pos.mpr hsignal).trans_le (le_samplingForm hexcess hpairing hsize)
  unfold trainedAccuracy trainedNumerator trainedDenominator
  simp only [correlationNumerator_linearScore, correlationDenominator_linearScore,
    Fintype.sum_unique, expectation_const_mul_observable]
  rw [mul_div_mul_right _ _ hsecond.ne', mul_div_mul_right _ _ (mul_self_ne_zero.mpr hsignal)]

/-- **Finite-sample training can raise the accuracy above the population value.**  Suppose the
population marginal score is uncorrelated with the outcome in the target, the target marginal
score and the outcome vary in the source, and the population target denominator is positive.
Then the population marginal-score accuracy is zero and every finite cohort gives positive trained
accuracy. -/
theorem populationAccuracy_lt_trainedAccuracy (source target : FiniteReportLaw Ω) {size : ℕ}
    (hsize : 2 ≤ size) (genotype : Ω → J → ℝ) (outcome : Ω → ℝ)
    (hzero : target.covariance
      (linearScore genotype (marginalWeights source genotype outcome)) outcome = 0)
    (hscore : 0 < source.variance (linearScore genotype (marginalWeights target genotype outcome)))
    (houtcome : 0 < source.variance outcome)
    (hdenominator : 0 < correlationDenominator target
      (linearScore genotype (marginalWeights source genotype outcome)) outcome) :
    correlationNumerator target
          (linearScore genotype (marginalWeights source genotype outcome)) outcome
        / correlationDenominator target
          (linearScore genotype (marginalWeights source genotype outcome)) outcome = 0
      ∧ 0 < trainedAccuracy source target size genotype outcome := by
  have hN : (2 : ℝ) ≤ size := by exact_mod_cast hsize
  have hpopulation : correlationNumerator target
      (linearScore genotype (marginalWeights source genotype outcome)) outcome = 0 := by
    rw [correlationNumerator, hzero]
    norm_num
  refine ⟨by rw [hpopulation, zero_div], ?_⟩
  have hpairing : 0 < ∑ i, ∑ j, numeratorMatrix target genotype outcome i j
      * weightPairing source genotype outcome i j := by
    rw [sum_numeratorMatrix_mul, quadraticForm_weightPairing]
    have hproduct := mul_pos hscore houtcome
    positivity
  have hexcess := sum_numeratorMatrix_mul_nonneg target genotype outcome _
    (quadraticForm_weightExcess_nonneg source genotype outcome)
  have hnumerator : 0 < trainedNumerator source target size genotype outcome := by
    rw [trainedNumerator_eq source target hsize, hpopulation, samplingForm]
    have hfirst : 0 ≤ (∑ i, ∑ j, numeratorMatrix target genotype outcome i j
        * weightExcess source genotype outcome i j) / size := div_nonneg hexcess (by linarith)
    have hsecond : 0 < (∑ i, ∑ j, numeratorMatrix target genotype outcome i j
        * weightPairing source genotype outcome i j) / (size * (size - 1)) :=
      div_pos hpairing (mul_pos (by linarith) (by linarith))
    linarith
  exact div_pos hnumerator (hdenominator.trans_le (le_trainedDenominator source target hsize
    genotype outcome))

end Training

/-! ## A two-locus witness -/

/-- The witness target law on the four haplotypes of two biallelic loci, with masses
`1/4, 1/4, 0, 1/2`. -/
def trainingWitnessTarget : FiniteReportLaw (Fin 4) where
  mass := ![1 / 4, 1 / 4, 0, 1 / 2]
  mass_nonneg := by
    intro haplotype
    fin_cases haplotype <;> norm_num
  mass_sum := by
    rw [Fin.sum_univ_four]
    norm_num

/-- The witness tags: the biallelic contrasts `rad1` and `rad2` of the master theorem. -/
def trainingWitnessGenotype (haplotype : Fin 4) (marker : Fin 2) : ℝ :=
  ![rad1 haplotype, rad2 haplotype] marker

/-- The witness outcome: an additive effect of the first locus plus an interaction of the two
loci. -/
def trainingWitnessOutcome (haplotype : Fin 4) : ℝ :=
  rad1 haplotype + 2 * (rad1 haplotype * rad2 haplotype)

/-- **The witness.**  Train on the uniform law of the two loci and deploy in the witness target.
The population marginal score, the first tag, has zero accuracy in the target, and the GWAS score
trained on every finite cohort has positive accuracy, so the trained accuracy is not monotone in
the cohort size and exceeds the population value. -/
theorem trainingWitness_accuracy {size : ℕ} (hsize : 2 ≤ size) :
    correlationNumerator trainingWitnessTarget (linearScore trainingWitnessGenotype
          (marginalWeights (SamplingDesignLaw.uniform (Fin 4)) trainingWitnessGenotype
            trainingWitnessOutcome)) trainingWitnessOutcome
        / correlationDenominator trainingWitnessTarget (linearScore trainingWitnessGenotype
          (marginalWeights (SamplingDesignLaw.uniform (Fin 4)) trainingWitnessGenotype
            trainingWitnessOutcome)) trainingWitnessOutcome = 0
      ∧ 0 < trainedAccuracy (SamplingDesignLaw.uniform (Fin 4)) trainingWitnessTarget size
          trainingWitnessGenotype trainingWitnessOutcome := by
  have hsource : marginalWeights (SamplingDesignLaw.uniform (Fin 4)) trainingWitnessGenotype
      trainingWitnessOutcome = ![1, 0] := by
    funext marker
    fin_cases marker <;>
      simp [marginalWeights, FiniteReportLaw.covariance_eq_rawMoments,
        FiniteReportLaw.expectation, Fin.sum_univ_four, SamplingDesignLaw.uniform,
        trainingWitnessGenotype, trainingWitnessOutcome, rad1, rad2] <;> norm_num
  have htarget : marginalWeights trainingWitnessTarget trainingWitnessGenotype
      trainingWitnessOutcome = ![0, 1] := by
    funext marker
    fin_cases marker <;>
      simp [marginalWeights, FiniteReportLaw.covariance_eq_rawMoments,
        FiniteReportLaw.expectation, Fin.sum_univ_four, trainingWitnessTarget,
        trainingWitnessGenotype, trainingWitnessOutcome, rad1, rad2] <;> norm_num
  refine populationAccuracy_lt_trainedAccuracy _ _ hsize _ _ ?_ ?_ ?_ ?_
  · rw [hsource]
    simp [FiniteReportLaw.covariance_eq_rawMoments, FiniteReportLaw.expectation, linearScore,
      Fin.sum_univ_two, Fin.sum_univ_four, trainingWitnessTarget, trainingWitnessGenotype,
      trainingWitnessOutcome, rad1, rad2]
    norm_num
  · rw [htarget]
    simp [FiniteReportLaw.variance_eq_rawMoments, FiniteReportLaw.expectation, linearScore,
      Fin.sum_univ_two, Fin.sum_univ_four, SamplingDesignLaw.uniform, trainingWitnessGenotype,
      rad1, rad2]
    norm_num
  · simp [FiniteReportLaw.variance_eq_rawMoments, FiniteReportLaw.expectation,
      Fin.sum_univ_four, SamplingDesignLaw.uniform, trainingWitnessOutcome, rad1, rad2]
    norm_num
  · rw [hsource]
    simp [correlationDenominator, FiniteReportLaw.variance_eq_rawMoments,
      FiniteReportLaw.expectation, linearScore, Fin.sum_univ_two, Fin.sum_univ_four,
      trainingWitnessTarget, trainingWitnessGenotype, trainingWitnessOutcome, rad1, rad2]
    norm_num

end

end Descent.Portability.EndToEndGWASTrainingLaw
