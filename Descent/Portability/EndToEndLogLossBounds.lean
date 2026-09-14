/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndLogLossLaw

assert_below Descent.Decision Descent.Program

/-!
# Bounds on mutual information and pseudo-`R²`, and the independence case

`EndToEndLogLossLaw` defines the mutual information `I(S; Y) = H(Y) - H(Y | S)` of a score-outcome
report law and carries it, with McFadden's pseudo-`R²`, through every kernel with dual moments.
This module bounds both and characterizes when the information vanishes.

The divergence summand.  For masses `x, y ≥ 0` with `y > 0` wherever `x > 0`, the Kullback–Leibler
summand `x log (x / y) - x + y` (`divergenceTerm`) is `x (t - 1 - log t)` at `t = y / x`
(`divergenceTerm_eq_mul`).  So it is nonnegative (`divergenceTerm_nonneg`), and because
`log t < t - 1` off `t = 1` it vanishes exactly when `x = y` (`divergenceTerm_eq_zero_iff`).

Mutual information is a divergence.  The outcome marginal puts `p_b = Σ_s m_{s,b}` on each outcome
(`pushforward_snd_mass`), the group masses `q_s` sum to one (`sum_scoreGroupMass`), and a cell of
positive mass has positive marginals (`mass_pos_marginals`).  Splitting the logarithm of each cell
against the product of its marginals (`mass_mul_log_div_split`) writes the mutual information as
the sum over cells of the divergence summands of `m_{s,b}` against `q_s p_b`
(`mutualInformation_eq_sum_divergenceTerm`).

The bounds.  Hence `0 ≤ I(S; Y)` (`mutualInformation_nonneg`), and `I(S; Y) ≤ H(Y)` because the
conditional entropy is nonnegative (`mutualInformation_le_outcomeEntropy`), so pseudo-`R²` lies in
the unit interval (`pseudoRSquared_mem`).  The mutual information vanishes exactly when score and
outcome are independent, every cell mass being the product `q_s p_b` of its marginals
(`mutualInformation_eq_zero_iff`).

Through a kernel.  The mutual information of a deme's report law is a continuous observable
(`continuous_mutualInformation`).  Under every Markov kernel the expected mutual information lies
between `0` and the expected outcome entropy (`expectedMutualInformation_nonneg`,
`expectedMutualInformation_le_expectedEntropy`).  So pseudo-`R²` in ratio-of-expectations form lies
in the unit interval and its portability is nonnegative (`expectedPseudoRSquared_mem`,
`pseudoRSquaredPortability_nonneg`).  The expected mutual information vanishes exactly when the
kernel produces, almost surely, populations in which score and outcome are independent
(`expectedMutualInformation_eq_zero_iff`).  Along a history of epochs, splits and pulses and along a
rate history all of this holds (`logLossBounds_historyEventKernel`,
`logLossBounds_rateHistoryKernel`).  Along an event history the series of budget-`(k + 2)` dot
products for the mutual information is bracketed by `0` and the outcome entropy series
(`mutualInformationSeries_mem_historyEventKernel`).

Significance.  Pseudo-`R²` of a risk score is a genuine fraction of the outcome entropy under every
demographic history, and a history leaves a score uninformative about the outcome only by making
score and outcome independent in almost every population it produces.

Scope.  Score groups form a finite alphabet and outcomes are binary; one chromosome is sampled per
individual.  A ratio whose denominator vanishes reads zero, so the unit-interval bounds hold without
a positivity hypothesis and are informative where the expected outcome entropy is positive.

## Empirical status

None.  The bodies here are elementary inequalities of the logarithm, finite sums of masses and
integrals of nonnegative continuous observables against Markov kernels, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndLogLossBounds

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndLogLossLaw
open Filter
open scoped Matrix NNReal

noncomputable section

/-! ## The divergence summand -/

/-- The Kullback–Leibler summand `x log (x / y) - x + y` of a mass `x` against a reference mass
`y`. -/
def divergenceTerm (x y : ℝ) : ℝ :=
  x * Real.log (x / y) - x + y

/-- For positive masses the divergence summand is `x (t - 1 - log t)` at the ratio `t = y / x`. -/
theorem divergenceTerm_eq_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    divergenceTerm x y = x * (y / x - 1 - Real.log (y / x)) := by
  have hcancel : x * (y / x) = y := mul_div_cancel₀ y hx.ne'
  have hexpand : x * (y / x - 1 - Real.log (y / x))
      = x * (y / x) - x - x * (Real.log y - Real.log x) := by
    rw [Real.log_div hy.ne' hx.ne']
    ring
  rw [hexpand, hcancel, divergenceTerm, Real.log_div hx.ne' hy.ne']
  ring

/-- **The divergence summand is nonnegative** when the reference mass is positive wherever the
mass is. -/
theorem divergenceTerm_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hsupport : 0 < x → 0 < y) :
    0 ≤ divergenceTerm x y := by
  rcases hx.eq_or_lt with hzero | hpos
  · subst hzero
    simpa [divergenceTerm] using hy
  · have hlog := Real.log_le_sub_one_of_pos (div_pos (hsupport hpos) hpos)
    rw [divergenceTerm_eq_mul x y hpos (hsupport hpos)]
    exact mul_nonneg hpos.le (by linarith)

/-- **Equality case.**  The divergence summand vanishes exactly when the mass equals the reference
mass: off `t = 1` the inequality `log t ≤ t - 1` is strict. -/
theorem divergenceTerm_eq_zero_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsupport : 0 < x → 0 < y) : divergenceTerm x y = 0 ↔ x = y := by
  rcases hx.eq_or_lt with hzero | hpos
  · subst hzero
    have hvalue : divergenceTerm 0 y = y := by simp [divergenceTerm]
    rw [hvalue]
    exact eq_comm
  · have hy' := hsupport hpos
    rw [divergenceTerm_eq_mul x y hpos hy']
    constructor
    · intro hvanish
      by_contra hne
      have hratio : y / x ≠ 1 := fun hone ↦ hne ((div_eq_one_iff_eq hpos.ne').mp hone).symm
      have hstrict := Real.log_lt_sub_one_of_pos (div_pos hy' hpos) hratio
      have hproduct := mul_pos hpos (by linarith : 0 < y / x - 1 - Real.log (y / x))
      linarith
    · intro hequal
      subst hequal
      simp [div_self hpos.ne']

/-! ## Mutual information as a divergence -/

section ScoreOutcome

variable {Score : Type*} [Fintype Score]

/-- The outcome marginal of a score-outcome law puts `p_b = Σ_s m_{s,b}` on outcome `b`. -/
theorem pushforward_snd_mass (law : FiniteReportLaw (Score × Bool)) (outcome : Bool) :
    (law.pushforward Prod.snd).mass outcome = ∑ group, law.mass (group, outcome) := by
  rw [pushforwardMass_eq_expectation, FiniteReportLaw.expectation, Fintype.sum_prod_type_right,
    Fintype.sum_bool]
  cases outcome <;> simp

/-- The group masses of a score-outcome law sum to one. -/
theorem sum_scoreGroupMass (law : FiniteReportLaw (Score × Bool)) :
    ∑ group, scoreGroupMass law group = 1 := by
  calc ∑ group, scoreGroupMass law group
      = ∑ group, ∑ outcome : Bool, law.mass (group, outcome) :=
        Finset.sum_congr rfl fun group _ ↦ by rw [Fintype.sum_bool, scoreGroupMass, add_comm]
    _ = 1 := by rw [← Fintype.sum_prod_type, law.mass_sum]

/-- A cell of positive mass has positive group mass and positive outcome mass. -/
theorem mass_pos_marginals (law : FiniteReportLaw (Score × Bool)) (cell : Score × Bool)
    (hmass : 0 < law.mass cell) :
    0 < scoreGroupMass law cell.1 ∧ 0 < (law.pushforward Prod.snd).mass cell.2 := by
  rcases cell with ⟨group, outcome⟩
  refine ⟨lt_of_lt_of_le hmass ?_, ?_⟩
  · cases outcome
    · exact le_add_of_nonneg_right (law.mass_nonneg (group, true))
    · exact caseMass_le_scoreGroupMass law group
  · rw [pushforward_snd_mass]
    exact lt_of_lt_of_le hmass (Finset.single_le_sum (f := fun other ↦ law.mass (other, outcome))
      (fun other _ ↦ law.mass_nonneg (other, outcome)) (Finset.mem_univ group))

/-- The product of the marginals of a cell is nonnegative. -/
theorem productMarginals_nonneg (law : FiniteReportLaw (Score × Bool)) (cell : Score × Bool) :
    0 ≤ scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2 :=
  mul_nonneg (scoreGroupMass_nonneg law cell.1) ((law.pushforward Prod.snd).mass_nonneg _)

/-- The product of the marginals of a cell of positive mass is positive. -/
theorem productMarginals_pos (law : FiniteReportLaw (Score × Bool)) (cell : Score × Bool)
    (hmass : 0 < law.mass cell) :
    0 < scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2 :=
  mul_pos (mass_pos_marginals law cell hmass).1 (mass_pos_marginals law cell hmass).2

/-- The logarithm of a cell mass against the product of its marginals splits into three
logarithms; a cell of mass zero contributes nothing to any of them. -/
theorem mass_mul_log_div_split (m q p : ℝ) (hm : 0 ≤ m) (hsupport : 0 < m → 0 < q ∧ 0 < p) :
    m * Real.log (m / (q * p)) = m * Real.log m - m * Real.log q + m * -Real.log p := by
  rcases hm.eq_or_lt with hzero | hpos
  · subst hzero
    simp
  · obtain ⟨hq, hp⟩ := hsupport hpos
    rw [Real.log_div hpos.ne' (mul_pos hq hp).ne', Real.log_mul hq.ne' hp.ne']
    ring

/-- **Mutual information is a divergence.**  The mutual information of a score-outcome law is the
sum over cells of the divergence summands of the cell masses `m_{s,b}` against the products
`q_s p_b` of their marginals. -/
theorem mutualInformation_eq_sum_divergenceTerm (law : FiniteReportLaw (Score × Bool)) :
    mutualInformation law = ∑ cell, divergenceTerm (law.mass cell)
      (scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2) := by
  have hterm : ∀ cell : Score × Bool, divergenceTerm (law.mass cell)
      (scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2)
      = law.mass cell * Real.log (law.mass cell)
        - law.mass cell * Real.log (scoreGroupMass law cell.1)
        + law.mass cell * -Real.log ((law.pushforward Prod.snd).mass cell.2)
        - law.mass cell + scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2 :=
    fun cell ↦ by
      rw [divergenceTerm, mass_mul_log_div_split _ _ _ (law.mass_nonneg cell)
        (mass_pos_marginals law cell)]
  have hconditional : conditionalEntropy law
      = ∑ cell : Score × Bool, law.mass cell * Real.log (scoreGroupMass law cell.1)
        - ∑ cell : Score × Bool, law.mass cell * Real.log (law.mass cell) := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type, conditionalEntropy]
    refine Finset.sum_congr rfl fun group _ ↦ ?_
    rw [Fintype.sum_bool]
    simp only [Real.negMulLog, scoreGroupMass]
    ring
  have houtcome : reportEntropy (law.pushforward Prod.snd)
      = ∑ cell : Score × Bool,
        law.mass cell * -Real.log ((law.pushforward Prod.snd).mass cell.2) := by
    rw [reportEntropy, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun outcome _ ↦ ?_
    simp only [← Finset.sum_mul, ← pushforward_snd_mass]
    show -(law.pushforward Prod.snd).mass outcome
        * Real.log ((law.pushforward Prod.snd).mass outcome) = _
    ring
  have hproduct : ∑ cell : Score × Bool,
      scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, (law.pushforward Prod.snd).mass_sum, mul_one, sum_scoreGroupMass]
  rw [Finset.sum_congr rfl fun cell _ ↦ hterm cell]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [mutualInformation, hconditional, houtcome, hproduct, law.mass_sum]
  ring

/-- **Mutual information is nonnegative.** -/
theorem mutualInformation_nonneg (law : FiniteReportLaw (Score × Bool)) :
    0 ≤ mutualInformation law := by
  rw [mutualInformation_eq_sum_divergenceTerm]
  exact Finset.sum_nonneg fun cell _ ↦ divergenceTerm_nonneg _ _ (law.mass_nonneg cell)
    (productMarginals_nonneg law cell) (productMarginals_pos law cell)

/-- **Mutual information is at most the outcome entropy**, since the conditional entropy is
nonnegative. -/
theorem mutualInformation_le_outcomeEntropy (law : FiniteReportLaw (Score × Bool)) :
    mutualInformation law ≤ reportEntropy (law.pushforward Prod.snd) :=
  sub_le_self _ (conditionalEntropy_nonneg law)

/-- **Mutual information vanishes exactly at independence**: every cell mass is the product
`q_s p_b` of its group mass and its outcome mass. -/
theorem mutualInformation_eq_zero_iff (law : FiniteReportLaw (Score × Bool)) :
    mutualInformation law = 0
      ↔ ∀ cell : Score × Bool,
        law.mass cell = scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2 := by
  rw [mutualInformation_eq_sum_divergenceTerm, Finset.sum_eq_zero_iff_of_nonneg fun cell _ ↦
    divergenceTerm_nonneg _ _ (law.mass_nonneg cell) (productMarginals_nonneg law cell)
      (productMarginals_pos law cell)]
  exact ⟨fun hzero cell ↦ (divergenceTerm_eq_zero_iff _ _ (law.mass_nonneg cell)
      (productMarginals_nonneg law cell) (productMarginals_pos law cell)).mp
        (hzero cell (Finset.mem_univ cell)),
    fun hequal cell _ ↦ (divergenceTerm_eq_zero_iff _ _ (law.mass_nonneg cell)
      (productMarginals_nonneg law cell) (productMarginals_pos law cell)).mpr (hequal cell)⟩

/-- **Pseudo-`R²` of a report law lies in the unit interval**: `0 ≤ I(S; Y) / H(Y) ≤ 1`, the ratio
read as zero when `H(Y) = 0`. -/
theorem pseudoRSquared_mem (law : FiniteReportLaw (Score × Bool)) :
    0 ≤ mutualInformation law / reportEntropy (law.pushforward Prod.snd)
      ∧ mutualInformation law / reportEntropy (law.pushforward Prod.snd) ≤ 1 := by
  have hnonneg := mutualInformation_nonneg law
  have hle := mutualInformation_le_outcomeEntropy law
  exact ⟨div_nonneg hnonneg (hnonneg.trans hle), div_le_one_of_le₀ hle (hnonneg.trans hle)⟩

end ScoreOutcome

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score : Type*} [Fintype Score] [DecidableEq Score]

/-! ## The bounds through a kernel -/

/-- The mutual information of the report law of a deme is a continuous observable of the frequency
state. -/
theorem continuous_mutualInformation (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      mutualInformation ((stateLaw y deme).pushforward report) := by
  have hpoint : (fun y : FrequencyState Deme Locus Allele ↦
      mutualInformation ((stateLaw y deme).pushforward report))
      = fun y ↦ reportEntropy ((stateLaw y deme).pushforward fun hap ↦ (report hap).2)
        - conditionalEntropy ((stateLaw y deme).pushforward report) :=
    funext fun y ↦ by rw [mutualInformation, reportEntropy_pushforward_pushforward]
  rw [hpoint]
  exact (continuous_reportEntropy deme _).sub (continuous_conditionalEntropy deme report)

/-- **The expected mutual information is nonnegative** under every kernel. -/
theorem expectedMutualInformation_nonneg
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    0 ≤ expectedMutualInformation κ x0 deme report := by
  unfold expectedMutualInformation
  exact integral_nonneg fun y ↦ mutualInformation_nonneg _

/-- **The expected mutual information is at most the expected outcome entropy.** -/
theorem expectedMutualInformation_le_expectedEntropy
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedMutualInformation κ x0 deme report
      ≤ expectedEntropy κ x0 deme (fun hap ↦ (report hap).2) := by
  rw [expectedMutualInformation_eq_sub]
  unfold expectedConditionalEntropy
  exact sub_le_self _ (integral_nonneg fun y ↦ conditionalEntropy_nonneg _)

/-- **Expected pseudo-`R²` lies in the unit interval.**  The ratio of expectations reads zero when
the expected outcome entropy vanishes. -/
theorem expectedPseudoRSquared_mem
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    0 ≤ expectedPseudoRSquared κ x0 deme report ∧ expectedPseudoRSquared κ x0 deme report ≤ 1 := by
  have hnonneg := expectedMutualInformation_nonneg κ x0 deme report
  have hle := expectedMutualInformation_le_expectedEntropy κ x0 deme report
  unfold expectedPseudoRSquared
  exact ⟨div_nonneg hnonneg (hnonneg.trans hle), div_le_one_of_le₀ hle (hnonneg.trans hle)⟩

/-- Pseudo-`R²` portability is nonnegative. -/
theorem pseudoRSquaredPortability_nonneg
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    0 ≤ pseudoRSquaredPortability κ x0 source target report := by
  unfold pseudoRSquaredPortability
  exact div_nonneg (expectedPseudoRSquared_mem κ x0 target report).1
    (expectedPseudoRSquared_mem κ x0 source report).1

/-- **The expected mutual information vanishes exactly at almost sure independence.**  Under a
Markov kernel the expected mutual information of a deme's report law is zero exactly when, for
almost every population the kernel produces, every cell mass is the product of its marginals. -/
theorem expectedMutualInformation_eq_zero_iff
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    expectedMutualInformation κ x0 deme report = 0
      ↔ ∀ᵐ y ∂(κ x0), ∀ cell : Score × Bool,
        ((stateLaw y deme).pushforward report).mass cell
          = scoreGroupMass ((stateLaw y deme).pushforward report) cell.1
            * (((stateLaw y deme).pushforward report).pushforward Prod.snd).mass cell.2 := by
  have hint := integrable_continuousObservable κ x0 (continuous_mutualInformation deme report)
  have hpos : (0 : FrequencyState Deme Locus Allele → ℝ)
      ≤ fun y ↦ mutualInformation ((stateLaw y deme).pushforward report) := fun y ↦
    mutualInformation_nonneg _
  unfold expectedMutualInformation
  rw [integral_eq_zero_iff_of_nonneg hpos hint]
  exact eventually_congr (Eventually.of_forall fun y ↦ mutualInformation_eq_zero_iff _)

/-- **The bounds along a history of epochs, splits and pulses.**  The expected mutual information
lies between zero and the expected outcome entropy, pseudo-`R²` lies in the unit interval, and the
expected mutual information vanishes exactly when the history produces, almost surely, populations
in which score and outcome are independent. -/
theorem logLossBounds_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    0 ≤ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report
    ∧ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report
      ≤ expectedEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme (fun hap ↦ (report hap).2)
    ∧ 0 ≤ expectedPseudoRSquared (historyEventKernel ℓ₀ hap₀ events) x0 deme report
    ∧ expectedPseudoRSquared (historyEventKernel ℓ₀ hap₀ events) x0 deme report ≤ 1
    ∧ (expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report = 0
      ↔ ∀ᵐ y ∂(historyEventKernel ℓ₀ hap₀ events x0), ∀ cell : Score × Bool,
        ((stateLaw y deme).pushforward report).mass cell
          = scoreGroupMass ((stateLaw y deme).pushforward report) cell.1
            * (((stateLaw y deme).pushforward report).pushforward Prod.snd).mass cell.2) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact ⟨expectedMutualInformation_nonneg _ x0 deme report,
    expectedMutualInformation_le_expectedEntropy _ x0 deme report,
    (expectedPseudoRSquared_mem _ x0 deme report).1,
    (expectedPseudoRSquared_mem _ x0 deme report).2,
    expectedMutualInformation_eq_zero_iff _ x0 deme report⟩

/-- **The bounds along a time-varying rate history.** -/
theorem logLossBounds_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    0 ≤ expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
    ∧ expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
      ≤ expectedEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
        (fun hap ↦ (report hap).2)
    ∧ 0 ≤ expectedPseudoRSquared (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
    ∧ expectedPseudoRSquared (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report ≤ 1
    ∧ (expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
        = 0
      ↔ ∀ᵐ y ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0), ∀ cell : Score × Bool,
        ((stateLaw y deme).pushforward report).mass cell
          = scoreGroupMass ((stateLaw y deme).pushforward report) cell.1
            * (((stateLaw y deme).pushforward report).pushforward Prod.snd).mass cell.2) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact ⟨expectedMutualInformation_nonneg _ x0 deme report,
    expectedMutualInformation_le_expectedEntropy _ x0 deme report,
    (expectedPseudoRSquared_mem _ x0 deme report).1,
    (expectedPseudoRSquared_mem _ x0 deme report).2,
    expectedMutualInformation_eq_zero_iff _ x0 deme report⟩

/-- **The certified bracket in series form.**  Along a history of epochs, splits and pulses the
series of budget-`(k + 2)` dot products that computes the expected mutual information is
nonnegative and at most the series that computes the expected outcome entropy. -/
theorem mutualInformationSeries_mem_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    0 ≤ ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report order))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ order + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1)
    ∧ ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (mutualInformationTermPolynomial report order))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ order + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1)
      ≤ ∑' order : ℕ, (budgetCoefficients ℓ₀ (fun _ ↦ order + 2)
          (demePolynomial deme (entropyTermPolynomial (fun hap ↦ (report hap).2) order))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ order + 2) events
          *ᵥ budgetMomentFeature (fun _ ↦ order + 2) x0)) / ((order : ℝ) + 1) := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  rw [← (expectedConditionalEntropy_and_mutualInformation_historyEventKernel ℓ₀ hap₀ events x0
    deme report).2, ← expectedEntropy_historyEventKernel ℓ₀ hap₀ events x0 deme]
  exact ⟨expectedMutualInformation_nonneg _ x0 deme report,
    expectedMutualInformation_le_expectedEntropy _ x0 deme report⟩

end

end Descent.Portability.EndToEndLogLossBounds
