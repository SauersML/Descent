/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndAscertainedLaw

assert_below Descent.Decision Descent.Program

/-!
# A founder event where ascertainment changes portability

`EndToEndAscertainedLaw` proves that ascertainment cancels along a deterministic kernel, so any
effect of ascertainment comes from the randomness of the terminal state.  This module exhibits an
explicit random terminal law where ascertained and expected portability differ, and a law where
the product rule for tags read on one shared draw fails.

The event.  A founder event in deme `source` draws a haplotype `g` with its frequency and replaces
a fraction `ε` of the deme by copies of `g` (`founderEventLaw`).  This is the resampling stage
`resamplingMove` of the corpus microscopic neutral kernel.  It moves only the source deme
(`stateLaw_resamplingMove_of_ne`) and mixes the source law with the point mass at `g`
(`stateLaw_resamplingMove_mass`, `expectation_resamplingMove_self`).  A polynomial observable
integrates to the frequency-weighted sum of its values after the event
(`integral_founderEventLaw`).

The witness.  At two distinct loci `ℓ` and `ℓ'`, with alleles `a ≠ b` at `ℓ` and `a' ≠ b'` at
`ℓ'`, every deme starts with the haplotype law giving `(a, a')` frequency `1/2` and `(a, b')` and
`(b, b')` frequency `1/4` (`founderWitnessLaw`, `founderWitnessState`).  One founder event at
fraction `1/2` runs in the source deme (`founderWitnessKernel`, `integral_founderWitnessKernel`).
The score is the indicator of `a` at `ℓ` and the outcome the indicator of `a'` at `ℓ'`
(`correlationNumerator_tagIndicators`, `correlationDenominator_tagIndicators`).  The panel is two
haplotypes from the source deme, and the tag passes when the panel is polymorphic, the window
`halfThreshold` of minor allele frequency `1/2`.  Its pass probability is `2 p (1 - p)`
(`expectation_windowWeight_halfThreshold`, `expectation_windowWeight_halfThreshold_mul`).

The numbers.  Expected portability is `9/11` (`expectedPortability_founderWitnessKernel`) and
ascertained portability is `93/127` (`ascertainedPortability_founderWitnessKernel`), so
ascertainment lowers portability here (`ascertainedPortability_founderWitnessKernel_lt`).  The
target deme does not move, and passing raises the ratio-of-expectations accuracy of the source
from `11/27` to `127/279` (`sourceAccuracies_founderWitnessKernel`).  The witness law has tag
covariance `1/8` (`covariance_founderWitnessLaw`), so on one shared draw the probability of
carrying both tag alleles is not the product of the tag frequencies
(`founderWitnessLaw_sharedDraw_ne_prod`).

Scope.  The founder event is not an epoch or a pulse of `historyEventKernel`, so the end-to-end
moment law is not applied to it here, and a witness along a neutral epoch stays open.  The theorems
hold for every two distinct demes, two distinct loci, two distinct alleles at each locus and every
background haplotype.

## Empirical status

None.  The bodies here are finite sums over stipulated finite laws, integrals against finite
combinations of point masses and rational arithmetic, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndAscertainedWitness

open MeasureTheory ProbabilityTheory PartialHaplotypeDualGenerator NeutralFellerGenerator
  PartialHaplotypeMicroscopicStages ReplicaMetricInstances EndToEndPortabilityLaw
  EndToEndAscertainedLaw

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Founder events -/

/-- The frequency state whose per-deme haplotype laws are `law`. -/
def stateOfLaws (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :
    FrequencyState Deme Locus Allele :=
  ⟨lawPoint law, fun coordinate ↦ (law coordinate.1).mass_nonneg coordinate.2,
    fun deme ↦ (law deme).mass_sum⟩

/-- The per-deme laws of `stateOfLaws law` are `law`. -/
theorem stateLaw_stateOfLaws (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (deme : Deme) : stateLaw (stateOfLaws law) deme = law deme :=
  FiniteReportLaw.ext fun _ ↦ rfl

/-- **The terminal law of a founder event** in deme `source`: a haplotype `g` is drawn from the
deme with its frequency, and a fraction `ε` of the deme is replaced by copies of `g`. -/
def founderEventLaw (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : FrequencyState Deme Locus Allele) : Measure (FrequencyState Deme Locus Allele) :=
  ∑ g, ENNReal.ofReal (x.1 (source, g)) • Measure.dirac (resamplingMove source g ε hε0 hε1 x)

/-- A polynomial observable integrates against the founder-event law to the frequency-weighted
sum of its values after the event. -/
theorem integral_founderEventLaw (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : FrequencyState Deme Locus Allele) (p : FrequencyPolynomial Deme Locus Allele)
    (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ∫ y, observable y ∂(founderEventLaw source ε hε0 hε1 x)
      = ∑ g, x.1 (source, g) * observable (resamplingMove source g ε hε0 hε1 x) := by
  obtain rfl : observable = fun y ↦ polynomialFunction p y :=
    funext fun y ↦ (hobservable y).symm
  have hmeasurable := (polynomialFunction p).continuous.stronglyMeasurable
  have hintegrable : ∀ g : FullHaplotype Locus Allele, Integrable (fun y ↦ polynomialFunction p y)
      (ENNReal.ofReal (x.1 (source, g)) • Measure.dirac (resamplingMove source g ε hε0 hε1 x)) :=
    fun g ↦ (integrable_dirac' hmeasurable (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [founderEventLaw, integral_finset_sum_measure fun g _ ↦ hintegrable g]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [integral_smul_measure, integral_dirac' _ _ hmeasurable,
    ENNReal.toReal_ofReal (x.2.1 (source, g)), smul_eq_mul]

/-- After a founder event in deme `source`, the haplotype law of `source` mixes the old law with
the point mass at the founder. -/
theorem stateLaw_resamplingMove_mass (source : Deme) (g : FullHaplotype Locus Allele) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele)
    (hap : FullHaplotype Locus Allele) :
    (stateLaw (resamplingMove source g ε hε0 hε1 x) source).mass hap
      = (1 - ε) * (stateLaw x source).mass hap + ε * (if hap = g then 1 else 0) := by
  have hdirection : resamplingDirection source g x.1 (source, hap)
      = (if hap = g then 1 else 0) - x.1 (source, hap) := if_pos rfl
  show x.1 (source, hap) + ε * resamplingDirection source g x.1 (source, hap)
    = (1 - ε) * x.1 (source, hap) + ε * (if hap = g then 1 else 0)
  rw [hdirection]
  ring

/-- A founder event in deme `source` leaves every other deme unchanged. -/
theorem stateLaw_resamplingMove_of_ne (source : Deme) (g : FullHaplotype Locus Allele) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele) {deme : Deme}
    (hdeme : deme ≠ source) :
    stateLaw (resamplingMove source g ε hε0 hε1 x) deme = stateLaw x deme := by
  refine FiniteReportLaw.ext fun hap ↦ ?_
  have hdirection : resamplingDirection source g x.1 (deme, hap) = 0 := if_neg hdeme
  show x.1 (deme, hap) + ε * resamplingDirection source g x.1 (deme, hap) = x.1 (deme, hap)
  rw [hdirection, mul_zero, add_zero]

/-- After a founder event in deme `source`, every expectation in `source` mixes the old
expectation with the value at the founder. -/
theorem expectation_resamplingMove_self (source : Deme) (g : FullHaplotype Locus Allele) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele)
    (f : FullHaplotype Locus Allele → ℝ) :
    (stateLaw (resamplingMove source g ε hε0 hε1 x) source).expectation f
      = (1 - ε) * (stateLaw x source).expectation f + ε * f g := by
  have hterm : ∀ hap, (stateLaw (resamplingMove source g ε hε0 hε1 x) source).mass hap * f hap
      = (1 - ε) * ((stateLaw x source).mass hap * f hap)
        + ε * (if hap = g then f hap else 0) := by
    intro hap
    rw [stateLaw_resamplingMove_mass]
    split_ifs <;> ring
  rw [FiniteReportLaw.expectation, FiniteReportLaw.expectation]
  simp only [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ g)]

/-! ## Allele indicators and the polymorphic window -/

/-- The correlation numerator of two allele indicators in the raw moments of the law. -/
theorem correlationNumerator_tagIndicators (law : FiniteReportLaw (FullHaplotype Locus Allele))
    (ℓ ℓ' : Locus) (a : Allele ℓ) (a' : Allele ℓ') :
    correlationNumerator law (tagIndicator ℓ a) (tagIndicator ℓ' a')
      = 16 * (law.expectation (fun hap ↦ tagIndicator ℓ a hap * tagIndicator ℓ' a' hap)
        - law.expectation (tagIndicator ℓ a) * law.expectation (tagIndicator ℓ' a')) ^ 2 := by
  rw [correlationNumerator, FiniteReportLaw.covariance_eq_rawMoments]

/-- The correlation denominator of two allele indicators in the raw moments of the law. -/
theorem correlationDenominator_tagIndicators
    (law : FiniteReportLaw (FullHaplotype Locus Allele)) (ℓ ℓ' : Locus) (a : Allele ℓ)
    (a' : Allele ℓ') :
    correlationDenominator law (tagIndicator ℓ a) (tagIndicator ℓ' a')
      = 16 * ((law.expectation (tagIndicator ℓ a) - law.expectation (tagIndicator ℓ a) ^ 2)
        * (law.expectation (tagIndicator ℓ' a') - law.expectation (tagIndicator ℓ' a') ^ 2)) := by
  have hsquare : ∀ (m : Locus) (c : Allele m) (hap : FullHaplotype Locus Allele),
      tagIndicator m c hap ^ 2 = tagIndicator m c hap := fun m c hap ↦ by
    unfold tagIndicator
    split_ifs <;> norm_num
  rw [correlationDenominator, FiniteReportLaw.variance_eq_rawMoments,
    FiniteReportLaw.variance_eq_rawMoments]
  simp only [hsquare]

/-- The rational window of minor allele frequency `1/2`: on two haplotypes it accepts exactly the
polymorphic panels. -/
def halfThreshold : PooledMAFThreshold where
  numerator := 1
  denominator := 2
  denominator_pos := by norm_num
  twice_numerator_le_denominator := by norm_num

/-- On two draws, the polymorphic window passes with probability `2 p (1 - p)`. -/
theorem expectation_windowWeight_halfThreshold
    (law : FiniteReportLaw (FullHaplotype Locus Allele)) (ℓ : Locus) (a : Allele ℓ) :
    (FiniteGeneticTransition.piLaw fun _ : Fin 2 ↦ law).expectation
        (windowWeight halfThreshold ℓ a)
      = 2 * law.expectation (tagIndicator ℓ a) * (1 - law.expectation (tagIndicator ℓ a)) := by
  rw [expectation_windowWeight_eq, Fintype.card_fin, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    if_neg (show ¬halfThreshold.Accepts 2 0 by decide),
    if_pos (show halfThreshold.Accepts 2 1 by decide),
    if_neg (show ¬halfThreshold.Accepts 2 2 by decide)]
  norm_num

/-- The polymorphic window weight times a constant averages to `2 p (1 - p)` times the
constant. -/
theorem expectation_windowWeight_halfThreshold_mul
    (law : FiniteReportLaw (FullHaplotype Locus Allele)) (ℓ : Locus) (a : Allele ℓ) (c : ℝ) :
    (FiniteGeneticTransition.piLaw fun _ : Fin 2 ↦ law).expectation
        (fun genotype ↦ windowWeight halfThreshold ℓ a genotype * c)
      = 2 * law.expectation (tagIndicator ℓ a) * (1 - law.expectation (tagIndicator ℓ a))
        * c := by
  rw [← expectation_windowWeight_halfThreshold]
  simp only [FiniteReportLaw.expectation, Finset.sum_mul, mul_assoc]

/-- The weights `1/2`, `1/4` and `1/4` of the three witness haplotypes. -/
def founderWitnessWeights : FiniteReportLaw (Fin 3) where
  mass j := if j = 0 then 1 / 2 else 1 / 4
  mass_nonneg j := by
    show (0 : ℝ) ≤ if j = 0 then 1 / 2 else 1 / 4
    split_ifs <;> norm_num
  mass_sum := by norm_num [Fin.sum_univ_three]

/-! ## The witness -/

section Witness

variable (ℓ ℓ' : Locus) (h0 : FullHaplotype Locus Allele)

/-- The haplotype carrying `u` at `ℓ`, `v` at `ℓ'` and the background `h₀` elsewhere. -/
def twoLocusHaplotype (u : Allele ℓ) (v : Allele ℓ') : FullHaplotype Locus Allele :=
  Function.update (Function.update h0 ℓ u) ℓ' v

/-- The indicator of `a` at `ℓ` reads one on a haplotype carrying `a` there. -/
theorem tagIndicator_left_self (hℓ : ℓ ≠ ℓ') (a : Allele ℓ) (v : Allele ℓ') :
    tagIndicator ℓ a (twoLocusHaplotype ℓ ℓ' h0 a v) = 1 := by
  simp [tagIndicator, twoLocusHaplotype, Function.update_of_ne hℓ]

/-- The indicator of `a` at `ℓ` reads zero on a haplotype carrying another allele there. -/
theorem tagIndicator_left_of_ne (hℓ : ℓ ≠ ℓ') {a b : Allele ℓ} (hba : b ≠ a) (v : Allele ℓ') :
    tagIndicator ℓ a (twoLocusHaplotype ℓ ℓ' h0 b v) = 0 := by
  simp [tagIndicator, twoLocusHaplotype, Function.update_of_ne hℓ, hba]

/-- The indicator of `a'` at `ℓ'` reads one on a haplotype carrying `a'` there. -/
theorem tagIndicator_right_self (u : Allele ℓ) (a' : Allele ℓ') :
    tagIndicator ℓ' a' (twoLocusHaplotype ℓ ℓ' h0 u a') = 1 := by
  simp [tagIndicator, twoLocusHaplotype]

/-- The indicator of `a'` at `ℓ'` reads zero on a haplotype carrying another allele there. -/
theorem tagIndicator_right_of_ne {a' b' : Allele ℓ'} (hba : b' ≠ a') (u : Allele ℓ) :
    tagIndicator ℓ' a' (twoLocusHaplotype ℓ ℓ' h0 u b') = 0 := by
  simp [tagIndicator, twoLocusHaplotype, hba]

/-- The three witness haplotypes `(a, a')`, `(a, b')` and `(b, b')`. -/
def founderWitnessHaplotype (a b : Allele ℓ) (a' b' : Allele ℓ') (j : Fin 3) :
    FullHaplotype Locus Allele :=
  if j = 0 then twoLocusHaplotype ℓ ℓ' h0 a a'
  else if j = 1 then twoLocusHaplotype ℓ ℓ' h0 a b'
  else twoLocusHaplotype ℓ ℓ' h0 b b'

/-- **The witness haplotype law**: `(a, a')` with frequency `1/2`, and `(a, b')` and `(b, b')`
with frequency `1/4`. -/
def founderWitnessLaw (a b : Allele ℓ) (a' b' : Allele ℓ') :
    FiniteReportLaw (FullHaplotype Locus Allele) :=
  founderWitnessWeights.pushforward (founderWitnessHaplotype ℓ ℓ' h0 a b a' b')

/-- Expectations under the witness law. -/
theorem expectation_founderWitnessLaw (a b : Allele ℓ) (a' b' : Allele ℓ')
    (f : FullHaplotype Locus Allele → ℝ) :
    (founderWitnessLaw ℓ ℓ' h0 a b a' b').expectation f
      = 1 / 2 * f (twoLocusHaplotype ℓ ℓ' h0 a a') + 1 / 4 * f (twoLocusHaplotype ℓ ℓ' h0 a b')
        + 1 / 4 * f (twoLocusHaplotype ℓ ℓ' h0 b b') := by
  rw [founderWitnessLaw, FiniteReportLaw.expectation_pushforward, FiniteReportLaw.expectation,
    Fin.sum_univ_three]
  simp [founderWitnessWeights, founderWitnessHaplotype]

/-- The witness state: every deme has the witness haplotype law. -/
def founderWitnessState (a b : Allele ℓ) (a' b' : Allele ℓ') :
    FrequencyState Deme Locus Allele :=
  stateOfLaws fun _ ↦ founderWitnessLaw ℓ ℓ' h0 a b a' b'

/-- **The witness history**: one founder event at fraction `1/2` in deme `source`, from the
witness state. -/
def founderWitnessKernel (source : Deme) (a b : Allele ℓ) (a' b' : Allele ℓ') :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele) :=
  Kernel.const _ (founderEventLaw source (1 / 2) (by norm_num) (by norm_num)
    (founderWitnessState ℓ ℓ' h0 a b a' b'))

/-- A polynomial observable integrates along the witness history to the weighted values at the
three founder outcomes. -/
theorem integral_founderWitnessKernel (source : Deme) (a b : Allele ℓ) (a' b' : Allele ℓ')
    (x : FrequencyState Deme Locus Allele) (p : FrequencyPolynomial Deme Locus Allele)
    (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ∫ y, observable y ∂(founderWitnessKernel ℓ ℓ' h0 source a b a' b' x)
      = 1 / 2 * observable (resamplingMove source (twoLocusHaplotype ℓ ℓ' h0 a a') (1 / 2)
          (by norm_num) (by norm_num) (founderWitnessState ℓ ℓ' h0 a b a' b'))
        + 1 / 4 * observable (resamplingMove source (twoLocusHaplotype ℓ ℓ' h0 a b') (1 / 2)
          (by norm_num) (by norm_num) (founderWitnessState ℓ ℓ' h0 a b a' b'))
        + 1 / 4 * observable (resamplingMove source (twoLocusHaplotype ℓ ℓ' h0 b b') (1 / 2)
          (by norm_num) (by norm_num) (founderWitnessState ℓ ℓ' h0 a b a' b')) := by
  rw [founderWitnessKernel, Kernel.const_apply,
    integral_founderEventLaw source (1 / 2) _ _ _ p observable hobservable]
  exact expectation_founderWitnessLaw ℓ ℓ' h0 a b a' b' fun g ↦
    observable (resamplingMove source g (1 / 2) (by norm_num) (by norm_num)
      (founderWitnessState ℓ ℓ' h0 a b a' b'))

/-- **Expected portability along the witness history is `9/11`.** -/
theorem expectedPortability_founderWitnessKernel (source target : Deme) (hst : source ≠ target)
    (hℓ : ℓ ≠ ℓ') (a b : Allele ℓ) (hab : a ≠ b) (a' b' : Allele ℓ') (hab' : a' ≠ b') :
    expectedPortability (founderWitnessKernel ℓ ℓ' h0 source a b a' b')
        (founderWitnessState ℓ ℓ' h0 a b a' b') source target (tagIndicator ℓ a)
        (tagIndicator ℓ' a')
      = 9 / 11 := by
  rw [expectedPortability,
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_numeratorPolynomial target (tagIndicator ℓ a) (tagIndicator ℓ' a')),
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_denominatorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a')),
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_denominatorPolynomial target (tagIndicator ℓ a) (tagIndicator ℓ' a')),
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_numeratorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a'))]
  simp only [stateLaw_resamplingMove_of_ne _ _ _ _ _ _ hst.symm, expectation_resamplingMove_self,
    founderWitnessState, stateLaw_stateOfLaws, correlationNumerator_tagIndicators,
    correlationDenominator_tagIndicators, expectation_founderWitnessLaw,
    tagIndicator_left_self ℓ ℓ' h0 hℓ, tagIndicator_left_of_ne ℓ ℓ' h0 hℓ hab.symm,
    tagIndicator_right_self ℓ ℓ' h0, tagIndicator_right_of_ne ℓ ℓ' h0 hab'.symm]
  norm_num

/-- **Ascertained portability along the witness history is `93/127`.** -/
theorem ascertainedPortability_founderWitnessKernel (source target : Deme)
    (hst : source ≠ target) (hℓ : ℓ ≠ ℓ') (a b : Allele ℓ) (hab : a ≠ b) (a' b' : Allele ℓ')
    (hab' : a' ≠ b') :
    ascertainedPortability (founderWitnessKernel ℓ ℓ' h0 source a b a' b')
        (founderWitnessState ℓ ℓ' h0 a b a' b') (fun _ : Fin 2 ↦ source)
        (windowWeight halfThreshold ℓ a) source target (tagIndicator ℓ a) (tagIndicator ℓ' a')
      = 93 / 127 := by
  rw [ascertainedPortability, ascertainedExpectation, ascertainedExpectation,
    ascertainedExpectation, ascertainedExpectation,
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_acceptance_mul (fun _ : Fin 2 ↦ source) (windowWeight halfThreshold ℓ a)
        _ _
        (polynomialFunction_numeratorPolynomial target (tagIndicator ℓ a) (tagIndicator ℓ' a'))),
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_acceptance_mul (fun _ : Fin 2 ↦ source) (windowWeight halfThreshold ℓ a)
        _ _
        (polynomialFunction_denominatorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a'))),
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_acceptance_mul (fun _ : Fin 2 ↦ source) (windowWeight halfThreshold ℓ a)
        _ _
        (polynomialFunction_denominatorPolynomial target (tagIndicator ℓ a) (tagIndicator ℓ' a'))),
    integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
      (polynomialFunction_acceptance_mul (fun _ : Fin 2 ↦ source) (windowWeight halfThreshold ℓ a)
        _ _
        (polynomialFunction_numeratorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a')))]
  simp only [expectation_windowWeight_halfThreshold_mul,
    stateLaw_resamplingMove_of_ne _ _ _ _ _ _ hst.symm, expectation_resamplingMove_self,
    founderWitnessState, stateLaw_stateOfLaws, correlationNumerator_tagIndicators,
    correlationDenominator_tagIndicators, expectation_founderWitnessLaw,
    tagIndicator_left_self ℓ ℓ' h0 hℓ, tagIndicator_left_of_ne ℓ ℓ' h0 hℓ hab.symm,
    tagIndicator_right_self ℓ ℓ' h0, tagIndicator_right_of_ne ℓ ℓ' h0 hab'.symm]
  norm_num

/-- **Ascertainment lowers portability along the witness history.** -/
theorem ascertainedPortability_founderWitnessKernel_lt (source target : Deme)
    (hst : source ≠ target) (hℓ : ℓ ≠ ℓ') (a b : Allele ℓ) (hab : a ≠ b) (a' b' : Allele ℓ')
    (hab' : a' ≠ b') :
    ascertainedPortability (founderWitnessKernel ℓ ℓ' h0 source a b a' b')
        (founderWitnessState ℓ ℓ' h0 a b a' b') (fun _ : Fin 2 ↦ source)
        (windowWeight halfThreshold ℓ a) source target (tagIndicator ℓ a) (tagIndicator ℓ' a')
      < expectedPortability (founderWitnessKernel ℓ ℓ' h0 source a b a' b')
        (founderWitnessState ℓ ℓ' h0 a b a' b') source target (tagIndicator ℓ a)
        (tagIndicator ℓ' a') := by
  rw [ascertainedPortability_founderWitnessKernel ℓ ℓ' h0 source target hst hℓ a b hab a' b' hab',
    expectedPortability_founderWitnessKernel ℓ ℓ' h0 source target hst hℓ a b hab a' b' hab']
  norm_num

/-- **Passing raises the source accuracy along the witness history**, from `11/27` to
`127/279`. -/
theorem sourceAccuracies_founderWitnessKernel (source : Deme) (hℓ : ℓ ≠ ℓ') (a b : Allele ℓ)
    (hab : a ≠ b) (a' b' : Allele ℓ') (hab' : a' ≠ b') :
    (∫ y, correlationNumerator (stateLaw y source) (tagIndicator ℓ a) (tagIndicator ℓ' a')
        ∂(founderWitnessKernel ℓ ℓ' h0 source a b a' b' (founderWitnessState ℓ ℓ' h0 a b a' b')))
      / ∫ y, correlationDenominator (stateLaw y source) (tagIndicator ℓ a) (tagIndicator ℓ' a')
        ∂(founderWitnessKernel ℓ ℓ' h0 source a b a' b' (founderWitnessState ℓ ℓ' h0 a b a' b'))
      = 11 / 27
    ∧ ascertainedExpectation (founderWitnessKernel ℓ ℓ' h0 source a b a' b')
        (founderWitnessState ℓ ℓ' h0 a b a' b') (fun _ : Fin 2 ↦ source)
        (windowWeight halfThreshold ℓ a)
        (fun y ↦ correlationNumerator (stateLaw y source) (tagIndicator ℓ a) (tagIndicator ℓ' a'))
      / ascertainedExpectation (founderWitnessKernel ℓ ℓ' h0 source a b a' b')
        (founderWitnessState ℓ ℓ' h0 a b a' b') (fun _ : Fin 2 ↦ source)
        (windowWeight halfThreshold ℓ a)
        (fun y ↦ correlationDenominator (stateLaw y source) (tagIndicator ℓ a)
          (tagIndicator ℓ' a'))
      = 127 / 279 := by
  constructor
  · rw [integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
        (polynomialFunction_numeratorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a')),
      integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
        (polynomialFunction_denominatorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a'))]
    simp only [expectation_resamplingMove_self, founderWitnessState, stateLaw_stateOfLaws,
      correlationNumerator_tagIndicators, correlationDenominator_tagIndicators,
      expectation_founderWitnessLaw, tagIndicator_left_self ℓ ℓ' h0 hℓ,
      tagIndicator_left_of_ne ℓ ℓ' h0 hℓ hab.symm, tagIndicator_right_self ℓ ℓ' h0,
      tagIndicator_right_of_ne ℓ ℓ' h0 hab'.symm]
    norm_num
  · rw [ascertainedExpectation, ascertainedExpectation,
      integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
        (polynomialFunction_acceptance_mul (fun _ : Fin 2 ↦ source)
          (windowWeight halfThreshold ℓ a) _ _
          (polynomialFunction_numeratorPolynomial source (tagIndicator ℓ a) (tagIndicator ℓ' a'))),
      integral_founderWitnessKernel ℓ ℓ' h0 source a b a' b' _ _ _
        (polynomialFunction_acceptance_mul (fun _ : Fin 2 ↦ source)
          (windowWeight halfThreshold ℓ a) _ _
          (polynomialFunction_denominatorPolynomial source (tagIndicator ℓ a)
            (tagIndicator ℓ' a')))]
    simp only [expectation_windowWeight_halfThreshold_mul, expectation_resamplingMove_self,
      founderWitnessState, stateLaw_stateOfLaws, correlationNumerator_tagIndicators,
      correlationDenominator_tagIndicators, expectation_founderWitnessLaw,
      tagIndicator_left_self ℓ ℓ' h0 hℓ, tagIndicator_left_of_ne ℓ ℓ' h0 hℓ hab.symm,
      tagIndicator_right_self ℓ ℓ' h0, tagIndicator_right_of_ne ℓ ℓ' h0 hab'.symm]
    norm_num

/-- The witness law puts covariance `1/8` between the two allele indicators. -/
theorem covariance_founderWitnessLaw (hℓ : ℓ ≠ ℓ') (a b : Allele ℓ) (hab : a ≠ b)
    (a' b' : Allele ℓ') (hab' : a' ≠ b') :
    (founderWitnessLaw ℓ ℓ' h0 a b a' b').covariance (tagIndicator ℓ a) (tagIndicator ℓ' a')
      = 1 / 8 := by
  rw [FiniteReportLaw.covariance_eq_rawMoments]
  simp only [expectation_founderWitnessLaw, tagIndicator_left_self ℓ ℓ' h0 hℓ,
    tagIndicator_left_of_ne ℓ ℓ' h0 hℓ hab.symm, tagIndicator_right_self ℓ ℓ' h0,
    tagIndicator_right_of_ne ℓ ℓ' h0 hab'.symm]
  norm_num

/-- **On a shared draw the tag pass probabilities do not multiply** under the witness law. -/
theorem founderWitnessLaw_sharedDraw_ne_prod (hℓ : ℓ ≠ ℓ') (a b : Allele ℓ) (hab : a ≠ b)
    (a' b' : Allele ℓ') (hab' : a' ≠ b') :
    (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ founderWitnessLaw ℓ ℓ' h0 a b a' b').expectation
        (fun genotype ↦ tagIndicator ℓ a (genotype 0) * tagIndicator ℓ' a' (genotype 0))
      ≠ (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦
            founderWitnessLaw ℓ ℓ' h0 a b a' b').expectation
          (fun genotype ↦ tagIndicator ℓ a (genotype 0))
        * (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦
            founderWitnessLaw ℓ ℓ' h0 a b a' b').expectation
          (fun genotype ↦ tagIndicator ℓ' a' (genotype 0)) := by
  rw [ne_eq, expectation_sharedDraw_eq_prod_iff,
    covariance_founderWitnessLaw ℓ ℓ' h0 hℓ a b hab a' b' hab']
  norm_num

end Witness

end

end Descent.Portability.EndToEndAscertainedWitness
