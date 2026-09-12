/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDiploidHistoryLaw
import Descent.Portability.EndToEndScoreLaw

assert_below Descent.Decision Descent.Program

/-!
# The end-to-end accuracy law of ascertained polygenic scores

The history-to-accuracy laws of `EndToEndPortabilityLaw` and its companions average over every
state of the frequency diffusion, so every variant counts, however rare.  A deployed score keeps
only the tags that pass an ascertainment rule in a source sample.  This module carries the law to
such scores.

Ascertainment as a polynomial.  A panel of `n` draws takes one haplotype per draw, independently,
from the terminal haplotype law of the draw's deme.  A rule with acceptance weight `w` on panel
genotypes passes with probability `Σ_g w(g) ∏_draw x_{deme draw}[g draw]`, a polynomial of total
degree at most `n` in the haplotype frequencies (`acceptancePolynomial`,
`polynomialFunction_acceptancePolynomial`, `totalDegree_acceptancePolynomial_le`).  Its monomials
are the moments of the corpus seed configurations (`momentPolynomial_seedConfiguration`).  At a
tag locus the count of the tag allele among `n` draws from one deme has the binomial count cells
`P(count = k) = C(n, k) p^k (1 - p)^(n - k)`, with `p` the tag allele frequency
(`expectation_tagAlleleCount_eq`).  Each cell is `C(n, k)` times the corpus product-Bernstein
weight of one deme (`countCell_eq_manyDemeBernsteinWeight`), and `p` is the moment of the
one-locus carrier `singleLocusType` (`expectation_tagIndicator_eq_marginal`).  For the rational
minor-allele-frequency window of the corpus, `PooledMAFThreshold.Accepts`, the pass probability is
the sum of the accepted cells (`windowWeight`, `expectation_windowWeight_eq`).  That sum is the
corpus Bernstein polynomial `windowBernsteinPolynomial`, of total degree at most `n` in `p`
(`totalDegree_windowBernsteinPolynomial_le`, `eval_windowBernsteinPolynomial`,
`polynomialFunction_acceptancePolynomial_windowWeight`).

Ascertained expectations.  `ascertainedExpectation` averages the acceptance weight times a state
observable over the terminal state and an independent panel.  If the observable is a frequency
polynomial `p` of total degree at most `m`, the integrand is the polynomial `A_w · p` of degree at
most `n + m`.  So along a history of epochs, splits and pulses, or a rate history, the ascertained
expectation is the coefficient vector of `A_w · p` dotted with the propagated moments
`U · H_{n+m}(x₀)` (`ascertainedExpectation_historyEventKernel`,
`ascertainedExpectation_rateHistoryKernel`).  The expected pass probability is a budget-`n` pairing
(`acceptanceProbability_historyEventKernel`, `integral_windowProbability_historyEventKernel`).  The
ascertained correlation numerator `E[w N]`, `N = 16 C_SY²`, and denominator `E[w D]`,
`D = 16 V_S V_Y`, are budget-`(n + 4)` pairings (`ascertainedNumerator_historyEventKernel`,
`ascertainedDenominator_historyEventKernel` and the rate-history forms).

The law.  Ascertained expected portability `(E[w N_t] E[w D_s]) / (E[w D_t] E[w N_s])`
(`ascertainedPortability`) is the rational function `ascertainedMomentPortability` of
`U · H_{n+4}(x₀)` (`ascertainedPortability_historyEventKernel`,
`ascertainedPortability_rateHistoryKernel`).  Two histories with equal propagated budget-`(n + 4)`
moments have equal ascertained portability (`ascertainedPortability_eq_of_moments_eq`).

Which query.  Weighting by `w` is conditioning on passing, and the normalizer `E[w]` cancels.
Whenever the pass probability is nonzero, the ascertained portability is the portability of the
expectations conditional on passing, `E[N_t | pass] E[D_s | pass] / (E[D_t | pass] E[N_s | pass])`
(`conditionalOnPassing`, `ascertainedPortability_eq_conditionalOnPassing`).  It is the
ratio-of-expectations query of NOTE2 §6.2 in the law conditioned on the panel passing.

The ascertainment effect.  Along a deterministic kernel, the empty history included, the weight
cancels, and the two portabilities agree whenever the pass probability is nonzero
(`ascertainedPortability_eq_expectedPortability_of_dirac`,
`ascertainedPortability_historyEventKernel_nil`).  The effect is the covariance of the pass
probability with the metrics across the random terminal states.  When the target numerator and
denominator are uncorrelated with passing, ascertained portability is below expected portability
exactly when passing raises the ratio-of-expectations accuracy of the source
(`ascertainedPortability_lt_expectedPortability_iff`).

Several tags.  A joint rule over several tags read on one shared panel is one acceptance weight
on that panel, so the law above applies at budget `n + 4`.  When each tag is ascertained on its
own independently drawn panel, the pass probability is the product of the per-panel probabilities
(`expectation_piLaw_prod`).  That product is the polynomial `∏_j A_{w_j}` of degree at most
`Σ_j n_j` (`polynomialFunction_prod_acceptancePolynomial`,
`totalDegree_prod_acceptancePolynomial_le`), and the ascertained expectations are
budget-`(Σ_j n_j + m)` pairings (`integral_independentPanels_historyEventKernel`).  On a shared
panel the product rule fails.  On one shared draw, the probability of carrying both tag alleles
minus the product of the two tag frequencies is the covariance of the tag indicators, their
linkage disequilibrium (`expectation_sharedDraw_sub_prod`, `expectation_sharedDraw_eq_prod_iff`).

Scope.  Panels are haploid and drawn from the terminal state, and a rule reads only its panel.
The score and the outcome are fixed functions of the haplotype, not estimated from the panel;
weights estimated from a training cohort are `EndToEndGWASTrainingLaw`.  The expected squared
correlation `E[N / D | pass]` and the joint form NOTE2 (27) under ascertainment are not stated.
The pooled-MAF evaluator of `EndToEndScoreLaw` runs on the one-locus moment system of a
`PipelineDemographicHistory`; identifying it with the partial-haplotype propagator used here is
open.  No closed form of `U · H_{n+4}(x₀)` along a neutral epoch is proved, so no epoch of
`historyEventKernel` is exhibited where the two portabilities differ.  P+T selection by association
p-values, the executable protocol coordinates and numerical evaluation at scale are not covered.

## Empirical status

None.  The bodies here are polynomial identities, finite sums over independent product laws and
integrals of polynomials against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndAscertainedLaw

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  PartialHaplotypePanelLikelihood ReplicaMetricInstances EndToEndPortabilityLaw
  EndToEndDiploidHistoryLaw
open scoped Matrix NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Sample : Type*} [Fintype Sample] [DecidableEq Sample]

/-! ## Panel rules and their acceptance polynomials -/

/-- The probability monomial `∏_draw x_{deme draw}[genotype draw]` of a panel genotype whose draws
come from the demes `panelDeme`. -/
def panelMonomial (panelDeme : Sample → Deme) (genotype : Sample → FullHaplotype Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  ∏ draw, X (panelDeme draw, genotype draw)

/-- The panel monomial is the moment polynomial of the corpus seed configuration of the panel
genotype. -/
theorem momentPolynomial_seedConfiguration (panelDeme : Sample → Deme)
    (genotype : Sample → FullHaplotype Locus Allele) (ℓ₀ : Locus) :
    momentPolynomial (seedConfiguration panelDeme genotype ℓ₀)
      = panelMonomial panelDeme genotype := by
  rw [momentPolynomial, seedConfiguration, Multiset.map_map, panelMonomial]
  exact Finset.prod_congr rfl fun draw _ ↦
    marginalPolynomial_fullType (panelDeme draw) (genotype draw) ℓ₀

/-- At a state, the panel monomial is the probability of the panel genotype when every draw comes
independently from the haplotype law of its deme. -/
theorem polynomialFunction_panelMonomial (panelDeme : Sample → Deme)
    (genotype : Sample → FullHaplotype Locus Allele) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (panelMonomial panelDeme genotype) y
      = (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme draw)).mass
          genotype := by
  rw [polynomialFunction_apply, panelMonomial, map_prod]
  show ∏ draw, eval y.1 (X (panelDeme draw, genotype draw))
      = ∏ draw, y.1 (panelDeme draw, genotype draw)
  simp only [eval_X]

/-- The panel monomial has total degree at most the panel size. -/
theorem totalDegree_panelMonomial_le (panelDeme : Sample → Deme)
    (genotype : Sample → FullHaplotype Locus Allele) :
    (panelMonomial panelDeme genotype).totalDegree ≤ Fintype.card Sample := by
  rw [panelMonomial]
  refine (totalDegree_finset_prod _ _).trans ?_
  simp [totalDegree_X]

/-- **The acceptance polynomial** `Σ_g w(g) ∏_draw x_{deme draw}[g draw]` of a panel rule with
acceptance weight `w`. -/
def acceptancePolynomial (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ genotype, C (weight genotype) * panelMonomial panelDeme genotype

/-- **The pass probability is a polynomial.**  At a state, the acceptance polynomial is the
expected acceptance weight of a panel drawn from the per-deme haplotype laws. -/
theorem polynomialFunction_acceptancePolynomial (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (acceptancePolynomial panelDeme weight) y
      = (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme draw)).expectation
          weight := by
  rw [polynomialFunction_apply, acceptancePolynomial, map_sum, FiniteReportLaw.expectation]
  refine Finset.sum_congr rfl fun genotype _ ↦ ?_
  rw [map_mul, eval_C, ← polynomialFunction_apply, polynomialFunction_panelMonomial, mul_comm]

/-- The acceptance polynomial has total degree at most the panel size. -/
theorem totalDegree_acceptancePolynomial_le (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) :
    (acceptancePolynomial panelDeme weight).totalDegree ≤ Fintype.card Sample := by
  rw [acceptancePolynomial]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun genotype _ ↦ ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact totalDegree_panelMonomial_le panelDeme genotype

/-! ## Count cells at a tag locus -/

/-- The indicator that a haplotype carries allele `a` at the tag locus `ℓ`. -/
def tagIndicator (ℓ : Locus) (a : Allele ℓ) (hap : FullHaplotype Locus Allele) : ℝ :=
  if hap ℓ = a then 1 else 0

/-- The number of draws of a panel genotype that carry allele `a` at the tag locus `ℓ`. -/
def tagAlleleCount (ℓ : Locus) (a : Allele ℓ) (genotype : Sample → FullHaplotype Locus Allele) :
    ℕ :=
  (Finset.univ.filter fun draw ↦ genotype draw ℓ = a).card

/-- The tag allele frequency of a deme is the moment of the one-locus carrier `singleLocusType`. -/
theorem expectation_tagIndicator_eq_marginal (y : FrequencyState Deme Locus Allele) (deme : Deme)
    (ℓ : Locus) (a : Allele ℓ) :
    (stateLaw y deme).expectation (tagIndicator ℓ a)
      = polynomialFunction (marginalPolynomial (singleLocusType deme ℓ a)) y := by
  have hagrees : ∀ hap : FullHaplotype Locus Allele,
      Agrees (singleLocusType deme ℓ a) hap ↔ hap ℓ = a := by
    intro hap
    constructor
    · intro h
      rcases h ℓ with h | h
      · simp [singleLocusType] at h
      · simpa [singleLocusType] using h.symm
    · intro h ℓ'
      rcases eq_or_ne ℓ' ℓ with rfl | hne
      · exact Or.inr (by simp [singleLocusType, h])
      · exact Or.inl (by simp [singleLocusType, Function.update_of_ne hne])
  have hmoment := eval_marginalPolynomial (stateLaw y) (singleLocusType deme ℓ a)
  rw [lawPoint_stateLaw] at hmoment
  rw [polynomialFunction_apply, hmoment, marginalFrequency, FiniteReportLaw.expectation,
    Finset.sum_filter]
  show ∑ hap, (stateLaw y deme).mass hap * tagIndicator ℓ a hap
      = ∑ hap, if Agrees (singleLocusType deme ℓ a) hap then (stateLaw y deme).mass hap else 0
  refine Finset.sum_congr rfl fun hap _ ↦ ?_
  by_cases hℓ : hap ℓ = a
  · rw [tagIndicator, if_pos hℓ, if_pos ((hagrees hap).mpr hℓ), mul_one]
  · rw [tagIndicator, if_neg hℓ, if_neg fun h ↦ hℓ ((hagrees hap).mp h), mul_zero]

/-- The factor of one draw in the indicator that the tag carriers of a panel are exactly `T`. -/
def carrierFactor (ℓ : Locus) (a : Allele ℓ) (T : Finset Sample) (draw : Sample)
    (hap : FullHaplotype Locus Allele) : ℝ :=
  if draw ∈ T then tagIndicator ℓ a hap else 1 - tagIndicator ℓ a hap

/-- The indicator that the draws carrying the tag allele are exactly `T` is the product of the
carrier factors of the draws. -/
theorem indicator_carriers_eq_prod (ℓ : Locus) (a : Allele ℓ)
    (genotype : Sample → FullHaplotype Locus Allele) (T : Finset Sample) :
    (if (Finset.univ.filter fun draw ↦ genotype draw ℓ = a) = T then (1 : ℝ) else 0)
      = ∏ draw, carrierFactor ℓ a T draw (genotype draw) := by
  have hmem : ∀ draw, draw ∈ Finset.univ.filter (fun draw ↦ genotype draw ℓ = a)
      ↔ genotype draw ℓ = a := fun draw ↦ by
    rw [Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ draw)
  by_cases hT : (Finset.univ.filter fun draw ↦ genotype draw ℓ = a) = T
  · rw [if_pos hT]
    have hmemT : ∀ draw, draw ∈ T ↔ genotype draw ℓ = a := by
      intro draw
      rw [← hT]
      exact hmem draw
    refine (Finset.prod_eq_one fun draw _ ↦ ?_).symm
    by_cases hg : genotype draw ℓ = a
    · rw [carrierFactor, if_pos ((hmemT draw).mpr hg), tagIndicator, if_pos hg]
    · rw [carrierFactor, if_neg fun h ↦ hg ((hmemT draw).mp h), tagIndicator, if_neg hg,
        sub_zero]
  · rw [if_neg hT]
    obtain ⟨draw, hdraw⟩ : ∃ draw, ¬(genotype draw ℓ = a ↔ draw ∈ T) := by
      by_contra hall
      push_neg at hall
      exact hT (Finset.ext fun draw ↦ (hmem draw).trans (hall draw))
    refine (Finset.prod_eq_zero (Finset.mem_univ draw) ?_).symm
    by_cases hg : genotype draw ℓ = a
    · have hout : draw ∉ T := fun h ↦ hdraw ⟨fun _ ↦ h, fun _ ↦ hg⟩
      rw [carrierFactor, if_neg hout, tagIndicator, if_pos hg, sub_self]
    · have hin : draw ∈ T := by
        by_contra h
        exact hdraw ⟨fun h' ↦ absurd h' hg, fun h' ↦ absurd h' h⟩
      rw [carrierFactor, if_pos hin, tagIndicator, if_neg hg]

/-- A carrier factor averages to the tag allele frequency on `T` and to its complement off `T`. -/
theorem expectation_carrierFactor (law : FiniteReportLaw (FullHaplotype Locus Allele))
    (ℓ : Locus) (a : Allele ℓ) (T : Finset Sample) (draw : Sample) :
    law.expectation (carrierFactor ℓ a T draw)
      = if draw ∈ T then law.expectation (tagIndicator ℓ a)
        else 1 - law.expectation (tagIndicator ℓ a) := by
  by_cases hT : draw ∈ T
  · rw [if_pos hT]
    exact congrArg law.expectation (funext fun hap ↦ if_pos hT)
  · rw [if_neg hT, ← FiniteReportLaw.expectation_complement]
    exact congrArg law.expectation (funext fun hap ↦ if_neg hT)

/-- The product over the draws of `p` on `T` and `1 - p` off `T`. -/
theorem prod_ite_mem_eq_pow (T : Finset Sample) (p : ℝ) :
    ∏ draw, (if draw ∈ T then p else 1 - p)
      = p ^ T.card * (1 - p) ^ (Fintype.card Sample - T.card) := by
  have hcard : (Finset.univ.filter fun draw ↦ ¬draw ∈ T).card = Fintype.card Sample - T.card := by
    rw [Finset.filter_not, Finset.card_sdiff, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.inter_univ, Finset.card_univ]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, hcard]

/-- **The count cell.**  Under independent draws from one haplotype law, the probability that
exactly `k` of the `n` draws carry allele `a` at the tag locus is `C(n, k) p^k (1 - p)^(n - k)`,
with `p` the tag allele frequency. -/
theorem expectation_tagAlleleCount_eq (law : FiniteReportLaw (FullHaplotype Locus Allele))
    (ℓ : Locus) (a : Allele ℓ) (k : ℕ) :
    (FiniteGeneticTransition.piLaw fun _ : Sample ↦ law).expectation
        (fun genotype ↦ if tagAlleleCount ℓ a genotype = k then 1 else 0)
      = ((Fintype.card Sample).choose k : ℝ) * law.expectation (tagIndicator ℓ a) ^ k
        * (1 - law.expectation (tagIndicator ℓ a)) ^ (Fintype.card Sample - k) := by
  have hpoint : ∀ genotype : Sample → FullHaplotype Locus Allele,
      (if tagAlleleCount ℓ a genotype = k then (1 : ℝ) else 0)
        = ∑ T ∈ Finset.powersetCard k Finset.univ,
            ∏ draw, carrierFactor ℓ a T draw (genotype draw) := by
    intro genotype
    calc (if tagAlleleCount ℓ a genotype = k then (1 : ℝ) else 0)
        = ∑ T ∈ Finset.powersetCard k Finset.univ,
            if (Finset.univ.filter fun draw ↦ genotype draw ℓ = a) = T then (1 : ℝ) else 0 := by
          rw [Finset.sum_ite_eq]
          by_cases hk : tagAlleleCount ℓ a genotype = k
          · rw [if_pos hk, if_pos (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hk⟩)]
          · rw [if_neg hk, if_neg fun (h : (Finset.univ.filter fun draw ↦ genotype draw ℓ = a)
              ∈ Finset.powersetCard k Finset.univ) ↦ hk (Finset.mem_powersetCard.mp h).2]
      _ = _ := Finset.sum_congr rfl fun T _ ↦ indicator_carriers_eq_prod ℓ a genotype T
  calc (FiniteGeneticTransition.piLaw fun _ : Sample ↦ law).expectation
        (fun genotype ↦ if tagAlleleCount ℓ a genotype = k then 1 else 0)
      = ∑ T ∈ Finset.powersetCard k Finset.univ,
          (FiniteGeneticTransition.piLaw fun _ : Sample ↦ law).expectation
            fun genotype ↦ ∏ draw, carrierFactor ℓ a T draw (genotype draw) := by
        simp only [hpoint, FiniteReportLaw.expectation, Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ T ∈ Finset.powersetCard k Finset.univ, ∏ draw : Sample,
          (if draw ∈ T then law.expectation (tagIndicator ℓ a)
            else 1 - law.expectation (tagIndicator ℓ a)) := by
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        rw [piLaw_eq_independentLaw,
          HWEInteractionLaw.expectation_independent_product (fun _ : Sample ↦ law)
            (carrierFactor ℓ a T)]
        exact Finset.prod_congr rfl fun draw _ ↦ expectation_carrierFactor law ℓ a T draw
    _ = ∑ T ∈ Finset.powersetCard k Finset.univ,
          law.expectation (tagIndicator ℓ a) ^ k
            * (1 - law.expectation (tagIndicator ℓ a)) ^ (Fintype.card Sample - k) := by
        refine Finset.sum_congr rfl fun T hT ↦ ?_
        rw [prod_ite_mem_eq_pow, (Finset.mem_powersetCard.mp hT).2]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The count cell is `C(n, k)` times the corpus product-Bernstein weight of one deme. -/
theorem countCell_eq_manyDemeBernsteinWeight (n k : ℕ) (p : ℝ) :
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
      = n.choose k * manyDemeBernsteinWeight (fun _ : Fin 1 ↦ p) (fun _ ↦ k) (fun _ ↦ n - k) := by
  simp only [manyDemeBernsteinWeight, Fin.prod_univ_one]
  ring

/-- The acceptance weight of a rational minor-allele-frequency window at a tag locus: one when the
panel's tag allele count passes the corpus threshold `PooledMAFThreshold.Accepts`. -/
def windowWeight (threshold : PooledMAFThreshold) (ℓ : Locus) (a : Allele ℓ)
    (genotype : Sample → FullHaplotype Locus Allele) : ℝ :=
  if threshold.Accepts (Fintype.card Sample) (tagAlleleCount ℓ a genotype) then 1 else 0

/-- **The window probability** is the sum of the accepted count cells. -/
theorem expectation_windowWeight_eq (law : FiniteReportLaw (FullHaplotype Locus Allele))
    (threshold : PooledMAFThreshold) (ℓ : Locus) (a : Allele ℓ) :
    (FiniteGeneticTransition.piLaw fun _ : Sample ↦ law).expectation (windowWeight threshold ℓ a)
      = ∑ k ∈ Finset.range (Fintype.card Sample + 1),
          if threshold.Accepts (Fintype.card Sample) k then
            ((Fintype.card Sample).choose k : ℝ) * law.expectation (tagIndicator ℓ a) ^ k
              * (1 - law.expectation (tagIndicator ℓ a)) ^ (Fintype.card Sample - k)
          else 0 := by
  have hpoint : ∀ genotype : Sample → FullHaplotype Locus Allele,
      windowWeight threshold ℓ a genotype
        = ∑ k ∈ Finset.range (Fintype.card Sample + 1),
            (if threshold.Accepts (Fintype.card Sample) k then (1 : ℝ) else 0)
              * (if tagAlleleCount ℓ a genotype = k then 1 else 0) := by
    intro genotype
    have hle : tagAlleleCount ℓ a genotype ≤ Fintype.card Sample := by
      rw [tagAlleleCount, ← Finset.card_univ]
      exact Finset.card_filter_le _ _
    have hrange : tagAlleleCount ℓ a genotype ∈ Finset.range (Fintype.card Sample + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
    rw [windowWeight, Finset.sum_eq_single_of_mem (tagAlleleCount ℓ a genotype) hrange,
      if_pos (rfl : tagAlleleCount ℓ a genotype = tagAlleleCount ℓ a genotype), mul_one]
    intro k _ hk
    rw [if_neg (Ne.symm hk), mul_zero]
  rw [funext hpoint, FiniteReportLaw.expectation]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hcell := expectation_tagAlleleCount_eq (Sample := Sample) law ℓ a k
  rw [FiniteReportLaw.expectation] at hcell
  by_cases hk : threshold.Accepts (Fintype.card Sample) k
  · simp only [if_pos hk, one_mul]
    exact hcell
  · simp only [if_neg hk, zero_mul, mul_zero, Finset.sum_const_zero]

/-- **The window as a polynomial in the tag allele frequency**: the accepted count cells, built
from the corpus product-Bernstein polynomial of one deme. -/
def windowBernsteinPolynomial (threshold : PooledMAFThreshold) (n : ℕ) :
    MvPolynomial (Fin 1) ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if threshold.Accepts n k then
      C (n.choose k : ℝ) * manyDemeBernsteinPolynomial (fun _ ↦ k) (fun _ ↦ n - k)
    else 0

/-- The window polynomial has total degree at most the panel size. -/
theorem totalDegree_windowBernsteinPolynomial_le (threshold : PooledMAFThreshold) (n : ℕ) :
    (windowBernsteinPolynomial threshold n).totalDegree ≤ n := by
  rw [windowBernsteinPolynomial]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k hk ↦ ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  split_ifs
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (manyDemeBernsteinPolynomial_totalDegree_le _ _).trans ?_
    simp only [Fin.sum_univ_one]
    omega
  · simp

/-- The window polynomial evaluates at `p` to the accepted sum of count cells. -/
theorem eval_windowBernsteinPolynomial (threshold : PooledMAFThreshold) (n : ℕ) (p : ℝ) :
    eval (fun _ ↦ p) (windowBernsteinPolynomial threshold n)
      = ∑ k ∈ Finset.range (n + 1),
          if threshold.Accepts n k then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0 := by
  rw [windowBernsteinPolynomial, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs
  · simp only [map_mul, eval_C, eval_manyDemeBernsteinPolynomial, manyDemeBernsteinWeight,
      Fin.prod_univ_one]
    ring
  · exact map_zero _

/-- **The window pass probability at a state** is the window polynomial at the source tag allele
frequency. -/
theorem polynomialFunction_acceptancePolynomial_windowWeight (source : Deme)
    (threshold : PooledMAFThreshold) (ℓ : Locus) (a : Allele ℓ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (acceptancePolynomial (fun _ : Sample ↦ source) (windowWeight threshold ℓ a))
        y
      = eval (fun _ ↦ (stateLaw y source).expectation (tagIndicator ℓ a))
          (windowBernsteinPolynomial threshold (Fintype.card Sample)) := by
  rw [polynomialFunction_acceptancePolynomial, eval_windowBernsteinPolynomial]
  exact expectation_windowWeight_eq (stateLaw y source) threshold ℓ a

/-! ## Ascertained expectations along a history -/

/-- **The ascertained expectation** of a state observable: the expectation, over the terminal state
under `κ x₀` and a panel drawn independently from it, of the panel's acceptance weight times the
observable. -/
def ascertainedExpectation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (observable : FrequencyState Deme Locus Allele → ℝ) : ℝ :=
  ∫ y, (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme draw)).expectation
      (fun genotype ↦ weight genotype * observable y) ∂(κ x0)

/-- At a state, the acceptance polynomial times a polynomial observable is the expected acceptance
weight times the observable. -/
theorem polynomialFunction_acceptance_mul (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (p : FrequencyPolynomial Deme Locus Allele) (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (acceptancePolynomial panelDeme weight * p) y
      = (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme draw)).expectation
          fun genotype ↦ weight genotype * observable y := by
  rw [polynomialFunction_apply, map_mul, ← polynomialFunction_apply, ← polynomialFunction_apply,
    polynomialFunction_acceptancePolynomial, hobservable]
  simp only [FiniteReportLaw.expectation, Finset.sum_mul, mul_assoc]

/-- **Ascertained expectations along a history.**  If a state observable equals a frequency
polynomial of total degree at most `m`, its ascertained expectation along a history of epochs,
splits and pulses is the coefficient vector of `A_w · p` dotted with the propagated
budget-`(n + m)` moments of `x₀`, with `n` the panel size. -/
theorem ascertainedExpectation_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) {m : ℕ}
    (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ m)
    (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ascertainedExpectation (historyEventKernel ℓ₀ hap₀ events) x0 panelDeme weight observable
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + m)
          (acceptancePolynomial panelDeme weight * p)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ Fintype.card Sample + m) events
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + m) x0) := by
  rw [ascertainedExpectation]
  exact integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    ((totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_acceptancePolynomial_le panelDeme weight) hp))
    _ (polynomialFunction_acceptance_mul panelDeme weight p observable hobservable)

/-- **Ascertained expectations along a rate history.** -/
theorem ascertainedExpectation_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ) {m : ℕ}
    (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ m)
    (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ascertainedExpectation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 panelDeme weight
        observable
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + m)
          (acceptancePolynomial panelDeme weight * p)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ Fintype.card Sample + m) T
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + m) x0) := by
  rw [ascertainedExpectation]
  exact integral_rateHistoryKernel_of_totalDegree_le hT hcontinuous ℓ₀ hap₀ x0 _
    ((totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_acceptancePolynomial_le panelDeme weight) hp))
    _ (polynomialFunction_acceptance_mul panelDeme weight p observable hobservable)

/-- **The expected pass probability along a history** is a budget-`n` pairing. -/
theorem acceptanceProbability_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) :
    ∫ y, (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme draw)).expectation weight
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample) (acceptancePolynomial panelDeme weight)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ Fintype.card Sample) events
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    (totalDegree_acceptancePolynomial_le panelDeme weight) _
    (polynomialFunction_acceptancePolynomial panelDeme weight)

/-- **The expected window pass probability along a history**: the window polynomial at the
source tag allele frequency, averaged along the history, is a budget-`n` pairing. -/
theorem integral_windowProbability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (source : Deme) (threshold : PooledMAFThreshold)
    (ℓ : Locus) (a : Allele ℓ) :
    ∫ y, eval (fun _ ↦ (stateLaw y source).expectation (tagIndicator ℓ a))
        (windowBernsteinPolynomial threshold (Fintype.card Sample))
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample)
          (acceptancePolynomial (fun _ : Sample ↦ source) (windowWeight threshold ℓ a))
        ⬝ᵥ (historyEventPropagator (fun _ ↦ Fintype.card Sample) events
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    (totalDegree_acceptancePolynomial_le _ _) _
    (polynomialFunction_acceptancePolynomial_windowWeight source threshold ℓ a)

/-- **The ascertained correlation numerator along a history** is a budget-`(n + 4)` pairing. -/
theorem ascertainedNumerator_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedExpectation (historyEventKernel ℓ₀ hap₀ events) x0 panelDeme weight
        (fun y ↦ correlationNumerator (stateLaw y deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
          (acceptancePolynomial panelDeme weight * numeratorPolynomial deme score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ Fintype.card Sample + 4) events
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x0) :=
  ascertainedExpectation_historyEventKernel ℓ₀ hap₀ events x0 panelDeme weight _
    (totalDegree_numeratorPolynomial_le deme score outcome) _
    (polynomialFunction_numeratorPolynomial deme score outcome)

/-- **The ascertained correlation denominator along a history** is a budget-`(n + 4)` pairing. -/
theorem ascertainedDenominator_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedExpectation (historyEventKernel ℓ₀ hap₀ events) x0 panelDeme weight
        (fun y ↦ correlationDenominator (stateLaw y deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
          (acceptancePolynomial panelDeme weight * denominatorPolynomial deme score outcome)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ Fintype.card Sample + 4) events
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x0) :=
  ascertainedExpectation_historyEventKernel ℓ₀ hap₀ events x0 panelDeme weight _
    (totalDegree_denominatorPolynomial_le deme score outcome) _
    (polynomialFunction_denominatorPolynomial deme score outcome)

/-- **The ascertained correlation numerator along a rate history.** -/
theorem ascertainedNumerator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedExpectation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 panelDeme weight
        (fun y ↦ correlationNumerator (stateLaw y deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
          (acceptancePolynomial panelDeme weight * numeratorPolynomial deme score outcome)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ Fintype.card Sample + 4) T
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x0) :=
  ascertainedExpectation_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ x0 panelDeme weight _
    (totalDegree_numeratorPolynomial_le deme score outcome) _
    (polynomialFunction_numeratorPolynomial deme score outcome)

/-- **The ascertained correlation denominator along a rate history.** -/
theorem ascertainedDenominator_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (deme : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedExpectation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 panelDeme weight
        (fun y ↦ correlationDenominator (stateLaw y deme) score outcome)
      = budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
          (acceptancePolynomial panelDeme weight * denominatorPolynomial deme score outcome)
        ⬝ᵥ (rateHistoryDualPropagator rates (fun _ ↦ Fintype.card Sample + 4) T
          *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x0) :=
  ascertainedExpectation_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ x0 panelDeme weight _
    (totalDegree_denominatorPolynomial_le deme score outcome) _
    (polynomialFunction_denominatorPolynomial deme score outcome)

/-- **Ascertained expected portability**: `(E[w N_t] E[w D_s]) / (E[w D_t] E[w N_s])`, with every
expectation over the terminal state under `κ x₀` and an independent panel with acceptance
weight `w`. -/
def ascertainedPortability
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) : ℝ :=
  (ascertainedExpectation κ x0 panelDeme weight
      (fun y ↦ correlationNumerator (stateLaw y target) score outcome)
    * ascertainedExpectation κ x0 panelDeme weight
      (fun y ↦ correlationDenominator (stateLaw y source) score outcome))
  / (ascertainedExpectation κ x0 panelDeme weight
      (fun y ↦ correlationDenominator (stateLaw y target) score outcome)
    * ascertainedExpectation κ x0 panelDeme weight
      (fun y ↦ correlationNumerator (stateLaw y source) score outcome))

/-- **The rational ascertained portability function** of a budget-`(n + 4)` moment vector, with
written-out coefficients. -/
def ascertainedMomentPortability (ℓ₀ : Locus) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (v : BudgetConfiguration Deme Locus Allele (fun _ ↦ Fintype.card Sample + 4) → ℝ) : ℝ :=
  ((budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
        (acceptancePolynomial panelDeme weight * numeratorPolynomial target score outcome) ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
        (acceptancePolynomial panelDeme weight * denominatorPolynomial source score outcome)
          ⬝ᵥ v))
    / ((budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
        (acceptancePolynomial panelDeme weight * denominatorPolynomial target score outcome)
          ⬝ᵥ v)
      * (budgetCoefficients ℓ₀ (fun _ ↦ Fintype.card Sample + 4)
        (acceptancePolynomial panelDeme weight * numeratorPolynomial source score outcome) ⬝ᵥ v))

/-- **The end-to-end law of ascertained portability along a history of epochs, splits and
pulses.**  Ascertained expected portability is the rational function
`ascertainedMomentPortability` of the chronological propagator applied to the budget-`(n + 4)`
configuration moments of the initial state. -/
theorem ascertainedPortability_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedPortability (historyEventKernel ℓ₀ hap₀ events) x0 panelDeme weight source target
        score outcome
      = ascertainedMomentPortability ℓ₀ panelDeme weight source target score outcome
          (historyEventPropagator (fun _ ↦ Fintype.card Sample + 4) events
            *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x0) := by
  rw [ascertainedPortability, ascertainedNumerator_historyEventKernel,
    ascertainedNumerator_historyEventKernel, ascertainedDenominator_historyEventKernel,
    ascertainedDenominator_historyEventKernel]
  rfl

/-- **The end-to-end law of ascertained portability along a rate history.** -/
theorem ascertainedPortability_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedPortability (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 panelDeme weight
        source target score outcome
      = ascertainedMomentPortability ℓ₀ panelDeme weight source target score outcome
          (rateHistoryDualPropagator rates (fun _ ↦ Fintype.card Sample + 4) T
            *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x0) := by
  rw [ascertainedPortability, ascertainedNumerator_rateHistoryKernel,
    ascertainedNumerator_rateHistoryKernel, ascertainedDenominator_rateHistoryKernel,
    ascertainedDenominator_rateHistoryKernel]
  rfl

/-- **Ascertained portability sees the history only through finitely many moments.**  Two
histories, from two initial states, whose propagated budget-`(n + 4)` configuration moments agree
have equal ascertained portability for every panel rule, score, outcome, source and target. -/
theorem ascertainedPortability_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ Fintype.card Sample + 4) first
        *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x₁
      = historyEventPropagator (fun _ ↦ Fintype.card Sample + 4) second
        *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample + 4) x₂)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedPortability (historyEventKernel ℓ₀ hap₀ first) x₁ panelDeme weight source target
        score outcome
      = ascertainedPortability (historyEventKernel ℓ₀ hap₀ second) x₂ panelDeme weight source
          target score outcome := by
  rw [ascertainedPortability_historyEventKernel, ascertainedPortability_historyEventKernel,
    hmoments]

/-! ## Which query: conditioning on passing -/

/-- The expectation of a state observable conditional on the panel passing: the ascertained
expectation divided by the pass probability. -/
def conditionalOnPassing
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (observable : FrequencyState Deme Locus Allele → ℝ) : ℝ :=
  ascertainedExpectation κ x0 panelDeme weight observable
    / ascertainedExpectation κ x0 panelDeme weight fun _ ↦ 1

/-- **Ascertained portability is portability conditional on passing.**  Whenever the pass
probability is nonzero, the normalizer cancels and ascertained portability is the ratio of the
expected numerators and denominators conditional on the panel passing. -/
theorem ascertainedPortability_eq_conditionalOnPassing
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hpass : ascertainedExpectation κ x0 panelDeme weight (fun _ ↦ 1) ≠ 0) :
    ascertainedPortability κ x0 panelDeme weight source target score outcome
      = (conditionalOnPassing κ x0 panelDeme weight
            (fun y ↦ correlationNumerator (stateLaw y target) score outcome)
          * conditionalOnPassing κ x0 panelDeme weight
            (fun y ↦ correlationDenominator (stateLaw y source) score outcome))
        / (conditionalOnPassing κ x0 panelDeme weight
            (fun y ↦ correlationDenominator (stateLaw y target) score outcome)
          * conditionalOnPassing κ x0 panelDeme weight
            (fun y ↦ correlationNumerator (stateLaw y source) score outcome)) := by
  have hcancel : ∀ a b c d P : ℝ, P ≠ 0 →
      a / P * (b / P) / (c / P * (d / P)) = a * b / (c * d) := by
    intro a b c d P hP
    rw [div_mul_div_comm, div_mul_div_comm, div_div_div_eq, mul_comm (P * P) (c * d),
      mul_div_mul_right _ _ (mul_ne_zero hP hP)]
  simp only [conditionalOnPassing]
  rw [hcancel _ _ _ _ _ hpass]
  rfl

/-! ## The ascertainment effect -/

/-- A state observable equal to a frequency polynomial integrates against a point mass to its
value there. -/
theorem integral_dirac_of_polynomial (y0 : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ∫ y, observable y ∂(Measure.dirac y0) = observable y0 := by
  obtain rfl : observable = fun y ↦ polynomialFunction p y :=
    funext fun y ↦ (hobservable y).symm
  exact integral_dirac' _ y0 (polynomialFunction p).continuous.stronglyMeasurable

/-- **Without drift, ascertainment cancels.**  Along a kernel that moves `x₀` deterministically,
ascertained portability equals expected portability whenever the pass probability at the terminal
state is nonzero. -/
theorem ascertainedPortability_eq_expectedPortability_of_dirac
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 y0 : FrequencyState Deme Locus Allele) (hκ : κ x0 = Measure.dirac y0)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (hpass : (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y0 (panelDeme draw)).expectation
      weight ≠ 0)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedPortability κ x0 panelDeme weight source target score outcome
      = expectedPortability κ x0 source target score outcome := by
  have hweighted : ∀ (p : FrequencyPolynomial Deme Locus Allele)
      (observable : FrequencyState Deme Locus Allele → ℝ),
      (∀ y, polynomialFunction p y = observable y) →
        ascertainedExpectation κ x0 panelDeme weight observable
          = (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y0 (panelDeme draw)).expectation
              weight * observable y0 := by
    intro p observable hobservable
    rw [ascertainedExpectation, hκ, integral_dirac_of_polynomial y0 _ _
      (polynomialFunction_acceptance_mul panelDeme weight p observable hobservable)]
    simp only [FiniteReportLaw.expectation, Finset.sum_mul, mul_assoc]
  have hplain : ∀ (p : FrequencyPolynomial Deme Locus Allele)
      (observable : FrequencyState Deme Locus Allele → ℝ),
      (∀ y, polynomialFunction p y = observable y) → ∫ y, observable y ∂(κ x0) = observable y0 := by
    intro p observable hobservable
    rw [hκ]
    exact integral_dirac_of_polynomial y0 p observable hobservable
  have hcancel : ∀ w a b c d : ℝ, w ≠ 0 →
      w * a * (w * b) / (w * c * (w * d)) = a * b / (c * d) := by
    intro w a b c d hw
    rw [mul_mul_mul_comm, mul_mul_mul_comm w c w d, mul_div_mul_left _ _ (mul_ne_zero hw hw)]
  rw [ascertainedPortability, expectedPortability,
    hweighted _ _ (polynomialFunction_numeratorPolynomial target score outcome),
    hweighted _ _ (polynomialFunction_denominatorPolynomial source score outcome),
    hweighted _ _ (polynomialFunction_denominatorPolynomial target score outcome),
    hweighted _ _ (polynomialFunction_numeratorPolynomial source score outcome),
    hplain _ _ (polynomialFunction_numeratorPolynomial target score outcome),
    hplain _ _ (polynomialFunction_denominatorPolynomial source score outcome),
    hplain _ _ (polynomialFunction_denominatorPolynomial target score outcome),
    hplain _ _ (polynomialFunction_numeratorPolynomial source score outcome),
    hcancel _ _ _ _ _ hpass]

/-- **The empty history does not see ascertainment.** -/
theorem ascertainedPortability_historyEventKernel_nil (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (panelDeme : Sample → Deme) (weight : (Sample → FullHaplotype Locus Allele) → ℝ)
    (hpass : (FiniteGeneticTransition.piLaw fun draw ↦ stateLaw x0 (panelDeme draw)).expectation
      weight ≠ 0)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) :
    ascertainedPortability (historyEventKernel ℓ₀ hap₀ []) x0 panelDeme weight source target score
        outcome
      = expectedPortability (historyEventKernel ℓ₀ hap₀ []) x0 source target score outcome :=
  ascertainedPortability_eq_expectedPortability_of_dirac _ x0 x0
    (by rw [historyEventKernel, Kernel.id_apply]) panelDeme weight hpass source target score
    outcome

/-- **Direction of the ascertainment effect.**  If the target numerator and denominator are
uncorrelated with passing and every expectation is positive, ascertained portability is below
expected portability exactly when passing raises the ratio-of-expectations accuracy of the
source. -/
theorem ascertainedPortability_lt_expectedPortability_iff
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : Sample → Deme)
    (weight : (Sample → FullHaplotype Locus Allele) → ℝ) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (htargetNumerator : ascertainedExpectation κ x0 panelDeme weight
        (fun y ↦ correlationNumerator (stateLaw y target) score outcome)
      = ascertainedExpectation κ x0 panelDeme weight (fun _ ↦ 1)
        * ∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ x0))
    (htargetDenominator : ascertainedExpectation κ x0 panelDeme weight
        (fun y ↦ correlationDenominator (stateLaw y target) score outcome)
      = ascertainedExpectation κ x0 panelDeme weight (fun _ ↦ 1)
        * ∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ x0))
    (hpass : 0 < ascertainedExpectation κ x0 panelDeme weight fun _ ↦ 1)
    (hNt : 0 < ∫ y, correlationNumerator (stateLaw y target) score outcome ∂(κ x0))
    (hDt : 0 < ∫ y, correlationDenominator (stateLaw y target) score outcome ∂(κ x0))
    (hNs : 0 < ∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ x0))
    (hDs : 0 < ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ x0))
    (hwNs : 0 < ascertainedExpectation κ x0 panelDeme weight
      fun y ↦ correlationNumerator (stateLaw y source) score outcome)
    (hwDs : 0 < ascertainedExpectation κ x0 panelDeme weight
      fun y ↦ correlationDenominator (stateLaw y source) score outcome) :
    ascertainedPortability κ x0 panelDeme weight source target score outcome
        < expectedPortability κ x0 source target score outcome
      ↔ (∫ y, correlationNumerator (stateLaw y source) score outcome ∂(κ x0))
          / ∫ y, correlationDenominator (stateLaw y source) score outcome ∂(κ x0)
        < ascertainedExpectation κ x0 panelDeme weight
            (fun y ↦ correlationNumerator (stateLaw y source) score outcome)
          / ascertainedExpectation κ x0 panelDeme weight
            (fun y ↦ correlationDenominator (stateLaw y source) score outcome) := by
  have key : ∀ W A B C D X Y : ℝ, 0 < W → 0 < A → 0 < B → 0 < C → 0 < D → 0 < X → 0 < Y →
      (W * A * Y / (W * B * X) < A * D / (B * C) ↔ C / D < X / Y) := by
    intro W A B C D X Y hW hA hB hC hD hX hY
    rw [div_lt_div_iff₀ (mul_pos (mul_pos hW hB) hX) (mul_pos hB hC), div_lt_div_iff₀ hD hY]
    have hWAB : 0 < W * A * B := mul_pos (mul_pos hW hA) hB
    have hleft : W * A * Y * (B * C) = W * A * B * (C * Y) := by ring
    have hright : A * D * (W * B * X) = W * A * B * (X * D) := by ring
    rw [hleft, hright]
    exact ⟨fun h ↦ lt_of_mul_lt_mul_left h hWAB.le, fun h ↦ mul_lt_mul_of_pos_left h hWAB⟩
  rw [ascertainedPortability, expectedPortability, htargetNumerator, htargetDenominator]
  exact key _ _ _ _ _ _ _ hpass hNt hDt hNs hDs hwNs hwDs

/-! ## Several tags -/

/-- **Independent panels multiply.**  Under the product of finitely many laws, the expectation of
a product of per-coordinate weights is the product of their expectations. -/
theorem expectation_piLaw_prod {Panel : Type*} [Fintype Panel] [DecidableEq Panel]
    {Genotype : Panel → Type*} [∀ j, Fintype (Genotype j)]
    (law : ∀ j, FiniteReportLaw (Genotype j)) (weight : ∀ j, Genotype j → ℝ) :
    (FiniteGeneticTransition.piLaw law).expectation (fun panels ↦ ∏ j, weight j (panels j))
      = ∏ j, (law j).expectation (weight j) := by
  simp only [FiniteReportLaw.expectation, FiniteGeneticTransition.piLaw_mass,
    ← Finset.prod_mul_distrib]
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun j ↦ (Finset.univ : Finset (Genotype j)))
      fun j genotype ↦ (law j).mass genotype * weight j genotype).symm

section IndependentPanels

variable {Panel : Type*} [Fintype Panel] [DecidableEq Panel] {Draw : Panel → Type*}
  [∀ j, Fintype (Draw j)] [∀ j, DecidableEq (Draw j)]

/-- **The pass probability of independent panels** is the product of their acceptance
polynomials. -/
theorem polynomialFunction_prod_acceptancePolynomial (panelDeme : ∀ j, Draw j → Deme)
    (weight : ∀ j, (Draw j → FullHaplotype Locus Allele) → ℝ)
    (y : FrequencyState Deme Locus Allele) :
    polynomialFunction (∏ j, acceptancePolynomial (panelDeme j) (weight j)) y
      = (FiniteGeneticTransition.piLaw fun j ↦
          FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme j draw)).expectation
          (fun panels ↦ ∏ j, weight j (panels j)) := by
  rw [expectation_piLaw_prod, polynomialFunction_apply, map_prod]
  exact Finset.prod_congr rfl fun j _ ↦
    polynomialFunction_acceptancePolynomial (panelDeme j) (weight j) y

/-- The product of the acceptance polynomials of independent panels has total degree at most the
total panel size. -/
theorem totalDegree_prod_acceptancePolynomial_le (panelDeme : ∀ j, Draw j → Deme)
    (weight : ∀ j, (Draw j → FullHaplotype Locus Allele) → ℝ) :
    (∏ j, acceptancePolynomial (panelDeme j) (weight j)).totalDegree
      ≤ ∑ j, Fintype.card (Draw j) :=
  (totalDegree_finset_prod _ _).trans
    (Finset.sum_le_sum fun j _ ↦ totalDegree_acceptancePolynomial_le (panelDeme j) (weight j))

/-- **Independently ascertained tags along a history.**  The expectation of the joint pass
probability of independent panels times a polynomial observable of degree at most `m` is the
coefficient vector of `(∏_j A_{w_j}) · p` dotted with the propagated budget-`(Σ_j n_j + m)`
moments. -/
theorem integral_independentPanels_historyEventKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (panelDeme : ∀ j, Draw j → Deme)
    (weight : ∀ j, (Draw j → FullHaplotype Locus Allele) → ℝ) {m : ℕ}
    (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ m)
    (observable : FrequencyState Deme Locus Allele → ℝ)
    (hobservable : ∀ y, polynomialFunction p y = observable y) :
    ∫ y, (FiniteGeneticTransition.piLaw fun j ↦
          FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (panelDeme j draw)).expectation
          (fun panels ↦ ∏ j, weight j (panels j)) * observable y
        ∂(historyEventKernel ℓ₀ hap₀ events x0)
      = budgetCoefficients ℓ₀ (fun _ ↦ (∑ j, Fintype.card (Draw j)) + m)
          ((∏ j, acceptancePolynomial (panelDeme j) (weight j)) * p)
        ⬝ᵥ (historyEventPropagator (fun _ ↦ (∑ j, Fintype.card (Draw j)) + m) events
          *ᵥ budgetMomentFeature (fun _ ↦ (∑ j, Fintype.card (Draw j)) + m) x0) :=
  integral_historyEventKernel_of_totalDegree_le ℓ₀ hap₀ events x0 _
    ((totalDegree_mul _ _).trans
      (Nat.add_le_add (totalDegree_prod_acceptancePolynomial_le panelDeme weight) hp)) _
    fun y ↦ by
      rw [polynomialFunction_apply, map_mul, ← polynomialFunction_apply,
        ← polynomialFunction_apply, polynomialFunction_prod_acceptancePolynomial, hobservable]

end IndependentPanels

/-- **A shared draw does not multiply.**  On one shared draw, the probability that the draw carries
both tag alleles minus the product of the two tag frequencies is the covariance of the tag
indicators, the linkage disequilibrium between the tags. -/
theorem expectation_sharedDraw_sub_prod (law : FiniteReportLaw (FullHaplotype Locus Allele))
    (ℓ ℓ' : Locus) (a : Allele ℓ) (a' : Allele ℓ') :
    (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
        (fun genotype ↦ tagIndicator ℓ a (genotype 0) * tagIndicator ℓ' a' (genotype 0))
      - (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
          (fun genotype ↦ tagIndicator ℓ a (genotype 0))
        * (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
          (fun genotype ↦ tagIndicator ℓ' a' (genotype 0))
      = law.covariance (tagIndicator ℓ a) (tagIndicator ℓ' a') := by
  have hcoordinate : ∀ f : FullHaplotype Locus Allele → ℝ,
      (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
          (fun genotype ↦ f (genotype 0))
        = law.expectation f := fun f ↦ by
    rw [piLaw_eq_independentLaw]
    exact FiniteIndependentMoments.coordinate_expectation (fun _ : Fin 1 ↦ law) 0 f
  rw [hcoordinate (fun hap ↦ tagIndicator ℓ a hap * tagIndicator ℓ' a' hap),
    hcoordinate (tagIndicator ℓ a), hcoordinate (tagIndicator ℓ' a'),
    FiniteReportLaw.covariance_eq_rawMoments]

/-- **The product rule holds on a shared draw exactly when the tags are uncorrelated.** -/
theorem expectation_sharedDraw_eq_prod_iff (law : FiniteReportLaw (FullHaplotype Locus Allele))
    (ℓ ℓ' : Locus) (a : Allele ℓ) (a' : Allele ℓ') :
    (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
        (fun genotype ↦ tagIndicator ℓ a (genotype 0) * tagIndicator ℓ' a' (genotype 0))
      = (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
          (fun genotype ↦ tagIndicator ℓ a (genotype 0))
        * (FiniteGeneticTransition.piLaw fun _ : Fin 1 ↦ law).expectation
          (fun genotype ↦ tagIndicator ℓ' a' (genotype 0))
      ↔ law.covariance (tagIndicator ℓ a) (tagIndicator ℓ' a') = 0 := by
  rw [← expectation_sharedDraw_sub_prod, sub_eq_zero]

end

end Descent.Portability.EndToEndAscertainedLaw
