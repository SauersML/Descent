/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityRatioQueries
import Descent.Portability.JointMetricMomentDeterminacy

assert_below Descent.Decision Descent.Program

/-!
# The four portability queries under an arbitrary probability measure

NOTE 2 section 6.2 compares a source and a target squared correlation `M_s = N_s / D_s` and
`M_t = N_t / D_t` through the portability ratio `𝒫 = M_t / M_s = N_t D_s / (D_t N_s)` of
equation (27), defined on `D_s > 0`, `D_t > 0`, `N_s > 0`, and names four queries of the same
joint law: the mean of (27), the ratio of the means, the probability that `M_t > M_s`, and the
conditional probability that (27) exceeds one. `PortabilityRatioQueries` proves the gating
identity and separates the four queries on one finite report law. This module lifts them to an
arbitrary probability measure.

`portabilityDomain` is the definedness event of (27). `ratioMean` is the first query as an
extended nonnegative expectation, because the ratio is not bounded:
`portabilityRatio_small_source` exhibits admissible accumulators with ratio `n + 1`, and
`portabilityRatio_exceeds` concludes that the ratio exceeds every bound. `ratioOfMeans`,
`targetExceedsMass` and `ratioExceedsOneProbability` are the other three queries, and
`targetExceedsMass_eq_mul` shows that the third is the fourth scaled by the probability of
definedness.

The gating instruction of the note is `ratioMean_eq_tsum`: on the definedness event the ratio is
the sum of the positive geometric series of `gatedTerm k = N_t D_s (1 - D_t N_s)^k`, so the first
query is exactly the normalized sum of the expectations of those terms over the event. Without
the gate the same series is infinite wherever the source numerator vanishes and the gated
coefficient is positive (`tsum_gatedTerm_eq_top`), and `lintegral_ungated_eq_top` shows that its
expectation is infinite as soon as those reports have positive probability.

The four queries are queries of one joint law. `sourceTargetFamily` turns the source and target
accumulators into a two-metric family, `sourceTargetVector` is its metric vector `(M_s, M_t)` in
the unit square of `JointMetricMomentDeterminacy`, and `sourceTargetLaw` is the law of that vector
on the event where both denominators are positive. `portabilityQueries_eq_sourceTargetLaw`
expresses each of the four queries through that law alone, and
`portabilityQueries_eq_of_expansion_eq` concludes that two laws of the population with the same
positive ratio expansions (15) of every multi-index pair (25) of the family have the same four
queries.

Scope: the accumulators are measurable and satisfy `0 ≤ N ≤ D ≤ 1`. The observation that the
ratio of means is a query of the two marginal laws while the other three need the joint law is not
formalized here.

## Empirical status

None. The bodies here are measure theory: the four accumulators are supplied measurable
functions, and every statement is an identity or an inequality between integrals and measures
of functions of them, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMeasureQueries

open MeasureTheory ProbabilityTheory PositiveRatioExpansion JointRatioFailureMasks
open JointMetricMomentDeterminacy
open PortabilityRatioQueries (portabilityRatio)
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

section Gating

/-- **NOTE 2 (27), definedness.** The event on which the portability ratio is defined: both
denominators and the source numerator are positive. -/
def portabilityDomain (sourceNum sourceDen targetDen : Ω → ℝ) : Set Ω :=
  {ω | 0 < sourceDen ω ∧ 0 < targetDen ω ∧ 0 < sourceNum ω}

/-- The definedness event of a measurable report is measurable. -/
theorem measurableSet_portabilityDomain (sourceNum sourceDen targetDen : Ω → ℝ)
    (hsourceNum : Measurable sourceNum) (hsourceDen : Measurable sourceDen)
    (htargetDen : Measurable targetDen) :
    MeasurableSet (portabilityDomain sourceNum sourceDen targetDen) :=
  (measurableSet_lt measurable_const hsourceDen).inter
    ((measurableSet_lt measurable_const htargetDen).inter
      (measurableSet_lt measurable_const hsourceNum))

omit [MeasurableSpace Ω] in
/-- **NOTE 2 (27), the gating identity at one report.** Where the portability ratio is defined it
is the cross product `N_t D_s / (D_t N_s)`; this is
`PortabilityRatioQueries.portabilityRatio_eq_cross` read at a single report. -/
theorem portabilityRatio_eq_cross_at (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (ω : Ω)
    (hdomain : ω ∈ portabilityDomain sourceNum sourceDen targetDen) :
    portabilityRatio sourceNum sourceDen targetNum targetDen ω =
      targetNum ω * sourceDen ω / (targetDen ω * sourceNum ω) :=
  PortabilityRatioQueries.portabilityRatio_eq_cross (Ω := Unit) (fun _ ↦ sourceNum ω)
    (fun _ ↦ sourceDen ω) (fun _ ↦ targetNum ω) (fun _ ↦ targetDen ω) () hdomain.1
    hdomain.2.1 hdomain.2.2

omit [MeasurableSpace Ω] in
/-- On the definedness event the portability ratio exceeds one exactly when the target metric
exceeds the source metric; this is `PortabilityRatioQueries.one_lt_portabilityRatio_iff` read at
a single report. -/
theorem one_lt_portabilityRatio_iff_at (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (ω : Ω) (hdomain : ω ∈ portabilityDomain sourceNum sourceDen targetDen) :
    1 < portabilityRatio sourceNum sourceDen targetNum targetDen ω ↔
      sourceNum ω / sourceDen ω < targetNum ω / targetDen ω :=
  PortabilityRatioQueries.one_lt_portabilityRatio_iff (Ω := Unit) (fun _ ↦ sourceNum ω)
    (fun _ ↦ sourceDen ω) (fun _ ↦ targetNum ω) (fun _ ↦ targetDen ω) () hdomain.1
    hdomain.2.1 hdomain.2.2

/-- **NOTE 2 §6.2, the ratio is not bounded.** A report whose source numerator is `1 / (n + 1)`
and whose other accumulators are one keeps both metrics in the admissible range
`0 ≤ N ≤ D ≤ 1`, and its portability ratio is `n + 1`. -/
theorem portabilityRatio_small_source (n : ℕ) :
    0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 ∧
      portabilityRatio (fun _ : Unit ↦ 1 / ((n : ℝ) + 1)) (fun _ ↦ 1) (fun _ ↦ 1)
        (fun _ ↦ 1) () = n + 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one hpos]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · simp [portabilityRatio]

/-- **NOTE 2 §6.2.** Unlike each squared correlation, the portability ratio of admissible
reports exceeds every real bound. -/
theorem portabilityRatio_exceeds (bound : ℝ) :
    ∃ n : ℕ, bound < portabilityRatio (fun _ : Unit ↦ 1 / ((n : ℝ) + 1)) (fun _ ↦ 1)
      (fun _ ↦ 1) (fun _ ↦ 1) () := by
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  refine ⟨n, ?_⟩
  rw [(portabilityRatio_small_source n).2.2]
  linarith

end Gating

section Queries

/-- **NOTE 2 §6.2, first query.** The conditional mean of the portability ratio given its
definedness event, as an extended nonnegative expectation, which may be infinite. -/
def ratioMean (μ : Measure Ω) (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (portabilityRatio sourceNum sourceDen targetNum targetDen ω)
    ∂μ[|portabilityDomain sourceNum sourceDen targetDen]

/-- **NOTE 2 §6.2, second query.** The ratio of the conditional means of the target metric and
the source metric given the definedness event. -/
def ratioOfMeans (μ : Measure Ω) (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  (∫ ω, targetNum ω / targetDen ω ∂μ[|portabilityDomain sourceNum sourceDen targetDen]) /
    ∫ ω, sourceNum ω / sourceDen ω ∂μ[|portabilityDomain sourceNum sourceDen targetDen]

/-- **NOTE 2 §6.2, third query.** The probability that the portability ratio is defined and the
target metric exceeds the source metric, not conditioned on definedness. -/
def targetExceedsMass (μ : Measure Ω) (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  μ.real (portabilityDomain sourceNum sourceDen targetDen ∩
    {ω | sourceNum ω / sourceDen ω < targetNum ω / targetDen ω})

/-- **NOTE 2 §6.2, fourth query.** The conditional probability that the portability ratio
exceeds one given its definedness event. -/
def ratioExceedsOneProbability (μ : Measure Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  (μ[|portabilityDomain sourceNum sourceDen targetDen]).real
    {ω | 1 < portabilityRatio sourceNum sourceDen targetNum targetDen ω}

/-- The fourth query in closed form: the mass of the comparison event over the probability of
the definedness event, because on that event the ratio exceeding one and the target metric
exceeding the source metric are one event. -/
theorem ratioExceedsOneProbability_eq (μ : Measure Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (hsourceNum : Measurable sourceNum)
    (hsourceDen : Measurable sourceDen) (htargetDen : Measurable targetDen) :
    ratioExceedsOneProbability μ sourceNum sourceDen targetNum targetDen =
      (μ.real (portabilityDomain sourceNum sourceDen targetDen))⁻¹ *
        targetExceedsMass μ sourceNum sourceDen targetNum targetDen := by
  have hevent : portabilityDomain sourceNum sourceDen targetDen ∩
      {ω | 1 < portabilityRatio sourceNum sourceDen targetNum targetDen ω} =
      portabilityDomain sourceNum sourceDen targetDen ∩
        {ω | sourceNum ω / sourceDen ω < targetNum ω / targetDen ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact and_congr_right fun hdomain ↦
      one_lt_portabilityRatio_iff_at sourceNum sourceDen targetNum targetDen ω hdomain
  rw [ratioExceedsOneProbability, targetExceedsMass, measureReal_def, measureReal_def,
    measureReal_def, cond_apply (measurableSet_portabilityDomain sourceNum sourceDen targetDen
      hsourceNum hsourceDen htargetDen), hevent, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- **NOTE 2 §6.2.** The third query is the fourth scaled by the probability of definedness. -/
theorem targetExceedsMass_eq_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (hsourceNum : Measurable sourceNum)
    (hsourceDen : Measurable sourceDen) (htargetDen : Measurable targetDen) :
    targetExceedsMass μ sourceNum sourceDen targetNum targetDen =
      μ.real (portabilityDomain sourceNum sourceDen targetDen) *
        ratioExceedsOneProbability μ sourceNum sourceDen targetNum targetDen := by
  rw [ratioExceedsOneProbability_eq μ sourceNum sourceDen targetNum targetDen hsourceNum
    hsourceDen htargetDen]
  by_cases hzero : μ.real (portabilityDomain sourceNum sourceDen targetDen) = 0
  · have hle : targetExceedsMass μ sourceNum sourceDen targetNum targetDen ≤
        μ.real (portabilityDomain sourceNum sourceDen targetDen) :=
      measureReal_mono Set.inter_subset_left
    have hnonneg : 0 ≤ targetExceedsMass μ sourceNum sourceDen targetNum targetDen :=
      measureReal_nonneg
    rw [hzero, zero_mul]
    linarith
  · rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul]

/-- The second query without the normalizations, which cancel: the ratio of the integrals of the
target and source metrics over the definedness event. -/
theorem ratioOfMeans_eq_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) :
    ratioOfMeans μ sourceNum sourceDen targetNum targetDen =
      (∫ ω in portabilityDomain sourceNum sourceDen targetDen, targetNum ω / targetDen ω ∂μ) /
        ∫ ω in portabilityDomain sourceNum sourceDen targetDen, sourceNum ω / sourceDen ω ∂μ := by
  rw [ratioOfMeans, ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    smul_eq_mul, smul_eq_mul]
  by_cases hzero : μ (portabilityDomain sourceNum sourceDen targetDen) = 0
  · have hrestrict : μ.restrict (portabilityDomain sourceNum sourceDen targetDen) = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    simp [hrestrict]
  · have hscale : ((μ (portabilityDomain sourceNum sourceDen targetDen))⁻¹).toReal ≠ 0 := by
      rw [ENNReal.toReal_inv]
      exact inv_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hzero, measure_ne_top μ _⟩)
    rw [mul_div_mul_left _ _ hscale]

end Queries

section GatedExpansion

/-- The coefficient integrand `N_t D_s (1 - D_t N_s)^k` of the positive geometric expansion of
the portability ratio, read as an extended nonnegative number. -/
def gatedTerm (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (power : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (targetNum ω * sourceDen ω * (1 - targetDen ω * sourceNum ω) ^ power)

/-- Every gated coefficient integrand of a measurable report is measurable. -/
theorem measurable_gatedTerm (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNum : Measurable sourceNum) (hsourceDen : Measurable sourceDen)
    (htargetNum : Measurable targetNum) (htargetDen : Measurable targetDen) (power : ℕ) :
    Measurable (gatedTerm sourceNum sourceDen targetNum targetDen power) :=
  ((htargetNum.mul hsourceDen).mul
    ((measurable_const.sub (htargetDen.mul hsourceNum)).pow_const power)).ennreal_ofReal

omit [MeasurableSpace Ω] in
/-- **NOTE 2 §6.2, the gated expansion at a defined report.** Where the portability ratio is
defined and both metrics satisfy `0 ≤ N ≤ D ≤ 1`, the positive geometric series of the gated
coefficients sums to the ratio. -/
theorem tsum_gatedTerm (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (ω : Ω)
    (hdomain : ω ∈ portabilityDomain sourceNum sourceDen targetDen)
    (htargetNum : 0 ≤ targetNum ω) (hsourceLe : sourceNum ω ≤ sourceDen ω)
    (hsourceDen : sourceDen ω ≤ 1) (htargetDen : targetDen ω ≤ 1) :
    ∑' power, gatedTerm sourceNum sourceDen targetNum targetDen power ω =
      ENNReal.ofReal (portabilityRatio sourceNum sourceDen targetNum targetDen ω) := by
  obtain ⟨hsd, htd, hsn⟩ := hdomain
  have hsourceNumLe : sourceNum ω ≤ 1 := le_trans hsourceLe hsourceDen
  have hproduct := mul_le_mul htargetDen hsourceNumLe hsn.le zero_le_one
  have hdeficitNonneg : 0 ≤ 1 - targetDen ω * sourceNum ω := by linarith
  have hdeficitLt : 1 - targetDen ω * sourceNum ω < 1 := by linarith [mul_pos htd hsn]
  have hgeometric : Summable fun power : ℕ ↦ (1 - targetDen ω * sourceNum ω) ^ power :=
    summable_geometric_of_lt_one hdeficitNonneg hdeficitLt
  have hreal : ∑' power : ℕ,
      targetNum ω * sourceDen ω * (1 - targetDen ω * sourceNum ω) ^ power =
        portabilityRatio sourceNum sourceDen targetNum targetDen ω := by
    have hcomplement :
        (1 : ℝ) - (1 - targetDen ω * sourceNum ω) = targetDen ω * sourceNum ω := by
      ring
    rw [hgeometric.tsum_mul_left, tsum_geometric_of_lt_one hdeficitNonneg hdeficitLt,
      hcomplement, portabilityRatio_eq_cross_at sourceNum sourceDen targetNum targetDen ω
        ⟨hsd, htd, hsn⟩, div_eq_mul_inv]
  unfold gatedTerm
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun power ↦ mul_nonneg (mul_nonneg htargetNum hsd.le) (pow_nonneg hdeficitNonneg power))
    (hgeometric.mul_left _), hreal]

/-- **NOTE 2 §6.2, gate before expanding.** Over the definedness event the extended expectation
of the portability ratio is the sum of the expectations of the gated coefficient integrands, and
the first query is that sum normalized by the probability of the event. -/
theorem ratioMean_eq_tsum (μ : Measure Ω) (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNumMeasurable : Measurable sourceNum) (hsourceDenMeasurable : Measurable sourceDen)
    (htargetNumMeasurable : Measurable targetNum) (htargetDenMeasurable : Measurable targetDen)
    (htargetNum : ∀ ω, 0 ≤ targetNum ω) (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω)
    (hsourceDen : ∀ ω, sourceDen ω ≤ 1) (htargetDen : ∀ ω, targetDen ω ≤ 1) :
    ∫⁻ ω in portabilityDomain sourceNum sourceDen targetDen,
        ENNReal.ofReal (portabilityRatio sourceNum sourceDen targetNum targetDen ω) ∂μ =
      ∑' power, ∫⁻ ω in portabilityDomain sourceNum sourceDen targetDen,
        gatedTerm sourceNum sourceDen targetNum targetDen power ω ∂μ ∧
    ratioMean μ sourceNum sourceDen targetNum targetDen =
      (μ (portabilityDomain sourceNum sourceDen targetDen))⁻¹ *
        ∑' power, ∫⁻ ω in portabilityDomain sourceNum sourceDen targetDen,
          gatedTerm sourceNum sourceDen targetNum targetDen power ω ∂μ := by
  have hgated : ∫⁻ ω in portabilityDomain sourceNum sourceDen targetDen,
        ENNReal.ofReal (portabilityRatio sourceNum sourceDen targetNum targetDen ω) ∂μ =
      ∑' power, ∫⁻ ω in portabilityDomain sourceNum sourceDen targetDen,
        gatedTerm sourceNum sourceDen targetNum targetDen power ω ∂μ := by
    rw [← lintegral_tsum fun power ↦ (measurable_gatedTerm sourceNum sourceDen targetNum
      targetDen hsourceNumMeasurable hsourceDenMeasurable htargetNumMeasurable
      htargetDenMeasurable power).aemeasurable]
    refine lintegral_congr_ae ((ae_restrict_iff' (measurableSet_portabilityDomain sourceNum
      sourceDen targetDen hsourceNumMeasurable hsourceDenMeasurable htargetDenMeasurable)).mpr
        (ae_of_all μ fun ω hω ↦ ?_))
    exact (tsum_gatedTerm sourceNum sourceDen targetNum targetDen ω hω (htargetNum ω)
      (hsourceLe ω) (hsourceDen ω) (htargetDen ω)).symm
  refine ⟨hgated, ?_⟩
  rw [ratioMean, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, hgated]

omit [MeasurableSpace Ω] in
/-- **NOTE 2 §6.2, the ungated series at zero source accuracy.** Where the source numerator
vanishes but the gated coefficient `N_t D_s` is positive, every coefficient integrand is that
coefficient, so the ungated geometric series is infinite. -/
theorem tsum_gatedTerm_eq_top (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (ω : Ω)
    (hzero : sourceNum ω = 0) (hcoefficient : 0 < targetNum ω * sourceDen ω) :
    ∑' power, gatedTerm sourceNum sourceDen targetNum targetDen power ω = ∞ := by
  have hconstant : ∀ power : ℕ, gatedTerm sourceNum sourceDen targetNum targetDen power ω =
      ENNReal.ofReal (targetNum ω * sourceDen ω) := fun power ↦ by
    simp [gatedTerm, hzero]
  simp only [hconstant]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.mpr hcoefficient).ne'

/-- **NOTE 2 §6.2, why the definedness event must be gated.** If zero source accuracy with a
positive gated coefficient has positive probability, the ungated geometric series has infinite
expectation: it assigns infinity to those reports instead of marking them undefined. -/
theorem lintegral_ungated_eq_top (μ : Measure Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (hsourceNum : Measurable sourceNum)
    (hsourceDen : Measurable sourceDen) (htargetNum : Measurable targetNum)
    (hmass : μ {ω | sourceNum ω = 0 ∧ 0 < targetNum ω * sourceDen ω} ≠ 0) :
    ∫⁻ ω, ∑' power, gatedTerm sourceNum sourceDen targetNum targetDen power ω ∂μ = ∞ := by
  have hset : MeasurableSet {ω | sourceNum ω = 0 ∧ 0 < targetNum ω * sourceDen ω} :=
    (hsourceNum (measurableSet_singleton 0)).inter
      (measurableSet_lt measurable_const (htargetNum.mul hsourceDen))
  refine top_unique ?_
  calc ∞ = ∫⁻ ω, Set.indicator {ω | sourceNum ω = 0 ∧ 0 < targetNum ω * sourceDen ω}
        (fun _ ↦ ∞) ω ∂μ := by
        rw [lintegral_indicator_const hset, ENNReal.top_mul hmass]
    _ ≤ ∫⁻ ω, ∑' power, gatedTerm sourceNum sourceDen targetNum targetDen power ω ∂μ := by
        refine lintegral_mono fun ω ↦ ?_
        dsimp only
        by_cases hω : ω ∈ {ω | sourceNum ω = 0 ∧ 0 < targetNum ω * sourceDen ω}
        · rw [tsum_gatedTerm_eq_top sourceNum sourceDen targetNum targetDen ω hω.1 hω.2]
          exact le_top
        · simp only [Set.indicator_apply, hω, ↓reduceIte]
          exact zero_le _

end GatedExpansion

section JointLaw

/-- A source and a target functional as a two-metric family: index `0` is the source and
index `1` is the target. -/
def sourceTargetFamily (source target : Ω → ℝ) : Fin 2 → Ω → ℝ := ![source, target]

omit [MeasurableSpace Ω] in
/-- A pointwise relation between two source functionals and between two target functionals holds
between the two-metric families at every index. -/
theorem sourceTargetFamily_rel (r : ℝ → ℝ → Prop) (source target source' target' : Ω → ℝ)
    (hsource : ∀ ω, r (source ω) (source' ω)) (htarget : ∀ ω, r (target ω) (target' ω)) :
    ∀ index ω, r (sourceTargetFamily source target index ω)
      (sourceTargetFamily source' target' index ω) := by
  intro index ω
  fin_cases index
  · exact hsource ω
  · exact htarget ω

omit [MeasurableSpace Ω] in
/-- The two-metric family of nonnegative functionals is nonnegative. -/
theorem sourceTargetFamily_nonneg (source target : Ω → ℝ) (hsource : ∀ ω, 0 ≤ source ω)
    (htarget : ∀ ω, 0 ≤ target ω) :
    ∀ index ω, 0 ≤ sourceTargetFamily source target index ω :=
  sourceTargetFamily_rel (fun value _ ↦ 0 ≤ value) source target source target hsource htarget

omit [MeasurableSpace Ω] in
/-- Numerators dominated by their denominators give a dominated two-metric family. -/
theorem sourceTargetFamily_le (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    ∀ index ω, sourceTargetFamily sourceNum targetNum index ω ≤
      sourceTargetFamily sourceDen targetDen index ω :=
  sourceTargetFamily_rel (· ≤ ·) sourceNum targetNum sourceDen targetDen hsourceLe htargetLe

omit [MeasurableSpace Ω] in
/-- Denominators below one give a two-metric family below one. -/
theorem sourceTargetFamily_le_one (sourceDen targetDen : Ω → ℝ)
    (hsourceDen : ∀ ω, sourceDen ω ≤ 1) (htargetDen : ∀ ω, targetDen ω ≤ 1) :
    ∀ index ω, sourceTargetFamily sourceDen targetDen index ω ≤ 1 :=
  sourceTargetFamily_rel (fun value _ ↦ value ≤ 1) sourceDen targetDen sourceDen targetDen
    hsourceDen htargetDen

/-- Measurable source and target functionals give a measurable two-metric family. -/
theorem measurable_sourceTargetFamily (source target : Ω → ℝ) (hsource : Measurable source)
    (htarget : Measurable target) :
    ∀ index, Measurable (sourceTargetFamily source target index) := by
  intro index
  fin_cases index
  · exact hsource
  · exact htarget

omit [MeasurableSpace Ω] in
/-- The common defined event of the source/target denominators is the event where both are
positive. -/
theorem mem_definedDomain_sourceTargetFamily (sourceDen targetDen : Ω → ℝ) (ω : Ω) :
    ω ∈ definedDomain (sourceTargetFamily sourceDen targetDen) Finset.univ ↔
      0 < sourceDen ω ∧ 0 < targetDen ω := by
  constructor
  · intro hmem
    exact ⟨hmem 0 (Finset.mem_univ 0), hmem 1 (Finset.mem_univ 1)⟩
  · rintro ⟨hsource, htarget⟩ index _
    fin_cases index
    · exact hsource
    · exact htarget

/-- **NOTE 2 §6.2.** The metric vector `(M_s, M_t)` of a source/target report, each metric read
as zero off its own defined event, as a point of the unit square. -/
def sourceTargetVector (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    Ω → ↥(metricCube (Fin 2)) :=
  metricVector (sourceTargetFamily sourceNum targetNum) (sourceTargetFamily sourceDen targetDen)
    (sourceTargetFamily_nonneg sourceNum targetNum hsourceNum htargetNum)
    (sourceTargetFamily_le sourceNum sourceDen targetNum targetDen hsourceLe htargetLe)

/-- **NOTE 2 §6.2.** The joint law of the source and target metrics on the event where both
denominators are positive: the population restricted to that event, pushed forward by the
metric vector. -/
def sourceTargetLaw (μ : Measure Ω) (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    Measure ↥(metricCube (Fin 2)) :=
  (μ.restrict (definedDomain (sourceTargetFamily sourceDen targetDen) Finset.univ)).map
    (sourceTargetVector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
      htargetLe)

/-- The measurable source/target report has a measurable metric vector. -/
theorem measurable_sourceTargetVector (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNumMeasurable : Measurable sourceNum) (hsourceDenMeasurable : Measurable sourceDen)
    (htargetNumMeasurable : Measurable targetNum) (htargetDenMeasurable : Measurable targetDen)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    Measurable (sourceTargetVector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
      hsourceLe htargetLe) :=
  measurable_metricVector _ _
    (measurable_sourceTargetFamily sourceNum targetNum hsourceNumMeasurable htargetNumMeasurable)
    (measurable_sourceTargetFamily sourceDen targetDen hsourceDenMeasurable htargetDenMeasurable)
    _ _

/-- The unit-square event on which the source metric is positive. -/
def sourcePositiveCube : Set ↥(metricCube (Fin 2)) := {point | 0 < (point : Fin 2 → ℝ) 0}

/-- The unit-square event on which the source metric is positive and the target metric exceeds
it. -/
def targetExceedsCube : Set ↥(metricCube (Fin 2)) :=
  {point | 0 < (point : Fin 2 → ℝ) 0 ∧ (point : Fin 2 → ℝ) 0 < (point : Fin 2 → ℝ) 1}

omit [MeasurableSpace Ω] in
/-- The definedness event of the portability ratio is the preimage of the source-positive
event under the metric vector, within the event where both denominators are positive. -/
theorem portabilityDomain_eq_preimage (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    portabilityDomain sourceNum sourceDen targetDen =
      sourceTargetVector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
          htargetLe ⁻¹' sourcePositiveCube ∩
        definedDomain (sourceTargetFamily sourceDen targetDen) Finset.univ := by
  ext ω
  rw [Set.mem_inter_iff, mem_definedDomain_sourceTargetFamily]
  constructor
  · rintro ⟨hsd, htd, hsn⟩
    refine ⟨?_, hsd, htd⟩
    show 0 < ratioOnDefined sourceNum sourceDen ω
    rw [ratioOnDefined, if_pos hsd]
    exact div_pos hsn hsd
  · rintro ⟨hpositive, hsd, htd⟩
    have hvalue : 0 < ratioOnDefined sourceNum sourceDen ω := hpositive
    rw [ratioOnDefined, if_pos hsd] at hvalue
    exact ⟨hsd, htd, (div_pos_iff_of_pos_right hsd).mp hvalue⟩

omit [MeasurableSpace Ω] in
/-- The comparison event of the third query is the preimage of the target-exceeds event under
the metric vector, within the event where both denominators are positive. -/
theorem targetExceedsEvent_eq_preimage (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    portabilityDomain sourceNum sourceDen targetDen ∩
        {ω | sourceNum ω / sourceDen ω < targetNum ω / targetDen ω} =
      sourceTargetVector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
          htargetLe ⁻¹' targetExceedsCube ∩
        definedDomain (sourceTargetFamily sourceDen targetDen) Finset.univ := by
  ext ω
  rw [Set.mem_inter_iff, Set.mem_inter_iff, mem_definedDomain_sourceTargetFamily]
  constructor
  · rintro ⟨⟨hsd, htd, hsn⟩, hcompare⟩
    refine ⟨?_, hsd, htd⟩
    show 0 < ratioOnDefined sourceNum sourceDen ω ∧
      ratioOnDefined sourceNum sourceDen ω < ratioOnDefined targetNum targetDen ω
    rw [ratioOnDefined, ratioOnDefined, if_pos hsd, if_pos htd]
    exact ⟨div_pos hsn hsd, hcompare⟩
  · rintro ⟨hcube, hsd, htd⟩
    have hvalues : 0 < ratioOnDefined sourceNum sourceDen ω ∧
        ratioOnDefined sourceNum sourceDen ω < ratioOnDefined targetNum targetDen ω := hcube
    rw [ratioOnDefined, ratioOnDefined, if_pos hsd, if_pos htd] at hvalues
    exact ⟨⟨hsd, htd, (div_pos_iff_of_pos_right hsd).mp hvalues.1⟩, hvalues.2⟩

omit [MeasurableSpace Ω] in
/-- On the definedness event the portability ratio is the ratio of the two coordinates of the
metric vector. -/
theorem portabilityRatio_eq_vector (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω)
    (ω : Ω) (hdomain : ω ∈ portabilityDomain sourceNum sourceDen targetDen) :
    portabilityRatio sourceNum sourceDen targetNum targetDen ω =
      (sourceTargetVector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
          htargetLe ω : Fin 2 → ℝ) 1 /
        (sourceTargetVector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
          hsourceLe htargetLe ω : Fin 2 → ℝ) 0 := by
  obtain ⟨hsd, htd, _⟩ := hdomain
  show targetNum ω / targetDen ω / (sourceNum ω / sourceDen ω) =
    ratioOnDefined targetNum targetDen ω / ratioOnDefined sourceNum sourceDen ω
  rw [ratioOnDefined, ratioOnDefined, if_pos hsd, if_pos htd]

/-- **NOTE 2 §6.2, four queries of one joint law.** Each portability query is a functional of the
joint law of `(M_s, M_t)` on the event where both denominators are positive: the first is the
normalized extended mean of `x_t / x_s` over `x_s > 0`, the second the ratio of the integrals of
`x_t` and `x_s` over `x_s > 0`, the third the mass of `0 < x_s < x_t`, and the fourth that mass
over the mass of `x_s > 0`. -/
theorem portabilityQueries_eq_sourceTargetLaw (μ : Measure Ω) [IsFiniteMeasure μ]
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNumMeasurable : Measurable sourceNum) (hsourceDenMeasurable : Measurable sourceDen)
    (htargetNumMeasurable : Measurable targetNum) (htargetDenMeasurable : Measurable targetDen)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω) :
    ratioMean μ sourceNum sourceDen targetNum targetDen =
        (sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
          hsourceLe htargetLe sourcePositiveCube)⁻¹ *
          ∫⁻ point in sourcePositiveCube,
            ENNReal.ofReal ((point : Fin 2 → ℝ) 1 / (point : Fin 2 → ℝ) 0)
            ∂sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
              hsourceLe htargetLe ∧
      ratioOfMeans μ sourceNum sourceDen targetNum targetDen =
        (∫ point in sourcePositiveCube, (point : Fin 2 → ℝ) 1
            ∂sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
              hsourceLe htargetLe) /
          ∫ point in sourcePositiveCube, (point : Fin 2 → ℝ) 0
            ∂sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
              hsourceLe htargetLe ∧
      targetExceedsMass μ sourceNum sourceDen targetNum targetDen =
        (sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
          hsourceLe htargetLe).real targetExceedsCube ∧
      ratioExceedsOneProbability μ sourceNum sourceDen targetNum targetDen =
        ((sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
          hsourceLe htargetLe).real sourcePositiveCube)⁻¹ *
          (sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
            hsourceLe htargetLe).real targetExceedsCube := by
  have hvector := measurable_sourceTargetVector sourceNum sourceDen targetNum targetDen
    hsourceNumMeasurable hsourceDenMeasurable htargetNumMeasurable htargetDenMeasurable
    hsourceNum htargetNum hsourceLe htargetLe
  have hdomainSet := measurableSet_portabilityDomain sourceNum sourceDen targetDen
    hsourceNumMeasurable hsourceDenMeasurable htargetDenMeasurable
  have hcoordinateZero :
      Measurable fun point : ↥(metricCube (Fin 2)) ↦ (point : Fin 2 → ℝ) 0 :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have hcoordinateOne :
      Measurable fun point : ↥(metricCube (Fin 2)) ↦ (point : Fin 2 → ℝ) 1 :=
    (measurable_pi_apply 1).comp measurable_subtype_coe
  have hratioIntegrand : Measurable fun point : ↥(metricCube (Fin 2)) ↦
      ENNReal.ofReal ((point : Fin 2 → ℝ) 1 / (point : Fin 2 → ℝ) 0) :=
    (hcoordinateOne.div hcoordinateZero).ennreal_ofReal
  have hpositiveSet : MeasurableSet sourcePositiveCube :=
    measurableSet_lt measurable_const hcoordinateZero
  have hexceedsSet : MeasurableSet targetExceedsCube :=
    (measurableSet_lt measurable_const hcoordinateZero).inter
      (measurableSet_lt hcoordinateZero hcoordinateOne)
  have hmass : μ (portabilityDomain sourceNum sourceDen targetDen) =
      sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
        htargetLe sourcePositiveCube := by
    rw [sourceTargetLaw, Measure.map_apply hvector hpositiveSet,
      Measure.restrict_apply (hvector hpositiveSet),
      ← portabilityDomain_eq_preimage sourceNum sourceDen targetNum targetDen hsourceNum
        htargetNum hsourceLe htargetLe]
  have hexceeds : targetExceedsMass μ sourceNum sourceDen targetNum targetDen =
      (sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
        htargetLe).real targetExceedsCube := by
    rw [targetExceedsMass, measureReal_def, measureReal_def, sourceTargetLaw,
      Measure.map_apply hvector hexceedsSet, Measure.restrict_apply (hvector hexceedsSet),
      ← targetExceedsEvent_eq_preimage sourceNum sourceDen targetNum targetDen hsourceNum
        htargetNum hsourceLe htargetLe]
  refine ⟨?_, ?_, hexceeds, ?_⟩
  · rw [ratioMean, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, hmass]
    congr 1
    rw [sourceTargetLaw, setLIntegral_map hpositiveSet hratioIntegrand hvector,
      Measure.restrict_restrict (hvector hpositiveSet),
      ← portabilityDomain_eq_preimage sourceNum sourceDen targetNum targetDen hsourceNum
        htargetNum hsourceLe htargetLe]
    refine lintegral_congr_ae ((ae_restrict_iff' hdomainSet).mpr (ae_of_all μ fun ω hω ↦ ?_))
    dsimp only
    rw [portabilityRatio_eq_vector sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
      hsourceLe htargetLe ω hω]
  · rw [ratioOfMeans_eq_setIntegral, sourceTargetLaw,
      setIntegral_map hpositiveSet hcoordinateOne.aestronglyMeasurable hvector.aemeasurable,
      setIntegral_map hpositiveSet hcoordinateZero.aestronglyMeasurable hvector.aemeasurable,
      Measure.restrict_restrict (hvector hpositiveSet),
      ← portabilityDomain_eq_preimage sourceNum sourceDen targetNum targetDen hsourceNum
        htargetNum hsourceLe htargetLe]
    congr 1
    · refine integral_congr_ae ((ae_restrict_iff' hdomainSet).mpr (ae_of_all μ fun ω hω ↦ ?_))
      show targetNum ω / targetDen ω = ratioOnDefined targetNum targetDen ω
      rw [ratioOnDefined, if_pos hω.2.1]
    · refine integral_congr_ae ((ae_restrict_iff' hdomainSet).mpr (ae_of_all μ fun ω hω ↦ ?_))
      show sourceNum ω / sourceDen ω = ratioOnDefined sourceNum sourceDen ω
      rw [ratioOnDefined, if_pos hω.1]
  · rw [ratioExceedsOneProbability_eq μ sourceNum sourceDen targetNum targetDen
      hsourceNumMeasurable hsourceDenMeasurable htargetDenMeasurable, hexceeds, measureReal_def,
      hmass]
    rfl

/-- **NOTE 2 §6.2, the queries are replica readouts of the joint law.** Two laws of the
population under which the positive ratio expansions (15) of every multi-index pair (25) of the
source/target family agree give the same value to each of the four portability queries. -/
theorem portabilityQueries_eq_of_expansion_eq (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hsourceNumMeasurable : Measurable sourceNum) (hsourceDenMeasurable : Measurable sourceDen)
    (htargetNumMeasurable : Measurable targetNum) (htargetDenMeasurable : Measurable targetDen)
    (hsourceNum : ∀ ω, 0 ≤ sourceNum ω) (htargetNum : ∀ ω, 0 ≤ targetNum ω)
    (hsourceLe : ∀ ω, sourceNum ω ≤ sourceDen ω) (htargetLe : ∀ ω, targetNum ω ≤ targetDen ω)
    (hsourceDen : ∀ ω, sourceDen ω ≤ 1) (htargetDen : ∀ ω, targetDen ω ≤ 1)
    (hexpansion : ∀ order : Fin 2 → ℕ,
      ∑' power : ℕ, ∫ ω, multiIndexNumerator (sourceTargetFamily sourceNum targetNum)
          (sourceTargetFamily sourceDen targetDen) order ω *
          (1 - multiIndexDenominator (sourceTargetFamily sourceDen targetDen) order ω) ^ power
            ∂μ =
        ∑' power : ℕ, ∫ ω, multiIndexNumerator (sourceTargetFamily sourceNum targetNum)
          (sourceTargetFamily sourceDen targetDen) order ω *
          (1 - multiIndexDenominator (sourceTargetFamily sourceDen targetDen) order ω) ^ power
            ∂ν) :
    ratioMean μ sourceNum sourceDen targetNum targetDen =
        ratioMean ν sourceNum sourceDen targetNum targetDen ∧
      ratioOfMeans μ sourceNum sourceDen targetNum targetDen =
        ratioOfMeans ν sourceNum sourceDen targetNum targetDen ∧
      targetExceedsMass μ sourceNum sourceDen targetNum targetDen =
        targetExceedsMass ν sourceNum sourceDen targetNum targetDen ∧
      ratioExceedsOneProbability μ sourceNum sourceDen targetNum targetDen =
        ratioExceedsOneProbability ν sourceNum sourceDen targetNum targetDen := by
  have hlaw : sourceTargetLaw μ sourceNum sourceDen targetNum targetDen hsourceNum htargetNum
      hsourceLe htargetLe =
      sourceTargetLaw ν sourceNum sourceDen targetNum targetDen hsourceNum htargetNum hsourceLe
        htargetLe :=
    (jointMetricLaw_eq_of_expansion_eq μ ν (sourceTargetFamily sourceNum targetNum)
      (sourceTargetFamily sourceDen targetDen)
      (measurable_sourceTargetFamily sourceNum targetNum hsourceNumMeasurable
        htargetNumMeasurable)
      (measurable_sourceTargetFamily sourceDen targetDen hsourceDenMeasurable
        htargetDenMeasurable)
      (sourceTargetFamily_nonneg sourceNum targetNum hsourceNum htargetNum)
      (sourceTargetFamily_le sourceNum sourceDen targetNum targetDen hsourceLe htargetLe)
      (sourceTargetFamily_le_one sourceDen targetDen hsourceDen htargetDen) hexpansion).1
  obtain ⟨hmeanμ, hratioμ, hexceedsμ, hprobabilityμ⟩ := portabilityQueries_eq_sourceTargetLaw μ
    sourceNum sourceDen targetNum targetDen hsourceNumMeasurable hsourceDenMeasurable
    htargetNumMeasurable htargetDenMeasurable hsourceNum htargetNum hsourceLe htargetLe
  obtain ⟨hmeanν, hratioν, hexceedsν, hprobabilityν⟩ := portabilityQueries_eq_sourceTargetLaw ν
    sourceNum sourceDen targetNum targetDen hsourceNumMeasurable hsourceDenMeasurable
    htargetNumMeasurable htargetDenMeasurable hsourceNum htargetNum hsourceLe htargetLe
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmeanμ, hmeanν, hlaw]
  · rw [hratioμ, hratioν, hlaw]
  · rw [hexceedsμ, hexceedsν, hlaw]
  · rw [hprobabilityμ, hprobabilityν, hlaw]

end JointLaw

end

end Descent.Portability.PortabilityMeasureQueries
