/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaDomainCertificate
import Descent.Portability.FiniteDiscreteMeasure
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

assert_below Descent.Decision Descent.Program

/-!
# The replica-domain certificate over an arbitrary probability measure

NOTE 2 section 5.2 certifies the conditional expectation `E[M | D > 0]` of a bounded ratio
metric `M = N / D` from finitely many replica coefficients. `ReplicaDomainCertificate` proves
the certificate when the population is a finite report law. This module proves it over an
arbitrary probability measure `μ` on a measurable space, which is the setting of the note:
the conditional population law is a random object whose law need not be finitely supported.

`retainedNumerator` and `retainedMass` are `L_K` and `H_K` of NOTE 2 equation (16): the
first `K` expansion coefficients `∫ N (1 - D)^k` and the total mass `∫ 1 - (1 - D)^K` of the
subprobability weight `w_K`. `unresolvedNumerator` is the discarded numerator `δ_n`, the
metric damped by `(1 - D)^K`, and `unresolvedMass` is the discarded definedness mass
`δ_d = E[1_E (1 - D)^K]` that a tolerance must dominate in equation (17).
`integral_ratioOnDefined_partition` and `definedProbability_partition` show that the retained
and unresolved parts reconstitute `E[1_E M]` and `P(E)` exactly. `coupled_residuals` is
`0 ≤ δ_n ≤ δ_d ≤ min τ_K (1 - H_K)`. `measure_replica_certificate` is Theorem 4, equation
(18), with the conditional expectation read in Mathlib's conditional measure `μ[|E]`; its
proof is `SublawReportCertificate.ratio_bounds` with value interval zero to one.
`measure_certificate_width` is the exact width `τ_K / (H_K + τ_K)` and
`replica_certificate_min_tolerance` replaces `τ_K` by `min τ_K (1 - H_K)`.

Two statements make the convergence remark at the end of section 5.2 precise.
`tendsto_unresolvedMass` proves by dominated convergence that `δ_d → 0` for every model, so a
tolerance sequence tending to zero always exists, and `certificate_endpoints_tendsto` proves
that whenever a dominating tolerance sequence tends to zero and `P(E) > 0`, both endpoints of
the certificate converge to `E[M | D > 0]`. `unresolvedMass_le_pow` is equation (19) in
measure form. `retained_measure_eq` and `unresolvedMass_measure_eq` identify the four
quantities with their finite counterparts under `FiniteDiscreteMeasure.measure`, so the
finite certificate is the special case of a finitely supported law.

Scope: the bounds `0 ≤ N ≤ D ≤ 1` are assumed everywhere, and `N` and `D` are assumed
measurable. The sharpness remark of section 5.2, that the endpoints are the values of the
true mean at the residual pairs `(0, τ_K)` and `(τ_K, τ_K)`, is a statement about real
numbers and is not restated. The small-denominator rate (20) is not proved here.

## Empirical status

None. The bodies here are measure theory: every quantity is an integral of a stipulated
function of two given measurable functionals, and every claim is an identity, an inequality
or a limit between such integrals, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReplicaMeasureCertificate

open MeasureTheory ProbabilityTheory Filter Topology PositiveRatioExpansion

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **NOTE 2 equation (16).** The retained replica numerator `L_K`: the first `terms`
coefficients `∫ N (1 - D)^k` of the positive ratio expansion, each a polynomial functional
of the population law. -/
def retainedNumerator (μ : Measure Ω) (num den : Ω → ℝ) (terms : ℕ) : ℝ :=
  ∑ power ∈ Finset.range terms, ∫ point, num point * (1 - den point) ^ power ∂μ

/-- **NOTE 2 equation (16).** The retained definedness mass `H_K`, the total mass of the
subprobability weight `1 - (1 - D)^K`. -/
def retainedMass (μ : Measure Ω) (den : Ω → ℝ) (terms : ℕ) : ℝ :=
  ∫ point, 1 - (1 - den point) ^ terms ∂μ

/-- The numerator a truncation leaves unresolved, in closed form: the metric damped by the
denominator deficit raised to the truncation order. -/
def unresolvedNumerator (μ : Measure Ω) (num den : Ω → ℝ) (terms : ℕ) : ℝ :=
  ∫ point, ratioOnDefined num den point * (1 - den point) ^ terms ∂μ

/-- **NOTE 2 equation (17).** The definedness mass a truncation leaves unresolved,
`E[1_E (1 - D)^K]` over the defined event `E = {D > 0}`. -/
def unresolvedMass (μ : Measure Ω) (den : Ω → ℝ) (terms : ℕ) : ℝ :=
  ∫ point in {point | 0 < den point}, (1 - den point) ^ terms ∂μ

/-- The ratio metric read as zero off its defined event is measurable whenever its numerator
and its denominator are. -/
theorem measurable_ratioOnDefined (num den : Ω → ℝ) (hnumMeasurable : Measurable num)
    (hdenMeasurable : Measurable den) : Measurable (ratioOnDefined num den) := by
  unfold ratioOnDefined
  refine Measurable.ite ?_ (hnumMeasurable.div hdenMeasurable) measurable_const
  exact measurableSet_lt measurable_const hdenMeasurable

/-- A measurable function with values in the unit interval is integrable against a
probability measure. -/
theorem integrable_of_unit_bounds (μ : Measure Ω) [IsProbabilityMeasure μ] (value : Ω → ℝ)
    (hmeasurable : Measurable value) (hlower : ∀ point, 0 ≤ value point)
    (hupper : ∀ point, value point ≤ 1) : Integrable value μ := by
  refine (integrable_const (1 : ℝ)).mono' hmeasurable.aestronglyMeasurable
    (ae_of_all _ fun point ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hlower point)]
  exact hupper point

/-- Every coefficient integrand `N (1 - D)^k` of the positive ratio expansion is integrable. -/
theorem integrable_expansion_term (μ : Measure Ω) [IsProbabilityMeasure μ] (num den : Ω → ℝ)
    (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (power : ℕ) :
    Integrable (fun point ↦ num point * (1 - den point) ^ power) μ := by
  refine integrable_of_unit_bounds μ _
    (hnumMeasurable.mul ((measurable_const.sub hdenMeasurable).pow_const power))
    (fun point ↦ ?_) (fun point ↦ ?_)
  · exact mul_nonneg (hnum point) (pow_nonneg (by linarith [hden point]) power)
  · have hnumLeOne : num point ≤ 1 := le_trans (hle point) (hden point)
    have hpowNonneg : 0 ≤ (1 - den point) ^ power :=
      pow_nonneg (by linarith [hden point]) power
    have hpowLeOne : (1 - den point) ^ power ≤ 1 :=
      pow_le_one₀ (by linarith [hden point]) (by linarith [hnum point, hle point])
    nlinarith [hnum point]

/-- The retained weight `1 - (1 - D)^K` is integrable. -/
theorem integrable_retainedWeight (μ : Measure Ω) [IsProbabilityMeasure μ] (den : Ω → ℝ)
    (hdenMeasurable : Measurable den) (hdenNonneg : ∀ point, 0 ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    Integrable (fun point ↦ 1 - (1 - den point) ^ terms) μ := by
  refine integrable_of_unit_bounds μ _
    (measurable_const.sub ((measurable_const.sub hdenMeasurable).pow_const terms))
    (fun point ↦ ?_) (fun point ↦ ?_)
  · have hpowLeOne : (1 - den point) ^ terms ≤ 1 :=
      pow_le_one₀ (by linarith [hden point]) (by linarith [hdenNonneg point])
    linarith
  · have hpowNonneg : 0 ≤ (1 - den point) ^ terms :=
      pow_nonneg (by linarith [hden point]) terms
    linarith

/-- The damped metric `M (1 - D)^K` is integrable. -/
theorem integrable_dampedRatio (μ : Measure Ω) [IsProbabilityMeasure μ] (num den : Ω → ℝ)
    (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    Integrable (fun point ↦ ratioOnDefined num den point * (1 - den point) ^ terms) μ := by
  refine integrable_of_unit_bounds μ _
    ((measurable_ratioOnDefined num den hnumMeasurable hdenMeasurable).mul
      ((measurable_const.sub hdenMeasurable).pow_const terms))
    (fun point ↦ ?_) (fun point ↦ ?_)
  · exact mul_nonneg (ratioOnDefined_nonneg num den hnum point)
      (pow_nonneg (by linarith [hden point]) terms)
  · have hratioNonneg := ratioOnDefined_nonneg num den hnum point
    have hratioLeOne := ratioOnDefined_le_one num den hle point
    have hpowNonneg : 0 ≤ (1 - den point) ^ terms :=
      pow_nonneg (by linarith [hden point]) terms
    have hpowLeOne : (1 - den point) ^ terms ≤ 1 :=
      pow_le_one₀ (by linarith [hden point]) (by linarith [hnum point, hle point])
    nlinarith

/-- The unresolved weight, the deficit power restricted to the defined event, is integrable.
No lower bound on the denominator is needed: off the defined event the weight is zero. -/
theorem integrable_unresolvedWeight (μ : Measure Ω) [IsProbabilityMeasure μ] (den : Ω → ℝ)
    (hdenMeasurable : Measurable den) (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    Integrable
      (Set.indicator {point | 0 < den point} fun point ↦ (1 - den point) ^ terms) μ := by
  refine integrable_of_unit_bounds μ _
    (((measurable_const.sub hdenMeasurable).pow_const terms).indicator
      (measurableSet_lt measurable_const hdenMeasurable)) (fun point ↦ ?_) (fun point ↦ ?_)
  · by_cases hpos : 0 < den point
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte]
      exact pow_nonneg (by linarith [hden point]) terms
    · simp [hpos]
  · by_cases hpos : 0 < den point
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte]
      exact pow_le_one₀ (by linarith [hden point]) (by linarith)
    · simp [hpos]

/-- **NOTE 2 equation (16), measure form.** The expectation of the ratio metric is the retained
replica numerator plus the unresolved numerator, with no approximation. The pointwise identity
is `ReplicaDomainCertificate.geometric_partition`, read at one point. -/
theorem integral_ratioOnDefined_partition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Ω → ℝ) (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    ∫ point, ratioOnDefined num den point ∂μ =
      retainedNumerator μ num den terms + unresolvedNumerator μ num den terms := by
  have hpoint : ∀ point, ratioOnDefined num den point =
      (∑ power ∈ Finset.range terms, num point * (1 - den point) ^ power) +
        ratioOnDefined num den point * (1 - den point) ^ terms := by
    intro point
    have hprod : den point * ratioOnDefined num den point = num point :=
      ReplicaDomainCertificate.den_mul_ratioOnDefined (Report := Unit) (fun _ ↦ num point)
        (fun _ ↦ den point) (fun _ ↦ hnum point) (fun _ ↦ hle point) ()
    have hsplit := ReplicaDomainCertificate.geometric_partition (den point)
      (ratioOnDefined num den point) terms
    rw [hprod] at hsplit
    exact hsplit
  have htermIntegrable := integrable_expansion_term μ num den hnumMeasurable hdenMeasurable
    hnum hle hden
  rw [integral_congr_ae (ae_of_all μ hpoint),
    integral_add (integrable_finset_sum _ fun power _ ↦ htermIntegrable power)
      (integrable_dampedRatio μ num den hnumMeasurable hdenMeasurable hnum hle hden terms),
    integral_finset_sum _ fun power _ ↦ htermIntegrable power]
  rfl

/-- **NOTE 2 equations (16) and (17), measure form.** The probability of the defined event is
the retained definedness mass plus the unresolved definedness mass, with no approximation. -/
theorem definedProbability_partition (μ : Measure Ω) [IsProbabilityMeasure μ] (den : Ω → ℝ)
    (hdenMeasurable : Measurable den) (hdenNonneg : ∀ point, 0 ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    μ.real {point | 0 < den point} = retainedMass μ den terms + unresolvedMass μ den terms := by
  have hset : MeasurableSet {point | 0 < den point} :=
    measurableSet_lt measurable_const hdenMeasurable
  have hpoint : ∀ point, Set.indicator {point | 0 < den point} 1 point =
      (1 - (1 - den point) ^ terms) +
        Set.indicator {point | 0 < den point} (fun point ↦ (1 - den point) ^ terms) point := by
    intro point
    by_cases hpos : 0 < den point
    · simp [hpos]
    · have hzero : den point = 0 := le_antisymm (not_lt.mp hpos) (hdenNonneg point)
      simp [hzero]
  rw [← integral_indicator_one hset, integral_congr_ae (ae_of_all μ hpoint),
    integral_add (integrable_retainedWeight μ den hdenMeasurable hdenNonneg hden terms)
      (integrable_unresolvedWeight μ den hdenMeasurable hden terms),
    integral_indicator hset]
  rfl

/-- The retained replica numerator is nonnegative. -/
theorem retainedNumerator_nonneg (μ : Measure Ω) (num den : Ω → ℝ)
    (hnum : ∀ point, 0 ≤ num point) (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    0 ≤ retainedNumerator μ num den terms :=
  Finset.sum_nonneg fun power _ ↦ integral_nonneg fun point ↦
    mul_nonneg (hnum point) (pow_nonneg (by linarith [hden point]) power)

/-- **NOTE 2 section 5.2.** The retained numerator never exceeds the retained mass: the
subprobability weight `1 - (1 - D)^K` carries numerator `L_K` and total mass `H_K`, and the
metric it weights is at most one. -/
theorem retainedNumerator_le_retainedMass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Ω → ℝ) (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    retainedNumerator μ num den terms ≤ retainedMass μ den terms := by
  have htermIntegrable := integrable_expansion_term μ num den hnumMeasurable hdenMeasurable
    hnum hle hden
  have hdenNonneg : ∀ point, 0 ≤ den point := fun point ↦ le_trans (hnum point) (hle point)
  rw [retainedNumerator, ← integral_finset_sum _ fun power _ ↦ htermIntegrable power]
  exact integral_mono (integrable_finset_sum _ fun power _ ↦ htermIntegrable power)
    (integrable_retainedWeight μ den hdenMeasurable hdenNonneg hden terms) fun point ↦
      ReplicaDomainCertificate.partial_numerator_le (num point) (den point) (hnum point)
        (hle point) (hden point) terms

/-- The unresolved numerator is nonnegative. -/
theorem unresolvedNumerator_nonneg (μ : Measure Ω) (num den : Ω → ℝ)
    (hnum : ∀ point, 0 ≤ num point) (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    0 ≤ unresolvedNumerator μ num den terms :=
  integral_nonneg fun point ↦ mul_nonneg (ratioOnDefined_nonneg num den hnum point)
    (pow_nonneg (by linarith [hden point]) terms)

/-- The unresolved definedness mass is nonnegative. -/
theorem unresolvedMass_nonneg (μ : Measure Ω) (den : Ω → ℝ) (hden : ∀ point, den point ≤ 1)
    (terms : ℕ) : 0 ≤ unresolvedMass μ den terms :=
  integral_nonneg fun point ↦ pow_nonneg (by linarith [hden point]) terms

/-- **NOTE 2 section 5.2, the coupling.** The numerator a truncation discards never exceeds
the definedness mass it discards, because the metric is at most one on the defined event and
vanishes off it. -/
theorem unresolvedNumerator_le_unresolvedMass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Ω → ℝ) (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    unresolvedNumerator μ num den terms ≤ unresolvedMass μ den terms := by
  have hset : MeasurableSet {point | 0 < den point} :=
    measurableSet_lt measurable_const hdenMeasurable
  rw [unresolvedMass, ← integral_indicator hset]
  refine integral_mono
    (integrable_dampedRatio μ num den hnumMeasurable hdenMeasurable hnum hle hden terms)
    (integrable_unresolvedWeight μ den hdenMeasurable hden terms) fun point ↦ ?_
  have hpowNonneg : 0 ≤ (1 - den point) ^ terms := pow_nonneg (by linarith [hden point]) terms
  show ratioOnDefined num den point * (1 - den point) ^ terms ≤ _
  by_cases hpos : 0 < den point
  · have hweight : Set.indicator {point | 0 < den point} (fun point ↦ (1 - den point) ^ terms)
        point = (1 - den point) ^ terms := by simp [hpos]
    rw [hweight]
    calc ratioOnDefined num den point * (1 - den point) ^ terms
        ≤ 1 * (1 - den point) ^ terms :=
          mul_le_mul_of_nonneg_right (ratioOnDefined_le_one num den hle point) hpowNonneg
      _ = (1 - den point) ^ terms := one_mul _
  · have hweight : Set.indicator {point | 0 < den point} (fun point ↦ (1 - den point) ^ terms)
        point = 0 := by simp [hpos]
    have hratio : ratioOnDefined num den point = 0 := by simp [ratioOnDefined, hpos]
    rw [hweight, hratio, zero_mul]

/-- The unresolved definedness mass never exceeds the complement of the retained mass, since
together they make up the probability of the defined event. -/
theorem unresolvedMass_le_one_sub_retainedMass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (den : Ω → ℝ) (hdenMeasurable : Measurable den) (hdenNonneg : ∀ point, 0 ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    unresolvedMass μ den terms ≤ 1 - retainedMass μ den terms := by
  have hpartition := definedProbability_partition μ den hdenMeasurable hdenNonneg hden terms
  have hprobability : μ.real {point | 0 < den point} ≤ 1 := measureReal_le_one
  linarith

/-- **NOTE 2 equation (17) and section 5.2.** A tolerance dominating the unresolved definedness
mass controls both unresolved quantities at once: `0 ≤ δ_n ≤ δ_d ≤ min τ_K (1 - H_K)`. -/
theorem coupled_residuals (μ : Measure Ω) [IsProbabilityMeasure μ] (num den : Ω → ℝ)
    (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass μ den terms ≤ tolerance) :
    0 ≤ unresolvedNumerator μ num den terms ∧
      unresolvedNumerator μ num den terms ≤ unresolvedMass μ den terms ∧
      unresolvedMass μ den terms ≤ min tolerance (1 - retainedMass μ den terms) :=
  ⟨unresolvedNumerator_nonneg μ num den hnum hden terms,
    unresolvedNumerator_le_unresolvedMass μ num den hnumMeasurable hdenMeasurable hnum hle hden
      terms,
    le_min htolerance (unresolvedMass_le_one_sub_retainedMass μ den hdenMeasurable
      (fun point ↦ le_trans (hnum point) (hle point)) hden terms)⟩

/-- The conditional expectation of the metric given the defined event, read in Mathlib's
conditional measure `μ[|E]`, is the metric expectation over the probability of that event. -/
theorem conditional_integral_ratioOnDefined (μ : Measure Ω) (num den : Ω → ℝ) :
    ∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}] =
      (∫ point, ratioOnDefined num den point ∂μ) / μ.real {point | 0 < den point} := by
  have hvanish : ∀ point, point ∉ {point | 0 < den point} →
      ratioOnDefined num den point = 0 := by
    intro point hpoint
    have hneg : ¬ 0 < den point := hpoint
    simp [ratioOnDefined, hneg]
  rw [ProbabilityTheory.cond, integral_smul_measure,
    setIntegral_eq_integral_of_forall_compl_eq_zero hvanish, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul, inv_mul_eq_div]

/-- **NOTE 2 equation (18), Theorem 4, over a probability measure.** With a tolerance
dominating the unresolved definedness mass and positive retained mass, the conditional
expectation of the bounded ratio metric given its defined event lies between `L_K / (H_K + τ_K)`
and `(L_K + τ_K) / (H_K + τ_K)`. Only retained quantities and the tolerance appear in the
bounds, so the enclosure is computable from finitely many replica coefficients, and the
undefined event may carry positive probability. -/
theorem measure_replica_certificate (μ : Measure Ω) [IsProbabilityMeasure μ] (num den : Ω → ℝ)
    (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass μ den terms ≤ tolerance)
    (hretained : 0 < retainedMass μ den terms) :
    retainedNumerator μ num den terms / (retainedMass μ den terms + tolerance) ≤
        ∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}] ∧
      ∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}] ≤
        (retainedNumerator μ num den terms + tolerance) /
          (retainedMass μ den terms + tolerance) := by
  have hdenNonneg : ∀ point, 0 ≤ den point := fun point ↦ le_trans (hnum point) (hle point)
  have hretainedNonneg := retainedNumerator_nonneg μ num den hnum hden terms
  have hretainedLe := retainedNumerator_le_retainedMass μ num den hnumMeasurable
    hdenMeasurable hnum hle hden terms
  have hunresolvedNonneg := unresolvedNumerator_nonneg μ num den hnum hden terms
  have hunresolvedLe := unresolvedNumerator_le_unresolvedMass μ num den hnumMeasurable
    hdenMeasurable hnum hle hden terms
  have hmassNonneg := unresolvedMass_nonneg μ den hden terms
  obtain ⟨hlow, hhigh⟩ := SublawReportCertificate.ratio_bounds 0 1 (retainedMass μ den terms)
    (retainedNumerator μ num den terms) (unresolvedMass μ den terms)
    (unresolvedNumerator μ num den terms) tolerance hretained hmassNonneg htolerance
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [conditional_integral_ratioOnDefined μ num den,
    integral_ratioOnDefined_partition μ num den hnumMeasurable hdenMeasurable hnum hle hden
      terms,
    definedProbability_partition μ den hdenMeasurable hdenNonneg hden terms]
  exact ⟨by simpa using hlow, by simpa using hhigh⟩

/-- **NOTE 2 equation (18), width.** The certified interval has width exactly
`τ_K / (H_K + τ_K)`, and that width is nonnegative. -/
theorem measure_certificate_width (μ : Measure Ω) (num den : Ω → ℝ) (terms : ℕ)
    (tolerance : ℝ) (htolerance : 0 ≤ tolerance) (hretained : 0 < retainedMass μ den terms) :
    (retainedNumerator μ num den terms + tolerance) / (retainedMass μ den terms + tolerance) -
        retainedNumerator μ num den terms / (retainedMass μ den terms + tolerance) =
      tolerance / (retainedMass μ den terms + tolerance) ∧
    0 ≤ tolerance / (retainedMass μ den terms + tolerance) := by
  refine ⟨?_, div_nonneg htolerance (by linarith)⟩
  rw [div_sub_div_same, add_sub_cancel_left]

/-- **NOTE 2 section 5.2.** The tolerance of the certificate may be replaced by its minimum
with `1 - H_K`, because that minimum still dominates the unresolved definedness mass. -/
theorem replica_certificate_min_tolerance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Ω → ℝ) (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) (tolerance : ℝ)
    (htolerance : unresolvedMass μ den terms ≤ tolerance)
    (hretained : 0 < retainedMass μ den terms) :
    retainedNumerator μ num den terms /
          (retainedMass μ den terms + min tolerance (1 - retainedMass μ den terms)) ≤
        ∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}] ∧
      ∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}] ≤
        (retainedNumerator μ num den terms + min tolerance (1 - retainedMass μ den terms)) /
          (retainedMass μ den terms + min tolerance (1 - retainedMass μ den terms)) :=
  measure_replica_certificate μ num den hnumMeasurable hdenMeasurable hnum hle hden terms
    (min tolerance (1 - retainedMass μ den terms))
    (coupled_residuals μ num den hnumMeasurable hdenMeasurable hnum hle hden terms tolerance
      htolerance).2.2 hretained

/-- The unresolved definedness mass tends to zero as the truncation order grows, for every
model: on the defined event the deficit `1 - D` lies in `[0, 1)`, so its powers tend to zero,
and dominated convergence against the constant one moves the limit through the integral. -/
theorem tendsto_unresolvedMass (μ : Measure Ω) [IsProbabilityMeasure μ] (den : Ω → ℝ)
    (hdenMeasurable : Measurable den) (hden : ∀ point, den point ≤ 1) :
    Tendsto (fun terms ↦ unresolvedMass μ den terms) atTop (𝓝 0) := by
  have hset : MeasurableSet {point | 0 < den point} :=
    measurableSet_lt measurable_const hdenMeasurable
  have hlimit : Tendsto (fun terms : ℕ ↦ ∫ point,
      Set.indicator {point | 0 < den point} (fun point ↦ (1 - den point) ^ terms) point ∂μ)
      atTop (𝓝 (∫ _point, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun terms ↦
        (integrable_unresolvedWeight μ den hdenMeasurable hden terms).aestronglyMeasurable)
      (integrable_const 1) (fun terms ↦ ae_of_all _ fun point ↦ ?_)
      (ae_of_all _ fun point ↦ ?_)
    · by_cases hpos : 0 < den point
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte, Real.norm_eq_abs]
        rw [abs_of_nonneg (pow_nonneg (by linarith [hden point]) terms)]
        exact pow_le_one₀ (by linarith [hden point]) (by linarith)
      · simp [hpos]
    · by_cases hpos : 0 < den point
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hden point]) (by linarith)
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte]
        exact tendsto_const_nhds
  rw [integral_zero] at hlimit
  refine hlimit.congr fun terms ↦ ?_
  dsimp only
  rw [unresolvedMass, integral_indicator hset]

/-- **NOTE 2 section 5.2, convergence.** When tolerances dominating the unresolved definedness
mass tend to zero and the defined event has positive probability, both endpoints of the
certificate converge to the conditional expectation of the metric given the defined event. -/
theorem certificate_endpoints_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Ω → ℝ) (hnumMeasurable : Measurable num) (hdenMeasurable : Measurable den)
    (hnum : ∀ point, 0 ≤ num point) (hle : ∀ point, num point ≤ den point)
    (hden : ∀ point, den point ≤ 1) (tolerance : ℕ → ℝ)
    (htolerance : ∀ terms, unresolvedMass μ den terms ≤ tolerance terms)
    (hvanish : Tendsto tolerance atTop (𝓝 0))
    (hdefined : 0 < μ.real {point | 0 < den point}) :
    Tendsto (fun terms ↦ retainedNumerator μ num den terms /
        (retainedMass μ den terms + tolerance terms)) atTop
        (𝓝 (∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}])) ∧
      Tendsto (fun terms ↦ (retainedNumerator μ num den terms + tolerance terms) /
        (retainedMass μ den terms + tolerance terms)) atTop
        (𝓝 (∫ point, ratioOnDefined num den point ∂μ[|{point | 0 < den point}])) := by
  have hdenNonneg : ∀ point, 0 ≤ den point := fun point ↦ le_trans (hnum point) (hle point)
  have hmassVanish : Tendsto (fun terms ↦ unresolvedMass μ den terms) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvanish
      (fun terms ↦ unresolvedMass_nonneg μ den hden terms) htolerance
  have hnumeratorVanish : Tendsto (fun terms ↦ unresolvedNumerator μ num den terms) atTop
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmassVanish
      (fun terms ↦ unresolvedNumerator_nonneg μ num den hnum hden terms)
      (fun terms ↦ unresolvedNumerator_le_unresolvedMass μ num den hnumMeasurable
        hdenMeasurable hnum hle hden terms)
  have hnumerator : Tendsto (fun terms ↦ retainedNumerator μ num den terms) atTop
      (𝓝 (∫ point, ratioOnDefined num den point ∂μ)) := by
    have hdifference : Tendsto (fun terms ↦ (∫ point, ratioOnDefined num den point ∂μ) -
        unresolvedNumerator μ num den terms) atTop
        (𝓝 ((∫ point, ratioOnDefined num den point ∂μ) - 0)) :=
      tendsto_const_nhds.sub hnumeratorVanish
    rw [sub_zero] at hdifference
    refine hdifference.congr fun terms ↦ ?_
    dsimp only
    rw [integral_ratioOnDefined_partition μ num den hnumMeasurable hdenMeasurable hnum hle hden
      terms, add_sub_cancel_right]
  have hmass : Tendsto (fun terms ↦ retainedMass μ den terms + tolerance terms) atTop
      (𝓝 (μ.real {point | 0 < den point})) := by
    have hdifference : Tendsto (fun terms ↦ μ.real {point | 0 < den point} -
        unresolvedMass μ den terms + tolerance terms) atTop
        (𝓝 (μ.real {point | 0 < den point} - 0 + 0)) :=
      (tendsto_const_nhds.sub hmassVanish).add hvanish
    rw [sub_zero, add_zero] at hdifference
    refine hdifference.congr fun terms ↦ ?_
    dsimp only
    rw [definedProbability_partition μ den hdenMeasurable hdenNonneg hden terms,
      add_sub_cancel_right]
  have hupper : Tendsto (fun terms ↦ retainedNumerator μ num den terms + tolerance terms)
      atTop (𝓝 ((∫ point, ratioOnDefined num den point ∂μ) + 0)) := hnumerator.add hvanish
  rw [add_zero] at hupper
  rw [conditional_integral_ratioOnDefined μ num den]
  exact ⟨hnumerator.div hmass hdefined.ne', hupper.div hmass hdefined.ne'⟩

/-- **NOTE 2 equation (19), measure form.** A denominator bounded below by a floor on its
defined event makes the unresolved definedness mass decay geometrically in the truncation
order, so `(1 - floor)^K` is an admissible tolerance. -/
theorem unresolvedMass_le_pow (μ : Measure Ω) [IsProbabilityMeasure μ] (den : Ω → ℝ)
    (hdenMeasurable : Measurable den) (denFloor : ℝ) (hfloorLeOne : denFloor ≤ 1)
    (hfloor : ∀ point, 0 < den point → denFloor ≤ den point)
    (hden : ∀ point, den point ≤ 1) (terms : ℕ) :
    unresolvedMass μ den terms ≤ (1 - denFloor) ^ terms := by
  have hset : MeasurableSet {point | 0 < den point} :=
    measurableSet_lt measurable_const hdenMeasurable
  rw [unresolvedMass, ← integral_indicator hset]
  calc ∫ point, Set.indicator {point | 0 < den point} (fun point ↦ (1 - den point) ^ terms)
        point ∂μ
      ≤ ∫ _point, (1 - denFloor) ^ terms ∂μ := by
        refine integral_mono (integrable_unresolvedWeight μ den hdenMeasurable hden terms)
          (integrable_const _) fun point ↦ ?_
        by_cases hpos : 0 < den point
        · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte]
          exact pow_le_pow_left₀ (by linarith [hden point]) (by linarith [hfloor point hpos])
            terms
        · simp only [Set.indicator_apply, Set.mem_setOf_eq, hpos, ↓reduceIte]
          exact pow_nonneg (by linarith) terms
    _ = (1 - denFloor) ^ terms := by
        rw [integral_const, measureReal_univ_eq_one, one_smul]

/-- For a finite report law viewed as a probability measure, the retained numerator, the
retained mass and the unresolved numerator are the finite quantities of
`ReplicaDomainCertificate`, so the finite certificate is the finitely supported case. -/
theorem retained_measure_eq {Report : Type*} [Fintype Report] [MeasurableSpace Report]
    [MeasurableSingletonClass Report] (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (terms : ℕ) :
    retainedNumerator (FiniteDiscreteMeasure.measure law) num den terms =
        ReplicaDomainCertificate.retainedNumerator law num den terms ∧
      retainedMass (FiniteDiscreteMeasure.measure law) den terms =
        ReplicaDomainCertificate.retainedMass law den terms ∧
      unresolvedNumerator (FiniteDiscreteMeasure.measure law) num den terms =
        ReplicaDomainCertificate.unresolvedNumerator law num den terms := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [retainedNumerator, ReplicaDomainCertificate.retainedNumerator,
      FiniteDiscreteMeasure.integral_observable]
  · exact FiniteDiscreteMeasure.integral_observable law fun report ↦ 1 - (1 - den report) ^ terms
  · exact FiniteDiscreteMeasure.integral_observable law fun report ↦
      ratioOnDefined num den report * (1 - den report) ^ terms

/-- For a finite report law viewed as a probability measure, the unresolved definedness mass is
the finite unresolved mass of `ReplicaDomainCertificate`: the restricted integral is the
expectation of the definedness indicator times the deficit power. -/
theorem unresolvedMass_measure_eq {Report : Type*} [Fintype Report] [MeasurableSpace Report]
    [MeasurableSingletonClass Report] (law : FiniteReportLaw Report) (den : Report → ℝ)
    (terms : ℕ) :
    unresolvedMass (FiniteDiscreteMeasure.measure law) den terms =
      ReplicaDomainCertificate.unresolvedMass law den terms := by
  rw [unresolvedMass,
    ← integral_indicator (Set.toFinite {report | 0 < den report}).measurableSet,
    FiniteDiscreteMeasure.integral_observable, ReplicaDomainCertificate.unresolvedMass]
  refine congrArg law.expectation (funext fun report ↦ ?_)
  by_cases hpos : 0 < den report <;>
    simp [SublawReportCertificate.definedIndicator, hpos]

end

end Descent.Portability.ReplicaMeasureCertificate
