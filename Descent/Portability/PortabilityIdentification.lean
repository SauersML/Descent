/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AttainableChronologyCurve
import Descent.Portability.ChronologyReportLaw
import Descent.Portability.EmpiricalLawContinuityBound
import Descent.Portability.ExposureLaplaceConstraints
import Descent.Portability.PortabilityMinimaxLowerBound

assert_below Descent.Decision Descent.Program

/-!
# What identifies target portability: the exposure law, and a plug-in estimator

`PortabilityMinimaxLowerBound` shows that source data alone cannot certify target portability.
This module proves the positive half in NOTE1's chronology model (section 6). The target report
law is an explicit functional of the source report law and the exposure law `ν` of (29)-(30).
Equal source laws and equal exposure laws therefore give equal target portability, and the plug-in
estimator built from `ν` reaches the target from source replicas with an error bounded by the source
estimation error.

## Statement

**Transport form of NOTE1 (31).** For a law `w` on score-outcome cells and a coupling `c`, the
transported law is `c w + (1 - c) w_S ⊗ w_Y`, where `w_S` and `w_Y` are the score and outcome
shares (`transportMass`). The chronology law at donor fraction `p` and coupling `C` is the frozen
fully coupled discovery law at `p` (`chronologyMass p 1`, NOTE1 section 6.1) transported with
coupling `C` (`chronologyMass_eq_transportMass`). So every target expectation is
`C E_q f + (1 - C) E_{q_S ⊗ q_Y} f` (`expectation_chronologyLaw_eq_transportExpectation`).

**Identification.** For continuous rates, a nonnegative migration rate, a forward horizon and a
positive donor fraction, the coupling is `L_ν(1) = ∫ e^{-b} ν(db)`
(`normalisedCoupling_eq_measureLaplace_one`, NOTE1 (29)). For nonnegative rates the target squared
correlation, AUC and linear slope are `L_ν(1)²`, `(1 + L_ν(1))/2` and `L_ν(1)`
(`targetLaw_metrics`). The frozen discovery population has squared correlation one
(`squaredCorrelation_frozenSource`), so the source-relative portability ratio is `L_ν(1)²`. Two
chronologies with equal source laws and equal exposure laws have the same target law
(`chronologyMass_eq_of_source_eq_of_exposureLaw_eq`). They therefore agree on every target metric
and every source-relative portability quantity.

**Plug-in estimator.** For probability vectors `w`, `w'` and a metric bounded by `B`, the
transported expectation moves by at most `2B ∑ |w - w'|` (`abs_transportExpectation_sub_le`). The
plug-in estimator replaces the source law by the empirical law of `n` source replicas and keeps the
coupling `L_ν(1)`. It has no identification bias: at the population law it equals the target value
exactly. Its expected absolute error is at most `2B √((K - 1)/n)` with `K` report cells
(`expectation_abs_plugIn_sub_le`), which is `2B √(3/n)` for NOTE1's two-locus reports
(`expectation_abs_plugIn_chronologyLaw_sub_le`). For the squared correlation, the slope, the AUC and
the portability ratio the plug-in needs no replicas at all.

**The information boundary.** At `M = R = log 2` the migration-first and recombination-first
chronologies share one source law, and their couplings are the transforms of the point masses
`δ_{log 2}` and `δ_0` (`couplingOfState_threeBlockHistory_eq_measureLaplace`). Every source-only
estimator of the target squared correlation has worst-case error at least `3/8`, for every number of
replicas. The plug-in values `L_ν(1)²` are the target values `1/4` and `1` exactly
(`logTwo_informationBoundary`).

## Significance

Together with `PortabilityMinimaxLowerBound` this gives an exact information boundary for the
chronology model. Source data identify at most the source report law. The target squared
correlation and the source-relative portability ratio are functions of the single number `L_ν(1)`,
which no source panel carries. Supplying `ν`, or only `L_ν(1)`, turns an irreducible error of half
the target range into zero error for correlation-type quantities. For every bounded target metric it
leaves only the source sampling error `2B √(3/n)`. The exposure law also carries the whole
recombination-scaling curve `λ ↦ L_ν(λ)` of NOTE1 (30), and that curve determines `ν`
(`ExposureLaplaceConstraints.measure_eq_of_measureLaplace_eq`).

## Scope

The model is NOTE1 section 6: a recipient monomorphic for `00`, a donor fixed for `11`, fixed score
and phenotype maps, and no drift, mutation or selection. The full target law is the transport of the
fully coupled discovery law at the target allele frequency. Correlation-type quantities do not
depend on that frequency. "No identification bias" means the functional is exact at the population
law. The plug-in with empirical score and outcome shares is not claimed to be unbiased in the
product term. Its bias is at most its expected absolute error. The error bound is in expectation,
not with high probability. The three-block couplings are identified with transforms of point
masses, not the
exposure law of an event history as a measure.

## Empirical status

None. The theorems are identities and inequalities about stated laws and the constructed replica
law, so no measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityIdentification

open Finset MeasureTheory
open Descent.Portability.AdmixtureChronologyLaw (donorFraction normalisedCoupling
  donorFraction_nonneg donorFraction_lt_one)
open Descent.Portability.AttainableChronologyCurve (chronologyExposureLaw)
open Descent.Portability.ExposureLaplaceConstraints (measureLaplace)
open Descent.Portability.EmpiricalLawLipschitzBound (replicaLaw empiricalMass)

noncomputable section

section Transport

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The score share `w_S(s) = ∑_y w(s, y)` of a law on score-outcome cells. -/
def scoreShare (w : α × β → ℝ) (s : α) : ℝ := ∑ y, w (s, y)

/-- The outcome share `w_Y(y) = ∑_s w(s, y)` of a law on score-outcome cells. -/
def outcomeShare (w : α × β → ℝ) (y : β) : ℝ := ∑ s, w (s, y)

/-- The transported cell mass `c w + (1 - c) w_S ⊗ w_Y`: a fraction `c` of the source linkage
survives, and the rest is replaced by independent recombinants with the same shares. -/
def transportMass (w : α × β → ℝ) (c : ℝ) (cell : α × β) : ℝ :=
  c * w cell + (1 - c) * (scoreShare w cell.1 * outcomeShare w cell.2)

/-- The expectation of a metric under the transported law. -/
def transportExpectation (w : α × β → ℝ) (c : ℝ) (metric : α × β → ℝ) : ℝ :=
  ∑ cell, transportMass w c cell * metric cell

/-- The score shares add up to the total mass. -/
theorem sum_scoreShare (w : α × β → ℝ) : ∑ s, scoreShare w s = ∑ cell, w cell := by
  simp only [scoreShare]
  exact (Fintype.sum_prod_type w).symm

/-- The outcome shares add up to the total mass. -/
theorem sum_outcomeShare (w : α × β → ℝ) : ∑ y, outcomeShare w y = ∑ cell, w cell := by
  simp only [outcomeShare]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type w).symm

/-- The score shares move by at most the total cell movement. -/
theorem sum_abs_scoreShare_sub_le (w w' : α × β → ℝ) :
    ∑ s, |scoreShare w s - scoreShare w' s| ≤ ∑ cell, |w cell - w' cell| := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  simp only [scoreShare, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The outcome shares move by at most the total cell movement. -/
theorem sum_abs_outcomeShare_sub_le (w w' : α × β → ℝ) :
    ∑ y, |outcomeShare w y - outcomeShare w' y| ≤ ∑ cell, |w cell - w' cell| := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  simp only [outcomeShare, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **The transported expectation is Lipschitz on probability vectors.** For laws `w`, `w'` and a
metric bounded by `bound`, the transported expectations differ by at most
`2 bound ∑ |w - w'|`. Assumes: both are probability vectors, `0 ≤ c ≤ 1` and a bounded metric. -/
theorem abs_transportExpectation_sub_le {w w' : α × β → ℝ} (hw : ∀ cell, 0 ≤ w cell)
    (hw1 : ∑ cell, w cell = 1) (hw' : ∀ cell, 0 ≤ w' cell) (hw'1 : ∑ cell, w' cell = 1)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {metric : α × β → ℝ} {bound : ℝ} (witness : α × β)
    (hmetric : ∀ cell, |metric cell| ≤ bound) :
    |transportExpectation w c metric - transportExpectation w' c metric| ≤
      2 * bound * ∑ cell, |w cell - w' cell| := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hmetric witness)
  have hcell : ∀ cell, |transportMass w c cell - transportMass w' c cell| ≤
      c * |w cell - w' cell| +
        (1 - c) * (|scoreShare w cell.1 - scoreShare w' cell.1| * outcomeShare w cell.2 +
          scoreShare w' cell.1 * |outcomeShare w cell.2 - outcomeShare w' cell.2|) := by
    intro cell
    have houtcome : 0 ≤ outcomeShare w cell.2 := Finset.sum_nonneg fun _ _ ↦ hw _
    have hscore : 0 ≤ scoreShare w' cell.1 := Finset.sum_nonneg fun _ _ ↦ hw' _
    have hsplit : transportMass w c cell - transportMass w' c cell =
        c * (w cell - w' cell) +
          (1 - c) * ((scoreShare w cell.1 - scoreShare w' cell.1) * outcomeShare w cell.2 +
            scoreShare w' cell.1 * (outcomeShare w cell.2 - outcomeShare w' cell.2)) := by
      simp only [transportMass]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [abs_mul, abs_of_nonneg hc0]
    · rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hc1)]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
        (add_le_add (le_of_eq ?_) (le_of_eq ?_))) (sub_nonneg.mpr hc1)
      · rw [abs_mul, abs_of_nonneg houtcome]
      · rw [abs_mul, abs_of_nonneg hscore]
  have hscoreSum : ∑ cell : α × β,
      |scoreShare w cell.1 - scoreShare w' cell.1| * outcomeShare w cell.2 =
        ∑ s, |scoreShare w s - scoreShare w' s| := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, sum_outcomeShare, hw1, mul_one]
  have houtcomeSum : ∑ cell : α × β,
      scoreShare w' cell.1 * |outcomeShare w cell.2 - outcomeShare w' cell.2| =
        ∑ y, |outcomeShare w y - outcomeShare w' y| := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_scoreShare, hw'1, one_mul]
  have hsum : ∑ cell, |transportMass w c cell - transportMass w' c cell| ≤
      2 * ∑ cell, |w cell - w' cell| := by
    have hstep := Finset.sum_le_sum fun cell (_ : cell ∈ (univ : Finset (α × β))) ↦ hcell cell
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      hscoreSum, houtcomeSum] at hstep
    have hscoreMove := sum_abs_scoreShare_sub_le w w'
    have houtcomeMove := sum_abs_outcomeShare_sub_le w w'
    have hmove : 0 ≤ ∑ cell, |w cell - w' cell| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hscoreMove houtcomeMove)
      (sub_nonneg.mpr hc1), mul_nonneg hc0 hmove]
  calc |transportExpectation w c metric - transportExpectation w' c metric|
      = |∑ cell, (transportMass w c cell - transportMass w' c cell) * metric cell| := by
        simp only [transportExpectation, ← Finset.sum_sub_distrib, sub_mul]
    _ ≤ ∑ cell, |transportMass w c cell - transportMass w' c cell| * bound := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun cell _ ↦ ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmetric cell) (abs_nonneg _)
    _ = bound * ∑ cell, |transportMass w c cell - transportMass w' c cell| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun cell _ ↦ mul_comm _ _
    _ ≤ bound * (2 * ∑ cell, |w cell - w' cell|) := mul_le_mul_of_nonneg_left hsum hbound
    _ = 2 * bound * ∑ cell, |w cell - w' cell| := by ring

/-- **The plug-in estimator from source replicas.** Replace the source law by the empirical law of
`n` replicas and keep the coupling. The expected absolute error of the transported expectation of a
metric bounded by `bound` is then at most `2 bound √((K - 1)/n)`, where `K` is the number of report
cells. Assumes: `0 < n`, `0 ≤ c ≤ 1` and a bounded metric. -/
theorem expectation_abs_plugIn_sub_le (count : ℕ) (hcount : 0 < count)
    (q : FiniteReportLaw (α × β)) (witness : α × β) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {metric : α × β → ℝ} {bound : ℝ} (hmetric : ∀ cell, |metric cell| ≤ bound) :
    (replicaLaw count q).expectation
        (fun draw ↦ |transportExpectation (empiricalMass draw) c metric -
          transportExpectation q.mass c metric|) ≤
      2 * bound * Real.sqrt (((Fintype.card (α × β) : ℝ) - 1) / count) := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hmetric witness)
  have hpoint : ∀ draw : Fin count → α × β,
      |transportExpectation (empiricalMass draw) c metric -
          transportExpectation q.mass c metric| ≤
        2 * bound * ∑ cell, |empiricalMass draw cell - q.mass cell| := fun draw ↦
    abs_transportExpectation_sub_le
      (EmpiricalLawContinuityBound.empiricalMass_mem_stdSimplex hcount draw).1
      (EmpiricalLawContinuityBound.empiricalMass_mem_stdSimplex hcount draw).2
      q.mass_nonneg q.mass_sum hc0 hc1 witness hmetric
  calc (replicaLaw count q).expectation
        (fun draw ↦ |transportExpectation (empiricalMass draw) c metric -
          transportExpectation q.mass c metric|)
      ≤ (replicaLaw count q).expectation
          (fun draw ↦ 2 * bound * ∑ cell, |empiricalMass draw cell - q.mass cell|) := by
        simp only [FiniteReportLaw.expectation]
        exact Finset.sum_le_sum fun draw _ ↦
          mul_le_mul_of_nonneg_left (hpoint draw) ((replicaLaw count q).mass_nonneg draw)
    _ = 2 * bound * (replicaLaw count q).expectation
          (fun draw ↦ ∑ cell, |empiricalMass draw cell - q.mass cell|) := by
        simp only [FiniteReportLaw.expectation]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun draw _ ↦ by ring
    _ ≤ 2 * bound * Real.sqrt (((Fintype.card (α × β) : ℝ) - 1) / count) :=
        mul_le_mul_of_nonneg_left
          (EmpiricalLawLipschitzBound.expectation_deviation_sum_le count hcount witness q)
          (mul_nonneg zero_le_two hbound)

end Transport

section Chronology

open Descent.Portability.ChronologyReportLaw (chronologyMass chronologyLaw)

/-- **NOTE1 (31) is a transport.** The chronology law at donor fraction `p` and coupling `C` is
the fully coupled discovery law at `p` transported with coupling `C`. -/
theorem chronologyMass_eq_transportMass (p C : ℝ) :
    chronologyMass p C = transportMass (chronologyMass p 1) C := by
  funext cell
  rcases cell with ⟨_ | _, _ | _⟩ <;>
    simp only [transportMass, scoreShare, outcomeShare, Fintype.sum_bool,
      ChronologyReportLaw.chronologyMass_false_false,
      ChronologyReportLaw.chronologyMass_false_true,
      ChronologyReportLaw.chronologyMass_true_false,
      ChronologyReportLaw.chronologyMass_true_true] <;>
    ring

/-- Every target expectation is the transported expectation of the frozen discovery law.
Assumes: `0 ≤ p ≤ 1` and `0 ≤ C ≤ 1`. -/
theorem expectation_chronologyLaw_eq_transportExpectation (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (metric : Bool × Bool → ℝ) :
    (chronologyLaw p C hp0 hp1 hC0 hC1).expectation metric =
      transportExpectation (chronologyMass p 1) C metric := by
  change ∑ cell, chronologyMass p C cell * metric cell = _
  rw [chronologyMass_eq_transportMass p C]
  rfl

/-- NOTE1 (29) at recombination multiplier one: the coupling of a chronology is the transform
`L_ν(1) = ∫ e^{-b} ν(db)` of its exposure law. Assumes: continuous rates, a nonnegative migration
rate, `0 ≤ T` and a positive donor fraction. -/
theorem normalisedCoupling_eq_measureLaplace_one (m r : ℝ → ℝ) (hm : Continuous m)
    (hmnonneg : ∀ s, 0 ≤ m s) (hr : Continuous r) (T : ℝ) (hT : 0 ≤ T)
    (hpos : 0 < donorFraction m T) :
    normalisedCoupling m r T = measureLaplace (chronologyExposureLaw m r T) 1 := by
  have hscaled := AttainableChronologyCurve.scaled_normalisedCoupling_eq_measureLaplace m r hm
    hmnonneg hr 1 T hT hpos
  have hrate : (fun s ↦ 1 * r s) = r := funext fun s ↦ one_mul (r s)
  rwa [hrate] at hscaled

/-- The target report law of a chronology with continuous nonnegative rates: NOTE1 (31) at donor
fraction `1 - e^{-M(T)}` and the chronology's coupling. Assumes: continuous nonnegative rates,
`0 ≤ T` and a positive donor fraction. -/
def targetLaw (m r : ℝ → ℝ) (hm : Continuous m) (hr : Continuous r) (hmnonneg : ∀ s, 0 ≤ m s)
    (hrnonneg : ∀ s, 0 ≤ r s) (T : ℝ) (hT : 0 ≤ T) (hpos : 0 < donorFraction m T) :
    FiniteReportLaw (Bool × Bool) :=
  chronologyLaw (donorFraction m T) (normalisedCoupling m r T)
    (donorFraction_nonneg m hmnonneg T hT) (donorFraction_lt_one m T).le
    ((Real.exp_pos _).le.trans (AttainableChronologyCurve.exp_neg_le_normalisedCoupling m r hm hr
      hmnonneg hrnonneg T hT hpos))
    (AttainableChronologyCurve.normalisedCoupling_le_one m r hm hr hmnonneg hrnonneg T hT hpos)

/-- **The target metrics are functions of `L_ν(1)`.** The target squared correlation, AUC and
linear slope of a chronology are `L_ν(1)²`, `(1 + L_ν(1))/2` and `L_ν(1)`. Assumes: continuous
nonnegative rates, `0 ≤ T` and a positive donor fraction. -/
theorem targetLaw_metrics (m r : ℝ → ℝ) (hm : Continuous m) (hr : Continuous r)
    (hmnonneg : ∀ s, 0 ≤ m s) (hrnonneg : ∀ s, 0 ≤ r s) (T : ℝ) (hT : 0 ≤ T)
    (hpos : 0 < donorFraction m T) :
    (targetLaw m r hm hr hmnonneg hrnonneg T hT hpos).squaredCorrelation
        ChronologyReportLaw.scoreOf ChronologyReportLaw.outcomeOf =
        some (measureLaplace (chronologyExposureLaw m r T) 1 ^ 2) ∧
      ChronologyReportLaw.populationAUC (targetLaw m r hm hr hmnonneg hrnonneg T hT hpos) =
        (1 + measureLaplace (chronologyExposureLaw m r T) 1) / 2 ∧
      ChronologyReportLaw.linearSlope (targetLaw m r hm hr hmnonneg hrnonneg T hT hpos) =
        measureLaplace (chronologyExposureLaw m r T) 1 := by
  have hcoupling := normalisedCoupling_eq_measureLaplace_one m r hm hmnonneg hr T hT hpos
  obtain ⟨hsquared, hauc, hslope, -⟩ := ChronologyReportLaw.metric_values_chronologyLaw
    (donorFraction m T) (normalisedCoupling m r T) (donorFraction_nonneg m hmnonneg T hT)
    (donorFraction_lt_one m T).le
    ((Real.exp_pos _).le.trans (AttainableChronologyCurve.exp_neg_le_normalisedCoupling m r hm hr
      hmnonneg hrnonneg T hT hpos))
    (AttainableChronologyCurve.normalisedCoupling_le_one m r hm hr hmnonneg hrnonneg T hT hpos)
    hpos (donorFraction_lt_one m T)
  refine ⟨hsquared.trans (by rw [hcoupling]), hauc.trans (by rw [hcoupling]),
    hslope.trans hcoupling⟩

/-- The frozen discovery population of NOTE1 section 6.1 has population squared correlation one,
so the source-relative portability ratio of a chronology is its target squared correlation
`L_ν(1)²`. Assumes: `0 < p < 1`. -/
theorem squaredCorrelation_frozenSource (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (chronologyLaw p 1 hp0.le hp1.le zero_le_one le_rfl).squaredCorrelation
      ChronologyReportLaw.scoreOf ChronologyReportLaw.outcomeOf = some 1 := by
  rw [(ChronologyReportLaw.metric_values_chronologyLaw p 1 hp0.le hp1.le zero_le_one le_rfl hp0
    hp1).1, one_pow]

/-- **Equal source law and equal exposure law give one target law.** Two chronologies whose frozen
discovery laws agree and whose exposure laws agree have the same target cell masses, so every target
metric and every source-relative portability quantity agrees. Assumes: continuous rates, nonnegative
migration rates, forward horizons and positive donor fractions. -/
theorem chronologyMass_eq_of_source_eq_of_exposureLaw_eq (m₁ r₁ m₂ r₂ : ℝ → ℝ)
    (hm₁ : Continuous m₁) (hmnonneg₁ : ∀ s, 0 ≤ m₁ s) (hr₁ : Continuous r₁)
    (hm₂ : Continuous m₂) (hmnonneg₂ : ∀ s, 0 ≤ m₂ s) (hr₂ : Continuous r₂) (T₁ T₂ : ℝ)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (hpos₁ : 0 < donorFraction m₁ T₁)
    (hpos₂ : 0 < donorFraction m₂ T₂)
    (hsource : chronologyMass (donorFraction m₁ T₁) 1 = chronologyMass (donorFraction m₂ T₂) 1)
    (hexposure : chronologyExposureLaw m₁ r₁ T₁ = chronologyExposureLaw m₂ r₂ T₂) :
    chronologyMass (donorFraction m₁ T₁) (normalisedCoupling m₁ r₁ T₁) =
      chronologyMass (donorFraction m₂ T₂) (normalisedCoupling m₂ r₂ T₂) := by
  rw [chronologyMass_eq_transportMass (donorFraction m₁ T₁),
    chronologyMass_eq_transportMass (donorFraction m₂ T₂), hsource,
    normalisedCoupling_eq_measureLaplace_one m₁ r₁ hm₁ hmnonneg₁ hr₁ T₁ hT₁ hpos₁,
    normalisedCoupling_eq_measureLaplace_one m₂ r₂ hm₂ hmnonneg₂ hr₂ T₂ hT₂ hpos₂, hexposure]

/-- **The plug-in estimator in NOTE1's model.** From `n` replicas of the frozen discovery
population, the transported expectation with coupling `C` of a metric bounded by `bound` has
expected absolute error at most `2 bound √(3/n)` against the target expectation.
Assumes: `0 < n`, `0 ≤ p ≤ 1`, `0 ≤ C ≤ 1` and a bounded metric. -/
theorem expectation_abs_plugIn_chronologyLaw_sub_le (count : ℕ) (hcount : 0 < count) (p C : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) {metric : Bool × Bool → ℝ}
    {bound : ℝ} (hmetric : ∀ cell, |metric cell| ≤ bound) :
    (replicaLaw count (chronologyLaw p 1 hp0 hp1 zero_le_one le_rfl)).expectation
        (fun draw ↦ |transportExpectation (empiricalMass draw) C metric -
          (chronologyLaw p C hp0 hp1 hC0 hC1).expectation metric|) ≤
      2 * bound * Real.sqrt (3 / count) := by
  have hplug := expectation_abs_plugIn_sub_le count hcount
    (chronologyLaw p 1 hp0 hp1 zero_le_one le_rfl) (false, false) hC0 hC1 hmetric
  have hcard : ((Fintype.card (Bool × Bool) : ℕ) : ℝ) - 1 = 3 := by
    norm_num [Fintype.card_prod, Fintype.card_bool]
  rw [hcard] at hplug
  rw [expectation_chronologyLaw_eq_transportExpectation]
  exact hplug

/-- The three-block chronology with late exposure `b` has the coupling of the point mass `δ_b`:
its coupling is the transform `L_{δ_b}(1)`. Assumes: a positive migration total. -/
theorem couplingOfState_threeBlockHistory_eq_measureLaplace (bexp mtot rtot : ℝ)
    (hm : 0 < mtot) :
    AttainableChronologyCurve.couplingOfState (AdmixtureChronologyLaw.runEvents
        (AttainableChronologyCurve.threeBlockHistory bexp mtot rtot) (0, 0)) =
      measureLaplace (Measure.dirac bexp) 1 := by
  rw [AttainableChronologyCurve.couplingOfState_threeBlockHistory bexp mtot rtot hm,
    (ExposureLaplaceConstraints.measureLaplace_dirac bexp 1).2, one_mul]

/-- **The information boundary at `M = R = log 2`.** The migration-first and recombination-first
chronologies share one source law, and every estimator of the target squared correlation from any
number of source replicas has worst-case error at least `3/8`. The plug-in values `L_ν(1)²` of the
point masses `δ_{log 2}` and `δ_0` are the target values `1/4` and `1` exactly. -/
theorem logTwo_informationBoundary (base : FiniteReportLaw (Bool × Bool)) (n : ℕ) :
    (∀ estimator : (Fin n → Bool × Bool) → ℝ,
      3 / 8 ≤ max ((FourCellCohortLaw.cohortLaw (PortabilityMinimaxLowerBound.sourceCohortLaw 0
            le_rfl zero_le_one base (Real.log 2) (Real.log 2) (Real.log_nonneg one_le_two)
            (Real.log_nonneg one_le_two)) n).expectation
          fun sample ↦ |estimator sample - 1 / 4|)
        ((FourCellCohortLaw.cohortLaw (PortabilityMinimaxLowerBound.sourceCohortLaw 0 le_rfl
            zero_le_one base 0 (Real.log 2) le_rfl (Real.log_nonneg one_le_two)) n).expectation
          fun sample ↦ |estimator sample - 1|)) ∧
      measureLaplace (Measure.dirac (Real.log 2)) 1 ^ 2 = 1 / 4 ∧
      measureLaplace (Measure.dirac 0) 1 ^ 2 = 1 := by
  refine ⟨fun estimator ↦ ?_, ?_, ?_⟩
  · have hbound := PortabilityMinimaxLowerBound.logTwo_sourceCohort_lowerBound 0 le_rfl
      zero_le_one base n estimator
    rwa [zero_div, mul_zero, sub_zero, max_eq_right zero_le_one, mul_one] at hbound
  · rw [(ExposureLaplaceConstraints.measureLaplace_dirac (Real.log 2) 1).2, one_mul,
      AttainableChronologyCurve.exp_neg_log_two]
    norm_num
  · rw [(ExposureLaplaceConstraints.measureLaplace_dirac 0 1).2, mul_zero, neg_zero,
      Real.exp_zero, one_pow]

end Chronology

end

end Descent.Portability.PortabilityIdentification
