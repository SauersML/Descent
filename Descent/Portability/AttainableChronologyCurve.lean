/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdmixtureChronologyLaw
import Descent.Portability.ExposureLaplaceConstraints
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

assert_below Descent.Decision Descent.Program

/-!
# The attainable coupling curve at fixed demographic totals

NOTE1 Theorem 5 fixes the two demographic totals of an admixture chronology, the migration
total `M > 0` and the recombination total `R ≥ 0`, and lets the chronology vary. The donor
fraction is then pinned at `p = 1 - e^{-M}`, while the normalised coupling `C` is free in
exactly the interval `[e^{-R}, 1]`, which is NOTE1 (33). This module proves both halves.

The upper and lower bounds are proved for the continuous chronology of
`AdmixtureChronologyLaw`, from the exposure representation (29): the coupling is the
immigration-increment average of `e^{-b}` where the remaining recombination exposure `b`
satisfies `0 ≤ b ≤ R` whenever the recombination rate is nonnegative and time runs forward,
and the immigration increments themselves integrate to the donor fraction. Averaging a
quantity confined to `[e^{-R}, 1]` against weights of total mass `p` and dividing by `p` gives
a value confined to the same interval.

Attainment is proved for the ordered-event recursion of `AdmixtureChronologyLaw`, whose two
steps are theorems about the solutions of (27) rather than stipulations. The three-block
history of NOTE1 Theorem 5 spends exposure `R - b` on a monomorphic recipient, then the whole
migration total, then the remaining exposure `b`; it has the prescribed totals and coupling
exactly `e^{-b}`. As `b` runs over `[0, R]` the coupling runs over all of `[e^{-R}, 1]`, so the
attainable set of metric vectors is exactly the image of that interval under the NOTE1
section 6.2 table map, in both directions. The worked example `M = R = log 2` is checked in
both orders, giving coupling one half and coupling one.

The two halves meet in `chronologyReportLaw`: for a forward-time chronology with nonnegative
continuous rates and a positive migration total, the pair `(p, C)` is proved to lie in the unit
square, so NOTE1 (31) applies to it and the whole section 6.2 metric table is a function of the
chronology alone.

The exposure law itself is built as a measure. `incrementMeasure m T` is the
immigration-increment measure `dA(s) = m(s) e^{-M(s)} ds` on `(0, T]`, and
`chronologyExposureLaw m r T` is its pushforward by the remaining recombination exposure
`B(s) = R(T) - R(s)`, normalised by the donor fraction. For continuous rates with a nonnegative
migration rate, a forward horizon and a positive donor fraction it is a probability measure
(`isProbabilityMeasure_chronologyExposureLaw`); it is carried by `[0, R(T)]` when the
recombination rate is nonnegative (`chronologyExposureLaw_ae_mem_Icc`); and the coupling of the
recombination history scaled by `λ` is its transform `measureLaplace ν λ` for every `λ`
(`scaled_normalisedCoupling_eq_measureLaplace`), which is NOTE1 (29) and (30) in measure form.

Not proved here: that every chronology with the given totals is equivalent to a three-block
one. The attainment half uses the three-block family only, which is all NOTE1 Theorem 5 claims,
and the bounds half covers every continuous chronology.

## Empirical status

None. The bodies here are calculus and algebra: the demographic totals and the chronology are
stated parameters of a stated mechanism, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AttainableChronologyCurve

open Descent.Portability.AdmixtureChronologyLaw

noncomputable section

/-- The donor fraction is the total immigration increment: `p T = ∫₀ᵀ m e^{-M}`, which is the
`dA` weight of NOTE1 Theorem 4. -/
theorem donorFraction_eq_integral (m : ℝ → ℝ) (hm : Continuous m) (T : ℝ) :
    donorFraction m T = ∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (donorFraction m) (m s * Real.exp (-cumulativeRate m s)) s := by
    intro s _
    have hstep := hasDerivAt_donorFraction m hm s
    rwa [one_sub_donorFraction] at hstep
  have hcont : Continuous (fun s ↦ m s * Real.exp (-cumulativeRate m s)) :=
    hm.mul (((continuous_cumulativeRate m hm).neg).rexp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _),
    donorFraction_zero, sub_zero]

/-- The recombination exposure still to be met by material arriving at time `s` is the
recombination accumulated after `s`. -/
theorem cumulativeRate_sub_eq_integral (r : ℝ → ℝ) (hr : Continuous r) (s T : ℝ) :
    cumulativeRate r T - cumulativeRate r s = ∫ u in s..T, r u := by
  unfold cumulativeRate
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hr.intervalIntegrable 0 s) (hr.intervalIntegrable s T)]
  ring

/-- NOTE1 (33), upper bound: the normalised coupling never exceeds one, because the survival
factor of a nonnegative remaining exposure never does. -/
theorem normalisedCoupling_le_one (m r : ℝ → ℝ) (hm : Continuous m) (hr : Continuous r)
    (hmnn : ∀ s, 0 ≤ m s) (hrnn : ∀ s, 0 ≤ r s) (T : ℝ) (hT : 0 ≤ T)
    (hpos : 0 < donorFraction m T) : normalisedCoupling m r T ≤ 1 := by
  have hw : Continuous (fun s ↦ m s * Real.exp (-cumulativeRate m s)) :=
    hm.mul (((continuous_cumulativeRate m hm).neg).rexp)
  have hwf : Continuous (fun s ↦ m s * Real.exp (-cumulativeRate m s) *
      Real.exp (-(cumulativeRate r T - cumulativeRate r s))) :=
    hw.mul (((continuous_const.sub (continuous_cumulativeRate r hr)).neg).rexp)
  have hmono : (∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) *
      Real.exp (-(cumulativeRate r T - cumulativeRate r s))) ≤
      ∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) := by
    refine intervalIntegral.integral_mono_on hT (hwf.intervalIntegrable _ _)
      (hw.intervalIntegrable _ _) ?_
    intro s hs
    have hwnn : 0 ≤ m s * Real.exp (-cumulativeRate m s) :=
      mul_nonneg (hmnn s) (Real.exp_pos _).le
    have hexposure : 0 ≤ cumulativeRate r T - cumulativeRate r s := by
      rw [cumulativeRate_sub_eq_integral r hr s T]
      exact intervalIntegral.integral_nonneg hs.2 (fun u _ ↦ hrnn u)
    have hsurvival : Real.exp (-(cumulativeRate r T - cumulativeRate r s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [hwnn, hsurvival]
  rw [normalisedCoupling_eq_exposure_integral m r T hpos, one_div, inv_mul_eq_div,
    div_le_one hpos, donorFraction_eq_integral m hm T]
  exact hmono

/-- NOTE1 (33), lower bound: the normalised coupling is at least the survival factor of the
whole recombination total, because no arrival meets more exposure than that. -/
theorem exp_neg_le_normalisedCoupling (m r : ℝ → ℝ) (hm : Continuous m) (hr : Continuous r)
    (hmnn : ∀ s, 0 ≤ m s) (hrnn : ∀ s, 0 ≤ r s) (T : ℝ) (hT : 0 ≤ T)
    (hpos : 0 < donorFraction m T) :
    Real.exp (-cumulativeRate r T) ≤ normalisedCoupling m r T := by
  have hw : Continuous (fun s ↦ m s * Real.exp (-cumulativeRate m s)) :=
    hm.mul (((continuous_cumulativeRate m hm).neg).rexp)
  have hwf : Continuous (fun s ↦ m s * Real.exp (-cumulativeRate m s) *
      Real.exp (-(cumulativeRate r T - cumulativeRate r s))) :=
    hw.mul (((continuous_const.sub (continuous_cumulativeRate r hr)).neg).rexp)
  have hmono : (∫ s in (0 : ℝ)..T, Real.exp (-cumulativeRate r T) *
      (m s * Real.exp (-cumulativeRate m s))) ≤
      ∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) *
        Real.exp (-(cumulativeRate r T - cumulativeRate r s)) := by
    refine intervalIntegral.integral_mono_on hT
      ((continuous_const.mul hw).intervalIntegrable _ _) (hwf.intervalIntegrable _ _) ?_
    intro s hs
    have hwnn : 0 ≤ m s * Real.exp (-cumulativeRate m s) :=
      mul_nonneg (hmnn s) (Real.exp_pos _).le
    have hearlier : 0 ≤ cumulativeRate r s := cumulativeRate_nonneg r hrnn s hs.1
    have hsurvival : Real.exp (-cumulativeRate r T) ≤
        Real.exp (-(cumulativeRate r T - cumulativeRate r s)) :=
      Real.exp_le_exp.mpr (by linarith)
    nlinarith [hwnn, hsurvival]
  rw [intervalIntegral.integral_const_mul, ← donorFraction_eq_integral m hm T] at hmono
  rw [normalisedCoupling_eq_exposure_integral m r T hpos, one_div, inv_mul_eq_div,
    le_div_iff₀ hpos]
  linarith [hmono]

/-- The three-block history of NOTE1 Theorem 5: recombination exposure `rtot - bexp` while the
recipient is still monomorphic, then the whole migration total, then the remaining exposure
`bexp`. -/
def threeBlockHistory (bexp mtot rtot : ℝ) : List ChronologyEvent :=
  [ChronologyEvent.recombination (rtot - bexp), ChronologyEvent.migration mtot,
    ChronologyEvent.recombination bexp]

/-- The state after the three-block history: donor fraction `1 - e^{-M}` and linkage
`e^{-M}(1 - e^{-M}) e^{-b}`. -/
theorem runEvents_threeBlockHistory (bexp mtot rtot : ℝ) :
    runEvents (threeBlockHistory bexp mtot rtot) (0, 0) =
      (1 - Real.exp (-mtot),
        Real.exp (-mtot) * (1 - Real.exp (-mtot)) * Real.exp (-bexp)) := by
  simp only [threeBlockHistory, runEvents_cons, runEvents_nil, stepEvent_recombination,
    stepEvent_migration, Prod.mk.injEq]
  constructor <;> ring

/-- The three-block history supplies exactly the prescribed migration total. -/
theorem migrationTotal_threeBlockHistory (bexp mtot rtot : ℝ) :
    ((threeBlockHistory bexp mtot rtot).map eventMigration).sum = mtot := by
  simp [threeBlockHistory, eventMigration]

/-- The three-block history supplies exactly the prescribed recombination total. -/
theorem recombinationTotal_threeBlockHistory (bexp mtot rtot : ℝ) :
    ((threeBlockHistory bexp mtot rtot).map eventRecombination).sum = rtot := by
  simp [threeBlockHistory, eventRecombination]

/-- The normalised coupling read off an ordered-event state `(p, D)`, the counterpart for the
piecewise chronology of `normalisedCoupling` for the continuous one. -/
def couplingOfState (state : ℝ × ℝ) : ℝ := state.2 / (state.1 * (1 - state.1))

/-- The three-block history realises coupling exactly `e^{-b}`, where `b` is the recombination
exposure it places after the migration. -/
theorem couplingOfState_threeBlockHistory (bexp mtot rtot : ℝ) (hmpos : 0 < mtot) :
    couplingOfState (runEvents (threeBlockHistory bexp mtot rtot) (0, 0)) =
      Real.exp (-bexp) := by
  have hlt : Real.exp (-mtot) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgt : (0 : ℝ) < Real.exp (-mtot) := Real.exp_pos _
  have hne : (1 - Real.exp (-mtot)) * (1 - (1 - Real.exp (-mtot))) ≠ 0 := by
    have hrewrite : (1 : ℝ) - (1 - Real.exp (-mtot)) = Real.exp (-mtot) := by ring
    rw [hrewrite]
    exact ne_of_gt (mul_pos (by linarith) hgt)
  unfold couplingOfState
  simp only [runEvents_threeBlockHistory]
  rw [div_eq_iff hne]
  ring

/-- NOTE1 Theorem 5 with (33): at fixed totals the couplings attainable by an ordered
three-block history are exactly the interval `[e^{-R}, 1]`. -/
theorem attainable_coupling_range (mtot rtot : ℝ) (hmpos : 0 < mtot) :
    {coupling : ℝ | ∃ bexp ∈ Set.Icc (0 : ℝ) rtot,
        couplingOfState (runEvents (threeBlockHistory bexp mtot rtot) (0, 0)) = coupling} =
      Set.Icc (Real.exp (-rtot)) 1 := by
  ext coupling
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨bexp, hmem, rfl⟩
    rw [couplingOfState_threeBlockHistory bexp mtot rtot hmpos]
    exact ⟨Real.exp_le_exp.mpr (by linarith [hmem.2]),
      Real.exp_le_one_iff.mpr (by linarith [hmem.1])⟩
  · rintro ⟨hlow, hhigh⟩
    have hcpos : 0 < coupling := lt_of_lt_of_le (Real.exp_pos _) hlow
    refine ⟨-Real.log coupling, ⟨?_, ?_⟩, ?_⟩
    · have hnp : Real.log coupling ≤ 0 := Real.log_nonpos hcpos.le hhigh
      linarith
    · have hge : -rtot ≤ Real.log coupling := (Real.le_log_iff_exp_le hcpos).mpr hlow
      linarith
    · rw [couplingOfState_threeBlockHistory _ mtot rtot hmpos, neg_neg,
        Real.exp_log hcpos]

/-- The NOTE1 section 6.2 metric table as an explicit function of the donor fraction and the
coupling: AUC, calibration slope, calibration intercept, Brier loss, repaired Brier loss,
accuracy at an interior threshold, and discrete calibration error. -/
def metricTable (p C : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  ((1 + C) / 2, C, p * (1 - C), 2 * (p * (1 - p)) * (1 - C), p * (1 - p) * (1 - C ^ 2),
    1 - 2 * (p * (1 - p)) * (1 - C), 2 * (p * (1 - p)) * (1 - C))

/-- The same seven numbers read off a report law on the pair (score, outcome). -/
def reportMetrics (law : FiniteReportLaw (Bool × Bool)) :
    ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  (ChronologyReportLaw.populationAUC law, ChronologyReportLaw.linearSlope law,
    ChronologyReportLaw.linearIntercept law,
    law.meanSquaredError ChronologyReportLaw.scoreOf ChronologyReportLaw.outcomeOf,
    ChronologyReportLaw.repairedBrier law,
    ChronologyReportLaw.thresholdAccuracy law (1 / 2),
    ChronologyReportLaw.discreteECE law)

/-- The report law of NOTE1 (31) reports exactly the table entries. -/
theorem reportMetrics_chronologyLaw (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hlow : 0 < p) (hhigh : p < 1) :
    reportMetrics (ChronologyReportLaw.chronologyLaw p C hp0 hp1 hC0 hC1) =
      metricTable p C := by
  unfold reportMetrics metricTable
  rw [ChronologyReportLaw.populationAUC_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    ChronologyReportLaw.linearSlope_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    ChronologyReportLaw.linearIntercept_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    ChronologyReportLaw.meanSquaredError_chronologyLaw p C hp0 hp1 hC0 hC1,
    ChronologyReportLaw.repairedBrier_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh,
    ChronologyReportLaw.thresholdAccuracy_chronologyLaw p C (1 / 2) hp0 hp1 hC0 hC1
      (by norm_num) (by norm_num),
    ChronologyReportLaw.discreteECE_chronologyLaw p C hp0 hp1 hC0 hC1 hlow hhigh]

/-- NOTE1 Theorem 5, the curve statement: at fixed totals the attainable metric vectors are
exactly the image of the coupling interval `[e^{-R}, 1]` under the table map, in both
directions. -/
theorem attainable_metric_curve (mtot rtot : ℝ) (hmpos : 0 < mtot) :
    metricTable (1 - Real.exp (-mtot)) ''
        {coupling : ℝ | ∃ bexp ∈ Set.Icc (0 : ℝ) rtot,
          couplingOfState (runEvents (threeBlockHistory bexp mtot rtot) (0, 0)) = coupling} =
      metricTable (1 - Real.exp (-mtot)) '' Set.Icc (Real.exp (-rtot)) 1 := by
  rw [attainable_coupling_range mtot rtot hmpos]

/-- The report law of the chronology itself: NOTE1 (31) instantiated at the donor fraction and
normalised coupling that a forward-time chronology with nonnegative continuous rates and a
positive migration total produces. The four range hypotheses NOTE1 (31) needs are discharged
by the bounds above rather than assumed. -/
def chronologyReportLaw (m r : ℝ → ℝ) (hm : Continuous m) (hr : Continuous r)
    (hmnn : ∀ s, 0 ≤ m s) (hrnn : ∀ s, 0 ≤ r s) (T : ℝ) (hT : 0 ≤ T)
    (hmig : 0 < cumulativeRate m T) : FiniteReportLaw (Bool × Bool) :=
  ChronologyReportLaw.chronologyLaw (donorFraction m T) (normalisedCoupling m r T)
    (donorFraction_nonneg m hmnn T hT) (le_of_lt (donorFraction_lt_one m T))
    (le_trans (Real.exp_pos _).le
      (exp_neg_le_normalisedCoupling m r hm hr hmnn hrnn T hT (donorFraction_pos m T hmig)))
    (normalisedCoupling_le_one m r hm hr hmnn hrnn T hT (donorFraction_pos m T hmig))

/-- A chronology determines the whole NOTE1 section 6.2 metric table, and only through its
donor fraction and its normalised coupling. -/
theorem reportMetrics_chronologyReportLaw (m r : ℝ → ℝ) (hm : Continuous m)
    (hr : Continuous r) (hmnn : ∀ s, 0 ≤ m s) (hrnn : ∀ s, 0 ≤ r s) (T : ℝ) (hT : 0 ≤ T)
    (hmig : 0 < cumulativeRate m T) :
    reportMetrics (chronologyReportLaw m r hm hr hmnn hrnn T hT hmig) =
      metricTable (donorFraction m T) (normalisedCoupling m r T) := by
  unfold chronologyReportLaw
  exact reportMetrics_chronologyLaw _ _ _ _ _ _ (donorFraction_pos m T hmig)
    (donorFraction_lt_one m T)

/-- The survival factor of the worked example's totals. -/
theorem exp_neg_log_two : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- NOTE1 section 6.2 worked example, migration first: with `M = R = log 2` and all
recombination after the migration the state is donor fraction one half and linkage one eighth,
so the coupling is one half. -/
theorem threeBlock_migration_first :
    runEvents (threeBlockHistory (Real.log 2) (Real.log 2) (Real.log 2)) (0, 0) =
        (1 / 2, 1 / 8) ∧
      couplingOfState
        (runEvents (threeBlockHistory (Real.log 2) (Real.log 2) (Real.log 2)) (0, 0)) =
          1 / 2 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · rw [runEvents_threeBlockHistory, exp_neg_log_two, Prod.mk.injEq]
    constructor <;> norm_num
  · rw [couplingOfState_threeBlockHistory _ _ _ hlog, exp_neg_log_two]

/-- The same totals with all recombination before the migration leave the loci fully coupled:
linkage one quarter and coupling one. -/
theorem threeBlock_recombination_first :
    runEvents (threeBlockHistory 0 (Real.log 2) (Real.log 2)) (0, 0) = (1 / 2, 1 / 4) ∧
      couplingOfState (runEvents (threeBlockHistory 0 (Real.log 2) (Real.log 2)) (0, 0)) =
        1 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · rw [runEvents_threeBlockHistory, exp_neg_log_two, Prod.mk.injEq]
    constructor <;> norm_num
  · rw [couplingOfState_threeBlockHistory _ _ _ hlog]
    norm_num

open MeasureTheory
open scoped ENNReal NNReal
open Descent.Portability.ExposureLaplaceConstraints (measureLaplace)

/-- The immigration-increment measure `dA(s) = m(s) e^{-M(s)} ds` of NOTE1 Theorem 4 on the
interval `(0, T]`. -/
def incrementMeasure (m : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 T)).withDensity
    fun s ↦ ((m s * Real.exp (-cumulativeRate m s)).toNNReal : ℝ≥0∞)

/-- NOTE1 Theorem 4: the exposure law `ν` of a chronology, the pushforward of the normalised
immigration increments `dA / p` by the remaining recombination exposure `B(s) = R(T) - R(s)`. -/
def chronologyExposureLaw (m r : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / donorFraction m T) •
    Measure.map (fun s ↦ cumulativeRate r T - cumulativeRate r s) (incrementMeasure m T)

/-- NOTE1 (29) and (30) in measure form. Assumes: continuous rates, a nonnegative migration
rate, a forward horizon `0 ≤ T` and a positive donor fraction. The coupling of the recombination
history scaled by `λ` is the transform `∫ e^{-λ b} ν(db)` of the one exposure law `ν`. -/
theorem scaled_normalisedCoupling_eq_measureLaplace (m r : ℝ → ℝ) (hm : Continuous m)
    (hmnonneg : ∀ s, 0 ≤ m s) (hr : Continuous r) (lam T : ℝ) (hT : 0 ≤ T)
    (hpos : 0 < donorFraction m T) :
    normalisedCoupling m (fun s ↦ lam * r s) T =
      measureLaplace (chronologyExposureLaw m r T) lam := by
  have hremaining : Continuous fun s ↦ cumulativeRate r T - cumulativeRate r s :=
    continuous_const.sub (continuous_cumulativeRate r hr)
  have hdensity : Continuous fun s ↦ m s * Real.exp (-cumulativeRate m s) :=
    hm.mul (continuous_cumulativeRate m hm).neg.rexp
  have hmeasurable : Measurable fun s ↦ (m s * Real.exp (-cumulativeRate m s)).toNNReal :=
    (continuous_real_toNNReal.comp hdensity).measurable
  rw [scaled_normalisedCoupling_eq_exposure_integral m r lam T hpos]
  unfold measureLaplace chronologyExposureLaw incrementMeasure
  rw [integral_smul_measure, integral_map hremaining.measurable.aemeasurable
      (by fun_prop : Continuous fun b : ℝ ↦ Real.exp (-(lam * b))).aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hmeasurable,
    ENNReal.toReal_ofReal (one_div_pos.mpr hpos).le, smul_eq_mul,
    intervalIntegral.integral_of_le hT]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun s _ ↦ ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (mul_nonneg (hmnonneg s) (Real.exp_pos _).le)]

/-- NOTE1 Theorem 4: the exposure law of a chronology has total mass one. Assumes: continuous
rates, a nonnegative migration rate, a forward horizon and a positive donor fraction. The
immigration increments integrate to the donor fraction, which the normalisation divides out. -/
theorem chronologyExposureLaw_univ (m r : ℝ → ℝ) (hm : Continuous m) (hmnonneg : ∀ s, 0 ≤ m s)
    (hr : Continuous r) (T : ℝ) (hT : 0 ≤ T) (hpos : 0 < donorFraction m T) :
    chronologyExposureLaw m r T Set.univ = 1 := by
  have hremaining : Measurable fun s ↦ cumulativeRate r T - cumulativeRate r s :=
    (continuous_const.sub (continuous_cumulativeRate r hr)).measurable
  have hdensity : Continuous fun s ↦ m s * Real.exp (-cumulativeRate m s) :=
    hm.mul (continuous_cumulativeRate m hm).neg.rexp
  have hmass : ∫⁻ s in Set.Ioc 0 T,
      ((m s * Real.exp (-cumulativeRate m s)).toNNReal : ℝ≥0∞) =
        ENNReal.ofReal (donorFraction m T) := by
    rw [donorFraction_eq_integral m hm T, intervalIntegral.integral_of_le hT,
      ofReal_integral_eq_lintegral_ofReal
        (hdensity.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (ae_of_all _ fun s ↦ mul_nonneg (hmnonneg s) (Real.exp_pos _).le)]
    rfl
  unfold chronologyExposureLaw incrementMeasure
  rw [Measure.smul_apply, Measure.map_apply hremaining MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass, smul_eq_mul,
    ← ENNReal.ofReal_mul (one_div_pos.mpr hpos).le, one_div_mul_cancel (ne_of_gt hpos),
    ENNReal.ofReal_one]

/-- The exposure law of a forward chronology with continuous rates, a nonnegative migration
rate and a positive donor fraction is a probability measure. -/
theorem isProbabilityMeasure_chronologyExposureLaw (m r : ℝ → ℝ) (hm : Continuous m)
    (hmnonneg : ∀ s, 0 ≤ m s) (hr : Continuous r) (T : ℝ) (hT : 0 ≤ T)
    (hpos : 0 < donorFraction m T) :
    IsProbabilityMeasure (chronologyExposureLaw m r T) :=
  ⟨chronologyExposureLaw_univ m r hm hmnonneg hr T hT hpos⟩

/-- NOTE1 Theorem 4: the exposure law is carried by `[0, R(T)]`. Assumes: a continuous
nonnegative recombination rate. Material arriving at a time `s ∈ (0, T]` still has between none
and all of the recombination total to meet. -/
theorem chronologyExposureLaw_ae_mem_Icc (m r : ℝ → ℝ) (hr : Continuous r)
    (hrnonneg : ∀ s, 0 ≤ r s) (T : ℝ) :
    ∀ᵐ exposure ∂chronologyExposureLaw m r T, exposure ∈ Set.Icc 0 (cumulativeRate r T) := by
  have hremaining : Measurable fun s ↦ cumulativeRate r T - cumulativeRate r s :=
    (continuous_const.sub (continuous_cumulativeRate r hr)).measurable
  unfold chronologyExposureLaw incrementMeasure
  refine Measure.ae_smul_measure ?_ _
  refine (ae_map_iff hremaining.aemeasurable
    (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (cumulativeRate r T)))).mpr ?_
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ Set.mem_Icc.mpr ⟨?_, ?_⟩
  · show 0 ≤ cumulativeRate r T - cumulativeRate r s
    rw [cumulativeRate_sub_eq_integral r hr s T]
    exact intervalIntegral.integral_nonneg hs.2 fun u _ ↦ hrnonneg u
  · show cumulativeRate r T - cumulativeRate r s ≤ cumulativeRate r T
    linarith [cumulativeRate_nonneg r hrnonneg s hs.1.le]

end

end Descent.Portability.AttainableChronologyCurve
