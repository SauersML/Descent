/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PolygenicPortabilityDecay

assert_below Descent.Decision Descent.Program

/-!
# Calibration portability along divergence time

`TwoLocusPortabilityDecay` and `PolygenicPortabilityDecay` give the portability of a tag-locus
score in closed form along divergence time, as a ratio of cross-population expected squared
correlations.  Neither carries calibration: the slope of the regression of the outcome on the
score, covariance of score and outcome over score variance, as in
`PortabilityMasterTheorem.DeploymentPopulation.calibrationSlope`.  This module adds it and
compares it with the squared correlation.

## The model

A score is trained in the source on tag–causal pairs `p` and read in the target.  Genotypes are
standardized in each deme, and different pairs are in linkage equilibrium with each other.  The
outcome is `Y = ∑_p β_p X^causal_p + ε` with environmental variance `σ²_e`.  Pair `p` has
tag–causal correlation `r^S_p` in the source and `r^T_p` in the target.  The trained weight is the
source marginal regression coefficient `w_p = β_p r^S_p` (`trainedWeight`).  In a deme with
correlations `r` the score–outcome covariance is `∑_p w_p β_p r_p` (`predictiveCovariance`), the
score variance is `∑_p w_p²` in both demes (`trainedScoreVariance`), and the outcome variance is
`∑_p β_p² + σ²_e` (`outcomeVariance`).  The calibration slope is covariance over score variance
(`calibrationSlope`), and the squared correlation is squared covariance over the product of the
variances (`squaredCorrelation`).  Portability is the target value over the source value
(`calibrationPortability`, `squaredCorrelationPortability`).

## Main results

- `calibrationSlope_source`: in the source the trained score has slope `1`.
- `squaredCorrelationPortability_eq_calibrationPortability_sq`: squared-correlation portability
  is the square of calibration portability.  Both variances are the same in the two demes, so only
  the covariance moves: once in the slope, twice in the squared correlation.
- `calibrationSlope_retained`: if pair `p` keeps the fraction `κ_p` of its source correlation,
  `r^T_p = κ_p r^S_p`, the target slope is `∑_p ω_p κ_p`, with the trained signal shares
  `ω_p = w_p² / ∑_q w_q²` (`trainedShare`, `trainedShare_nonneg`, `sum_trainedShare`).
- `calibrationPortability_decay`, `squaredCorrelationPortability_decay`: with retention
  `κ_p = e^{-x_p T}` along divergence time `T` (`portabilityDecay`), calibration portability is
  the weighted decay `∑_p ω_p e^{-x_p T}` of `PolygenicPortabilityDecay` (`polygenicDecay`), and
  squared-correlation portability is its square.
- `calibrationPortability_commonRate`, `squaredCorrelationPortability_commonRate`,
  `portabilityDecay_sq`: at one rate `x`, calibration portability is `e^{-xT}` and
  squared-correlation portability is `e^{-2xT}`.  They are different functions of one decay
  factor.
- `tendsto_calibrationPortability_decay`, `tendsto_squaredCorrelationPortability_decay`: as
  `T → ∞` calibration portability tends to the coverage floor `∑_{p : x_p = 0} ω_p`
  (`coverageFloor`), and squared-correlation portability tends to its square.
- `calibrationPortability_decay_antitone`, `squaredCorrelationPortability_decay_antitone`: both
  decrease with divergence time.
- `squaredCorrelationPortability_decay_le`: squared-correlation portability never exceeds
  calibration portability.  `squaredCorrelationPortability_decay_lt`: at every positive time, if a
  pair that carries signal loses correlation at a positive rate, `0 < R²-portability <
  calibration portability < 1`.  `squaredCorrelationPortability_eq_calibrationPortability_iff`:
  the two are equal exactly when calibration portability is `0` or `1`, as at the split
  (`calibrationPortability_decay_zero`).
- `squaredCorrelationPortability_decay_le_polygenicDecay`: squared-correlation portability is at
  most the signal-weighted mean `∑_p ω_p e^{-2 x_p T}` of the per-pair squared retentions
  (`sq_weightedMean_le_weightedMean_sq`).  A polygenic score's squared correlation loses at least
  as much as its average pair.
- `splitPortabilityRatio_eq_mul_portabilityDecay`: the two-locus ratio `e^{-ρ̄T}` of
  `TwoLocusPortabilityDecay.splitPortabilityRatio_eq` is the product
  `e^{-(ρ_S/2) T} e^{-(ρ_T/2) T}` of one factor per deme, and at equal rates the square of one
  factor (`splitPortabilityRatio_eq_sq_portabilityDecay`).
- `splitPortabilityRatio_eq_squaredCorrelationPortability`,
  `calibrationPortability_sq_eq_splitPortabilityRatio`,
  `splitPortabilityRatio_lt_calibrationPortability`: at equal recombination rates the two-locus
  ratio is the squared-correlation portability of a trained score whose pairs retain the one-deme
  factor `e^{-(ρ/2) T}`, the calibration portability of that score is its square root, and for
  `ρ > 0` and `T > 0` the ratio is strictly below it.

## Significance

Calibration decays more slowly than accuracy.  After divergence the trained score's slope falls
to the signal-weighted retention of its pairs, and its squared correlation falls to the square of
that value.  So a score that keeps 80 percent of its slope keeps 64 percent of its `R²`.  The floor
that no divergence removes is the share of signal at zero rate for the slope and the square of
that share for the squared correlation.

## Scope

Genotypes are standardized in each deme, different pairs are in linkage equilibrium, the score is
trained on population parameters with no estimation error, and the effects are shared by the two
demes.  With genotypes in allele counts the score variance moves with the target heterozygosity,
and the square law carries a variance factor.  The retention `κ_p` is an input.  No theorem here
derives the per-deme retention `e^{-(ρ/2) T}` of a correlation from the low-order moment system,
which has no degree-two linkage coordinate.  The bridge theorems equate the two-locus ratio with
the portabilities of a score at that retention.  Migration is not treated: the migration factor
of `MigrationPortabilityFactor` is a ratio of cross moments, and nothing here reads it as a
per-deme retention.

## Empirical status

None.  The bodies are algebra on finite sums and real exponentials, and the corpus decay law.  No
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CalibrationPortabilityDecay

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay
  Descent.Portability.PolygenicPortabilityDecay

noncomputable section

variable {P : Type*} [Fintype P]

/-! ## A source-trained score in standardized units -/

/-- **The trained weight** `w_p = β_p r^S_p` of pair `p`: the source marginal regression
coefficient of the outcome on the standardized tag genotype.

Empirical status: NOT AN EMPIRICAL CLAIM.  A product of two numbers. -/
def trainedWeight (effect sourceCorrelation : P → ℝ) (pair : P) : ℝ :=
  effect pair * sourceCorrelation pair

/-- **The score variance** `∑_p w_p²` of the trained score.  For standardized tag genotypes in
linkage equilibrium it is the same in every deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of squares. -/
def trainedScoreVariance (effect sourceCorrelation : P → ℝ) : ℝ :=
  ∑ pair, trainedWeight effect sourceCorrelation pair ^ 2

/-- **The score–outcome covariance** `∑_p w_p β_p r_p` in a deme whose tag–causal correlations
are `r`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum. -/
def predictiveCovariance (effect sourceCorrelation correlation : P → ℝ) : ℝ :=
  ∑ pair, trainedWeight effect sourceCorrelation pair * effect pair * correlation pair

/-- **The outcome variance** `∑_p β_p² + σ²_e`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum plus a number. -/
def outcomeVariance (effect : P → ℝ) (environment : ℝ) : ℝ :=
  ∑ pair, effect pair ^ 2 + environment

/-- **The calibration slope** `Cov(S, Y) / Var(S)` of the trained score in a deme with
correlations `r`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two finite sums. -/
def calibrationSlope (effect sourceCorrelation correlation : P → ℝ) : ℝ :=
  predictiveCovariance effect sourceCorrelation correlation
    / trainedScoreVariance effect sourceCorrelation

/-- **The squared correlation** `Cov(S, Y)² / (Var(S) Var(Y))` of the trained score in a deme
with correlations `r`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of finite sums. -/
def squaredCorrelation (effect sourceCorrelation correlation : P → ℝ) (environment : ℝ) : ℝ :=
  predictiveCovariance effect sourceCorrelation correlation ^ 2
    / (trainedScoreVariance effect sourceCorrelation * outcomeVariance effect environment)

/-- **Calibration portability**, the target slope over the source slope.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two slopes. -/
def calibrationPortability (effect sourceCorrelation targetCorrelation : P → ℝ) : ℝ :=
  calibrationSlope effect sourceCorrelation targetCorrelation
    / calibrationSlope effect sourceCorrelation sourceCorrelation

/-- **Squared-correlation portability**, the target squared correlation over the source one.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two squared correlations. -/
def squaredCorrelationPortability (effect sourceCorrelation targetCorrelation : P → ℝ)
    (environment : ℝ) : ℝ :=
  squaredCorrelation effect sourceCorrelation targetCorrelation environment
    / squaredCorrelation effect sourceCorrelation sourceCorrelation environment

/-- In the source the covariance of the trained score with the outcome is the score variance. -/
theorem predictiveCovariance_source (effect sourceCorrelation : P → ℝ) :
    predictiveCovariance effect sourceCorrelation sourceCorrelation
      = trainedScoreVariance effect sourceCorrelation := by
  unfold predictiveCovariance trainedScoreVariance trainedWeight
  exact Finset.sum_congr rfl fun pair _ ↦ by ring

/-- **The trained score is calibrated in the source**: its slope is `1`.

Assumes: nonzero score variance. -/
theorem calibrationSlope_source (effect sourceCorrelation : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationSlope effect sourceCorrelation sourceCorrelation = 1 := by
  rw [calibrationSlope, predictiveCovariance_source, div_self hvariance]

/-- Calibration portability is the target slope.

Assumes: nonzero score variance. -/
theorem calibrationPortability_eq (effect sourceCorrelation targetCorrelation : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation targetCorrelation
      = calibrationSlope effect sourceCorrelation targetCorrelation := by
  rw [calibrationPortability, calibrationSlope_source effect sourceCorrelation hvariance,
    div_one]

/-- **Squared-correlation portability is the square of calibration portability.**

Assumes: nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_eq_calibrationPortability_sq
    (effect sourceCorrelation targetCorrelation : P → ℝ) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation targetCorrelation environment
      = calibrationPortability effect sourceCorrelation targetCorrelation ^ 2 := by
  rw [calibrationPortability_eq effect sourceCorrelation targetCorrelation hvariance]
  simp only [squaredCorrelationPortability, squaredCorrelation, predictiveCovariance_source,
    calibrationSlope]
  field_simp <;> ring

/-- **Squared-correlation portability equals calibration portability exactly when calibration
portability is `0` or `1`.**

Assumes: nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_eq_calibrationPortability_iff
    (effect sourceCorrelation targetCorrelation : P → ℝ) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation targetCorrelation environment
        = calibrationPortability effect sourceCorrelation targetCorrelation
      ↔ calibrationPortability effect sourceCorrelation targetCorrelation = 0
        ∨ calibrationPortability effect sourceCorrelation targetCorrelation = 1 := by
  rw [squaredCorrelationPortability_eq_calibrationPortability_sq effect sourceCorrelation
    targetCorrelation environment hvariance houtcome]
  constructor
  · intro h
    have hfactor : calibrationPortability effect sourceCorrelation targetCorrelation
        * (calibrationPortability effect sourceCorrelation targetCorrelation - 1) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  · rintro (h | h) <;> rw [h] <;> norm_num

/-! ## Retention of the source correlations -/

/-- **The trained signal share** `ω_p = w_p² / ∑_q w_q²` of pair `p`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A square over a sum of squares. -/
def trainedShare (effect sourceCorrelation : P → ℝ) (pair : P) : ℝ :=
  trainedWeight effect sourceCorrelation pair ^ 2 / trainedScoreVariance effect sourceCorrelation

/-- The trained signal shares are nonnegative. -/
theorem trainedShare_nonneg (effect sourceCorrelation : P → ℝ) (pair : P) :
    0 ≤ trainedShare effect sourceCorrelation pair :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The trained signal shares sum to one.

Assumes: nonzero score variance. -/
theorem sum_trainedShare (effect sourceCorrelation : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    ∑ pair, trainedShare effect sourceCorrelation pair = 1 := by
  unfold trainedShare
  rw [← Finset.sum_div]
  exact div_self hvariance

/-- A pair with a nonzero effect and a nonzero source correlation makes the score variance
positive.

Assumes: the pair has a nonzero effect and a nonzero source correlation. -/
theorem trainedScoreVariance_pos (effect sourceCorrelation : P → ℝ) {pair : P}
    (heffect : effect pair ≠ 0) (hcorrelation : sourceCorrelation pair ≠ 0) :
    0 < trainedScoreVariance effect sourceCorrelation := by
  have hweight : trainedWeight effect sourceCorrelation pair ≠ 0 :=
    mul_ne_zero heffect hcorrelation
  exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hweight).symm)
    (Finset.single_le_sum (fun other _ ↦ sq_nonneg (trainedWeight effect sourceCorrelation other))
      (Finset.mem_univ pair))

/-- Such a pair carries a positive trained signal share.

Assumes: the pair has a nonzero effect and a nonzero source correlation. -/
theorem trainedShare_pos (effect sourceCorrelation : P → ℝ) {pair : P}
    (heffect : effect pair ≠ 0) (hcorrelation : sourceCorrelation pair ≠ 0) :
    0 < trainedShare effect sourceCorrelation pair := by
  have hweight : trainedWeight effect sourceCorrelation pair ≠ 0 :=
    mul_ne_zero heffect hcorrelation
  exact div_pos (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hweight).symm)
    (trainedScoreVariance_pos effect sourceCorrelation heffect hcorrelation)

/-- A pair with a nonzero effect makes the outcome variance positive.

Assumes: the pair has a nonzero effect, and the environmental variance is nonnegative. -/
theorem outcomeVariance_pos (effect : P → ℝ) {pair : P} (heffect : effect pair ≠ 0)
    {environment : ℝ} (henvironment : 0 ≤ environment) :
    0 < outcomeVariance effect environment := by
  have heffectSq : 0 < effect pair ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 heffect).symm
  have hsum : effect pair ^ 2 ≤ ∑ other, effect other ^ 2 :=
    Finset.single_le_sum (fun other _ ↦ sq_nonneg (effect other)) (Finset.mem_univ pair)
  unfold outcomeVariance
  linarith

/-- **The target slope is the signal-weighted retention.**  If pair `p` keeps the fraction `κ_p`
of its source correlation, the target calibration slope is `∑_p ω_p κ_p`. -/
theorem calibrationSlope_retained (effect sourceCorrelation retention : P → ℝ) :
    calibrationSlope effect sourceCorrelation
        (fun pair ↦ retention pair * sourceCorrelation pair)
      = ∑ pair, trainedShare effect sourceCorrelation pair * retention pair := by
  simp only [calibrationSlope, predictiveCovariance, trainedShare, trainedWeight, Finset.sum_div]
  refine Finset.sum_congr rfl fun pair _ ↦ ?_
  ring

/-! ## Calibration and squared-correlation portability along divergence time -/

/-- **Calibration portability along divergence time is the weighted decay**
`∑_p ω_p e^{-x_p T}`.

Assumes: nonzero score variance. -/
theorem calibrationPortability_decay (effect sourceCorrelation rate : P → ℝ) (duration : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair)
      = polygenicDecay (trainedShare effect sourceCorrelation) rate duration := by
  rw [polygenicDecay, calibrationPortability_eq effect sourceCorrelation _ hvariance,
    calibrationSlope_retained]

/-- **Squared-correlation portability along divergence time is the square of the weighted
decay.**

Assumes: nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_decay (effect sourceCorrelation rate : P → ℝ)
    (environment duration : ℝ) (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment
      = polygenicDecay (trainedShare effect sourceCorrelation) rate duration ^ 2 := by
  rw [squaredCorrelationPortability_eq_calibrationPortability_sq _ _ _ _ hvariance houtcome,
    calibrationPortability_decay _ _ _ _ hvariance]

/-- At the split the trained score keeps its calibration.

Assumes: nonzero score variance. -/
theorem calibrationPortability_decay_zero (effect sourceCorrelation rate : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) 0 * sourceCorrelation pair) = 1 := by
  rw [calibrationPortability_decay effect sourceCorrelation rate 0 hvariance,
    polygenicDecay_zero_duration, sum_trainedShare effect sourceCorrelation hvariance]

/-- **The squared decay is the decay at twice the rate.** -/
theorem portabilityDecay_sq (rate duration : ℝ) :
    portabilityDecay rate duration ^ 2 = portabilityDecay (2 * rate) duration := by
  rw [portabilityDecay, portabilityDecay, sq, ← Real.exp_add]
  congr 1
  ring

/-- **At one rate calibration portability is the decay itself.**

Assumes: nonzero score variance. -/
theorem calibrationPortability_commonRate (effect sourceCorrelation : P → ℝ)
    (rate duration : ℝ) (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay rate duration * sourceCorrelation pair)
      = portabilityDecay rate duration := by
  rw [calibrationPortability_eq effect sourceCorrelation _ hvariance, calibrationSlope_retained,
    ← Finset.sum_mul, sum_trainedShare effect sourceCorrelation hvariance, one_mul]

/-- **At one rate squared-correlation portability is the decay at twice the rate.**

Assumes: nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_commonRate (effect sourceCorrelation : P → ℝ)
    (rate environment duration : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay rate duration * sourceCorrelation pair) environment
      = portabilityDecay (2 * rate) duration := by
  rw [squaredCorrelationPortability_eq_calibrationPortability_sq _ _ _ _ hvariance houtcome,
    calibrationPortability_commonRate _ _ _ _ hvariance, portabilityDecay_sq]

/-- The weighted decay is nonnegative.

Assumes: nonnegative shares. -/
theorem polygenicDecay_nonneg {share : P → ℝ} (hshare : ∀ index, 0 ≤ share index)
    (rate : P → ℝ) (duration : ℝ) : 0 ≤ polygenicDecay share rate duration :=
  Finset.sum_nonneg fun index _ ↦ mul_nonneg (hshare index) (Real.exp_pos _).le

/-- The weighted decay is positive when some share is.

Assumes: nonnegative shares, one of them positive. -/
theorem polygenicDecay_pos {share : P → ℝ} (hshare : ∀ index, 0 ≤ share index) {index : P}
    (hindex : 0 < share index) (rate : P → ℝ) (duration : ℝ) :
    0 < polygenicDecay share rate duration :=
  Finset.sum_pos' (fun other _ ↦ mul_nonneg (hshare other) (Real.exp_pos _).le)
    ⟨index, Finset.mem_univ index, mul_pos hindex (Real.exp_pos _)⟩

/-- After the split the weighted decay is at most one.

Assumes: nonnegative shares summing to one, nonnegative rates, and `0 ≤ duration`. -/
theorem polygenicDecay_le_one {share rate : P → ℝ} (hshare : ∀ index, 0 ≤ share index)
    (hsum : ∑ index, share index = 1) (hrate : ∀ index, 0 ≤ rate index) {duration : ℝ}
    (hduration : 0 ≤ duration) : polygenicDecay share rate duration ≤ 1 :=
  (polygenicDecay_antitone_duration hshare hrate hduration).trans_eq
    ((polygenicDecay_zero_duration share rate).trans hsum)

/-- After a positive time the weighted decay is below one when a positive share sits at a
positive rate.

Assumes: nonnegative shares summing to one, nonnegative rates, a positive duration, and an index
with a positive share and a positive rate. -/
theorem polygenicDecay_lt_one {share rate : P → ℝ} (hshare : ∀ index, 0 ≤ share index)
    (hsum : ∑ index, share index = 1) (hrate : ∀ index, 0 ≤ rate index) {duration : ℝ}
    (hduration : 0 < duration) {index : P} (hindex : 0 < share index)
    (hpos : 0 < rate index) : polygenicDecay share rate duration < 1 := by
  rw [← hsum, polygenicDecay]
  refine Finset.sum_lt_sum (fun other _ ↦ mul_le_of_le_one_right (hshare other) ?_)
    ⟨index, Finset.mem_univ index, mul_lt_of_lt_one_right hindex ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hrate other) hduration.le))
  · exact (Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hpos hduration))).trans_eq
      Real.exp_zero

/-- **Calibration portability tends to the coverage floor.**

Assumes: nonnegative rates and nonzero score variance. -/
theorem tendsto_calibrationPortability_decay (effect sourceCorrelation : P → ℝ) {rate : P → ℝ}
    (hrate : ∀ pair, 0 ≤ rate pair)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    Filter.Tendsto (fun duration ↦ calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair))
      Filter.atTop (nhds (coverageFloor (trainedShare effect sourceCorrelation) rate)) := by
  have hfun : (fun duration ↦ calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair))
      = polygenicDecay (trainedShare effect sourceCorrelation) rate :=
    funext fun duration ↦
      calibrationPortability_decay effect sourceCorrelation rate duration hvariance
  rw [hfun]
  exact tendsto_polygenicDecay_atTop hrate

/-- **Squared-correlation portability tends to the square of the coverage floor.**

Assumes: nonnegative rates, nonzero score variance and nonzero outcome variance. -/
theorem tendsto_squaredCorrelationPortability_decay (effect sourceCorrelation : P → ℝ)
    {rate : P → ℝ} (hrate : ∀ pair, 0 ≤ rate pair) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    Filter.Tendsto (fun duration ↦ squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment)
      Filter.atTop (nhds (coverageFloor (trainedShare effect sourceCorrelation) rate ^ 2)) := by
  have hfun : (fun duration ↦ squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment)
      = fun duration ↦ polygenicDecay (trainedShare effect sourceCorrelation) rate duration ^ 2 :=
    funext fun duration ↦ squaredCorrelationPortability_decay effect sourceCorrelation rate
      environment duration hvariance houtcome
  rw [hfun]
  exact (tendsto_polygenicDecay_atTop hrate).pow 2

/-- **Calibration portability decreases with divergence time.**

Assumes: nonnegative rates and nonzero score variance. -/
theorem calibrationPortability_decay_antitone (effect sourceCorrelation : P → ℝ)
    {rate : P → ℝ} (hrate : ∀ pair, 0 ≤ rate pair)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    Antitone fun duration ↦ calibrationPortability effect sourceCorrelation
      (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) := by
  have hfun : (fun duration ↦ calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair))
      = polygenicDecay (trainedShare effect sourceCorrelation) rate :=
    funext fun duration ↦
      calibrationPortability_decay effect sourceCorrelation rate duration hvariance
  rw [hfun]
  exact polygenicDecay_antitone_duration (trainedShare_nonneg effect sourceCorrelation) hrate

/-- **Squared-correlation portability decreases with divergence time.**

Assumes: nonnegative rates, nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_decay_antitone (effect sourceCorrelation : P → ℝ)
    {rate : P → ℝ} (hrate : ∀ pair, 0 ≤ rate pair) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    Antitone fun duration ↦ squaredCorrelationPortability effect sourceCorrelation
      (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment := by
  have hfun : (fun duration ↦ squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment)
      = fun duration ↦ polygenicDecay (trainedShare effect sourceCorrelation) rate duration ^ 2 :=
    funext fun duration ↦ squaredCorrelationPortability_decay effect sourceCorrelation rate
      environment duration hvariance houtcome
  rw [hfun]
  intro earlier later hlater
  have hle := polygenicDecay_antitone_duration (trainedShare_nonneg effect sourceCorrelation)
    hrate hlater
  have hnonneg := polygenicDecay_nonneg (trainedShare_nonneg effect sourceCorrelation) rate later
  show polygenicDecay (trainedShare effect sourceCorrelation) rate later ^ 2
    ≤ polygenicDecay (trainedShare effect sourceCorrelation) rate earlier ^ 2
  nlinarith

/-- **Squared-correlation portability never exceeds calibration portability.**

Assumes: nonnegative rates, `0 ≤ duration`, nonzero score variance and nonzero outcome
variance. -/
theorem squaredCorrelationPortability_decay_le (effect sourceCorrelation : P → ℝ)
    {rate : P → ℝ} (hrate : ∀ pair, 0 ≤ rate pair) {environment duration : ℝ}
    (hduration : 0 ≤ duration) (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment
      ≤ calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) := by
  rw [squaredCorrelationPortability_decay effect sourceCorrelation rate environment duration
      hvariance houtcome,
    calibrationPortability_decay effect sourceCorrelation rate duration hvariance]
  have hnonneg := polygenicDecay_nonneg (trainedShare_nonneg effect sourceCorrelation) rate
    duration
  have hle := polygenicDecay_le_one (trainedShare_nonneg effect sourceCorrelation)
    (sum_trainedShare effect sourceCorrelation hvariance) hrate hduration
  nlinarith

/-- **Squared-correlation portability is strictly below calibration portability.**  At every
positive divergence time, if a pair that carries signal loses correlation at a positive rate,
`0 < R²-portability < calibration portability < 1`.

Assumes: nonnegative rates, a pair with nonzero effect, nonzero source correlation and positive
rate, nonnegative environmental variance, and a positive duration. -/
theorem squaredCorrelationPortability_decay_lt (effect sourceCorrelation : P → ℝ)
    {rate : P → ℝ} (hrate : ∀ pair, 0 ≤ rate pair) {pair : P} (heffect : effect pair ≠ 0)
    (hcorrelation : sourceCorrelation pair ≠ 0) (hpos : 0 < rate pair)
    {environment duration : ℝ} (henvironment : 0 ≤ environment) (hduration : 0 < duration) :
    0 < squaredCorrelationPortability effect sourceCorrelation
        (fun other ↦ portabilityDecay (rate other) duration * sourceCorrelation other) environment
      ∧ squaredCorrelationPortability effect sourceCorrelation
          (fun other ↦ portabilityDecay (rate other) duration * sourceCorrelation other)
          environment
        < calibrationPortability effect sourceCorrelation
          (fun other ↦ portabilityDecay (rate other) duration * sourceCorrelation other)
      ∧ calibrationPortability effect sourceCorrelation
          (fun other ↦ portabilityDecay (rate other) duration * sourceCorrelation other) < 1 := by
  have hvariance := (trainedScoreVariance_pos effect sourceCorrelation heffect hcorrelation).ne'
  have houtcome := (outcomeVariance_pos effect heffect henvironment).ne'
  rw [squaredCorrelationPortability_decay effect sourceCorrelation rate environment duration
      hvariance houtcome,
    calibrationPortability_decay effect sourceCorrelation rate duration hvariance]
  have hshare := trainedShare_pos effect sourceCorrelation heffect hcorrelation
  have hlower := polygenicDecay_pos (trainedShare_nonneg effect sourceCorrelation) hshare rate
    duration
  have hupper := polygenicDecay_lt_one (trainedShare_nonneg effect sourceCorrelation)
    (sum_trainedShare effect sourceCorrelation hvariance) hrate hduration hshare hpos
  exact ⟨pow_pos hlower 2, by nlinarith [mul_pos hlower (sub_pos.mpr hupper)], hupper⟩

/-- **A weighted mean squared is at most the weighted mean of the squares.**

Assumes: nonnegative weights summing to one. -/
theorem sq_weightedMean_le_weightedMean_sq {weight : P → ℝ}
    (hweight : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1) (value : P → ℝ) :
    (∑ index, weight index * value index) ^ 2 ≤ ∑ index, weight index * value index ^ 2 := by
  obtain ⟨mean, hmean⟩ : ∃ mean, mean = ∑ index, weight index * value index := ⟨_, rfl⟩
  have hspread : 0 ≤ ∑ index, weight index * (value index - mean) ^ 2 :=
    Finset.sum_nonneg fun index _ ↦ mul_nonneg (hweight index) (sq_nonneg _)
  have hexpand : ∑ index, weight index * (value index - mean) ^ 2
      = ∑ index, (weight index * value index ^ 2 - 2 * mean * (weight index * value index)
        + mean ^ 2 * weight index) :=
    Finset.sum_congr rfl fun index _ ↦ by ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← hmean, hsum] at hexpand
  rw [← hmean]
  nlinarith

/-- **A polygenic score's squared correlation loses at least as much as its average pair.**  Its
portability is at most the signal-weighted mean `∑_p ω_p e^{-2 x_p T}` of the per-pair squared
retentions.

Assumes: nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_decay_le_polygenicDecay
    (effect sourceCorrelation rate : P → ℝ) (environment duration : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rate pair) duration * sourceCorrelation pair) environment
      ≤ polygenicDecay (trainedShare effect sourceCorrelation) (fun pair ↦ 2 * rate pair)
        duration := by
  rw [squaredCorrelationPortability_decay effect sourceCorrelation rate environment duration
    hvariance houtcome]
  have h := sq_weightedMean_le_weightedMean_sq (trainedShare_nonneg effect sourceCorrelation)
    (sum_trainedShare effect sourceCorrelation hvariance)
    (fun pair ↦ portabilityDecay (rate pair) duration)
  simp only [portabilityDecay_sq] at h
  exact h

/-! ## The two-locus ratio as a product of per-deme factors -/

section TwoLocus

variable {D : ℕ}

/-- **The two-locus portability ratio is the product of one decay factor per deme**,
`e^{-ρ̄T} = e^{-(ρ_S/2) T} e^{-(ρ_T/2) T}`.

Assumes: no migration, no mutation, `parent ≠ child`, and a nonzero ancestral correlation. -/
theorem splitPortabilityRatio_eq_mul_portabilityDecay (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) :
    splitPortabilityRatio rates parent child hduration ancestral
      = portabilityDecay (rates.recombination parent / 2) duration
        * portabilityDecay (rates.recombination child / 2) duration := by
  rw [splitPortabilityRatio_eq rates hmigration hmutation hne hduration ancestral hsource,
    add_div, portabilityDecay_add]

/-- **At equal rates the two-locus ratio is the square of the one-deme factor.**

Assumes: no migration, no mutation, `parent ≠ child`, equal recombination rates, and a nonzero
ancestral correlation. -/
theorem splitPortabilityRatio_eq_sq_portabilityDecay (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hrec : rates.recombination child = rates.recombination parent)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) :
    splitPortabilityRatio rates parent child hduration ancestral
      = portabilityDecay (rates.recombination parent / 2) duration ^ 2 := by
  rw [splitPortabilityRatio_eq_mul_portabilityDecay rates hmigration hmutation hne hduration
    ancestral hsource, hrec, sq]

/-- **The two-locus ratio is the squared-correlation portability of a score at the one-deme
retention.**  At equal recombination rates, a trained score whose pairs keep the fraction
`e^{-(ρ/2) T}` of their source correlation has squared-correlation portability `e^{-ρT}`.

Assumes: no migration, no mutation, `parent ≠ child`, equal recombination rates, a nonzero
ancestral correlation, nonzero score variance and nonzero outcome variance. -/
theorem splitPortabilityRatio_eq_squaredCorrelationPortability (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hrec : rates.recombination child = rates.recombination parent)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0)
    (effect sourceCorrelation : P → ℝ) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    splitPortabilityRatio rates parent child hduration ancestral
      = squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rates.recombination parent / 2) duration
          * sourceCorrelation pair) environment := by
  rw [squaredCorrelationPortability_eq_calibrationPortability_sq _ _ _ _ hvariance houtcome,
    calibrationPortability_commonRate _ _ _ _ hvariance,
    splitPortabilityRatio_eq_sq_portabilityDecay rates hmigration hmutation hne hrec hduration
      ancestral hsource]

/-- **Calibration portability at the one-deme retention is the square root of the two-locus
ratio.**

Assumes: no migration, no mutation, `parent ≠ child`, equal recombination rates, a nonzero
ancestral correlation, and nonzero score variance. -/
theorem calibrationPortability_sq_eq_splitPortabilityRatio (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hrec : rates.recombination child = rates.recombination parent)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0)
    (effect sourceCorrelation : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rates.recombination parent / 2) duration
          * sourceCorrelation pair) ^ 2
      = splitPortabilityRatio rates parent child hduration ancestral := by
  rw [calibrationPortability_commonRate _ _ _ _ hvariance,
    splitPortabilityRatio_eq_sq_portabilityDecay rates hmigration hmutation hne hrec hduration
      ancestral hsource]

/-- **The two-locus ratio is strictly below calibration portability at the one-deme retention.**

Assumes: no migration, no mutation, `parent ≠ child`, equal and positive recombination rates, a
positive duration, a nonzero ancestral correlation, and nonzero score variance. -/
theorem splitPortabilityRatio_lt_calibrationPortability (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hrec : rates.recombination child = rates.recombination parent)
    (hpositive : 0 < rates.recombination parent) {duration : ℝ} (hduration : 0 < duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0)
    (effect sourceCorrelation : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    splitPortabilityRatio rates parent child hduration.le ancestral
      < calibrationPortability effect sourceCorrelation
        (fun pair ↦ portabilityDecay (rates.recombination parent / 2) duration
          * sourceCorrelation pair) := by
  rw [calibrationPortability_commonRate _ _ _ _ hvariance,
    splitPortabilityRatio_eq_sq_portabilityDecay rates hmigration hmutation hne hrec hduration.le
      ancestral hsource]
  have hlower : 0 < portabilityDecay (rates.recombination parent / 2) duration :=
    Real.exp_pos _
  have hupper : portabilityDecay (rates.recombination parent / 2) duration < 1 :=
    (Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos (half_pos hpositive) hduration))).trans_eq
      Real.exp_zero
  nlinarith [mul_pos hlower (sub_pos.mpr hupper)]

end TwoLocus

end

end Descent.Portability.CalibrationPortabilityDecay
