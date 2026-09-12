/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityCurveIdentifiability
import Descent.Portability.PortabilityMinimaxLowerBound

assert_below Descent.Decision Descent.Program

/-!
# Portability curves are blind to population size

`PortabilityCurveIdentifiability` shows that the split-law average of the portability ratio of a
split history is the portability curve `E_ν[e^{-rT}]` of the split-time law, and that the curve
determines that law.  There the history after the split is one epoch of constant drift.  Here it
is any size history: a list of epochs, each with its own drift rates and duration.

## Main results

- `propagate_sizeHistoryEpochs_DD`, `propagate_sizeHistoryEpochs_pi2`: along a size history
  without migration or mutation, `E[D_S D_T]` is multiplied by `e^{-(E + rT)}` and
  `E[π^A_S π^B_T]` by `e^{-E}`.  Here `E = ∑ (c_S + c_T) t` is the drift exposure of the epochs
  and `T = ∑ t` their total duration.
- `sizeHistoryPortabilityRatio_eq`: so after a split and a size history the portability ratio is
  `e^{-rT}`, whatever the drift rates of the epochs.  With one epoch this is the corpus ratio
  (`sizeHistoryPortabilityRatio_constantSizeHistory`).
- `meanSizeHistoryPortabilityRatio_eq`: for a random split time, with a size history of duration
  `T` after each split time `T`, the average ratio is the portability curve of the split-time law.
- `meanSizeHistoryPortabilityRatio_eq_of_splitLaw`: **size blindness.**  Two demographic histories
  with one split-time law and any two size histories have the same portability curve.
- `splitLaw_eq_of_meanSizeHistoryPortabilityRatio_eq`: the curve still identifies the split-time
  law, whatever the size histories.
- `abs_sub_div_two_le_max_sizeEstimator_error`, `sizeEstimator_cohortLowerBound`: **the
  information boundary.**  Every estimator of a size value from the portability curve, or from
  `n` reports whose law is any function of the curve, has worst-case error at least half the
  separation of the two size values (`PortabilityMinimaxLowerBound.lowerBound_cohortLaw_of_eq`).
- `populationSize_error_ge`: between constant population sizes `1` and `2B + 1`, every estimator
  of the size `N = 1/c` of the source deme errs by at least `B` under one of them.  No estimator
  of population size from portability curves has bounded worst-case risk.

## Significance

Two-locus portability curves identify the divergence history and never the effective population
size.  In every epoch drift lowers the cross linkage covariance and the cross heterozygosity
product at the same rate, so a change of size multiplies both by one factor and leaves the ratio
unchanged.  The curve carries the split-time law and nothing else, and population size needs
other data.

## Scope

The blindness is for the average of the per-history ratio.  For the pooled ratio of expectations
with a random split time drift does not cancel
(`PortabilityCurveIdentifiability.pooledSplitPortabilityRatio_ne_of_drift_ne`), so the blindness
does not hold in that form.  The recombination rate is constant in time and shared by the two
demes, and there is no migration or mutation after the split.  Estimators are deterministic
functions of the curve or of the reports.

## Empirical status

None.  The bodies here are algebra on the corpus moment system and integrals against stated laws,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilitySizeBlindness

open MeasureTheory Descent.Coalescent
open scoped NNReal
open Descent.Portability.TwoLocusPortabilityDecay (portabilityDecay splitTransform_DD
  splitTransform_pi2 augmentedLowOrderLDGenerator_DD_row augmentedLowOrderLDGenerator_pi2_row
  matrixExponential_mulVec_apply_of_row_eq ancestralSquaredCorrelation splitPortabilityRatio
  splitPortabilityRatio_eq)
open Descent.Portability.PortabilityCurveIdentifiability (portabilityCurve neutralLinkageRates
  neutralLinkageRates_coalescence neutralLinkageRates_migration neutralLinkageRates_mutation
  neutralLinkageRates_recombination_mean constantSizeRates splitLaw_eq_of_portabilityCurve_eq)
open Descent.Portability.FourCellCohortLaw (cohortLaw)

noncomputable section

variable {D : ℕ}

/-! ## Size histories -/

/-- **The total duration of a size history**: the sum of its epoch durations.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of stated durations. -/
def totalDuration (epochs : List (ManyDemeLDRates D × ℝ≥0)) : ℝ :=
  (epochs.map fun stage ↦ (stage.2 : ℝ)).sum

/-- **The drift exposure of a size history** between two demes, `∑ (c_S + c_T) t` over its
epochs.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of products of stated rates and durations. -/
def driftExposure (parent child : Fin D) (epochs : List (ManyDemeLDRates D × ℝ≥0)) : ℝ :=
  (epochs.map fun stage ↦
    (stage.1.coalescence parent + stage.1.coalescence child) * (stage.2 : ℝ)).sum

/-- **The epochs of a size history at recombination rate `rate`.**  Each epoch evolves under the
neutral linkage rates of its own drift rates, for its own duration.

Empirical status: NOT AN EMPIRICAL CLAIM.  A list of corpus instructions. -/
def sizeHistoryEpochs (rate : ℝ) (epochs : List (ManyDemeLDRates D × ℝ≥0)) :
    List (LowOrderLDInstruction D) :=
  epochs.map fun stage ↦ LowOrderLDInstruction.evolve
    ((neutralLinkageRates stage.1 rate).epoch stage.2 (NNReal.coe_nonneg stage.2))

/-- **A split followed by a size history**, as corpus instructions.

Empirical status: NOT AN EMPIRICAL CLAIM.  A list of corpus instructions. -/
def sizeHistoryInstructions (parent child : Fin D) (rate : ℝ)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) : List (LowOrderLDInstruction D) :=
  LowOrderLDInstruction.split parent child :: sizeHistoryEpochs rate epochs

/-- A list of instructions acts one instruction at a time. -/
theorem propagate_cons (instruction : LowOrderLDInstruction D)
    (rest : List (LowOrderLDInstruction D)) (state : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (instruction :: rest) state
      = propagateLowOrderLDInstructions rest (instruction.apply state) :=
  rfl

/-- The epochs of a size history, one stage at a time. -/
theorem sizeHistoryEpochs_cons (rate : ℝ) (stage : ManyDemeLDRates D × ℝ≥0)
    (rest : List (ManyDemeLDRates D × ℝ≥0)) :
    sizeHistoryEpochs rate (stage :: rest)
      = LowOrderLDInstruction.evolve ((neutralLinkageRates stage.1 rate).epoch stage.2
          (NNReal.coe_nonneg stage.2)) :: sizeHistoryEpochs rate rest :=
  rfl

/-! ## One epoch, then a whole size history -/

/-- **One epoch multiplies `E[D_S D_T]` by `e^{-(c_S + c_T + r) t}`.**

Assumes: `parent ≠ child`. -/
theorem apply_evolve_DD (drift : ManyDemeLDRates D) (rate : ℝ) (duration : ℝ≥0)
    {parent child : Fin D} (hne : parent ≠ child) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (LowOrderLDInstruction.evolve ((neutralLinkageRates drift rate).epoch duration
        (NNReal.coe_nonneg duration))).apply state (some (.DD parent child))
      = Real.exp (-((drift.coalescence parent + drift.coalescence child) * duration
          + max rate 0 * duration)) * state (some (.DD parent child)) := by
  have h := matrixExponential_mulVec_apply_of_row_eq
    (augmentedLowOrderLDGenerator (neutralLinkageRates drift rate)) duration _ state _
    (augmentedLowOrderLDGenerator_DD_row (neutralLinkageRates drift rate)
      (neutralLinkageRates_migration drift rate) (neutralLinkageRates_mutation drift rate) hne)
  rw [neutralLinkageRates_recombination_mean, neutralLinkageRates_coalescence,
    neutralLinkageRates_coalescence] at h
  refine h.trans ?_
  congr 2
  ring

/-- **One epoch multiplies `E[π^A_S π^B_T]` by `e^{-(c_S + c_T) t}`.**

Assumes: `parent ≠ child`. -/
theorem apply_evolve_pi2 (drift : ManyDemeLDRates D) (rate : ℝ) (duration : ℝ≥0)
    {parent child : Fin D} (hne : parent ≠ child) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (LowOrderLDInstruction.evolve ((neutralLinkageRates drift rate).epoch duration
        (NNReal.coe_nonneg duration))).apply state (some (.pi2 parent parent child child))
      = Real.exp (-((drift.coalescence parent + drift.coalescence child) * duration))
        * state (some (.pi2 parent parent child child)) := by
  have h := matrixExponential_mulVec_apply_of_row_eq
    (augmentedLowOrderLDGenerator (neutralLinkageRates drift rate)) duration _ state _
    (augmentedLowOrderLDGenerator_pi2_row (neutralLinkageRates drift rate)
      (neutralLinkageRates_migration drift rate) (neutralLinkageRates_mutation drift rate) hne)
  rw [neutralLinkageRates_coalescence, neutralLinkageRates_coalescence] at h
  refine h.trans ?_
  congr 2
  ring

/-- **A size history multiplies `E[D_S D_T]` by `e^{-(E + rT)}`**, with `E` its drift exposure and
`T` its total duration.

Assumes: `parent ≠ child`. -/
theorem propagate_sizeHistoryEpochs_DD (rate : ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) (state : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (sizeHistoryEpochs rate epochs) state
        (some (.DD parent child))
      = Real.exp (-(driftExposure parent child epochs + max rate 0 * totalDuration epochs))
        * state (some (.DD parent child)) := by
  induction epochs generalizing state with
  | nil =>
    simp [sizeHistoryEpochs, propagateLowOrderLDInstructions, driftExposure, totalDuration]
  | cons stage rest ih =>
    rw [sizeHistoryEpochs_cons, propagate_cons, ih, apply_evolve_DD stage.1 rate stage.2 hne state,
      ← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [driftExposure, totalDuration, List.map_cons, List.sum_cons]
    ring

/-- **A size history multiplies `E[π^A_S π^B_T]` by `e^{-E}`**, with `E` its drift exposure.

Assumes: `parent ≠ child`. -/
theorem propagate_sizeHistoryEpochs_pi2 (rate : ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) (state : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (sizeHistoryEpochs rate epochs) state
        (some (.pi2 parent parent child child))
      = Real.exp (-driftExposure parent child epochs)
        * state (some (.pi2 parent parent child child)) := by
  induction epochs generalizing state with
  | nil =>
    simp [sizeHistoryEpochs, propagateLowOrderLDInstructions, driftExposure]
  | cons stage rest ih =>
    rw [sizeHistoryEpochs_cons, propagate_cons, ih,
      apply_evolve_pi2 stage.1 rate stage.2 hne state, ← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [driftExposure, List.map_cons, List.sum_cons]
    ring

/-- **After a split and a size history, `E[D_S D_T] = e^{-(E + rT)} E[D²](0)`.**

Assumes: `parent ≠ child`. -/
theorem sizeHistoryState_DD (rate : ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (sizeHistoryInstructions parent child rate epochs) ancestral
        (some (.DD parent child))
      = Real.exp (-(driftExposure parent child epochs + max rate 0 * totalDuration epochs))
        * ancestral (some (.DD parent parent)) := by
  have hsplit : (LowOrderLDInstruction.split parent child).apply ancestral
        (some (.DD parent child))
      = ancestral (some (.DD parent parent)) :=
    splitTransform_DD hne ancestral
  rw [sizeHistoryInstructions, propagate_cons, propagate_sizeHistoryEpochs_DD rate hne, hsplit]

/-- **After a split and a size history, `E[π^A_S π^B_T] = e^{-E} E[π^A π^B](0)`.**

Assumes: `parent ≠ child`. -/
theorem sizeHistoryState_pi2 (rate : ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    propagateLowOrderLDInstructions (sizeHistoryInstructions parent child rate epochs) ancestral
        (some (.pi2 parent parent child child))
      = Real.exp (-driftExposure parent child epochs)
        * ancestral (some (.pi2 parent parent parent parent)) := by
  have hsplit : (LowOrderLDInstruction.split parent child).apply ancestral
        (some (.pi2 parent parent child child))
      = ancestral (some (.pi2 parent parent parent parent)) :=
    splitTransform_pi2 hne ancestral
  rw [sizeHistoryInstructions, propagate_cons, propagate_sizeHistoryEpochs_pi2 rate hne, hsplit]

/-! ## Drift cancels along any size history -/

/-- **The portability ratio of a split followed by a size history**, `σ²_{S→T} / σ²_D(0)` with
`σ²_{S→T} = E[D_S D_T] / E[π^A_S π^B_T]`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of moment coordinates. -/
def sizeHistoryPortabilityRatio (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (rate : ℝ)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) : ℝ :=
  (propagateLowOrderLDInstructions (sizeHistoryInstructions parent child rate epochs) ancestral
        (some (.DD parent child))
      / propagateLowOrderLDInstructions (sizeHistoryInstructions parent child rate epochs)
        ancestral (some (.pi2 parent parent child child)))
    / ancestralSquaredCorrelation ancestral parent

/-- **Drift cancels along any size history.**  After a split and a size history at recombination
rate `r ≥ 0`, the portability ratio is `e^{-rT}` with `T` the total duration, whatever the drift
rates of the epochs.

Assumes: `parent ≠ child` and a nonzero ancestral correlation. -/
theorem sizeHistoryPortabilityRatio_eq {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) (rate : ℝ)
    (epochs : List (ManyDemeLDRates D × ℝ≥0)) :
    sizeHistoryPortabilityRatio parent child ancestral rate epochs
      = portabilityDecay (max rate 0) (totalDuration epochs) := by
  have hfactor :
      Real.exp (-(driftExposure parent child epochs + max rate 0 * totalDuration epochs))
        = Real.exp (-driftExposure parent child epochs)
          * portabilityDecay (max rate 0) (totalDuration epochs) := by
    rw [portabilityDecay, ← Real.exp_add]
    congr 1
    ring
  have hcorrelation : ancestral (some (.DD parent parent))
        / ancestral (some (.pi2 parent parent parent parent))
      = ancestralSquaredCorrelation ancestral parent :=
    rfl
  rw [sizeHistoryPortabilityRatio, sizeHistoryState_DD rate hne, sizeHistoryState_pi2 rate hne,
    hfactor, mul_assoc, mul_div_mul_left _ _ (Real.exp_pos _).ne', mul_div_assoc, hcorrelation,
    mul_div_cancel_right₀ _ hsource]

/-- **A size history with one epoch** of drift rates `drift`, lasting the split time.

Empirical status: NOT AN EMPIRICAL CLAIM.  A one-epoch list. -/
def constantSizeHistory (drift : ManyDemeLDRates D) (duration : ℝ) :
    List (ManyDemeLDRates D × ℝ≥0) :=
  [(drift, duration.toNNReal)]

/-- The one-epoch history lasts `max T 0`. -/
theorem totalDuration_constantSizeHistory (drift : ManyDemeLDRates D) (duration : ℝ) :
    totalDuration (constantSizeHistory drift duration) = max duration 0 := by
  simp [totalDuration, constantSizeHistory, Real.coe_toNNReal']

/-- The one-epoch history of a nonnegative split time lasts that split time.

Assumes: `0 ≤ duration`. -/
theorem totalDuration_constantSizeHistory_of_nonneg (drift : ManyDemeLDRates D) (duration : ℝ)
    (hduration : 0 ≤ duration) : totalDuration (constantSizeHistory drift duration) = duration := by
  rw [totalDuration_constantSizeHistory, max_eq_left hduration]

/-- **The one-epoch size history is the corpus split history.**  Its portability ratio is the ratio
`splitPortabilityRatio` of `TwoLocusPortabilityDecay` at the neutral linkage rates.

Assumes: `parent ≠ child` and a nonzero ancestral correlation. -/
theorem sizeHistoryPortabilityRatio_constantSizeHistory (drift : ManyDemeLDRates D)
    (rate duration : ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) :
    sizeHistoryPortabilityRatio parent child ancestral rate (constantSizeHistory drift duration)
      = splitPortabilityRatio (neutralLinkageRates drift rate) parent child
          (le_max_right duration 0) ancestral := by
  rw [sizeHistoryPortabilityRatio_eq hne ancestral hsource, totalDuration_constantSizeHistory,
    splitPortabilityRatio_eq (neutralLinkageRates drift rate)
      (neutralLinkageRates_migration drift rate) (neutralLinkageRates_mutation drift rate) hne
      (le_max_right duration 0) ancestral hsource,
    neutralLinkageRates_recombination_mean]

/-! ## Size blindness for a random split time -/

/-- **The average portability curve of a demographic history.**  The split time has law
`splitLaw`, and after a split `T` ago the size history `history T` runs.  At recombination rate
`rate` the value is the split-law average of the portability ratio.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral of a ratio of moment coordinates. -/
def meanSizeHistoryPortabilityRatio (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (history : ℝ → List (ManyDemeLDRates D × ℝ≥0)) (splitLaw : Measure ℝ) (rate : ℝ) : ℝ :=
  ∫ duration, sizeHistoryPortabilityRatio parent child ancestral rate (history duration)
    ∂splitLaw

/-- **Drift cancels from the average curve of any demographic history.**  If each size history
`history T` lasts `T`, the average ratio at rate `r` is the portability curve of the split law at
`max r 0`.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, size histories lasting their split
times, and a split law carried by `[0, ∞)`. -/
theorem meanSizeHistoryPortabilityRatio_eq {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0)
    (history : ℝ → List (ManyDemeLDRates D × ℝ≥0))
    (hhistory : ∀ duration, 0 ≤ duration → totalDuration (history duration) = duration)
    (splitLaw : Measure ℝ) (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) (rate : ℝ) :
    meanSizeHistoryPortabilityRatio parent child ancestral history splitLaw rate
      = portabilityCurve splitLaw (max rate 0) := by
  unfold meanSizeHistoryPortabilityRatio portabilityCurve
  refine integral_congr_ae (hsupport.mono fun duration hduration ↦ ?_)
  exact (sizeHistoryPortabilityRatio_eq hne ancestral hsource rate (history duration)).trans
    (by rw [hhistory duration hduration])

/-- **Size blindness.**  Two demographic histories with one split-time law, any two size
histories, and any two ancestral states have the same portability curve at every recombination
rate.

Assumes: `parent ≠ child`, nonzero ancestral correlations, size histories lasting their split
times, and a split law carried by `[0, ∞)`. -/
theorem meanSizeHistoryPortabilityRatio_eq_of_splitLaw {parent child : Fin D}
    (hne : parent ≠ child) (firstAncestral secondAncestral : AffineLowOrderLDCoordinate D → ℝ)
    (hfirstSource : ancestralSquaredCorrelation firstAncestral parent ≠ 0)
    (hsecondSource : ancestralSquaredCorrelation secondAncestral parent ≠ 0)
    (firstHistory secondHistory : ℝ → List (ManyDemeLDRates D × ℝ≥0))
    (hfirstHistory : ∀ duration, 0 ≤ duration → totalDuration (firstHistory duration) = duration)
    (hsecondHistory :
      ∀ duration, 0 ≤ duration → totalDuration (secondHistory duration) = duration)
    (splitLaw : Measure ℝ) (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) :
    meanSizeHistoryPortabilityRatio parent child firstAncestral firstHistory splitLaw
      = meanSizeHistoryPortabilityRatio parent child secondAncestral secondHistory splitLaw := by
  funext rate
  rw [meanSizeHistoryPortabilityRatio_eq hne firstAncestral hfirstSource firstHistory
      hfirstHistory splitLaw hsupport,
    meanSizeHistoryPortabilityRatio_eq hne secondAncestral hsecondSource secondHistory
      hsecondHistory splitLaw hsupport]

/-- **The curve still identifies the split-time law.**  Two demographic histories, with any size
histories, drift rates and ancestral states, whose average portability curves agree at
`r₀, 2r₀, 3r₀, …` have the same split-time law.

Assumes: `parent ≠ child`, nonzero ancestral correlations, size histories lasting their split
times, probability laws carried by `[0, ∞)`, `0 < rate`, and equal curves at `k r₀` for
`k ≥ 1`. -/
theorem splitLaw_eq_of_meanSizeHistoryPortabilityRatio_eq {parent child : Fin D}
    (hne : parent ≠ child) (firstAncestral secondAncestral : AffineLowOrderLDCoordinate D → ℝ)
    (hfirstSource : ancestralSquaredCorrelation firstAncestral parent ≠ 0)
    (hsecondSource : ancestralSquaredCorrelation secondAncestral parent ≠ 0)
    (firstHistory secondHistory : ℝ → List (ManyDemeLDRates D × ℝ≥0))
    (hfirstHistory : ∀ duration, 0 ≤ duration → totalDuration (firstHistory duration) = duration)
    (hsecondHistory :
      ∀ duration, 0 ≤ duration → totalDuration (secondHistory duration) = duration)
    (firstLaw secondLaw : Measure ℝ) [IsProbabilityMeasure firstLaw]
    [IsProbabilityMeasure secondLaw] (hfirst : ∀ᵐ duration ∂firstLaw, 0 ≤ duration)
    (hsecond : ∀ᵐ duration ∂secondLaw, 0 ≤ duration) {rate : ℝ} (hrate : 0 < rate)
    (hcurve : ∀ scale : ℕ, 0 < scale →
      meanSizeHistoryPortabilityRatio parent child firstAncestral firstHistory firstLaw
          (scale * rate)
        = meanSizeHistoryPortabilityRatio parent child secondAncestral secondHistory secondLaw
          (scale * rate)) :
    firstLaw = secondLaw := by
  refine splitLaw_eq_of_portabilityCurve_eq firstLaw secondLaw hrate hfirst hsecond
    fun scale hscale ↦ ?_
  have h := hcurve scale hscale
  rw [meanSizeHistoryPortabilityRatio_eq hne firstAncestral hfirstSource firstHistory
      hfirstHistory firstLaw hfirst,
    meanSizeHistoryPortabilityRatio_eq hne secondAncestral hsecondSource secondHistory
      hsecondHistory secondLaw hsecond,
    max_eq_left (mul_nonneg (Nat.cast_nonneg scale) hrate.le)] at h
  exact h

/-! ## The information boundary -/

/-- **No estimator of size from a portability curve beats half the separation.**  Two
demographic histories with one split-time law and different size histories have the same curve,
so an estimator, any function of the curve, errs under one of the two by at least half the
distance between their size values.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, size histories lasting their split
times, and a split law carried by `[0, ∞)`. -/
theorem abs_sub_div_two_le_max_sizeEstimator_error {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0)
    (firstHistory secondHistory : ℝ → List (ManyDemeLDRates D × ℝ≥0))
    (hfirstHistory : ∀ duration, 0 ≤ duration → totalDuration (firstHistory duration) = duration)
    (hsecondHistory :
      ∀ duration, 0 ≤ duration → totalDuration (secondHistory duration) = duration)
    (splitLaw : Measure ℝ) (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration)
    (estimator : (ℝ → ℝ) → ℝ) (firstSize secondSize : ℝ) :
    |firstSize - secondSize| / 2
      ≤ max
          |estimator (meanSizeHistoryPortabilityRatio parent child ancestral firstHistory
              splitLaw) - firstSize|
          |estimator (meanSizeHistoryPortabilityRatio parent child ancestral secondHistory
              splitLaw) - secondSize| := by
  rw [meanSizeHistoryPortabilityRatio_eq_of_splitLaw hne ancestral ancestral hsource hsource
    secondHistory firstHistory hsecondHistory hfirstHistory splitLaw hsupport]
  set value :=
    estimator (meanSizeHistoryPortabilityRatio parent child ancestral firstHistory splitLaw)
  have htriangle := abs_sub_le firstSize value secondSize
  rw [abs_sub_comm firstSize value] at htriangle
  have hleft := le_max_left |value - firstSize| |value - secondSize|
  have hright := le_max_right |value - firstSize| |value - secondSize|
  linarith

/-- **The information boundary with noisy data.**  Let a measurement scheme `observation` turn a
portability curve into a finite report law.  Two demographic histories with one split-time law
and different size histories give one report law.  So every estimator of a size value from `n`
independent reports has, under one of the two, expected absolute error at least half the
separation of the size values, for every `n`.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, size histories lasting their split
times, and a split law carried by `[0, ∞)`. -/
theorem sizeEstimator_cohortLowerBound {Report : Type*} [Fintype Report] {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0)
    (firstHistory secondHistory : ℝ → List (ManyDemeLDRates D × ℝ≥0))
    (hfirstHistory : ∀ duration, 0 ≤ duration → totalDuration (firstHistory duration) = duration)
    (hsecondHistory :
      ∀ duration, 0 ≤ duration → totalDuration (secondHistory duration) = duration)
    (splitLaw : Measure ℝ) (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration)
    (observation : (ℝ → ℝ) → FiniteReportLaw Report) (n : ℕ)
    (estimator : (Fin n → Report) → ℝ) (firstSize secondSize : ℝ) :
    |firstSize - secondSize| / 2
      ≤ max
          ((cohortLaw (observation (meanSizeHistoryPortabilityRatio parent child ancestral
              firstHistory splitLaw)) n).expectation
            fun sample ↦ |estimator sample - firstSize|)
          ((cohortLaw (observation (meanSizeHistoryPortabilityRatio parent child ancestral
              secondHistory splitLaw)) n).expectation
            fun sample ↦ |estimator sample - secondSize|) := by
  rw [meanSizeHistoryPortabilityRatio_eq_of_splitLaw hne ancestral ancestral hsource hsource
    secondHistory firstHistory hsecondHistory hfirstHistory splitLaw hsupport]
  exact PortabilityMinimaxLowerBound.lowerBound_cohortLaw_of_eq _ n firstSize secondSize estimator

/-- The population size `1/c` of a deme of `constantSizeRates D logSize` is `e^{logSize}`. -/
theorem inv_coalescence_constantSizeRates (logSize : ℝ) (deme : Fin D) :
    ((constantSizeRates D logSize).coalescence deme)⁻¹ = Real.exp logSize := by
  show (Real.exp (-logSize))⁻¹ = Real.exp logSize
  rw [Real.exp_neg, inv_inv]

/-- **Population size is not estimable from portability curves.**  For every estimator of the
population size `N = 1/c` of the source deme from a portability curve and every `B ≥ 0`, one of
the constant-size histories of size `1` or of size `2B + 1` forces an error of at least `B`.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, a split law carried by `[0, ∞)`, and
`0 ≤ bound`. -/
theorem populationSize_error_ge {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) (splitLaw : Measure ℝ)
    (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) (estimator : (ℝ → ℝ) → ℝ) {bound : ℝ}
    (hbound : 0 ≤ bound) :
    bound ≤ max
      |estimator (meanSizeHistoryPortabilityRatio parent child ancestral
          (constantSizeHistory (constantSizeRates D 0)) splitLaw)
        - ((constantSizeRates D 0).coalescence parent)⁻¹|
      |estimator (meanSizeHistoryPortabilityRatio parent child ancestral
          (constantSizeHistory (constantSizeRates D (Real.log (2 * bound + 1)))) splitLaw)
        - ((constantSizeRates D (Real.log (2 * bound + 1))).coalescence parent)⁻¹| := by
  have h := abs_sub_div_two_le_max_sizeEstimator_error hne ancestral hsource
    (constantSizeHistory (constantSizeRates D 0))
    (constantSizeHistory (constantSizeRates D (Real.log (2 * bound + 1))))
    (totalDuration_constantSizeHistory_of_nonneg _) (totalDuration_constantSizeHistory_of_nonneg _)
    splitLaw hsupport estimator ((constantSizeRates D 0).coalescence parent)⁻¹
    ((constantSizeRates D (Real.log (2 * bound + 1))).coalescence parent)⁻¹
  have hpositive : 0 < 2 * bound + 1 := by linarith
  have hnonpositive : 1 - (2 * bound + 1) ≤ 0 := by linarith
  have hgap : |((constantSizeRates D 0).coalescence parent)⁻¹
        - ((constantSizeRates D (Real.log (2 * bound + 1))).coalescence parent)⁻¹| / 2
      = bound := by
    rw [inv_coalescence_constantSizeRates, inv_coalescence_constantSizeRates, Real.exp_zero,
      Real.exp_log hpositive, abs_of_nonpos hnonpositive]
    ring
  linarith

end

end Descent.Portability.PortabilitySizeBlindness
