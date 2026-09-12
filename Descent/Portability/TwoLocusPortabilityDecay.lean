/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory
import Descent.Portability.SubstochasticGeneratorSemigroup

assert_below Descent.Decision Descent.Program

/-!
# Closed-form two-locus portability decay

A source and a target population split from one ancestor `T` ago.  A tag-locus score trained on
the ancestral linkage pattern tags a causal locus through the linkage covariance `D`.  How much
of its expected squared correlation survives in the pair of descendant populations?

This module answers exactly on the NOTE1 low-order moment system `H/DD/Dz/pi2`.  The history is
the corpus split instruction, which copies the ancestral moment vector into both demes, followed
by one corpus epoch of `augmentedLowOrderLDGenerator` with drift `c_S, c_T`, recombination
`ρ_S, ρ_T` and no migration or mutation.  Expectations enter as a ratio of expectations
`E N / E D`, as in the end-to-end law F8, never as the mean of a ratio.

## Main results

- `splitHistoryState_DD`: `E[D_S D_T](T) = e^{-(c_S + c_T + (ρ_S + ρ_T)/2) T} E[D²](0)`.
- `splitHistoryState_pi2`: `E[π^A_S π^B_T](T) = e^{-(c_S + c_T) T} E[π^A π^B](0)`.
- `crossSquaredCorrelation_eq`: the cross-population expected squared correlation
  `σ²_{S→T} = E[D_S D_T] / E[π^A_S π^B_T]` is `e^{-r T} σ²_D(0)` with `r = (ρ_S + ρ_T)/2`.
- `splitPortabilityRatio_eq`: the target-to-source ratio `σ²_{S→T}(T) / σ²_D(0)` is exactly
  `portabilityDecay r T = e^{-r T}`.  With equal rates `r = ρ`, and the per-lineage rate
  `ρ/2` of the corpus gives `e^{-2 (ρ/2) T}`.
- `portabilityDecay_antitone_duration`, `portabilityDecay_antitone_rate`,
  `tendsto_portabilityDecay_atTop`, `portabilityDecay_zero_rate`: the ratio decreases in the
  split time and in the recombination rate, tends to `0` as `T → ∞` when `r > 0`, and is `1`
  when `r = 0`.

## Significance

Portability through linkage decays with split time and recombination distance, and drift does
not enter.  Drift lowers the cross-population linkage covariance at rate `c_S + c_T` and the
cross-population heterozygosity product at the same rate, so it cancels from the ratio exactly,
whatever the two drift rates are.  What remains is the recombination clock alone.

## The mechanism

A coordinate whose generator row is `μ` times its own unit row is multiplied by `e^{μ t}` along
every trajectory of the exact matrix exponential (`matrixExponential_mulVec_apply_of_row_eq`),
through the one-row intertwining `matrixExponential_intertwines` and the scalar exponential
`SubstochasticGeneratorSemigroup.matrixExponential_scalar_shift`.  With no migration and no
mutation, the rows of `DD(i, j)` and `pi2(i, i, j, j)` for `i ≠ j` are of that form
(`augmentedLowOrderLDGenerator_DD_row`, `augmentedLowOrderLDGenerator_pi2_row`).

## Scope

The source reference is the split-time value `σ²_D(0)`.  The present-day within-source value
follows the Ohta–Kimura system, whose rates are the roots of a cubic, and has no closed form in
`e^{-cT}` and `e^{-(c+r)T}`.  Migration and mutation are zero after the split.

## Empirical status

None.  The bodies here are algebra on a finite matrix exponential and on real exponentials.
No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TwoLocusPortabilityDecay

open Descent.Coalescent

noncomputable section

/-! ## Eigen-rows of the exact matrix exponential -/

/-- **A left eigenvector of the generator decays exponentially along every trajectory.**  If
`w A = μ w`, then `w e^{tA} v = e^{tμ} w v`.

Assumes: `weight` is a left eigenvector of `A` with eigenvalue `μ`. -/
theorem sum_mul_matrixExponential_mulVec_of_left_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (weight : ι → ℝ) (μ time : ℝ) (state : ι → ℝ)
    (heigen : ∀ column, ∑ row, weight row * A row column = μ * weight column) :
    ∑ row, weight row * (matrixExponential A time).mulVec state row
      = Real.exp (time * μ) * ∑ row, weight row * state row := by
  let select : Matrix Unit ι ℝ := fun _ column ↦ weight column
  have hgenerator : select * A = (μ • (1 : Matrix Unit Unit ℝ)) * select := by
    ext _ column
    simp [Matrix.mul_apply, select, heigen]
  have hscalar : matrixExponential (μ • (1 : Matrix Unit Unit ℝ)) time
      = Real.exp (time * μ) • (1 : Matrix Unit Unit ℝ) := by
    have h := SubstochasticGeneratorSemigroup.matrixExponential_scalar_shift
      (0 : Matrix Unit Unit ℝ) μ time
    rwa [zero_add, matrixExponential_zero_matrix] at h
  have hsemigroup := matrixExponential_intertwines select A (μ • (1 : Matrix Unit Unit ℝ))
    hgenerator time
  rw [hscalar, Matrix.smul_mul, Matrix.one_mul] at hsemigroup
  have happ := congrFun (congrArg (fun matrix ↦ matrix.mulVec state) hsemigroup) ()
  simp only [← Matrix.mulVec_mulVec] at happ
  simpa [Matrix.mulVec, dotProduct, select, Finset.mul_sum, mul_assoc] using happ

/-- **A coordinate whose generator row is `μ` times its own unit row is multiplied by `e^{tμ}`.**

Assumes: the row of `coordinate` is `μ` times its unit row. -/
theorem matrixExponential_mulVec_apply_of_row_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time μ : ℝ) (state : ι → ℝ) (coordinate : ι)
    (hrow : ∀ column, A coordinate column = μ * (if column = coordinate then 1 else 0)) :
    (matrixExponential A time).mulVec state coordinate
      = Real.exp (time * μ) * state coordinate := by
  have h := sum_mul_matrixExponential_mulVec_of_left_eigen A
    (fun row ↦ if row = coordinate then 1 else 0) μ time state
    (fun column ↦ by simp [ite_mul, hrow])
  simpa [ite_mul] using h

variable {D : ℕ}

/-! ## The split history -/

/-- **The moment vector of a split history.**  The ancestral vector is split from deme `parent`
into deme `child`, and the joint vector then evolves for `duration` under `rates`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A composition of two corpus instructions. -/
def splitHistoryState (rates : ManyDemeLDRates D) (parent child : Fin D) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    AffineLowOrderLDCoordinate D → ℝ :=
  propagateLowOrderLDInstructions
    [LowOrderLDInstruction.split parent child, .evolve (rates.epoch duration hduration)] ancestral

/-- The split history is the corpus epoch propagator applied to the split vector. -/
theorem splitHistoryState_eq (rates : ManyDemeLDRates D) (parent child : Fin D) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState rates parent child hduration ancestral
      = (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec
          ((lowOrderLDSplitTransform parent child).mulVec ancestral) :=
  rfl

/-- Right after the split, the cross-population `DD` coordinate is the ancestral `DD`.

Assumes: `parent ≠ child`. -/
theorem splitTransform_DD {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDSplitTransform parent child).mulVec ancestral (some (.DD parent child))
      = ancestral (some (.DD parent parent)) := by
  rw [lowOrderLDSplitTransform_mulVec]
  simp [LowOrderLDCoordinate.mergeSplit, hne]

/-- Right after the split, the cross-population `pi2` coordinate is the ancestral `pi2`.

Assumes: `parent ≠ child`. -/
theorem splitTransform_pi2 {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDSplitTransform parent child).mulVec ancestral
        (some (.pi2 parent parent child child))
      = ancestral (some (.pi2 parent parent parent parent)) := by
  rw [lowOrderLDSplitTransform_mulVec]
  simp [LowOrderLDCoordinate.mergeSplit, hne]

/-! ## The diagonal rows -/

/-- **The cross-population `DD` row is diagonal.**  With no migration and no mutation, the row of
`E[D_i D_j]` for two different demes reads only that coordinate, at the rate
`c_i + c_j + (ρ_i + ρ_j)/2`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_DD_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D}
    (hne : first ≠ second) (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.DD first second)) column
      = -(rates.coalescence first + rates.coalescence second
          + (rates.recombination first + rates.recombination second) / 2)
        * (if column = some (.DD first second) then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    by_cases hcolumn : column = .DD first second
    · subst hcolumn
      simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne]
      ring
    · simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne,
        hcolumn, Ne.symm hcolumn]

/-- **The cross-population heterozygosity row is diagonal.**  With no migration and no mutation,
the row of `E[π^A_i π^B_j]` for two different demes reads only that coordinate, at the rate
`c_i + c_j`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_pi2_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D}
    (hne : first ≠ second) (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.pi2 first first second second)) column
      = -(rates.coalescence first + rates.coalescence second)
        * (if column = some (.pi2 first first second second) then 1 else 0) := by
  have hne' : second ≠ first := Ne.symm hne
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    by_cases hcolumn : column = .pi2 first first second second
    · subst hcolumn
      simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne, hne']
    · simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne, hne',
        hcolumn, Ne.symm hcolumn]

/-! ## The cross moments in closed form -/

/-- **The cross-population linkage covariance decays at `c_S + c_T + (ρ_S + ρ_T)/2`.**

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem splitHistoryState_DD (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState rates parent child hduration ancestral (some (.DD parent child))
      = Real.exp (-(rates.coalescence parent + rates.coalescence child
          + (rates.recombination parent + rates.recombination child) / 2) * duration)
        * ancestral (some (.DD parent parent)) := by
  rw [splitHistoryState_eq, matrixExponential_mulVec_apply_of_row_eq _ duration _ _ _
    (augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne),
    splitTransform_DD hne, mul_comm duration]

/-- **The cross-population heterozygosity product decays at `c_S + c_T`.**

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem splitHistoryState_pi2 (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState rates parent child hduration ancestral
        (some (.pi2 parent parent child child))
      = Real.exp (-(rates.coalescence parent + rates.coalescence child) * duration)
        * ancestral (some (.pi2 parent parent parent parent)) := by
  rw [splitHistoryState_eq, matrixExponential_mulVec_apply_of_row_eq _ duration _ _ _
    (augmentedLowOrderLDGenerator_pi2_row rates hmigration hmutation hne),
    splitTransform_pi2 hne, mul_comm duration]

/-! ## The portability law -/

/-- **The closed-form portability decay** `e^{-r T}` at recombination rate `r` and split time
`T`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A real exponential. -/
def portabilityDecay (rate duration : ℝ) : ℝ :=
  Real.exp (-(rate * duration))

/-- **The cross-population expected squared correlation of the split history**,
`E[D_S D_T] / E[π^A_S π^B_T]` as a ratio of expectations.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two moment coordinates. -/
def crossSquaredCorrelation (rates : ManyDemeLDRates D) (parent child : Fin D) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  splitHistoryState rates parent child hduration ancestral (some (.DD parent child))
    / splitHistoryState rates parent child hduration ancestral
        (some (.pi2 parent parent child child))

/-- **The ancestral expected squared correlation** `σ²_D = E[D²] / E[π^A π^B]` of one deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two moment coordinates. -/
def ancestralSquaredCorrelation (ancestral : AffineLowOrderLDCoordinate D → ℝ) (deme : Fin D) :
    ℝ :=
  ancestral (some (.DD deme deme)) / ancestral (some (.pi2 deme deme deme deme))

/-- **The target-to-source portability ratio** `σ²_{S→T}(T) / σ²_D(0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of moment coordinates. -/
def splitPortabilityRatio (rates : ManyDemeLDRates D) (parent child : Fin D) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  crossSquaredCorrelation rates parent child hduration ancestral
    / ancestralSquaredCorrelation ancestral parent

/-- **The cross-population expected squared correlation is the ancestral one times `e^{-rT}`**,
with `r = (ρ_S + ρ_T)/2`.  Drift does not enter.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem crossSquaredCorrelation_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    crossSquaredCorrelation rates parent child hduration ancestral
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
        * ancestralSquaredCorrelation ancestral parent := by
  have hfactor : Real.exp (-(rates.coalescence parent + rates.coalescence child
        + (rates.recombination parent + rates.recombination child) / 2) * duration)
      = Real.exp (-(rates.coalescence parent + rates.coalescence child) * duration)
        * portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration := by
    rw [portabilityDecay, ← Real.exp_add]
    congr 1
    ring
  rw [crossSquaredCorrelation, splitHistoryState_DD rates hmigration hmutation hne,
    splitHistoryState_pi2 rates hmigration hmutation hne, hfactor, mul_assoc,
    mul_div_mul_left _ _ (Real.exp_pos _).ne', ancestralSquaredCorrelation, mul_div_assoc]

/-- **F9, the two-locus portability decay law.**  The target-to-source ratio of the expected
squared correlation of a tag-locus score is exactly `e^{-rT}`, `r = (ρ_S + ρ_T)/2`.

Assumes: no migration, no mutation, `parent ≠ child`, and a nonzero ancestral correlation. -/
theorem splitPortabilityRatio_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) :
    splitPortabilityRatio rates parent child hduration ancestral
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration := by
  rw [splitPortabilityRatio, crossSquaredCorrelation_eq rates hmigration hmutation hne,
    mul_div_assoc, div_self hsource, mul_one]

/-- **The portability decay decreases with the split time.**

Assumes: `0 ≤ rate`. -/
theorem portabilityDecay_antitone_duration {rate : ℝ} (hrate : 0 ≤ rate) :
    Antitone (portabilityDecay rate) := by
  intro s t hst
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hst hrate))

/-- **The portability decay decreases with the recombination rate.**

Assumes: `0 ≤ duration`. -/
theorem portabilityDecay_antitone_rate {duration : ℝ} (hduration : 0 ≤ duration) :
    Antitone fun rate ↦ portabilityDecay rate duration := by
  intro s t hst
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hst hduration))

/-- **Portability through linkage is lost as the split time grows.**

Assumes: `0 < rate`. -/
theorem tendsto_portabilityDecay_atTop {rate : ℝ} (hrate : 0 < rate) :
    Filter.Tendsto (portabilityDecay rate) Filter.atTop (nhds 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hrate)

/-- Without recombination nothing is lost. -/
theorem portabilityDecay_zero_rate (duration : ℝ) : portabilityDecay 0 duration = 1 := by
  simp [portabilityDecay]

end

end Descent.Portability.TwoLocusPortabilityDecay
