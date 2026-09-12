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
- `splitHistoryState_pi2Cross_symmetric`: at equal rates the mixed heterozygosity
  `pi2(S, T, S, T)` is `pi2₀ + (c/(2β)) Dz₀ (1 - E) + (c/β)² DD₀ (1 - E)²`, `E = e^{-βT}`,
  `β = c + ρ/2`.
- `crossHeterozygosityPortabilityRatio_eq`: the target-to-source ratio of
  `E[D_S D_T] / pi2(S, T, S, T)` is
  `crossHeterozygosityDecay = E² / (1 + (c/(2β)) (Dz₀/pi2₀) (1 - E) + (c/β)² (DD₀/pi2₀) (1 - E)²)`.
- `crossHeterozygosityDecay_antitoneOn_duration`, `crossHeterozygosityDecay_antitoneOn_rate`,
  `tendsto_crossHeterozygosityDecay_atTop`: with nonnegative ancestral ratios it decreases in
  the split time and in the linkage rate, and tends to `0` as `T → ∞`.  Here drift enters.

## Significance

Portability through linkage decays with split time and recombination distance, and drift does
not enter.  Drift lowers the cross-population linkage covariance at rate `c_S + c_T` and the
cross-population heterozygosity product at the same rate, so it cancels from the ratio exactly,
whatever the two drift rates are.  What remains is the recombination clock alone.

## Relation to the end-to-end law F8

`EndToEndPortabilityLaw.expectedPortability` is a within-deme ratio of expectations,
`(E N_t · E D_s) / (E D_t · E N_s)` with `N = 16 C_SY²` and `D = 16 V_S V_Y` of NOTE2 (21).
For a single tag-locus score with a fixed weight, after a split at equal rates with no migration
or mutation, the source and target demes have one law, so that ratio is `1` whenever it is
defined: a fixed single-tag score keeps its expected squared correlation.  The loss through
linkage enters only when the score weight is the source's own linkage covariance, which brings
in the cross moment `E[D_S D_T]`.  That cross moment is the statistic of this module, a readout
of cross-deme coordinates rather than one of the F8 functionals.  This paragraph records the
distinction; no theorem here states the F8 value.

## The mechanism

A coordinate whose generator row is `μ` times its own unit row is multiplied by `e^{μ t}` along
every trajectory of the exact matrix exponential (`matrixExponential_mulVec_apply_of_row_eq`),
through the one-row intertwining `matrixExponential_intertwines` and the scalar exponential
`SubstochasticGeneratorSemigroup.matrixExponential_scalar_shift`.  With no migration and no
mutation, the rows of `DD(i, j)` and `pi2(i, i, j, j)` for `i ≠ j` are of that form
(`augmentedLowOrderLDGenerator_DD_row`, `augmentedLowOrderLDGenerator_pi2_row`).  The mixed
block `DD(S, T), DD(T, S), Dz(S, T, T), Dz(T, S, S), pi2(S, T, S, T)` is triangular, and its left
eigenvectors give one decaying combination per `Dz` coordinate
(`matrixExponential_Dz_combination`) and one conserved combination for `pi2`
(`matrixExponential_pi2Cross_combination`).  The monotonicity in the rate reads the secant
slopes of the convex exponential (`exp_sub_one_mul_le`, `mul_one_sub_exp_neg_le`).

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
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    by_cases hcolumn : column = .pi2 first first second second
    · subst hcolumn
      simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne]
    · simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne,
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

/-! ## The cross-heterozygosity block -/

/-- A point mass reads a vector at its point. -/
theorem sum_pointMass_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (coeff : ℝ) (point : ι)
    (vector : ι → ℝ) :
    ∑ row, coeff * (if row = point then 1 else 0) * vector row = coeff * vector point := by
  simp [mul_ite, ite_mul, Finset.sum_ite_eq']

/-- A unit point mass reads a vector at its point. -/
theorem sum_unitPointMass_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (point : ι)
    (vector : ι → ℝ) : ∑ row, (if row = point then 1 else 0) * vector row = vector point := by
  simp [ite_mul, Finset.sum_ite_eq']

/-- **The linkage decay rate** `c_i + ρ_i/2` of one deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A sum of two rates. -/
def linkageRate (rates : ManyDemeLDRates D) (deme : Fin D) : ℝ :=
  rates.coalescence deme + rates.recombination deme / 2

/-- The linkage decay rate is positive. -/
theorem linkageRate_pos (rates : ManyDemeLDRates D) (deme : Fin D) : 0 < linkageRate rates deme :=
  add_pos_of_pos_of_nonneg (rates.coalescence_pos deme)
    (div_nonneg (rates.recombination_nonneg deme) zero_le_two)

/-- **The cross-population `Dz` row.**  With no migration and no mutation, the row of
`E[D_i z^A_j z^B_j]` for two different demes reads
`4 c_j E[D_i D_j] - (c_i + ρ_i/2) E[D_i z_j z_j]`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_Dz_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D}
    (hne : first ≠ second) (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.Dz first second second)) column
      = 4 * rates.coalescence second * (if column = some (.DD first second) then 1 else 0)
        - (rates.coalescence first + rates.recombination first / 2)
          * (if column = some (.Dz first second second) then 1 else 0) := by
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    by_cases hDD : column = .DD first second
    · subst hDD
      simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne]
    · by_cases hDz : column = .Dz first second second
      · subst hDz
        simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
          lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
          lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne]
        ring
      · simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
          lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
          lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne,
          hDD, hDz, Ne.symm hDD, Ne.symm hDz]

/-- **The cross-population mixed heterozygosity row.**  With no migration and no mutation, the
row of `pi2(i, j, i, j)` for two different demes reads
`(c_i/4) E[D_i z_j z_j] + (c_j/4) E[D_j z_i z_i]`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem augmentedLowOrderLDGenerator_pi2Cross_row (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D}
    (hne : first ≠ second) (column : AffineLowOrderLDCoordinate D) :
    augmentedLowOrderLDGenerator rates (some (.pi2 first second first second)) column
      = rates.coalescence first / 4 * (if column = some (.Dz first second second) then 1 else 0)
        + rates.coalescence second / 4
          * (if column = some (.Dz second first first) then 1 else 0) := by
  have hne' : second ≠ first := Ne.symm hne
  cases column with
  | none => simp [augmentedLowOrderLDGenerator, lowOrderLDMutationForcing]
  | some column =>
    by_cases hleft : column = .Dz first second second
    · subst hleft
      simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
        lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
        lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne,
        hne']
    · by_cases hright : column = .Dz second first first
      · subst hright
        simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
          lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
          lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne,
          hne']
      · simp [augmentedLowOrderLDGenerator, lowOrderLDHomogeneousGenerator, lowOrderLDDrift,
          lowOrderLDMigration, lowOrderLDRecombination, lowOrderLDMutationCoupling,
          lowOrderLDRecurrentMutationDamping, lowOrderLDBasis, hmigration, hmutation, hne,
          hne', hleft, hright, Ne.symm hleft, Ne.symm hright]

/-- **The linkage-contrast combination decays at `c_i + ρ_i/2`.**  Along every trajectory,
`Dz(i, j, j) + (4 c_j / (c_j + ρ_j/2)) DD(i, j)` is multiplied by `e^{-(c_i + ρ_i/2) t}`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem matrixExponential_Dz_combination (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D}
    (hne : first ≠ second) (duration : ℝ) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
          (some (.Dz first second second))
        + 4 * rates.coalescence second / linkageRate rates second
          * (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
            (some (.DD first second))
      = Real.exp (-linkageRate rates first * duration)
        * (state (some (.Dz first second second))
          + 4 * rates.coalescence second / linkageRate rates second
            * state (some (.DD first second))) := by
  have hα : 4 * rates.coalescence second / linkageRate rates second * linkageRate rates second
      = 4 * rates.coalescence second :=
    div_mul_cancel₀ _ (linkageRate_pos rates second).ne'
  have h := sum_mul_matrixExponential_mulVec_of_left_eigen (augmentedLowOrderLDGenerator rates)
    (fun row : AffineLowOrderLDCoordinate D ↦
      1 * (if row = some (LowOrderLDCoordinate.Dz first second second) then 1 else 0)
        + 4 * rates.coalescence second / linkageRate rates second
          * (if row = some (LowOrderLDCoordinate.DD first second) then 1 else 0))
    (-linkageRate rates first) duration state (fun column ↦ by
      simp only [add_mul, Finset.sum_add_distrib, sum_pointMass_mul]
      rw [augmentedLowOrderLDGenerator_Dz_row rates hmigration hmutation hne,
        augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne]
      unfold linkageRate at hα ⊢
      linear_combination
        (-(if column = some (LowOrderLDCoordinate.DD first second) then (1 : ℝ) else 0)) * hα)
  simp only [add_mul, Finset.sum_add_distrib, sum_pointMass_mul, one_mul,
    sum_unitPointMass_mul] at h
  rw [mul_comm duration] at h
  exact h

/-- **The mixed heterozygosity combination is conserved.**  Along every trajectory,
`pi2(i, j, i, j) + γ_i Dz(i, j, j) + γ_j Dz(j, i, i) + δ_i DD(i, j) + δ_j DD(j, i)` is constant,
with `γ_i = c_i / (4 β_i)`, `δ_i = c_i c_j / (β_i (β_i + β_j))` and `β_i = c_i + ρ_i/2`.

Assumes: no migration, no mutation, and `first ≠ second`. -/
theorem matrixExponential_pi2Cross_combination (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {first second : Fin D}
    (hne : first ≠ second) (duration : ℝ) (state : AffineLowOrderLDCoordinate D → ℝ) :
    (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
          (some (.pi2 first second first second))
        + rates.coalescence first / (4 * linkageRate rates first)
          * (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
            (some (.Dz first second second))
        + rates.coalescence second / (4 * linkageRate rates second)
          * (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
            (some (.Dz second first first))
        + rates.coalescence first * rates.coalescence second
            / (linkageRate rates first * (linkageRate rates first + linkageRate rates second))
          * (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
            (some (.DD first second))
        + rates.coalescence first * rates.coalescence second
            / (linkageRate rates second * (linkageRate rates first + linkageRate rates second))
          * (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state
            (some (.DD second first))
      = state (some (.pi2 first second first second))
        + rates.coalescence first / (4 * linkageRate rates first)
          * state (some (.Dz first second second))
        + rates.coalescence second / (4 * linkageRate rates second)
          * state (some (.Dz second first first))
        + rates.coalescence first * rates.coalescence second
            / (linkageRate rates first * (linkageRate rates first + linkageRate rates second))
          * state (some (.DD first second))
        + rates.coalescence first * rates.coalescence second
            / (linkageRate rates second * (linkageRate rates first + linkageRate rates second))
          * state (some (.DD second first)) := by
  have hne' : second ≠ first := Ne.symm hne
  have hfirst := (linkageRate_pos rates first).ne'
  have hsecond := (linkageRate_pos rates second).ne'
  have hsum : linkageRate rates first + linkageRate rates second ≠ 0 :=
    (add_pos (linkageRate_pos rates first) (linkageRate_pos rates second)).ne'
  have hγfirst : rates.coalescence first / (4 * linkageRate rates first) * linkageRate rates first
      = rates.coalescence first / 4 := by
    field_simp
  have hγsecond : rates.coalescence second / (4 * linkageRate rates second)
        * linkageRate rates second = rates.coalescence second / 4 := by
    field_simp
  have hδfirst : rates.coalescence first * rates.coalescence second
          / (linkageRate rates first * (linkageRate rates first + linkageRate rates second))
        * (linkageRate rates first + linkageRate rates second)
      = 4 * rates.coalescence second
        * (rates.coalescence first / (4 * linkageRate rates first)) := by
    field_simp
  have hδsecond : rates.coalescence first * rates.coalescence second
          / (linkageRate rates second * (linkageRate rates first + linkageRate rates second))
        * (linkageRate rates first + linkageRate rates second)
      = 4 * rates.coalescence first
        * (rates.coalescence second / (4 * linkageRate rates second)) := by
    field_simp
  have h := sum_mul_matrixExponential_mulVec_of_left_eigen (augmentedLowOrderLDGenerator rates)
    (fun row : AffineLowOrderLDCoordinate D ↦
      1 * (if row = some (LowOrderLDCoordinate.pi2 first second first second) then 1 else 0)
        + rates.coalescence first / (4 * linkageRate rates first)
          * (if row = some (LowOrderLDCoordinate.Dz first second second) then 1 else 0)
        + rates.coalescence second / (4 * linkageRate rates second)
          * (if row = some (LowOrderLDCoordinate.Dz second first first) then 1 else 0)
        + rates.coalescence first * rates.coalescence second
            / (linkageRate rates first * (linkageRate rates first + linkageRate rates second))
          * (if row = some (LowOrderLDCoordinate.DD first second) then 1 else 0)
        + rates.coalescence first * rates.coalescence second
            / (linkageRate rates second * (linkageRate rates first + linkageRate rates second))
          * (if row = some (LowOrderLDCoordinate.DD second first) then 1 else 0))
    0 duration state (fun column ↦ by
      simp only [add_mul, Finset.sum_add_distrib, sum_pointMass_mul, zero_mul]
      rw [augmentedLowOrderLDGenerator_pi2Cross_row rates hmigration hmutation hne,
        augmentedLowOrderLDGenerator_Dz_row rates hmigration hmutation hne,
        augmentedLowOrderLDGenerator_Dz_row rates hmigration hmutation hne',
        augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne,
        augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne']
      unfold linkageRate at hγfirst hγsecond hδfirst hδsecond ⊢
      linear_combination
        (-(if column = some (LowOrderLDCoordinate.Dz first second second) then (1 : ℝ) else 0))
            * hγfirst
          - (if column = some (LowOrderLDCoordinate.Dz second first first) then (1 : ℝ) else 0)
            * hγsecond
          - (if column = some (LowOrderLDCoordinate.DD first second) then (1 : ℝ) else 0)
            * hδfirst
          - (if column = some (LowOrderLDCoordinate.DD second first) then (1 : ℝ) else 0)
            * hδsecond)
  simp only [add_mul, Finset.sum_add_distrib, sum_pointMass_mul, one_mul, mul_zero, Real.exp_zero,
    sum_unitPointMass_mul] at h
  exact h

/-- Right after the split, every coordinate of the cross-heterozygosity block is the matching
ancestral coordinate.

Assumes: `parent ≠ child`. -/
theorem splitTransform_block {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDSplitTransform parent child).mulVec ancestral (some (.DD child parent))
        = ancestral (some (.DD parent parent)) ∧
      (lowOrderLDSplitTransform parent child).mulVec ancestral
          (some (.Dz parent child child)) = ancestral (some (.Dz parent parent parent)) ∧
      (lowOrderLDSplitTransform parent child).mulVec ancestral
          (some (.Dz child parent parent)) = ancestral (some (.Dz parent parent parent)) ∧
      (lowOrderLDSplitTransform parent child).mulVec ancestral
          (some (.pi2 parent child parent child))
        = ancestral (some (.pi2 parent parent parent parent)) := by
  rw [lowOrderLDSplitTransform_mulVec]
  simp [LowOrderLDCoordinate.mergeSplit, hne]

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

/-! ## The cross-heterozygosity portability law -/

/-- **The closed-form cross-heterozygosity decay.**  At drift `c`, linkage rate `β = c + r`,
ancestral ratios `contrast = Dz₀/pi2₀` and `linkage = DD₀/pi2₀`, and split time `T`, with
`E = e^{-βT}`, the value `E² / (1 + (c/(2β)) contrast (1 - E) + (c/β)² linkage (1 - E)²)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A rational expression in a real exponential. -/
def crossHeterozygosityDecay (coalescence rate contrast linkage duration : ℝ) : ℝ :=
  Real.exp (-rate * duration) ^ 2
    / (1 + coalescence / (2 * rate) * contrast * (1 - Real.exp (-rate * duration))
      + (coalescence / rate) ^ 2 * linkage * (1 - Real.exp (-rate * duration)) ^ 2)

/-- **The cross-heterozygosity expected squared correlation of the split history**,
`E[D_S D_T] / pi2(S, T, S, T)` as a ratio of expectations.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two moment coordinates. -/
def crossHeterozygositySquaredCorrelation (rates : ManyDemeLDRates D) (parent child : Fin D)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    ℝ :=
  splitHistoryState rates parent child hduration ancestral (some (.DD parent child))
    / splitHistoryState rates parent child hduration ancestral
        (some (.pi2 parent child parent child))

/-- **The cross-heterozygosity portability ratio** `σ̃²_{S→T}(T) / σ²_D(0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of moment coordinates. -/
def crossHeterozygosityPortabilityRatio (rates : ManyDemeLDRates D) (parent child : Fin D)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    ℝ :=
  crossHeterozygositySquaredCorrelation rates parent child hduration ancestral
    / ancestralSquaredCorrelation ancestral parent

/-- **At equal rates the cross-population linkage covariance is `E² DD₀`**, `E = e^{-βT}`.

Assumes: no migration, no mutation, `parent ≠ child`, and equal drift and recombination rates. -/
theorem splitHistoryState_DD_symmetric (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState rates parent child hduration ancestral (some (.DD parent child))
      = Real.exp (-linkageRate rates parent * duration) ^ 2
        * ancestral (some (.DD parent parent)) := by
  rw [splitHistoryState_DD rates hmigration hmutation hne, hcoal, hrec, sq, ← Real.exp_add]
  congr 2
  unfold linkageRate
  ring

/-- **At equal rates the mixed heterozygosity has a closed form**:
`pi2(S, T, S, T)(T) = pi2₀ + (c/(2β)) Dz₀ (1 - E) + (c/β)² DD₀ (1 - E)²`, `E = e^{-βT}`.

Assumes: no migration, no mutation, `parent ≠ child`, and equal drift and recombination rates. -/
theorem splitHistoryState_pi2Cross_symmetric (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState rates parent child hduration ancestral
        (some (.pi2 parent child parent child))
      = ancestral (some (.pi2 parent parent parent parent))
        + rates.coalescence parent / (2 * linkageRate rates parent)
          * ancestral (some (.Dz parent parent parent))
          * (1 - Real.exp (-linkageRate rates parent * duration))
        + (rates.coalescence parent / linkageRate rates parent) ^ 2
          * ancestral (some (.DD parent parent))
          * (1 - Real.exp (-linkageRate rates parent * duration)) ^ 2 := by
  have hne' : child ≠ parent := Ne.symm hne
  have hβ : linkageRate rates child = linkageRate rates parent := by
    unfold linkageRate
    rw [hcoal, hrec]
  have ha := splitHistoryState_DD_symmetric rates hmigration hmutation hne hcoal hrec hduration
    ancestral
  have ha' : (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec
        ((lowOrderLDSplitTransform parent child).mulVec ancestral) (some (.DD child parent))
      = Real.exp (-linkageRate rates parent * duration) ^ 2
        * ancestral (some (.DD parent parent)) := by
    rw [matrixExponential_mulVec_apply_of_row_eq _ duration _ _ _
      (augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne'),
      (splitTransform_block hne ancestral).1, hcoal, hrec, mul_comm duration, sq,
      ← Real.exp_add]
    congr 2
    unfold linkageRate
    ring
  have hb := matrixExponential_Dz_combination rates hmigration hmutation hne duration
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  have hb' := matrixExponential_Dz_combination rates hmigration hmutation hne' duration
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  have hπ := matrixExponential_pi2Cross_combination rates hmigration hmutation hne duration
    ((lowOrderLDSplitTransform parent child).mulVec ancestral)
  obtain ⟨h0DD, h0Dz, h0Dz', h0pi2⟩ := splitTransform_block hne ancestral
  rw [splitHistoryState_eq] at ha ⊢
  rw [h0Dz, splitTransform_DD hne, hcoal, hβ] at hb
  rw [h0Dz', h0DD, hβ] at hb'
  rw [h0pi2, h0Dz, h0Dz', splitTransform_DD hne, h0DD, hcoal, hβ] at hπ
  linear_combination hπ
    - rates.coalescence parent / (4 * linkageRate rates parent) * hb
    - rates.coalescence parent / (4 * linkageRate rates parent) * hb'
    + (rates.coalescence parent / (4 * linkageRate rates parent)
        * (4 * rates.coalescence parent / linkageRate rates parent)
      - rates.coalescence parent * rates.coalescence parent
        / (linkageRate rates parent * (linkageRate rates parent + linkageRate rates parent)))
      * ha
    + (rates.coalescence parent / (4 * linkageRate rates parent)
        * (4 * rates.coalescence parent / linkageRate rates parent)
      - rates.coalescence parent * rates.coalescence parent
        / (linkageRate rates parent * (linkageRate rates parent + linkageRate rates parent)))
      * ha'

/-- **F9, the cross-heterozygosity portability law.**  At equal rates, the target-to-source
ratio of `E[D_S D_T] / pi2(S, T, S, T)` is `crossHeterozygosityDecay c β (Dz₀/pi2₀) (DD₀/pi2₀) T`.

Assumes: no migration, no mutation, `parent ≠ child`, equal drift and recombination rates,
positive ancestral `pi2` and `DD`, and nonnegative ancestral `Dz`. -/
theorem crossHeterozygosityPortabilityRatio_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D}
    (hne : parent ≠ child) (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hpi2 : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hDD : 0 < ancestral (some (.DD parent parent)))
    (hDz : 0 ≤ ancestral (some (.Dz parent parent parent))) :
    crossHeterozygosityPortabilityRatio rates parent child hduration ancestral
      = crossHeterozygosityDecay (rates.coalescence parent) (linkageRate rates parent)
          (ancestral (some (.Dz parent parent parent))
            / ancestral (some (.pi2 parent parent parent parent)))
          (ancestral (some (.DD parent parent))
            / ancestral (some (.pi2 parent parent parent parent))) duration := by
  have hβ := linkageRate_pos rates parent
  have hc := rates.coalescence_pos parent
  have hE : 0 ≤ 1 - Real.exp (-linkageRate rates parent * duration) := by
    rw [sub_nonneg, Real.exp_le_one_iff]
    nlinarith
  have hden : 0 < ancestral (some (.pi2 parent parent parent parent))
      + rates.coalescence parent / (2 * linkageRate rates parent)
        * ancestral (some (.Dz parent parent parent))
        * (1 - Real.exp (-linkageRate rates parent * duration))
      + (rates.coalescence parent / linkageRate rates parent) ^ 2
        * ancestral (some (.DD parent parent))
        * (1 - Real.exp (-linkageRate rates parent * duration)) ^ 2 := by
    positivity
  have hratio : 1 + rates.coalescence parent / (2 * linkageRate rates parent)
          * (ancestral (some (.Dz parent parent parent))
            / ancestral (some (.pi2 parent parent parent parent)))
          * (1 - Real.exp (-linkageRate rates parent * duration))
        + (rates.coalescence parent / linkageRate rates parent) ^ 2
          * (ancestral (some (.DD parent parent))
            / ancestral (some (.pi2 parent parent parent parent)))
          * (1 - Real.exp (-linkageRate rates parent * duration)) ^ 2
      = (ancestral (some (.pi2 parent parent parent parent))
          + rates.coalescence parent / (2 * linkageRate rates parent)
            * ancestral (some (.Dz parent parent parent))
            * (1 - Real.exp (-linkageRate rates parent * duration))
          + (rates.coalescence parent / linkageRate rates parent) ^ 2
            * ancestral (some (.DD parent parent))
            * (1 - Real.exp (-linkageRate rates parent * duration)) ^ 2)
        / ancestral (some (.pi2 parent parent parent parent)) := by
    field_simp
  rw [crossHeterozygosityPortabilityRatio, crossHeterozygositySquaredCorrelation,
    splitHistoryState_DD_symmetric rates hmigration hmutation hne hcoal hrec,
    splitHistoryState_pi2Cross_symmetric rates hmigration hmutation hne hcoal hrec,
    ancestralSquaredCorrelation, crossHeterozygosityDecay, hratio]
  field_simp

/-- **The cross-heterozygosity decay decreases with the split time.**

Assumes: positive drift and linkage rate, and nonnegative ancestral ratios. -/
theorem crossHeterozygosityDecay_antitoneOn_duration {coalescence rate contrast linkage : ℝ}
    (hc : 0 < coalescence) (hrate : 0 < rate) (hcontrast : 0 ≤ contrast)
    (hlinkage : 0 ≤ linkage) :
    AntitoneOn (crossHeterozygosityDecay coalescence rate contrast linkage) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs
  have hEt : Real.exp (-rate * t) ≤ Real.exp (-rate * s) := Real.exp_le_exp.mpr (by nlinarith)
  have hEs : Real.exp (-rate * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hEt0 := Real.exp_pos (-rate * t)
  have hEs0 := Real.exp_pos (-rate * s)
  have h1 : 1 - Real.exp (-rate * s) ≤ 1 - Real.exp (-rate * t) := by linarith
  have h1s : 0 ≤ 1 - Real.exp (-rate * s) := by linarith
  have hA : 0 ≤ coalescence / (2 * rate) * contrast :=
    mul_nonneg (div_nonneg hc.le (by linarith)) hcontrast
  have hB : 0 ≤ (coalescence / rate) ^ 2 * linkage := mul_nonneg (sq_nonneg _) hlinkage
  have hsq : Real.exp (-rate * t) ^ 2 ≤ Real.exp (-rate * s) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hEt hEt hEt0.le hEs0.le
  have hden : 0 < 1 + coalescence / (2 * rate) * contrast * (1 - Real.exp (-rate * s))
      + (coalescence / rate) ^ 2 * linkage * (1 - Real.exp (-rate * s)) ^ 2 := by
    have := mul_nonneg hA h1s
    have := mul_nonneg hB (sq_nonneg (1 - Real.exp (-rate * s)))
    linarith
  have hle : 1 + coalescence / (2 * rate) * contrast * (1 - Real.exp (-rate * s))
        + (coalescence / rate) ^ 2 * linkage * (1 - Real.exp (-rate * s)) ^ 2
      ≤ 1 + coalescence / (2 * rate) * contrast * (1 - Real.exp (-rate * t))
        + (coalescence / rate) ^ 2 * linkage * (1 - Real.exp (-rate * t)) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 hA
    have hsq1 : (1 - Real.exp (-rate * s)) ^ 2 ≤ (1 - Real.exp (-rate * t)) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul h1 h1 h1s (h1s.trans h1)
    have := mul_le_mul_of_nonneg_left hsq1 hB
    linarith
  exact div_le_div₀ (sq_nonneg _) hsq hden hle

/-- **Portability through the cross heterozygosity is lost as the split time grows.**

Assumes: positive drift and linkage rate, and nonnegative ancestral ratios. -/
theorem tendsto_crossHeterozygosityDecay_atTop {coalescence rate contrast linkage : ℝ}
    (hc : 0 < coalescence) (hrate : 0 < rate) (hcontrast : 0 ≤ contrast)
    (hlinkage : 0 ≤ linkage) :
    Filter.Tendsto (crossHeterozygosityDecay coalescence rate contrast linkage) Filter.atTop
      (nhds 0) := by
  have hE : Filter.Tendsto (fun t : ℝ ↦ Real.exp (-rate * t)) Filter.atTop (nhds 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop hrate)).congr fun t ↦ by simp [neg_mul]
  have hA : 0 ≤ coalescence / (2 * rate) * contrast :=
    mul_nonneg (div_nonneg hc.le (by linarith)) hcontrast
  have hB : 0 ≤ (coalescence / rate) ^ 2 * linkage := mul_nonneg (sq_nonneg _) hlinkage
  have hden : Filter.Tendsto (fun t : ℝ ↦ 1 + coalescence / (2 * rate) * contrast
        * (1 - Real.exp (-rate * t))
      + (coalescence / rate) ^ 2 * linkage * (1 - Real.exp (-rate * t)) ^ 2) Filter.atTop
      (nhds (1 + coalescence / (2 * rate) * contrast * (1 - 0)
        + (coalescence / rate) ^ 2 * linkage * (1 - 0) ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub hE))).add
      (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hE).pow 2))
  have hpos : 1 + coalescence / (2 * rate) * contrast * (1 - 0)
      + (coalescence / rate) ^ 2 * linkage * (1 - 0) ^ 2 ≠ 0 := by
    have : 0 < 1 + coalescence / (2 * rate) * contrast * (1 - 0)
        + (coalescence / rate) ^ 2 * linkage * (1 - 0) ^ 2 := by
      norm_num
      linarith
    exact this.ne'
  have h := (hE.pow 2).div hden hpos
  rw [zero_pow two_ne_zero, zero_div] at h
  exact h

/-- The secant slope `(e^x - 1)/x` of the exponential from `0` increases: for `0 < x ≤ y`,
`(e^x - 1) y ≤ (e^y - 1) x`.

Assumes: `0 < x ≤ y`. -/
theorem exp_sub_one_mul_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (Real.exp x - 1) * y ≤ (Real.exp y - 1) * x := by
  have hy : 0 < y := hx.trans_le hxy
  have h := convexOn_exp.secant_mono (a := 0) (Set.mem_univ 0) (Set.mem_univ x)
    (Set.mem_univ y) hx.ne' hy.ne' hxy
  simp only [Real.exp_zero, sub_zero] at h
  rwa [div_le_div_iff₀ hx hy] at h

/-- The ratio `(1 - e^{-x})/x` decreases: for `0 < x ≤ y`, `x (1 - e^{-y}) ≤ y (1 - e^{-x})`.

Assumes: `0 < x ≤ y`. -/
theorem mul_one_sub_exp_neg_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x * (1 - Real.exp (-y)) ≤ y * (1 - Real.exp (-x)) := by
  have hy : 0 < y := hx.trans_le hxy
  have hconv : ConvexOn ℝ Set.univ fun z : ℝ ↦ Real.exp (-z) := by
    have h := convexOn_exp.comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    simpa [Function.comp_def] using h
  have h := hconv.secant_mono (a := 0) (Set.mem_univ 0) (Set.mem_univ x) (Set.mem_univ y)
    hx.ne' hy.ne' hxy
  simp only [neg_zero, Real.exp_zero, sub_zero] at h
  rw [div_le_div_iff₀ hx hy] at h
  linarith

/-- **The cross-heterozygosity decay decreases with the linkage rate.**  At fixed drift `c` a
larger recombination rate raises `β = c + r` and lowers the decay.

Assumes: positive drift, nonnegative ancestral ratios, and `0 ≤ duration`. -/
theorem crossHeterozygosityDecay_antitoneOn_rate {coalescence contrast linkage duration : ℝ}
    (hc : 0 < coalescence) (hcontrast : 0 ≤ contrast) (hlinkage : 0 ≤ linkage)
    (hduration : 0 ≤ duration) :
    AntitoneOn (fun rate ↦ crossHeterozygosityDecay coalescence rate contrast linkage duration)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  have hu0 : 0 < u := hu
  have hv0 : 0 < v := hv
  show crossHeterozygosityDecay coalescence v contrast linkage duration
    ≤ crossHeterozygosityDecay coalescence u contrast linkage duration
  rcases hduration.eq_or_lt with hT | hT
  · subst hT
    simp [crossHeterozygosityDecay]
  have hform : ∀ w : ℝ, 0 < w → 0 < 1 - Real.exp (-w * duration) →
      crossHeterozygosityDecay coalescence w contrast linkage duration
        = (w * Real.exp (-w * duration) / (1 - Real.exp (-w * duration))) ^ 2
          / ((w / (1 - Real.exp (-w * duration))) ^ 2
            + coalescence * contrast / 2 * (w / (1 - Real.exp (-w * duration)))
            + coalescence ^ 2 * linkage) := by
    intro w hw h1w
    have hwne := hw.ne'
    have h1wne := h1w.ne'
    have hm : (w / (1 - Real.exp (-w * duration))) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (div_pos hw h1w).ne'
    rw [crossHeterozygosityDecay, ← mul_div_mul_left (Real.exp (-w * duration) ^ 2)
      (1 + coalescence / (2 * w) * contrast * (1 - Real.exp (-w * duration))
        + (coalescence / w) ^ 2 * linkage * (1 - Real.exp (-w * duration)) ^ 2) hm]
    congr 1
    · ring
    · set q := 1 - Real.exp (-w * duration)
      first | (field_simp; ring) | field_simp
  have hEu := Real.exp_pos (-u * duration)
  have hEv := Real.exp_pos (-v * duration)
  have h1u : 0 < 1 - Real.exp (-u * duration) := by
    have : Real.exp (-u * duration) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by nlinarith)
    linarith
  have h1v : 0 < 1 - Real.exp (-v * duration) := by
    have : Real.exp (-v * duration) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by nlinarith)
    linarith
  have hxy : u * duration ≤ v * duration := mul_le_mul_of_nonneg_right huv hT.le
  have hsecant := exp_sub_one_mul_le (mul_pos hu0 hT) hxy
  have hsecant' := mul_one_sub_exp_neg_le (mul_pos hu0 hT) hxy
  rw [← neg_mul, ← neg_mul] at hsecant'
  have hexu : Real.exp (u * duration) * Real.exp (-u * duration) = 1 := by
    simp [← Real.exp_add]
  have hexv : Real.exp (v * duration) * Real.exp (-v * duration) = 1 := by
    simp [← Real.exp_add]
  have hq : u / (1 - Real.exp (-u * duration)) ≤ v / (1 - Real.exp (-v * duration)) := by
    rw [div_le_div_iff₀ h1u h1v]
    refine le_of_mul_le_mul_left ?_ hT
    linarith
  have hk : v * Real.exp (-v * duration) / (1 - Real.exp (-v * duration))
      ≤ u * Real.exp (-u * duration) / (1 - Real.exp (-u * duration)) := by
    rw [div_le_div_iff₀ h1v h1u]
    refine le_of_mul_le_mul_left ?_ hT
    have hscaled := mul_le_mul_of_nonneg_right hsecant (mul_pos hEu hEv).le
    have h3 : Real.exp (u * duration) * Real.exp (-u * duration)
        * (v * duration * Real.exp (-v * duration)) = v * duration * Real.exp (-v * duration) := by
      rw [hexu, one_mul]
    have h4 : Real.exp (v * duration) * Real.exp (-v * duration)
        * (u * duration * Real.exp (-u * duration)) = u * duration * Real.exp (-u * duration) := by
      rw [hexv, one_mul]
    linarith
  have hkv : 0 ≤ v * Real.exp (-v * duration) / (1 - Real.exp (-v * duration)) :=
    div_nonneg (mul_nonneg hv0.le hEv.le) h1v.le
  have hqu : 0 < u / (1 - Real.exp (-u * duration)) := div_pos hu0 h1u
  have hksq : (v * Real.exp (-v * duration) / (1 - Real.exp (-v * duration))) ^ 2
      ≤ (u * Real.exp (-u * duration) / (1 - Real.exp (-u * duration))) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hk hk hkv (hkv.trans hk)
  have hA : 0 ≤ coalescence * contrast / 2 :=
    div_nonneg (mul_nonneg hc.le hcontrast) zero_le_two
  have hB : 0 ≤ coalescence ^ 2 * linkage := mul_nonneg (sq_nonneg _) hlinkage
  have hDu : 0 < (u / (1 - Real.exp (-u * duration))) ^ 2
      + coalescence * contrast / 2 * (u / (1 - Real.exp (-u * duration)))
      + coalescence ^ 2 * linkage := by
    have := pow_pos hqu 2
    have := mul_nonneg hA hqu.le
    linarith
  have hDle : (u / (1 - Real.exp (-u * duration))) ^ 2
        + coalescence * contrast / 2 * (u / (1 - Real.exp (-u * duration)))
        + coalescence ^ 2 * linkage
      ≤ (v / (1 - Real.exp (-v * duration))) ^ 2
        + coalescence * contrast / 2 * (v / (1 - Real.exp (-v * duration)))
        + coalescence ^ 2 * linkage := by
    have hsq : (u / (1 - Real.exp (-u * duration))) ^ 2
        ≤ (v / (1 - Real.exp (-v * duration))) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul hq hq hqu.le (hqu.le.trans hq)
    have := mul_le_mul_of_nonneg_left hq hA
    linarith
  rw [hform u hu0 h1u, hform v hv0 h1v]
  exact div_le_div₀ (sq_nonneg _) hksq hDu hDle

end

end Descent.Portability.TwoLocusPortabilityDecay
