/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CalibrationPortabilityDecay
import Descent.Portability.MigrationPortabilityRemainder
import Mathlib.Analysis.SpecialFunctions.Sqrt

assert_below Descent.Decision Descent.Program

/-!
# Calibration portability under symmetric migration

`CalibrationPortabilityDecay` shows that for a trained score in standardized units, with different
pairs in linkage equilibrium, squared-correlation portability is the square of calibration
portability.  `MigrationPortabilityFactor`, `MigrationPortabilityFirstOrderFactor` and
`MigrationPortabilityRemainder` give the two-locus ratio `R_m` with symmetric migration `m`, its
derivative `φ₁(T)` at `m = 0` and an explicit second-order remainder.  This module carries the
three through the square law to the calibration slope.

## Main results

- `calibrationPortability_commonRetention`, `squaredCorrelationPortability_commonRetention`,
  `squaredCorrelationPortability_sqrtRetention`: if every pair keeps the fraction `κ` of its source
  correlation, calibration portability is `κ` and squared-correlation portability is `κ²`.  So a
  nonnegative ratio `R` is the squared-correlation portability of the score at `κ = √R`, whose
  calibration portability is `√R`.  Both reuse
  `CalibrationPortabilityDecay.squaredCorrelationPortability_eq_calibrationPortability_sq`.
- `calibrationPortability_migration`, `squaredCorrelationPortability_migration`: with migration,
  the score at retention `√R_m` has calibration portability `√R_m` (`calibrationMigrationRatio`)
  and squared-correlation portability `R_m`, the corpus ratio of
  `MigrationPortabilityFactor.splitPortabilityRatio_withSymmetricMigration`.
- `sqrt_portabilityDecay`, `calibrationMigrationRatio_zero`: without migration the calibration
  ratio is `e^{-(ρ̄/2) T}`, the square root of `e^{-ρ̄T}`.
- `hasDerivWithinAt_calibrationMigrationRatio`: on `m ≥ 0` the calibration ratio has one-sided
  derivative `φ₁(T) / (2 e^{-(ρ̄/2) T})` at `m = 0` (`calibrationMigrationFactor`), the derivative
  of the square root at the value without migration.
- `calibrationMigrationFactor_div_eq_half`: relative to its value, calibration moves at half the
  rate of the squared correlation, `(dκ/dm)/κ = (dR/dm)/R / 2` at `m = 0`.
  `calibrationMigrationFactor_eq_half_of_recombination_eq_zero`: without recombination the value
  is `1` and the calibration factor is exactly `φ₁/2`.
  `calibrationMigrationFactor_zeroRecombination`,
  `calibrationMigrationFactor_nonneg_zeroRecombination`: there it is
  `(cosh cT - 1)(π₀ - DD₀)(π₀ + Dz₀)/(c DD₀ π₀)`, nonnegative when `DD₀ ≤ π₀` and
  `π₀ + Dz₀ ≥ 0`.
- `abs_sqrt_sub_sub_le`: for `a > 0` and every real `x`,
  `|√x - √a - (x - a)/(2√a)| ≤ (x - a)²/(2 √a³)`.  `abs_sqrt_sub_sub_mul_le` composes it with a
  second-order bound on `x`.
- `abs_calibrationMigrationRatio_sub_le`: under the hypotheses of the corpus remainder bound,
  `|√R_m - e^{-(ρ̄/2) T} - m φ₁(T)/(2 e^{-(ρ̄/2) T})| ≤ C' m²` with the explicit
  `C' = calibrationRemainderConstant`.
- `exists_calibrationDecay_lt_calibrationMigrationRatio`,
  `exists_calibrationMigrationRatio_lt_calibrationDecay`: a positive first-order factor means a
  little migration raises calibration portability, and a negative one means it lowers it.

## Significance

Migration moves calibration the way it moves the squared correlation, in the same direction and
at half the relative rate.  Weak symmetric migration that raises the squared correlation by a
relative amount `ε` raises the calibration slope by about `ε/2`.

## Scope

The score model is that of `CalibrationPortabilityDecay`: standardized genotypes, linkage
equilibrium between pairs, a common retention for every pair, and no estimation error.  The
retention `√R_m` is an input read from the corpus ratio; no theorem here derives a per-pair
correlation under migration from the low-order moment system.  The identity
`squaredCorrelationPortability_migration` needs `R_m ≥ 0`, because the real square root is `0`
on negative numbers.  The derivative, the remainder bound and the sign theorems need no such
hypothesis.  Two demes, symmetric migration between them only, and no mutation, as in the corpus
migration modules.

## Empirical status

None.  The bodies are algebra and calculus on real square roots, and the corpus migration laws.
No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CalibrationPortabilityMigration

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay
  Descent.Portability.MigrationPortabilityFactor
  Descent.Portability.MigrationPortabilityFirstOrderFactor
  Descent.Portability.MigrationPortabilityRemainder
  Descent.Portability.CalibrationPortabilityDecay

noncomputable section

/-! ## A common retention -/

section Retention

variable {P : Type*} [Fintype P]

/-- **At a common retention calibration portability is the retention.**  If every pair keeps the
fraction `κ` of its source correlation, the target calibration slope is `κ`.

Assumes: nonzero score variance. -/
theorem calibrationPortability_commonRetention (effect sourceCorrelation : P → ℝ)
    (retention : ℝ) (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation
        (fun pair ↦ retention * sourceCorrelation pair)
      = retention := by
  rw [calibrationPortability_eq effect sourceCorrelation _ hvariance, calibrationSlope_retained,
    ← Finset.sum_mul, sum_trainedShare effect sourceCorrelation hvariance, one_mul]

/-- **At a common retention squared-correlation portability is the squared retention.**

Assumes: nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_commonRetention (effect sourceCorrelation : P → ℝ)
    (retention environment : ℝ) (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ retention * sourceCorrelation pair) environment
      = retention ^ 2 := by
  rw [squaredCorrelationPortability_eq_calibrationPortability_sq _ _ _ _ hvariance houtcome,
    calibrationPortability_commonRetention _ _ _ hvariance]

/-- **A nonnegative ratio is the squared-correlation portability of the score at its square
root.**  The calibration portability of that score is the square root.

Assumes: a nonnegative ratio, nonzero score variance and nonzero outcome variance. -/
theorem squaredCorrelationPortability_sqrtRetention (effect sourceCorrelation : P → ℝ)
    {ratio : ℝ} (hratio : 0 ≤ ratio) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ Real.sqrt ratio * sourceCorrelation pair) environment
      = ratio := by
  rw [squaredCorrelationPortability_commonRetention _ _ _ _ hvariance houtcome,
    Real.sq_sqrt hratio]

end Retention

/-! ## The square root of the decay -/

/-- **The square root of the decay is the decay at half the rate.** -/
theorem sqrt_portabilityDecay (rate duration : ℝ) :
    Real.sqrt (portabilityDecay rate duration) = portabilityDecay (rate / 2) duration := by
  have hsquare : portabilityDecay rate duration = portabilityDecay (rate / 2) duration ^ 2 := by
    rw [portabilityDecay_sq]
    congr 1
    ring
  have hnonneg : 0 ≤ portabilityDecay (rate / 2) duration := (Real.exp_pos _).le
  rw [hsquare, Real.sqrt_sq hnonneg]

/-- **Second-order Taylor bound for the square root.**  For `a > 0` and every real `x`,
`|√x - √a - (x - a)/(2√a)| ≤ (x - a)² / (2 √a³)`.

Assumes: `0 < a`. -/
theorem abs_sqrt_sub_sub_le {value : ℝ} (hvalue : 0 < value) (point : ℝ) :
    |Real.sqrt point - Real.sqrt value - (point - value) / (2 * Real.sqrt value)|
      ≤ (point - value) ^ 2 / (2 * Real.sqrt value ^ 3) := by
  obtain ⟨root, hroot, rfl⟩ : ∃ root, 0 < root ∧ value = root ^ 2 :=
    ⟨Real.sqrt value, Real.sqrt_pos.mpr hvalue, (Real.sq_sqrt hvalue.le).symm⟩
  have hne : root ≠ 0 := hroot.ne'
  rw [Real.sqrt_sq hroot.le]
  rcases le_or_lt 0 point with hpoint | hpoint
  · obtain ⟨other, hother, rfl⟩ : ∃ other, 0 ≤ other ∧ point = other ^ 2 :=
      ⟨Real.sqrt point, Real.sqrt_nonneg point, (Real.sq_sqrt hpoint).symm⟩
    rw [Real.sqrt_sq hother]
    have hequal : other - root - (other ^ 2 - root ^ 2) / (2 * root)
        = -((other - root) ^ 2 / (2 * root)) := by
      field_simp <;> ring
    rw [hequal, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (other - root) ^ 2 / (2 * root)),
      div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * root)
        (by positivity : (0 : ℝ) < 2 * root ^ 3)]
    have hwide : root ^ 2 ≤ (other + root) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hwide (sq_nonneg (other - root)), hroot]
  · rw [Real.sqrt_eq_zero'.mpr hpoint.le]
    have hequal : 0 - root - (point - root ^ 2) / (2 * root)
        = -(root ^ 2 + point) / (2 * root) := by
      field_simp <;> ring
    rw [hequal, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * root),
      div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * root)
        (by positivity : (0 : ℝ) < 2 * root ^ 3)]
    have hgap : 0 ≤ root ^ 2 - point := by nlinarith [sq_nonneg root]
    have habs : |-(root ^ 2 + point)| ≤ root ^ 2 - point := by
      rw [abs_neg]
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg root], by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_right habs (by positivity : (0 : ℝ) ≤ 2 * root ^ 3),
      mul_nonneg (mul_nonneg hroot.le hgap) (neg_nonneg.mpr hpoint.le)]

/-- **A second-order bound carries to the square root.**  If
`|x - a - m φ| ≤ C m²` for `0 ≤ m ≤ m₀`, then
`|√x - √a - m φ/(2√a)| ≤ ((|φ| + C m₀)²/(2 √a³) + C/(2√a)) m²`.

Assumes: `0 < a`, `0 ≤ m ≤ m₀`, `0 ≤ C`, and the second-order bound on `x`. -/
theorem abs_sqrt_sub_sub_mul_le {ratio decay factor constant migration bound : ℝ}
    (hdecay : 0 < decay) (hmigration : 0 ≤ migration) (hbound : migration ≤ bound)
    (hconstant : 0 ≤ constant)
    (hremainder : |ratio - decay - migration * factor| ≤ constant * migration ^ 2) :
    |Real.sqrt ratio - Real.sqrt decay - migration * (factor / (2 * Real.sqrt decay))|
      ≤ ((|factor| + constant * bound) ^ 2 / (2 * Real.sqrt decay ^ 3)
        + constant / (2 * Real.sqrt decay)) * migration ^ 2 := by
  have hroot : 0 < Real.sqrt decay := Real.sqrt_pos.mpr hdecay
  have htaylor := abs_sqrt_sub_sub_le hdecay ratio
  have htriangle : |ratio - decay|
      ≤ |ratio - decay - migration * factor| + |migration * factor| := by
    calc |ratio - decay| = |(ratio - decay - migration * factor) + migration * factor| := by
          congr 1
          ring
      _ ≤ |ratio - decay - migration * factor| + |migration * factor| := abs_add_le _ _
  rw [abs_mul, abs_of_nonneg hmigration] at htriangle
  have hquadratic : constant * migration ^ 2 ≤ migration * (constant * bound) := by
    nlinarith [mul_le_mul_of_nonneg_left hbound (mul_nonneg hconstant hmigration)]
  have hlinear : |ratio - decay| ≤ migration * (|factor| + constant * bound) := by
    linarith
  have hsquare : (ratio - decay) ^ 2 ≤ migration ^ 2 * (|factor| + constant * bound) ^ 2 := by
    have habs : (ratio - decay) ^ 2 = |ratio - decay| ^ 2 := (sq_abs _).symm
    rw [habs]
    nlinarith [abs_nonneg (ratio - decay)]
  have hsplit : Real.sqrt ratio - Real.sqrt decay - migration * (factor / (2 * Real.sqrt decay))
      = (Real.sqrt ratio - Real.sqrt decay - (ratio - decay) / (2 * Real.sqrt decay))
        + (ratio - decay - migration * factor) / (2 * Real.sqrt decay) := by
    ring
  rw [hsplit]
  calc |(Real.sqrt ratio - Real.sqrt decay - (ratio - decay) / (2 * Real.sqrt decay))
          + (ratio - decay - migration * factor) / (2 * Real.sqrt decay)|
        ≤ |Real.sqrt ratio - Real.sqrt decay - (ratio - decay) / (2 * Real.sqrt decay)|
          + |(ratio - decay - migration * factor) / (2 * Real.sqrt decay)| := abs_add_le _ _
    _ = |Real.sqrt ratio - Real.sqrt decay - (ratio - decay) / (2 * Real.sqrt decay)|
          + |ratio - decay - migration * factor| / (2 * Real.sqrt decay) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt decay)]
    _ ≤ migration ^ 2 * (|factor| + constant * bound) ^ 2 / (2 * Real.sqrt decay ^ 3)
          + constant * migration ^ 2 / (2 * Real.sqrt decay) := by
        refine add_le_add (htaylor.trans ?_) ?_
        · gcongr
        · gcongr
    _ = ((|factor| + constant * bound) ^ 2 / (2 * Real.sqrt decay ^ 3)
          + constant / (2 * Real.sqrt decay)) * migration ^ 2 := by
        ring

/-! ## The calibration ratio with migration -/

variable {D : ℕ}

/-- **The calibration ratio with symmetric migration** `√R_m`: the calibration portability of a
trained score whose pairs keep `√R_m` of their source correlation, with `R_m` the two-locus ratio
with migration `m`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A square root of a ratio of moment coordinates. -/
def calibrationMigrationRatio (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (migration : ℝ) (hmigration : 0 ≤ migration) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  Real.sqrt (splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration) parent
    child hduration ancestral)

/-- **The score at retention `√R_m` has calibration portability `√R_m`.**

Assumes: nonzero score variance. -/
theorem calibrationPortability_migration (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    {P : Type*} [Fintype P] (effect sourceCorrelation : P → ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0) :
    calibrationPortability effect sourceCorrelation
        (fun pair ↦ calibrationMigrationRatio rates hne migration hmigration hduration ancestral
          * sourceCorrelation pair)
      = calibrationMigrationRatio rates hne migration hmigration hduration ancestral :=
  calibrationPortability_commonRetention effect sourceCorrelation _ hvariance

/-- **The score at retention `√R_m` has squared-correlation portability `R_m`**, the corpus
two-locus ratio with migration.

Assumes: a nonnegative ratio with migration, nonzero score variance and nonzero outcome
variance. -/
theorem squaredCorrelationPortability_migration (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) {migration : ℝ} (hmigration : 0 ≤ migration)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hnonneg : 0 ≤ splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration)
      parent child hduration ancestral)
    {P : Type*} [Fintype P] (effect sourceCorrelation : P → ℝ) (environment : ℝ)
    (hvariance : trainedScoreVariance effect sourceCorrelation ≠ 0)
    (houtcome : outcomeVariance effect environment ≠ 0) :
    squaredCorrelationPortability effect sourceCorrelation
        (fun pair ↦ calibrationMigrationRatio rates hne migration hmigration hduration ancestral
          * sourceCorrelation pair) environment
      = splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration) parent child
          hduration ancestral :=
  squaredCorrelationPortability_sqrtRetention effect sourceCorrelation hnonneg environment
    hvariance houtcome

/-- **Without migration the calibration ratio is `e^{-(ρ̄/2) T}`**, the square root of the corpus
ratio `e^{-ρ̄T}`.

Assumes: no mutation, `parent ≠ child`, and a nonzero ancestral correlation. -/
theorem calibrationMigrationRatio_zero (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) :
    calibrationMigrationRatio rates hne 0 le_rfl hduration ancestral
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
          duration := by
  rw [calibrationMigrationRatio,
    splitPortabilityRatio_withSymmetricMigration_zero rates hmutation hne hduration ancestral
      hsource, sqrt_portabilityDecay]

/-! ## First order in the migration rate -/

/-- **The first-order migration factor of calibration** `φ₁(T) / (2 e^{-(ρ̄/2) T})`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The corpus factor over twice a real exponential. -/
def calibrationMigrationFactor (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  firstOrderMigrationFactor rates hne ancestral duration
    / (2 * portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
      duration)

/-- **The calibration ratio has derivative `φ₁(T) / (2 e^{-(ρ̄/2) T})` at `m = 0`**, one-sided on
`m ≥ 0`: the derivative of the square root at the value without migration, applied to the corpus
factor.  The rate enters as `max m 0`, as in the corpus.

Assumes: no mutation, `parent ≠ child`, a nonzero ancestral `E[D²]` and a nonzero ancestral
heterozygosity product. -/
theorem hasDerivWithinAt_calibrationMigrationRatio (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) :
    HasDerivWithinAt
      (fun migration ↦ calibrationMigrationRatio rates hne (max migration 0)
        (le_max_right migration 0) hduration ancestral)
      (calibrationMigrationFactor rates hne ancestral duration) (Set.Ici 0) 0 := by
  have hsource : ancestralSquaredCorrelation ancestral parent ≠ 0 :=
    div_ne_zero hlinkage hheterozygosity
  have hvalue : splitPortabilityRatio
        (withSymmetricMigration rates hne (max 0 0) (le_max_right 0 0)) parent child hduration
        ancestral
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
        duration := by
    rw [splitPortabilityRatio_withSymmetricMigration_eq_affine, max_self,
      ← splitPortabilityRatio_withSymmetricMigration_eq_affine rates hne le_rfl hduration
        ancestral,
      splitPortabilityRatio_withSymmetricMigration_zero rates hmutation hne hduration ancestral
        hsource]
  have hderivative := (hasDerivWithinAt_splitPortabilityRatio_withSymmetricMigration rates
    hmutation hne hduration ancestral hlinkage hheterozygosity).sqrt
    (hvalue.trans_ne (Real.exp_pos _).ne')
  refine hderivative.congr_deriv ?_
  show firstOrderMigrationFactor rates hne ancestral duration
      / (2 * Real.sqrt (splitPortabilityRatio
        (withSymmetricMigration rates hne (max 0 0) (le_max_right 0 0)) parent child hduration
        ancestral))
    = calibrationMigrationFactor rates hne ancestral duration
  rw [calibrationMigrationFactor, hvalue, sqrt_portabilityDecay]

/-- **Relative to its value, calibration moves at half the rate of the squared correlation.**
`(φ₁ / (2 e^{-(ρ̄/2) T})) / e^{-(ρ̄/2) T} = (φ₁ / e^{-ρ̄T}) / 2`. -/
theorem calibrationMigrationFactor_div_eq_half (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration : ℝ) :
    calibrationMigrationFactor rates hne ancestral duration
        / portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
          duration
      = firstOrderMigrationFactor rates hne ancestral duration
        / portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration / 2 := by
  have hsquare : portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
        duration
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
        duration ^ 2 := by
    rw [portabilityDecay_sq]
    congr 1
    ring
  have hroot : portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
      duration ≠ 0 := (Real.exp_pos _).ne'
  rw [calibrationMigrationFactor, hsquare]
  field_simp <;> ring

/-- **Without recombination the calibration factor is half the corpus factor.**  The value
without migration is then `1`, and the square root has derivative `1/2` there.

Assumes: `ρ_S + ρ_T = 0`. -/
theorem calibrationMigrationFactor_eq_half_of_recombination_eq_zero (rates : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hrecombination : rates.recombination parent + rates.recombination child = 0)
    (duration : ℝ) :
    calibrationMigrationFactor rates hne ancestral duration
      = firstOrderMigrationFactor rates hne ancestral duration / 2 := by
  rw [calibrationMigrationFactor, hrecombination, zero_div, zero_div, portabilityDecay_zero_rate,
    mul_one]

/-- **The calibration factor without recombination in closed form**,
`(cosh cT - 1)(π₀ - DD₀)(π₀ + Dz₀)/(c DD₀ π₀)`.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, `ρ = 0`, and nonzero
ancestral `DD` and `pi2`. -/
theorem calibrationMigrationFactor_zeroRecombination (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0)
    (duration : ℝ) :
    calibrationMigrationFactor rates hne ancestral duration
      = (Real.cosh (rates.coalescence parent * duration) - 1)
          * (ancestral (some (.pi2 parent parent parent parent))
            - ancestral (some (.DD parent parent)))
          * (ancestral (some (.pi2 parent parent parent parent))
            + ancestral (some (.Dz parent parent parent)))
        / (rates.coalescence parent * ancestral (some (.DD parent parent))
          * ancestral (some (.pi2 parent parent parent parent))) := by
  have hsum : rates.recombination parent + rates.recombination child = 0 := by
    rw [hrec, hρ, add_zero]
  rw [calibrationMigrationFactor_eq_half_of_recombination_eq_zero rates hne ancestral hsum,
    firstOrderMigrationFactor_zeroRecombination rates hmutation hne hcoal hrec hρ ancestral
      hlinkage hheterozygosity]
  ring

/-- **To first order, migration raises calibration without recombination** when `DD₀ ≤ π₀` and
`π₀ + Dz₀ ≥ 0`.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, `ρ = 0`, positive
ancestral `DD` and `pi2`, `DD₀ ≤ π₀`, and `0 ≤ π₀ + Dz₀`. -/
theorem calibrationMigrationFactor_nonneg_zeroRecombination (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (horder : ancestral (some (.DD parent parent))
      ≤ ancestral (some (.pi2 parent parent parent parent)))
    (hcontrast : 0 ≤ ancestral (some (.pi2 parent parent parent parent))
      + ancestral (some (.Dz parent parent parent))) (duration : ℝ) :
    0 ≤ calibrationMigrationFactor rates hne ancestral duration :=
  div_nonneg (firstOrderMigrationFactor_nonneg_zeroRecombination rates hmutation hne hcoal hrec hρ
      ancestral hlinkage hheterozygosity horder hcontrast duration)
    (mul_pos two_pos (Real.exp_pos _)).le

/-! ## Second order in the migration rate -/

/-- **The second-order constant of the calibration ratio**
`C' = (|φ₁| + C m₀)² / (2 κ₀³) + C / (2 κ₀)`, with `κ₀ = e^{-(ρ̄/2) T}` and
`C = migrationRatioRemainderConstant`.

Empirical status: NOT AN EMPIRICAL CLAIM.  An algebraic combination of corpus constants. -/
def calibrationRemainderConstant (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration bound : ℝ) : ℝ :=
  (|firstOrderMigrationFactor rates hne ancestral duration|
        + migrationRatioRemainderConstant rates hne ancestral duration bound * bound) ^ 2
      / (2 * portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
        duration ^ 3)
    + migrationRatioRemainderConstant rates hne ancestral duration bound
      / (2 * portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
        duration)

/-- **The calibration ratio to second order in the migration rate.**  For `0 ≤ m ≤ m₀`,
`|√R_m - e^{-(ρ̄/2) T} - m φ₁(T)/(2 e^{-(ρ̄/2) T})| ≤ C' m²` with
`C' = calibrationRemainderConstant`, under the smallness condition of the corpus bound.

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`,
`0 ≤ m ≤ m₀`, and `m |Dn₁| + K m² ≤ Dn₀/2`. -/
theorem abs_calibrationMigrationRatio_sub_le (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    {migration bound : ℝ} (hmigration : 0 ≤ migration) (hbound : migration ≤ bound)
    (hsmall : migration * |heterozygositySlope rates hne ancestral duration|
        + migrationRemainderConstant rates hne ancestral duration bound * migration ^ 2
      ≤ heterozygosityValue rates parent child ancestral duration / 2) :
    |calibrationMigrationRatio rates hne migration hmigration hduration ancestral
        - portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
          duration
        - migration * calibrationMigrationFactor rates hne ancestral duration|
      ≤ calibrationRemainderConstant rates hne ancestral duration bound * migration ^ 2 := by
  have hK := migrationRemainderConstant_nonneg rates hne ancestral duration bound
  have hvalue : 0 < heterozygosityValue rates parent child ancestral duration :=
    mul_pos (Real.exp_pos _) hheterozygosity
  have hσ : 0 < ancestralSquaredCorrelation ancestral parent := div_pos hlinkage hheterozygosity
  have hbound0 : 0 ≤ bound := hmigration.trans hbound
  have hconstant : 0 ≤ migrationRatioRemainderConstant rates hne ancestral duration bound := by
    unfold migrationRatioRemainderConstant
    positivity
  have hdecay : 0 < portabilityDecay
      ((rates.recombination parent + rates.recombination child) / 2) duration :=
    Real.exp_pos _
  have h := abs_sqrt_sub_sub_mul_le hdecay hmigration hbound hconstant
    (abs_splitPortabilityRatio_withSymmetricMigration_sub_le rates hmutation hne hduration
      ancestral hlinkage hheterozygosity hmigration hbound hsmall)
  rw [sqrt_portabilityDecay] at h
  exact h

/-! ## The sign of the first-order factor decides the direction -/

/-- **A positive first-order factor means a little migration raises calibration portability.**

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`, and
`0 < φ₁(T)`. -/
theorem exists_calibrationDecay_lt_calibrationMigrationRatio (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hfactor : 0 < firstOrderMigrationFactor rates hne ancestral duration) :
    ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
            duration
          < calibrationMigrationRatio rates hne migration hmigration.le hduration ancestral := by
  obtain ⟨threshold, hpositive, hraise⟩ := exists_portabilityDecay_lt_splitPortabilityRatio rates
    hmutation hne hduration ancestral hlinkage hheterozygosity hfactor
  refine ⟨threshold, hpositive, fun migration hmigration hthreshold ↦ ?_⟩
  have hnonneg : 0 ≤ portabilityDecay
      ((rates.recombination parent + rates.recombination child) / 2) duration :=
    (Real.exp_pos _).le
  rw [calibrationMigrationRatio, ← sqrt_portabilityDecay]
  exact Real.sqrt_lt_sqrt hnonneg (hraise migration hmigration hthreshold)

/-- **A negative first-order factor means a little migration lowers calibration portability.**

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`, and
`φ₁(T) < 0`. -/
theorem exists_calibrationMigrationRatio_lt_calibrationDecay (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hfactor : firstOrderMigrationFactor rates hne ancestral duration < 0) :
    ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        calibrationMigrationRatio rates hne migration hmigration.le hduration ancestral
          < portabilityDecay ((rates.recombination parent + rates.recombination child) / 2 / 2)
            duration := by
  obtain ⟨threshold, hpositive, hlower⟩ := exists_splitPortabilityRatio_lt_portabilityDecay rates
    hmutation hne hduration ancestral hlinkage hheterozygosity hfactor
  refine ⟨threshold, hpositive, fun migration hmigration hthreshold ↦ ?_⟩
  have h := hlower migration hmigration hthreshold
  rw [calibrationMigrationRatio, ← sqrt_portabilityDecay]
  rcases le_or_lt 0 (splitPortabilityRatio
      (withSymmetricMigration rates hne migration hmigration.le) parent child hduration
      ancestral) with hnonneg | hnegative
  · exact Real.sqrt_lt_sqrt hnonneg h
  · rw [Real.sqrt_eq_zero'.mpr hnegative.le]
    exact Real.sqrt_pos.mpr (Real.exp_pos _)

end

end Descent.Portability.CalibrationPortabilityMigration
