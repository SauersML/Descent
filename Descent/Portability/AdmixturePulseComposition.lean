/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdmixturePortabilityDecay
import Descent.Portability.TwoLocusMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# Portability along a split, an epoch, an admixture pulse and a second epoch

A source and a target population split from one ancestor.  A time `T₁` later the target
receives a fraction `α` of its haplotypes from the source in one pulse, and a time `T₂` then
passes.  This module gives the cross-population squared correlation of a tag-locus score over
the whole chronology in closed form, `E[D_S D_T] / E[π^A_S π^B_T]` as a ratio of expectations.
Here `S` is the parent deme and `T` the child deme.

The chronology is composed from finished corpus pieces.  The split and the first epoch are
`TwoLocusPortabilityDecay.splitHistoryState`.  A locus-exchangeable haplotype realization of the
ancestral state survives the split (`TwoLocusRealizabilityPreservation.locusExchangeableSplit`)
and the epoch, with nothing assumed
(`TwoLocusMicroscopicApproximation.rateEpoch_preserves_locusExchangeable_realization`).  So the
pre-pulse state carries a haplotype law (`nonempty_splitHistoryState_realization`), and the
corpus pulse acts on it.  The pulse and the second epoch are
`AdmixturePortabilityDecay.pulseHistoryState`, evaluated at a realization chosen from that
existence statement (`prePulseRealization`, `chronologySquaredCorrelation`).  The two readouts
after the pulse are fixed combinations of pre-pulse coordinates, so the choice enters no closed
form below.

## Main results

- `nonempty_splitHistoryState_realization`: the state after a split and an epoch is
  locus-exchangeably realizable whenever the ancestral state is.
- `chronologySquaredCorrelation_eq`: the squared correlation of the chronology is
  `e^{-r₂ T₂} N / M`, with `r_k = (ρ_S + ρ_T)/2` in epoch `k`, the drift factor
  `E₁ = e^{-(c_S + c_T) T₁}` of the first epoch, and
  `N = α E[D_S²](T₁) + (1 − α) E₁ e^{-r₁ T₁} E[D²](0) + α (1 − α) Λ(T₁)`,
  `M = α² pi2(S, S, S, S)(T₁) + α (1 − α) (pi2(S, S, S, T) + pi2(S, S, T, S))(T₁)
  + (1 − α)² E₁ E[π^A π^B](0)`.
  The pre-pulse cross terms are the ancestral moments times the split decay `e^{-r₁ T₁}` and the
  drift factor, and `Λ` is `AdmixturePortabilityDecay.admixtureChannel`.
- `chronologySquaredCorrelation_zero`, `chronologyPortabilityRatio_zero`: at `α = 0` the
  chronology is `e^{-r₂ T₂} e^{-r₁ T₁} σ²_D(0)`.  Relative to the ancestral value the two epochs
  compose as the product of their decay factors, and drift cancels.
- `chronologySquaredCorrelation_one`: at `α = 1` the chronology is `e^{-r₂ T₂}` times the
  source's own `σ²_D` at the pulse.

## The mechanism

Without migration or mutation the cross moments `DD(S, T)` and `pi2(S, S, T, T)` have diagonal
generator rows in both epochs.  Across the first epoch they are the ancestral moments times
`E₁ e^{-r₁ T₁}` and `E₁` (`TwoLocusPortabilityDecay.splitHistoryState_DD`,
`TwoLocusPortabilityDecay.splitHistoryState_pi2`).  The pulse mixes them with the source's own
moments at `T₁` (`AdmixturePortabilityDecay.pulseState_DD_cross`,
`AdmixturePortabilityDecay.pulseState_pi2_cross`).  The second epoch multiplies the post-pulse
ratio by `e^{-r₂ T₂}` (`AdmixturePortabilityDecay.pulseHistorySquaredCorrelation_eq`).  The drift
factor `E₁` multiplies only the pre-pulse cross terms, not the source's own moments at the pulse.

## Scope

The within-source coordinates at the pulse, `E[D_S²](T₁)`, the stencil `Λ(T₁)` and the products
`pi2(S, S, S, ·)(T₁)`, stay coordinates of the split history.  They follow the Ohta–Kimura
system, whose rates are the roots of a cubic, and have no closed form in `e^{-cT}` and
`e^{-(c + r)T}`.  Migration and mutation are zero in both epochs.  The pulse goes from the
parent deme into the child deme, and repeated pulses are not treated.

## Empirical status

None.  The bodies here compose corpus theorems by rewriting and real algebra.  No measurement
can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AdmixturePulseComposition

open Descent.Coalescent

noncomputable section

variable {D : ℕ}

/-! ## The pre-pulse state is realizable -/

/-- **A split and an epoch preserve locus-exchangeable realizability.**  The split relabels the
ancestral haplotype law, and the epoch is NOTE1 Theorem 2 with nothing assumed. -/
theorem nonempty_splitHistoryState_realization (rates : ManyDemeLDRates D) (parent child : Fin D)
    {duration : ℝ} (hduration : 0 ≤ duration) {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (TwoLocusPortabilityDecay.splitHistoryState rates parent child hduration ancestral)) :=
  TwoLocusMicroscopicApproximation.rateEpoch_preserves_locusExchangeable_realization rates
    duration hduration
    (TwoLocusRealizabilityPreservation.locusExchangeableSplit realization parent child)

/-- **A haplotype realization of the pre-pulse state**, chosen from
`nonempty_splitHistoryState_realization`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A choice from a proved existence statement. -/
def prePulseRealization (rates : ManyDemeLDRates D) (parent child : Fin D) {duration : ℝ}
    (hduration : 0 ≤ duration) {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral) :
    LowOrderLDHaplotypeRealization
      (TwoLocusPortabilityDecay.splitHistoryState rates parent child hduration ancestral) :=
  (Classical.choice (nonempty_splitHistoryState_realization rates parent child hduration
    realization)).toLowOrderLDHaplotypeRealization

/-! ## The chronology -/

/-- **The cross-population expected squared correlation of the chronology**: a split, an epoch
under `splitRates`, a pulse of fraction `α` from `parent` into `child`, and an epoch under
`pulseRates`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two moment coordinates of a composed
history. -/
def chronologySquaredCorrelation (splitRates pulseRates : ManyDemeLDRates D)
    {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral)
    (parent child : Fin D) {splitDuration : ℝ} (hsplitDuration : 0 ≤ splitDuration) (alpha : ℝ)
    (hnonneg : 0 ≤ alpha) (hle : alpha ≤ 1) {pulseDuration : ℝ}
    (hpulseDuration : 0 ≤ pulseDuration) : ℝ :=
  AdmixturePortabilityDecay.pulseHistorySquaredCorrelation pulseRates
    (prePulseRealization splitRates parent child hsplitDuration realization) alpha hnonneg hle
    parent child hpulseDuration

/-- **The portability ratio of the chronology**: its squared correlation over the ancestral
`σ²_D(0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of moment coordinates. -/
def chronologyPortabilityRatio (splitRates pulseRates : ManyDemeLDRates D)
    {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral)
    (parent child : Fin D) {splitDuration : ℝ} (hsplitDuration : 0 ≤ splitDuration) (alpha : ℝ)
    (hnonneg : 0 ≤ alpha) (hle : alpha ≤ 1) {pulseDuration : ℝ}
    (hpulseDuration : 0 ≤ pulseDuration) : ℝ :=
  chronologySquaredCorrelation splitRates pulseRates realization parent child hsplitDuration
      alpha hnonneg hle hpulseDuration
    / TwoLocusPortabilityDecay.ancestralSquaredCorrelation ancestral parent

/-- **The chronology in closed form.**  A time `T₂` after the pulse the squared correlation is
`e^{-r₂ T₂} N / M`.  The numerator is the admixed covariance of the source's own `E[D_S²](T₁)`,
the pre-pulse cross covariance `E₁ e^{-r₁ T₁} E[D²](0)` and the channel `Λ(T₁)`.  The denominator
is the admixed heterozygosity product of the source's own products at `T₁` and the pre-pulse
cross product `E₁ E[π^A π^B](0)`.  Here `E₁ = e^{-(c_S + c_T) T₁}` and `r_k = (ρ_S + ρ_T)/2`.

Assumes: no migration and no mutation in either epoch, and `parent ≠ child`. -/
theorem chronologySquaredCorrelation_eq (splitRates pulseRates : ManyDemeLDRates D)
    (hsplitMigration : ∀ source target, splitRates.migration source target = 0)
    (hsplitMutation : ∀ deme, splitRates.mutation deme = 0)
    (hpulseMigration : ∀ source target, pulseRates.migration source target = 0)
    (hpulseMutation : ∀ deme, pulseRates.mutation deme = 0)
    {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral)
    {parent child : Fin D} (hne : parent ≠ child) {splitDuration : ℝ}
    (hsplitDuration : 0 ≤ splitDuration) {alpha : ℝ} (hnonneg : 0 ≤ alpha) (hle : alpha ≤ 1)
    {pulseDuration : ℝ} (hpulseDuration : 0 ≤ pulseDuration) :
    chronologySquaredCorrelation splitRates pulseRates realization parent child hsplitDuration
        alpha hnonneg hle hpulseDuration
      = TwoLocusPortabilityDecay.portabilityDecay
          ((pulseRates.recombination parent + pulseRates.recombination child) / 2) pulseDuration
        * (AdmixturePortabilityDecay.admixedCovariance alpha
            (TwoLocusPortabilityDecay.splitHistoryState splitRates parent child hsplitDuration
              ancestral (some (.DD parent parent)))
            (Real.exp (-(splitRates.coalescence parent + splitRates.coalescence child)
                * splitDuration)
              * (TwoLocusPortabilityDecay.portabilityDecay
                  ((splitRates.recombination parent + splitRates.recombination child) / 2)
                  splitDuration
                * ancestral (some (.DD parent parent))))
            (AdmixturePortabilityDecay.admixtureChannel
              (TwoLocusPortabilityDecay.splitHistoryState splitRates parent child hsplitDuration
                ancestral) parent child)
          / AdmixturePortabilityDecay.admixedHeterozygosity alpha
            (TwoLocusPortabilityDecay.splitHistoryState splitRates parent child hsplitDuration
              ancestral (some (.pi2 parent parent parent parent)))
            (TwoLocusPortabilityDecay.splitHistoryState splitRates parent child hsplitDuration
                ancestral (some (.pi2 parent parent parent child))
              + TwoLocusPortabilityDecay.splitHistoryState splitRates parent child hsplitDuration
                ancestral (some (.pi2 parent parent child parent)))
            (Real.exp (-(splitRates.coalescence parent + splitRates.coalescence child)
                * splitDuration)
              * ancestral (some (.pi2 parent parent parent parent)))) := by
  have hfactor : Real.exp (-(splitRates.coalescence parent + splitRates.coalescence child
          + (splitRates.recombination parent + splitRates.recombination child) / 2)
          * splitDuration)
        * ancestral (some (.DD parent parent))
      = Real.exp (-(splitRates.coalescence parent + splitRates.coalescence child)
          * splitDuration)
        * (TwoLocusPortabilityDecay.portabilityDecay
            ((splitRates.recombination parent + splitRates.recombination child) / 2)
            splitDuration
          * ancestral (some (.DD parent parent))) := by
    rw [TwoLocusPortabilityDecay.portabilityDecay, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [chronologySquaredCorrelation,
    AdmixturePortabilityDecay.pulseHistorySquaredCorrelation_eq_closedForm pulseRates
      hpulseMigration hpulseMutation
      (prePulseRealization splitRates parent child hsplitDuration realization) hnonneg hle hne
      hpulseDuration,
    TwoLocusPortabilityDecay.splitHistoryState_DD splitRates hsplitMigration hsplitMutation hne
      hsplitDuration ancestral,
    TwoLocusPortabilityDecay.splitHistoryState_pi2 splitRates hsplitMigration hsplitMutation hne
      hsplitDuration ancestral, hfactor]

/-- **Without a pulse the two epochs compose.**  At `α = 0` the squared correlation of the
chronology is `e^{-r₂ T₂} e^{-r₁ T₁} σ²_D(0)`.

Assumes: no migration and no mutation in either epoch, and `parent ≠ child`. -/
theorem chronologySquaredCorrelation_zero (splitRates pulseRates : ManyDemeLDRates D)
    (hsplitMigration : ∀ source target, splitRates.migration source target = 0)
    (hsplitMutation : ∀ deme, splitRates.mutation deme = 0)
    (hpulseMigration : ∀ source target, pulseRates.migration source target = 0)
    (hpulseMutation : ∀ deme, pulseRates.mutation deme = 0)
    {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral)
    {parent child : Fin D} (hne : parent ≠ child) {splitDuration : ℝ}
    (hsplitDuration : 0 ≤ splitDuration) {pulseDuration : ℝ}
    (hpulseDuration : 0 ≤ pulseDuration) :
    chronologySquaredCorrelation splitRates pulseRates realization parent child hsplitDuration 0
        le_rfl zero_le_one hpulseDuration
      = TwoLocusPortabilityDecay.portabilityDecay
          ((pulseRates.recombination parent + pulseRates.recombination child) / 2) pulseDuration
        * (TwoLocusPortabilityDecay.portabilityDecay
            ((splitRates.recombination parent + splitRates.recombination child) / 2)
            splitDuration
          * TwoLocusPortabilityDecay.ancestralSquaredCorrelation ancestral parent) := by
  rw [chronologySquaredCorrelation,
    AdmixturePortabilityDecay.pulseHistorySquaredCorrelation_eq pulseRates hpulseMigration
      hpulseMutation (prePulseRealization splitRates parent child hsplitDuration realization)
      le_rfl zero_le_one hne hpulseDuration,
    AdmixturePortabilityDecay.pulseSquaredCorrelation_zero
      (prePulseRealization splitRates parent child hsplitDuration realization) hne,
    ← TwoLocusPortabilityDecay.crossSquaredCorrelation_eq splitRates hsplitMigration
      hsplitMutation hne hsplitDuration ancestral]
  rfl

/-- **A complete pulse restarts from the source.**  At `α = 1` the squared correlation of the
chronology is `e^{-r₂ T₂}` times the source's own `σ²_D` at the pulse.

Assumes: no migration and no mutation after the pulse, and `parent ≠ child`. -/
theorem chronologySquaredCorrelation_one (splitRates pulseRates : ManyDemeLDRates D)
    (hpulseMigration : ∀ source target, pulseRates.migration source target = 0)
    (hpulseMutation : ∀ deme, pulseRates.mutation deme = 0)
    {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral)
    {parent child : Fin D} (hne : parent ≠ child) {splitDuration : ℝ}
    (hsplitDuration : 0 ≤ splitDuration) {pulseDuration : ℝ}
    (hpulseDuration : 0 ≤ pulseDuration) :
    chronologySquaredCorrelation splitRates pulseRates realization parent child hsplitDuration 1
        zero_le_one le_rfl hpulseDuration
      = TwoLocusPortabilityDecay.portabilityDecay
          ((pulseRates.recombination parent + pulseRates.recombination child) / 2) pulseDuration
        * TwoLocusPortabilityDecay.ancestralSquaredCorrelation
          (TwoLocusPortabilityDecay.splitHistoryState splitRates parent child hsplitDuration
            ancestral) parent := by
  rw [chronologySquaredCorrelation,
    AdmixturePortabilityDecay.pulseHistorySquaredCorrelation_eq pulseRates hpulseMigration
      hpulseMutation (prePulseRealization splitRates parent child hsplitDuration realization)
      zero_le_one le_rfl hne hpulseDuration,
    AdmixturePortabilityDecay.pulseSquaredCorrelation_one
      (prePulseRealization splitRates parent child hsplitDuration realization) hne]

/-- **Without a pulse the portability ratio is the product of the two decay factors**,
`e^{-r₂ T₂} e^{-r₁ T₁}`.

Assumes: no migration and no mutation in either epoch, `parent ≠ child`, and a nonzero ancestral
correlation. -/
theorem chronologyPortabilityRatio_zero (splitRates pulseRates : ManyDemeLDRates D)
    (hsplitMigration : ∀ source target, splitRates.migration source target = 0)
    (hsplitMutation : ∀ deme, splitRates.mutation deme = 0)
    (hpulseMigration : ∀ source target, pulseRates.migration source target = 0)
    (hpulseMutation : ∀ deme, pulseRates.mutation deme = 0)
    {ancestral : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization ancestral)
    {parent child : Fin D} (hne : parent ≠ child) {splitDuration : ℝ}
    (hsplitDuration : 0 ≤ splitDuration) {pulseDuration : ℝ}
    (hpulseDuration : 0 ≤ pulseDuration)
    (hsource : TwoLocusPortabilityDecay.ancestralSquaredCorrelation ancestral parent ≠ 0) :
    chronologyPortabilityRatio splitRates pulseRates realization parent child hsplitDuration 0
        le_rfl zero_le_one hpulseDuration
      = TwoLocusPortabilityDecay.portabilityDecay
          ((pulseRates.recombination parent + pulseRates.recombination child) / 2) pulseDuration
        * TwoLocusPortabilityDecay.portabilityDecay
          ((splitRates.recombination parent + splitRates.recombination child) / 2)
          splitDuration := by
  rw [chronologyPortabilityRatio,
    chronologySquaredCorrelation_zero splitRates pulseRates hsplitMigration hsplitMutation
      hpulseMigration hpulseMutation realization hne hsplitDuration hpulseDuration,
    mul_div_assoc, mul_div_assoc, div_self hsource, mul_one]

end

end Descent.Portability.AdmixturePulseComposition
