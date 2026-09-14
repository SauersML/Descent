/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusPortabilityDecay

assert_below Descent.Decision Descent.Program

/-!
# Closed-form portability after an admixture pulse

A target deme receives a fraction `α ∈ [0, 1]` of its haplotypes from a source deme in one
instantaneous pulse.  How does the cross-population squared correlation of a tag-locus score
move, and what becomes of it afterwards?

The pulse is the corpus one, `LowOrderLDHaplotypeRealization.pulseState`.  The pre-pulse moment
vector is carried by a haplotype realization, the recipient's four haplotype frequencies become
`α · source + (1 − α) · target`, and every coordinate after the pulse is read from the mixed
law.  The readout is the cross-population statistic of `TwoLocusPortabilityDecay`,
`E[D_S D_T] / E[π^A_S π^B_T]`, a ratio of expectations.  Here `S` is the source and `T` the
recipient.

## Main results

- `pulseState_DD_cross`: the cross-population linkage covariance after the pulse is
  `α E[D_S²] + (1 − α) E[D_S D_T] + α (1 − α) Λ` (`admixedCovariance`).  The channel
  `Λ = E[D_S (p_S − p_T)(q_S − q_T)]` is the four-`Dz` stencil `admixtureChannel`.  Mixing keeps
  the two parental linkage terms and adds the joint differentiation at the two loci.
- `pulseState_pi2_cross`: the cross heterozygosity product mixes bilinearly,
  `α² pi2(S, S, S, S) + α (1 − α) (pi2(S, S, S, T) + pi2(S, S, T, S)) + (1 − α)² pi2(S, S, T, T)`
  (`admixedHeterozygosity`).
- `pulseSquaredCorrelation_eq`: the cross-population squared correlation right after the pulse
  is the ratio of the two closed forms.
- `pulseSquaredCorrelation_zero`, `pulseSquaredCorrelation_one`: `α = 0` gives back the pre-pulse
  cross squared correlation, and `α = 1` gives the source's own `σ²_D`.  Relative to the source's
  own value the ratio is the pre-pulse ratio at `α = 0` and `1` at `α = 1`
  (`pulsePortabilityRatio_zero`, `pulsePortabilityRatio_one`).
- `pulseState_DD_cross_div`: relative to `E[D_S²]` the covariance ratio after the pulse is
  `α + (1 − α) R₀ + α (1 − α) κ`, with `R₀` the pre-pulse covariance ratio and `κ = Λ / E[D_S²]`.
- `admixedCovariance_monotoneOn`: when `|Λ| ≤ E[D_S²] − E[D_S D_T]`, the covariance after the
  pulse increases with `α` on `[0, 1]`.
- `pulseHistoryState_DD`, `pulseHistoryState_pi2`, `pulseHistorySquaredCorrelation_eq`,
  `pulseHistorySquaredCorrelation_eq_closedForm`: evolving for a time `T` after the pulse, with
  no migration or mutation, multiplies the post-pulse squared correlation by
  `portabilityDecay r T = e^{-r T}`, `r = (ρ_S + ρ_T)/2`.  Drift cancels, as after a split.

## The mechanism

At the recipient the mixed haplotype law has linkage
`α D_S + (1 − α) D_T + α (1 − α) (p_S − p_T)(q_S − q_T)`
(`TwoLocusHaplotypeFrequencies.mixture_linkage`), and its allele frequencies are the convex
combinations.  Multiplying by the source's linkage and writing `p = (1 − z)/2` turns the
differentiation term into four `Dz` observables.  The heterozygosity at the mixed frequency is a
quadratic form in the two parental frequencies.  Expectations are linear, so each coordinate
after the pulse is a fixed combination of pre-pulse coordinates.  After the pulse the generator
rows of `DD(S, T)` and `pi2(S, S, T, T)` are diagonal
(`TwoLocusPortabilityDecay.augmentedLowOrderLDGenerator_DD_row`,
`TwoLocusPortabilityDecay.augmentedLowOrderLDGenerator_pi2_row`), so the epoch only rescales the
two moments, and the common drift factor cancels from the ratio (`exp_mul_div_exp_mul`).

## Scope

The pre-pulse state is any haplotype-realizable moment vector.  A split followed by an epoch
supplies one, and the chronology split, epoch, pulse, epoch is composed in
`Descent.Portability.AdmixturePulseComposition`.  Monotonicity in `α` is proved for the
covariance, not for the squared-correlation ratio, whose heterozygosity denominator also moves
with `α`.
The mixed-heterozygosity readout `pi2(S, T, S, T)`, repeated pulses and continuous migration are
not treated here.

## Empirical status

None.  The bodies here are algebra on finite linear combinations of expectations and on real
exponentials.  No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AdmixturePortabilityDecay

open Descent.Coalescent

noncomputable section

variable {D : ℕ}

/-! ## The closed forms -/

/-- **The admixed linkage covariance** `α a + (1 − α) b + α (1 − α) Λ` at pulse fraction `α`,
source-own covariance `a`, pre-pulse cross covariance `b` and differentiation channel `Λ`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A quadratic polynomial in `α`. -/
def admixedCovariance (alpha sourceOwn cross channel : ℝ) : ℝ :=
  alpha * sourceOwn + (1 - alpha) * cross + alpha * (1 - alpha) * channel

/-- **The admixed heterozygosity product** `α² A + α (1 − α) M + (1 − α)² B` at pulse fraction
`α`, source-own product `A`, mixed products `M` and pre-pulse cross product `B`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A quadratic polynomial in `α`. -/
def admixedHeterozygosity (alpha sourceOwn mixed cross : ℝ) : ℝ :=
  alpha ^ 2 * sourceOwn + alpha * (1 - alpha) * mixed + (1 - alpha) ^ 2 * cross

/-- **The differentiation channel of a pulse**, `E[D_S (p_S − p_T)(q_S − q_T)]`, as the four-`Dz`
stencil `(Dz(S, T, T) − Dz(S, T, S) − Dz(S, S, T) + Dz(S, S, S)) / 4`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A signed sum of four moment coordinates. -/
def admixtureChannel (state : AffineLowOrderLDCoordinate D → ℝ) (source recipient : Fin D) : ℝ :=
  (state (some (.Dz source recipient recipient)) - state (some (.Dz source recipient source))
    - state (some (.Dz source source recipient)) + state (some (.Dz source source source))) / 4

/-! ## The moment vector right after the pulse -/

/-- At the recipient, the pulse witness holds the mixed haplotype law. -/
theorem pulseHaplotype_recipient {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) (source recipient : Fin D) (outcome : realization.sampleSpace) :
    realization.pulseHaplotype alpha hnonneg hle source recipient outcome recipient
      = TwoLocusHaplotypeFrequencies.mixture alpha hnonneg hle
          (realization.haplotype outcome source) (realization.haplotype outcome recipient) := by
  simp [LowOrderLDHaplotypeRealization.pulseHaplotype]

/-- **The cross-population linkage covariance right after the pulse.**  With `α` of the
recipient's haplotypes drawn from the source,
`E[D_S D_T]' = α E[D_S²] + (1 − α) E[D_S D_T] + α (1 − α) Λ`.

Assumes: `source ≠ recipient`. -/
theorem pulseState_DD_cross {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) :
    realization.pulseState alpha hnonneg hle source recipient (some (.DD source recipient))
      = admixedCovariance alpha (state (some (.DD source source)))
          (state (some (.DD source recipient))) (admixtureChannel state source recipient) := by
  have hpoint : (fun outcome ↦
      (realization.pulseHaplotype alpha hnonneg hle source recipient outcome source).linkage
        * (realization.pulseHaplotype alpha hnonneg hle source recipient outcome
          recipient).linkage)
      = alpha • (fun outcome ↦
          (realization.haplotype outcome source).linkage
            * (realization.haplotype outcome source).linkage)
        + (1 - alpha) • (fun outcome ↦
          (realization.haplotype outcome source).linkage
            * (realization.haplotype outcome recipient).linkage)
        + (alpha * (1 - alpha) / 4) • ((fun outcome ↦
            twoLocusDzObservable (realization.haplotype outcome source)
              (realization.haplotype outcome recipient) (realization.haplotype outcome recipient))
          - (fun outcome ↦
            twoLocusDzObservable (realization.haplotype outcome source)
              (realization.haplotype outcome recipient) (realization.haplotype outcome source))
          - (fun outcome ↦
            twoLocusDzObservable (realization.haplotype outcome source)
              (realization.haplotype outcome source) (realization.haplotype outcome recipient))
          + (fun outcome ↦
            twoLocusDzObservable (realization.haplotype outcome source)
              (realization.haplotype outcome source) (realization.haplotype outcome source))) := by
    funext outcome
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [realization.pulseHaplotype_of_ne alpha hnonneg hle source recipient source hne outcome,
      pulseHaplotype_recipient realization hnonneg hle source recipient outcome,
      TwoLocusHaplotypeFrequencies.mixture_linkage]
    simp only [twoLocusDzObservable, TwoLocusHaplotypeFrequencies.leftContrast,
      TwoLocusHaplotypeFrequencies.rightContrast]
    ring
  change realization.expectation (fun outcome ↦
      (realization.pulseHaplotype alpha hnonneg hle source recipient outcome source).linkage
        * (realization.pulseHaplotype alpha hnonneg hle source recipient outcome
          recipient).linkage) = _
  rw [hpoint, realization.expectation.add_eval, realization.expectation.add_eval,
    realization.expectation.smul_eval, realization.expectation.smul_eval,
    realization.expectation.smul_eval, realization.expectation.add_eval,
    realization.expectation.eval_sub, realization.expectation.eval_sub, admixedCovariance,
    admixtureChannel, realization.DD_eq source source, realization.DD_eq source recipient,
    realization.Dz_eq source recipient recipient, realization.Dz_eq source recipient source,
    realization.Dz_eq source source recipient, realization.Dz_eq source source source]
  ring

/-- **The cross heterozygosity product right after the pulse mixes bilinearly**:
`pi2(S, S, T, T)' = α² pi2(S, S, S, S) + α (1 − α) (pi2(S, S, S, T) + pi2(S, S, T, S))
+ (1 − α)² pi2(S, S, T, T)`.

Assumes: `source ≠ recipient`. -/
theorem pulseState_pi2_cross {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) :
    realization.pulseState alpha hnonneg hle source recipient
        (some (.pi2 source source recipient recipient))
      = admixedHeterozygosity alpha (state (some (.pi2 source source source source)))
          (state (some (.pi2 source source source recipient))
            + state (some (.pi2 source source recipient source)))
          (state (some (.pi2 source source recipient recipient))) := by
  have hpoint : (fun outcome ↦
      twoLocusJointHeterozygosity
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome source)
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome source)
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome recipient)
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome recipient))
      = alpha ^ 2 • (fun outcome ↦
          twoLocusJointHeterozygosity (realization.haplotype outcome source)
            (realization.haplotype outcome source) (realization.haplotype outcome source)
            (realization.haplotype outcome source))
        + (alpha * (1 - alpha)) • ((fun outcome ↦
            twoLocusJointHeterozygosity (realization.haplotype outcome source)
              (realization.haplotype outcome source) (realization.haplotype outcome source)
              (realization.haplotype outcome recipient))
          + (fun outcome ↦
            twoLocusJointHeterozygosity (realization.haplotype outcome source)
              (realization.haplotype outcome source) (realization.haplotype outcome recipient)
              (realization.haplotype outcome source)))
        + (1 - alpha) ^ 2 • (fun outcome ↦
          twoLocusJointHeterozygosity (realization.haplotype outcome source)
            (realization.haplotype outcome source) (realization.haplotype outcome recipient)
            (realization.haplotype outcome recipient)) := by
    funext outcome
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [realization.pulseHaplotype_of_ne alpha hnonneg hle source recipient source hne outcome,
      pulseHaplotype_recipient realization hnonneg hle source recipient outcome]
    simp only [twoLocusJointHeterozygosity, twoLocusLeftHeterozygosity,
      twoLocusRightHeterozygosity, TwoLocusHaplotypeFrequencies.mixture_rightFrequency]
    ring
  change realization.expectation (fun outcome ↦
      twoLocusJointHeterozygosity
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome source)
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome source)
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome recipient)
        (realization.pulseHaplotype alpha hnonneg hle source recipient outcome recipient)) = _
  rw [hpoint, realization.expectation.add_eval, realization.expectation.add_eval,
    realization.expectation.smul_eval, realization.expectation.smul_eval,
    realization.expectation.smul_eval, realization.expectation.add_eval, admixedHeterozygosity,
    realization.pi2_eq source source source source,
    realization.pi2_eq source source source recipient,
    realization.pi2_eq source source recipient source,
    realization.pi2_eq source source recipient recipient]

/-! ## The squared correlation right after the pulse -/

/-- **The cross-population expected squared correlation right after the pulse**,
`E[D_S D_T]' / E[π^A_S π^B_T]'` as a ratio of expectations.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two moment coordinates. -/
def pulseSquaredCorrelation {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) (source recipient : Fin D) : ℝ :=
  realization.pulseState alpha hnonneg hle source recipient (some (.DD source recipient))
    / realization.pulseState alpha hnonneg hle source recipient
        (some (.pi2 source source recipient recipient))

/-- **The portability ratio right after the pulse**: the post-pulse cross squared correlation
over the source's own `σ²_D`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of moment coordinates. -/
def pulsePortabilityRatio {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) (source recipient : Fin D) : ℝ :=
  pulseSquaredCorrelation realization alpha hnonneg hle source recipient
    / TwoLocusPortabilityDecay.ancestralSquaredCorrelation state source

/-- **The squared correlation right after the pulse in closed form**: the admixed covariance over
the admixed heterozygosity product.

Assumes: `source ≠ recipient`. -/
theorem pulseSquaredCorrelation_eq {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) :
    pulseSquaredCorrelation realization alpha hnonneg hle source recipient
      = admixedCovariance alpha (state (some (.DD source source)))
          (state (some (.DD source recipient))) (admixtureChannel state source recipient)
        / admixedHeterozygosity alpha (state (some (.pi2 source source source source)))
          (state (some (.pi2 source source source recipient))
            + state (some (.pi2 source source recipient source)))
          (state (some (.pi2 source source recipient recipient))) := by
  rw [pulseSquaredCorrelation, pulseState_DD_cross realization hnonneg hle hne,
    pulseState_pi2_cross realization hnonneg hle hne]

/-- **An empty pulse changes nothing**: at `α = 0` the squared correlation is the pre-pulse
cross squared correlation `E[D_S D_T] / E[π^A_S π^B_T]`.

Assumes: `source ≠ recipient`. -/
theorem pulseSquaredCorrelation_zero {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {source recipient : Fin D}
    (hne : source ≠ recipient) :
    pulseSquaredCorrelation realization 0 le_rfl zero_le_one source recipient
      = state (some (.DD source recipient))
        / state (some (.pi2 source source recipient recipient)) := by
  rw [pulseSquaredCorrelation_eq realization le_rfl zero_le_one hne]
  simp [admixedCovariance, admixedHeterozygosity]

/-- **A complete pulse gives the source's own value**: at `α = 1` the squared correlation is
the source's `σ²_D = E[D_S²] / E[π^A_S π^B_S]`.

Assumes: `source ≠ recipient`. -/
theorem pulseSquaredCorrelation_one {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {source recipient : Fin D}
    (hne : source ≠ recipient) :
    pulseSquaredCorrelation realization 1 zero_le_one le_rfl source recipient
      = TwoLocusPortabilityDecay.ancestralSquaredCorrelation state source := by
  rw [pulseSquaredCorrelation_eq realization zero_le_one le_rfl hne,
    TwoLocusPortabilityDecay.ancestralSquaredCorrelation]
  simp [admixedCovariance, admixedHeterozygosity]

/-- At `α = 0` the portability ratio is the pre-pulse ratio.

Assumes: `source ≠ recipient`. -/
theorem pulsePortabilityRatio_zero {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {source recipient : Fin D}
    (hne : source ≠ recipient) :
    pulsePortabilityRatio realization 0 le_rfl zero_le_one source recipient
      = state (some (.DD source recipient))
          / state (some (.pi2 source source recipient recipient))
        / TwoLocusPortabilityDecay.ancestralSquaredCorrelation state source := by
  rw [pulsePortabilityRatio, pulseSquaredCorrelation_zero realization hne]

/-- At `α = 1` the portability ratio is `1`.

Assumes: `source ≠ recipient` and a nonzero source correlation. -/
theorem pulsePortabilityRatio_one {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {source recipient : Fin D}
    (hne : source ≠ recipient)
    (hsource : TwoLocusPortabilityDecay.ancestralSquaredCorrelation state source ≠ 0) :
    pulsePortabilityRatio realization 1 zero_le_one le_rfl source recipient = 1 := by
  rw [pulsePortabilityRatio, pulseSquaredCorrelation_one realization hne, div_self hsource]

/-- **The covariance ratio right after the pulse**, relative to the source's own `E[D_S²]`, is
`α + (1 − α) R₀ + α (1 − α) κ`, with `R₀ = E[D_S D_T] / E[D_S²]` and `κ = Λ / E[D_S²]`.

Assumes: `source ≠ recipient` and `E[D_S²] ≠ 0`. -/
theorem pulseState_DD_cross_div {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient)
    (hsource : state (some (.DD source source)) ≠ 0) :
    realization.pulseState alpha hnonneg hle source recipient (some (.DD source recipient))
        / state (some (.DD source source))
      = alpha
        + (1 - alpha) * (state (some (.DD source recipient)) / state (some (.DD source source)))
        + alpha * (1 - alpha)
          * (admixtureChannel state source recipient / state (some (.DD source source))) := by
  rw [pulseState_DD_cross realization hnonneg hle hne, admixedCovariance, div_eq_iff hsource]
  have hcross := div_mul_cancel₀ (state (some (.DD source recipient))) hsource
  have hchannel := div_mul_cancel₀ (admixtureChannel state source recipient) hsource
  linear_combination -(1 - alpha) * hcross - alpha * (1 - alpha) * hchannel

/-- **The admixed covariance increases with the pulse fraction** when the differentiation
channel is at most the gap `a − b` between the source's own and the cross covariance.

Assumes: `|Λ| ≤ a − b`. -/
theorem admixedCovariance_monotoneOn {sourceOwn cross channel : ℝ}
    (hchannel : |channel| ≤ sourceOwn - cross) :
    MonotoneOn (fun alpha ↦ admixedCovariance alpha sourceOwn cross channel) (Set.Icc 0 1) := by
  intro s hs t ht hst
  have hsum : |1 - s - t| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hs.2, ht.2], by linarith [hs.1, ht.1]⟩
  have hbound : |channel * (1 - s - t)| ≤ sourceOwn - cross := by
    rw [abs_mul]
    calc |channel| * |1 - s - t| ≤ |channel| * 1 :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg channel)
      _ = |channel| := mul_one _
      _ ≤ sourceOwn - cross := hchannel
  have hinner : 0 ≤ sourceOwn - cross + channel * (1 - s - t) := by
    linarith [neg_abs_le (channel * (1 - s - t))]
  have hprod := mul_nonneg (sub_nonneg.mpr hst) hinner
  have hdiff : admixedCovariance t sourceOwn cross channel
        - admixedCovariance s sourceOwn cross channel
      = (t - s) * (sourceOwn - cross + channel * (1 - s - t)) := by
    unfold admixedCovariance
    ring
  show admixedCovariance s sourceOwn cross channel ≤ admixedCovariance t sourceOwn cross channel
  linarith

/-! ## Decay after the pulse -/

/-- A common exponential factor cancels from a ratio, and the extra rate survives as a factor. -/
theorem exp_mul_div_exp_mul (common extra duration numerator denominator : ℝ) :
    Real.exp (-(common + extra) * duration) * numerator
        / (Real.exp (-common * duration) * denominator)
      = Real.exp (-(extra * duration)) * (numerator / denominator) := by
  rw [show -(common + extra) * duration = -common * duration + -(extra * duration) by ring,
    Real.exp_add, mul_assoc, mul_div_mul_left _ _ (Real.exp_pos _).ne', mul_div_assoc]

/-- **The moment vector of a pulse followed by one epoch.**  The recipient receives `α` of its
haplotypes from the source, and the joint vector then evolves for `duration` under `rates`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A corpus epoch applied to the pulsed moment vector. -/
def pulseHistoryState (rates : ManyDemeLDRates D) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) (source recipient : Fin D) {duration : ℝ} (hduration : 0 ≤ duration) :
    AffineLowOrderLDCoordinate D → ℝ :=
  propagateLowOrderLDInstructions [LowOrderLDInstruction.evolve (rates.epoch duration hduration)]
    (realization.pulseState alpha hnonneg hle source recipient)

/-- The pulse history is the corpus epoch propagator applied to the pulsed vector. -/
theorem pulseHistoryState_eq (rates : ManyDemeLDRates D) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) (source recipient : Fin D) {duration : ℝ} (hduration : 0 ≤ duration) :
    pulseHistoryState rates realization alpha hnonneg hle source recipient hduration
      = (matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec
          (realization.pulseState alpha hnonneg hle source recipient) :=
  rfl

/-- **After the pulse the cross linkage covariance decays at `c_S + c_T + (ρ_S + ρ_T)/2`.**

Assumes: no migration, no mutation, and `source ≠ recipient`. -/
theorem pulseHistoryState_DD (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) {duration : ℝ}
    (hduration : 0 ≤ duration) :
    pulseHistoryState rates realization alpha hnonneg hle source recipient hduration
        (some (.DD source recipient))
      = Real.exp (-(rates.coalescence source + rates.coalescence recipient
          + (rates.recombination source + rates.recombination recipient) / 2) * duration)
        * admixedCovariance alpha (state (some (.DD source source)))
          (state (some (.DD source recipient))) (admixtureChannel state source recipient) := by
  have hrow := TwoLocusPortabilityDecay.matrixExponential_mulVec_apply_of_row_eq
    (augmentedLowOrderLDGenerator rates) duration _
    (realization.pulseState alpha hnonneg hle source recipient) (some (.DD source recipient))
    (TwoLocusPortabilityDecay.augmentedLowOrderLDGenerator_DD_row rates hmigration hmutation hne)
  rw [pulseState_DD_cross realization hnonneg hle hne, mul_comm duration] at hrow
  exact hrow

/-- **After the pulse the cross heterozygosity product decays at `c_S + c_T`.**

Assumes: no migration, no mutation, and `source ≠ recipient`. -/
theorem pulseHistoryState_pi2 (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) {duration : ℝ}
    (hduration : 0 ≤ duration) :
    pulseHistoryState rates realization alpha hnonneg hle source recipient hduration
        (some (.pi2 source source recipient recipient))
      = Real.exp (-(rates.coalescence source + rates.coalescence recipient) * duration)
        * admixedHeterozygosity alpha (state (some (.pi2 source source source source)))
          (state (some (.pi2 source source source recipient))
            + state (some (.pi2 source source recipient source)))
          (state (some (.pi2 source source recipient recipient))) := by
  have hrow := TwoLocusPortabilityDecay.matrixExponential_mulVec_apply_of_row_eq
    (augmentedLowOrderLDGenerator rates) duration _
    (realization.pulseState alpha hnonneg hle source recipient)
    (some (.pi2 source source recipient recipient))
    (TwoLocusPortabilityDecay.augmentedLowOrderLDGenerator_pi2_row rates hmigration hmutation hne)
  rw [pulseState_pi2_cross realization hnonneg hle hne, mul_comm duration] at hrow
  exact hrow

/-- **The cross-population expected squared correlation a time `duration` after the pulse**,
`E[D_S D_T] / E[π^A_S π^B_T]` as a ratio of expectations.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two moment coordinates. -/
def pulseHistorySquaredCorrelation (rates : ManyDemeLDRates D)
    {state : AffineLowOrderLDCoordinate D → ℝ} (realization : LowOrderLDHaplotypeRealization state)
    (alpha : ℝ) (hnonneg : 0 ≤ alpha) (hle : alpha ≤ 1) (source recipient : Fin D)
    {duration : ℝ} (hduration : 0 ≤ duration) : ℝ :=
  pulseHistoryState rates realization alpha hnonneg hle source recipient hduration
      (some (.DD source recipient))
    / pulseHistoryState rates realization alpha hnonneg hle source recipient hduration
        (some (.pi2 source source recipient recipient))

/-- **After the pulse the squared correlation decays by the split decay factor**: a time `T`
after the pulse it is `e^{-r T}` times its post-pulse value, `r = (ρ_S + ρ_T)/2`.  Drift does
not enter.

Assumes: no migration, no mutation, and `source ≠ recipient`. -/
theorem pulseHistorySquaredCorrelation_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) {duration : ℝ}
    (hduration : 0 ≤ duration) :
    pulseHistorySquaredCorrelation rates realization alpha hnonneg hle source recipient hduration
      = TwoLocusPortabilityDecay.portabilityDecay
          ((rates.recombination source + rates.recombination recipient) / 2) duration
        * pulseSquaredCorrelation realization alpha hnonneg hle source recipient := by
  rw [pulseHistorySquaredCorrelation,
    pulseHistoryState_DD rates hmigration hmutation realization hnonneg hle hne hduration,
    pulseHistoryState_pi2 rates hmigration hmutation realization hnonneg hle hne hduration,
    exp_mul_div_exp_mul, pulseSquaredCorrelation_eq realization hnonneg hle hne,
    TwoLocusPortabilityDecay.portabilityDecay]

/-- **Portability after a pulse in closed form**: a time `T` after the pulse the squared
correlation is `e^{-r T}` times the admixed covariance over the admixed heterozygosity product.

Assumes: no migration, no mutation, and `source ≠ recipient`. -/
theorem pulseHistorySquaredCorrelation_eq_closedForm (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) {alpha : ℝ} (hnonneg : 0 ≤ alpha)
    (hle : alpha ≤ 1) {source recipient : Fin D} (hne : source ≠ recipient) {duration : ℝ}
    (hduration : 0 ≤ duration) :
    pulseHistorySquaredCorrelation rates realization alpha hnonneg hle source recipient hduration
      = TwoLocusPortabilityDecay.portabilityDecay
          ((rates.recombination source + rates.recombination recipient) / 2) duration
        * (admixedCovariance alpha (state (some (.DD source source)))
            (state (some (.DD source recipient))) (admixtureChannel state source recipient)
          / admixedHeterozygosity alpha (state (some (.pi2 source source source source)))
            (state (some (.pi2 source source source recipient))
              + state (some (.pi2 source source recipient source)))
            (state (some (.pi2 source source recipient recipient)))) := by
  rw [pulseHistorySquaredCorrelation_eq rates hmigration hmutation realization hnonneg hle hne
    hduration, pulseSquaredCorrelation_eq realization hnonneg hle hne]

end

end Descent.Portability.AdmixturePortabilityDecay
