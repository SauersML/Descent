/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PulseJetExpansion
import Descent.Portability.RandomStageKernel

assert_below Descent.Decision Descent.Program

/-!
# The deterministic pulse stages as probability kernels, and the five-stage index

`PulseJetExpansion` proves that each deterministic pulse moves a low-order coordinate by its
parameter times a velocity, with a uniform quadratic remainder on `[0,1]`.  `RandomStageKernel`
does the same for the random resampling stage and supplies the uniform mixture that adds the
stage generators.  This file is the bridge: it presents each pulse as a genuine probability
kernel with the same branch type as the resampling kernel, puts all five stages under one
index, and proves the single expansion lemma that `apply_uniformStageMixture` consumes.

`deterministicHaplotypeKernel` carries a deterministic move as a four-branch kernel whose
branch is drawn from a point mass and then ignored.  The corpus already has a one-branch
deterministic kernel over `Unit`, but a `uniformMixture` requires all its sub-kernels to share
one branch type, and the resampling stage's branch type is `TwoLocusHaplotype`; that is the
only reason this exists.  `pulseStageKernel pulse rate tau` runs the pulse at `tau * rate`,
and the pulse clamps its own fraction into `[0,1]`, so the result is a probability kernel for
every real `tau` with no side condition.

`apply_pulseStageKernel_expansion` is the NOTE 1 (3) estimate for one pulse stage:
`|K f x - f x - tau * rate * velocity x| ≤ tau * pulseStageSlack`.  Below the clamp the slack
is the quadratic remainder carried linearly in `tau`; at and above the clamp a second term
switches on, large enough to absorb the whole unexpanded difference.  The switch is written
with the corpus's own `pulseFraction`, so the slack is continuous and
`pulseStageSlack_tendsto` gives the vanishing `epsilon` Theorem 1 needs.  This is the same
device `driftStageSlack` uses for the random stage.

`Stage D` indexes the five stage kinds of one microscopic step: resampling in each deme,
migration between each ordered pair, recombination, and the two single-locus mutation pulses.
`stageRate` reads each stage's rate out of the corpus's `ManyDemeLDRates` in that structure's
own coordinates, and the half-rates are NOTE 1 section 2.2's: `rho_i / 2` for recombination
and `theta_i / 2` for each allele-flip pulse, so that summing a stage velocity against
`stageRate` reproduces the corpus generator row rather than twice it.  `StageExpansion`
bundles the five certificates one observable needs, `coordinateStageExpansion` and
`rightHeterozygosityStageExpansion` are its inhabitants, and `apply_stageKernel_expansion` is
the per-stage expansion uniform over the index.

Scope.  The identification of each `stageRate * stageVelocity` with the matching row of
`augmentedLowOrderLDGenerator` is NOT proved here; four such bridges live in
`PulseJetExpansion` and the rest belong to the module that assembles the
`MicroscopicApproximation`.  Nothing here forms a semigroup or takes a limit.  Multinomial
resampling, NOTE 1 (10), remains unformalized; the single-draw alternative is used throughout.

## Empirical status

None.  The bodies here are algebra: a kernel built from a deterministic map and a point mass,
a clamped parameter, and bounds relating them, so no measurement can bear on them.  Whether a
population's microscopic step is this list of stages is asked wherever a composed prediction
meets data, not here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PulseStageKernel

open Coalescent PulseJetExpansion ResamplingJetExpansion RandomStageKernel
open Descent.Portability.FiniteMixtureKernel

noncomputable section

/-! ## A deterministic move with the resampling branch type -/

/-- A deterministic move carried as a four-branch probability kernel: the branch is drawn from
a point mass at `AB` and the move ignores it.  The corpus's one-branch `deterministic` kernel
over `Unit` cannot be used here, because a `uniformMixture` requires every sub-kernel to carry
the same branch type and the resampling stage's is `TwoLocusHaplotype`. -/
def deterministicHaplotypeKernel {X : Type*} (move : X → X) :
    FiniteMixtureKernel TwoLocusHaplotype X where
  weight _ drawn := twoLocusHaplotypeIndicator .AB drawn
  move _ point := move point
  weight_nonneg _ drawn := by
    simp only [twoLocusHaplotypeIndicator]
    split <;> norm_num
  weight_sum _ := by
    simp [twoLocusHaplotypeIndicator]

/-- The deterministic kernel evaluates an observable at the moved state. -/
theorem apply_deterministicHaplotypeKernel {X : Type*} (move : X → X)
    (observable : X → ℝ) (point : X) :
    (deterministicHaplotypeKernel move).apply observable point = observable (move point) := by
  simp [FiniteMixtureKernel.apply, deterministicHaplotypeKernel,
    twoLocusHaplotypeIndicator]

/-! ## One deterministic pulse stage -/

/-- One deterministic pulse stage: the pulse family run at parameter `tau * rate`, presented
as a four-branch probability kernel.  The pulse clamps its own fraction, so this is a genuine
kernel for every real `tau` and every real `rate`. -/
def pulseStageKernel {D : ℕ}
    (pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D) (rate tau : ℝ) :
    FiniteMixtureKernel TwoLocusHaplotype (DemeHaplotypeState D) :=
  deterministicHaplotypeKernel (pulse (tau * rate))

/-- The explicit slack of one deterministic pulse stage.  The first term is the pulse's
quadratic remainder carried linearly in `tau`; the second switches on only once the clamp
binds, and is then large enough to absorb the whole unexpanded difference.  The switch reuses
the corpus's `pulseFraction`, so the slack is continuous and vanishes at `tau = 0`. -/
def pulseStageSlack (rate valueBound velocityBound remainder tau : ℝ) : ℝ :=
  remainder * rate ^ 2 * tau +
    (2 * valueBound * rate + rate * velocityBound) * pulseFraction (2 * rate * tau - 1)

/-- The pulse-stage slack vanishes with the step size, which is what NOTE 1 (3) asks of
`epsilon`.  The clamp term is identically zero near the origin. -/
theorem pulseStageSlack_tendsto (rate valueBound velocityBound remainder : ℝ) :
    Filter.Tendsto (pulseStageSlack rate valueBound velocityBound remainder)
      (nhds 0) (nhds 0) := by
  have hcontinuous : Continuous
      fun tau : ℝ ↦ pulseStageSlack rate valueBound velocityBound remainder tau := by
    simp only [pulseStageSlack, pulseFraction]
    exact Continuous.add (continuous_const.mul continuous_id)
      (continuous_const.mul (Continuous.min continuous_const
        (Continuous.max continuous_const
          (Continuous.sub (continuous_const.mul continuous_id) continuous_const))))
  have hmax : max (0 : ℝ) (2 * rate * 0 - 1) = 0 := by
    rw [max_eq_left]
    norm_num
  have hzero : pulseStageSlack rate valueBound velocityBound remainder 0 = 0 := by
    simp only [pulseStageSlack, pulseFraction, hmax, min_eq_right zero_le_one]
    ring
  exact hcontinuous.tendsto' 0 0 hzero

/-- **One deterministic pulse stage is its generator row plus a vanishing slack.**  For any
observable carrying a `PulseExpansion`, the stage at rate `rate` and parameter `tau` moves the
observable by `tau * rate` times its velocity, up to `tau` times a slack that tends to zero
with `tau`.  This is hypothesis (3) of NOTE 1 Theorem 1 for one deterministic stage. -/
theorem apply_pulseStageKernel_expansion {D : ℕ}
    {pulse : ℝ → DemeHaplotypeState D → DemeHaplotypeState D}
    {observable : DemeHaplotypeState D → ℝ}
    (certificate : PulseExpansion pulse observable) (rate tau : ℝ) (hrate : 0 ≤ rate)
    (htau : 0 ≤ tau) (state : DemeHaplotypeState D) :
    |(pulseStageKernel pulse rate tau).apply observable state - observable state -
        tau * (rate * certificate.velocity state)| ≤
      tau * pulseStageSlack rate certificate.valueBound certificate.velocityBound
        certificate.remainder tau := by
  have hvalue := certificate.valueBound_nonneg
  have hvelocity := certificate.velocityBound_nonneg
  have hremainder := certificate.remainder_nonneg
  have hproduct : (0 : ℝ) ≤ tau * rate := mul_nonneg htau hrate
  have hconstant : (0 : ℝ) ≤
      2 * certificate.valueBound * rate + rate * certificate.velocityBound := by
    have hleft := mul_nonneg hvalue hrate
    have hright := mul_nonneg hrate hvelocity
    linarith
  simp only [pulseStageKernel]
  rw [apply_deterministicHaplotypeKernel]
  by_cases hclamp : tau * rate ≤ 1
  · have hbase := certificate.expansion (tau * rate) hproduct hclamp state
    have hmatch : tau * (rate * certificate.velocity state) =
        tau * rate * certificate.velocity state := by
      ring
    rw [hmatch]
    refine le_trans hbase ?_
    have hfraction : (0 : ℝ) ≤ pulseFraction (2 * rate * tau - 1) := pulseFraction_nonneg _
    simp only [pulseStageSlack]
    nlinarith [mul_nonneg htau (mul_nonneg hconstant hfraction)]
  · push_neg at hclamp
    have hactive : pulseFraction (2 * rate * tau - 1) = 1 := by
      rw [pulseFraction, max_eq_right (by nlinarith : (0 : ℝ) ≤ 2 * rate * tau - 1),
        min_eq_left (by nlinarith : (1 : ℝ) ≤ 2 * rate * tau - 1)]
    obtain ⟨hmovedlow, hmovedhigh⟩ :=
      abs_le.mp (certificate.value_abs_le (pulse (tau * rate) state))
    obtain ⟨hstatelow, hstatehigh⟩ := abs_le.mp (certificate.value_abs_le state)
    obtain ⟨hvelocitylow, hvelocityhigh⟩ := abs_le.mp (certificate.velocity_abs_le state)
    have hscaledhigh := mul_le_mul_of_nonneg_left hvelocityhigh hproduct
    have hscaledlow := mul_le_mul_of_nonneg_left hvelocitylow hproduct
    have hquadratic : (0 : ℝ) ≤
        tau * (certificate.remainder * rate ^ 2 * tau) :=
      mul_nonneg htau (mul_nonneg (mul_nonneg hremainder (sq_nonneg rate)) htau)
    have hgain : (0 : ℝ) ≤ certificate.valueBound * (tau * rate - 1) :=
      mul_nonneg hvalue (le_of_lt (sub_pos.mpr hclamp))
    simp only [pulseStageSlack, hactive]
    rw [abs_le]
    constructor <;> nlinarith [hquadratic, hgain, hscaledhigh, hscaledlow]

/-! ## The five stages of one microscopic step -/

/-- The stages of one microscopic step for `demeCount` demes: the random resampling stage in
each deme, migration along each ordered pair, recombination in each deme, and the two
single-locus allele-flip pulses in each deme. -/
inductive Stage (demeCount : ℕ) where
  | drift (deme : Fin demeCount)
  | migration (source recipient : Fin demeCount)
  | recombination (deme : Fin demeCount)
  | mutationLeft (deme : Fin demeCount)
  | mutationRight (deme : Fin demeCount)
deriving DecidableEq, Fintype

/-- With at least one deme there is at least one stage, so the uniform mixture over stages is
defined.  The deme is taken as data rather than through a nonemptiness instance. -/
theorem card_stage_pos {demeCount : ℕ} (deme : Fin demeCount) :
    0 < Fintype.card (Stage demeCount) :=
  Fintype.card_pos_iff.mpr ⟨Stage.drift deme⟩

/-- The rate carried by each stage, read out of the corpus's `ManyDemeLDRates` in that
structure's own coordinates.  Migration into recipient `i` from source `j` carries `m_ij`; the
halves on recombination and mutation are NOTE 1 section 2.2's, where the recombination drift
rate is `rho_i / 2` and the per-locus allele-flip rate is `theta_i / 2`. -/
def stageRate {D : ℕ} (rates : ManyDemeLDRates D) : Stage D → ℝ
  | .drift deme => rates.coalescence deme
  | .migration source recipient => rates.migration recipient source
  | .recombination deme => rates.recombination deme / 2
  | .mutationLeft deme => rates.mutation deme / 2
  | .mutationRight deme => rates.mutation deme / 2

/-- Every stage rate is nonnegative; the coalescence rate is strictly positive. -/
theorem stageRate_nonneg {D : ℕ} (rates : ManyDemeLDRates D) (stage : Stage D) :
    0 ≤ stageRate rates stage := by
  cases stage with
  | drift deme => exact le_of_lt (rates.coalescence_pos deme)
  | migration source recipient => exact rates.migration_nonneg recipient source
  | recombination deme =>
      simp only [stageRate]
      linarith [rates.recombination_nonneg deme]
  | mutationLeft deme =>
      simp only [stageRate]
      linarith [rates.mutation_nonneg deme]
  | mutationRight deme =>
      simp only [stageRate]
      linarith [rates.mutation_nonneg deme]

/-- The kernel of each stage at parameter `tau`: the calibrated resampling kernel for drift
and the clamped deterministic pulse for each of the four pulse stages.  All five carry the
branch type `TwoLocusHaplotype`, so they sit in one `uniformMixture`. -/
def stageKernel {D : ℕ} (rates : ManyDemeLDRates D) :
    Stage D → ℝ → FiniteMixtureKernel TwoLocusHaplotype (DemeHaplotypeState D)
  | .drift deme, tau => driftStageKernel deme (rates.coalescence deme) tau
  | .migration source recipient, tau =>
      pulseStageKernel (migrationPulse source recipient)
        (rates.migration recipient source) tau
  | .recombination deme, tau =>
      pulseStageKernel (recombinationPulseAt deme) (rates.recombination deme / 2) tau
  | .mutationLeft deme, tau =>
      pulseStageKernel (leftMutationPulseAt deme) (rates.mutation deme / 2) tau
  | .mutationRight deme, tau =>
      pulseStageKernel (rightMutationPulseAt deme) (rates.mutation deme / 2) tau

/-! ## One observable's certificates for all five stages -/

/-- Everything the stage expansion needs about one corpus jet: a resampling expansion for the
drift stage, and a pulse expansion of the same observable under each of the four deterministic
pulse families.

Assumes: the five certificates.  Its inhabitants are `coordinateStageExpansion`, for every
coordinate of the closed low-order family, and `rightHeterozygosityStageExpansion`. -/
structure StageExpansion {D : ℕ} (jet : TwoLocusDiffusionJet D) where
  /-- The resampling expansion used by the drift stage. -/
  drift : ResamplingExpansion jet
  /-- The pulse expansion under each migration pulse. -/
  migration : ∀ source recipient : Fin D,
    PulseExpansion (migrationPulse source recipient) jet.value
  /-- The pulse expansion under each recombination pulse. -/
  recombination : ∀ deme : Fin D, PulseExpansion (recombinationPulseAt deme) jet.value
  /-- The pulse expansion under each left-locus mutation pulse. -/
  mutationLeft : ∀ deme : Fin D, PulseExpansion (leftMutationPulseAt deme) jet.value
  /-- The pulse expansion under each right-locus mutation pulse. -/
  mutationRight : ∀ deme : Fin D, PulseExpansion (rightMutationPulseAt deme) jet.value

/-- The unweighted velocity of one stage: the corpus drift for the resampling stage and the
pulse velocity for each deterministic stage. -/
def stageVelocity {D : ℕ} {jet : TwoLocusDiffusionJet D} (certificate : StageExpansion jet) :
    Stage D → DemeHaplotypeState D → ℝ
  | .drift deme => jet.driftAt deme
  | .migration source recipient => (certificate.migration source recipient).velocity
  | .recombination deme => (certificate.recombination deme).velocity
  | .mutationLeft deme => (certificate.mutationLeft deme).velocity
  | .mutationRight deme => (certificate.mutationRight deme).velocity

/-- The rate-weighted velocity of one stage.  This is exactly the `velocity` argument
`apply_uniformStageMixture` consumes, so that the mixture's first-order term is the sum of the
generator rows rather than of the bare pulse velocities. -/
def stageDrift {D : ℕ} {jet : TwoLocusDiffusionJet D} (rates : ManyDemeLDRates D)
    (certificate : StageExpansion jet) (stage : Stage D)
    (state : DemeHaplotypeState D) : ℝ :=
  stageRate rates stage * stageVelocity certificate stage state

/-- The slack of one stage: the drift-stage slack for resampling and the pulse-stage slack for
each deterministic stage, each at that stage's own rate. -/
def stageSlack {D : ℕ} {jet : TwoLocusDiffusionJet D} (rates : ManyDemeLDRates D)
    (certificate : StageExpansion jet) : Stage D → ℝ → ℝ
  | .drift deme => fun tau ↦ driftStageSlack (rates.coalescence deme) tau
      certificate.drift.bound certificate.drift.remainder
  | .migration source recipient =>
      pulseStageSlack (rates.migration recipient source)
        (certificate.migration source recipient).valueBound
        (certificate.migration source recipient).velocityBound
        (certificate.migration source recipient).remainder
  | .recombination deme =>
      pulseStageSlack (rates.recombination deme / 2)
        (certificate.recombination deme).valueBound
        (certificate.recombination deme).velocityBound
        (certificate.recombination deme).remainder
  | .mutationLeft deme =>
      pulseStageSlack (rates.mutation deme / 2)
        (certificate.mutationLeft deme).valueBound
        (certificate.mutationLeft deme).velocityBound
        (certificate.mutationLeft deme).remainder
  | .mutationRight deme =>
      pulseStageSlack (rates.mutation deme / 2)
        (certificate.mutationRight deme).valueBound
        (certificate.mutationRight deme).velocityBound
        (certificate.mutationRight deme).remainder

/-- **Every stage expands to first order, uniformly over the stage index.**  This is the
single hypothesis `apply_uniformStageMixture` asks for, at the one state and the one parameter
it is applied to. -/
theorem apply_stageKernel_expansion {D : ℕ} {jet : TwoLocusDiffusionJet D}
    (rates : ManyDemeLDRates D) (certificate : StageExpansion jet) (stage : Stage D)
    (tau : ℝ) (htau : 0 < tau) (state : DemeHaplotypeState D) :
    |(stageKernel rates stage tau).apply jet.value state - jet.value state -
        tau * stageDrift rates certificate stage state| ≤
      tau * stageSlack rates certificate stage tau := by
  cases stage with
  | drift deme =>
      exact apply_driftStageKernel_expansion certificate.drift (rates.coalescence deme) tau
        (rates.coalescence_pos deme) htau state deme
  | migration source recipient =>
      exact apply_pulseStageKernel_expansion (certificate.migration source recipient)
        (rates.migration recipient source) tau (rates.migration_nonneg recipient source)
        (le_of_lt htau) state
  | recombination deme =>
      exact apply_pulseStageKernel_expansion (certificate.recombination deme)
        (rates.recombination deme / 2) tau
        (by linarith [rates.recombination_nonneg deme]) (le_of_lt htau) state
  | mutationLeft deme =>
      exact apply_pulseStageKernel_expansion (certificate.mutationLeft deme)
        (rates.mutation deme / 2) tau
        (by linarith [rates.mutation_nonneg deme]) (le_of_lt htau) state
  | mutationRight deme =>
      exact apply_pulseStageKernel_expansion (certificate.mutationRight deme)
        (rates.mutation deme / 2) tau
        (by linarith [rates.mutation_nonneg deme]) (le_of_lt htau) state

/-- Every stage's slack vanishes with the parameter, so the assembled mixture inherits a
vanishing `epsilon`. -/
theorem stageSlack_tendsto {D : ℕ} {jet : TwoLocusDiffusionJet D}
    (rates : ManyDemeLDRates D) (certificate : StageExpansion jet) (stage : Stage D) :
    Filter.Tendsto (stageSlack rates certificate stage) (nhds 0) (nhds 0) := by
  cases stage with
  | drift deme =>
      exact driftStageSlack_tendsto (rates.coalescence deme) certificate.drift.bound
        certificate.drift.remainder
  | migration source recipient =>
      exact pulseStageSlack_tendsto (rates.migration recipient source)
        (certificate.migration source recipient).valueBound
        (certificate.migration source recipient).velocityBound
        (certificate.migration source recipient).remainder
  | recombination deme =>
      exact pulseStageSlack_tendsto (rates.recombination deme / 2)
        (certificate.recombination deme).valueBound
        (certificate.recombination deme).velocityBound
        (certificate.recombination deme).remainder
  | mutationLeft deme =>
      exact pulseStageSlack_tendsto (rates.mutation deme / 2)
        (certificate.mutationLeft deme).valueBound
        (certificate.mutationLeft deme).velocityBound
        (certificate.mutationLeft deme).remainder
  | mutationRight deme =>
      exact pulseStageSlack_tendsto (rates.mutation deme / 2)
        (certificate.mutationRight deme).valueBound
        (certificate.mutationRight deme).velocityBound
        (certificate.mutationRight deme).remainder

/-! ## Inhabitants: every enlarged coordinate carries all five certificates -/

/-- Every coordinate of the closed low-order family carries the five stage certificates. -/
def coordinateStageExpansion {D : ℕ} (feature : LowOrderLDCoordinate D) :
    StageExpansion (twoLocusCoordinateJet feature) where
  drift := resamplingExpansionCoordinateJet feature
  migration source recipient :=
    (migrationCoordinateExpansion source recipient).coordinate feature
  recombination deme := (recombinationCoordinateExpansion deme).coordinate feature
  mutationLeft deme := (leftMutationCoordinateExpansion deme).coordinate feature
  mutationRight deme := (rightMutationCoordinateExpansion deme).coordinate feature

/-- The right-locus heterozygosity that NOTE 1 (6) adds to the stored family carries the five
stage certificates too, which is what makes the enlarged family closed under the whole
microscopic step and not only under the stored generator. -/
def rightHeterozygosityStageExpansion {D : ℕ} (first second : Fin D) :
    StageExpansion (twoLocusRightHJet first second) where
  drift := resamplingExpansionRightHJet first second
  migration source recipient :=
    (migrationCoordinateExpansion source recipient).rightHeterozygosity first second
  recombination deme :=
    (recombinationCoordinateExpansion deme).rightHeterozygosity first second
  mutationLeft deme :=
    (leftMutationCoordinateExpansion deme).rightHeterozygosity first second
  mutationRight deme :=
    (rightMutationCoordinateExpansion deme).rightHeterozygosity first second

end

end Descent.Portability.PulseStageKernel
