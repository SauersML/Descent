/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusMicroscopicApproximation

assert_below Descent.Decision Descent.Program

/-!
# Realizability under demographic histories with admixture pulses

NOTE1 closes its Theorem 2 with a condition for going beyond rate epochs and splits: a more
general instantaneous demographic map is covered whenever its pullback on the chosen features
has been shown to equal a proposed finite matrix.  This module shows that for an admixture
pulse, in which the recipient deme's haplotype frequencies become the mixture
`alpha * source + (1 - alpha) * recipient`, and extends NOTE1 Theorem 2 and Corollary 2.1 from
histories of rate epochs and splits to histories that also contain pulses.

The matrix.  Every stored coordinate `H`, `DD`, `Dz`, `pi2` is a polynomial in the per-deme
haplotype frequencies that is affine in each deme slot, except that the linkage determinant is
quadratic: the corpus's `mixture_linkage` adds `alpha (1 - alpha) (p_s - p_r) (q_s - q_r)`.  A
slot sitting at the recipient therefore expands as `slotAverage`, and a linkage slot at the
recipient also contributes that cross term, which against contrasts is an alternating stencil of
`Dz` or `pi2` coordinates, `contrastStencil`.  `pulseMoment` writes the resulting row for every
coordinate, `pulseMomentMap` is it as a linear map, and `lowOrderLDPulseTransform` is its matrix.
`pulseMoment_lowOrderLDFeature` is the pullback identity on one haplotype configuration,
`mulVec_expectation` carries a matrix through any expectation, and
`lowOrderLDPulseTransform_mulVec_eq_pulseState` is the pullback identity itself: for every
haplotype realization, the matrix applied to the stored state is the corpus's `pulseState`, the
moment vector of the transformed law.

Preservation.  `pulseRealization` realizes the pulsed state with the corpus's transformed witness
`pulseHaplotype`, and `locusExchangeablePulse` keeps locus exchangeability, the right-locus
heterozygosity being pulled back by the same slot average
(`lowOrderLDPulseTransform_mulVec_rightHeterozygosity`).  `PulseHistoryEvent` adds pulses to the
rate epochs and splits of `RateHistoryEvent`, and
`propagate_pulseHistory_preserves_locusExchangeable_realization` is NOTE1 Theorem 2 for any
finite list of them.  The present state of a compiled history is realizable, lies in the corpus
realization body, and satisfies Corollary 2.1: a positive semidefinite `DD` block,
Cauchy--Schwarz, a nonnegative diagonal, and the linkage-pair domain.

Scope.  Only admixture pulses are added; any other instantaneous map still needs its own pullback
identity.  The pulse fraction is a real number supplied together with its bounds `0 ≤ alpha ≤ 1`.

## Empirical status

None.  The bodies here are algebra: identities between polynomials in haplotype frequencies, and
expectations of them under one probability law, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PulseHistoryRealization

open Coalescent
open Descent.Portability.RealizationBody
open Descent.Portability.TwoLocusMicroscopicApproximation

noncomputable section

/-! ## The finite matrix of an admixture pulse -/

/-- The value at `deme` of a quantity that is affine in that deme's haplotype frequencies, after
a pulse of fraction `alpha` from `source` into `recipient`: at the recipient it is `alpha` times
the source's value plus `1 - alpha` times its own, and at every other deme it is unchanged. -/
def slotAverage {D : ℕ} (alpha : ℝ) (source recipient deme : Fin D) (value : Fin D → ℝ) : ℝ :=
  if deme = recipient then alpha * value source + (1 - alpha) * value recipient else value deme

/-- The alternating stencil over the two pulse endpoints, `g r r - g r s - g s r + g s s`: the
product of the locus-wise contrast differences `recipient - source`, read through `g`. -/
def contrastStencil {D : ℕ} (source recipient : Fin D) (value : Fin D → Fin D → ℝ) : ℝ :=
  value recipient recipient - value recipient source - value source recipient +
    value source source

/-- The stored low-order moment vector after a pulse of fraction `alpha` from `source` into
`recipient`, as a fixed linear combination of the moment vector before it.  `H` and `pi2` expand
slot by slot; a linkage slot at the recipient adds the cross term of the exact mixture law, a
`Dz` stencil against each other linkage factor and a `pi2` stencil against contrasts. -/
def pulseMoment {D : ℕ} (alpha : ℝ) (source recipient : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) : AffineLowOrderLDCoordinate D → ℝ
  | none => state none
  | some (.H first second) =>
      slotAverage alpha source recipient first fun a ↦
        slotAverage alpha source recipient second fun b ↦ state (some (.H a b))
  | some (.DD first second) =>
      (slotAverage alpha source recipient first fun a ↦
          slotAverage alpha source recipient second fun b ↦ state (some (.DD a b))) +
        (if second = recipient then alpha * (1 - alpha) / 4 *
            slotAverage alpha source recipient first (fun a ↦
              contrastStencil source recipient fun x y ↦ state (some (.Dz a x y)))
          else 0) +
        (if first = recipient then alpha * (1 - alpha) / 4 *
            slotAverage alpha source recipient second (fun b ↦
              contrastStencil source recipient fun x y ↦ state (some (.Dz b x y)))
          else 0) +
        (if first = recipient then
            (if second = recipient then (alpha * (1 - alpha)) ^ 2 *
                contrastStencil source recipient (fun x y ↦
                  contrastStencil source recipient fun x' y' ↦ state (some (.pi2 x x' y y')))
              else 0)
          else 0)
  | some (.Dz first second third) =>
      (slotAverage alpha source recipient first fun a ↦
          slotAverage alpha source recipient second fun b ↦
            slotAverage alpha source recipient third fun c ↦ state (some (.Dz a b c))) +
        (if first = recipient then 4 * (alpha * (1 - alpha)) *
            slotAverage alpha source recipient second (fun b ↦
              slotAverage alpha source recipient third fun c ↦
                contrastStencil source recipient fun x y ↦ state (some (.pi2 x b y c)))
          else 0)
  | some (.pi2 first second third fourth) =>
      slotAverage alpha source recipient first fun a ↦
        slotAverage alpha source recipient second fun b ↦
          slotAverage alpha source recipient third fun c ↦
            slotAverage alpha source recipient fourth fun e ↦ state (some (.pi2 a b c e))

/-- The pulse moment map is linear in the moment vector. -/
def pulseMomentMap {D : ℕ} (alpha : ℝ) (source recipient : Fin D) :
    (AffineLowOrderLDCoordinate D → ℝ) →ₗ[ℝ] (AffineLowOrderLDCoordinate D → ℝ) where
  toFun := pulseMoment alpha source recipient
  map_add' first second := by
    funext coordinate
    rcases coordinate with _ | (⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j, k⟩ | ⟨i, j, k, l⟩) <;>
      simp only [pulseMoment, slotAverage, contrastStencil, Pi.add_apply] <;>
      (try split_ifs) <;> ring
  map_smul' scalar state := by
    funext coordinate
    rcases coordinate with _ | (⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j, k⟩ | ⟨i, j, k, l⟩) <;>
      simp only [pulseMoment, slotAverage, contrastStencil, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply] <;>
      (try split_ifs) <;> ring

/-- **The finite matrix of an admixture pulse on the stored low-order coordinates.** -/
def lowOrderLDPulseTransform {D : ℕ} (alpha : ℝ) (source recipient : Fin D) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  LinearMap.toMatrix' (pulseMomentMap alpha source recipient)

/-- Multiplying by the pulse matrix is the pulse moment map. -/
theorem lowOrderLDPulseTransform_mulVec {D : ℕ} (alpha : ℝ) (source recipient : Fin D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (lowOrderLDPulseTransform alpha source recipient).mulVec state =
      pulseMoment alpha source recipient state :=
  LinearMap.toMatrix'_mulVec (pulseMomentMap alpha source recipient) state

/-! ## The pullback identity -/

/-- **The pulse pullback on one haplotype configuration.**  The pulse moment map applied to the
stored feature vector of the outcome's haplotype configuration is the feature vector of the
configuration after the corpus's pulse witness `pulseHaplotype`. -/
theorem pulseMoment_lowOrderLDFeature {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : Fin D) (outcome : realization.sampleSpace) :
    pulseMoment alpha source recipient (lowOrderLDFeature D (realization.haplotype outcome)) =
      lowOrderLDFeature D
        (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome) := by
  funext coordinate
  rcases coordinate with _ | (⟨first, second⟩ | ⟨first, second⟩ | ⟨first, second, third⟩ |
      ⟨first, second, third, fourth⟩) <;>
    simp only [pulseMoment, lowOrderLDFeature_none, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusHJet_value, twoLocusDDJet_value, twoLocusDzJet_value,
      twoLocusPi2Jet_value, slotAverage, contrastStencil,
      LowOrderLDHaplotypeRealization.pulseHaplotype] <;>
    split_ifs <;>
    (try simp only [TwoLocusHaplotypeFrequencies.mixture_linkage,
      TwoLocusHaplotypeFrequencies.mixture_leftFrequency,
      TwoLocusHaplotypeFrequencies.mixture_rightFrequency, twoLocusLeftHeterozygosity,
      twoLocusRightHeterozygosity, twoLocusJointHeterozygosity, twoLocusDzObservable,
      TwoLocusHaplotypeFrequencies.leftContrast, TwoLocusHaplotypeFrequencies.rightContrast,
      add_zero]) <;>
    ring

/-- A finite matrix passes through an expectation: applied to the expected vector, it gives the
expectation of the matrix applied to the random vector. -/
theorem mulVec_expectation {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (expectation : Foundations.ExpFunctional Ω) (matrix : Matrix ι ι ℝ)
    (vector : Ω → ι → ℝ) (row : ι) :
    matrix.mulVec (fun column ↦ expectation fun outcome ↦ vector outcome column) row =
      expectation fun outcome ↦ matrix.mulVec (vector outcome) row := by
  have hsum : (fun outcome ↦ matrix.mulVec (vector outcome) row) =
      ∑ column, fun outcome ↦ matrix row column * vector outcome column := by
    funext outcome
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [hsum, Foundations.ExpFunctional.eval_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun column _ ↦ ?_
  exact (expectation.smul_eval (matrix row column) fun outcome ↦ vector outcome column).symm

/-- A haplotype-realized stored state is the expectation of the corpus feature map under its
own law. -/
theorem realization_state_eq_expectation {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) :
    state = fun coordinate ↦ realization.expectation fun outcome ↦
      lowOrderLDFeature D (realization.haplotype outcome) coordinate := by
  funext coordinate
  rw [← haplotypeLowOrderLDState_eq_eval_lowOrderLDFeature]
  rcases coordinate with _ | (⟨first, second⟩ | ⟨first, second⟩ | ⟨first, second, third⟩ |
      ⟨first, second, third, fourth⟩)
  · exact realization.constant_eq
  · exact realization.H_eq first second
  · exact realization.DD_eq first second
  · exact realization.Dz_eq first second third
  · exact realization.pi2_eq first second third fourth

/-- **The pulse matrix pulls the stored features back exactly.**  For every haplotype realization
of a stored state, the pulse matrix applied to the state is the corpus's `pulseState`, the
complete moment vector of the law after the haplotype-level pulse.  This is NOTE1's condition for
covering an instantaneous map, shown for an admixture pulse. -/
theorem lowOrderLDPulseTransform_mulVec_eq_pulseState {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : Fin D) :
    (lowOrderLDPulseTransform alpha source recipient).mulVec state =
      realization.pulseState alpha alpha_nonneg alpha_le_one source recipient := by
  funext coordinate
  calc (lowOrderLDPulseTransform alpha source recipient).mulVec state coordinate
      = (lowOrderLDPulseTransform alpha source recipient).mulVec
          (fun column ↦ realization.expectation fun outcome ↦
            lowOrderLDFeature D (realization.haplotype outcome) column) coordinate :=
        congrArg (fun vector ↦ (lowOrderLDPulseTransform alpha source recipient).mulVec vector
          coordinate) (realization_state_eq_expectation realization)
    _ = realization.expectation fun outcome ↦
          (lowOrderLDPulseTransform alpha source recipient).mulVec
            (lowOrderLDFeature D (realization.haplotype outcome)) coordinate :=
        mulVec_expectation _ _ _ _
    _ = realization.expectation fun outcome ↦ lowOrderLDFeature D
          (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome)
          coordinate := by
        congr 1
        funext outcome
        rw [lowOrderLDPulseTransform_mulVec, pulseMoment_lowOrderLDFeature]
    _ = realization.pulseState alpha alpha_nonneg alpha_le_one source recipient coordinate :=
        (haplotypeLowOrderLDState_eq_eval_lowOrderLDFeature _ _ _).symm

/-! ## Pulses preserve realizability -/

/-- **A pulse preserves haplotype realizability by the corpus's transformed witness.**  The pulsed
stored state is realized by the same probability law with every recipient haplotype vector
replaced by its mixture with the source's. -/
def pulseRealization {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient : Fin D) :
    LowOrderLDHaplotypeRealization
      ((lowOrderLDPulseTransform alpha source recipient).mulVec state) where
  sampleSpace := realization.sampleSpace
  expectation := realization.expectation
  haplotype := realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient
  constant_eq := congrFun (lowOrderLDPulseTransform_mulVec_eq_pulseState realization alpha
    alpha_nonneg alpha_le_one source recipient) none
  H_eq first second := congrFun (lowOrderLDPulseTransform_mulVec_eq_pulseState realization alpha
    alpha_nonneg alpha_le_one source recipient) (some (.H first second))
  DD_eq first second := congrFun (lowOrderLDPulseTransform_mulVec_eq_pulseState realization alpha
    alpha_nonneg alpha_le_one source recipient) (some (.DD first second))
  Dz_eq first second third := congrFun (lowOrderLDPulseTransform_mulVec_eq_pulseState realization
    alpha alpha_nonneg alpha_le_one source recipient) (some (.Dz first second third))
  pi2_eq first second third fourth := congrFun (lowOrderLDPulseTransform_mulVec_eq_pulseState
    realization alpha alpha_nonneg alpha_le_one source recipient)
    (some (.pi2 first second third fourth))

/-- An expectation passes through a slot average. -/
theorem expectation_slotAverage {Ω : Type*} {D : ℕ} (expectation : Foundations.ExpFunctional Ω)
    (alpha : ℝ) (source recipient deme : Fin D) (observable : Fin D → Ω → ℝ) :
    (expectation fun outcome ↦ slotAverage alpha source recipient deme fun a ↦ observable a outcome) =
      slotAverage alpha source recipient deme fun a ↦ expectation (observable a) := by
  by_cases hdeme : deme = recipient
  · have hform : (fun outcome ↦
        slotAverage alpha source recipient deme fun a ↦ observable a outcome) =
        alpha • observable source + (1 - alpha) • observable recipient := by
      funext outcome
      simp only [slotAverage, if_pos hdeme, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hform, expectation.add_eval, expectation.smul_eval, expectation.smul_eval]
    simp only [slotAverage, if_pos hdeme]
  · simp only [slotAverage, if_neg hdeme]

/-- The right-locus heterozygosity of the pulsed configuration expands by the same slot average
as the left-locus one. -/
theorem rightHeterozygosity_pulseHaplotype {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization state) (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) (source recipient first second : Fin D)
    (outcome : realization.sampleSpace) :
    twoLocusRightHeterozygosity
        (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome first)
        (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome
          second) =
      slotAverage alpha source recipient first fun a ↦
        slotAverage alpha source recipient second fun b ↦
          twoLocusRightHeterozygosity (realization.haplotype outcome a)
            (realization.haplotype outcome b) := by
  simp only [LowOrderLDHaplotypeRealization.pulseHaplotype, slotAverage]
  split_ifs <;>
    simp only [twoLocusRightHeterozygosity,
      TwoLocusHaplotypeFrequencies.mixture_rightFrequency] <;>
    ring

/-- On a locus-exchangeably realized state, the pulse matrix's heterozygosity row is also the
expected right-locus heterozygosity of the pulsed law. -/
theorem lowOrderLDPulseTransform_mulVec_rightHeterozygosity {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) (alpha : ℝ)
    (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1) (source recipient first second : Fin D) :
    (lowOrderLDPulseTransform alpha source recipient).mulVec state (some (.H first second)) =
      realization.expectation fun outcome ↦ twoLocusRightHeterozygosity
        (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome first)
        (realization.pulseHaplotype alpha alpha_nonneg alpha_le_one source recipient outcome
          second) := by
  rw [lowOrderLDPulseTransform_mulVec]
  have hentries : ∀ a b : Fin D, state (some (.H a b)) = realization.expectation fun outcome ↦
      twoLocusRightHeterozygosity (realization.haplotype outcome a)
        (realization.haplotype outcome b) :=
    realization.H_right_eq
  calc pulseMoment alpha source recipient state (some (.H first second))
      = slotAverage alpha source recipient first fun a ↦
          slotAverage alpha source recipient second fun b ↦
            realization.expectation fun outcome ↦ twoLocusRightHeterozygosity
              (realization.haplotype outcome a) (realization.haplotype outcome b) := by
        simp only [pulseMoment, hentries]
    _ = slotAverage alpha source recipient first fun a ↦
          realization.expectation fun outcome ↦ slotAverage alpha source recipient second fun b ↦
            twoLocusRightHeterozygosity (realization.haplotype outcome a)
              (realization.haplotype outcome b) :=
        congrArg (slotAverage alpha source recipient first) (funext fun a ↦
          (expectation_slotAverage realization.expectation alpha source recipient second
            fun b outcome ↦ twoLocusRightHeterozygosity (realization.haplotype outcome a)
              (realization.haplotype outcome b)).symm)
    _ = realization.expectation fun outcome ↦ slotAverage alpha source recipient first fun a ↦
          slotAverage alpha source recipient second fun b ↦
            twoLocusRightHeterozygosity (realization.haplotype outcome a)
              (realization.haplotype outcome b) :=
        (expectation_slotAverage realization.expectation alpha source recipient first
          fun a outcome ↦ slotAverage alpha source recipient second fun b ↦
            twoLocusRightHeterozygosity (realization.haplotype outcome a)
              (realization.haplotype outcome b)).symm
    _ = _ := by
        congr 1
        funext outcome
        exact (rightHeterozygosity_pulseHaplotype realization.toLowOrderLDHaplotypeRealization
          alpha alpha_nonneg alpha_le_one source recipient first second outcome).symm

/-- **A pulse preserves locus-exchangeable realizability.**  The stored realization is the
transformed witness, and the equality of expected left and right heterozygosities is pulled back
through the same slot averages. -/
def locusExchangeablePulse {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) (alpha : ℝ)
    (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1) (source recipient : Fin D) :
    LocusExchangeableLowOrderLDHaplotypeRealization
      ((lowOrderLDPulseTransform alpha source recipient).mulVec state) where
  toLowOrderLDHaplotypeRealization := pulseRealization realization.toLowOrderLDHaplotypeRealization
    alpha alpha_nonneg alpha_le_one source recipient
  H_right_eq first second := lowOrderLDPulseTransform_mulVec_rightHeterozygosity realization alpha
    alpha_nonneg alpha_le_one source recipient first second

/-! ## Histories of rate epochs, splits and pulses -/

/-- One event of a compiled demographic history: a rate epoch or a split, as in
`RateHistoryEvent`, or an admixture pulse of fraction `alpha` from `source` into `recipient`. -/
inductive PulseHistoryEvent (D : ℕ) where
  /-- A rate epoch or a split. -/
  | rate (event : RateHistoryEvent D)
  /-- An admixture pulse of fraction `alpha` from `source` into `recipient`. -/
  | pulse (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) (alpha_le_one : alpha ≤ 1)
      (source recipient : Fin D)

/-- The corpus instruction an event compiles to: the rate event's instruction, or the pulse
matrix as an instantaneous map. -/
def PulseHistoryEvent.instruction {D : ℕ} : PulseHistoryEvent D → LowOrderLDInstruction D
  | .rate event => event.instruction
  | .pulse alpha _ _ source recipient =>
      .instantaneous (lowOrderLDPulseTransform alpha source recipient)

/-- A pulse of fraction zero from a deme into itself, an event built from a deme alone. -/
def PulseHistoryEvent.identityPulse {D : ℕ} (deme : Fin D) : PulseHistoryEvent D :=
  .pulse 0 le_rfl zero_le_one deme deme

/-- **Every event preserves locus-exchangeable realizability.**  A rate epoch or a split is the
corpus's one-event theorem, and a pulse is the transformed witness. -/
theorem PulseHistoryEvent.preserves_locusExchangeable_realization {D : ℕ}
    (event : PulseHistoryEvent D) {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization (event.instruction.apply state)) := by
  cases event with
  | rate event => exact propagate_preserves_locusExchangeable_realization [event] realization
  | pulse alpha alpha_nonneg alpha_le_one source recipient =>
      exact ⟨locusExchangeablePulse realization alpha alpha_nonneg alpha_le_one source recipient⟩

/-- **NOTE1 Theorem 2 for histories with pulses, with no hypotheses.**  Composing any finite list
of rate epochs, physically realized splits and admixture pulses carries a locus-exchangeably
realizable stored state to a locus-exchangeably realizable one. -/
theorem propagate_pulseHistory_preserves_locusExchangeable_realization {D : ℕ}
    (events : List (PulseHistoryEvent D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (propagateLowOrderLDInstructions (events.map PulseHistoryEvent.instruction) initial)) := by
  induction events generalizing initial with
  | nil => exact ⟨realization⟩
  | cons head rest ih =>
      obtain ⟨propagated⟩ := head.preserves_locusExchangeable_realization realization
      exact ih propagated

/-- The present state of a history compiled from rate epochs, splits and pulses is
locus-exchangeably realizable whenever its initial state is. -/
theorem pulseHistory_present_locusExchangeable_realization {D : ℕ}
    (history : LowOrderLDHistory D) (events : List (PulseHistoryEvent D))
    (hcompiled : history.instructions = events.map PulseHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization history.present) := by
  rw [LowOrderLDHistory.present, hcompiled]
  exact propagate_pulseHistory_preserves_locusExchangeable_realization events realization

/-- A history with pulses places its present state in the corpus realization body. -/
theorem pulseHistory_present_mem_realizationBody {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (PulseHistoryEvent D))
    (hcompiled : history.instructions = events.map PulseHistoryEvent.instruction)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    history.present ∈ realizationBody (lowOrderLDFeature D) := by
  obtain ⟨propagated⟩ :=
    pulseHistory_present_locusExchangeable_realization history events hcompiled realization
  exact KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    propagated.toLowOrderLDHaplotypeRealization

/-! ## NOTE1 Corollary 2.1 for histories with pulses -/

/-- The propagated `DD` block is positive semidefinite after every history of rate epochs, splits
and pulses. -/
theorem pulseHistory_present_dd_quadraticForm_nonneg {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (PulseHistoryEvent D))
    (hcompiled : history.instructions = events.map PulseHistoryEvent.instruction)
    (weight : Fin D → ℝ)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    0 ≤ ∑ first, ∑ second,
      weight first * history.present (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ :=
    pulseHistory_present_locusExchangeable_realization history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) after every history with pulses: the propagated cross-deme `DD` entries obey
Cauchy--Schwarz against the propagated diagonals, with no strict positivity assumed. -/
theorem pulseHistory_present_dd_cauchySchwarz {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (PulseHistoryEvent D))
    (hcompiled : history.instructions = events.map PulseHistoryEvent.instruction)
    (first second : Fin D)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    history.present (some (.DD first second)) ^ 2 ≤
      history.present (some (.DD first first)) *
        history.present (some (.DD second second)) := by
  obtain ⟨propagated⟩ :=
    pulseHistory_present_locusExchangeable_realization history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The propagated within-deme `DD` diagonal is nonnegative after every history with pulses. -/
theorem pulseHistory_present_dd_diagonal_nonneg {D : ℕ} (history : LowOrderLDHistory D)
    (events : List (PulseHistoryEvent D))
    (hcompiled : history.instructions = events.map PulseHistoryEvent.instruction)
    (deme : Fin D)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization history.initial) :
    0 ≤ history.present (some (.DD deme deme)) := by
  obtain ⟨propagated⟩ :=
    pulseHistory_present_locusExchangeable_realization history events hcompiled realization
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg deme

/-- **NOTE1 Corollary 2.1 at the `EndToEndScoreLaw` endpoint, for histories with pulses.**  For a
separation-indexed family of histories compiled from rate epochs, splits and pulses and started
from locus-exchangeably realizable states, the normalized linkage-pair domain holds at every
pair of demes whose within-deme `DD` entries are nonzero. -/
theorem pulseHistory_LDPairDomain {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (eventsAt : MarkerSeparationBp → List (PulseHistoryEvent D))
    (hcompiled : ∀ separation,
      (historyAt separation).instructions =
        (eventsAt separation).map PulseHistoryEvent.instruction)
    (separation : MarkerSeparationBp)
    (realization :
      LocusExchangeableLowOrderLDHaplotypeRealization (historyAt separation).initial)
    (first second : Fin D)
    (first_ne : (historyAt separation).present (some (.DD first first)) ≠ 0)
    (second_ne : (historyAt separation).present (some (.DD second second)) ≠ 0) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain
      separation first second := by
  obtain ⟨propagated⟩ := pulseHistory_present_locusExchangeable_realization
    (historyAt separation) (eventsAt separation) (hcompiled separation) realization
  have hwitness := propagated.toLowOrderLDHaplotypeRealization.toDDDRealization
  exact hwitness.toLDPairDomain historyAt separation first second
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg first) (Ne.symm first_ne))
    (lt_of_le_of_ne (hwitness.dd_diagonal_nonneg second) (Ne.symm second_ne))

end

end Descent.Portability.PulseHistoryRealization
