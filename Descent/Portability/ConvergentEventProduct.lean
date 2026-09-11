/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.InterleavedHistoryRealization

assert_below Descent.Decision Descent.Program

/-!
# Realizability at the limit of a convergent event product

NOTE1 section 2.4 interleaves finitely many instantaneous demographic events with rate histories
and adds a caution about countably many: an accumulation of events needs a separately specified
convergent event product, and merely calling a history arbitrary does not define a process with
infinite uncompensated activity.  This module takes the convergence as that separate
specification, stated as an explicit hypothesis, and proves that whatever the finite products
converge to is again locus-exchangeably realizable.

`InterleavedHistoryRealization.propagateInterleaved_preserves_locusExchangeable_realization`
carries a realizable stored state through every finite list of interleaved segments: rate
histories with continuous generators, rate histories with integrable rate coordinates, splits
and admixture pulses.  `IntegrableRateHistoryRealization.isClosed_exchangeableStates` says the
locus-exchangeably realizable stored states form a closed set.  So a limit of realizable states
is realizable.  The limit is taken in three forms.
`convergentHistory_limit_locusExchangeable_realization` asks that the propagated states converge
at one initial state; `convergentOperator_locusExchangeable_realization` that the finite products,
as maps of the stored state, converge pointwise, and reads the limit at every realizable initial
state; and `convergentMatrix_locusExchangeable_realization` that their matrices converge.
`InterleavedSegment.matrix` is the matrix of one segment and `productMatrix` the ordered product
of a list, with `productMatrix_mulVec` identifying it with `propagateInterleaved`, so the matrix
form needs no representation premise.  The positive-semidefinite `DD` block, Cauchy--Schwarz and
the nonnegative diagonal hold at the limit state.

Scope.  Nothing here constructs a process with countably many events or proves that any
particular sequence of finite histories converges: the convergence is the hypothesis NOTE1 asks
for, and each theorem says what follows from it.

## Empirical status

None.  The bodies here compose linear maps along finite lists and pass to a limit inside a closed
set of realizable states, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConvergentEventProduct

open Coalescent
open Filter Topology
open Descent.Portability.IntegrableRateHistoryRealization
open Descent.Portability.PulseHistoryRealization
open Descent.Portability.InterleavedHistoryRealization

noncomputable section

/-! ## The matrix of a finite event product -/

/-- The matrix one segment applies to the stored low-order state: the propagator of a rate
history at its horizon, the split transform, or the pulse matrix. -/
def InterleavedSegment.matrix {D : ℕ} :
    InterleavedSegment D →
      Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ
  | .segment (.evolve rates horizon _ _) => rateHistoryPropagator rates horizon
  | .segment (.split parent child) => lowOrderLDSplitTransform parent child
  | .integrable rates horizon horizon_nonneg hintegrable =>
      integrablePropagator rates horizon_nonneg hintegrable horizon
  | .pulse alpha _ _ source recipient => lowOrderLDPulseTransform alpha source recipient

/-- One segment applies its matrix. -/
theorem InterleavedSegment.apply_eq_mulVec {D : ℕ} (segment : InterleavedSegment D)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    segment.apply state = segment.matrix.mulVec state := by
  cases segment with
  | segment event => cases event <;> rfl
  | integrable rates horizon horizon_nonneg hintegrable => rfl
  | pulse alpha alpha_nonneg alpha_le_one source recipient => rfl

/-- The ordered product of the segment matrices of a finite list: the first segment acts first,
so its matrix is the rightmost factor. -/
def productMatrix {D : ℕ} (segments : List (InterleavedSegment D)) :
    Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ :=
  segments.foldl (fun product segment ↦ segment.matrix * product) 1

/-- Folding the segment matrices onto an accumulated product applies the segments after it. -/
theorem foldl_matrix_mulVec {D : ℕ} (segments : List (InterleavedSegment D))
    (accumulated : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ)
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (segments.foldl (fun product segment ↦ segment.matrix * product) accumulated).mulVec state =
      propagateInterleaved segments (accumulated.mulVec state) := by
  induction segments generalizing accumulated with
  | nil => rfl
  | cons head rest ih =>
      rw [List.foldl_cons, ih, ← Matrix.mulVec_mulVec, ← InterleavedSegment.apply_eq_mulVec]
      rfl

/-- **The product matrix of a finite list is its event product.**  Applying it to a stored state
is propagating the state through the segments in order. -/
theorem productMatrix_mulVec {D : ℕ} (segments : List (InterleavedSegment D))
    (state : AffineLowOrderLDCoordinate D → ℝ) :
    (productMatrix segments).mulVec state = propagateInterleaved segments state := by
  rw [productMatrix, foldl_matrix_mulVec, Matrix.one_mulVec]

/-! ## The limit of a convergent event product -/

/-- **A convergent sequence of finite event products ends in a realizable state.**  For a
sequence of finite interleaved histories started from one locus-exchangeably realizable stored
state, if the propagated states converge, the limit state is locus-exchangeably realizable.

Assumes: `hconverges`, the convergence of the propagated states.  This is the separately
specified convergent event product that NOTE1 section 2.4 asks for; no particular sequence of
histories is shown to converge here. -/
theorem convergentHistory_limit_locusExchangeable_realization {D : ℕ}
    (histories : ℕ → List (InterleavedSegment D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial)
    {limit : AffineLowOrderLDCoordinate D → ℝ}
    (hconverges : Tendsto (fun index ↦ propagateInterleaved (histories index) initial) atTop
      (𝓝 limit)) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization limit) := by
  refine (mem_exchangeableStates_iff limit).mp ?_
  refine (isClosed_exchangeableStates D).mem_of_tendsto hconverges (Eventually.of_forall ?_)
  intro index
  exact (mem_exchangeableStates_iff _).mpr
    (propagateInterleaved_preserves_locusExchangeable_realization (histories index) realization)

/-- **A pointwise convergent sequence of finite event products preserves realizability.**  If
the finite products, read as maps of the stored state, converge pointwise to a map, that map
carries every locus-exchangeably realizable stored state to a locus-exchangeably realizable one.

Assumes: `hconverges`, the pointwise convergence of the event products. -/
theorem convergentOperator_locusExchangeable_realization {D : ℕ}
    (histories : ℕ → List (InterleavedSegment D))
    {product : (AffineLowOrderLDCoordinate D → ℝ) → AffineLowOrderLDCoordinate D → ℝ}
    (hconverges : Tendsto (fun index ↦ propagateInterleaved (histories index)) atTop
      (𝓝 product))
    {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization (product initial)) :=
  convergentHistory_limit_locusExchangeable_realization histories realization
    (tendsto_pi_nhds.mp hconverges initial)

/-- **A convergent sequence of finite product matrices preserves realizability.**  If the product
matrices of a sequence of finite interleaved histories converge, the limit matrix carries every
locus-exchangeably realizable stored state to a locus-exchangeably realizable one.

Assumes: `hconverges`, the convergence of the product matrices. -/
theorem convergentMatrix_locusExchangeable_realization {D : ℕ}
    (histories : ℕ → List (InterleavedSegment D))
    {limit : Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ}
    (hconverges : Tendsto (fun index ↦ productMatrix (histories index)) atTop (𝓝 limit))
    {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization (limit.mulVec initial)) := by
  have hcontinuous : Continuous fun matrix :
      Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ ↦
        matrix.mulVec initial :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have hstates := (hcontinuous.tendsto limit).comp hconverges
  refine convergentHistory_limit_locusExchangeable_realization histories realization ?_
  convert hstates using 1
  funext index
  exact (productMatrix_mulVec (histories index) initial).symm

/-! ## NOTE1 Corollary 2.1 at the limit -/

/-- The `DD` block of the limit state of a convergent event product is positive semidefinite.

Assumes: `hconverges`, the convergence of the propagated states. -/
theorem convergentHistory_limit_dd_quadraticForm_nonneg {D : ℕ}
    (histories : ℕ → List (InterleavedSegment D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial)
    {limit : AffineLowOrderLDCoordinate D → ℝ}
    (hconverges : Tendsto (fun index ↦ propagateInterleaved (histories index) initial) atTop
      (𝓝 limit))
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second, weight first * limit (some (.DD first second)) * weight second := by
  obtain ⟨propagated⟩ :=
    convergentHistory_limit_locusExchangeable_realization histories realization hconverges
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_quadraticForm_nonneg
    weight

/-- NOTE1 (13) at the limit of a convergent event product: the cross-deme `DD` entries obey
Cauchy--Schwarz against the diagonals, with no strict positivity assumed.

Assumes: `hconverges`, the convergence of the propagated states. -/
theorem convergentHistory_limit_dd_cauchySchwarz {D : ℕ}
    (histories : ℕ → List (InterleavedSegment D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial)
    {limit : AffineLowOrderLDCoordinate D → ℝ}
    (hconverges : Tendsto (fun index ↦ propagateInterleaved (histories index) initial) atTop
      (𝓝 limit))
    (first second : Fin D) :
    limit (some (.DD first second)) ^ 2 ≤
      limit (some (.DD first first)) * limit (some (.DD second second)) := by
  obtain ⟨propagated⟩ :=
    convergentHistory_limit_locusExchangeable_realization histories realization hconverges
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_cauchySchwarz first
    second

/-- The within-deme `DD` entries of the limit state of a convergent event product are
nonnegative.

Assumes: `hconverges`, the convergence of the propagated states. -/
theorem convergentHistory_limit_dd_diagonal_nonneg {D : ℕ}
    (histories : ℕ → List (InterleavedSegment D)) {initial : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization initial)
    {limit : AffineLowOrderLDCoordinate D → ℝ}
    (hconverges : Tendsto (fun index ↦ propagateInterleaved (histories index) initial) atTop
      (𝓝 limit))
    (deme : Fin D) :
    0 ≤ limit (some (.DD deme deme)) := by
  obtain ⟨propagated⟩ :=
    convergentHistory_limit_locusExchangeable_realization histories realization hconverges
  exact propagated.toLowOrderLDHaplotypeRealization.toDDDRealization.dd_diagonal_nonneg deme

end

end Descent.Portability.ConvergentEventProduct
