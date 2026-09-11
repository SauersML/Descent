/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.InterleavedHistoryRealization

/-! Axiom audit of realizability under interleaved integrable rate histories, splits and
pulses. -/

open Descent.Portability.InterleavedHistoryRealization

#print axioms integrablePropagator
#print axioms continuous_integrablePropagator
#print axioms integrablePropagator_eq_integral
#print axioms integrablePropagator_unique
#print axioms integrablePropagator_preserves_locusExchangeable_realization
#print axioms InterleavedSegment.apply
#print axioms identityPulseSegment
#print axioms InterleavedSegment.apply_segment
#print axioms InterleavedSegment.preserves_locusExchangeable_realization
#print axioms propagateInterleaved
#print axioms propagateInterleaved_preserves_locusExchangeable_realization
#print axioms propagateInterleaved_dd_quadraticForm_nonneg
