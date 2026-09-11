/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EnlargedLowOrderLDGenerator
import Descent.Portability.KernelRealizationPreservation

assert_below Descent.Decision Descent.Program

/-!
# Low-order realizability under demographic epochs

This is NOTE1 Theorem 2 and Corollary 2.1 in the corpus's own vocabulary.  The corpus states
at `Descent/Coalescent/TwoLocusHistory.lean` that preservation of
`LocusExchangeableLowOrderLDHaplotypeRealization` by the moment semigroup remains to be
proved, and `Descent/Portability/EndToEndScoreLaw.lean` asks for a realizability corollary
showing that the propagated `DD` block stays positive semidefinite.  Both are proved here,
the first in the stronger form NOTE1 asks for: the propagated vector is again the vector of
all its defining polynomials under one common probability law on the haplotype simplex, with
the left and right expected heterozygosities still identified.

The argument is the composition of three finished pieces.  From
`Descent.Portability.EnlargedLowOrderLDGenerator`, a locus-exchangeable realization makes the
embedded state the expectation of the enlarged feature map, and the enlarged propagator
intertwines with the embedding, `exp(t A~) E = E exp(t A)`, which is NOTE1's invariance of the
subspace `E H^L = E H^R` of equation (12).  From `Descent.Portability.RealizationBody`, a
positive normalized expectation functional lands inside a closed realization body by
separation, and a point of the body carries a finitely supported law.  From
`Descent.Portability.KernelRealizationPreservation`, NOTE1 Theorem 1: a generator with a
microscopic approximation by genuine probability kernels carries the body into itself.

Two hypotheses are carried rather than discharged, and both are named in every statement that
uses them.  The first is `IsClosed (realizationBody enlargedLowOrderLDFeature)`; the corpus
gives `TwoLocusHaplotypeFrequencies` no topology, so compactness of the body is not available
yet.  The second is the `MicroscopicApproximation` of the enlarged generator, NOTE1 equation
(11), which is the business of the microscopic-kernel module; here it is taken as data the
caller holds, never as an existential.  Nothing else is assumed: in particular no
Wright--Fisher semigroup, no closure approximation and no fitted retention coefficient.

Splits need neither hypothesis.  `locusExchangeableSplit` relabels the very same haplotype
random variables, so it preserves the right-locus identification along with everything else,
exactly as the corpus's `LowOrderLDHaplotypeRealization.split` preserves the stored
coordinates.  What is NOT proved here is the time-varying case of NOTE1 section 2.4 beyond
piecewise-constant composition, and the full-history statement over
`propagateLowOrderLDInstructions`, whose evolve steps need the approximation hypothesis at
every epoch.

## Empirical status

None.  The bodies here are algebra and point-set topology: a convex hull, a matrix
exponential, and the expectation of polynomial coordinates under one probability law.  No
measurement can bear on whether a convex set is mapped into itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TwoLocusRealizabilityPreservation

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody
open Descent.Portability.EnlargedLowOrderLDGenerator

noncomputable section

/-! ## The embedded state and the enlarged body -/

/-- A locus-exchangeable haplotype realization of a stored state places its embedding inside
the enlarged realization body.  The realization's expectation functional is an arbitrary
positive normalized functional, so this is the separation half of NOTE1 section 2.1 rather
than a finite-support argument.

Assumes: the enlarged body is closed. -/
theorem embed_mem_enlargedRealizationBody {D : ℕ}
    (hclosed : IsClosed (realizationBody (enlargedLowOrderLDFeature (D := D))))
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    embedLowOrderLDState state ∈ realizationBody (enlargedLowOrderLDFeature (D := D)) := by
  have hfunction : embedLowOrderLDState state =
      fun coordinate ↦ realization.expectation (fun outcome ↦
        enlargedLowOrderLDFeature (realization.haplotype outcome) coordinate) := by
    funext coordinate
    exact embed_eq_enlargedFeature_expectation realization coordinate
  rw [hfunction]
  exact expFunctional_feature_mem _ hclosed realization.expectation realization.haplotype

/-- Conversely, an embedded state that lies in the enlarged body is locus-exchangeably
realizable: the finitely supported law of `mem_realizationBody_iff`, read through
`weightedExp`, identifies the stored and right-locus heterozygosity coordinates because the
embedding put the same number in both. -/
theorem nonempty_locusExchangeableRealization_of_embed_mem {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (hmember : embedLowOrderLDState state ∈
      realizationBody (enlargedLowOrderLDFeature (D := D))) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization state) := by
  obtain ⟨Outcome, hOutcome, mass, point, hmass, hsum, hfeature⟩ :=
    (mem_realizationBody_iff (enlargedLowOrderLDFeature (D := D))
      (embedLowOrderLDState state)).mp hmember
  refine ⟨locusExchangeableRealizationOfEnlargedFeature (weightedExp mass hmass hsum) point
    state ?_⟩
  intro coordinate
  rw [← hfeature, featureVector_apply, weightedExp_apply]

/-! ## NOTE1 Theorem 2 -/

/-- **Every epoch of the arbitrary-deme low-order system preserves locus-exchangeable
haplotype realizability.**  This is NOTE1 Theorem 2 for one epoch: the propagated stored
vector is again the vector of all its defining polynomials under one common probability law
on the haplotype simplex, with the expected left and right heterozygosities still equal.  The
enlarged generator is what is propagated; the intertwining returns the stored block.

Assumes: the enlarged body is closed, and the enlarged generator has a microscopic
approximation by genuine finite mixture kernels, supplied as data. -/
theorem epoch_preserves_locusExchangeable_realization {D : ℕ} {Branch : Type*}
    [Fintype Branch]
    (hclosed : IsClosed (realizationBody (enlargedLowOrderLDFeature (D := D))))
    (rates : ManyDemeLDRates D)
    (approximation : MicroscopicApproximation (B := Branch)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) := by
  refine nonempty_locusExchangeableRealization_of_embed_mem ?_
  have hpropagator : (rates.epoch duration hduration).propagator =
      matrixExponential (augmentedLowOrderLDGenerator rates) duration := rfl
  rw [hpropagator, ← enlargedPropagator_mulVec_embed]
  exact KernelRealizationPreservation.exp_mulVec_mem_realizationBody _ _ approximation hclosed
    duration hduration _ (embed_mem_enlargedRealizationBody hclosed realization)

/-- A physically realized split preserves locus-exchangeable realizability with no
approximation and no limit: the child deme's haplotype random variable is replaced by the
parent's, so every coordinate, including the right-locus heterozygosity, is read off the same
probability law. -/
def locusExchangeableSplit {D : ℕ} {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (parent child : Fin D) :
    LocusExchangeableLowOrderLDHaplotypeRealization
      ((lowOrderLDSplitTransform parent child).mulVec state) where
  toLowOrderLDHaplotypeRealization :=
    realization.toLowOrderLDHaplotypeRealization.split parent child
  H_right_eq := by
    intro first second
    have hvalue : (lowOrderLDSplitTransform parent child).mulVec state
        (some (.H first second)) =
        state (some (.H (if first = child then parent else first)
          (if second = child then parent else second))) := by
      rw [lowOrderLDSplitTransform_mulVec]
      rfl
    rw [hvalue]
    exact realization.H_right_eq _ _

/-! ## NOTE1 Corollary 2.1 -/

/-- The propagated `DD` block carries a common Gram witness after every epoch, which is what
turns the low-order vector into an object with positive-semidefinite structure rather than a
list of numbers satisfying an assumed inequality. -/
theorem nonempty_propagatedDDRealization {D : ℕ} {Branch : Type*} [Fintype Branch]
    (hclosed : IsClosed (realizationBody (enlargedLowOrderLDFeature (D := D))))
    (rates : ManyDemeLDRates D)
    (approximation : MicroscopicApproximation (B := Branch)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LowOrderLDDDRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) := by
  obtain ⟨propagated⟩ := epoch_preserves_locusExchangeable_realization hclosed rates
    approximation duration hduration realization
  exact ⟨propagated.toLowOrderLDHaplotypeRealization.toDDDRealization⟩

/-- **NOTE1 Corollary 2.1, the endpoint obligation of `EndToEndScoreLaw`.**  The propagated
`DD` block is positive semidefinite: every finite linear combination of deme-specific linkage
disequilibria has nonnegative second moment under the common propagated law.  This is derived
from the realization, not assumed as an inequality on the numbers. -/
theorem propagated_dd_quadraticForm_nonneg {D : ℕ} {Branch : Type*} [Fintype Branch]
    (hclosed : IsClosed (realizationBody (enlargedLowOrderLDFeature (D := D))))
    (rates : ManyDemeLDRates D)
    (approximation : MicroscopicApproximation (B := Branch)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second, weight first *
      ((rates.epoch duration hduration).propagator.mulVec state (some (.DD first second))) *
        weight second := by
  obtain ⟨propagated⟩ := nonempty_propagatedDDRealization hclosed rates approximation duration
    hduration realization
  exact propagated.dd_quadraticForm_nonneg weight

/-- NOTE1 (13) after an epoch: the propagated cross-deme `DD` entries obey Cauchy--Schwarz
against the propagated diagonals, without any strict positivity assumption. -/
theorem propagated_dd_cauchySchwarz {D : ℕ} {Branch : Type*} [Fintype Branch]
    (hclosed : IsClosed (realizationBody (enlargedLowOrderLDFeature (D := D))))
    (rates : ManyDemeLDRates D)
    (approximation : MicroscopicApproximation (B := Branch)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (first second : Fin D) :
    ((rates.epoch duration hduration).propagator.mulVec state (some (.DD first second))) ^ 2 ≤
      ((rates.epoch duration hduration).propagator.mulVec state (some (.DD first first))) *
        ((rates.epoch duration hduration).propagator.mulVec state
          (some (.DD second second))) := by
  obtain ⟨propagated⟩ := nonempty_propagatedDDRealization hclosed rates approximation duration
    hduration realization
  exact propagated.dd_cauchySchwarz first second

/-- The propagated within-deme `DD` diagonal is a second moment and therefore nonnegative,
which is the sign condition the normalized portability domain needs before its positivity
hypothesis can even be stated. -/
theorem propagated_dd_diagonal_nonneg {D : ℕ} {Branch : Type*} [Fintype Branch]
    (hclosed : IsClosed (realizationBody (enlargedLowOrderLDFeature (D := D))))
    (rates : ManyDemeLDRates D)
    (approximation : MicroscopicApproximation (B := Branch)
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state)
    (deme : Fin D) :
    0 ≤ (rates.epoch duration hduration).propagator.mulVec state (some (.DD deme deme)) := by
  obtain ⟨propagated⟩ := nonempty_propagatedDDRealization hclosed rates approximation duration
    hduration realization
  exact propagated.dd_diagonal_nonneg deme

/-- The normalized linkage-pair domain of the composed history is constructed from the
propagated Gram witness, so the `EndToEndScoreLaw` contract's `LDPairDomain` is reached
whenever the two within-deme diagonals are positive.  The Cauchy--Schwarz field comes from
the witness rather than from an independently supplied pairwise inequality. -/
def propagatedLDPairDomain {D : ℕ}
    (historyAt : MarkerSeparationBp → LowOrderLDHistory D)
    (separation : MarkerSeparationBp) (first second : Fin D)
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization
      (historyAt separation).present)
    (first_pos : 0 < (historyAt separation).present (some (.DD first first)))
    (second_pos : 0 < (historyAt separation).present (some (.DD second second))) :
    (LowOrderLDHistory.toDemographicTwoLocusMoments historyAt).LDPairDomain
      separation first second :=
  LowOrderLDHaplotypeRealization.toLDPairDomain historyAt separation first second
    realization.toLowOrderLDHaplotypeRealization first_pos second_pos

end

end Descent.Portability.TwoLocusRealizabilityPreservation
