/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EnlargedLowOrderLDGenerator
import Descent.Portability.KernelRealizationPreservation
import Descent.Portability.TwoLocusRealizabilityPreservation

assert_below Descent.Decision Descent.Program

/-!
# Closedness of the enlarged realization body

NOTE1 §2.1 asserts that the realization body of a continuous feature map on a compact space is
compact and convex, and the limit arguments of NOTE1 Theorems 1-3 need that body to be closed.
For the stored low-order coordinates this is
`RealizationBody.isClosed_realizationBody_lowOrderLDFeature`. This module proves the same for
the enlarged observable family of NOTE1 (6), which carries the right-locus heterozygosities
`H^R_ij` beside the stored coordinates, and so discharges the closedness hypothesis that every
enlarged invariance statement of `TwoLocusRealizabilityPreservation` carries.

The corpus haplotype-frequency structure has no topology, so the body is reached through a
parametrisation. `simplexOfState` lists a multi-deme haplotype-frequency state as a point of
the compact multi-deme simplex of `RealizationBody`, and `demeFrequencies_surjective` says
every state arises this way. `isCompact_realizationBody_of_surjective` is the general
principle: a feature map that becomes continuous after composing with a surjection from a
compact space has a compact body, because the composite has the same range and hence the same
convex hull. `continuous_enlargedLowOrderLDFeature_comp` checks the continuity coordinate by
coordinate: the stored coordinates are the corpus polynomial coordinates already shown
continuous by `continuous_simplexLowOrderLDFeature`, and the added coordinate
`H^R_ij = q_i (1 - q_j) + q_j (1 - q_i)` is a polynomial in the right-locus allele
frequencies, `continuous_rightHeterozygosity`.

`isCompact_realizationBody_enlargedLowOrderLDFeature` and
`isClosed_realizationBody_enlargedLowOrderLDFeature` are stated for the enlarged feature map
of `KernelRealizationPreservation`. `isCompact_enlargedRealizationBody` and
`isClosed_enlargedRealizationBody` are stated for the enlarged feature map of
`EnlargedLowOrderLDGenerator`, which the microscopic kernel and
`TwoLocusRealizabilityPreservation` use; the two maps agree at every coordinate by evaluation,
which the proof checks before transferring compactness.

The corollaries carry no closedness hypothesis.
`exp_mulVec_mem_enlargedRealizationBody_of_approx` is NOTE1 Theorem 1 for the enlarged family:
any generator on the enlarged coordinates with a microscopic approximation carries the
enlarged body into itself at every nonnegative time. `enlargedPropagator_mulVec_mem_of_approx`
is one epoch of the enlarged generator `enlargedLowOrderLDGenerator rates` of NOTE1 §2.2.
`embed_mem_enlargedRealizationBody_of_realization` places the embedding of every
locus-exchangeably realizable stored state inside the enlarged body, and
`epoch_preserves_locusExchangeable_realization_of_approx` is NOTE1 Theorem 2 for one epoch
with the microscopic approximation as its only hypothesis.

What is NOT proved here: the microscopic approximation of the enlarged generator itself,
NOTE1 (11). The epoch statements are exactly as strong as the approximation they are given.

## Empirical status

None. The bodies here are point-set topology: the convex hull of the image of a compact product
of simplices under a polynomial map. No measurement can bear on whether such a set is closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EnlargedBodyClosedness

open Descent.Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody
open Descent.Portability.EnlargedLowOrderLDGenerator
  (AffineEnlargedCoordinate enlargedLowOrderLDGenerator embedLowOrderLDState)

noncomputable section

/-! ## A surjective compact parametrisation of the haplotype states -/

/-- The four haplotype frequencies of one deme, listed in the order `AB, Ab, aB, ab`, form a
point of the standard three-simplex. -/
theorem frequencies_mem_stdSimplex (frequencies : TwoLocusHaplotypeFrequencies) :
    ![frequencies.AB, frequencies.Ab, frequencies.aB, frequencies.ab]
      ∈ stdSimplex ℝ (Fin 4) := by
  refine ⟨fun k ↦ ?_, ?_⟩
  · fin_cases k
    exacts [frequencies.AB_nonneg, frequencies.Ab_nonneg, frequencies.aB_nonneg,
      frequencies.ab_nonneg]
  · rw [Fin.sum_univ_four]
    simpa using frequencies.total_eq_one

/-- The point of the compact multi-deme simplex that lists a multi-deme haplotype-frequency
state, one standard three-simplex coordinate block per deme. -/
def simplexOfState (D : ℕ) (state : Fin D → TwoLocusHaplotypeFrequencies) :
    multiDemeSimplex D :=
  ⟨fun d ↦ ![(state d).AB, (state d).Ab, (state d).aB, (state d).ab],
    fun d _ ↦ frequencies_mem_stdSimplex (state d)⟩

/-- Reading the haplotype frequencies back off `simplexOfState` returns the state it lists. -/
theorem demeFrequencies_simplexOfState (D : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies) :
    demeFrequencies D (simplexOfState D state) = state := rfl

/-- The compact multi-deme simplex parametrises every multi-deme haplotype-frequency state. -/
theorem demeFrequencies_surjective (D : ℕ) : Function.Surjective (demeFrequencies D) :=
  fun state ↦ ⟨simplexOfState D state, demeFrequencies_simplexOfState D state⟩

/-- **A surjective compact parametrisation gives a compact body.** If a feature map becomes
continuous after composing with a surjection from a compact space, its realization body is
compact: the composite has the same range, hence the same convex hull, and the body of a
continuous map on a compact space is compact by `isCompact_realizationBody`. -/
theorem isCompact_realizationBody_of_surjective {X Y ι : Type*} [Fintype ι]
    [TopologicalSpace Y] [CompactSpace Y] (φ : X → ι → ℝ) (g : Y → X)
    (hg : Function.Surjective g) (hcont : Continuous (φ ∘ g)) :
    IsCompact (realizationBody φ) := by
  have hbody : realizationBody φ = realizationBody (φ ∘ g) := by
    rw [realizationBody, realizationBody, hg.range_comp φ]
  rw [hbody]
  exact isCompact_realizationBody (φ ∘ g) hcont

/-! ## Compactness and closedness of the enlarged body -/

/-- The enlarged feature map of NOTE1 (6), read off the compact multi-deme simplex, is
continuous. The affine coordinate is constant, the stored coordinates are the corpus
polynomial coordinates, and the right-locus heterozygosity `H^R_ij` is a polynomial in the
right-locus allele frequencies. -/
theorem continuous_enlargedLowOrderLDFeature_comp (D : ℕ) :
    Continuous (KernelRealizationPreservation.enlargedLowOrderLDFeature D ∘
      demeFrequencies D) := by
  refine continuous_pi fun coordinate ↦ ?_
  match coordinate with
  | none => exact (continuous_const : Continuous fun _ : multiDemeSimplex D ↦ (1 : ℝ))
  | some (Sum.inl stored) =>
    exact continuous_pi_iff.mp (continuous_simplexLowOrderLDFeature D) (some stored)
  | some (Sum.inr (first, second)) =>
    exact continuous_rightHeterozygosity D first second

/-- **NOTE1 §2.1 for the enlarged coordinates.** The realization body of the enlarged feature
map of NOTE1 (6) is compact: it is the body of a continuous map on the compact multi-deme
simplex. -/
theorem isCompact_realizationBody_enlargedLowOrderLDFeature (D : ℕ) :
    IsCompact (realizationBody (KernelRealizationPreservation.enlargedLowOrderLDFeature D)) := by
  haveI : CompactSpace (multiDemeSimplex D) :=
    isCompact_iff_compactSpace.mp (isCompact_multiDemeSimplex D)
  exact isCompact_realizationBody_of_surjective _ (demeFrequencies D)
    (demeFrequencies_surjective D) (continuous_enlargedLowOrderLDFeature_comp D)

/-- The enlarged realization body is closed, which is the hypothesis every invariance theorem
about it needs. -/
theorem isClosed_realizationBody_enlargedLowOrderLDFeature (D : ℕ) :
    IsClosed (realizationBody (KernelRealizationPreservation.enlargedLowOrderLDFeature D)) :=
  (isCompact_realizationBody_enlargedLowOrderLDFeature D).isClosed

/-- The enlarged feature map of `EnlargedLowOrderLDGenerator`, which the microscopic kernel
uses, has a compact realization body. It agrees with the enlarged feature map of
`KernelRealizationPreservation` at every state and coordinate by evaluation, so the two bodies
are one set. -/
theorem isCompact_enlargedRealizationBody (D : ℕ) :
    IsCompact
      (realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D))) := by
  have hsame : EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D)
      = KernelRealizationPreservation.enlargedLowOrderLDFeature D := by
    funext state coordinate
    cases coordinate with
    | none => rfl
    | some enlarged => cases enlarged <;> rfl
  rw [hsame]
  exact isCompact_realizationBody_enlargedLowOrderLDFeature D

/-- The enlarged realization body used by the microscopic kernel is closed. -/
theorem isClosed_enlargedRealizationBody (D : ℕ) :
    IsClosed
      (realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D))) :=
  (isCompact_enlargedRealizationBody D).isClosed

/-! ## Invariance statements with no closedness hypothesis -/

/-- **NOTE1 Theorem 1 for the enlarged family, with no closedness hypothesis.** Any generator
on the enlarged coordinates that admits a microscopic approximation by genuine finite mixture
kernels carries the enlarged realization body into itself at every nonnegative time.
Assumes: the approximation, supplied as data. -/
theorem exp_mulVec_mem_enlargedRealizationBody_of_approx {D : ℕ} {B : Type*} [Fintype B]
    (generator : Matrix (AffineEnlargedCoordinate D) (AffineEnlargedCoordinate D) ℝ)
    (approx : MicroscopicApproximation (B := B)
      (KernelRealizationPreservation.enlargedLowOrderLDFeature D) generator)
    (t : ℝ) (ht : 0 ≤ t) (v : AffineEnlargedCoordinate D → ℝ)
    (hv : v ∈ realizationBody (KernelRealizationPreservation.enlargedLowOrderLDFeature D)) :
    (matrixExponential generator t).mulVec v
      ∈ realizationBody (KernelRealizationPreservation.enlargedLowOrderLDFeature D) :=
  KernelRealizationPreservation.exp_mulVec_mem_realizationBody _ generator approx
    (isClosed_realizationBody_enlargedLowOrderLDFeature D) t ht v hv

/-- **One enlarged epoch, with no closedness hypothesis.** The exact propagator of the enlarged
generator of NOTE1 §2.2 over a nonnegative duration carries the enlarged realization body into
itself whenever that generator has a microscopic approximation.
Assumes: the approximation, supplied as data. -/
theorem enlargedPropagator_mulVec_mem_of_approx {D : ℕ} {B : Type*} [Fintype B]
    (rates : ManyDemeLDRates D)
    (approx : MicroscopicApproximation (B := B)
      (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D))
      (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration) (v : AffineEnlargedCoordinate D → ℝ)
    (hv : v ∈
      realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D))) :
    (matrixExponential (enlargedLowOrderLDGenerator rates) duration).mulVec v
      ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D)) :=
  KernelRealizationPreservation.exp_mulVec_mem_realizationBody _ _ approx
    (isClosed_enlargedRealizationBody D) duration hduration v hv

/-- The embedding of every locus-exchangeably realizable stored state lies in the enlarged
realization body. The realization's expectation is an arbitrary positive normalized
functional, and the separation argument places it in the body because the body is closed. -/
theorem embed_mem_enlargedRealizationBody_of_realization {D : ℕ}
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    embedLowOrderLDState state
      ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D)) :=
  TwoLocusRealizabilityPreservation.embed_mem_enlargedRealizationBody
    (isClosed_enlargedRealizationBody D) realization

/-- **NOTE1 Theorem 2 for one epoch, with the microscopic approximation as the only
hypothesis.** The propagated stored vector of every locus-exchangeably realizable state is
again the vector of all its defining polynomials under one common haplotype law, with the
expected left and right heterozygosities still identified.
Assumes: the approximation of the enlarged generator, supplied as data. -/
theorem epoch_preserves_locusExchangeable_realization_of_approx {D : ℕ} {Branch : Type*}
    [Fintype Branch] (rates : ManyDemeLDRates D)
    (approximation : MicroscopicApproximation (B := Branch)
      (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D))
      (enlargedLowOrderLDGenerator rates))
    (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) :=
  TwoLocusRealizabilityPreservation.epoch_preserves_locusExchangeable_realization
    (isClosed_enlargedRealizationBody D) rates approximation duration hduration realization

end

end Descent.Portability.EnlargedBodyClosedness
