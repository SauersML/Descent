/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory
import Descent.Portability.StationaryHaplotypeRealization

assert_below Descent.Decision Descent.Program

/-!
# The unsplit ancestral state has a common haplotype realization

A demographic history in the corpus starts at the instant before the first split, where every
descendant deme label still denotes the same ancestral population. Its initial low-order state
is `commonAncestralLowOrderLDState ancestralRates`: the constant coordinate is one, and every
coordinate, whatever its deme indices, carries the value of the one-deme stationary state of
NOTE1 (16) at the collapsed one-deme coordinate. This module proves, with no hypotheses, that
this state carries a locus-exchangeable haplotype realization, which is the initial-state input
that NOTE1 Theorem 2 needs to propagate realizability through a compiled history.

The construction is the relabelling that the state's definition describes.
`cloneLocusExchangeableRealization` takes any locus-exchangeable realization of the one-deme
stationary state and keeps its sample space and its expectation, but reads the single ancestral
haplotype at every deme label. Each defining polynomial of the multi-deme state, at any deme
indices, is then the same polynomial of that one haplotype, which is exactly the collapsed
one-deme coordinate; the right-locus heterozygosity field is inherited in the same way. This is
the full-family analogue of the corpus's `commonAncestralLowOrderLDDDRealization`, which does
the same for the `DD` block with a deterministic linkage observable, and of the relabelling in
`LowOrderLDHaplotypeRealization.split`.

`ancestralLocusExchangeableRealization` applies the clone to the one-deme realization that
`StationaryHaplotypeRealization.nonempty_stationaryLocusExchangeableRealization` provides, NOTE1
Theorem 3 with no hypotheses; the choice of that realization is the only non-constructive step.
`nonempty_ancestralLocusExchangeableRealization`,
`commonAncestralLowOrderLDState_mem_realizationBody` and
`embed_commonAncestralLowOrderLDState_mem` are its consequences for the stored and the enlarged
realization bodies.

## Empirical status

None. The bodies here are relabellings: one probability law read at several deme labels. No
measurement can bear on whether a relabelled law has the moments of the law it relabels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralHaplotypeRealization

open Descent.Coalescent
open Descent.Portability.RealizationBody

noncomputable section

/-- **Cloning the ancestral haplotype into every deme.** A locus-exchangeable haplotype
realization of the one-deme stationary state gives one of the unsplit multi-deme ancestral
state: keep the probability law and read the single ancestral haplotype at every deme label.
Every multi-deme coordinate is the collapsed one-deme coordinate of that haplotype. -/
def cloneLocusExchangeableRealization {D : ℕ} {ancestralRates : ManyDemeLDRates 1}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization
      (oneDemeStationaryLowOrderLDState ancestralRates)) :
    LocusExchangeableLowOrderLDHaplotypeRealization
      (commonAncestralLowOrderLDState (D := D) ancestralRates) where
  sampleSpace := realization.sampleSpace
  expectation := realization.expectation
  haplotype := fun outcome _ ↦ realization.haplotype outcome 0
  constant_eq := rfl
  H_eq _ _ := realization.H_eq 0 0
  DD_eq _ _ := realization.DD_eq 0 0
  Dz_eq _ _ _ := realization.Dz_eq 0 0 0
  pi2_eq _ _ _ _ := realization.pi2_eq 0 0 0 0
  H_right_eq _ _ := realization.H_right_eq 0 0

/-- **The unsplit ancestral state is locus-exchangeably realizable, with no hypotheses.** The
realization is the clone of the one-deme stationary realization of NOTE1 Theorem 3 into every
deme label; only the choice of that one-deme realization is non-constructive. -/
def ancestralLocusExchangeableRealization {D : ℕ} (ancestralRates : ManyDemeLDRates 1) :
    LocusExchangeableLowOrderLDHaplotypeRealization
      (commonAncestralLowOrderLDState (D := D) ancestralRates) :=
  cloneLocusExchangeableRealization (Classical.choice
    (StationaryHaplotypeRealization.nonempty_stationaryLocusExchangeableRealization
      ancestralRates))

/-- The unsplit ancestral state of every demographic history has a locus-exchangeable
haplotype realization. -/
theorem nonempty_ancestralLocusExchangeableRealization {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      (commonAncestralLowOrderLDState (D := D) ancestralRates)) :=
  ⟨ancestralLocusExchangeableRealization ancestralRates⟩

/-- The unsplit ancestral state lies in the stored realization body, so every inequality valid
on that body holds at the start of every history. -/
theorem commonAncestralLowOrderLDState_mem_realizationBody {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) :
    commonAncestralLowOrderLDState (D := D) ancestralRates
      ∈ realizationBody (lowOrderLDFeature D) :=
  KernelRealizationPreservation.lowOrderLDState_mem_realizationBody_of_realization
    (ancestralLocusExchangeableRealization ancestralRates).toLowOrderLDHaplotypeRealization

/-- The locus-exchangeable embedding of the unsplit ancestral state lies in the enlarged
realization body, which is where the enlarged epoch propagator acts. -/
theorem embed_commonAncestralLowOrderLDState_mem {D : ℕ}
    (ancestralRates : ManyDemeLDRates 1) :
    EnlargedLowOrderLDGenerator.embedLowOrderLDState
        (commonAncestralLowOrderLDState (D := D) ancestralRates)
      ∈ realizationBody (EnlargedLowOrderLDGenerator.enlargedLowOrderLDFeature (D := D)) :=
  EnlargedBodyClosedness.embed_mem_enlargedRealizationBody_of_realization
    (ancestralLocusExchangeableRealization ancestralRates)

end

end Descent.Portability.AncestralHaplotypeRealization
