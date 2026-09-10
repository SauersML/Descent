/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.WholeGenomeMutationSemigroup

assert_below Descent.Decision Descent.Program

/-!
Catalogue coverage and clade homogeneity throughout a finite demographic
history. The continuation invariant is propagated through mutation intervals,
ancestral proposals, epoch mixtures, relocations, and the complete final tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralEpochGenotypeSupport

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralAbsorptionLaw StoppedAncestralTiming AncestralGenealogyLaw
open AncestralCladePartition StoppedGenotypeReadiness
open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue
open InterleavedMutationLaw InterleavedMutationMeasurability StoppedGenotypeLaw
open AncestralEpochGenotypeLaw WholeGenomeMutationSemigroup
open AncestralEpochLaw TimedAncestralLaw MeasureTheory
open scoped NNReal

variable {D L n count : ℕ}

private theorem pushforward_excludes {A B : Type*} [Fintype A] [Fintype B]
    (law : FiniteReportLaw A) (map : A → B) (property : B → Prop)
    (hmap : ∀ source, property (map source)) (target : B) (htarget : ¬ property target) :
    (law.pushforward map).mass target = 0 := by
  classical
  have hne (source : A) : target ≠ map source := by
    intro heq
    exact htarget (heq ▸ hmap source)
  simp [pushforward, FiniteReportLaw.bind, pointMass, hne]

private theorem bind_excludes {A B : Type*} [Fintype A] [Fintype B]
    (law : FiniteReportLaw A) (kernel : A → FiniteReportLaw B)
    (sourceProperty : A → Prop) (targetProperty : B → Prop)
    (hlaw : ∀ source, ¬ sourceProperty source → law.mass source = 0)
    (hkernel : ∀ source, sourceProperty source →
      ∀ target, ¬ targetProperty target → (kernel source).mass target = 0)
    (target : B) (htarget : ¬ targetProperty target) : (law.bind kernel).mass target = 0 := by
  classical
  change (∑ source, law.mass source * (kernel source).mass target) = 0
  apply Finset.sum_eq_zero
  intro source _
  by_cases hs : sourceProperty source
  · rw [hkernel source hs target htarget, mul_zero]
  · rw [hlaw source hs, zero_mul]

private theorem intervalKernel_excludes {branchCount : ℕ}
    (branches : Fin branchCount → Branch n) (property : SiteState n → Prop)
    (hstep : ∀ site, property site → ∀ index base,
      property (recordMutation (branches index) site base))
    (site target : SiteState n) (hsite : property site) (htarget : ¬ property target) :
    (intervalKernel branches site).mass target = 0 := by
  classical
  have hne : target ≠ site := by intro heq; exact htarget (heq ▸ hsite)
  change (∑ mark, (markLaw branches).mass mark *
    (markedKernel branches site mark).mass target) = 0
  apply Finset.sum_eq_zero
  intro mark _
  cases mark with
  | none => simp [markedKernel, pointMass, hne]
  | some index =>
      have hzero : (mutationKernel (branches index) site).mass target = 0 :=
        pushforward_excludes _ _ property (hstep site hsite index) target htarget
      simp [markedKernel, hzero]

private theorem count_excludes {branchCount : ℕ}
    (branches : Fin branchCount → Branch n) (property : SiteState n → Prop)
    (hstep : ∀ site, property site → ∀ index base,
      property (recordMutation (branches index) site base))
    (site : SiteState n) (hsite : property site) (proposals : ℕ)
    (target : SiteState n) (htarget : ¬ property target) :
    (InterleavedMutationLaw.countLaw branches site proposals).mass target = 0 := by
  classical
  induction proposals generalizing target with
  | zero =>
      have hne : target ≠ site := by intro heq; exact htarget (heq ▸ hsite)
      simp [InterleavedMutationLaw.countLaw, ExactFiniteHistoryLaw.propagate, pointMass, hne]
  | succ proposals ih =>
      exact bind_excludes _ _ property property ih
        (fun middle hm output ho ↦
          intervalKernel_excludes branches property hstep middle output hm ho)
        target htarget

private theorem interval_excludes {branchCount : ℕ}
    (branches : Fin branchCount → Branch n) (property : SiteState n → Prop)
    (hstep : ∀ site, property site → ∀ index base,
      property (recordMutation (branches index) site base))
    (site target : SiteState n) (hsite : property site) (htarget : ¬ property target) :
    (intervalLaw branches site).mass target = 0 := by
  simp [intervalLaw, count_excludes branches property hstep site hsite _ target htarget]

/-- Every sample nucleotide is catalogued and every extant clade has the
single shared nucleotide needed for subsequent younger branch mutations. -/
def GenomeGood (earlier : State D L n) (genome : WholeGenome L n) : Prop :=
  ∀ locus, StateReady earlier locus (genome locus) ∧ Covered (genome locus)

/-- The continuation retains the invariant for every earlier clade partition. -/
def ContinuationGood (continuation : Continuation D L n) : Prop :=
  ∀ state hs earlier, Extends earlier state → ∀ genome,
    ¬ GenomeGood earlier genome → (continuation state hs).mass genome = 0

theorem intervalGenome_excludes (earlier older : State D L n) (hext : Extends earlier older)
    (rate : ℝ≥0) (wait : ℝ) (source target : WholeGenome L n)
    (hsource : GenomeGood earlier source) (htarget : ¬ GenomeGood earlier target) :
    (intervalGenomeKernel older rate wait source).mass target = 0 := by
  classical
  obtain ⟨locus, hlocus⟩ : ∃ locus, ¬ (StateReady earlier locus (target locus) ∧
      Covered (target locus)) := by simpa [GenomeGood] using htarget
  have hzero : (stateIntervalLaw older locus rate wait (source locus)).mass (target locus) = 0 := by
    apply interval_excludes _ (fun site ↦ StateReady earlier locus site ∧ Covered site)
    · intro site hsite index base
      exact ⟨recordMutation_ready earlier older hext locus _ site hsite.1 index base,
        recordMutation_covered _ site base hsite.2⟩
    · exact hsource locus
    · exact hlocus
  exact Finset.prod_eq_zero (Finset.mem_univ locus) hzero

theorem conditionalEpoch_excludes (continuation : Continuation D L n)
    (hcontinuation : ContinuationGood continuation) (rate : ℝ≥0)
    (earlier : State D L n) {start : State D L n} (trace : Trace count start)
    (hs : SampleComplete start) (hext : Extends earlier start)
    (duration : ℝ) (times : Fin count → ℝ) (target : WholeGenome L n)
    (htarget : ¬ GenomeGood earlier target) :
    (conditionalEpochLaw continuation rate trace hs duration times).mass target = 0 := by
  induction count generalizing start earlier target duration with
  | zero =>
      apply bind_excludes _ _ (GenomeGood earlier) (GenomeGood earlier)
      · exact hcontinuation start hs earlier hext
      · intro source hsource output houtput
        exact intervalGenome_excludes earlier start hext rate duration source output hsource houtput
      · exact htarget
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      apply bind_excludes _ _ (GenomeGood earlier) (GenomeGood earlier)
      · intro source hsource
        exact ih earlier rest (sampleComplete_proposal start hs event)
          (hext.trans (extends_proposal start event)) (duration - times 0)
          (fun index ↦ times index.succ - times 0) source hsource
      · intro source hsource output houtput
        exact intervalGenome_excludes earlier start hext rate (times 0) source output
          hsource houtput
      · exact htarget

theorem conditionalEpoch_good (continuation : Continuation D L n)
    (hcontinuation : ContinuationGood continuation) (rate : ℝ≥0)
    (earlier : State D L n) {start : State D L n} (trace : Trace count start)
    (hs : SampleComplete start) (hext : Extends earlier start)
    (duration : ℝ) (times : Fin count → ℝ) (target : WholeGenome L n)
    (hpositive : 0 < (conditionalEpochLaw continuation rate trace hs duration times).mass target) :
    GenomeGood earlier target := by
  by_contra htarget
  rw [conditionalEpoch_excludes continuation hcontinuation rate earlier trace hs hext
    duration times target htarget] at hpositive
  exact lt_irrefl 0 hpositive

/-- Every older intermediate genome entering a younger epoch interval has
one shared nucleotide across each of that interval's active branch clades. -/
theorem nextEpochInterval_input_homogeneous (continuation : Continuation D L n)
    (hcontinuation : ContinuationGood continuation) (rate : ℝ≥0)
    (start : State D L n) (hs : SampleComplete start) (event : Option (Channel start))
    (rest : Trace count (proposalNext start event)) (duration : ℝ) (times : Fin count → ℝ)
    (input : WholeGenome L n)
    (hpositive : 0 < (conditionalEpochLaw continuation rate rest
      (sampleComplete_proposal start hs event) duration times).mass input)
    (locus : Fin L) (branch : Fin (intervalBranches start locus 0).length) :
    Homogeneous (intervalTemplates start locus branch) (input locus).1 := by
  have hgood := conditionalEpoch_good continuation hcontinuation rate start rest
    (sampleComplete_proposal start hs event) (extends_proposal start event) duration times
      input hpositive
  exact stateReady_branch start locus (input locus) (hgood locus).1 (fun _ ↦ 0) branch

/-- A finite demographic epoch preserves the full continuation invariant. -/
theorem epochGenome_good (rates : Rates D L) (continuation : Continuation D L n)
    (hcontinuation : ContinuationGood continuation) (rate duration : ℝ≥0) :
    ContinuationGood (fun start hs ↦ epochGenomeLaw rates continuation rate start hs duration) := by
  intro start hs earlier hext target htarget
  have hzero (count : ℕ) (trace : Trace count start) (times : Fin count → ℝ) :=
    conditionalEpoch_excludes continuation hcontinuation rate earlier trace hs hext
      duration times target htarget
  simp [epochGenomeLaw, epochCountMass, countExpectation, expectation, hzero]

theorem conditionalGenome_excludes_good (earlier : State D L n) (rate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (hext : Extends earlier start)
    (waits : Fin count → ℝ) (target : WholeGenome L n) (htarget : ¬ GenomeGood earlier target) :
    (conditionalGenomeLaw rate trace waits).mass target = 0 := by
  classical
  obtain ⟨locus, hlocus⟩ : ∃ locus, ¬ (StateReady earlier locus (target locus) ∧
      Covered (target locus)) := by simpa [GenomeGood] using htarget
  apply Finset.prod_eq_zero (Finset.mem_univ locus)
  by_cases hready : StateReady earlier locus (target locus)
  · exact conditionalSite_unsupported_covered locus rate trace waits (target locus)
      (fun hcovered ↦ hlocus ⟨hready, hcovered⟩)
  · exact conditionalSite_unsupported_ready earlier locus rate trace hext waits
      (target locus) hready

theorem stoppedGenome_excludes_good (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (rate : ℝ≥0) (earlier : State D L n) (hext : Extends earlier start)
    (target : WholeGenome L n) (htarget : ¬ GenomeGood earlier target) :
    (stoppedGenomeLaw rates deme start hs hsupported hisolated rate).mass target = 0 := by
  have hzero (count : ℕ) (trace : Trace count start) (waits : Fin count → ℝ) :=
    conditionalGenome_excludes_good earlier rate trace hext waits target htarget
  simp [stoppedGenomeLaw, genomeCountMass, stoppedCountExpectation, hzero]

theorem mergingTail_good (rates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, rates.migration ancestor destination = 0) (rate : ℝ≥0) :
    ContinuationGood (mergingTailContinuation (n := n) rates ancestor hisolated rate) := by
  intro start hs earlier hext target htarget
  exact stoppedGenome_excludes_good rates ancestor _ (sampleComplete_relabel start hs _)
    (supportedAt_relabel ancestor start) hisolated rate earlier
      (hext.trans (extends_relabel start (fun _ ↦ ancestor))) target htarget

/-- Epoch and relocation composition preserve ancestral clade homogeneity. -/
theorem historyGenome_good (rate : ℝ≥0) (instructions : List (Instruction D L))
    (continuation : Continuation D L n) (hcontinuation : ContinuationGood continuation) :
    ContinuationGood (historyGenomeLaw rate instructions continuation) := by
  induction instructions with
  | nil => exact hcontinuation
  | cons instruction rest ih =>
      cases instruction with
      | epoch rates duration => exact epochGenome_good rates _ ih rate duration
      | relocate destination =>
          intro start hs earlier hext target htarget
          exact ih _ (sampleComplete_relabel start hs destination) earlier
            (hext.trans (extends_relabel start destination)) target htarget

/-- Every positive-mass genome produced by the complete finite demographic
history has valid catalogue decoding and the correct shared clade states. -/
theorem completeDemography_good (instructions : List (Instruction D L))
    (finalRates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, finalRates.migration ancestor destination = 0)
    (rate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (target : WholeGenome L n)
    (hpositive : 0 < (completeDemographyLaw instructions finalRates ancestor hisolated rate
      start hs).mass target) : GenomeGood start target := by
  by_contra htarget
  have hzero := historyGenome_good rate instructions _
    (mergingTail_good finalRates ancestor hisolated rate) start hs start (Extends.refl start)
      target htarget
  change (completeDemographyLaw instructions finalRates ancestor hisolated rate start hs).mass
    target = 0 at hzero
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

theorem completeDemography_covered (instructions : List (Instruction D L))
    (finalRates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, finalRates.migration ancestor destination = 0)
    (rate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (target : WholeGenome L n)
    (hpositive : 0 < (completeDemographyLaw instructions finalRates ancestor hisolated rate
      start hs).mass target) : GenomeCovered target := by
  intro locus
  exact (completeDemography_good instructions finalRates ancestor hisolated rate start hs
    target hpositive locus).2

/-- Raw diploid allele-index dosage is bounded by six on every positive-mass
output of the complete demographic simulation law. -/
theorem completeDemography_rawDosage_le_six {individuals : ℕ}
    (instructions : List (Instruction D L)) (finalRates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, finalRates.migration ancestor destination = 0)
    (rate : ℝ≥0) (start : State D L (2 * individuals)) (hs : SampleComplete start)
    (target : WholeGenome L (2 * individuals))
    (hpositive : 0 < (completeDemographyLaw instructions finalRates ancestor hisolated rate
      start hs).mass target) (locus : Fin L) (individual : Fin individuals) :
    rawDiploidDosage target locus individual ≤ 6 :=
  StoppedGenotypeReadiness.rawDiploidDosage_le_six target
    (completeDemography_covered instructions finalRates ancestor hisolated rate start hs
      target hpositive) locus individual

end Descent.Portability.AncestralEpochGenotypeSupport
