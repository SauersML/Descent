/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StoppedGenotypeLaw
import Descent.Portability.AncestralGenealogyOrdering

assert_below Descent.Decision Descent.Program

/-!
Support invariants for the stopped genealogy mutation construction. Active
descendant clades have a shared ancestral nucleotide before mutation, and all
sample nucleotide states remain represented in their ordered allele catalogue.
These properties are derived from ancestral material coarsening and the actual
mutation updates, not imposed as assumptions on the resulting genotype law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.StoppedGenotypeReadiness

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralAbsorptionLaw StoppedAncestralTiming AncestralGenealogyLaw
open AncestralCladePartition AncestralGenealogyOrdering OrderedCladeLaw
open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue
open InterleavedMutationLaw InterleavedMutationMeasurability StoppedGenotypeLaw
open MeasureTheory NucleotideMutationLaw
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

private theorem rootSite_excludes (property : SiteState n → Prop)
    (hroot : ∀ root, property (OrderedMutationCatalogue.initialState root))
    (target : SiteState n) (htarget : ¬ property target) : rootSiteLaw.mass target = 0 :=
  pushforward_excludes rootLaw _ property hroot target htarget

def StateReady (state : State D L n) (locus : Fin L) (site : SiteState n) : Prop :=
  Ready (intervalBranches state locus 0) site.1

/-- Every mutation on an older active clade preserves the common nucleotide
on every intersecting earlier clade. Ancestral material coarsening supplies the
required containment or disjointness relation. -/
theorem recordMutation_ready (earlier older : State D L n) (hext : Extends earlier older)
    (locus : Fin L) (exposure : Fin (intervalBranches older locus 0).length → ℝ≥0)
    (site : SiteState n) (hsite : StateReady earlier locus site)
    (index : Fin (intervalBranches older locus 0).length) (base : Nucleotide) :
    StateReady earlier locus
      (recordMutation (replaceExposure (intervalTemplates older locus) exposure index)
        site base) := by
  intro younger hyounger
  have htemplate : intervalTemplates older locus index ∈ intervalBranches older locus 0 :=
    List.get_mem _ index
  obtain ⟨a, ha, hea⟩ := mem_intervalBranches older locus 0 _ htemplate
  obtain ⟨b, hb, heb⟩ := mem_intervalBranches earlier locus 0 younger hyounger
  apply homogeneous_overwrite _ younger _ site.1 (hsite younger hyounger) base
  change Disjoint (intervalTemplates older locus index).descendants younger.descendants ∨
    younger.descendants ⊆ (intervalTemplates older locus index).descendants
  rw [hea, heb]
  exact hext.2 a ha b hb locus

theorem conditionalSite_unsupported_ready (earlier : State D L n) (locus : Fin L)
    (mutationRate : ℝ≥0) {start : State D L n} (trace : Trace count start)
    (hext : Extends earlier start) (waits : Fin count → ℝ) (target : SiteState n)
    (htarget : ¬ StateReady earlier locus target) :
    (conditionalSiteLaw locus mutationRate trace waits).mass target = 0 := by
  induction count generalizing earlier start target with
  | zero =>
      exact rootSite_excludes (StateReady earlier locus)
        (fun root ↦ ready_uniform _ root) target htarget
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      apply bind_excludes _ _ (StateReady earlier locus) (StateReady earlier locus)
      · intro middle hmiddle
        exact ih earlier rest (hext.trans (extends_proposal start event))
          (fun index ↦ waits index.succ) middle hmiddle
      · intro middle hmiddle output houtput
        exact interval_excludes _ (StateReady earlier locus)
          (recordMutation_ready earlier start hext locus _) middle output hmiddle houtput
      · exact htarget

/-- Every positive-mass conditional output is ready on all clades of every
earlier ancestry state. In particular, the next younger interval receives the
shared ancestral base required by its JC69 branch mutation kernels. -/
theorem conditionalSiteLaw_ready (earlier : State D L n) (locus : Fin L)
    (mutationRate : ℝ≥0) {start : State D L n} (trace : Trace count start)
    (hext : Extends earlier start) (waits : Fin count → ℝ) (target : SiteState n)
    (hpositive : 0 < (conditionalSiteLaw locus mutationRate trace waits).mass target) :
    StateReady earlier locus target := by
  by_contra htarget
  rw [conditionalSite_unsupported_ready earlier locus mutationRate trace hext waits target htarget]
    at hpositive
  exact lt_irrefl 0 hpositive

theorem stateReady_branch (state : State D L n) (locus : Fin L) (site : SiteState n)
    (hsite : StateReady state locus site)
    (exposure : Fin (intervalBranches state locus 0).length → ℝ≥0)
    (index : Fin (intervalBranches state locus 0).length) :
    Homogeneous (replaceExposure (intervalTemplates state locus) exposure index) site.1 :=
  hsite (intervalTemplates state locus index) (List.get_mem _ index)

/-- The older recursive result supplies a shared ancestral nucleotide to
every branch of the next younger interval in the stopped construction. -/
theorem nextInterval_input_homogeneous (start : State D L n) (event : Option (Channel start))
    (rest : Trace count (proposalNext start event)) (locus : Fin L) (mutationRate : ℝ≥0)
    (waits : Fin count → ℝ) (site : SiteState n)
    (hpositive : 0 < (conditionalSiteLaw locus mutationRate rest waits).mass site)
    (exposure : Fin (intervalBranches start locus 0).length → ℝ≥0)
    (index : Fin (intervalBranches start locus 0).length) :
    Homogeneous (replaceExposure (intervalTemplates start locus) exposure index) site.1 :=
  stateReady_branch start locus site
    (conditionalSiteLaw_ready start locus mutationRate rest (extends_proposal start event)
      waits site hpositive) exposure index

/-- Shared clade bases remain valid at every proposal step inside an interval,
including arbitrarily interleaved mutations on all contemporaneous branches. -/
theorem intervalCount_ready (state : State D L n) (locus : Fin L)
    (exposure : Fin (intervalBranches state locus 0).length → ℝ≥0)
    (site : SiteState n) (hsite : StateReady state locus site) (proposals : ℕ)
    (target : SiteState n)
    (hpositive : 0 < FiniteReportLaw.mass
      (InterleavedMutationLaw.countLaw (replaceExposure (intervalTemplates state locus) exposure)
        site proposals) target) : StateReady state locus target := by
  by_contra htarget
  have hzero := count_excludes _ (StateReady state locus)
    (recordMutation_ready state state (Extends.refl state) locus exposure)
    site hsite proposals target htarget
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

theorem conditionalSite_unsupported_covered (locus : Fin L) (mutationRate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (waits : Fin count → ℝ)
    (target : SiteState n) (htarget : ¬ Covered target) :
    (conditionalSiteLaw locus mutationRate trace waits).mass target = 0 := by
  induction count generalizing start target with
  | zero => exact rootSite_excludes Covered initialState_covered target htarget
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      apply bind_excludes _ _ Covered Covered
      · intro middle hmiddle
        exact ih rest (fun index ↦ waits index.succ) middle hmiddle
      · intro middle hmiddle output houtput
        exact interval_excludes _ Covered
          (fun site hsite index base ↦ recordMutation_covered _ site base hsite)
          middle output hmiddle houtput
      · exact htarget

def GenomeCovered (genome : WholeGenome L n) : Prop := ∀ locus, Covered (genome locus)

theorem conditionalGenome_unsupported_covered (mutationRate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (waits : Fin count → ℝ)
    (genome : WholeGenome L n) (hgenome : ¬ GenomeCovered genome) :
    (conditionalGenomeLaw mutationRate trace waits).mass genome = 0 := by
  classical
  obtain ⟨locus, hlocus⟩ := not_forall.mp hgenome
  exact Finset.prod_eq_zero (Finset.mem_univ locus)
    (conditionalSite_unsupported_covered locus mutationRate trace waits (genome locus) hlocus)

theorem stoppedGenome_unsupported_covered (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) (genome : WholeGenome L n) (hgenome : ¬ GenomeCovered genome) :
    (stoppedGenomeLaw rates deme start hs hsupported hisolated mutationRate).mass genome = 0 := by
  simp [stoppedGenomeLaw, genomeCountMass, stoppedCountExpectation,
    conditionalGenome_unsupported_covered mutationRate _ _ genome hgenome]

/-- The complete stopped mixture is supported on valid allele-index decoding
states. This survives both the continuous waiting-time integral and the
infinite sum over first-completion indices. -/
theorem stoppedGenome_covered (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) (genome : WholeGenome L n)
    (hpositive : 0 < FiniteReportLaw.mass
      (stoppedGenomeLaw rates deme start hs hsupported hisolated mutationRate) genome) :
    GenomeCovered genome := by
  by_contra hgenome
  rw [stoppedGenome_unsupported_covered rates deme start hs hsupported hisolated mutationRate
    genome hgenome] at hpositive
  exact lt_irrefl 0 hpositive

theorem rawDiploidDosage_le_six {individuals : ℕ} (genome : WholeGenome L (2 * individuals))
    (hgenome : GenomeCovered genome) (locus : Fin L) (individual : Fin individuals) :
    rawDiploidDosage genome locus individual ≤ 6 :=
  rawDosage_le_six (genome locus) (hgenome locus) _ _

end Descent.Portability.StoppedGenotypeReadiness
