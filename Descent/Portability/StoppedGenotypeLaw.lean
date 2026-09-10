/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StoppedAncestralTiming
import Descent.Portability.AncestralGenealogyLaw
import Descent.Portability.InterleavedMutationMeasurability

assert_below Descent.Decision Descent.Program

/-!
Joint finite genotype law from stopped marked ancestral histories, including
their exponential waiting increments. Each locus retains its ordered allele
catalogue and site-presence flag. Mutation intervals are processed from older
to younger; events on contemporaneous branches are globally interleaved.

Sites have independent JC69 mutation and root draws conditional on the common
linked ancestry and waiting times. Averaging that common history preserves
dependence between loci. This constructs the complete ancestral tail in an
isolated final population; earlier demographic epochs must be composed with
this tail to obtain the original present-day simulation law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.StoppedGenotypeLaw

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralAbsorptionLaw StoppedAncestralTiming AncestralGenealogyLaw
open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue
open InterleavedMutationLaw InterleavedMutationMeasurability MeasureTheory
open scoped NNReal

variable {D L n count : ℕ}

abbrev WholeGenome (L n : ℕ) := Fin L → SiteState n

/-- Only sites with at least one mutation enter the simulator's genotype
matrix, including sites whose sample nucleotide states are monomorphic. -/
def retainedSites (genome : WholeGenome L n) : Finset (Fin L) :=
  Finset.univ.filter (fun locus ↦ (genome locus).2.2)

theorem mem_retainedSites (genome : WholeGenome L n) (locus : Fin L) :
    locus ∈ retainedSites genome ↔ (genome locus).2.2 = true := by
  simp [retainedSites]

def firstHaplotype {individuals : ℕ} (individual : Fin individuals) : Fin (2 * individuals) :=
  ⟨2 * individual.val, by have h := individual.isLt; omega⟩

def secondHaplotype {individuals : ℕ} (individual : Fin individuals) : Fin (2 * individuals) :=
  ⟨2 * individual.val + 1, by have h := individual.isLt; omega⟩

/-- The causal/PCA reservoir retains these raw allele-index sums. -/
def rawDiploidDosage {individuals : ℕ} (genome : WholeGenome L (2 * individuals))
    (locus : Fin L) (individual : Fin individuals) : ℕ :=
  rawDosage (genome locus) (firstHaplotype individual) (secondHaplotype individual)

/-- The BED training matrix uses the clipped sums instead. -/
def bedDiploidDosage {individuals : ℕ} (genome : WholeGenome L (2 * individuals))
    (locus : Fin L) (individual : Fin individuals) : ℕ :=
  bedDosage (genome locus) (firstHaplotype individual) (secondHaplotype individual)

theorem bedDiploidDosage_eq_clip {individuals : ℕ}
    (genome : WholeGenome L (2 * individuals)) (locus : Fin L) (individual : Fin individuals) :
    bedDiploidDosage genome locus individual = min (rawDiploidDosage genome locus individual) 2 :=
  rfl

noncomputable def rootSiteLaw : FiniteReportLaw (SiteState n) :=
  rootLaw.pushforward (OrderedMutationCatalogue.initialState (n := n))

noncomputable def intervalTemplates (state : State D L n) (locus : Fin L) :
    Fin (intervalBranches state locus 0).length → Branch n :=
  (intervalBranches state locus 0).get

noncomputable def stateIntervalLaw (state : State D L n) (locus : Fin L)
    (mutationRate : ℝ≥0) (wait : ℝ) (site : SiteState n) : FiniteReportLaw (SiteState n) :=
  intervalLaw (replaceExposure (intervalTemplates state locus)
    (fun _ ↦ mutationRate * Real.toNNReal wait)) site

theorem stateInterval_mass_measurable (state : State D L n) (locus : Fin L)
    (mutationRate : ℝ≥0) (site target : SiteState n) :
    Measurable (fun wait ↦ (stateIntervalLaw state locus mutationRate wait site).mass target) :=
  interval_mass_measurable (intervalTemplates state locus)
    (fun _ wait ↦ mutationRate * Real.toNNReal wait)
    (fun _ ↦ waiting_exposure_measurable mutationRate id measurable_id) site target

/-- The recursion reverses backward ancestry time. The mutation interval
preceding the first backward proposal is applied after all older intervals. -/
noncomputable def conditionalSiteLaw (locus : Fin L) (mutationRate : ℝ≥0) :
    {count : ℕ} → {start : State D L n} → Trace count start →
      (Fin count → ℝ) → FiniteReportLaw (SiteState n)
  | 0, _, _, _ => rootSiteLaw
  | _count + 1, start, ⟨_event, rest⟩, waits =>
      (conditionalSiteLaw locus mutationRate rest (fun index ↦ waits index.succ)).bind
        (stateIntervalLaw start locus mutationRate (waits 0))

theorem conditionalSite_mass_measurable (locus : Fin L) (mutationRate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (target : SiteState n) :
    Measurable (fun waits ↦ (conditionalSiteLaw locus mutationRate trace waits).mass target) := by
  induction count generalizing start target with
  | zero => exact measurable_const
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      have htail : Measurable (fun waits : Fin (count + 1) → ℝ ↦
          fun index : Fin count ↦ waits index.succ) :=
        measurable_pi_lambda _ (fun index ↦ measurable_pi_apply index.succ)
      apply bind_mass_measurable
      · intro site
        exact (ih rest site).comp htail
      · intro site output
        exact (stateInterval_mass_measurable start locus mutationRate site output).comp
          (measurable_pi_apply 0)

/-- The conditional product law retains the common history as an input. Only
mutation and root randomness are independent across loci at this stage. -/
noncomputable def conditionalGenomeLaw (mutationRate : ℝ≥0) {start : State D L n}
    (trace : Trace count start) (waits : Fin count → ℝ) : FiniteReportLaw (WholeGenome L n) where
  mass := fun genome ↦
    ∏ locus, (conditionalSiteLaw locus mutationRate trace waits).mass (genome locus)
  mass_nonneg := fun genome ↦ Finset.prod_nonneg (fun locus _ ↦
    (conditionalSiteLaw locus mutationRate trace waits).mass_nonneg (genome locus))
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

theorem conditionalGenome_mass_measurable (mutationRate : ℝ≥0) {start : State D L n}
    (trace : Trace count start) (genome : WholeGenome L n) :
    Measurable (fun waits ↦ (conditionalGenomeLaw mutationRate trace waits).mass genome) := by
  change Measurable (fun waits ↦ ∏ locus,
    (conditionalSiteLaw locus mutationRate trace waits).mass (genome locus))
  apply Finset.measurable_prod
  intro locus _
  exact conditionalSite_mass_measurable locus mutationRate trace (genome locus)

theorem conditionalGenome_mass_bounds (mutationRate : ℝ≥0) {start : State D L n}
    (trace : Trace count start) (waits : Fin count → ℝ) (genome : WholeGenome L n) :
    0 ≤ (conditionalGenomeLaw mutationRate trace waits).mass genome ∧
      (conditionalGenomeLaw mutationRate trace waits).mass genome ≤ 1 := by
  constructor
  · exact (conditionalGenomeLaw mutationRate trace waits).mass_nonneg genome
  · rw [← (conditionalGenomeLaw mutationRate trace waits).mass_sum]
    exact Finset.single_le_sum (fun output _ ↦
      (conditionalGenomeLaw mutationRate trace waits).mass_nonneg output) (Finset.mem_univ genome)

theorem conditionalGenome_mass_integrable (rates : Rates D L) (mutationRate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (genome : WholeGenome L n) :
    Integrable (fun waits ↦ (conditionalGenomeLaw mutationRate trace waits).mass genome)
      (waitingLaw (n := n) rates count) := by
  apply Integrable.of_bound (Measurable.aestronglyMeasurable
    (conditionalGenome_mass_measurable mutationRate trace genome)) 1
  exact Filter.Eventually.of_forall (fun waits ↦ by
    have hb := conditionalGenome_mass_bounds mutationRate trace waits genome
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)

theorem conditionalGenome_expectation_measurable (mutationRate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (readout : WholeGenome L n → ℝ) :
    Measurable (fun waits ↦
      (conditionalGenomeLaw mutationRate trace waits).expectation readout) := by
  apply Finset.measurable_sum
  intro genome _
  exact (conditionalGenome_mass_measurable mutationRate trace genome).mul_const (readout genome)

/-- A trace with incomplete terminal ancestry has zero stopped weight, so the
root draw used to define conditional laws on those traces has no influence. -/
theorem incomplete_trace_weight_zero (rates : Rates D L) {start : State D L n}
    (trace : Trace count start) (hincomplete : (terminal trace).val ≠ ∅) :
    stoppingTraceMass rates start trace = 0 := by
  apply le_antisymm _ (stoppingTraceMass_nonneg rates start trace)
  exact not_lt.mp (fun hpositive ↦
    hincomplete (stoppingTraceMass_pos_terminal rates trace hpositive))

noncomputable def genomeCountMass (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (count : ℕ) (genome : WholeGenome L n) : ℝ :=
  stoppedCountExpectation rates start count
    (fun trace waits ↦ (conditionalGenomeLaw mutationRate trace waits).mass genome)

theorem genomeCountMass_bounds (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (count : ℕ) (genome : WholeGenome L n) :
    0 ≤ genomeCountMass rates start mutationRate count genome ∧
      genomeCountMass rates start mutationRate count genome ≤ completionMass rates start count := by
  simpa only [genomeCountMass, mul_one] using
    stoppedCountExpectation_bounds rates start count
      (fun trace waits ↦ (conditionalGenomeLaw mutationRate trace waits).mass genome)
      (fun trace ↦ conditionalGenome_mass_measurable mutationRate trace genome) 1
      (fun trace ↦ Filter.Eventually.of_forall (fun waits ↦
        conditionalGenome_mass_bounds mutationRate trace waits genome))

/-- Finite genotype marginalization commutes with the timed ancestry integral.
Nonlinear readouts are evaluated on realized genomes before integration. -/
theorem genomeCountMass_expectation (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (count : ℕ) (readout : WholeGenome L n → ℝ) :
    (∑ genome, genomeCountMass rates start mutationRate count genome * readout genome) =
      stoppedCountExpectation rates start count
        (fun trace waits ↦
          (conditionalGenomeLaw mutationRate trace waits).expectation readout) := by
  unfold genomeCountMass stoppedCountExpectation expectation
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro trace _
  rw [integral_finset_sum _ (fun genome _ ↦
    (conditionalGenome_mass_integrable rates mutationRate trace genome).mul_const (readout genome))]
  simp only [integral_mul_const, Finset.mul_sum, mul_assoc]

theorem genomeCountMass_sum (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (count : ℕ) :
    (∑ genome, genomeCountMass rates start mutationRate count genome) =
      completionMass rates start count := by
  simpa only [mul_one, expectation, FiniteReportLaw.mass_sum, stoppedCountExpectation_one] using
    genomeCountMass_expectation rates start mutationRate count (fun _ ↦ 1)

theorem genomeCountMass_summable (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) (genome : WholeGenome L n) :
    Summable (fun count ↦ genomeCountMass rates start mutationRate count genome) := by
  apply (completionMass_hasSum rates deme start hs hsupported hisolated).summable.of_nonneg_of_le
  · intro count
    exact (genomeCountMass_bounds rates start mutationRate count genome).1
  · intro count
    exact (genomeCountMass_bounds rates start mutationRate count genome).2

/-- The complete joint sample-genome law through the isolated ancestral tail.
Its masses depend on demographic rates, recombination, mutation, and the full
linked starting state; no independent-locus ancestry approximation is used. -/
noncomputable def stoppedGenomeLaw (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) : FiniteReportLaw (WholeGenome L n) where
  mass := fun genome ↦ ∑' count, genomeCountMass rates start mutationRate count genome
  mass_nonneg := fun genome ↦ tsum_nonneg (fun count ↦
    (genomeCountMass_bounds rates start mutationRate count genome).1)
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun genome _ ↦
      genomeCountMass_summable rates deme start hs hsupported hisolated mutationRate genome)]
    simp only [genomeCountMass_sum]
    exact (completionMass_hasSum rates deme start hs hsupported hisolated).tsum_eq

/-- Exact expectation of every finite-genome readout under the complete
stopped law, with proved interchange of the count series and genotype sum. -/
theorem stoppedGenome_expectation (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) (readout : WholeGenome L n → ℝ) :
    (stoppedGenomeLaw rates deme start hs hsupported hisolated mutationRate).expectation readout =
      stoppedExpectation rates start
        (fun _ trace waits ↦
          (conditionalGenomeLaw mutationRate trace waits).expectation readout) := by
  unfold expectation stoppedGenomeLaw
  simp only [← tsum_mul_right]
  have hsum (genome : WholeGenome L n) :
      Summable (fun count ↦
        genomeCountMass rates start mutationRate count genome * readout genome) := by
    have h := genomeCountMass_summable rates deme start hs hsupported hisolated mutationRate genome
    exact h.mul_right (readout genome)
  rw [← Summable.tsum_finsetSum (fun genome _ ↦ hsum genome)]
  unfold stoppedExpectation
  apply tsum_congr
  intro count
  exact genomeCountMass_expectation rates start mutationRate count readout

private theorem finite_expectation_bounds (law : FiniteReportLaw (WholeGenome L n))
    (readout : WholeGenome L n → ℝ) (bound : ℝ)
    (hbound : ∀ genome, 0 ≤ readout genome ∧ readout genome ≤ bound) :
    0 ≤ law.expectation readout ∧ law.expectation readout ≤ bound := by
  constructor
  · exact Finset.sum_nonneg (fun genome _ ↦ mul_nonneg (law.mass_nonneg genome) (hbound genome).1)
  · calc
      law.expectation readout ≤ ∑ genome, law.mass genome * bound :=
        Finset.sum_le_sum (fun genome _ ↦
          mul_le_mul_of_nonneg_left (hbound genome).2 (law.mass_nonneg genome))
      _ = bound := by rw [← Finset.sum_mul, FiniteReportLaw.mass_sum, one_mul]

/-- The truncation error for a bounded realized-genome readout is at most its
bound times the exact probability that ancestry remains unfinished. -/
theorem stoppedGenome_truncation (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) (readout : WholeGenome L n → ℝ) (bound : ℝ)
    (hbound : ∀ genome, 0 ≤ readout genome ∧ readout genome ≤ bound) (cutoff : ℕ) :
    let partialSum := ∑ count ∈ Finset.range (cutoff + 1),
      ∑ genome, genomeCountMass rates start mutationRate count genome * readout genome
    0 ≤ FiniteReportLaw.expectation
        (stoppedGenomeLaw rates deme start hs hsupported hisolated mutationRate) readout -
          partialSum ∧
      FiniteReportLaw.expectation
        (stoppedGenomeLaw rates deme start hs hsupported hisolated mutationRate) readout -
          partialSum ≤
          survival rates cutoff start * bound := by
  dsimp only
  simp only [stoppedGenome_expectation, genomeCountMass_expectation]
  exact stoppedExpectation_truncation rates deme start hs hsupported hisolated
    (fun _ trace waits ↦ (conditionalGenomeLaw mutationRate trace waits).expectation readout)
    (fun _ trace ↦ conditionalGenome_expectation_measurable mutationRate trace readout) bound
    (fun _ trace ↦ Filter.Eventually.of_forall (fun waits ↦
      finite_expectation_bounds (conditionalGenomeLaw mutationRate trace waits)
        readout bound hbound))
    cutoff

end Descent.Portability.StoppedGenotypeLaw
