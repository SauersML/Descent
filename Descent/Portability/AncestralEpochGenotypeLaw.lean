/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.StoppedGenotypeReadiness

assert_below Descent.Decision Descent.Program

/-!
Whole-genome continuation through finite demographic epochs. The older
continuation can already correlate loci through linked ancestry. Each younger
interval applies independent site mutation kernels conditional on that entire
older genome; it does not replace the continuation by independent marginals.

Admissible continuations take the proved SampleComplete invariant explicitly.
This allows the completed ancestral tail to be composed without assigning an
arbitrary substitute law to inadmissible ancestry states.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralEpochGenotypeLaw

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralAbsorptionLaw AncestralEpochLaw TimedAncestralLaw
open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue
open InterleavedMutationMeasurability StoppedGenotypeLaw MeasureTheory ProbabilityTheory
open scoped NNReal

variable {D L n count : ℕ}

abbrev Continuation (D L n : ℕ) :=
  (state : State D L n) → SampleComplete state → FiniteReportLaw (WholeGenome L n)

/-- Conditional site mutation independence is applied to a fixed whole genome,
so existing dependence between loci in the older law is preserved by binding. -/
noncomputable def intervalGenomeKernel (state : State D L n) (mutationRate : ℝ≥0)
    (wait : ℝ) (genome : WholeGenome L n) : FiniteReportLaw (WholeGenome L n) where
  mass := fun target ↦ ∏ locus,
    (stateIntervalLaw state locus mutationRate wait (genome locus)).mass (target locus)
  mass_nonneg := fun target ↦ Finset.prod_nonneg (fun locus _ ↦
    (stateIntervalLaw state locus mutationRate wait (genome locus)).mass_nonneg (target locus))
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

theorem intervalGenome_mass_measurable (state : State D L n) (mutationRate : ℝ≥0)
    (genome target : WholeGenome L n) :
    Measurable (fun wait ↦ (intervalGenomeKernel state mutationRate wait genome).mass target) := by
  change Measurable (fun wait ↦ ∏ locus,
    (stateIntervalLaw state locus mutationRate wait (genome locus)).mass (target locus))
  apply Finset.measurable_prod
  intro locus _
  exact stateInterval_mass_measurable state locus mutationRate (genome locus) (target locus)

/-- Compose an older whole-genome law through every interval of one marked
epoch. The final interval after the last proposal is retained. -/
noncomputable def conditionalEpochLaw (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) : {count : ℕ} → {start : State D L n} →
      Trace count start → SampleComplete start → ℝ → (Fin count → ℝ) →
        FiniteReportLaw (WholeGenome L n)
  | 0, start, _, hs, duration, _ =>
      (continuation start hs).bind (intervalGenomeKernel start mutationRate duration)
  | _count + 1, start, ⟨event, rest⟩, hs, duration, times =>
      (conditionalEpochLaw continuation mutationRate rest (sampleComplete_proposal start hs event)
        (duration - times 0) (fun index ↦ times index.succ - times 0)).bind
          (intervalGenomeKernel start mutationRate (times 0))

theorem conditionalEpoch_mass_measurable (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) {start : State D L n} (trace : Trace count start)
    (hs : SampleComplete start) (target : WholeGenome L n) :
    Measurable (fun input : ℝ × (Fin count → ℝ) ↦
      (conditionalEpochLaw continuation mutationRate trace hs input.1 input.2).mass target) := by
  induction count generalizing start target with
  | zero =>
      apply bind_mass_measurable
      · intro genome
        exact measurable_const
      · intro genome output
        exact (intervalGenome_mass_measurable start mutationRate genome output).comp measurable_fst
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      have hshift : Measurable (fun input : ℝ × (Fin (count + 1) → ℝ) ↦
          (input.1 - input.2 0, fun index : Fin count ↦ input.2 index.succ - input.2 0)) := by
        apply Measurable.prodMk
        · exact measurable_fst.sub ((measurable_pi_apply 0).comp measurable_snd)
        · apply measurable_pi_lambda
          intro index
          exact ((measurable_pi_apply index.succ).comp measurable_snd).sub
            ((measurable_pi_apply 0).comp measurable_snd)
      apply bind_mass_measurable
      · intro genome
        exact (ih rest (sampleComplete_proposal start hs event) genome).comp hshift
      · intro genome output
        exact (intervalGenome_mass_measurable start mutationRate genome output).comp
          ((measurable_pi_apply 0).comp measurable_snd)

theorem conditionalEpoch_times_measurable (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) {start : State D L n} (trace : Trace count start)
    (hs : SampleComplete start) (duration : ℝ≥0) (target : WholeGenome L n) :
    Measurable (fun times ↦
      (conditionalEpochLaw continuation mutationRate trace hs duration times).mass target) :=
  (conditionalEpoch_mass_measurable continuation mutationRate trace hs target).comp
    (measurable_const.prodMk measurable_id)

theorem genome_mass_bounds (law : FiniteReportLaw (WholeGenome L n)) (genome : WholeGenome L n) :
    0 ≤ law.mass genome ∧ law.mass genome ≤ 1 := by
  constructor
  · exact law.mass_nonneg genome
  · rw [← law.mass_sum]
    exact Finset.single_le_sum (fun output _ ↦ law.mass_nonneg output) (Finset.mem_univ genome)

theorem conditionalEpoch_mass_integrable (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) {start : State D L n} (trace : Trace count start)
    (hs : SampleComplete start) (duration : ℝ≥0) (target : WholeGenome L n) :
    Integrable (fun times ↦
      (conditionalEpochLaw continuation mutationRate trace hs duration times).mass target)
      (timeLaw duration count) :=
  time_integrable duration _
    (conditionalEpoch_times_measurable continuation mutationRate trace hs duration target) 1
    (Filter.Eventually.of_forall (fun times ↦ genome_mass_bounds
      (conditionalEpochLaw continuation mutationRate trace hs duration times) target))

noncomputable def epochCountMass (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) (count : ℕ) (genome : WholeGenome L n) : ℝ :=
  countExpectation rates start duration count
    (fun trace times ↦ FiniteReportLaw.mass
      (conditionalEpochLaw continuation mutationRate trace hs duration times) genome)

theorem epochCountMass_bounds (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) (count : ℕ) (genome : WholeGenome L n) :
    0 ≤ epochCountMass rates continuation mutationRate start hs duration count genome ∧
      epochCountMass rates continuation mutationRate start hs duration count genome ≤ 1 :=
  countExpectation_bounds rates start duration count _
    (fun trace ↦
      conditionalEpoch_times_measurable continuation mutationRate trace hs duration genome)
    1 (fun trace ↦ Filter.Eventually.of_forall (fun times ↦ genome_mass_bounds
      (conditionalEpochLaw continuation mutationRate trace hs duration times) genome))

theorem epochCountMass_expectation (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) (count : ℕ) (readout : WholeGenome L n → ℝ) :
    (∑ genome, epochCountMass rates continuation mutationRate start hs duration count genome *
      readout genome) = countExpectation rates start duration count
        (fun trace times ↦ FiniteReportLaw.expectation
          (conditionalEpochLaw continuation mutationRate trace hs duration times) readout) := by
  unfold epochCountMass countExpectation expectation
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro trace _
  have hint (genome : WholeGenome L n) : Integrable
      (fun times ↦
        (conditionalEpochLaw continuation mutationRate trace hs duration times).mass genome *
          readout genome) (timeLaw duration count) := by
    have h := conditionalEpoch_mass_integrable continuation mutationRate trace hs duration genome
    exact h.mul_const (readout genome)
  rw [integral_finset_sum _ (fun genome _ ↦ hint genome)]
  simp only [integral_mul_const, Finset.mul_sum, mul_assoc]

theorem epochCountMass_sum (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) (count : ℕ) :
    (∑ genome, epochCountMass rates continuation mutationRate start hs duration count genome) =
      1 := by
  simpa only [mul_one, expectation, FiniteReportLaw.mass_sum, countExpectation_one] using
    epochCountMass_expectation rates continuation mutationRate start hs duration count (fun _ ↦ 1)

theorem epoch_coordinate_summable (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) (genome : WholeGenome L n) :
    Summable (fun count ↦ poissonPMFReal (poissonParameter (n := n) rates duration) count *
      epochCountMass rates continuation mutationRate start hs duration count genome) := by
  apply (poissonPMFRealSum _).summable.of_nonneg_of_le
  · intro count
    exact mul_nonneg poissonPMFReal_nonneg
      (epochCountMass_bounds rates continuation mutationRate start hs duration count genome).1
  · intro count
    exact mul_le_of_le_one_right poissonPMFReal_nonneg
      (epochCountMass_bounds rates continuation mutationRate start hs duration count genome).2

/-- Exact finite-epoch transform of an older linked whole-genome law. Both
ancestral marks and inter-proposal times are integrated, including mutations
in the interval between the last proposal and the older epoch boundary. -/
noncomputable def epochGenomeLaw (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) : FiniteReportLaw (WholeGenome L n) where
  mass := fun genome ↦ ∑' count, poissonPMFReal (poissonParameter (n := n) rates duration) count *
    epochCountMass rates continuation mutationRate start hs duration count genome
  mass_nonneg := fun genome ↦ tsum_nonneg (fun count ↦ mul_nonneg poissonPMFReal_nonneg
    (epochCountMass_bounds rates continuation mutationRate start hs duration count genome).1)
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun genome _ ↦
      epoch_coordinate_summable rates continuation mutationRate start hs duration genome)]
    simp only [← Finset.mul_sum, epochCountMass_sum, mul_one]
    exact (poissonPMFRealSum _).tsum_eq

theorem epochGenome_expectation (rates : Rates D L) (continuation : Continuation D L n)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (duration : ℝ≥0) (readout : WholeGenome L n → ℝ) :
    (epochGenomeLaw rates continuation mutationRate start hs duration).expectation readout =
      timedExpectation rates start duration
        (fun _ trace times ↦ FiniteReportLaw.expectation
          (conditionalEpochLaw continuation mutationRate trace hs duration times) readout) := by
  unfold expectation epochGenomeLaw
  simp only [← tsum_mul_right]
  have hsum (genome : WholeGenome L n) :
      Summable (fun count ↦
        (poissonPMFReal (poissonParameter (n := n) rates duration) count *
          epochCountMass rates continuation mutationRate start hs duration count genome) *
            readout genome) := by
    have h := epoch_coordinate_summable rates continuation mutationRate start hs duration genome
    exact h.mul_right (readout genome)
  rw [← Summable.tsum_finsetSum (fun genome _ ↦ hsum genome)]
  unfold timedExpectation
  apply tsum_congr
  intro count
  calc
    _ = poissonPMFReal (poissonParameter (n := n) rates duration) count *
        ∑ genome, epochCountMass rates continuation mutationRate start hs duration count genome *
          readout genome := by simp only [Finset.mul_sum, mul_assoc]
    _ = _ := congrArg
      (fun value ↦ poissonPMFReal (poissonParameter (n := n) rates duration) count * value)
      (epochCountMass_expectation rates continuation mutationRate start hs duration count readout)

/-- Backward demographic instructions become an older-to-younger mutation
continuation. Relocations are instantaneous and preserve descendant material. -/
noncomputable def historyGenomeLaw (mutationRate : ℝ≥0) :
    List (Instruction D L) → Continuation D L n → Continuation D L n
  | [], continuation => continuation
  | .epoch rates duration :: rest, continuation => fun start hs ↦
      epochGenomeLaw rates (historyGenomeLaw mutationRate rest continuation)
        mutationRate start hs duration
  | .relocate destination :: rest, continuation => fun start hs ↦
      historyGenomeLaw mutationRate rest continuation (relabelDemes start destination)
        (sampleComplete_relabel start hs destination)

theorem historyGenome_epoch_expectation (mutationRate : ℝ≥0)
    (rates : Rates D L) (duration : ℝ≥0) (rest : List (Instruction D L))
    (continuation : Continuation D L n) (start : State D L n) (hs : SampleComplete start)
    (readout : WholeGenome L n → ℝ) :
    FiniteReportLaw.expectation
      (historyGenomeLaw mutationRate (.epoch rates duration :: rest) continuation start hs)
        readout = timedExpectation rates start duration
        (fun _ trace times ↦ FiniteReportLaw.expectation
          (conditionalEpochLaw (historyGenomeLaw mutationRate rest continuation)
            mutationRate trace hs duration times) readout) :=
  epochGenome_expectation rates (historyGenomeLaw mutationRate rest continuation)
    mutationRate start hs duration readout

/-- Merge all remaining lineages into the final isolated ancestral population,
then use its proved complete stopped genotype law. The merge is explicit. -/
noncomputable def mergingTailContinuation (rates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, rates.migration ancestor destination = 0)
    (mutationRate : ℝ≥0) : Continuation D L n := fun start hs ↦
  stoppedGenomeLaw rates ancestor (relabelDemes start (fun _ ↦ ancestor))
    (sampleComplete_relabel start hs (fun _ ↦ ancestor)) (supportedAt_relabel ancestor start)
    hisolated mutationRate

/-- Full joint genome law for a finite piecewise-constant demographic history
followed by an explicit merge and an isolated ancestral tail. -/
noncomputable def completeDemographyLaw (instructions : List (Instruction D L))
    (finalRates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, finalRates.migration ancestor destination = 0)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start) :
    FiniteReportLaw (WholeGenome L n) :=
  historyGenomeLaw mutationRate instructions
    (mergingTailContinuation finalRates ancestor hisolated mutationRate) start hs

theorem mergingTail_expectation (rates : Rates D L) (ancestor : Fin D)
    (hisolated : ∀ destination, rates.migration ancestor destination = 0)
    (mutationRate : ℝ≥0) (start : State D L n) (hs : SampleComplete start)
    (readout : WholeGenome L n → ℝ) :
    (mergingTailContinuation rates ancestor hisolated mutationRate start hs).expectation readout =
      StoppedAncestralTiming.stoppedExpectation rates (relabelDemes start (fun _ ↦ ancestor))
        (fun _ trace waits ↦ (conditionalGenomeLaw mutationRate trace waits).expectation readout) :=
  stoppedGenome_expectation rates ancestor (relabelDemes start (fun _ ↦ ancestor))
    (sampleComplete_relabel start hs (fun _ ↦ ancestor)) (supportedAt_relabel ancestor start)
    hisolated mutationRate readout

end Descent.Portability.AncestralEpochGenotypeLaw
