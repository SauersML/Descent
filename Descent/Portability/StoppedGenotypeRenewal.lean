/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.WholeGenomeMutationRace

assert_below Descent.Decision Descent.Program

/-!
Renewal of the stopped genotype law at the first backward ancestry proposal.
The first waiting increment is integrated independently of the older linked
trace, while the full genome mutation kernel retains that shared increment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.StoppedGenotypeRenewal

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw
open AncestralAbsorptionLaw StoppedAncestralTiming StoppedGenotypeLaw
open AncestralEpochGenotypeLaw WholeGenomeMutationSemigroup WholeGenomeMutationRace
open FiniteReportLaw MeasureTheory ProbabilityTheory
open scoped NNReal

variable {D L n count : ℕ}

/-- The first proposal wait and the vector of all older waits are independent. -/
theorem waiting_integral_split (rates : Rates D L) (count : ℕ)
    (first : ℝ → ℝ) (rest : (Fin count → ℝ) → ℝ) :
    (∫ waits, rest (fun index ↦ waits index.succ) * first (waits 0)
      ∂waitingLaw (n := n) rates (count + 1)) =
      (∫ waits, rest waits ∂waitingLaw (n := n) rates count) *
        ∫ wait, first wait ∂proposalWait (n := n) rates := by
  unfold waitingLaw
  rw [← ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (count + 1) ↦ proposalWait (n := n) rates) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
  rw [show (fun x : ℝ × (Fin count → ℝ) ↦ rest x.2 * first x.1) =
    (fun x ↦ first x.1 * rest x.2) by funext x; ring]
  rw [integral_prod_mul, mul_comm]

/-- The product of sitewise backward recursions is exactly a whole-genome bind. -/
theorem conditionalGenome_succ (mutationRate : ℝ≥0) (start : State D L n)
    (event : Option (Channel start)) (rest : Trace count (proposalNext start event))
    (waits : Fin (count + 1) → ℝ) :
    conditionalGenomeLaw (count := count + 1) (start := start) mutationRate
      (⟨event, rest⟩ : Trace (count + 1) start) waits =
      (conditionalGenomeLaw mutationRate rest (fun index ↦ waits index.succ)).bind
        (intervalGenomeKernel start mutationRate (waits 0)) := by
  exact (independent_bind (I := Fin L) (S := OrderedMutationCatalogue.SiteState n)
    (fun locus ↦ conditionalSiteLaw locus mutationRate rest (fun index ↦ waits index.succ))
    (fun locus ↦ stateIntervalLaw start locus mutationRate (waits 0))).symm

/-- The complete conditional genome integral splits at the youngest interval. -/
theorem conditionalGenome_integral_succ (rates : Rates D L) (mutationRate : ℝ≥0)
    (start : State D L n) (event : Option (Channel start))
    (rest : Trace count (proposalNext start event)) (target : WholeGenome L n) :
    (∫ waits, (conditionalGenomeLaw (count := count + 1) (start := start) mutationRate
      (⟨event, rest⟩ : Trace (count + 1) start) waits).mass target
        ∂waitingLaw (n := n) rates (count + 1)) =
      ∑ source, (∫ waits, (conditionalGenomeLaw mutationRate rest waits).mass source
        ∂waitingLaw (n := n) rates count) *
          (genomeWaitLaw (dominatingRate (n := n) rates) (dominatingRate_pos rates)
            start mutationRate source).mass target := by
  simp_rw [conditionalGenome_succ]
  change (∫ waits, ∑ source,
    (conditionalGenomeLaw mutationRate rest (fun index ↦ waits index.succ)).mass source *
      (intervalGenomeKernel start mutationRate (waits 0) source).mass target
        ∂waitingLaw (n := n) rates (count + 1)) = _
  have hint (source : WholeGenome L n) : Integrable (fun waits : Fin (count + 1) → ℝ ↦
      (conditionalGenomeLaw mutationRate rest (fun index ↦ waits index.succ)).mass source *
        (intervalGenomeKernel start mutationRate (waits 0) source).mass target)
          (waitingLaw (n := n) rates (count + 1)) := by
    have htail : Measurable (fun waits : Fin (count + 1) → ℝ ↦
        fun index : Fin count ↦ waits index.succ) :=
      measurable_pi_lambda _ (fun index ↦ measurable_pi_apply index.succ)
    have hm1 := (conditionalGenome_mass_measurable mutationRate rest source).comp htail
    have hhead : Measurable (fun waits : Fin (count + 1) → ℝ ↦ waits 0) :=
      measurable_pi_apply (0 : Fin (count + 1))
    have hm2 := (intervalGenome_mass_measurable start mutationRate source target).comp hhead
    apply Integrable.of_bound (hm1.mul hm2).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro waits
    have hfirst := conditionalGenome_mass_bounds mutationRate rest
      (fun index ↦ waits index.succ) source
    have hsecond := genome_mass_bounds
      (intervalGenomeKernel start mutationRate (waits 0) source) target
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfirst.1 hsecond.1)]
    exact mul_le_one₀ hfirst.2 hsecond.1 hsecond.2
  rw [integral_finset_sum _ (fun source _ ↦ hint source)]
  apply Finset.sum_congr rfl
  intro source _
  rw [waiting_integral_split (n := n) rates count
    (fun wait ↦ (intervalGenomeKernel start mutationRate wait source).mass target)
    (fun waits ↦ (conditionalGenomeLaw mutationRate rest waits).mass source)]
  congr 1
  exact intervalGenome_expMeasure _ (dominatingRate_pos rates) start mutationRate source target

theorem stoppingTraceMass_succ (rates : Rates D L) (start : State D L n)
    (event : Option (Channel start)) (rest : Trace count (proposalNext start event)) :
    stoppingTraceMass (count := count + 1) rates start (⟨event, rest⟩ : Trace (count + 1) start) =
      unfinished start * (proposalLaw rates start).mass event *
        stoppingTraceMass rates (proposalNext start event) rest := by
  simp only [stoppingTraceMass, traceMass, stoppingIndicator]
  ring

/-- Exact count-by-count renewal, before summing the unbounded stopping index. -/
theorem genomeCountMass_succ (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (count : ℕ) (target : WholeGenome L n) :
    genomeCountMass rates start mutationRate (count + 1) target =
      unfinished start * ∑ event : Option (Channel start), (proposalLaw rates start).mass event *
        ∑ source, genomeCountMass rates (proposalNext start event) mutationRate count source *
          (genomeWaitLaw (dominatingRate (n := n) rates) (dominatingRate_pos rates)
            start mutationRate source).mass target := by
  unfold genomeCountMass stoppedCountExpectation
  change (∑ trace : (event : Option (Channel start)) × Trace count (proposalNext start event),
    stoppingTraceMass (count := count + 1) rates start trace * ∫ waits,
      FiniteReportLaw.mass
        (conditionalGenomeLaw (count := count + 1) (start := start) mutationRate trace waits) target
        ∂waitingLaw (n := n) rates (count + 1)) = _
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro event _
  simp_rw [stoppingTraceMass_succ, conditionalGenome_integral_succ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro rest _
  ring

/-- First-completion coefficients are summable even at states that need not
complete almost surely. Normalization is a separate absorption theorem. -/
theorem completionMass_summable_any (rates : Rates D L) (start : State D L n) :
    Summable (completionMass rates start) := by
  apply summable_of_sum_range_le (c := 1) (completionMass_nonneg rates start)
  intro cutoff
  cases cutoff with
  | zero => simp
  | succ cutoff =>
      rw [completionMass_partial_sum]
      linarith [survival_nonneg rates cutoff start]

theorem genomeCountMass_summable_any (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (target : WholeGenome L n) :
    Summable (fun count ↦ genomeCountMass rates start mutationRate count target) := by
  exact (completionMass_summable_any rates start).of_nonneg_of_le
    (fun count ↦ (genomeCountMass_bounds rates start mutationRate count target).1)
    (fun count ↦ (genomeCountMass_bounds rates start mutationRate count target).2)

/-- The stopped mass on all material states. On admissible isolated states
this is the mass of the previously constructed normalized stoppedGenomeLaw. -/
noncomputable def stoppedMass (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (target : WholeGenome L n) : ℝ :=
  ∑' count, genomeCountMass rates start mutationRate count target

theorem genomeCountMass_zero (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (target : WholeGenome L n) :
    genomeCountMass rates start mutationRate 0 target =
      (1 - unfinished start) * AncestralMutationTransfer.rootGenomeLaw.mass target := by
  rw [← root_product_eq_transfer]
  simp [genomeCountMass, stoppedCountExpectation, stoppingTraceMass, traceMass,
    stoppingIndicator, conditionalGenomeLaw, conditionalSiteLaw, independentLaw, Trace]

/-- Exact renewal after summing every possible ancestral stopping index.
The formula applies on all material states; only completed histories enter. -/
theorem stoppedMass_renewal (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (target : WholeGenome L n) :
    stoppedMass rates start mutationRate target =
      (1 - unfinished start) * AncestralMutationTransfer.rootGenomeLaw.mass target +
        unfinished start * ∑ event : Option (Channel start), (proposalLaw rates start).mass event *
          ∑ source, stoppedMass rates (proposalNext start event) mutationRate source *
            (genomeWaitLaw (dominatingRate (n := n) rates) (dominatingRate_pos rates)
              start mutationRate source).mass target := by
  unfold stoppedMass
  rw [(genomeCountMass_summable_any rates start mutationRate target).tsum_eq_zero_add,
    genomeCountMass_zero]
  congr 1
  simp_rw [genomeCountMass_succ]
  rw [tsum_mul_left]
  congr 1
  have hs (event : Option (Channel start)) (source : WholeGenome L n) :
      Summable (fun count ↦ genomeCountMass rates (proposalNext start event) mutationRate
        count source * (genomeWaitLaw (dominatingRate (n := n) rates) (dominatingRate_pos rates)
          start mutationRate source).mass target) :=
    (genomeCountMass_summable_any rates (proposalNext start event) mutationRate source).mul_right _
  rw [Summable.tsum_finsetSum (fun event _ ↦
    (summable_sum (fun source _ ↦ hs event source)).mul_left
      ((proposalLaw rates start).mass event))]
  apply Finset.sum_congr rfl
  intro event _
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun source _ ↦ hs event source)]
  simp only [tsum_mul_right]

open ExponentialPoissonRace

/-- The geometric waiting kernel satisfies its resolvent equation on arbitrary
real rows; normalization of the input row is unnecessary. -/
theorem race_row_first_step {S : Type*} [Fintype S] (ancestry : ℝ) (ha : 0 < ancestry)
    (mutation : ℝ≥0) (kernel : S → FiniteReportLaw S) (row : S → ℝ) (target : S) :
    (∑ source, row source * (raceKernelLaw ancestry ha mutation kernel source).mass target) =
      (ancestry / (ancestry + (mutation : ℝ))) * row target +
        ((mutation : ℝ) / (ancestry + (mutation : ℝ))) *
          ∑ source, (∑ older, row older *
            (raceKernelLaw ancestry ha mutation kernel older).mass source) *
              (kernel source).mass target := by
  classical
  conv_lhs =>
    arg 2
    ext source
    rw [raceKernel_first_step]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp [pointMass, mul_ite, mul_comm]
  · simp only [FiniteReportLaw.bind]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro source _
    apply Finset.sum_congr rfl
    intro older _
    ring

noncomputable def olderMass (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (target : WholeGenome L n) : ℝ :=
  ∑ event : Option (Channel start), (proposalLaw rates start).mass event *
    stoppedMass rates (proposalNext start event) mutationRate target

theorem stoppedMass_eq_older_wait (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (hactive : start.val ≠ ∅) (target : WholeGenome L n) :
    stoppedMass rates start mutationRate target =
      ∑ source, olderMass rates start mutationRate source *
        (genomeWaitLaw (dominatingRate (n := n) rates) (dominatingRate_pos rates)
          start mutationRate source).mass target := by
  rw [stoppedMass_renewal]
  simp only [unfinished, if_neg hactive, sub_self, zero_mul, one_mul, zero_add,
    olderMass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro event _
  ring

/-- Mutation and ancestry balance derived from the timed stopped law, with
no unproved recurrence hypothesis. This is the equation to match to transfer. -/
theorem stoppedMass_proposal_balance (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (hactive : start.val ≠ ∅) (target : WholeGenome L n) :
    dominatingRate (n := n) rates *
        (olderMass rates start mutationRate target - stoppedMass rates start mutationRate target) +
      (proposalRate (siteProposalRates start mutationRate) : ℝ) *
        ((∑ source, stoppedMass rates start mutationRate source *
          (globalKernel (siteProposalRates start mutationRate)
            (siteProposalKernels start mutationRate) source).mass target) -
              stoppedMass rates start mutationRate target) = 0 := by
  have hrow (output : WholeGenome L n) :=
    stoppedMass_eq_older_wait rates start mutationRate hactive output
  have h := race_row_first_step (dominatingRate (n := n) rates) (dominatingRate_pos rates)
    (proposalRate (siteProposalRates start mutationRate))
    (globalKernel (siteProposalRates start mutationRate) (siteProposalKernels start mutationRate))
    (olderMass rates start mutationRate) target
  change (∑ source, olderMass rates start mutationRate source *
      (genomeWaitLaw _ _ start mutationRate source).mass target) =
    _ + _ * ∑ source, (∑ older, olderMass rates start mutationRate older *
      (genomeWaitLaw _ _ start mutationRate older).mass source) * _ at h
  simp_rw [← hrow] at h
  have hp : dominatingRate (n := n) rates +
      (proposalRate (siteProposalRates start mutationRate) : ℝ) ≠ 0 :=
    ne_of_gt (add_pos (dominatingRate_pos rates) (proposalRate_pos _))
  field_simp [hp] at h
  nlinarith

theorem stoppedMass_boundary (rates : Rates D L) (mutationRate : ℝ≥0)
    (target : WholeGenome L n) :
    stoppedMass rates emptyState mutationRate target =
      AncestralMutationTransfer.rootGenomeLaw.mass target := by
  rw [stoppedMass_renewal]
  simp [unfinished, emptyState]

theorem stoppedMass_eq_mass (rates : Rates D L) (deme : Fin D) (start : State D L n)
    (hs : SampleComplete start) (hsupported : SupportedAt deme start)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mutationRate : ℝ≥0) (target : WholeGenome L n) :
    stoppedMass rates start mutationRate target =
      (stoppedGenomeLaw rates deme start hs hsupported hisolated mutationRate).mass target := rfl

open FiniteProductExponential InterleavedMutationExponential
open InterleavedMutationMeasurability

theorem genomeGenerator_eq_proposal (state : State D L n) (rate : ℝ≥0) :
    genomeGenerator state rate = (proposalRate (siteProposalRates state rate) : ℝ) •
      (kernelMatrix (globalKernel (siteProposalRates state rate)
        (siteProposalKernels state rate)) - 1) := by
  rw [global_generator]
  unfold genomeGenerator siteProposalRates siteProposalKernels
  simp_rw [generator_matrix]

/-- The full finite mutation generator balances the actual ancestral renewal. -/
theorem stoppedMass_generator_balance (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (hactive : start.val ≠ ∅) (target : WholeGenome L n) :
    dominatingRate (n := n) rates *
        (olderMass rates start mutationRate target - stoppedMass rates start mutationRate target) +
      (∑ source, stoppedMass rates start mutationRate source *
        genomeGenerator start mutationRate source target) = 0 := by
  classical
  have heq : (∑ source, stoppedMass rates start mutationRate source *
      genomeGenerator start mutationRate source target) =
      (proposalRate (siteProposalRates start mutationRate) : ℝ) *
        ((∑ source, stoppedMass rates start mutationRate source *
          (globalKernel (siteProposalRates start mutationRate)
            (siteProposalKernels start mutationRate) source).mass target) -
              stoppedMass rates start mutationRate target) := by
    rw [genomeGenerator_eq_proposal]
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, kernelMatrix,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_sub, mul_comm, mul_left_comm]
  rw [heq]
  exact stoppedMass_proposal_balance rates start mutationRate hactive target

/-- Ancestral null proposals also cancel, leaving only physical ancestry
channels and the exact whole-genome mutation generator. -/
theorem stoppedMass_event_balance (rates : Rates D L) (start : State D L n)
    (mutationRate : ℝ≥0) (hactive : start.val ≠ ∅) (target : WholeGenome L n) :
    (∑ event : Channel start, eventRate rates start event *
        (stoppedMass rates (nextState start event) mutationRate target -
          stoppedMass rates start mutationRate target)) +
      (∑ source, stoppedMass rates start mutationRate source *
        genomeGenerator start mutationRate source target) = 0 := by
  have h := proposal_generator rates start
    (fun state ↦ stoppedMass rates state mutationRate target)
  have ho : (proposalKernel rates start).expectation
      (fun state ↦ stoppedMass rates state mutationRate target) =
        olderMass rates start mutationRate target := by
    rw [proposalKernel, expectation_pushforward]
    rfl
  rw [ho] at h
  rw [← h]
  exact stoppedMass_generator_balance rates start mutationRate hactive target

end Descent.Portability.StoppedGenotypeRenewal
