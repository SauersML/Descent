/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralMutationAbsorption

assert_below Descent.Decision Descent.Program

/-!
Existence of the exact joint genome/catalogue law as the limit of the finite
transfer recurrence. The demographic absorption bound proves the probability
coordinates are Cauchy and gives explicit error control for the resulting law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralMutationLimit

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralAbsorptionLaw
open AncestralMutationTransfer AncestralMutationAbsorption FiniteReportLaw
open scoped NNReal

variable {D L n : ℕ}

noncomputable def iterateLaw (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (count : ℕ) (s : State D L n) : FiniteReportLaw (Genome L n) :=
  ((transfer rates mutationRate)^[count]) (fun _ ↦ rootGenomeLaw) s

theorem iterateLaw_boundary (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count : ℕ) :
    iterateLaw (n := n) rates mutationRate count emptyState = rootGenomeLaw := by
  induction count with
  | zero => rfl
  | succ count ih =>
      unfold iterateLaw
      rw [Function.iterate_succ_apply']
      exact transfer_boundary rates mutationRate _ ih

private theorem coordinate_distance {A : Type*} [Fintype A]
    (first second : FiniteReportLaw A) (output : A) :
    |first.mass output - second.mass output| ≤ rowDistance first second :=
  Finset.single_le_sum (fun value (_ : value ∈ Finset.univ) ↦
    abs_nonneg (first.mass value - second.mass value)) (Finset.mem_univ output)

/-- Every pair of sufficiently deep finite calculations differs by at most
the probability that the shared initial proposal block has not completed. -/
theorem iterateLaw_tail_distance (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (start first second : ℕ) (hfirst : start ≤ first) (hsecond : start ≤ second)
    (s : State D L n) :
    rowDistance (iterateLaw rates mutationRate first s) (iterateLaw rates mutationRate second s) ≤
      2 * AncestralMutationAbsorption.survival rates mutationRate start s := by
  obtain ⟨left, rfl⟩ := Nat.exists_eq_add_of_le hfirst
  obtain ⟨right, rfl⟩ := Nat.exists_eq_add_of_le hsecond
  unfold iterateLaw
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  apply iterate_distance_survival rates mutationRate
  exact (iterateLaw_boundary rates mutationRate left).trans
    (iterateLaw_boundary rates mutationRate right).symm

/-- Cauchy convergence of every finite genome probability is derived from
coalescence and mutation-kernel contraction, without a supplied limiting law. -/
theorem coordinate_cauchy (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) (genome : Genome L n) :
    CauchySeq (fun count ↦ (iterateLaw rates mutationRate count s).mass genome) := by
  apply Metric.cauchySeq_iff.mpr
  intro tolerance htolerance
  have hlimit := (AncestralMutationAbsorption.survival_tendsto_zero rates mutationRate
    deme s hs hsupported hisolated).const_mul 2
  have heventually : ∀ᶠ count in Filter.atTop,
      2 * AncestralMutationAbsorption.survival rates mutationRate count s < tolerance := by
    exact hlimit.eventually (gt_mem_nhds (by simpa using htolerance))
  obtain ⟨start, hstart⟩ := heventually.exists
  refine ⟨start, ?_⟩
  intro first hfirst second hsecond
  rw [Real.dist_eq]
  exact ((coordinate_distance _ _ genome).trans
    (iterateLaw_tail_distance rates mutationRate start first second hfirst hsecond s)).trans_lt
      hstart

noncomputable def limitMass (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) (genome : Genome L n) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (coordinate_cauchy rates mutationRate deme s hs hsupported hisolated genome))

theorem tendsto_limitMass (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) (genome : Genome L n) :
    Filter.Tendsto (fun count ↦ (iterateLaw rates mutationRate count s).mass genome)
      Filter.atTop (nhds (limitMass rates mutationRate deme s hs hsupported hisolated genome)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (coordinate_cauchy rates mutationRate deme s hs hsupported hisolated genome))

/-- The constructed infinite-ancestry, infinite-mutation-count limit is a
normalized probability law on finite nucleotide/catalogue/presence reports. -/
noncomputable def limitLaw (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    FiniteReportLaw (Genome L n) where
  mass := limitMass rates mutationRate deme s hs hsupported hisolated
  mass_nonneg := fun genome ↦ ge_of_tendsto
    (tendsto_limitMass rates mutationRate deme s hs hsupported hisolated genome)
      (Filter.Eventually.of_forall (fun count ↦
        (iterateLaw rates mutationRate count s).mass_nonneg genome))
  mass_sum := by
    have hlimit := tendsto_finset_sum Finset.univ (fun genome _ ↦
      tendsto_limitMass rates mutationRate deme s hs hsupported hisolated genome)
    have hsum : (fun count ↦ ∑ genome, (iterateLaw rates mutationRate count s).mass genome) =
        (fun _ : ℕ ↦ (1 : ℝ)) := funext (fun _ ↦ FiniteReportLaw.mass_sum _)
    rw [hsum] at hlimit
    exact tendsto_nhds_unique hlimit tendsto_const_nhds


private theorem distance_tendsto (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (law : FiniteReportLaw (Genome L n)) :
    Filter.Tendsto (fun count ↦ rowDistance law (iterateLaw rates mutationRate count s))
      Filter.atTop (nhds (rowDistance law
        (limitLaw rates mutationRate deme s hs hsupported hisolated))) := by
  apply tendsto_finset_sum
  intro genome _
  exact (tendsto_const_nhds.sub
    (tendsto_limitMass rates mutationRate deme s hs hsupported hisolated genome)).abs

/-- Error of a finite transfer calculation against the constructed exact law. -/
theorem limitLaw_error (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) (count : ℕ) :
    rowDistance (iterateLaw rates mutationRate count s)
        (limitLaw rates mutationRate deme s hs hsupported hisolated) ≤
      2 * AncestralMutationAbsorption.survival rates mutationRate count s := by
  apply le_of_tendsto (distance_tendsto rates mutationRate deme s hs hsupported hisolated _)
  filter_upwards [Filter.eventually_ge_atTop count] with later hlater
  exact iterateLaw_tail_distance rates mutationRate count count later le_rfl hlater s

theorem limitLaw_error_geometric (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) (blocks : ℕ) :
    rowDistance (iterateLaw rates mutationRate (L * n * blocks) s)
        (limitLaw rates mutationRate deme s hs hsupported hisolated) ≤
      2 * AncestralMutationAbsorption.blockSurvivalBound (n := n)
        rates mutationRate deme ^ blocks :=
  (limitLaw_error rates mutationRate deme s hs hsupported hisolated _).trans
    (mul_le_mul_of_nonneg_left (AncestralMutationAbsorption.survival_geometric
      rates mutationRate deme blocks s hs hsupported hisolated) (by norm_num))

/-- Every finite report readout, including nonlinear genotype/catalogue
statistics, has the exact expectation obtained from the constructed limit. -/
theorem limitLaw_expectation_tendsto (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (readout : Genome L n → ℝ) :
    Filter.Tendsto (fun count ↦ (iterateLaw rates mutationRate count s).expectation readout)
      Filter.atTop (nhds
        ((limitLaw rates mutationRate deme s hs hsupported hisolated).expectation readout)) := by
  apply tendsto_finset_sum
  intro genome _
  exact (tendsto_limitMass rates mutationRate deme s hs hsupported hisolated genome).mul_const _


/-- Zero-mass marks are omitted so every continuation carries proved sampled
ancestry and population support, without assigning laws to unreachable states. -/
abbrev PositiveMark (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (s : State D L n) :=
  {mark : Mark s // 0 < (markLaw rates mutationRate s).mass mark}

noncomputable instance positiveMarkFintype (rates : Rates D L)
    (mutationRate : Fin L → ℝ≥0) (s : State D L n) :
    Fintype (PositiveMark rates mutationRate s) := Fintype.ofFinite _

private theorem positiveMark_sum (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) (values : Mark s → ℝ) :
    (∑ mark : PositiveMark rates mutationRate s,
      (markLaw rates mutationRate s).mass mark.val * values mark.val) =
        ∑ mark : Mark s, (markLaw rates mutationRate s).mass mark * values mark := by
  classical
  have hzero : (∑ mark : {mark : Mark s // ¬ 0 < (markLaw rates mutationRate s).mass mark},
      (markLaw rates mutationRate s).mass mark.val * values mark.val) = 0 := by
    apply Finset.sum_eq_zero
    intro mark _
    have hmass := le_antisymm (le_of_not_gt mark.property)
      ((markLaw rates mutationRate s).mass_nonneg mark.val)
    rw [hmass, zero_mul]
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun mark : Mark s ↦ 0 < (markLaw rates mutationRate s).mass mark)
    (fun mark ↦ (markLaw rates mutationRate s).mass mark * values mark)
  rw [hzero, add_zero] at h
  convert h using 1
  congr 1
  ext mark
  simp

noncomputable def positiveMarkLaw (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) : FiniteReportLaw (PositiveMark rates mutationRate s) where
  mass := fun mark ↦ (markLaw rates mutationRate s).mass mark.val
  mass_nonneg := fun mark ↦ mark.property.le
  mass_sum := by
    simpa only [mul_one, FiniteReportLaw.mass_sum] using
      positiveMark_sum rates mutationRate s (fun _ ↦ 1)

private theorem positiveNextComplete (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) (hs : SampleComplete s) (mark : PositiveMark rates mutationRate s) :
    SampleComplete (scanNext s mark.val) := by
  rcases mark with ⟨mark, _⟩
  rcases mark with _ | (event | event)
  · exact hs
  · exact sampleComplete_proposal s hs (some event)
  · exact hs

private theorem positiveNextSupported (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mark : PositiveMark rates mutationRate s) : SupportedAt deme (scanNext s mark.val) := by
  rcases mark with ⟨mark, hpos⟩
  rcases mark with _ | (event | event)
  · exact hsupported
  · have hrate : 0 < eventRate rates s event := by
      change 0 < eventRate rates s event / intensity (n := n) rates mutationRate at hpos
      exact (div_pos_iff_of_pos_right (intensity_pos rates mutationRate)).mp hpos
    exact supportedAt_proposal rates deme hisolated s hsupported (some event)
      (div_pos hrate (dominatingRate_pos rates))
  · exact hsupported

noncomputable def postcomposeMark {s : State D L n} (mark : Mark s)
    (law : FiniteReportLaw (Genome L n)) : FiniteReportLaw (Genome L n) :=
  match mark with
  | none => law
  | some (.inl _) => law
  | some (.inr event) => law.bind (mutationKernel event)

noncomputable def limitMarkLaw (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mark : PositiveMark rates mutationRate s) : FiniteReportLaw (Genome L n) :=
  postcomposeMark mark.val (limitLaw rates mutationRate deme (scanNext s mark.val)
    (positiveNextComplete rates mutationRate s hs mark)
    (positiveNextSupported rates mutationRate deme s hsupported hisolated mark) hisolated)

private theorem transferMark_tendsto (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (mark : PositiveMark rates mutationRate s) (genome : Genome L n) :
    Filter.Tendsto (fun count ↦
      (transferMark (fun state ↦ iterateLaw rates mutationRate count state) s mark.val).mass genome)
      Filter.atTop (nhds ((limitMarkLaw rates mutationRate deme s hs hsupported hisolated mark).mass
        genome)) := by
  have hnext (output : Genome L n) := tendsto_limitMass rates mutationRate deme
    (scanNext s mark.val) (positiveNextComplete rates mutationRate s hs mark)
      (positiveNextSupported rates mutationRate deme s hsupported hisolated mark) hisolated output
  rcases mark with ⟨mark, hpos⟩
  rcases mark with _ | (event | event)
  · exact hnext genome
  · exact hnext genome
  · apply tendsto_finset_sum
    intro input _
    exact (hnext input).mul_const _

/-- A constructed normalized solution to the finite ancestry/mutation
recurrence. Every continuation is at an admissible ancestral configuration;
mutation is right composition by the actual chronological catalogue kernel. -/
theorem limitLaw_fixed (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    limitLaw rates mutationRate deme s hs hsupported hisolated =
      (positiveMarkLaw rates mutationRate s).bind
        (limitMarkLaw rates mutationRate deme s hs hsupported hisolated) := by
  apply FiniteReportLaw.ext
  intro genome
  have hleft := (Filter.tendsto_add_atTop_iff_nat 1).mpr
    (tendsto_limitMass rates mutationRate deme s hs hsupported hisolated genome)
  have hstep (count : ℕ) : (iterateLaw rates mutationRate (count + 1) s).mass genome =
      ∑ mark : PositiveMark rates mutationRate s,
        (positiveMarkLaw rates mutationRate s).mass mark *
          (transferMark (fun state ↦ iterateLaw rates mutationRate count state) s mark.val).mass
            genome := by
    unfold iterateLaw
    rw [Function.iterate_succ_apply']
    exact (positiveMark_sum rates mutationRate s
      (fun mark ↦ (transferMark ((transfer rates mutationRate)^[count]
        (fun _ ↦ rootGenomeLaw)) s mark).mass genome)).symm
  simp_rw [hstep] at hleft
  have hright := tendsto_finset_sum Finset.univ
    (fun (mark : PositiveMark rates mutationRate s) _ ↦
      (transferMark_tendsto rates mutationRate deme s hs hsupported hisolated mark genome).const_mul
        ((positiveMarkLaw rates mutationRate s).mass mark))
  exact tendsto_nhds_unique hleft hright

/-- The constructed solution has the specified completed-ancestry root law. -/
theorem limitLaw_boundary (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0) :
    limitLaw (n := n) rates mutationRate deme emptyState SampleComplete.empty
      (supportedAt_empty deme) hisolated = rootGenomeLaw := by
  apply FiniteReportLaw.ext
  intro genome
  have h := tendsto_limitMass (n := n) rates mutationRate deme emptyState SampleComplete.empty
    (supportedAt_empty deme) hisolated genome
  simp only [iterateLaw_boundary] at h
  exact tendsto_nhds_unique h tendsto_const_nhds


private theorem transferMark_eq_postcompose (family : LawFamily D L n)
    (s : State D L n) (mark : Mark s) :
    transferMark family s mark = postcomposeMark mark (family (scanNext s mark)) := by
  rcases mark with _ | (event | event) <;> rfl

/-- The finite transfer on supported sampled ancestry depends only on other
supported sampled rows. Zero-rate marks impose no equations outside that set. -/
theorem transfer_congr_on_supported (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (first second : LawFamily D L n)
    (heq : ∀ state, SampleComplete state → SupportedAt deme state → first state = second state)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    transfer rates mutationRate first s = transfer rates mutationRate second s := by
  apply FiniteReportLaw.ext
  intro genome
  change (∑ mark, (markLaw rates mutationRate s).mass mark *
    (transferMark first s mark).mass genome) =
      ∑ mark, (markLaw rates mutationRate s).mass mark * (transferMark second s mark).mass genome
  rw [← positiveMark_sum rates mutationRate s (fun mark ↦ (transferMark first s mark).mass genome),
    ← positiveMark_sum rates mutationRate s (fun mark ↦ (transferMark second s mark).mass genome)]
  apply Finset.sum_congr rfl
  intro mark _
  rw [transferMark_eq_postcompose, transferMark_eq_postcompose,
    heq _ (positiveNextComplete rates mutationRate s hs mark)
      (positiveNextSupported rates mutationRate deme s hsupported hisolated mark)]

private theorem iterate_fixed_on_supported (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (family : LawFamily D L n)
    (hfixed : ∀ state, SampleComplete state → SupportedAt deme state →
      transfer rates mutationRate family state = family state)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (count : ℕ) (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    ((transfer rates mutationRate)^[count]) family s = family s := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      exact (transfer_congr_on_supported rates mutationRate deme _ _ ih hisolated
        s hs hsupported).trans (hfixed s hs hsupported)

/-- The constructed law is identified uniquely by the finite transfer equations
and the root boundary. Equations are required only on admissible sampled rows;
no assumptions about unreachable material configurations enter the result. -/
theorem fixed_point_identifies_limit (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (family : LawFamily D L n)
    (hfixed : ∀ state, SampleComplete state → SupportedAt deme state →
      transfer rates mutationRate family state = family state)
    (hboundary : family emptyState = rootGenomeLaw)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    family s = limitLaw rates mutationRate deme s hs hsupported hisolated := by
  have hbound (count : ℕ) : rowDistance (family s) (iterateLaw rates mutationRate count s) ≤
      2 * AncestralMutationAbsorption.survival rates mutationRate count s := by
    have h := iterate_distance_survival rates mutationRate family (fun _ ↦ rootGenomeLaw)
      hboundary count s
    rw [iterate_fixed_on_supported rates mutationRate deme family hfixed hisolated count
      s hs hsupported] at h
    exact h
  have hzero := le_of_tendsto_of_tendsto
    (distance_tendsto rates mutationRate deme s hs hsupported hisolated (family s))
    ((AncestralMutationAbsorption.survival_tendsto_zero rates mutationRate deme s hs hsupported
      hisolated).const_mul 2) (Filter.Eventually.of_forall hbound)
  apply rowDistance_eq_zero
  exact le_antisymm (by simpa using hzero) (rowDistance_nonneg _ _)

end Descent.Portability.AncestralMutationLimit
