/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralCladePartition
import Descent.Portability.AncestralAbsorptionLaw
import Descent.Portability.OrderedMutationCatalogue

assert_below Descent.Decision Descent.Program

/-!
A finite transfer operator combines demographic ancestry and chronological
mutation on the whole finite genome. Backwards ancestry scanning composes a
younger mutation on the right of the older report law. The state retains site
presence and allele-discovery order, rather than only nucleotide endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralMutationTransfer

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralBranchExposure
open GenealogyGenotypeLaw OrderedMutationCatalogue FiniteReportLaw
open scoped NNReal

variable {D L n : ℕ}

abbrev Genome (L n : ℕ) := Fin L → SiteState n

/-- Each retained locus on each active lineage has its own mutation clock. -/
abbrev MutationChannel (s : State D L n) :=
  {pair : Lineage D L n × Fin L // pair.1 ∈ s.val ∧
    (locusDescendants pair.1.2 pair.2).Nonempty}

noncomputable instance mutationChannelFintype (s : State D L n) :
    Fintype (MutationChannel s) := Fintype.ofFinite _

noncomputable def mutationBranch {s : State D L n} (mark : MutationChannel s) : Branch n :=
  { descendants := locusDescendants mark.val.1.2 mark.val.2
    representative := (locusDescendants mark.val.1.2 mark.val.2).min' mark.property.2
    representative_mem := Finset.min'_mem _ mark.property.2
    exposure := 1 }

/-- Update the selected site and preserve every other site's catalogue and bases. -/
noncomputable def mutationKernel {s : State D L n} (mark : MutationChannel s)
    (genome : Genome L n) : FiniteReportLaw (Genome L n) :=
  (OrderedMutationCatalogue.mutationKernel (mutationBranch mark) (genome mark.val.2)).pushforward
    (fun site ↦ Function.update genome mark.val.2 site)

noncomputable def mutationIntensity (mutationRate : Fin L → ℝ≥0) (s : State D L n) : ℝ :=
  ∑ mark : MutationChannel s, (mutationRate mark.val.2 : ℝ)

theorem mutationIntensity_nonneg (mutationRate : Fin L → ℝ≥0) (s : State D L n) :
    0 ≤ mutationIntensity mutationRate s :=
  Finset.sum_nonneg (fun mark _ ↦ (mutationRate mark.val.2).property)

noncomputable def totalIntensity (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) : ℝ := totalRate rates s + mutationIntensity mutationRate s

theorem totalIntensity_nonneg (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) : 0 ≤ totalIntensity rates mutationRate s :=
  add_nonneg (totalRate_nonneg rates s) (mutationIntensity_nonneg mutationRate s)

/-- A single finite dominating rate for every joint ancestry/mutation state. -/
noncomputable def intensity (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) : ℝ :=
  1 + ∑ s : State D L n, totalIntensity rates mutationRate s

theorem intensity_pos (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) :
    0 < intensity (n := n) rates mutationRate := by
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun (s : State D L n) _ ↦ totalIntensity_nonneg rates mutationRate s)
  unfold intensity
  linarith

theorem totalIntensity_le (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) : totalIntensity rates mutationRate s ≤
      intensity (n := n) rates mutationRate := by
  have h := Finset.single_le_sum (fun (state : State D L n) (_ : state ∈ Finset.univ) ↦
    totalIntensity_nonneg rates mutationRate state) (Finset.mem_univ s)
  unfold intensity
  linarith

abbrev Mark (s : State D L n) := Option (Channel s ⊕ MutationChannel s)

noncomputable def markLaw (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) : FiniteReportLaw (Mark s) where
  mass := fun mark ↦ match mark with
    | none => 1 - totalIntensity rates mutationRate s / intensity (n := n) rates mutationRate
    | some (.inl event) => eventRate rates s event / intensity (n := n) rates mutationRate
    | some (.inr event) => (mutationRate event.val.2 : ℝ) / intensity (n := n) rates mutationRate
  mass_nonneg := by
    intro mark
    rcases mark with _ | (event | event)
    · exact sub_nonneg.mpr ((div_le_one (intensity_pos rates mutationRate)).mpr
        (totalIntensity_le rates mutationRate s))
    · exact div_nonneg (eventRate_nonneg rates s event) (intensity_pos rates mutationRate).le
    · exact div_nonneg (mutationRate event.val.2).property (intensity_pos rates mutationRate).le
  mass_sum := by
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    simp only [← Finset.sum_div]
    unfold totalIntensity totalRate mutationIntensity
    ring

abbrev LawFamily (D L n : ℕ) := State D L n → FiniteReportLaw (Genome L n)

/-- A youngest mutation acts after the older-generated genome. No nucleotide
is sampled backwards from the current sample configuration. -/
noncomputable def transferMark (family : LawFamily D L n) (s : State D L n) :
    Mark s → FiniteReportLaw (Genome L n)
  | none => family s
  | some (.inl event) => family (nextState s event)
  | some (.inr event) => (family s).bind (mutationKernel event)

noncomputable def transfer (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (family : LawFamily D L n) : LawFamily D L n :=
  fun s ↦ (markLaw rates mutationRate s).bind (transferMark family s)

/-- Each transfer row is a normalized nonnegative whole-genome report law. -/
theorem transfer_normalized (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (family : LawFamily D L n) (s : State D L n) :
    (∀ genome, 0 ≤ (transfer rates mutationRate family s).mass genome) ∧
      (∑ genome, (transfer rates mutationRate family s).mass genome) = 1 :=
  ⟨(transfer rates mutationRate family s).mass_nonneg,
    (transfer rates mutationRate family s).mass_sum⟩

/-- Explicit finite row-vector recurrence: mutation is right composition by
the selected catalogue-update kernel. -/
theorem transfer_expectation (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (family : LawFamily D L n) (s : State D L n) (readout : Genome L n → ℝ) :
    (transfer rates mutationRate family s).expectation readout =
      (1 - totalIntensity rates mutationRate s / intensity (n := n) rates mutationRate) *
          (family s).expectation readout +
        (∑ event : Channel s, eventRate rates s event *
          (family (nextState s event)).expectation readout) /
            intensity (n := n) rates mutationRate +
        (∑ event : MutationChannel s, (mutationRate event.val.2 : ℝ) *
          ((family s).bind (mutationKernel event)).expectation readout) /
            intensity (n := n) rates mutationRate := by
  rw [transfer, expectation_bind]
  unfold expectation markLaw transferMark
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

/-- Exact joint generator on finite row-law families, derived from the
ancestral event rates and the per-locus chronological mutation kernels. -/
theorem transfer_generator (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (family : LawFamily D L n) (s : State D L n) (readout : Genome L n → ℝ) :
    intensity (n := n) rates mutationRate *
        ((transfer rates mutationRate family s).expectation readout -
          (family s).expectation readout) =
      (∑ event : Channel s, eventRate rates s event *
        ((family (nextState s event)).expectation readout - (family s).expectation readout)) +
      ∑ event : MutationChannel s, (mutationRate event.val.2 : ℝ) *
        (((family s).bind (mutationKernel event)).expectation readout -
          (family s).expectation readout) := by
  rw [transfer_expectation]
  have hi := ne_of_gt (intensity_pos (n := n) rates mutationRate)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold totalIntensity totalRate mutationIntensity
  field_simp
  ring

noncomputable def rootVectorLaw : FiniteReportLaw (Fin L → NucleotideMutationLaw.Nucleotide) where
  mass := fun roots ↦ ∏ locus, GenealogyGenotypeLaw.rootLaw.mass (roots locus)
  mass_nonneg := fun roots ↦ Finset.prod_nonneg (fun locus _ ↦
    GenealogyGenotypeLaw.rootLaw.mass_nonneg (roots locus))
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

/-- Independent ancestral nucleotides at every locus, with empty mutation
presence flags and one-entry ancestral allele catalogues. -/
noncomputable def rootGenomeLaw : FiniteReportLaw (Genome L n) :=
  rootVectorLaw.pushforward (fun roots locus ↦ OrderedMutationCatalogue.initialState (roots locus))

theorem transfer_empty (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (family : LawFamily D L n) :
    transfer rates mutationRate family AncestralAbsorptionLaw.emptyState =
      family AncestralAbsorptionLaw.emptyState := by
  classical
  let empty : State D L n := AncestralAbsorptionLaw.emptyState
  letI : IsEmpty (Channel empty) := ⟨by
    intro event
    rcases event with event | (event | event)
    all_goals exact Finset.notMem_empty _ event.property.1⟩
  letI : IsEmpty (MutationChannel empty) :=
    ⟨fun event ↦ Finset.notMem_empty _ event.property.1⟩
  apply (eq_iff_singleton_expectations_eq _ _).mpr
  intro target
  change (transfer rates mutationRate family empty).expectation _ = _
  rw [transfer_expectation]
  simp [totalIntensity, totalRate, mutationIntensity]
  rfl

theorem transfer_boundary (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (family : LawFamily D L n)
    (hboundary : family AncestralAbsorptionLaw.emptyState = rootGenomeLaw) :
    transfer rates mutationRate family AncestralAbsorptionLaw.emptyState = rootGenomeLaw :=
  (transfer_empty rates mutationRate family).trans hboundary

noncomputable def scanNext (s : State D L n) : Mark s → State D L n
  | none => s
  | some (.inl event) => nextState s event
  | some (.inr _) => s

/-- Joint ancestry/mutation mark histories, scanned from younger to older. -/
def History : ℕ → State D L n → Type
  | 0, _ => PUnit
  | count + 1, s => (mark : Mark s) × History count (scanNext s mark)

noncomputable instance historyFintype : (count : ℕ) → (s : State D L n) →
    Fintype (History count s)
  | 0, _ => inferInstanceAs (Fintype PUnit)
  | count + 1, s => by
      letI : ∀ mark : Mark s, Fintype (History count (scanNext s mark)) :=
        fun mark ↦ historyFintype count (scanNext s mark)
      exact inferInstanceAs (Fintype ((mark : Mark s) × History count (scanNext s mark)))

noncomputable def historyMass (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) :
    {count : ℕ} → (s : State D L n) → History count s → ℝ
  | 0, _, _ => 1
  | _count + 1, s, ⟨mark, rest⟩ =>
      (markLaw rates mutationRate s).mass mark * historyMass rates mutationRate _ rest

theorem historyMass_nonneg (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    {count : ℕ} (s : State D L n) (history : History count s) :
    0 ≤ historyMass rates mutationRate s history := by
  induction count generalizing s with
  | zero => exact zero_le_one
  | succ count ih =>
      exact mul_nonneg ((markLaw rates mutationRate s).mass_nonneg history.1)
        (ih _ history.2)

theorem historyMass_sum (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (count : ℕ) (s : State D L n) :
    (∑ history : History count s, historyMass rates mutationRate s history) = 1 := by
  induction count generalizing s with
  | zero => simp [History, historyMass]
  | succ count ih =>
      change (∑ history : (mark : Mark s) × History count (scanNext s mark),
        (markLaw rates mutationRate s).mass history.1 *
          historyMass rates mutationRate (scanNext s history.1) history.2) = 1
      rw [Fintype.sum_sigma]
      simp only [← Finset.mul_sum, ih, mul_one, FiniteReportLaw.mass_sum]

/-- Reverse composition restores chronological mutation order. The recursively
older report is generated first; the younger mutation is then appended. -/
noncomputable def unwind (boundary : LawFamily D L n) : {count : ℕ} →
    {s : State D L n} → History count s → FiniteReportLaw (Genome L n)
  | 0, s, _ => boundary s
  | _count + 1, _s, ⟨none, rest⟩ => unwind boundary rest
  | _count + 1, _s, ⟨some (.inl _event), rest⟩ => unwind boundary rest
  | _count + 1, _s, ⟨some (.inr event), rest⟩ =>
      (unwind boundary rest).bind (mutationKernel event)

/-- Exact correspondence between the finite transfer iteration and summing
all marked histories with chronological right-composition of mutations. -/
theorem iterate_history_expectation (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (boundary : LawFamily D L n) (count : ℕ) (s : State D L n)
    (readout : Genome L n → ℝ) :
    (((transfer rates mutationRate)^[count]) boundary s).expectation readout =
      ∑ history : History count s, historyMass rates mutationRate s history *
        (unwind boundary history).expectation readout := by
  induction count generalizing s readout with
  | zero => simp [History, historyMass, unwind]
  | succ count ih =>
      rw [Function.iterate_succ_apply', transfer, expectation_bind]
      change (∑ mark : Mark s, (markLaw rates mutationRate s).mass mark *
        (transferMark (((transfer rates mutationRate)^[count]) boundary) s mark).expectation
          readout) =
        ∑ history : (mark : Mark s) × History count (scanNext s mark),
          ((markLaw rates mutationRate s).mass history.1 *
            historyMass rates mutationRate (scanNext s history.1) history.2) *
              (unwind (count := count + 1) (s := s) boundary history).expectation readout
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro mark _
      rcases mark with _ | (event | event)
      · simp only [transferMark, unwind, scanNext, ih]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro history _
        ring
      · simp only [transferMark, unwind, scanNext, ih]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro history _
        ring
      · simp only [transferMark, unwind, scanNext, expectation_bind, ih]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro history _
        ring

section Distance

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def rowDistance (first second : FiniteReportLaw A) : ℝ :=
  ∑ output, |first.mass output - second.mass output|

theorem rowDistance_nonneg (first second : FiniteReportLaw A) :
    0 ≤ rowDistance first second := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem rowDistance_self (law : FiniteReportLaw A) : rowDistance law law = 0 := by
  simp [rowDistance]

theorem rowDistance_eq_zero {first second : FiniteReportLaw A}
    (hzero : rowDistance first second = 0) : first = second := by
  apply FiniteReportLaw.ext
  intro output
  have h := Finset.single_le_sum (fun value (_ : value ∈ Finset.univ) ↦
    abs_nonneg (first.mass value - second.mass value)) (Finset.mem_univ output)
  change |first.mass output - second.mass output| ≤ rowDistance first second at h
  rw [hzero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

theorem rowDistance_le_two (first second : FiniteReportLaw A) :
    rowDistance first second ≤ 2 := by
  calc
    rowDistance first second ≤ ∑ output, (first.mass output + second.mass output) := by
      apply Finset.sum_le_sum
      intro output _
      exact (abs_sub (first.mass output) (second.mass output)).trans_eq
        (by rw [abs_of_nonneg (first.mass_nonneg output),
          abs_of_nonneg (second.mass_nonneg output)])
    _ = 2 := by simp [Finset.sum_add_distrib, FiniteReportLaw.mass_sum]; norm_num

/-- Right composition by any finite stochastic kernel contracts row L1 distance. -/
theorem rowDistance_bind (first second : FiniteReportLaw A)
    (kernel : A → FiniteReportLaw B) :
    rowDistance (first.bind kernel) (second.bind kernel) ≤ rowDistance first second := by
  calc
    rowDistance (first.bind kernel) (second.bind kernel) ≤
        ∑ output, ∑ input, |first.mass input - second.mass input| *
          (kernel input).mass output := by
      apply Finset.sum_le_sum
      intro output _
      change |(∑ input, first.mass input * (kernel input).mass output) -
        ∑ input, second.mass input * (kernel input).mass output| ≤ _
      rw [← Finset.sum_sub_distrib]
      simp only [← sub_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro input _
        rw [abs_mul, abs_of_nonneg ((kernel input).mass_nonneg output)])
    _ = rowDistance first second := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one, rowDistance]

theorem rowDistance_mixture (weights : FiniteReportLaw A)
    (first second : A → FiniteReportLaw B) :
    rowDistance (weights.bind first) (weights.bind second) ≤
      weights.expectation (fun input ↦ rowDistance (first input) (second input)) := by
  calc
    rowDistance (weights.bind first) (weights.bind second) ≤
        ∑ output, ∑ input, weights.mass input *
          |(first input).mass output - (second input).mass output| := by
      apply Finset.sum_le_sum
      intro output _
      change |(∑ input, weights.mass input * (first input).mass output) -
        ∑ input, weights.mass input * (second input).mass output| ≤ _
      rw [← Finset.sum_sub_distrib]
      simp only [← mul_sub]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro input _
        rw [abs_mul, abs_of_nonneg (weights.mass_nonneg input)])
    _ = weights.expectation (fun input ↦ rowDistance (first input) (second input)) := by
      rw [Finset.sum_comm]
      simp only [expectation, rowDistance, Finset.mul_sum]

end Distance

/-- One transfer cannot increase the maximal row distance. The sharper bound
retains the exact distribution of the next ancestral configuration. -/
theorem transfer_distance (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (first second : LawFamily D L n) (s : State D L n) :
    rowDistance (transfer rates mutationRate first s) (transfer rates mutationRate second s) ≤
      (markLaw rates mutationRate s).expectation
        (fun mark ↦ rowDistance (first (scanNext s mark)) (second (scanNext s mark))) := by
  apply (rowDistance_mixture (markLaw rates mutationRate s) _ _).trans
  apply Finset.sum_le_sum
  intro mark _
  apply mul_le_mul_of_nonneg_left _ ((markLaw rates mutationRate s).mass_nonneg mark)
  rcases mark with _ | (event | event)
  · exact le_rfl
  · exact le_rfl
  · exact rowDistance_bind (first s) (second s) (mutationKernel event)

noncomputable def terminal : {count : ℕ} → {s : State D L n} → History count s → State D L n
  | 0, s, _ => s
  | _count + 1, _s, ⟨_mark, rest⟩ => terminal rest

/-- The entire chronological mutation sequence contracts row distance; its
only remaining dependence on the boundary is at the terminal ancestral state. -/
theorem unwind_distance (first second : LawFamily D L n) {count : ℕ}
    {s : State D L n} (history : History count s) :
    rowDistance (unwind first history) (unwind second history) ≤
      rowDistance (first (terminal history)) (second (terminal history)) := by
  induction count generalizing s with
  | zero => exact le_rfl
  | succ count ih =>
      rcases history with ⟨mark, rest⟩
      rcases mark with _ | (event | event)
      · exact ih rest
      · exact ih rest
      · exact (rowDistance_bind (unwind first rest) (unwind second rest) _).trans (ih rest)

noncomputable def historyLaw (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (count : ℕ) (s : State D L n) : FiniteReportLaw (History count s) where
  mass := historyMass rates mutationRate s
  mass_nonneg := historyMass_nonneg rates mutationRate s
  mass_sum := historyMass_sum rates mutationRate count s

/-- Finite transfer iteration is exactly a mixture of completed chronological
kernel compositions, rather than a backward nucleotide transition process. -/
theorem iterate_history_law (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (boundary : LawFamily D L n) (count : ℕ) (s : State D L n) :
    ((transfer rates mutationRate)^[count]) boundary s =
      (historyLaw rates mutationRate count s).bind (unwind boundary) := by
  apply (eq_iff_singleton_expectations_eq _ _).mpr
  intro target
  rw [iterate_history_expectation, expectation_bind]
  rfl

theorem iterate_distance (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (first second : LawFamily D L n) (count : ℕ) (s : State D L n) :
    rowDistance (((transfer rates mutationRate)^[count]) first s)
        (((transfer rates mutationRate)^[count]) second s) ≤
      (historyLaw rates mutationRate count s).expectation
        (fun history ↦ rowDistance (first (terminal history)) (second (terminal history))) := by
  rw [iterate_history_law, iterate_history_law]
  apply (rowDistance_mixture _ _ _).trans
  apply Finset.sum_le_sum
  intro history _
  exact mul_le_mul_of_nonneg_left (unwind_distance first second history)
    (historyMass_nonneg rates mutationRate s history)

end Descent.Portability.AncestralMutationTransfer
