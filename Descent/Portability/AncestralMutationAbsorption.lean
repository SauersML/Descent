/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralMutationTransfer

assert_below Descent.Decision Descent.Program

/-!
Derived absorption and contraction for the joint ancestry/mutation transfer.
Mutation marks do not change ancestral support, but increase the proposal
intensity. The completion bound is therefore derived at the joint intensity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralMutationAbsorption

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralAbsorptionLaw
open AncestralMutationTransfer FiniteReportLaw
open scoped NNReal

variable {D L n : ℕ}

private theorem jointChannel_empty
    (event : Channel (emptyState : State D L n) ⊕ MutationChannel (emptyState : State D L n)) :
      False := by
  rcases event with (event | (event | event)) | event
  all_goals exact Finset.notMem_empty _ event.property.1

private theorem empty_mark_mass (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) :
    (markLaw rates mutationRate (emptyState : State D L n)).mass none = 1 := by
  have hancestry : totalRate rates (emptyState : State D L n) = 0 := by
    apply Finset.sum_eq_zero
    intro event _
    exact (jointChannel_empty (.inl event)).elim
  have hmutation : mutationIntensity mutationRate (emptyState : State D L n) = 0 := by
    apply Finset.sum_eq_zero
    intro event _
    exact (jointChannel_empty (.inr event)).elim
  simp [markLaw, totalIntensity, hancestry, hmutation]

private theorem sampleComplete_scan (s : State D L n) (hs : SampleComplete s) (mark : Mark s) :
    SampleComplete (scanNext s mark) := by
  rcases mark with _ | (event | event)
  · exact hs
  · exact sampleComplete_proposal s hs (some event)
  · exact hs

private theorem historySampleComplete {s : State D L n} (hs : SampleComplete s)
    {count : ℕ} (history : History count s) : SampleComplete (terminal history) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (sampleComplete_scan s hs history.1) history.2

private theorem supportedAt_coalesce (deme : Fin D) (s : State D L n)
    (hs : SupportedAt deme s) (event : CoalescenceChannel s) :
    SupportedAt deme (nextState s (.inr (.inl event))) := by
  intro c hc
  unfold nextState coalesce at hc
  dsimp only at hc
  split at hc
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hs event.val.1 event.property.1
    · exact hs c (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
  · exact hs c (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2

private theorem supportedAt_scan (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : State D L n) (hs : SupportedAt deme s) (mark : Mark s)
    (hpos : 0 < (markLaw rates mutationRate s).mass mark) : SupportedAt deme (scanNext s mark) := by
  rcases mark with _ | (event | event)
  · exact hs
  · have hrate : 0 < eventRate rates s event := by
      change 0 < eventRate rates s event / intensity (n := n) rates mutationRate at hpos
      exact (div_pos_iff_of_pos_right (intensity_pos rates mutationRate)).mp hpos
    exact supportedAt_proposal rates deme hisolated s hs (some event)
      (div_pos hrate (dominatingRate_pos rates))
  · exact hs

private theorem historySupportedAt (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    {count : ℕ} (s : State D L n) (hs : SupportedAt deme s) (history : History count s)
    (hpos : 0 < historyMass rates mutationRate s history) : SupportedAt deme (terminal history)
      := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih =>
      change 0 < (markLaw rates mutationRate s).mass history.1 *
        historyMass rates mutationRate (scanNext s history.1) history.2 at hpos
      have hfirst := pos_of_mul_pos_left hpos (historyMass_nonneg rates mutationRate _ history.2)
      have hrest := pos_of_mul_pos_right hpos ((markLaw rates mutationRate s).mass_nonneg history.1)
      exact ih _ (supportedAt_scan rates mutationRate deme hisolated s hs history.1 hfirst)
        history.2 hrest

private theorem history_expectation_succ (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (count : ℕ) (s : State D L n) (readout : History (count + 1) s → ℝ) :
    (historyLaw rates mutationRate (count + 1) s).expectation readout =
      (markLaw rates mutationRate s).expectation (fun mark ↦
        (historyLaw rates mutationRate count (scanNext s mark)).expectation
          (fun rest ↦ readout ⟨mark, rest⟩)) := by
  unfold expectation historyLaw
  change (∑ history : (mark : Mark s) × History count (scanNext s mark),
    ((markLaw rates mutationRate s).mass history.1 *
      historyMass rates mutationRate (scanNext s history.1) history.2) * readout history) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum, mul_assoc]

noncomputable def coalescenceFloor (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin
  D) : ℝ :=
  (1 / (4 * rates.populationSize deme)) /
    (intensity (n := n) rates mutationRate + 1 / (4 * rates.populationSize deme))

theorem coalescenceFloor_pos (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D) :
    0 < coalescenceFloor (n := n) rates mutationRate deme := by
  have hc : 0 < 1 / (4 * rates.populationSize deme) := one_div_pos.mpr (mul_pos (by norm_num)
    (rates.size_pos deme))
  exact div_pos hc (add_pos (intensity_pos (n := n) rates mutationRate) hc)

theorem coalescenceFloor_lt_one (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D) :
    coalescenceFloor (n := n) rates mutationRate deme < 1 := by
  have hc : 0 < 1 / (4 * rates.populationSize deme) := one_div_pos.mpr (mul_pos (by norm_num)
    (rates.size_pos deme))
  unfold coalescenceFloor
  apply (div_lt_one (add_pos (intensity_pos (n := n) rates mutationRate) hc)).mpr
  linarith [intensity_pos (n := n) rates mutationRate]

private theorem coalescenceFloor_le_mass (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme
  : Fin D) (s : State D L n)
    (hsupported : SupportedAt deme s) (event : CoalescenceChannel s) :
    coalescenceFloor (n := n) rates mutationRate deme ≤
      (markLaw rates mutationRate s).mass (some (.inl (.inr (.inl event)))) := by
  have hc : 0 < 1 / (4 * rates.populationSize deme) := one_div_pos.mpr (mul_pos (by norm_num)
    (rates.size_pos deme))
  have hd : event.val.1.1 = deme := hsupported _ event.property.1
  change _ ≤ (1 / (4 * rates.populationSize event.val.1.1)) / intensity (n := n) rates mutationRate
  rw [hd]
  exact div_le_div_of_nonneg_left hc.le (intensity_pos (n := n) rates mutationRate)
    (le_add_of_nonneg_right hc.le)

/-- From every sampled ancestral state in one population, an explicitly
positive-probability sequence of at most `L*n` coalescence proposals completes
all loci. Extra proposals after completion are null events of probability one. -/
theorem exists_completion_trace (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D)
  (count : ℕ)
    (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hcount : s.val.card ≤ count) :
    ∃ trace : History count s, (terminal trace).val = ∅ ∧
      coalescenceFloor (n := n) rates mutationRate deme ^ count ≤ historyMass rates
        mutationRate s trace := by
  classical
  induction count generalizing s with
  | zero =>
      have hempty : s = emptyState := Subtype.ext (Finset.card_eq_zero.mp
        (Nat.eq_zero_of_le_zero hcount))
      subst s
      exact ⟨PUnit.unit, rfl, le_rfl⟩
  | succ count ih =>
      by_cases hempty : s.val = ∅
      · have hstate : s = emptyState := Subtype.ext hempty
        subst s
        obtain ⟨rest, hrest, hmass⟩ := ih emptyState SampleComplete.empty (supportedAt_empty
          deme) (by simp [emptyState])
        refine ⟨⟨none, rest⟩, hrest, ?_⟩
        change _ ≤ (markLaw rates mutationRate emptyState).mass none * historyMass rates
          mutationRate emptyState rest
        rw [empty_mark_mass, one_mul]
        rw [pow_succ']
        exact (mul_le_of_le_one_left (pow_nonneg (coalescenceFloor_pos rates mutationRate
          deme).le count)
          (coalescenceFloor_lt_one rates mutationRate deme).le).trans hmass
      · have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (hs.nontrivial hnonempty)
        let event : CoalescenceChannel s := ⟨(a, b), ha, hb, hab, (hsupported a ha).trans
          (hsupported b hb).symm⟩
        let next := scanNext s (some (.inl (.inr (.inl event))))
        have hnext : SampleComplete next := sampleComplete_scan s hs _
        have hnextcard : next.val.card ≤ count := by
          have hlt := coalesce_count_lt s a b ha hb hab ((hsupported a ha).trans (hsupported b
            hb).symm)
          change (coalesce s a b ha hb hab ((hsupported a ha).trans (hsupported b
            hb).symm)).val.card ≤ count
          omega
        obtain ⟨rest, hrest, hmass⟩ := ih next hnext (supportedAt_coalesce deme s hsupported
          event) hnextcard
        refine ⟨⟨some (.inl (.inr (.inl event))), rest⟩, hrest, ?_⟩
        change _ ≤ (markLaw rates mutationRate s).mass (some (.inl (.inr (.inl event)))) *
          historyMass rates mutationRate next rest
        rw [pow_succ']
        exact mul_le_mul (coalescenceFloor_le_mass rates mutationRate deme s hsupported event) hmass
          (pow_nonneg (coalescenceFloor_pos rates mutationRate deme).le _) ((markLaw rates
            mutationRate s).mass_nonneg _)

noncomputable def survival (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count : ℕ) (s :
  State D L n) : ℝ :=
  (historyLaw rates mutationRate count s).expectation (fun trace ↦ unfinished (terminal trace))

theorem survival_nonneg (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count : ℕ) (s : State
  D L n) :
    0 ≤ survival rates mutationRate count s :=
  Finset.sum_nonneg (fun trace _ ↦
    mul_nonneg (historyMass_nonneg rates mutationRate s trace) (unfinished_nonneg _))

theorem survival_le_one (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count : ℕ) (s : State
  D L n) :
    survival rates mutationRate count s ≤ 1 := by
  calc
    survival rates mutationRate count s ≤ ∑ trace : History count s, historyMass rates
      mutationRate s trace := by
      apply Finset.sum_le_sum
      intro trace _
      exact mul_le_of_le_one_right (historyMass_nonneg rates mutationRate s trace)
        (unfinished_le_one _)
    _ = 1 := historyMass_sum rates mutationRate count s

private theorem terminal_empty {count : ℕ} (trace : History count (emptyState : State D L n)) :
    (terminal trace).val = ∅ := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      cases event with
      | none => exact ih rest
      | some event => exact (jointChannel_empty event).elim

theorem survival_empty (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count : ℕ) :
    survival rates mutationRate count (emptyState : State D L n) = 0 := by
  classical
  unfold survival expectation unfinished
  simp only [terminal_empty, ↓reduceIte, mul_zero, Finset.sum_const_zero]

private theorem survival_succ (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count : ℕ) (s :
  State D L n) :
    survival rates mutationRate (count + 1) s =
      (markLaw rates mutationRate s).expectation (fun event ↦ survival rates mutationRate count
        (scanNext s
        event)) := by
  exact history_expectation_succ rates mutationRate count s _

/-- Survival probabilities compose through the same marked genealogy law,
retaining dependence on the entire current ancestral configuration. -/
theorem survival_add (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (first rest : ℕ) (s :
  State D L n) :
    survival rates mutationRate (first + rest) s =
      (historyLaw rates mutationRate first s).expectation (fun trace ↦ survival rates
        mutationRate rest (terminal trace)) := by
  induction first generalizing s with
  | zero =>
      rw [Nat.zero_add]
      simp only [historyLaw, expectation, History, historyMass, terminal, Fintype.sum_unique,
        one_mul]
  | succ first ih =>
      rw [Nat.succ_add, survival_succ, history_expectation_succ]
      unfold expectation
      apply Finset.sum_congr rfl
      intro event _
      dsimp only
      rw [ih]
      rfl

/-- A demographic-rate-derived bound on the probability that ancestral
material remains after one block of `L*n` uniformization proposals. -/
theorem survival_block_bound (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D) (s
  : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    survival rates mutationRate (L * n) s ≤ 1 - coalescenceFloor (n := n) rates mutationRate
      deme ^ (L * n) := by
  classical
  obtain ⟨chosen, hchosen, hmass⟩ :=
    exists_completion_trace rates mutationRate deme (L * n) s hs hsupported (lineage_count_bound s)
  have hchosenZero : unfinished (terminal chosen) = 0 := by simp [unfinished, hchosen]
  have htotal : survival rates mutationRate (L * n) s + historyMass rates mutationRate s chosen
    ≤ 1 := by
    rw [← historyMass_sum rates mutationRate (L * n) s]
    unfold survival expectation historyLaw
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ chosen)]
    simp only [hchosenZero, mul_zero, add_zero]
    rw [← Finset.sum_erase_add Finset.univ (fun trace ↦ historyMass rates mutationRate s trace)
      (Finset.mem_univ chosen)]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro trace _
    exact mul_le_of_le_one_right (historyMass_nonneg rates mutationRate s trace)
      (unfinished_le_one _)
  linarith

noncomputable def blockSurvivalBound (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme :
  Fin D) : ℝ :=
  1 - coalescenceFloor (n := n) rates mutationRate deme ^ (L * n)

theorem blockSurvivalBound_nonneg (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D) :
    0 ≤ blockSurvivalBound (n := n) rates mutationRate deme :=
  sub_nonneg.mpr (pow_le_one₀ (coalescenceFloor_pos rates mutationRate deme).le
    (coalescenceFloor_lt_one
    rates mutationRate deme).le)

theorem blockSurvivalBound_lt_one (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D) :
    blockSurvivalBound (n := n) rates mutationRate deme < 1 := by
  unfold blockSurvivalBound
  exact sub_lt_self _ (pow_pos (coalescenceFloor_pos rates mutationRate deme) _)

private theorem survival_block_relative (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme
  : Fin D) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    survival rates mutationRate (L * n) s ≤ blockSurvivalBound (n := n) rates mutationRate deme
      * unfinished s := by
  classical
  by_cases h : s.val = ∅
  · have he : s = emptyState := Subtype.ext h
    subst s
    rw [survival_empty]
    simp [unfinished, emptyState]
  · simpa [unfinished, h, blockSurvivalBound] using survival_block_bound rates mutationRate
      deme s hs hsupported

/-- The final panmictic ancestry has a geometric termination bound despite
arbitrary finite recombination rates. The constant is deliberately conservative. -/
theorem survival_geometric (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D)
  (blocks : ℕ) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    survival rates mutationRate (L * n * blocks) s ≤ blockSurvivalBound (n := n) rates
      mutationRate deme ^ blocks := by
  induction blocks with
  | zero => simpa using survival_le_one rates mutationRate 0 s
  | succ blocks ih =>
      rw [Nat.mul_succ, survival_add]
      calc
        (historyLaw rates mutationRate (L * n * blocks) s).expectation
            (fun trace ↦ survival rates mutationRate (L * n) (terminal trace)) ≤
            (historyLaw rates mutationRate (L * n * blocks) s).expectation
              (fun trace ↦ blockSurvivalBound (n := n) rates mutationRate deme *
                unfinished (terminal trace)) := by
          apply Finset.sum_le_sum
          intro trace _
          by_cases hmass : historyMass rates mutationRate s trace = 0
          · change historyMass rates mutationRate s trace * _ ≤ historyMass rates mutationRate
              s trace * _
            simp [hmass]
          · have hpos := lt_of_le_of_ne (historyMass_nonneg rates mutationRate s trace)
              (Ne.symm hmass)
            exact mul_le_mul_of_nonneg_left
              (survival_block_relative rates mutationRate deme _ (historySampleComplete hs trace)
                (historySupportedAt rates mutationRate deme hisolated s hsupported trace hpos))
              (historyMass_nonneg rates mutationRate s trace)
        _ = blockSurvivalBound (n := n) rates mutationRate deme * survival rates mutationRate
          (L * n * blocks) s := by
          unfold survival expectation
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro trace _
          ring
        _ ≤ blockSurvivalBound (n := n) rates mutationRate deme * blockSurvivalBound (n := n)
          rates mutationRate deme ^
          blocks :=
          mul_le_mul_of_nonneg_left ih (blockSurvivalBound_nonneg rates mutationRate deme)
        _ = blockSurvivalBound (n := n) rates mutationRate deme ^ (blocks + 1) := (pow_succ' _
          _).symm

private theorem survival_le_unfinished (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (count
  : ℕ) (s : State D L n) :
    survival rates mutationRate count s ≤ unfinished s := by
  classical
  by_cases h : s.val = ∅
  · have he : s = emptyState := Subtype.ext h
    subst s
    rw [survival_empty]
    simp [unfinished, emptyState]
  · simpa [unfinished, h] using survival_le_one rates mutationRate count s

theorem survival_antitone (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (s : State D L n) :
    Antitone (fun count ↦ survival rates mutationRate count s) := by
  intro first second h
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le h
  dsimp only
  rw [survival_add]
  apply Finset.sum_le_sum
  intro trace _
  exact mul_le_mul_of_nonneg_left (survival_le_unfinished rates mutationRate rest (terminal trace))
    (historyMass_nonneg rates mutationRate s trace)

theorem survival_bound (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D) (count :
  ℕ) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    survival rates mutationRate count s ≤ blockSurvivalBound (n := n) rates mutationRate deme ^
      (count / (L * n)) :=
  (survival_antitone rates mutationRate s (Nat.mul_div_le count (L * n))).trans
    (survival_geometric rates mutationRate deme (count / (L * n)) s hs hsupported hisolated)

/-- The probability of unfinished ancestry tends to zero. This is derived from
sample preservation and the actual coalescence and mutation rates, without an assumed
absorption hypothesis. -/
theorem survival_tendsto_zero (rates : Rates D L) (mutationRate : Fin L → ℝ≥0) (deme : Fin D)
  (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    Filter.Tendsto (fun count ↦ survival rates mutationRate count s) Filter.atTop (nhds 0) := by
  by_cases hzero : L * n = 0
  · have hempty : s = emptyState := Subtype.ext
      (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hzero ▸ lineage_count_bound s)))
    subst s
    simpa only [survival_empty] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0))
  · have hpos : 0 < L * n := Nat.pos_of_ne_zero hzero
    have hdiv : Filter.Tendsto (fun count : ℕ ↦ count / (L * n)) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop.2
      intro bound
      filter_upwards [Filter.eventually_ge_atTop (bound * (L * n))] with count hcount
      exact (Nat.le_div_iff_mul_le hpos).mpr hcount
    exact squeeze_zero (fun count ↦ survival_nonneg rates mutationRate count s)
      (fun count ↦ survival_bound rates mutationRate deme count s hs hsupported hisolated)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (blockSurvivalBound_nonneg rates mutationRate deme)
        (blockSurvivalBound_lt_one rates mutationRate deme)).comp hdiv)

/-- Boundary uncertainty can survive only on histories whose ancestry has not
completed. All chronological mutation kernels contract that uncertainty. -/
theorem iterate_distance_survival (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (first second : LawFamily D L n)
    (hboundary : first emptyState = second emptyState) (count : ℕ) (s : State D L n) :
    rowDistance (((transfer rates mutationRate)^[count]) first s)
        (((transfer rates mutationRate)^[count]) second s) ≤
      2 * survival rates mutationRate count s := by
  classical
  apply (iterate_distance rates mutationRate first second count s).trans
  unfold survival expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro history _
  have hpoint : rowDistance (first (terminal history)) (second (terminal history)) ≤
      2 * unfinished (terminal history) := by
    by_cases hcomplete : (terminal history).val = ∅
    · have heq : terminal history = emptyState := Subtype.ext hcomplete
      rw [heq, hboundary, rowDistance_self]
      simp [unfinished, emptyState]
    · simpa [unfinished, hcomplete] using rowDistance_le_two
        (first (terminal history)) (second (terminal history))
  have hweighted := mul_le_mul_of_nonneg_left hpoint
    (historyMass_nonneg rates mutationRate s history)
  change historyMass rates mutationRate s history * _ ≤ _
  change historyMass rates mutationRate s history *
    rowDistance (first (terminal history)) (second (terminal history)) ≤
      2 * (historyMass rates mutationRate s history * unfinished (terminal history))
  nlinarith

/-- Explicit geometric truncation bound on the entire joint genome/catalogue
law, uniform over every choice of the unresolved older boundary distribution. -/
theorem iterate_distance_geometric (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (first second : LawFamily D L n)
    (hboundary : first emptyState = second emptyState) (blocks : ℕ) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    rowDistance (((transfer rates mutationRate)^[L * n * blocks]) first s)
        (((transfer rates mutationRate)^[L * n * blocks]) second s) ≤
      2 * blockSurvivalBound (n := n) rates mutationRate deme ^ blocks :=
  (iterate_distance_survival rates mutationRate first second hboundary _ s).trans
    (mul_le_mul_of_nonneg_left
      (survival_geometric rates mutationRate deme blocks s hs hsupported hisolated) (by norm_num))

/-- Any two normalized solutions of the finite transfer equations with the
same completed-ancestry boundary agree on sampled isolated-ANC states. This
uniqueness is derived from coalescence, not postulated as an operator axiom. -/
theorem fixed_point_unique (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (first second : LawFamily D L n)
    (hfirst : transfer rates mutationRate first = first)
    (hsecond : transfer rates mutationRate second = second)
    (hboundary : first emptyState = second emptyState) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) : first s = second s := by
  have hbound (count : ℕ) : rowDistance (first s) (second s) ≤
      2 * survival rates mutationRate count s := by
    have h := iterate_distance_survival rates mutationRate first second hboundary count s
    rw [Function.iterate_fixed hfirst count, Function.iterate_fixed hsecond count] at h
    exact h
  have hzero : rowDistance (first s) (second s) ≤ 0 := by
    have h := ge_of_tendsto
      ((survival_tendsto_zero rates mutationRate deme s hs hsupported hisolated).const_mul 2)
      (Filter.Eventually.of_forall hbound)
    simpa using h
  exact rowDistance_eq_zero (le_antisymm hzero (rowDistance_nonneg _ _))

end Descent.Portability.AncestralMutationAbsorption
