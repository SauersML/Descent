/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarkedAncestralLaw

assert_below Descent.Decision Descent.Program

/-!
Sample preservation and exact finite-genome ancestry completion probabilities.
The final isolated ancestral population has a derived geometric survival bound
and a normalized law on stopped marked histories, with arbitrary recombination.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralAbsorptionLaw

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw FiniteReportLaw

variable {D L n : ℕ}

/-- Every retained locus carries every sample, and no retained lineage has already
reached that locus's MRCA. These are additional invariants of sampled ancestry;
arbitrary disjoint material configurations need not satisfy them. -/
def SampleComplete (s : State D L n) : Prop :=
  (∀ a ∈ s.val, ∀ token ∈ a.2, ∀ sample : Fin n,
    ∃ b ∈ s.val, (token.1, sample) ∈ b.2) ∧
  (∀ a ∈ s.val, ∀ locus : Fin L, ¬ completedLocus a.2 locus)

theorem SampleComplete.empty : SampleComplete (⟨∅, valid_empty⟩ : State D L n) := by
  simp [SampleComplete]

theorem sampleComplete_initial (sampleDeme : Fin n → Fin D) (hL : 0 < L)
    (hn : 2 ≤ n) : SampleComplete (initialState sampleDeme hL hn) := by
  classical
  constructor
  · intro a ha token ht sample
    refine ⟨(sampleDeme sample, Finset.univ.product {sample}), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨sample, Finset.mem_univ _, rfl⟩
    · simp
  · intro a ha locus hcomplete
    obtain ⟨sample, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨other, hother⟩ : ∃ other : Fin n, other ≠ sample := by
      let zero : Fin n := ⟨0, by omega⟩
      let one : Fin n := ⟨1, by omega⟩
      by_cases h : sample = zero
      · exact ⟨one, by subst sample; simp [one, zero, Fin.ext_iff]⟩
      · exact ⟨zero, Ne.symm h⟩
    exact hother (Finset.mem_singleton.mp (Finset.mem_product.mp (hcomplete other)).2)

theorem SampleComplete.nontrivial {s : State D L n} (hs : SampleComplete s)
    (hne : s.val.Nonempty) : 2 ≤ s.val.card := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨token, ht⟩ := s.property.1 a ha
  obtain ⟨sample, hsample⟩ := not_forall.mp (hs.2 a ha token.1)
  obtain ⟨b, hb, htoken⟩ := hs.1 a ha token ht sample
  have hab : a ≠ b := by intro h; subst b; exact hsample htoken
  exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩

theorem coalesce_count_lt (s : State D L n) (a b : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (hab : a ≠ b) (hd : a.1 = b.1) :
    (coalesce s a b ha hb hab hd).val.card < s.val.card := by
  classical
  have hb' : b ∈ s.val.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hcard : 2 ≤ s.val.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have he₁ := Finset.card_erase_of_mem ha
  have he₂ := Finset.card_erase_of_mem hb'
  unfold coalesce
  dsimp only
  split
  · have hi := Finset.card_insert_le (a.1, unresolved (a.2 ∪ b.2)) ((s.val.erase a).erase b)
    simp only at hi ⊢
    omega
  · simp only
    omega

private theorem no_complete_unresolved (material : Material L n) (hn : 0 < n)
    (locus : Fin L) : ¬ completedLocus (unresolved material) locus := by
  intro h
  have hall : completedLocus material locus :=
    fun sample ↦ unresolved_subset material (h sample)
  exact unresolved_complete hall ⟨0, hn⟩ (h ⟨0, hn⟩)

private theorem member_coalesce (s : State D L n) (a b : Lineage D L n)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (hab : a ≠ b) (hd : a.1 = b.1)
    (c : Lineage D L n) :
    c ∈ (coalesce s a b ha hb hab hd).val ↔
      (c ∈ s.val ∧ c ≠ a ∧ c ≠ b) ∨
      ((unresolved (a.2 ∪ b.2)).Nonempty ∧ c = (a.1, unresolved (a.2 ∪ b.2))) := by
  classical
  unfold coalesce
  dsimp only
  split <;> simp_all only [Finset.mem_insert, Finset.mem_erase] <;> tauto

theorem sampleComplete_coalesce (s : State D L n) (hs : SampleComplete s)
    (a b : Lineage D L n) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (hab : a ≠ b) (hd : a.1 = b.1) :
    SampleComplete (coalesce s a b ha hb hab hd) := by
  classical
  have outside : ∀ c ∈ s.val, c ≠ a → c ≠ b → ∀ token ∈ c.2,
      ¬ completedLocus (a.2 ∪ b.2) token.1 := by
    intro c hc hca hcb token ht hcomplete
    rcases Finset.mem_union.mp (hcomplete token.2) with hta | htb
    · exact Finset.disjoint_left.mp (s.property.2 hc ha hca) ht hta
    · exact Finset.disjoint_left.mp (s.property.2 hc hb hcb) ht htb
  constructor
  · intro c hc token ht sample
    obtain ⟨old, hold, htoken, hnot⟩ : ∃ old ∈ s.val, token ∈ old.2 ∧
        ¬ completedLocus (a.2 ∪ b.2) token.1 := by
      rcases (member_coalesce s a b ha hb hab hd c).mp hc with ⟨hc, hca, hcb⟩ | ⟨_, rfl⟩
      · exact ⟨c, hc, ht, outside c hc hca hcb token ht⟩
      · have hfilter := Finset.mem_filter.mp ht
        rcases Finset.mem_union.mp hfilter.1 with hta | htb
        · exact ⟨a, ha, hta, hfilter.2⟩
        · exact ⟨b, hb, htb, hfilter.2⟩
    obtain ⟨d, hdmem, hdtoken⟩ := hs.1 old hold token htoken sample
    by_cases hda : d = a ∨ d = b
    · have hnew : (token.1, sample) ∈ unresolved (a.2 ∪ b.2) := by
        apply Finset.mem_filter.mpr
        constructor
        · rcases hda with rfl | rfl
          · exact Finset.mem_union_left _ hdtoken
          · exact Finset.mem_union_right _ hdtoken
        · exact hnot
      refine ⟨(a.1, unresolved (a.2 ∪ b.2)), ?_, hnew⟩
      exact (member_coalesce s a b ha hb hab hd _).mpr (Or.inr ⟨⟨_, hnew⟩, rfl⟩)
    · refine ⟨d, ?_, hdtoken⟩
      exact (member_coalesce s a b ha hb hab hd _).mpr
        (Or.inl ⟨hdmem, fun h ↦ hda (Or.inl h), fun h ↦ hda (Or.inr h)⟩)
  · intro c hc locus
    rcases (member_coalesce s a b ha hb hab hd c).mp hc with ⟨hc, _, _⟩ | ⟨hne, rfl⟩
    · exact hs.2 c hc locus
    · obtain ⟨token, _⟩ := hne
      exact no_complete_unresolved _ (Nat.zero_lt_of_lt token.2.isLt) locus


theorem sampleComplete_migrate (s : State D L n) (hs : SampleComplete s)
    (a : Lineage D L n) (ha : a ∈ s.val) (destination : Fin D) :
    SampleComplete (migrate s a ha destination) := by
  classical
  constructor
  · intro c hc token ht sample
    have hold : ∃ old ∈ s.val, token ∈ old.2 := by
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨a, ha, ht⟩
      · exact ⟨c, (Finset.mem_erase.mp hc).2, ht⟩
    obtain ⟨old, hold, htoken⟩ := hold
    obtain ⟨d, hd, hdt⟩ := hs.1 old hold token htoken sample
    by_cases hda : d = a
    · subst d
      exact ⟨(destination, a.2), Finset.mem_insert_self _ _, hdt⟩
    · exact ⟨d, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hda, hd⟩), hdt⟩
  · intro c hc locus
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hs.2 a ha locus
    · exact hs.2 c (Finset.mem_erase.mp hc).2 locus

theorem sampleComplete_relabel (s : State D L n) (hs : SampleComplete s)
    (destination : Fin D → Fin D) : SampleComplete (relabelDemes s destination) := by
  classical
  constructor
  · intro c hc token ht sample
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d, hd, hdt⟩ := hs.1 old hold token ht sample
    exact ⟨(destination d.1, d.2), Finset.mem_image.mpr ⟨d, hd, rfl⟩, hdt⟩
  · intro c hc locus
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    exact hs.2 old hold locus

theorem sampleComplete_recombine (s : State D L n) (hs : SampleComplete s)
    (a : Lineage D L n) (ha : a ∈ s.val) (cut : Fin (L + 1))
    (hl : (leftMaterial a.2 cut).Nonempty) (hr : (rightMaterial a.2 cut).Nonempty) :
    SampleComplete (recombine s a ha cut hl hr) := by
  classical
  constructor
  · intro c hc token ht sample
    have hold : ∃ old ∈ s.val, token ∈ old.2 := by
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨a, ha, (Finset.mem_filter.mp ht).1⟩
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact ⟨a, ha, (Finset.mem_filter.mp ht).1⟩
        · exact ⟨c, (Finset.mem_erase.mp hc).2, ht⟩
    obtain ⟨old, hold, htoken⟩ := hold
    obtain ⟨d, hd, hdt⟩ := hs.1 old hold token htoken sample
    by_cases hda : d = a
    · subst d
      by_cases hcut : token.1.val < cut.val
      · refine ⟨(a.1, leftMaterial a.2 cut), ?_, Finset.mem_filter.mpr ⟨hdt, hcut⟩⟩
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact ⟨(a.1, rightMaterial a.2 cut), Finset.mem_insert_self _ _,
          Finset.mem_filter.mpr ⟨hdt, hcut⟩⟩
    · exact ⟨d, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hda, hd⟩)), hdt⟩
  · intro c hc locus
    rcases Finset.mem_insert.mp hc with rfl | hc
    · intro hall
      exact hs.2 a ha locus (fun sample ↦ (Finset.mem_filter.mp (hall sample)).1)
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · intro hall
        exact hs.2 a ha locus (fun sample ↦ (Finset.mem_filter.mp (hall sample)).1)
      · exact hs.2 c (Finset.mem_erase.mp hc).2 locus

theorem sampleComplete_proposal (s : State D L n) (hs : SampleComplete s)
    (event : Option (Channel s)) : SampleComplete (proposalNext s event) := by
  rcases event with _ | (event | (event | event))
  · exact hs
  · exact sampleComplete_migrate s hs _ event.property.1 _
  · exact sampleComplete_coalesce s hs _ _ event.property.1 event.property.2.1
      event.property.2.2.1 event.property.2.2.2
  · exact sampleComplete_recombine s hs _ event.property.1 _
      event.property.2.1 event.property.2.2

theorem sampleComplete_terminal {s : State D L n} (hs : SampleComplete s)
    {count : ℕ} (trace : Trace count s) : SampleComplete (terminal trace) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (sampleComplete_proposal s hs trace.1) trace.2


def emptyState : State D L n := ⟨∅, valid_empty⟩

private theorem channel_empty (event : Channel (emptyState : State D L n)) : False := by
  rcases event with event | (event | event)
  all_goals exact Finset.notMem_empty _ event.property.1

private theorem empty_proposal_mass (rates : Rates D L) :
    (proposalLaw rates (emptyState : State D L n)).mass none = 1 := by
  have hzero : totalRate rates (emptyState : State D L n) = 0 := by
    apply Finset.sum_eq_zero
    intro event _
    exact (channel_empty event).elim
  simp [proposalLaw, hzero]

/-- All active material resides in the specified ancestral population. -/
def SupportedAt (deme : Fin D) (s : State D L n) : Prop :=
  ∀ a ∈ s.val, a.1 = deme

theorem supportedAt_empty (deme : Fin D) : SupportedAt deme (emptyState : State D L n) := by
  simp [SupportedAt, emptyState]

theorem supportedAt_relabel (deme : Fin D) (s : State D L n) :
    SupportedAt deme (relabelDemes s (fun _ ↦ deme)) := by
  intro a ha
  obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp ha
  rfl

private theorem supportedAt_coalesce (deme : Fin D) (s : State D L n)
    (hs : SupportedAt deme s) (event : CoalescenceChannel s) :
    SupportedAt deme (nextState s (.inr (.inl event))) := by
  intro c hc
  rcases (member_coalesce s _ _ event.property.1 event.property.2.1
    event.property.2.2.1 event.property.2.2.2 c).mp hc with ⟨hc, _, _⟩ | ⟨_, rfl⟩
  · exact hs c hc
  · exact hs event.val.1 event.property.1

/-- Zero-rate migration marks have zero mass and therefore cannot invalidate
single-population support on any positive-probability history. -/
theorem supportedAt_proposal (rates : Rates D L) (deme : Fin D)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : State D L n) (hs : SupportedAt deme s) (event : Option (Channel s))
    (hpos : 0 < (proposalLaw rates s).mass event) : SupportedAt deme (proposalNext s event) := by
  classical
  rcases event with _ | (event | (event | event))
  · exact hs
  · have hsource := hs _ event.property.1
    change 0 < rates.migration event.val.1.1 event.val.2 / dominatingRate (n := n) rates at hpos
    rw [hsource, hisolated, zero_div] at hpos
    exact hpos.false.elim
  · exact supportedAt_coalesce deme s hs event
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hs event.val.1 event.property.1
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hs event.val.1 event.property.1
      · exact hs c (Finset.mem_erase.mp hc).2

theorem supportedAt_terminal (rates : Rates D L) (deme : Fin D)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    {count : ℕ} (s : State D L n) (hs : SupportedAt deme s) (trace : Trace count s)
    (hpos : 0 < traceMass rates s trace) : SupportedAt deme (terminal trace) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih =>
      change 0 < (proposalLaw rates s).mass trace.1 *
        traceMass rates (proposalNext s trace.1) trace.2 at hpos
      have hfirst := pos_of_mul_pos_left hpos (traceMass_nonneg rates _ trace.2)
      have hrest := pos_of_mul_pos_right hpos ((proposalLaw rates s).mass_nonneg trace.1)
      exact ih _ (supportedAt_proposal rates deme hisolated s hs trace.1 hfirst) trace.2 hrest

/-- A strictly positive lower bound on a specified ordered coalescence proposal
in one ancestral population. It remains well-defined for empty sample spaces. -/
noncomputable def coalescenceFloor (rates : Rates D L) (deme : Fin D) : ℝ :=
  (1 / (4 * rates.populationSize deme)) /
    (dominatingRate (n := n) rates + 1 / (4 * rates.populationSize deme))

theorem coalescenceFloor_pos (rates : Rates D L) (deme : Fin D) :
    0 < coalescenceFloor (n := n) rates deme := by
  have hc : 0 < 1 / (4 * rates.populationSize deme) := one_div_pos.mpr (mul_pos (by norm_num)
    (rates.size_pos deme))
  exact div_pos hc (add_pos (dominatingRate_pos (n := n) rates) hc)

theorem coalescenceFloor_lt_one (rates : Rates D L) (deme : Fin D) :
    coalescenceFloor (n := n) rates deme < 1 := by
  have hc : 0 < 1 / (4 * rates.populationSize deme) := one_div_pos.mpr (mul_pos (by norm_num)
    (rates.size_pos deme))
  unfold coalescenceFloor
  apply (div_lt_one (add_pos (dominatingRate_pos (n := n) rates) hc)).mpr
  linarith [dominatingRate_pos (n := n) rates]

private theorem coalescenceFloor_le_mass (rates : Rates D L) (deme : Fin D) (s : State D L n)
    (hsupported : SupportedAt deme s) (event : CoalescenceChannel s) :
    coalescenceFloor (n := n) rates deme ≤
      (proposalLaw rates s).mass (some (.inr (.inl event))) := by
  have hc : 0 < 1 / (4 * rates.populationSize deme) := one_div_pos.mpr (mul_pos (by norm_num)
    (rates.size_pos deme))
  have hd : event.val.1.1 = deme := hsupported _ event.property.1
  change _ ≤ (1 / (4 * rates.populationSize event.val.1.1)) / dominatingRate (n := n) rates
  rw [hd]
  exact div_le_div_of_nonneg_left hc.le (dominatingRate_pos (n := n) rates)
    (le_add_of_nonneg_right hc.le)

/-- From every sampled ancestral state in one population, an explicitly
positive-probability sequence of at most `L*n` coalescence proposals completes
all loci. Extra proposals after completion are null events of probability one. -/
theorem exists_completion_trace (rates : Rates D L) (deme : Fin D) (count : ℕ)
    (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hcount : s.val.card ≤ count) :
    ∃ trace : Trace count s, (terminal trace).val = ∅ ∧
      coalescenceFloor (n := n) rates deme ^ count ≤ traceMass rates s trace := by
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
        change _ ≤ (proposalLaw rates emptyState).mass none * traceMass rates emptyState rest
        rw [empty_proposal_mass, one_mul]
        rw [pow_succ']
        exact (mul_le_of_le_one_left (pow_nonneg (coalescenceFloor_pos rates deme).le count)
          (coalescenceFloor_lt_one rates deme).le).trans hmass
      · have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (hs.nontrivial hnonempty)
        let event : CoalescenceChannel s := ⟨(a, b), ha, hb, hab, (hsupported a ha).trans
          (hsupported b hb).symm⟩
        let next := proposalNext s (some (.inr (.inl event)))
        have hnext : SampleComplete next := sampleComplete_proposal s hs _
        have hnextcard : next.val.card ≤ count := by
          have hlt := coalesce_count_lt s a b ha hb hab ((hsupported a ha).trans (hsupported b
            hb).symm)
          change (coalesce s a b ha hb hab ((hsupported a ha).trans (hsupported b
            hb).symm)).val.card ≤ count
          omega
        obtain ⟨rest, hrest, hmass⟩ := ih next hnext (supportedAt_coalesce deme s hsupported
          event) hnextcard
        refine ⟨⟨some (.inr (.inl event)), rest⟩, hrest, ?_⟩
        change _ ≤ (proposalLaw rates s).mass (some (.inr (.inl event))) * traceMass rates next rest
        rw [pow_succ']
        exact mul_le_mul (coalescenceFloor_le_mass rates deme s hsupported event) hmass
          (pow_nonneg (coalescenceFloor_pos rates deme).le _) ((proposalLaw rates s).mass_nonneg _)


noncomputable def unfinished (s : State D L n) : ℝ := if s.val = ∅ then 0 else 1

noncomputable def survival (rates : Rates D L) (count : ℕ) (s : State D L n) : ℝ :=
  (traceLaw rates count s).expectation (fun trace ↦ unfinished (terminal trace))

theorem unfinished_nonneg (s : State D L n) : 0 ≤ unfinished s := by
  classical
  unfold unfinished
  split <;> norm_num

theorem unfinished_le_one (s : State D L n) : unfinished s ≤ 1 := by
  classical
  unfold unfinished
  split <;> norm_num

theorem survival_nonneg (rates : Rates D L) (count : ℕ) (s : State D L n) :
    0 ≤ survival rates count s :=
  Finset.sum_nonneg (fun trace _ ↦
    mul_nonneg (traceMass_nonneg rates s trace) (unfinished_nonneg _))

theorem survival_le_one (rates : Rates D L) (count : ℕ) (s : State D L n) :
    survival rates count s ≤ 1 := by
  calc
    survival rates count s ≤ ∑ trace : Trace count s, traceMass rates s trace := by
      apply Finset.sum_le_sum
      intro trace _
      exact mul_le_of_le_one_right (traceMass_nonneg rates s trace) (unfinished_le_one _)
    _ = 1 := traceMass_sum rates count s

private theorem terminal_empty {count : ℕ} (trace : Trace count (emptyState : State D L n)) :
    (terminal trace).val = ∅ := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      cases event with
      | none => exact ih rest
      | some event => exact (channel_empty event).elim

theorem survival_empty (rates : Rates D L) (count : ℕ) :
    survival rates count (emptyState : State D L n) = 0 := by
  classical
  unfold survival expectation unfinished
  simp only [terminal_empty, ↓reduceIte, mul_zero, Finset.sum_const_zero]

private theorem survival_succ (rates : Rates D L) (count : ℕ) (s : State D L n) :
    survival rates (count + 1) s =
      (proposalLaw rates s).expectation (fun event ↦ survival rates count (proposalNext s
        event)) := by
  exact trace_expectation_succ rates count s _

/-- Survival probabilities compose through the same marked genealogy law,
retaining dependence on the entire current ancestral configuration. -/
theorem survival_add (rates : Rates D L) (first rest : ℕ) (s : State D L n) :
    survival rates (first + rest) s =
      (traceLaw rates first s).expectation (fun trace ↦ survival rates rest (terminal trace)) := by
  induction first generalizing s with
  | zero =>
      rw [Nat.zero_add]
      simp only [traceLaw, expectation, Trace, traceMass, terminal, Fintype.sum_unique, one_mul]
  | succ first ih =>
      rw [Nat.succ_add, survival_succ, trace_expectation_succ]
      unfold expectation
      apply Finset.sum_congr rfl
      intro event _
      dsimp only
      rw [ih]
      rfl

/-- A demographic-rate-derived bound on the probability that ancestral
material remains after one block of `L*n` uniformization proposals. -/
theorem survival_block_bound (rates : Rates D L) (deme : Fin D) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    survival rates (L * n) s ≤ 1 - coalescenceFloor (n := n) rates deme ^ (L * n) := by
  classical
  obtain ⟨chosen, hchosen, hmass⟩ :=
    exists_completion_trace rates deme (L * n) s hs hsupported (lineage_count_bound s)
  have hchosenZero : unfinished (terminal chosen) = 0 := by simp [unfinished, hchosen]
  have htotal : survival rates (L * n) s + traceMass rates s chosen ≤ 1 := by
    rw [← traceMass_sum rates (L * n) s]
    unfold survival expectation traceLaw
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ chosen)]
    simp only [hchosenZero, mul_zero, add_zero]
    rw [← Finset.sum_erase_add Finset.univ (fun trace ↦ traceMass rates s trace)
      (Finset.mem_univ chosen)]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro trace _
    exact mul_le_of_le_one_right (traceMass_nonneg rates s trace) (unfinished_le_one _)
  linarith

noncomputable def blockSurvivalBound (rates : Rates D L) (deme : Fin D) : ℝ :=
  1 - coalescenceFloor (n := n) rates deme ^ (L * n)

theorem blockSurvivalBound_nonneg (rates : Rates D L) (deme : Fin D) :
    0 ≤ blockSurvivalBound (n := n) rates deme :=
  sub_nonneg.mpr (pow_le_one₀ (coalescenceFloor_pos rates deme).le (coalescenceFloor_lt_one
    rates deme).le)

theorem blockSurvivalBound_lt_one (rates : Rates D L) (deme : Fin D) :
    blockSurvivalBound (n := n) rates deme < 1 := by
  unfold blockSurvivalBound
  exact sub_lt_self _ (pow_pos (coalescenceFloor_pos rates deme) _)

private theorem survival_block_relative (rates : Rates D L) (deme : Fin D) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    survival rates (L * n) s ≤ blockSurvivalBound (n := n) rates deme * unfinished s := by
  classical
  by_cases h : s.val = ∅
  · have he : s = emptyState := Subtype.ext h
    subst s
    rw [survival_empty]
    simp [unfinished, emptyState]
  · simpa [unfinished, h, blockSurvivalBound] using survival_block_bound rates deme s hs hsupported

/-- The final panmictic ancestry has a geometric termination bound despite
arbitrary finite recombination rates. The constant is deliberately conservative. -/
theorem survival_geometric (rates : Rates D L) (deme : Fin D) (blocks : ℕ) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    survival rates (L * n * blocks) s ≤ blockSurvivalBound (n := n) rates deme ^ blocks := by
  induction blocks with
  | zero => simpa using survival_le_one rates 0 s
  | succ blocks ih =>
      rw [Nat.mul_succ, survival_add]
      calc
        (traceLaw rates (L * n * blocks) s).expectation
            (fun trace ↦ survival rates (L * n) (terminal trace)) ≤
            (traceLaw rates (L * n * blocks) s).expectation
              (fun trace ↦ blockSurvivalBound (n := n) rates deme * unfinished (terminal
                trace)) := by
          apply Finset.sum_le_sum
          intro trace _
          by_cases hmass : traceMass rates s trace = 0
          · change traceMass rates s trace * _ ≤ traceMass rates s trace * _
            simp [hmass]
          · have hpos := lt_of_le_of_ne (traceMass_nonneg rates s trace) (Ne.symm hmass)
            exact mul_le_mul_of_nonneg_left
              (survival_block_relative rates deme _ (sampleComplete_terminal hs trace)
                (supportedAt_terminal rates deme hisolated s hsupported trace hpos))
              (traceMass_nonneg rates s trace)
        _ = blockSurvivalBound (n := n) rates deme * survival rates (L * n * blocks) s := by
          unfold survival expectation
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro trace _
          ring
        _ ≤ blockSurvivalBound (n := n) rates deme * blockSurvivalBound (n := n) rates deme ^
          blocks :=
          mul_le_mul_of_nonneg_left ih (blockSurvivalBound_nonneg rates deme)
        _ = blockSurvivalBound (n := n) rates deme ^ (blocks + 1) := (pow_succ' _ _).symm


private theorem survival_le_unfinished (rates : Rates D L) (count : ℕ) (s : State D L n) :
    survival rates count s ≤ unfinished s := by
  classical
  by_cases h : s.val = ∅
  · have he : s = emptyState := Subtype.ext h
    subst s
    rw [survival_empty]
    simp [unfinished, emptyState]
  · simpa [unfinished, h] using survival_le_one rates count s

theorem survival_antitone (rates : Rates D L) (s : State D L n) :
    Antitone (fun count ↦ survival rates count s) := by
  intro first second h
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le h
  dsimp only
  rw [survival_add]
  apply Finset.sum_le_sum
  intro trace _
  exact mul_le_mul_of_nonneg_left (survival_le_unfinished rates rest (terminal trace))
    (traceMass_nonneg rates s trace)

theorem survival_bound (rates : Rates D L) (deme : Fin D) (count : ℕ) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    survival rates count s ≤ blockSurvivalBound (n := n) rates deme ^ (count / (L * n)) :=
  (survival_antitone rates s (Nat.mul_div_le count (L * n))).trans
    (survival_geometric rates deme (count / (L * n)) s hs hsupported hisolated)

/-- The probability of unfinished ancestry tends to zero. This is derived from
sample preservation and the actual coalescence rates, without an assumed
absorption hypothesis. -/
theorem survival_tendsto_zero (rates : Rates D L) (deme : Fin D) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    Filter.Tendsto (fun count ↦ survival rates count s) Filter.atTop (nhds 0) := by
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
    exact squeeze_zero (fun count ↦ survival_nonneg rates count s)
      (fun count ↦ survival_bound rates deme count s hs hsupported hisolated)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (blockSurvivalBound_nonneg rates deme)
        (blockSurvivalBound_lt_one rates deme)).comp hdiv)


/-- Exact mass of first completion at a proposal index, including already
complete initial configurations at index zero. -/
noncomputable def completionMass (rates : Rates D L) (s : State D L n) : ℕ → ℝ
  | 0 => 1 - survival rates 0 s
  | count + 1 => survival rates count s - survival rates (count + 1) s

theorem completionMass_nonneg (rates : Rates D L) (s : State D L n) (count : ℕ) :
    0 ≤ completionMass rates s count := by
  cases count with
  | zero => exact sub_nonneg.mpr (survival_le_one rates 0 s)
  | succ count => exact sub_nonneg.mpr (survival_antitone rates s (Nat.le_succ count))

theorem completionMass_partial_sum (rates : Rates D L) (s : State D L n) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 1), completionMass rates s index) =
      1 - survival rates count s := by
  induction count with
  | zero => simp [completionMass]
  | succ count ih =>
      rw [Finset.sum_range_succ, ih, completionMass]
      ring

/-- The exact first-completion law has total mass one in final panmixia.
There is no residual probability mass at an infinite completion time. -/
theorem completionMass_hasSum (rates : Rates D L) (deme : Fin D) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) : HasSum (completionMass
      rates s) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (completionMass_nonneg rates s) 1).mpr
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simp only [completionMass_partial_sum]
  simpa using tendsto_const_nhds.sub (survival_tendsto_zero rates deme s hs hsupported hisolated)


theorem survival_zero (rates : Rates D L) (s : State D L n) :
    survival rates 0 s = unfinished s := by
  simp [survival, traceLaw, expectation, Trace, traceMass, terminal]

private theorem completionMass_succ (rates : Rates D L) (s : State D L n) (count : ℕ) :
    completionMass rates s (count + 1) = unfinished s *
      (proposalLaw rates s).expectation
        (fun event ↦ completionMass rates (proposalNext s event) count) := by
  classical
  by_cases h : s.val = ∅
  · have he : s = emptyState := Subtype.ext h
    subst s
    rw [completionMass, survival_empty, survival_empty]
    simp [unfinished, emptyState]
  · have hu : unfinished s = 1 := by simp [unfinished, h]
    rw [hu, one_mul]
    cases count with
    | zero =>
        simp only [completionMass, survival_zero]
        rw [hu, survival_succ]
        simp only [expectation, mul_sub, mul_one, Finset.sum_sub_distrib,
          FiniteReportLaw.mass_sum, survival_zero]
    | succ count =>
        simp only [completionMass, survival_succ, expectation, mul_sub, Finset.sum_sub_distrib]

/-- Indicator that a marked trace ends at the first completion, so completed
histories are counted once rather than again after arbitrary null padding. -/
noncomputable def stoppingIndicator : {count : ℕ} → (s : State D L n) → Trace count s → ℝ
  | 0, s, _ => 1 - unfinished s
  | _count + 1, s, ⟨_event, rest⟩ => unfinished s * stoppingIndicator _ rest

theorem stoppingIndicator_nonneg {count : ℕ} (s : State D L n) (trace : Trace count s) :
    0 ≤ stoppingIndicator s trace := by
  induction count generalizing s with
  | zero => exact sub_nonneg.mpr (unfinished_le_one s)
  | succ count ih => exact mul_nonneg (unfinished_nonneg s) (ih _ trace.2)

/-- Probability mass of a particular finite marked history whose final event
is its first complete ancestral configuration. -/
noncomputable def stoppingTraceMass (rates : Rates D L) {count : ℕ}
    (s : State D L n) (trace : Trace count s) : ℝ :=
  traceMass rates s trace * stoppingIndicator s trace

theorem stoppingTraceMass_nonneg (rates : Rates D L) {count : ℕ}
    (s : State D L n) (trace : Trace count s) : 0 ≤ stoppingTraceMass rates s trace :=
  mul_nonneg (traceMass_nonneg rates s trace) (stoppingIndicator_nonneg s trace)

/-- Summing stopped histories of a fixed length gives exactly the derived
first-completion index probability. -/
theorem stoppingTraceMass_sum (rates : Rates D L) (count : ℕ) (s : State D L n) :
    (∑ trace : Trace count s, stoppingTraceMass rates s trace) = completionMass rates s count := by
  induction count generalizing s with
  | zero =>
      simp [stoppingTraceMass, traceMass, stoppingIndicator, Trace, completionMass, survival_zero]
  | succ count ih =>
      change (traceLaw rates (count + 1) s).expectation (stoppingIndicator s) = _
      rw [trace_expectation_succ, completionMass_succ]
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro event _
      dsimp only [stoppingIndicator]
      have hinner : (∑ rest : Trace count (proposalNext s event),
          (traceLaw rates count (proposalNext s event)).mass rest *
            (unfinished s * stoppingIndicator (proposalNext s event) rest)) =
          unfinished s * completionMass rates (proposalNext s event) count := by
        rw [← ih, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rest _
        change traceMass rates _ rest * (unfinished s * stoppingIndicator _ rest) =
          unfinished s * (traceMass rates _ rest * stoppingIndicator _ rest)
        ring
      rw [hinner]
      ring

/-- Countably many genuinely stopped marked ancestral histories form a
normalized law in final panmixia. This law retains all genealogy event marks. -/
theorem stoppingTraceMass_hasSum (rates : Rates D L) (deme : Fin D) (s : State D L n)
    (hs : SampleComplete s) (hsupported : SupportedAt deme s)
    (hisolated : ∀ destination, rates.migration deme destination = 0) :
    HasSum (fun count ↦ ∑ trace : Trace count s, stoppingTraceMass rates s trace) 1 := by
  simpa only [stoppingTraceMass_sum] using completionMass_hasSum rates deme s hs hsupported
    hisolated


/-- Applying the final complete population merger supplies the support
hypothesis for the normalized stopped genealogy law on the original deme type. -/
theorem stoppingTraceMass_hasSum_after_relocation (rates : Rates D L) (deme : Fin D)
    (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : State D L n) (hs : SampleComplete s) :
    HasSum (fun count ↦ ∑ trace : Trace count (relabelDemes s (fun _ ↦ deme)),
      stoppingTraceMass rates (relabelDemes s (fun _ ↦ deme)) trace) 1 :=
  stoppingTraceMass_hasSum rates deme _ (sampleComplete_relabel s hs _)
    (supportedAt_relabel deme s) hisolated

end Descent.Portability.AncestralAbsorptionLaw
