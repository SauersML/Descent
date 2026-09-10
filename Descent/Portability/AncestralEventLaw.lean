/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.FiniteGenomeAncestry
import Descent.Portability.ExactFiniteHistoryLaw

assert_below Descent.Decision Descent.Program

/-!
Ancestral event probabilities constructed from diploid population sizes,
backward migration rates, and per-breakpoint recombination rates. The channels
operate on sampled descendant material, including common ancestry of disjoint
segments and recombination across gaps. Ordered common-ancestor pairs carry
half the unordered-pair rate. Uniformization adds explicit null proposals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralEventLaw

open Coalescent.FiniteGenomeAncestry FiniteReportLaw

variable {D L n : ℕ}

structure Rates (D L : ℕ) where
  populationSize : Fin D → ℝ
  size_pos : ∀ d, 0 < populationSize d
  migration : Fin D → Fin D → ℝ
  migration_nonneg : ∀ a b, 0 ≤ migration a b
  recombination : Fin (L + 1) → ℝ
  recombination_nonneg : ∀ cut, 0 ≤ recombination cut

abbrev MigrationChannel (s : State D L n) :=
  {pair : Lineage D L n × Fin D // pair.1 ∈ s.val ∧ pair.2 ≠ pair.1.1}

abbrev CoalescenceChannel (s : State D L n) :=
  {pair : Lineage D L n × Lineage D L n //
    pair.1 ∈ s.val ∧ pair.2 ∈ s.val ∧ pair.1 ≠ pair.2 ∧ pair.1.1 = pair.2.1}

abbrev RecombinationChannel (s : State D L n) :=
  {pair : Lineage D L n × Fin (L + 1) // pair.1 ∈ s.val ∧
    (leftMaterial pair.1.2 pair.2).Nonempty ∧ (rightMaterial pair.1.2 pair.2).Nonempty}

abbrev Channel (s : State D L n) :=
  MigrationChannel s ⊕ (CoalescenceChannel s ⊕ RecombinationChannel s)

noncomputable instance channelFintype (s : State D L n) : Fintype (Channel s) := by
  classical
  exact Fintype.ofFinite (Channel s)

noncomputable def nextState (s : State D L n) : Channel s → State D L n
  | .inl channel => migrate s channel.val.1 channel.property.1 channel.val.2
  | .inr (.inl channel) => coalesce s channel.val.1 channel.val.2
      channel.property.1 channel.property.2.1 channel.property.2.2.1 channel.property.2.2.2
  | .inr (.inr channel) => recombine s channel.val.1 channel.property.1 channel.val.2
      channel.property.2.1 channel.property.2.2

noncomputable def eventRate (rates : Rates D L) (s : State D L n) : Channel s → ℝ
  | .inl channel => rates.migration channel.val.1.1 channel.val.2
  | .inr (.inl channel) => 1 / (4 * rates.populationSize channel.val.1.1)
  | .inr (.inr channel) => rates.recombination channel.val.2

theorem eventRate_nonneg (rates : Rates D L) (s : State D L n) (channel : Channel s) :
    0 ≤ eventRate rates s channel := by
  rcases channel with channel | (channel | channel)
  · exact rates.migration_nonneg _ _
  · exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (rates.size_pos _).le)
  · exact rates.recombination_nonneg _

/-- Two ordered channels give the diploid unordered-pair rate `1 / (2 N)`. -/
theorem unordered_pair_rate (rates : Rates D L) (deme : Fin D) :
    1 / (4 * rates.populationSize deme) + 1 / (4 * rates.populationSize deme) =
      1 / (2 * rates.populationSize deme) := by
  ring

noncomputable def totalRate (rates : Rates D L) (s : State D L n) : ℝ :=
  ∑ channel, eventRate rates s channel

theorem totalRate_nonneg (rates : Rates D L) (s : State D L n) :
    0 ≤ totalRate rates s :=
  Finset.sum_nonneg (fun channel _ ↦ eventRate_nonneg rates s channel)

/-- Conditional on an ancestral event occurring, its channel has rate divided
by total rate. Zero-rate absorbing configurations have no such conditional law. -/
noncomputable def jumpLaw (rates : Rates D L) (s : State D L n)
    (h : 0 < totalRate rates s) : FiniteReportLaw (Channel s) where
  mass := fun channel ↦ eventRate rates s channel / totalRate rates s
  mass_nonneg := fun channel ↦ div_nonneg (eventRate_nonneg rates s channel) h.le
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt h)

noncomputable def jumpStateLaw (rates : Rates D L) (s : State D L n)
    (h : 0 < totalRate rates s) : FiniteReportLaw (State D L n) :=
  (jumpLaw rates s h).pushforward (nextState s)

theorem jump_expectation (rates : Rates D L) (s : State D L n)
    (h : 0 < totalRate rates s) (readout : State D L n → ℝ) :
    (jumpStateLaw rates s h).expectation readout =
      (∑ channel, eventRate rates s channel * readout (nextState s channel)) /
        totalRate rates s := by
  rw [jumpStateLaw, expectation_pushforward]
  unfold expectation jumpLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro channel _
  ring

/-- A finite dominating intensity derived from the finite ancestry state space.
This is a valid uniformization rate, not a claim of an efficient numerical bound. -/
noncomputable def dominatingRate (rates : Rates D L) : ℝ :=
  1 + ∑ s : State D L n, totalRate rates s

theorem dominatingRate_pos (rates : Rates D L) : 0 < dominatingRate (n := n) rates := by
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun (s : State D L n) _ ↦ totalRate_nonneg rates s)
  unfold dominatingRate
  linarith

theorem totalRate_le_dominating (rates : Rates D L) (s : State D L n) :
    totalRate rates s ≤ dominatingRate (n := n) rates := by
  have h := Finset.single_le_sum
    (fun (s : State D L n) (_ : s ∈ Finset.univ) ↦ totalRate_nonneg rates s)
    (Finset.mem_univ s)
  unfold dominatingRate
  linarith

noncomputable def proposalLaw (rates : Rates D L) (s : State D L n) :
    FiniteReportLaw (Option (Channel s)) where
  mass := fun channel ↦ match channel with
    | none => 1 - totalRate rates s / dominatingRate (n := n) rates
    | some event => eventRate rates s event / dominatingRate (n := n) rates
  mass_nonneg := by
    intro channel
    cases channel with
    | none =>
        exact sub_nonneg.mpr
          ((div_le_one (dominatingRate_pos (n := n) rates)).mpr (totalRate_le_dominating rates s))
    | some event =>
        exact div_nonneg (eventRate_nonneg rates s event)
          (dominatingRate_pos (n := n) rates).le
  mass_sum := by
    rw [Fintype.sum_option]
    simp only [← Finset.sum_div]
    unfold totalRate
    ring

noncomputable def proposalNext (s : State D L n) : Option (Channel s) → State D L n
  | none => s
  | some event => nextState s event

noncomputable def proposalKernel (rates : Rates D L) (s : State D L n) :
    FiniteReportLaw (State D L n) :=
  (proposalLaw rates s).pushforward (proposalNext s)

/-- The constructed kernel has exactly the ancestral event generator. Null
proposals cancel, including physical events whose next active state coincides. -/
theorem proposal_generator (rates : Rates D L) (s : State D L n)
    (readout : State D L n → ℝ) :
    dominatingRate (n := n) rates * ((proposalKernel rates s).expectation readout - readout s) =
      ∑ channel, eventRate rates s channel * (readout (nextState s channel) - readout s) := by
  rw [proposalKernel, expectation_pushforward]
  unfold expectation proposalLaw proposalNext
  rw [Fintype.sum_option]
  have hn : dominatingRate (n := n) rates ≠ 0 := ne_of_gt (dominatingRate_pos (n := n) rates)
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  unfold totalRate
  field_simp
  ring

end Descent.Portability.AncestralEventLaw
