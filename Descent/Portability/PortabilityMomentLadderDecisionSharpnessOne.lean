/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderDecisionSharpness

assert_below Descent.Decision Descent.Program

/-!
# The decision rung is sharp: fixation keeps the decision report and moves expected recall

`PortabilityMomentLadderDecision` proves that agreement up to degree one fixes the decision report
of every rule (`decisionReport_eq_of_polynomialsAgreeAt_one`), and that agreement at every degree
fixes the expected per-population recall and precision.  Its Scope leaves open whether a finite
degree fixes the expected recall.  This module settles the first case: degree one fixes neither
the expected recall nor the expected precision.

The events.  `PortabilityMomentLadderDecisionSharpness` shows that the founder events at fractions
`0` and `1` in deme `source` give different expected recall and precision
(`PortabilityMomentLadderDecisionSharpness.expectedPositiveQuotient_founderEventLaw_ne`), and that
every frequency coordinate is a martingale under a founder event
(`PortabilityMomentLadderDecisionSharpness.sum_resamplingMove_coordinate`).

Degree one.  Every monomial in the support of a polynomial of total degree at most one is constant
or a single frequency coordinate.  So for every fraction the expectation of such a polynomial after
the founder event is its value before (`integral_founderEventLaw_of_totalDegree_le_one`), and the
events at fractions `0` and `1` agree up to degree one (`polynomialsAgreeAt_one_founderEventLaw`).
Every rule on every report map then has one decision report under both.

The separation.  Two process laws with one decision report and different expected recall
(`polynomialsAgreeAt_one_and_expectedRecall_ne`) or different expected precision
(`polynomialsAgreeAt_one_and_expectedPrecision_ne`).

Significance.  The expected confusion table, case probability, called fraction and net benefit
cannot see fixation within a population; the expected per-population recall and precision can.  An
expected ratio is not the ratio of expected cells, and it depends on how the cells vary between
realizations of the process, which no polynomial of degree one measures.

Scope.  The two laws are single resampling stages, not neutral epochs of `historyEventKernel`.
Whether some finite degree above one fixes the expected recall or precision is not settled here.

## Empirical status

None.  The bodies here are finite sums over the outcomes of one resampling stage, the monomial
expansion of polynomials of degree at most one and rational arithmetic, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMomentLadderDecisionSharpnessOne

open MeasureTheory ProbabilityTheory MvPolynomial PartialHaplotypeDualGenerator
  NeutralFellerGenerator PartialHaplotypeMicroscopicStages ReplicaMetricInstances
  EndToEndDecisionLaw EndToEndAscertainedWitness PortabilityMomentLadder
  PortabilityMomentLadderDecision PortabilityMomentLadderDecisionSharpness

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Degree one -/

/-- **A founder event keeps the expectation of every polynomial of total degree at most one.**
Every monomial in the support of such a polynomial is constant or a single frequency coordinate,
and every coordinate is a martingale
(`PortabilityMomentLadderDecisionSharpness.sum_resamplingMove_coordinate`).

Assumes: total degree at most one. -/
theorem integral_founderEventLaw_of_totalDegree_le_one (source : Deme) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) (hp : p.totalDegree ≤ 1) :
    ∫ y, polynomialFunction p y ∂(founderEventLaw source ε hε0 hε1 x)
      = polynomialFunction p x := by
  have hmonomial : ∀ m ∈ p.support, ∑ g, x.1 (source, g)
        * eval (resamplingMove source g ε hε0 hε1 x).1 (monomial m (coeff m p))
      = eval x.1 (monomial m (coeff m p)) := by
    intro m hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simp only [eval_monomial, Finsupp.prod_zero_index, mul_one]
      rw [← Finset.sum_mul, x.2.2 source, one_mul]
    · have hdegree : (m.sum fun _ e ↦ e) ≤ 1 := (le_totalDegree hm).trans hp
      obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr hm0
      have hv0 : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
      have hsplit : m v + (m.erase v).sum (fun _ e ↦ e) = m.sum fun _ e ↦ e := by
        conv_rhs => rw [← Finsupp.single_add_erase v m]
        rw [Finsupp.sum_add_index' (h := fun _ (e : ℕ) ↦ e) (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
          Finsupp.sum_single_index (h := fun _ (e : ℕ) ↦ e) rfl]
      have hv1 : m v = 1 := by omega
      have herase : m.erase v = 0 := by
        by_contra hne
        obtain ⟨w, hw⟩ := Finsupp.support_nonempty_iff.mpr hne
        have hw0 : (m.erase v) w ≠ 0 := Finsupp.mem_support_iff.mp hw
        have hle : (m.erase v) w ≤ (m.erase v).sum fun _ e ↦ e :=
          Finset.single_le_sum (fun i _ ↦ Nat.zero_le ((m.erase v) i)) hw
        omega
      have hsingle : m = Finsupp.single v 1 :=
        (Finsupp.single_add_erase v m).symm.trans (by rw [hv1, herase, add_zero])
      have hvalue : ∀ z : FrequencyVariable Deme Locus Allele → ℝ,
          eval z (monomial m (coeff m p)) = coeff m p * z v := fun z ↦ by
        rw [hsingle, eval_monomial, Finsupp.prod_single_index] <;> simp
      simp only [hvalue]
      rw [← sum_resamplingMove_coordinate source ε hε0 hε1 x v, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring
  have hexpand : ∀ z : FrequencyVariable Deme Locus Allele → ℝ,
      eval z p = ∑ m ∈ p.support, eval z (monomial m (coeff m p)) := fun z ↦ by
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
  rw [integral_founderEventLaw source ε hε0 hε1 x p _ fun _ ↦ rfl]
  simp only [polynomialFunction_apply, hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl hmonomial

/-- **The founder events at fractions zero and one agree up to degree one.**  From any state, every
frequency polynomial of total degree at most one has one expectation without the event and after
complete fixation. -/
theorem polynomialsAgreeAt_one_founderEventLaw (source : Deme)
    (x₀ : FrequencyState Deme Locus Allele) :
    PolynomialsAgreeAt 1 (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x₀))
      (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x₀)) x₀ x₀ := by
  intro p hp
  rw [Kernel.const_apply, Kernel.const_apply,
    integral_founderEventLaw_of_totalDegree_le_one source 0 le_rfl zero_le_one x₀ p hp,
    integral_founderEventLaw_of_totalDegree_le_one source 1 zero_le_one le_rfl x₀ p hp]

/-! ## Degree one fixes neither recall nor precision -/

/-- **Degree one does not fix the expected recall.**  From a state `x₀`, the founder events at
fractions zero and one in deme `source` agree on every frequency polynomial of total degree at most
one.  So every rule on every report map has one decision report under both
(`PortabilityMomentLadderDecision.decisionReport_eq_of_polynomialsAgreeAt_one`).  Yet the expected
per-population recall `E[TP / (TP + FN)]` in the source deme is `TP / (TP + FN)` of `x₀` under the
first and `TP` of `x₀` under the second, and these differ.  The conditions hold whenever the source
deme carries called cases and controls with positive frequency.

Assumes: `0 < TP` and `TP + FN < 1` in the source deme at `x₀`. -/
theorem polynomialsAgreeAt_one_and_expectedRecall_ne (source : Deme)
    (x₀ : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (hpositive :
      0 < ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true))
    (hcases : ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true)
      + ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (false, true)
        < 1) :
    PolynomialsAgreeAt 1 (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x₀))
        (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x₀)) x₀ x₀
      ∧ decisionReport (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x₀)) x₀
          report called
        = decisionReport (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x₀)) x₀
          report called
      ∧ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).recallRate
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 0 le_rfl zero_le_one x₀) x₀)
        ≠ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).recallRate
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 1 zero_le_one le_rfl x₀) x₀) := by
  have hagree := polynomialsAgreeAt_one_founderEventLaw source x₀
  refine ⟨hagree, decisionReport_eq_of_polynomialsAgreeAt_one hagree report called, ?_⟩
  rw [(integral_recallRate_precision _ x₀ source report called).1,
    (integral_recallRate_precision _ x₀ source report called).1]
  exact expectedPositiveQuotient_founderEventLaw_ne source x₀ report called (false, true)
    (by decide) hpositive hcases

/-- **Degree one does not fix the expected precision.**  From a state `x₀`, the founder events at
fractions zero and one in deme `source` agree on every frequency polynomial of total degree at most
one and give every rule on every report map one decision report.  Yet the expected per-population
precision `E[TP / (TP + FP)]` in the source deme is `TP / (TP + FP)` of `x₀` under the first and
`TP` of `x₀` under the second, and these differ.  The conditions hold whenever the source deme
carries called cases and uncalled haplotypes with positive frequency.

Assumes: `0 < TP` and `TP + FP < 1` in the source deme at `x₀`. -/
theorem polynomialsAgreeAt_one_and_expectedPrecision_ne (source : Deme)
    (x₀ : FrequencyState Deme Locus Allele) {Score : Type*} [Fintype Score]
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (hpositive :
      0 < ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true))
    (hcalled : ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, true)
      + ((stateLaw x₀ source).pushforward (confusionReport report called)).mass (true, false)
        < 1) :
    PolynomialsAgreeAt 1 (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x₀))
        (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x₀)) x₀ x₀
      ∧ decisionReport (Kernel.const _ (founderEventLaw source 0 le_rfl zero_le_one x₀)) x₀
          report called
        = decisionReport (Kernel.const _ (founderEventLaw source 1 zero_le_one le_rfl x₀)) x₀
          report called
      ∧ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).precision
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 0 le_rfl zero_le_one x₀) x₀)
        ≠ ∫ y, (ruleConfusion ((stateLaw y source).pushforward report) called).precision
          ∂(Kernel.const (FrequencyState Deme Locus Allele)
            (founderEventLaw source 1 zero_le_one le_rfl x₀) x₀) := by
  have hagree := polynomialsAgreeAt_one_founderEventLaw source x₀
  refine ⟨hagree, decisionReport_eq_of_polynomialsAgreeAt_one hagree report called, ?_⟩
  rw [(integral_recallRate_precision _ x₀ source report called).2,
    (integral_recallRate_precision _ x₀ source report called).2]
  exact expectedPositiveQuotient_founderEventLaw_ne source x₀ report called (true, false)
    (by decide) hpositive hcalled

end

end Descent.Portability.PortabilityMomentLadderDecisionSharpnessOne
