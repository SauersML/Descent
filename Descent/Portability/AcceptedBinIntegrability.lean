/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DistanceBinnedPortabilityLaw

assert_below Descent.Decision Descent.Program

/-!
Exact decomposition of distance-bin integrability under the shared whole-run
acceptance event. Pairwise terms retain this event until an explicit Gaussian
null-exclusion theorem justifies removing it. No design nondegeneracy is assumed
merely because a learner returned coefficients.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AcceptedBinIntegrability

open MeasureTheory ProbabilityTheory FiniteReportLaw GaussianEffectPortabilityLaw
open DistanceBinnedPortabilityLaw
open scoped ENNReal

variable {D U I S J K : Type*} [Fintype D] [DecidableEq D]
  [Fintype U] [Fintype I] [DecidableEq I] [Fintype S] [Fintype J] [Fintype K]

variable (design : FixedDesign U I S S J K) (targets : TargetCohorts D U S J)

/-- One label/deme contribution, accepted by every deme in the run. -/
noncomputable def acceptedContribution (deme : D) (outcome : I → Bool)
    (effects : K → ℝ) : ℝ := by
  classical
  exact if allValid design targets effects outcome then
    (labelKernel design).weight effects outcome *
      (report (targetDesign design targets deme) effects outcome).getD 0 else 0

omit [Fintype D] [DecidableEq D] in
theorem acceptedContribution_nonneg (deme : D) (outcome : I → Bool) (effects : K → ℝ) :
    0 ≤ acceptedContribution design targets deme outcome effects := by
  classical
  unfold acceptedContribution
  split_ifs
  · exact mul_nonneg ((labelKernel design).weight_nonneg effects outcome)
      (reportValue_nonneg (targetDesign design targets deme) effects outcome)
  · exact le_rfl

theorem acceptedContribution_measurable (deme : D) (outcome : I → Bool) :
    Measurable (acceptedContribution design targets deme outcome) := by
  classical
  exact Measurable.ite (allValid_measurable design targets outcome)
    (((labelKernel design).weight_measurable outcome).mul
      (reportValue_measurable (targetDesign design targets deme) outcome)) measurable_const

omit [DecidableEq D] in
/-- Both sums are inside the same run-level acceptance guard. -/
theorem binInner_eq_accepted_sum (distance : ℕ)
    (hne : (binMembers targets distance).Nonempty) (effects : K → ℝ) :
    binInner design targets distance effects =
      (∑ outcome, ∑ deme ∈ binMembers targets distance,
        acceptedContribution design targets deme outcome effects) /
          (binMembers targets distance).card := by
  classical
  unfold binInner
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases ha : allValid design targets effects outcome
  · simp only [binReport, hne, ha, and_self, ite_true, Option.getD_some,
      DistanceBinnedPortabilityLaw.average, acceptedContribution]
    rw [← mul_div_assoc, Finset.mul_sum]
  · simp [binReport, ha, acceptedContribution]

omit [DecidableEq D] in
/-- Every nonnegative accepted term is controlled by cardinality times the bin. -/
theorem acceptedContribution_le_card_mul (distance : ℕ) (deme : D)
    (hd : deme ∈ binMembers targets distance) (outcome : I → Bool) (effects : K → ℝ) :
    acceptedContribution design targets deme outcome effects ≤
      (binMembers targets distance).card * binInner design targets distance effects := by
  classical
  have hc : (0 : ℝ) < (binMembers targets distance).card := by
    exact_mod_cast (show (binMembers targets distance).Nonempty from ⟨deme, hd⟩).card_pos
  rw [binInner_eq_accepted_sum design targets distance
    (show (binMembers targets distance).Nonempty from ⟨deme, hd⟩)]
  rw [mul_div_cancel₀ _ (ne_of_gt hc)]
  exact (Finset.single_le_sum (fun d _ ↦
    acceptedContribution_nonneg design targets d outcome effects) hd).trans
      (Finset.single_le_sum (fun y _ ↦ Finset.sum_nonneg (fun d _ ↦
        acceptedContribution_nonneg design targets d y effects)) (Finset.mem_univ outcome))

/-- Finiteness of the plotted bin is exactly finiteness of all its accepted
label/deme contributions. This equivalence needs no null-exclusion assumption. -/
theorem bin_integrable_iff_accepted (distance : ℕ)
    (hne : (binMembers targets distance).Nonempty) :
    Integrable (binInner design targets distance) (effectLaw K) ↔
      ∀ deme ∈ binMembers targets distance, ∀ outcome,
        Integrable (acceptedContribution design targets deme outcome) (effectLaw K) := by
  classical
  constructor
  · intro hi deme hd outcome
    apply (hi.const_mul ((binMembers targets distance).card : ℝ)).mono'
      (acceptedContribution_measurable design targets deme outcome).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro effects
    rw [Real.norm_eq_abs,
      abs_of_nonneg (acceptedContribution_nonneg design targets deme outcome effects)]
    exact acceptedContribution_le_card_mul design targets distance deme hd outcome effects
  · intro hi
    have hs : Integrable (fun effects ↦ ∑ outcome, ∑ deme ∈ binMembers targets distance,
        acceptedContribution design targets deme outcome effects) (effectLaw K) := by
      apply integrable_finset_sum
      intro outcome _
      exact integrable_finset_sum _ (fun deme hd ↦ hi deme hd outcome)
    convert hs.div_const ((binMembers targets distance).card : ℝ) using 1
    funext effects
    exact binInner_eq_accepted_sum design targets distance hne effects

/-- The untruncated extended numerator is finite under exactly the same condition. -/
theorem bin_numerator_finite_iff_accepted (distance : ℕ)
    (hne : (binMembers targets distance).Nonempty) :
    binExtendedNumerator design targets distance < ∞ ↔
      ∀ deme ∈ binMembers targets distance, ∀ outcome,
        Integrable (acceptedContribution design targets deme outcome) (effectLaw K) := by
  rw [← binInner_integrable_iff, bin_integrable_iff_accepted design targets distance hne]

omit [DecidableEq D] in
/-- Finite accepted expectations add before division by the number of demes. -/
theorem integral_bin_eq_accepted_sum (distance : ℕ)
    (hne : (binMembers targets distance).Nonempty)
    (hi : ∀ deme ∈ binMembers targets distance, ∀ outcome,
      Integrable (acceptedContribution design targets deme outcome) (effectLaw K)) :
    (∫ effects, binInner design targets distance effects ∂effectLaw K) =
      (∑ outcome, ∑ deme ∈ binMembers targets distance,
        ∫ effects, acceptedContribution design targets deme outcome effects ∂effectLaw K) /
          (binMembers targets distance).card := by
  simp_rw [binInner_eq_accepted_sum design targets distance hne]
  rw [integral_div, integral_finset_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro outcome _
    exact integral_finset_sum _ (fun deme hd ↦ hi deme hd outcome)
  · intro outcome _
    exact integrable_finset_sum _ (fun deme hd ↦ hi deme hd outcome)

omit [Fintype D] [DecidableEq D] in
/-- Removing whole-run acceptance is justified only by an a.e. acceptance
certificate for this particular learned label outcome. -/
theorem acceptedContribution_eq_pair_ae (deme : D) (outcome : I → Bool)
    (ha : ∀ᵐ effects ∂effectLaw K, allValid design targets effects outcome) :
    acceptedContribution design targets deme outcome =ᵐ[effectLaw K]
      (fun effects ↦ (labelKernel design).weight effects outcome *
        (report (targetDesign design targets deme) effects outcome).getD 0) := by
  classical
  filter_upwards [ha] with effects he
  simp [acceptedContribution, he]

/-- Pairwise integrability transfers to the plotted bin only after this common
acceptance hypothesis. No pairwise failure is assumed to survive the guard. -/
theorem bin_integrable_iff_pairwise (distance : ℕ)
    (hne : (binMembers targets distance).Nonempty)
    (ha : ∀ outcome weights, design.learn outcome = some weights →
      ∀ᵐ effects ∂effectLaw K, allValid design targets effects outcome) :
    Integrable (binInner design targets distance) (effectLaw K) ↔
      ∀ deme ∈ binMembers targets distance, ∀ outcome,
        Integrable (fun effects ↦ (labelKernel design).weight effects outcome *
          (report (targetDesign design targets deme) effects outcome).getD 0) (effectLaw K) := by
  rw [bin_integrable_iff_accepted design targets distance hne]
  apply forall_congr'
  intro deme
  apply forall_congr'
  intro _
  apply forall_congr'
  intro outcome
  cases hl : design.learn outcome with
  | none =>
      have hz : acceptedContribution design targets deme outcome = fun _ ↦ 0 := by
        funext effects
        classical
        simp [acceptedContribution, report, targetDesign, hl]
      simp [hz, report, targetDesign, hl]
  | some weights =>
      exact integrable_congr
        (acceptedContribution_eq_pair_ae design targets deme outcome (ha outcome weights hl))

end Descent.Portability.AcceptedBinIntegrability
