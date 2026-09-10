/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianEffectPortabilityLaw

assert_below Descent.Decision Descent.Program

/-!
The plotted distance-bin endpoint: every deme shares the same genetic effects,
training labels and fitted score. All deme ratios must be reportable before a
run is accepted, and a run contributes the equal-deme average at each available
distance. The target/source division precedes both levels of averaging.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DistanceBinnedPortabilityLaw

open MeasureTheory FiniteReportLaw GaussianEffectPortabilityLaw PartialMetricMixture
open scoped ENNReal

variable {D U I S J K : Type*} [Fintype D] [DecidableEq D]
  [Fintype U] [Fintype I] [DecidableEq I] [Fintype S] [Fintype J] [Fintype K]

structure TargetCohorts (D U S J : Type*) [Fintype S] where
  law : D → FiniteReportLaw S
  genotype : D → S → J → ℝ
  index : D → S → U
  distance : D → ℕ

variable (design : FixedDesign U I S S J K) (targets : TargetCohorts D U S J)

noncomputable def targetDesign (deme : D) : FixedDesign U I S S J K :=
  { design with
    target := targets.law deme
    targetGenotype := targets.genotype deme
    targetIndex := targets.index deme }

/-- Changing evaluation deme does not resample effects, labels, or the learner. -/
theorem target_labelKernel (deme : D) :
    labelKernel (targetDesign design targets deme) = labelKernel design := rfl

noncomputable def binMembers (distance : ℕ) : Finset D :=
  Finset.univ.filter (fun deme ↦ targets.distance deme = distance)

noncomputable def average (members : Finset D) (values : D → ℝ) : ℝ :=
  (∑ deme ∈ members, values deme) / members.card

private theorem average_bounds (members : Finset D) (hne : members.Nonempty)
    (values : D → ℝ) (bound : ℝ) (hb : ∀ deme ∈ members, 0 ≤ values deme ∧ values deme ≤ bound) :
    0 ≤ average members values ∧ average members values ≤ bound := by
  have hd : (0 : ℝ) < members.card := by exact_mod_cast hne.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun deme hm ↦ (hb deme hm).1)) hd.le
  · apply (div_le_iff₀ hd).mpr
    calc
      (∑ deme ∈ members, values deme) ≤ ∑ _deme ∈ members, bound :=
        Finset.sum_le_sum (fun deme hm ↦ (hb deme hm).2)
      _ = bound * members.card := by simp [mul_comm]

noncomputable def allValid (effects : K → ℝ) (outcome : I → Bool) : Prop :=
  ∀ deme : D, (report (targetDesign design targets deme) effects outcome).isSome

/-- A common run-level guard, rather than separate conditioning by target deme. -/
theorem allValid_measurable (outcome : I → Bool) :
    MeasurableSet {effects | allValid design targets effects outcome} := by
  unfold allValid
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro deme
  have heq : {effects | (report (targetDesign design targets deme) effects outcome).isSome} =
      {effects | (if (report (targetDesign design targets deme) effects outcome).isSome
        then (1 : ℝ) else 0) = 1} := by
    ext effects
    cases h : report (targetDesign design targets deme) effects outcome <;> simp [h]
  rw [heq]
  exact measurableSet_eq_fun
    (report_defined_measurable (targetDesign design targets deme) outcome) measurable_const

/-- Clip each realized ratio only for a proved integrable approximation. The
run-level acceptance guard and the available distance bins do not change. -/
noncomputable def clippedBinReport (distance : ℕ) (cap : ℝ)
    (effects : K → ℝ) (outcome : I → Bool) : Option ℝ := by
  classical
  exact if (binMembers targets distance).Nonempty ∧ allValid design targets effects outcome then
    some (average (binMembers targets distance) (fun deme ↦
      min ((report (targetDesign design targets deme) effects outcome).getD 0) cap))
    else none

noncomputable def binReport (distance : ℕ) (effects : K → ℝ) (outcome : I → Bool) : Option ℝ := by
  classical
  exact if (binMembers targets distance).Nonempty ∧ allValid design targets effects outcome then
    some (average (binMembers targets distance) (fun deme ↦
      (report (targetDesign design targets deme) effects outcome).getD 0))
    else none

theorem clippedBinReport_defined (distance : ℕ) (cap : ℝ)
    (effects : K → ℝ) (outcome : I → Bool) :
    (clippedBinReport design targets distance cap effects outcome).isSome =
      (binReport design targets distance effects outcome).isSome := by
  classical
  unfold clippedBinReport binReport
  split_ifs <;> rfl

private theorem accepted_measurable (distance : ℕ) (outcome : I → Bool) :
    MeasurableSet {effects | (binMembers targets distance).Nonempty ∧
      allValid design targets effects outcome} := by
  rw [Set.setOf_and]
  exact MeasurableSet.inter (by simp) (allValid_measurable design targets outcome)

theorem clippedBinReport_bounds (distance : ℕ) (cap : ℝ) (hc : 0 ≤ cap)
    (effects : K → ℝ) (outcome : I → Bool) :
    0 ≤ (clippedBinReport design targets distance cap effects outcome).getD 0 ∧
      (clippedBinReport design targets distance cap effects outcome).getD 0 ≤ cap := by
  classical
  unfold clippedBinReport
  split_ifs with h
  · exact average_bounds _ h.1 _ cap (fun deme _ ↦
      ⟨le_min (reportValue_nonneg (targetDesign design targets deme) effects outcome) hc,
        min_le_right _ _⟩)
  · exact ⟨le_rfl, hc⟩

theorem clippedBinReport_measurable (distance : ℕ) (cap : ℝ) (outcome : I → Bool) :
    Measurable (fun effects ↦
      (clippedBinReport design targets distance cap effects outcome).getD 0) := by
  classical
  have havg : Measurable (fun effects ↦ average (binMembers targets distance) (fun deme ↦
      min ((report (targetDesign design targets deme) effects outcome).getD 0) cap)) := by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro deme _
    exact (reportValue_measurable (targetDesign design targets deme) outcome).min measurable_const
  have h : Measurable (fun effects ↦
      if (binMembers targets distance).Nonempty ∧ allValid design targets effects outcome
      then average (binMembers targets distance) (fun deme ↦
        min ((report (targetDesign design targets deme) effects outcome).getD 0) cap)
      else (0 : ℝ)) :=
    Measurable.ite (accepted_measurable design targets distance outcome) havg measurable_const
  convert h using 1
  funext effects
  unfold clippedBinReport
  split_ifs <;> rfl

theorem binReport_defined_measurable (distance : ℕ) (outcome : I → Bool) :
    Measurable (fun effects ↦ if (binReport design targets distance effects outcome).isSome
      then (1 : ℝ) else 0) := by
  classical
  simpa [binReport] using Measurable.ite
    (accepted_measurable design targets distance outcome)
    (measurable_const : Measurable (fun _ : K → ℝ ↦ (1 : ℝ)))
    (measurable_const : Measurable (fun _ : K → ℝ ↦ (0 : ℝ)))

private theorem weighted_integrable (outcome : I → Bool) (value : (K → ℝ) → ℝ)
    (hmeas : Measurable value) (bound : ℝ)
    (hb : ∀ effects, 0 ≤ value effects ∧ value effects ≤ bound) :
    Integrable (fun effects ↦ (labelKernel design).weight effects outcome * value effects)
      (effectLaw K) := by
  apply (integrable_const bound).mono'
    (((labelKernel design).weight_measurable outcome).mul hmeas).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro effects
  have hn := mul_nonneg ((labelKernel design).weight_nonneg effects outcome) (hb effects).1
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact (mul_le_of_le_one_left (hb effects).1
    (labelWeight_le_one design effects outcome)).trans (hb effects).2

noncomputable def binSuccessProbability (distance : ℕ) : ℝ :=
  ∫ effects, ∑ outcome, (labelKernel design).weight effects outcome *
    (if (binReport design targets distance effects outcome).isSome then (1 : ℝ) else 0) ∂effectLaw K

noncomputable def binClippedNumerator (distance : ℕ) (cap : ℝ) : ℝ :=
  ∫ effects, ∑ outcome, (labelKernel design).weight effects outcome *
    (clippedBinReport design targets distance cap effects outcome).getD 0 ∂effectLaw K

/-- Exact Gaussian-effect/label expectation of the plotted per-run bin endpoint.
Deme ratios share all training randomness, and acceptance is applied to the
whole run before the equal-deme average is integrated. -/
theorem clipped_bin_expectation (distance : ℕ) (cap : ℝ) (hc : 0 ≤ cap) :
    PartialMetricMixture.conditionalMetric (jointLaw design)
      (fun pair ↦ clippedBinReport design targets distance cap pair.1 pair.2) =
      if binSuccessProbability design targets distance = 0 then none else
        some (binClippedNumerator design targets distance cap /
          binSuccessProbability design targets distance) := by
  have hd (outcome : I → Bool) : Integrable (fun effects ↦
      (labelKernel design).weight effects outcome *
        (if (clippedBinReport design targets distance cap effects outcome).isSome
          then (1 : ℝ) else 0)) (effectLaw K) := by
    simp only [clippedBinReport_defined]
    apply weighted_integrable design outcome _
      (binReport_defined_measurable design targets distance outcome) 1
    intro effects
    split_ifs <;> norm_num
  have hv (outcome : I → Bool) : Integrable (fun effects ↦
      (labelKernel design).weight effects outcome *
        (clippedBinReport design targets distance cap effects outcome).getD 0) (effectLaw K) :=
    weighted_integrable design outcome _
      (clippedBinReport_measurable design targets distance cap outcome) cap
      (fun effects ↦ clippedBinReport_bounds design targets distance cap hc effects outcome)
  simpa only [jointLaw, binSuccessProbability, binClippedNumerator,
    FiniteReportLaw.definedMass, FiniteReportLaw.weightedDefinedMetric,
    FiniteOutcomeKernel.lawAt, clippedBinReport_defined] using
    PartialMetricMixture.conditionalMetric_jointMeasure (labelKernel design) (effectLaw K)
      (fun pair ↦ clippedBinReport design targets distance cap pair.1 pair.2) hd hv


/-- The untruncated bin value remains nonnegative on every accepted run. -/
theorem binReport_nonneg (distance : ℕ) (effects : K → ℝ) (outcome : I → Bool) :
    0 ≤ (binReport design targets distance effects outcome).getD 0 := by
  classical
  unfold binReport
  split_ifs
  · exact div_nonneg (Finset.sum_nonneg (fun deme _ ↦
      reportValue_nonneg (targetDesign design targets deme) effects outcome)) (Nat.cast_nonneg _)
  · exact le_rfl

theorem binReport_measurable (distance : ℕ) (outcome : I → Bool) :
    Measurable (fun effects ↦ (binReport design targets distance effects outcome).getD 0) := by
  classical
  have havg : Measurable (fun effects ↦ average (binMembers targets distance) (fun deme ↦
      (report (targetDesign design targets deme) effects outcome).getD 0)) := by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro deme _
    exact reportValue_measurable (targetDesign design targets deme) outcome
  have h : Measurable (fun effects ↦
      if (binMembers targets distance).Nonempty ∧ allValid design targets effects outcome
      then average (binMembers targets distance) (fun deme ↦
        (report (targetDesign design targets deme) effects outcome).getD 0)
      else (0 : ℝ)) :=
    Measurable.ite (accepted_measurable design targets distance outcome) havg measurable_const
  convert h using 1
  funext effects
  unfold binReport
  split_ifs <;> rfl

noncomputable def binInner (distance : ℕ) (effects : K → ℝ) : ℝ :=
  ∑ outcome, (labelKernel design).weight effects outcome *
    (binReport design targets distance effects outcome).getD 0

noncomputable def binClippedInner (distance : ℕ) (cap : ℝ) (effects : K → ℝ) : ℝ :=
  ∑ outcome, (labelKernel design).weight effects outcome *
    (clippedBinReport design targets distance cap effects outcome).getD 0

theorem binInner_nonneg (distance : ℕ) (effects : K → ℝ) :
    0 ≤ binInner design targets distance effects :=
  Finset.sum_nonneg (fun outcome _ ↦ mul_nonneg
    ((labelKernel design).weight_nonneg effects outcome)
    (binReport_nonneg design targets distance effects outcome))

theorem binInner_measurable (distance : ℕ) : Measurable (binInner design targets distance) := by
  apply Finset.measurable_sum
  intro outcome _
  exact ((labelKernel design).weight_measurable outcome).mul
    (binReport_measurable design targets distance outcome)

theorem binClippedInner_measurable (distance : ℕ) (cap : ℝ) :
    Measurable (binClippedInner design targets distance cap) := by
  apply Finset.measurable_sum
  intro outcome _
  exact ((labelKernel design).weight_measurable outcome).mul
    (clippedBinReport_measurable design targets distance cap outcome)

theorem binClippedInner_nonneg (distance : ℕ) (cap : ℝ) (hc : 0 ≤ cap)
    (effects : K → ℝ) : 0 ≤ binClippedInner design targets distance cap effects :=
  Finset.sum_nonneg (fun outcome _ ↦ mul_nonneg
    ((labelKernel design).weight_nonneg effects outcome)
    (clippedBinReport_bounds design targets distance cap hc effects outcome).1)

theorem binClippedInner_integrable (distance : ℕ) (cap : ℝ) (hc : 0 ≤ cap) :
    Integrable (binClippedInner design targets distance cap) (effectLaw K) := by
  apply integrable_finset_sum
  intro outcome _
  exact weighted_integrable design outcome _
    (clippedBinReport_measurable design targets distance cap outcome) cap
    (fun effects ↦ clippedBinReport_bounds design targets distance cap hc effects outcome)

theorem binClippedInner_mono (distance : ℕ) {a b : ℝ} (hab : a ≤ b) :
    binClippedInner design targets distance a ≤ binClippedInner design targets distance b := by
  classical
  intro effects
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ ((labelKernel design).weight_nonneg effects outcome)
  unfold clippedBinReport
  split_ifs
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun deme _ ↦ min_le_min_left _ hab)
  · exact le_rfl

theorem binClippedInner_le (distance : ℕ) (cap : ℝ) :
    binClippedInner design targets distance cap ≤ binInner design targets distance := by
  classical
  intro effects
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ ((labelKernel design).weight_nonneg effects outcome)
  unfold clippedBinReport binReport
  split_ifs
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun deme _ ↦ min_le_left _ _)
  · exact le_rfl

/-- There are finitely many labels and demes for each fixed effect vector, so
some finite clipping level preserves every realized ratio simultaneously. -/
theorem binInner_eq_iSup_clipped (distance : ℕ) (effects : K → ℝ) :
    ENNReal.ofReal (binInner design targets distance effects) =
      ⨆ n : ℕ, ENNReal.ofReal (binClippedInner design targets distance n effects) := by
  classical
  apply le_antisymm
  · obtain ⟨n, hn⟩ := exists_nat_gt (∑ outcome : I → Bool, ∑ deme : D,
      (report (targetDesign design targets deme) effects outcome).getD 0)
    have hcap (outcome : I → Bool) (deme : D) :
        (report (targetDesign design targets deme) effects outcome).getD 0 ≤ (n : ℝ) := by
      apply le_trans _ hn.le
      exact (Finset.single_le_sum (fun other _ ↦
        reportValue_nonneg (targetDesign design targets other) effects outcome)
        (Finset.mem_univ deme)).trans (Finset.single_le_sum
          (fun other _ ↦ Finset.sum_nonneg (fun d _ ↦
            reportValue_nonneg (targetDesign design targets d) effects other))
          (Finset.mem_univ outcome))
    have heq : binClippedInner design targets distance n effects =
        binInner design targets distance effects := by
      unfold binClippedInner binInner
      apply Finset.sum_congr rfl
      intro outcome _
      simp only [clippedBinReport, binReport, min_eq_left (hcap outcome _)]
    exact le_iSup_of_le n (le_of_eq (congrArg ENNReal.ofReal heq.symm))
  · exact iSup_le (fun n ↦ ENNReal.ofReal_le_ofReal
      (binClippedInner_le design targets distance n effects))

noncomputable def binExtendedNumerator (distance : ℕ) : ENNReal :=
  ∫⁻ effects, ENNReal.ofReal (binInner design targets distance effects) ∂effectLaw K

/-- The exact untruncated numerator is the monotone limit of proved integrable
approximations. This statement does not assume that the limit is finite. -/
theorem binExtendedNumerator_eq_iSup (distance : ℕ) :
    binExtendedNumerator design targets distance =
      ⨆ n : ℕ, ENNReal.ofReal (binClippedNumerator design targets distance n) := by
  unfold binExtendedNumerator
  simp_rw [binInner_eq_iSup_clipped]
  rw [lintegral_iSup]
  · congr 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal
      (binClippedInner_integrable design targets distance n (Nat.cast_nonneg _))
      (Filter.Eventually.of_forall
        (binClippedInner_nonneg design targets distance n (Nat.cast_nonneg _)))).symm
  · intro n
    exact (binClippedInner_measurable design targets distance n).ennreal_ofReal
  · intro m n hmn effects
    exact ENNReal.ofReal_le_ofReal
      (binClippedInner_mono design targets distance (Nat.cast_le.mpr hmn) effects)

theorem binInner_integrable_iff (distance : ℕ) :
    Integrable (binInner design targets distance) (effectLaw K) ↔
      binExtendedNumerator design targets distance < ∞ := by
  rw [Integrable, hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (binInner_nonneg design targets distance))]
  exact and_iff_right (binInner_measurable design targets distance).aestronglyMeasurable

noncomputable def binExtendedExpectation (distance : ℕ) : Option ENNReal :=
  if binSuccessProbability design targets distance = 0 then none else
    some (binExtendedNumerator design targets distance /
      ENNReal.ofReal (binSuccessProbability design targets distance))


/-- A finite nonnegative numerator dominates each label contribution, so the
conditional expectation formula is justified rather than totalized at infinity. -/
theorem finite_bin_expectation (distance : ℕ)
    (hfinite : binExtendedNumerator design targets distance < ∞) :
    PartialMetricMixture.conditionalMetric (jointLaw design)
      (fun pair ↦ binReport design targets distance pair.1 pair.2) =
      if binSuccessProbability design targets distance = 0 then none else
        some ((binExtendedNumerator design targets distance).toReal /
          binSuccessProbability design targets distance) := by
  have hi := (binInner_integrable_iff design targets distance).mpr hfinite
  have hd (outcome : I → Bool) : Integrable (fun effects ↦
      (labelKernel design).weight effects outcome *
        (if (binReport design targets distance effects outcome).isSome
          then (1 : ℝ) else 0)) (effectLaw K) := by
    apply weighted_integrable design outcome _
      (binReport_defined_measurable design targets distance outcome) 1
    intro effects
    split_ifs <;> norm_num
  have hv (outcome : I → Bool) : Integrable (fun effects ↦
      (labelKernel design).weight effects outcome *
        (binReport design targets distance effects outcome).getD 0) (effectLaw K) := by
    apply hi.mono'
      (((labelKernel design).weight_measurable outcome).mul
        (binReport_measurable design targets distance outcome)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro effects
    have hn := mul_nonneg ((labelKernel design).weight_nonneg effects outcome)
      (binReport_nonneg design targets distance effects outcome)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact Finset.single_le_sum (fun other _ ↦ mul_nonneg
      ((labelKernel design).weight_nonneg effects other)
      (binReport_nonneg design targets distance effects other)) (Finset.mem_univ outcome)
  have hreal : (binExtendedNumerator design targets distance).toReal =
      ∫ effects, binInner design targets distance effects ∂effectLaw K := by
    have h := congrArg ENNReal.toReal (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (binInner_nonneg design targets distance)))
    rw [ENNReal.toReal_ofReal (integral_nonneg (binInner_nonneg design targets distance))] at h
    exact h.symm
  rw [hreal]
  simpa only [jointLaw, binSuccessProbability, binInner,
    FiniteReportLaw.definedMass, FiniteReportLaw.weightedDefinedMetric,
    FiniteOutcomeKernel.lawAt] using
    PartialMetricMixture.conditionalMetric_jointMeasure (labelKernel design) (effectLaw K)
      (fun pair ↦ binReport design targets distance pair.1 pair.2) hd hv

end Descent.Portability.DistanceBinnedPortabilityLaw
