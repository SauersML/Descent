/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

/-!
Finite training-label probabilities, label-dependent linear scores, and conditional
accuracy and portability bounds with explicit reporting domains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TrainingNoiseAccuracy

open FiniteReportLaw

variable {I S T J : Type*} [Fintype I] [DecidableEq I] [Fintype S] [Fintype T] [Fintype J]

noncomputable def labelMass (probability : I → ℝ) (labels : I → Bool) : ℝ :=
  ∏ i, if labels i then probability i else 1 - probability i

omit [DecidableEq I] in
theorem labelMass_nonneg (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1) (labels : I → Bool) :
    0 ≤ labelMass probability labels := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

theorem labelMass_sum (probability : I → ℝ) :
    ∑ labels : I → Bool, labelMass probability labels = 1 := by
  classical
  unfold labelMass
  have h := Fintype.prod_sum (fun (i : I) (b : Bool) ↦
    if b then probability i else 1 - probability i)
  simpa [Fintype.sum_bool] using h.symm

noncomputable def labelLaw (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1) : FiniteReportLaw (I → Bool) where
  mass := labelMass probability
  mass_nonneg := labelMass_nonneg probability hp
  mass_sum := labelMass_sum probability

noncomputable def linearScore (genotype : S → J → ℝ) (weights : J → ℝ) : S → ℝ :=
  fun individual ↦ ∑ marker, weights marker * genotype individual marker

/-- Evaluation data and trait values are fixed in this conditional experiment.
`learn` is the label-dependent learner, including failure. No independence between
the learned weights and their training labels is assumed. -/
noncomputable def accuracy (evaluation : FiniteReportLaw S)
    (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (labels : I → Bool) : Option ℝ :=
  (learn labels).bind fun weights ↦
    evaluation.squaredCorrelation (linearScore genotype weights) liability

omit [Fintype I] [DecidableEq I] in
theorem accuracy_mem_unitInterval (evaluation : FiniteReportLaw S)
    (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (labels : I → Bool) {r : ℝ}
    (hr : accuracy evaluation genotype liability learn labels = some r) :
    0 ≤ r ∧ r ≤ 1 := by
  unfold accuracy at hr
  cases hw : learn labels with
  | none => simp [hw] at hr
  | some weights =>
    simp only [hw, Option.bind_some] at hr
    exact evaluation.squaredCorrelation_mem_unitInterval _ _ hr

noncomputable def ratio (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceGenotype : S → J → ℝ) (targetGenotype : T → J → ℝ)
    (sourceLiability : S → ℝ) (targetLiability : T → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (labels : I → Bool) : Option ℝ :=
  (accuracy source sourceGenotype sourceLiability learn labels).bind fun sourceR2 ↦
    (accuracy target targetGenotype targetLiability learn labels).bind fun targetR2 ↦
      if 0 < sourceR2 then some (targetR2 / sourceR2) else none

omit [Fintype I] [DecidableEq I] in
theorem ratio_nonneg (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceGenotype : S → J → ℝ) (targetGenotype : T → J → ℝ)
    (sourceLiability : S → ℝ) (targetLiability : T → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (labels : I → Bool) {r : ℝ}
    (hr : ratio source target sourceGenotype targetGenotype
      sourceLiability targetLiability learn labels = some r) : 0 ≤ r := by
  unfold ratio at hr
  cases hs : accuracy source sourceGenotype sourceLiability learn labels with
  | none => simp [hs] at hr
  | some sourceR2 =>
    cases ht : accuracy target targetGenotype targetLiability learn labels with
    | none => simp [hs, ht] at hr
    | some targetR2 =>
      simp only [hs, ht, Option.bind_some] at hr
      split_ifs at hr with hpos
      · have heq := Option.some.inj hr
        rw [← heq]
        exact div_nonneg
          (accuracy_mem_unitInterval target targetGenotype targetLiability learn labels ht).1
          hpos.le

omit [Fintype I] [DecidableEq I] in
theorem ratio_self_value (source : FiniteReportLaw S)
    (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (labels : I → Bool) {r : ℝ}
    (hr : ratio source source genotype genotype liability liability learn labels = some r) :
    r = 1 := by
  unfold ratio at hr
  cases hs : accuracy source genotype liability learn labels with
  | none => simp [hs] at hr
  | some sourceR2 =>
    simp only [hs, Option.bind_some] at hr
    split_ifs at hr with hpos
    · simpa [div_self (ne_of_gt hpos)] using hr.symm

noncomputable def numerator (probability : I → ℝ) (readout : (I → Bool) → Option ℝ) : ℝ :=
  ∑ labels, labelMass probability labels * (readout labels).getD 0

noncomputable def definedProbability
    (probability : I → ℝ) (readout : (I → Bool) → Option ℝ) : ℝ :=
  ∑ labels, labelMass probability labels * (if (readout labels).isSome then 1 else 0)

noncomputable def conditionalExpectation (probability : I → ℝ)
    (readout : (I → Bool) → Option ℝ) : Option ℝ :=
  if definedProbability probability readout = 0 then none
  else some (numerator probability readout / definedProbability probability readout)

theorem conditionalExpectation_eq_labelLaw (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (readout : (I → Bool) → Option ℝ) :
    conditionalExpectation probability readout =
      (labelLaw probability hp).conditionalMetric readout := rfl

theorem numerator_nonneg (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (readout : (I → Bool) → Option ℝ)
    (hr : ∀ labels r, readout labels = some r → 0 ≤ r) :
    0 ≤ numerator probability readout := by
  apply Finset.sum_nonneg
  intro labels _
  apply mul_nonneg (labelMass_nonneg probability hp labels)
  cases h : readout labels with
  | none => simp
  | some r => exact hr labels r h

theorem definedProbability_nonneg (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (readout : (I → Bool) → Option ℝ) :
    0 ≤ definedProbability probability readout := by
  apply Finset.sum_nonneg
  intro labels _
  exact mul_nonneg (labelMass_nonneg probability hp labels) (by split_ifs <;> norm_num)

theorem definedProbability_le_one (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (readout : (I → Bool) → Option ℝ) :
    definedProbability probability readout ≤ 1 := by
  rw [← labelMass_sum probability]
  apply Finset.sum_le_sum
  intro labels _
  split_ifs
  · simp
  · simpa using labelMass_nonneg probability hp labels

theorem numerator_le_definedProbability (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (readout : (I → Bool) → Option ℝ)
    (hr : ∀ labels r, readout labels = some r → r ≤ 1) :
    numerator probability readout ≤ definedProbability probability readout := by
  apply Finset.sum_le_sum
  intro labels _
  cases h : readout labels with
  | none => simp
  | some r =>
    simp only [Option.getD_some, Option.isSome_some, ite_true, mul_one]
    exact mul_le_of_le_one_right (labelMass_nonneg probability hp labels) (hr labels r h)

theorem conditionalExpectation_bounds (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (readout : (I → Bool) → Option ℝ) (upper : ℝ)
    (hb : ∀ labels r, readout labels = some r → 0 ≤ r ∧ r ≤ upper) {r : ℝ}
    (hr : conditionalExpectation probability readout = some r) :
    0 ≤ r ∧ r ≤ upper := by
  have hlo := numerator_nonneg probability hp readout (fun labels r h ↦ (hb labels r h).1)
  have hhi : numerator probability readout ≤ upper * definedProbability probability readout := by
    unfold numerator definedProbability
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro labels _
    cases h : readout labels with
    | none => simp
    | some value =>
      simp only [Option.getD_some, Option.isSome_some, ite_true, mul_one]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hb labels value h).2 (labelMass_nonneg probability hp labels)
  unfold conditionalExpectation at hr
  split_ifs at hr with hz
  · have hpos : 0 < definedProbability probability readout :=
      lt_of_le_of_ne (definedProbability_nonneg probability hp readout) (Ne.symm hz)
    have heq := Option.some.inj hr
    rw [← heq]
    exact ⟨div_nonneg hlo hpos.le, (div_le_iff₀ hpos).mpr hhi⟩

theorem conditionalAccuracy_mem_unitInterval (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (evaluation : FiniteReportLaw S) (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) {r : ℝ}
    (hr : conditionalExpectation probability
      (accuracy evaluation genotype liability learn) = some r) :
    0 ≤ r ∧ r ≤ 1 := by
  exact conditionalExpectation_bounds probability hp _ 1
    (fun labels r h ↦ accuracy_mem_unitInterval evaluation genotype liability learn labels h) hr

omit [Fintype I] [DecidableEq I] in
/-- A quantitative ratio bound needs a source accuracy floor on the configurations
that can be reported. An accuracy upper bound alone does not supply this floor. -/
theorem ratio_le_inverse_floor (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceGenotype : S → J → ℝ) (targetGenotype : T → J → ℝ)
    (sourceLiability : S → ℝ) (targetLiability : T → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (labels : I → Bool)
    (floor : ℝ) (hf : 0 < floor)
    (hfloor : ∀ value, accuracy source sourceGenotype sourceLiability learn labels = some value →
      0 < value → floor ≤ value) {r : ℝ}
    (hr : ratio source target sourceGenotype targetGenotype
      sourceLiability targetLiability learn labels = some r) : r ≤ 1 / floor := by
  unfold ratio at hr
  cases hs : accuracy source sourceGenotype sourceLiability learn labels with
  | none => simp [hs] at hr
  | some sourceR2 =>
    cases ht : accuracy target targetGenotype targetLiability learn labels with
    | none => simp [hs, ht] at hr
    | some targetR2 =>
      simp only [hs, ht, Option.bind_some] at hr
      split_ifs at hr with hpos
      · have heq := Option.some.inj hr
        rw [← heq]
        exact le_trans
          (div_le_div_of_nonneg_right
            (accuracy_mem_unitInterval target targetGenotype targetLiability learn labels ht).2
            hpos.le)
          (one_div_le_one_div_of_le hf (hfloor sourceR2 hs hpos))

theorem conditionalRatio_bounds (probability : I → ℝ)
    (hp : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1)
    (source : FiniteReportLaw S) (target : FiniteReportLaw T)
    (sourceGenotype : S → J → ℝ) (targetGenotype : T → J → ℝ)
    (sourceLiability : S → ℝ) (targetLiability : T → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) (floor : ℝ) (hf : 0 < floor)
    (hfloor : ∀ labels value,
      accuracy source sourceGenotype sourceLiability learn labels = some value →
      0 < value → floor ≤ value)
    {r : ℝ} (hr : conditionalExpectation probability
      (ratio source target sourceGenotype targetGenotype sourceLiability targetLiability learn) =
      some r) : 0 ≤ r ∧ r ≤ 1 / floor := by
  apply conditionalExpectation_bounds probability hp _ (1 / floor) _ hr
  intro labels value h
  exact ⟨ratio_nonneg source target sourceGenotype targetGenotype
      sourceLiability targetLiability learn labels h,
    ratio_le_inverse_floor source target sourceGenotype targetGenotype
      sourceLiability targetLiability learn labels floor hf (hfloor labels) h⟩

theorem conditionalExpectation_eq_one (probability : I → ℝ)
    (readout : (I → Bool) → Option ℝ)
    (hr : ∀ labels r, readout labels = some r → r = 1)
    (hd : definedProbability probability readout ≠ 0) :
    conditionalExpectation probability readout = some 1 := by
  have heq : numerator probability readout = definedProbability probability readout := by
    apply Finset.sum_congr rfl
    intro labels _
    cases h : readout labels with
    | none => simp
    | some r => simp [hr labels r h]
  simp [conditionalExpectation, hd, heq]

theorem conditionalSourceRatio_eq_one (probability : I → ℝ)
    (source : FiniteReportLaw S) (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ))
    (hd : definedProbability probability
      (ratio source source genotype genotype liability liability learn) ≠ 0) :
    conditionalExpectation probability
      (ratio source source genotype genotype liability liability learn) = some 1 := by
  exact conditionalExpectation_eq_one probability _
    (fun labels r h ↦ ratio_self_value source genotype liability learn labels h) hd

private theorem finite_positive_floor {A : Type*} [Fintype A] (f : A → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, 0 < f a → δ ≤ f a := by
  classical
  have hfinite (s : Finset A) : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, 0 < f a → δ ≤ f a := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, hs⟩ := ih
      by_cases hfa : 0 < f a
      · refine ⟨min δ (f a), lt_min hδ hfa, ?_⟩
        intro b hb hfb
        rcases Finset.mem_insert.mp hb with hab | hbs
        · subst b
          exact min_le_right _ _
        · exact le_trans (min_le_left _ _) (hs b hbs hfb)
      · refine ⟨δ, hδ, ?_⟩
        intro b hb hfb
        rcases Finset.mem_insert.mp hb with hab | hbs
        · subst b
          exact (hfa hfb).elim
        · exact hs b hbs hfb
  obtain ⟨δ, hδ, hs⟩ := hfinite Finset.univ
  exact ⟨δ, hδ, fun a ↦ hs a (Finset.mem_univ a)⟩

/-- For fixed genetic data, a deterministic learner has finitely many binary-label
inputs. Its positive source accuracies therefore have a strictly positive floor.
The floor is allowed to depend on the fixed data and learner. -/
theorem positive_source_floor (source : FiniteReportLaw S)
    (genotype : S → J → ℝ) (liability : S → ℝ)
    (learn : (I → Bool) → Option (J → ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ outcome value,
      accuracy source genotype liability learn outcome = some value →
      0 < value → δ ≤ value := by
  obtain ⟨δ, hδ, hfloor⟩ := finite_positive_floor
    (fun outcome ↦ (accuracy source genotype liability learn outcome).getD 0)
  refine ⟨δ, hδ, ?_⟩
  intro outcome value hvalue hpos
  have h := hfloor outcome
  simp only [hvalue, Option.getD_some] at h
  exact h hpos

end Descent.Portability.TrainingNoiseAccuracy
