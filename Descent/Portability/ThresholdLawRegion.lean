/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricOrderingClassification

assert_below Descent.Decision Descent.Program

/-!
# The complete threshold-law region and the sharp fixed-score confusion fiber

At a fixed finite score law `mu` and prevalence `pi`, the joint laws of score and
binary outcome are exactly the submeasures `nu` of `mu` with total mass `pi`
(`threshold_law_region`, UPT Theorem 6.2 and PL Theorem 4.2), and every
threshold event's four confusion cells are then determined by that one submeasure
(`submeasure_threshold_cells`, UPT equation (6.5)). At one fixed threshold the
attainable true-positive mass is exactly the interval of UPT (6.8) and TQ (4.9)
(`fixed_score_confusion_fiber`), with every value realised by `fiberLaw` and, via
`MetricOrderingClassification.common_threshold_realizes`, by an actual
thresholded score. `finite_threshold_curve_iff` is the exact finite-grid form of
UPT Corollary 6.3: the possible top-`s` true-positive curves are exactly the
functions starting at `0`, ending at `pi`, with increments in `[0, 1/n]`. The
measure-theoretic absolutely-continuous form of that corollary is not proved
here. Constant-precision feasibility, UPT (6.10) and TQ (4.13), is already
`MetricOrderingClassification.constant_precision_feasible_iff` and is not
restated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ThresholdLawRegion

open Foundations

noncomputable section

variable {S : Type*} [Fintype S]

/-- The joint law of score and outcome built from a submeasure `nu` of the score
law `mu`: the case mass on a score value is `nu`, the control mass the rest. -/
def submeasureJoint (mu nu : S → ℝ) : S × Bool → ℝ :=
  fun z ↦ if z.2 then nu z.1 else mu z.1 - nu z.1

/-- The expectation functional of the joint law of a submeasure. -/
def submeasureLaw (mu nu : S → ℝ) (h0 : ∀ s, 0 ≤ nu s) (h1 : ∀ s, nu s ≤ mu s)
    (hsum : ∑ s, mu s = 1) : ExpFunctional (S × Bool) :=
  weightedExp (submeasureJoint mu nu)
    (by
      rintro ⟨s, b⟩
      simp only [submeasureJoint]
      cases b
      · simpa using sub_nonneg.mpr (h1 s)
      · simpa using h0 s)
    (by
      simp only [submeasureJoint, Fintype.sum_prod_type, Fintype.sum_bool,
        Bool.false_eq_true, if_false, if_true]
      have hpt : ∀ s : S, nu s + (mu s - nu s) = mu s := fun s ↦ by ring
      rw [Finset.sum_congr rfl fun s _ ↦ hpt s, hsum])

/-- **UPT Theorem 6.2 / PL Theorem 4.2 (complete threshold-law region).** At a
fixed finite score law and prevalence, the joint laws of score and binary outcome
are exactly the submeasures of the score law with total mass the prevalence.
There is no further freedom: one submeasure generates every threshold at once. -/
theorem threshold_law_region (mu : S → ℝ) (hmus : ∑ s, mu s = 1) (pi : ℝ)
    (nu : S → ℝ) :
    (∃ p : S × Bool → ℝ, (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧
        (∀ s, p (s, true) + p (s, false) = mu s) ∧ (∀ s, p (s, true) = nu s) ∧
        ∑ s, p (s, true) = pi) ↔
      ((∀ s, 0 ≤ nu s) ∧ (∀ s, nu s ≤ mu s) ∧ ∑ s, nu s = pi) := by
  constructor
  · rintro ⟨p, hp0, _, hmarg, hnu, hpre⟩
    refine ⟨fun s ↦ (hnu s) ▸ hp0 (s, true), fun s ↦ ?_, ?_⟩
    · have := hp0 (s, false)
      have hm := hmarg s
      rw [hnu s] at hm
      linarith
    · rw [← hpre]
      exact (Finset.sum_congr rfl fun s _ ↦ hnu s).symm
  · rintro ⟨h0, h1, hsum⟩
    refine ⟨submeasureJoint mu nu, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨s, b⟩
      simp only [submeasureJoint]
      cases b
      · simpa using sub_nonneg.mpr (h1 s)
      · simpa using h0 s
    · simp only [submeasureJoint, Fintype.sum_prod_type, Fintype.sum_bool,
        Bool.false_eq_true, if_false, if_true]
      have hpt : ∀ s : S, nu s + (mu s - nu s) = mu s := fun s ↦ by ring
      rw [Finset.sum_congr rfl fun s _ ↦ hpt s, hmus]
    · intro s
      simp only [submeasureJoint, Bool.false_eq_true, if_false, if_true]
      ring
    · intro s
      simp only [submeasureJoint, if_true]
    · rw [← hsum]
      exact Finset.sum_congr rfl fun s _ ↦ by simp only [submeasureJoint, if_true]

/-- **UPT equation (6.5).** Every threshold event's four confusion cells are the
submeasure and score masses inside and outside the event. One submeasure
determines all of them simultaneously; the threshold metrics are not free. -/
theorem submeasure_threshold_cells (mu nu : S → ℝ) (h0 : ∀ s, 0 ≤ nu s)
    (h1 : ∀ s, nu s ≤ mu s) (hsum : ∑ s, mu s = 1) (pred : S → Bool) :
    (ThresholdPolicyTransport.decisionCells (submeasureLaw mu nu h0 h1 hsum)
        (fun z ↦ pred z.1) (fun z ↦ z.2)).tp = ∑ s, (if pred s then nu s else 0) ∧
      (ThresholdPolicyTransport.decisionCells (submeasureLaw mu nu h0 h1 hsum)
        (fun z ↦ pred z.1) (fun z ↦ z.2)).fp =
        ∑ s, (if pred s then mu s - nu s else 0) ∧
      (ThresholdPolicyTransport.decisionCells (submeasureLaw mu nu h0 h1 hsum)
        (fun z ↦ pred z.1) (fun z ↦ z.2)).fn = ∑ s, (if pred s then 0 else nu s) ∧
      (ThresholdPolicyTransport.decisionCells (submeasureLaw mu nu h0 h1 hsum)
        (fun z ↦ pred z.1) (fun z ↦ z.2)).tn =
        ∑ s, (if pred s then 0 else mu s - nu s) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [ThresholdPolicyTransport.decisionCells, submeasureLaw, weightedExp_apply,
        submeasureJoint, Fintype.sum_prod_type, Fintype.sum_bool]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      by_cases h : pred s = true <;> simp [h]

/-- Every feasible true-positive mass at a fixed prevalence and predicted-positive
mass is realised by this confusion table. -/
def fiberLaw (pi s x : ℝ) (hx0 : 0 ≤ x) (hxs : x ≤ s) (hxpi : x ≤ pi)
    (hlow : pi + s - 1 ≤ x) : ConfusionMatrix where
  tp := x
  fp := s - x
  tn := 1 - pi - s + x
  fn := pi - x
  tp_nonneg := hx0
  fp_nonneg := by linarith
  tn_nonneg := by linarith
  fn_nonneg := by linarith
  mass_one := by ring

/-- **TQ Theorem 4.5 / UPT (6.8) / PL (4.4) (sharp fixed-score confusion fiber).**
Holding the prevalence and the predicted-positive mass fixed, the attainable
true-positive mass is exactly the stated interval, and every value in it is
attained by an actual confusion table. -/
theorem fixed_score_confusion_fiber (pi s x : ℝ) :
    (∃ c : ConfusionMatrix, c.prevalence = pi ∧ c.tp + c.fp = s ∧ c.tp = x) ↔
      (max 0 (pi + s - 1) ≤ x ∧ x ≤ min pi s) := by
  constructor
  · rintro ⟨c, hpre, hps, hx⟩
    have h1 := c.tp_nonneg
    have h2 := c.fp_nonneg
    have h3 := c.tn_nonneg
    have h4 := c.fn_nonneg
    have h5 := c.mass_one
    have hpre' : c.tp + c.fn = pi := hpre
    constructor
    · exact max_le (by linarith) (by linarith)
    · exact le_min (by linarith) (by linarith)
  · rintro ⟨hlow, hhigh⟩
    have hx0 : 0 ≤ x := le_trans (le_max_left 0 _) hlow
    have hx1 : pi + s - 1 ≤ x := le_trans (le_max_right 0 _) hlow
    have hxpi : x ≤ pi := le_trans hhigh (min_le_left _ _)
    have hxs : x ≤ s := le_trans hhigh (min_le_right _ _)
    refine ⟨fiberLaw pi s x hx0 hxs hxpi hx1, ?_, ?_, rfl⟩
    · show x + (pi - x) = pi
      ring
    · show x + (s - x) = s
      ring

/-- **TQ equation (4.10) / PL (4.3).** Precision and recall of the attaining law
are exactly the true-positive mass over the predicted-positive mass and over the
prevalence. -/
theorem fiber_precision_recall (pi s x : ℝ) (hx0 : 0 ≤ x) (hxs : x ≤ s)
    (hxpi : x ≤ pi) (hlow : pi + s - 1 ≤ x) :
    (fiberLaw pi s x hx0 hxs hxpi hlow).precision = x / s ∧
      (fiberLaw pi s x hx0 hxs hxpi hlow).recallRate = x / pi := by
  have hs : x + (s - x) = s := by ring
  have hp : x + (pi - x) = pi := by ring
  constructor
  · show x / (x + (s - x)) = x / s
    rw [hs]
  · show x / (x + (pi - x)) = x / pi
    rw [hp]

/-- **TQ equation (4.10) / PL (4.5).** At fixed prevalence and predicted-positive
mass, recall is precision times the ratio of the two, so the two metrics cannot
move independently. -/
theorem fiber_recall_eq_precision_scaled (pi s x : ℝ) (hs : 0 < s) (hpi : 0 < pi)
    (hx0 : 0 ≤ x) (hxs : x ≤ s) (hxpi : x ≤ pi) (hlow : pi + s - 1 ≤ x) :
    (fiberLaw pi s x hx0 hxs hxpi hlow).recallRate =
      (fiberLaw pi s x hx0 hxs hxpi hlow).precision * s / pi := by
  obtain ⟨hprec, hrec⟩ := fiber_precision_recall pi s x hx0 hxs hxpi hlow
  rw [hprec, hrec]
  field_simp

/-- Every point of the sharp fiber is realised by a genuine thresholded score:
the attaining table is the confusion table of a binary score at the fixed cutoff
`1 / 2`, via `MetricOrderingClassification.common_threshold_realizes`. -/
theorem fiber_realized_by_threshold (pi s x : ℝ) (hx0 : 0 ≤ x) (hxs : x ≤ s)
    (hxpi : x ≤ pi) (hlow : pi + s - 1 ≤ x) :
    (ThresholdPolicyTransport.thresholdCells
        (MetricOrderingClassification.confusionLaw (fiberLaw pi s x hx0 hxs hxpi hlow))
        (fun z ↦ if z.1 then 1 else 0) (fun z ↦ z.2) (1 / 2)).tp = x := by
  have h := MetricOrderingClassification.common_threshold_realizes
    (fiberLaw pi s x hx0 hxs hxpi hlow)
  exact h.1

/-- **UPT Corollary 6.3, exact finite-grid form.** On a grid of `n` equal score
atoms the possible top-`s` true-positive curves are exactly the functions that
start at zero, end at the prevalence, and have every increment between zero and
one atom of score mass. This is the finite counterpart of the manuscript's
absolutely continuous statement with derivative in `[0, 1]`; the
measure-theoretic form is not proved here. -/
theorem finite_threshold_curve_iff (n : ℕ) (pi : ℝ) (T : ℕ → ℝ) :
    (T 0 = 0 ∧ T n = pi ∧
        ∀ k, k < n → 0 ≤ T (k + 1) - T k ∧ T (k + 1) - T k ≤ (n : ℝ)⁻¹) ↔
      ∃ nu : ℕ → ℝ, (∀ k, k < n → 0 ≤ nu k ∧ nu k ≤ (n : ℝ)⁻¹) ∧
        (∑ k ∈ Finset.range n, nu k = pi) ∧
        ∀ k, k ≤ n → T k = ∑ i ∈ Finset.range k, nu i := by
  constructor
  · rintro ⟨h0, hn, hinc⟩
    refine ⟨fun k ↦ T (k + 1) - T k, hinc, ?_, ?_⟩
    · rw [Finset.sum_range_sub T n, hn, h0, sub_zero]
    · intro k _
      rw [Finset.sum_range_sub T k, h0, sub_zero]
  · rintro ⟨nu, hnu, hsum, hT⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hT 0 (Nat.zero_le n), Finset.range_zero, Finset.sum_empty]
    · rw [hT n le_rfl, hsum]
    · intro k hk
      rw [hT (k + 1) hk, hT k (le_of_lt hk), Finset.sum_range_succ]
      obtain ⟨hl, hu⟩ := hnu k hk
      constructor
      · linarith
      · linarith


end

end Descent.Portability.ThresholdLawRegion
