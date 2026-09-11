/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

assert_below Descent.Decision Descent.Program

/-!
# The exact global summary-invisible diameter

A finite linear summary reports the expectations of a span of feature functions containing
the constant one. The worst disagreement in an expectation metric between two probability
laws that the summary cannot tell apart is exactly twice the uniform distance from the
metric to that feature span, and the worst case is attained by an explicit pair of genuine
probability laws. The same distance is exactly the minimax error of the best summary-only
estimator, even when that estimator is allowed to be an arbitrary nonlinear function of the
summary. Exact identification on all probability laws therefore holds precisely when the
metric already lies in the feature span.

This is UPT Theorem 9.2 (9.2)-(9.4). It is a global replacement for a local response
ellipsoid, so the statements quantify over all probability laws rather than over
perturbations. The attaining pair is produced from an explicit dual direction of total
variation one that annihilates every feature and pairs with the metric exactly at the gap;
that direction is obtained by separating the metric from the open set of functions lying
strictly within the gap of the feature span, so nothing about it is assumed.

The module uses `FiniteReportLaw` and its `expectation` from `UniversalMetricIdentification`,
so the laws exhibited are probability laws by construction. The hypotheses are the
manuscript's domain conditions: a finite state space and a feature span containing the
constant function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SummaryInvisibleDiameter

open scoped Pointwise

noncomputable section

variable {S : Type*} [Fintype S]

/-- The gap Δ(f, 𝓕) of UPT (9.2): the uniform distance from the metric to the feature span. -/
def summaryGap (features : Submodule ℝ (S → ℝ)) (metric : S → ℝ) : ℝ :=
  Metric.infDist metric (features : Set (S → ℝ))

/-- The gap is nonnegative. -/
theorem summaryGap_nonneg (features : Submodule ℝ (S → ℝ)) (metric : S → ℝ) :
    0 ≤ summaryGap features metric :=
  Metric.infDist_nonneg

/-- A finite-dimensional feature span attains its uniform distance, so a best uniform
approximation exists rather than merely being approached. -/
theorem exists_best_approximation (features : Submodule ℝ (S → ℝ)) (metric : S → ℝ) :
    ∃ best ∈ features, ‖metric - best‖ = summaryGap features metric ∧
      ∀ h ∈ features, summaryGap features metric ≤ ‖metric - h‖ := by
  obtain ⟨best, hbest, hdist⟩ :=
    features.closed_of_finiteDimensional.exists_infDist_eq_dist ⟨0, features.zero_mem⟩ metric
  refine ⟨best, hbest, by rw [summaryGap, hdist, dist_eq_norm], fun h hh ↦ ?_⟩
  have hle : Metric.infDist metric (features : Set (S → ℝ)) ≤ dist metric h :=
    Metric.infDist_le_dist_of_mem hh
  rwa [dist_eq_norm] at hle

/-- Every expectation under a probability law is bounded by the uniform norm. -/
theorem abs_expectation_le_norm (p : FiniteReportLaw S) (g : S → ℝ) :
    |p.expectation g| ≤ ‖g‖ := by
  calc |p.expectation g| ≤ ∑ s, |p.mass s * g s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, p.mass s * ‖g‖ := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (p.mass_nonneg s)]
        refine mul_le_mul_of_nonneg_left ?_ (p.mass_nonneg s)
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm g s
    _ = ‖g‖ := by rw [← Finset.sum_mul, p.mass_sum, one_mul]

/-- Expectation is additive in the metric argument, so a feature can be subtracted off. -/
theorem expectation_sub_metric (p : FiniteReportLaw S) (metric best : S → ℝ) :
    p.expectation (metric - best) = p.expectation metric - p.expectation best := by
  simp only [FiniteReportLaw.expectation, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The upper bound in UPT (9.3): laws with the same summary differ in the metric by at most
twice the gap. -/
theorem abs_expectation_sub_le_two_summaryGap (features : Submodule ℝ (S → ℝ))
    (metric : S → ℝ) (p q : FiniteReportLaw S)
    (hsame : ∀ g ∈ features, p.expectation g = q.expectation g) :
    |p.expectation metric - q.expectation metric| ≤ 2 * summaryGap features metric := by
  obtain ⟨best, hbest, hnorm, -⟩ := exists_best_approximation features metric
  have hsplit : p.expectation metric - q.expectation metric =
      p.expectation (metric - best) - q.expectation (metric - best) := by
    rw [expectation_sub_metric, expectation_sub_metric, hsame best hbest]
    ring
  rw [hsplit]
  have hp := abs_expectation_le_norm p (metric - best)
  have hq := abs_expectation_le_norm q (metric - best)
  rw [hnorm] at hp hq
  calc |p.expectation (metric - best) - q.expectation (metric - best)|
      ≤ |p.expectation (metric - best)| + |q.expectation (metric - best)| := abs_sub _ _
    _ ≤ 2 * summaryGap features metric := by linarith

/-- Splitting a real number into its two nonnegative parts recovers the number. -/
theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- Splitting a real number into its two nonnegative parts recovers its absolute value. -/
theorem max_add_max_neg (a : ℝ) : max a 0 + max (-a) 0 = |a| := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
    ring

/-- A zero-mass direction of total variation one splits into two halves of mass one half. -/
theorem sum_max_eq_half (dir : S → ℝ) (hzero : ∑ s, dir s = 0) (hone : ∑ s, |dir s| = 1) :
    ∑ s, max (dir s) 0 = 1 / 2 ∧ ∑ s, max (-dir s) 0 = 1 / 2 := by
  have hsub : ∑ s, max (dir s) 0 - ∑ s, max (-dir s) 0 = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [max_sub_max_neg] using hzero
  have hadd : ∑ s, max (dir s) 0 + ∑ s, max (-dir s) 0 = 1 := by
    rw [← Finset.sum_add_distrib]
    simpa only [max_add_max_neg] using hone
  constructor <;> linarith

/-- The probability law carrying the positive part of a zero-mass unit direction. -/
def positiveHalf (dir : S → ℝ) (hzero : ∑ s, dir s = 0) (hone : ∑ s, |dir s| = 1) :
    FiniteReportLaw S where
  mass := fun s ↦ 2 * max (dir s) 0
  mass_nonneg := fun s ↦ by positivity
  mass_sum := by
    rw [← Finset.mul_sum, (sum_max_eq_half dir hzero hone).1]
    norm_num

/-- The probability law carrying the negative part of a zero-mass unit direction. -/
def negativeHalf (dir : S → ℝ) (hzero : ∑ s, dir s = 0) (hone : ∑ s, |dir s| = 1) :
    FiniteReportLaw S where
  mass := fun s ↦ 2 * max (-dir s) 0
  mass_nonneg := fun s ↦ by positivity
  mass_sum := by
    rw [← Finset.mul_sum, (sum_max_eq_half dir hzero hone).2]
    norm_num

/-- The two halves differ by exactly twice the direction, so they share every summary the
direction annihilates and split its metric pairing. -/
theorem half_expectation_sub (dir : S → ℝ) (hzero : ∑ s, dir s = 0)
    (hone : ∑ s, |dir s| = 1) (g : S → ℝ) :
    (positiveHalf dir hzero hone).expectation g -
        (negativeHalf dir hzero hone).expectation g = 2 * ∑ s, dir s * g s := by
  simp only [FiniteReportLaw.expectation, positiveHalf, negativeHalf, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hs := max_sub_max_neg (dir s)
  linear_combination (2 * g s) * hs

/-- The ℓ¹ dual certificate for the uniform gap: a signed direction of total variation one
that no feature can see and whose metric pairing is the entire gap. It is produced by
separating the metric from the open set of functions lying strictly within the gap of the
feature span, so nothing about it is assumed. -/
theorem exists_dual_direction [DecidableEq S] (features : Submodule ℝ (S → ℝ))
    (metric best : S → ℝ) (gap : ℝ) (hbest : best ∈ features)
    (hattained : ‖metric - best‖ = gap) (hfar : ∀ h ∈ features, gap ≤ ‖metric - h‖)
    (hpos : 0 < gap) :
    ∃ dir : S → ℝ, ∑ s, |dir s| = 1 ∧ (∀ g ∈ features, ∑ s, dir s * g s = 0) ∧
      ∑ s, dir s * metric s = gap := by
  classical
  have hopen : IsOpen ((features : Set (S → ℝ)) + Metric.ball (0 : S → ℝ) gap) :=
    Metric.isOpen_ball.add_left
  have hconv : Convex ℝ ((features : Set (S → ℝ)) + Metric.ball (0 : S → ℝ) gap) :=
    features.convex.add (convex_ball (0 : S → ℝ) gap)
  have hsub : ∀ h ∈ features,
      h ∈ (features : Set (S → ℝ)) + Metric.ball (0 : S → ℝ) gap := by
    intro h hh
    exact ⟨h, hh, 0, by simpa using hpos, by simp⟩
  have hout : metric ∉ (features : Set (S → ℝ)) + Metric.ball (0 : S → ℝ) gap := by
    rintro ⟨h, hh, b, hb, heq⟩
    have hle : gap ≤ ‖metric - h‖ := hfar h hh
    have hb' : ‖b‖ < gap := by simpa using hb
    have hval : metric - h = b := by
      rw [← heq]
      show h + b - h = b
      abel
    rw [hval] at hle
    linarith
  obtain ⟨sep, hsep⟩ := geometric_hahn_banach_open_point hconv hopen hout
  obtain ⟨coeff, hpair⟩ : ∃ c : S → ℝ, ∀ x : S → ℝ, ∑ s, c s * x s = sep x := by
    refine ⟨fun s ↦ sep fun t ↦ if s = t then (1 : ℝ) else 0, fun x ↦ ?_⟩
    have hx := LinearMap.pi_apply_eq_sum_univ (sep : (S → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at hx
    rw [hx]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [smul_eq_mul]; ring
  have hzeroFeature : ∀ h ∈ features, sep h = 0 := by
    intro h hh
    by_contra hne
    have hscaled := hsep (((sep metric + 1) / sep h) • h)
      (hsub _ (features.smul_mem ((sep metric + 1) / sep h) hh))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hscaled
    linarith
  have hmetricpos : 0 < sep metric := by
    have hzero := hsep 0 (hsub 0 features.zero_mem)
    simpa using hzero
  have hballlt : ∀ b : S → ℝ, ‖b‖ < gap → sep b < sep metric := by
    intro b hb
    exact hsep b ⟨0, features.zero_mem, b, by simpa using hb, by simp⟩
  have htotal_nonneg : (0 : ℝ) ≤ ∑ s, |coeff s| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hstep : ∀ ε : ℝ, 0 < ε → ε < gap → (gap - ε) * ∑ s, |coeff s| < sep metric := by
    intro ε hε hεgap
    have hprobenorm :
        ‖fun s ↦ (gap - ε) * (if 0 ≤ coeff s then (1 : ℝ) else -1)‖ < gap := by
      rw [pi_norm_lt_iff (by linarith)]
      intro s
      show ‖(gap - ε) * (if 0 ≤ coeff s then (1 : ℝ) else -1)‖ < gap
      rw [Real.norm_eq_abs]
      by_cases hc : 0 ≤ coeff s
      · rw [if_pos hc, mul_one, abs_of_nonneg (by linarith)]
        linarith
      · rw [if_neg hc, mul_neg_one, abs_neg, abs_of_nonneg (by linarith)]
        linarith
    have hlt : ∑ s, coeff s * ((gap - ε) * (if 0 ≤ coeff s then (1 : ℝ) else -1)) <
        sep metric := by
      rw [hpair]
      exact hballlt _ hprobenorm
    have hval : ∑ s, coeff s * ((gap - ε) * (if 0 ≤ coeff s then (1 : ℝ) else -1)) =
        (gap - ε) * ∑ s, |coeff s| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      by_cases hc : 0 ≤ coeff s
      · rw [if_pos hc, abs_of_nonneg hc]
        ring
      · rw [if_neg hc, abs_of_nonpos (le_of_not_ge hc)]
        ring
    linarith [hval ▸ hlt]
  have hupper : sep metric ≤ (∑ s, |coeff s|) * gap := by
    have hb := hzeroFeature best hbest
    have hsplit : sep metric = ∑ s, coeff s * (metric s - best s) := by
      have h1 : ∑ s, coeff s * (metric s - best s) =
          (∑ s, coeff s * metric s) - ∑ s, coeff s * best s := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      rw [h1, hpair metric, hpair best, hb, sub_zero]
    rw [hsplit]
    calc ∑ s, coeff s * (metric s - best s) ≤ ∑ s, |coeff s| * gap := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          have hbound : |metric s - best s| ≤ gap := by
            rw [← hattained, ← Real.norm_eq_abs]
            exact norm_le_pi_norm (metric - best) s
          calc coeff s * (metric s - best s) ≤ |coeff s * (metric s - best s)| :=
                le_abs_self _
            _ = |coeff s| * |metric s - best s| := abs_mul _ _
            _ ≤ |coeff s| * gap := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ = (∑ s, |coeff s|) * gap := by rw [Finset.sum_mul]
  have htotal_pos : (0 : ℝ) < ∑ s, |coeff s| := by
    rcases lt_or_eq_of_le htotal_nonneg with h | h
    · exact h
    · exfalso
      nlinarith [hupper, hmetricpos]
  have hlower : gap * ∑ s, |coeff s| ≤ sep metric := by
    by_contra hcon
    push_neg at hcon
    have hεpos : 0 < min (gap / 2)
        ((gap * ∑ s, |coeff s| - sep metric) / (2 * ∑ s, |coeff s|)) :=
      lt_min (by linarith) (div_pos (by linarith) (by linarith))
    have hεgap : min (gap / 2)
        ((gap * ∑ s, |coeff s| - sep metric) / (2 * ∑ s, |coeff s|)) < gap :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hkey := hstep _ hεpos hεgap
    have hεle : min (gap / 2)
        ((gap * ∑ s, |coeff s| - sep metric) / (2 * ∑ s, |coeff s|)) ≤
        (gap * ∑ s, |coeff s| - sep metric) / (2 * ∑ s, |coeff s|) := min_le_right _ _
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ∑ s, |coeff s|)] at hεle
    nlinarith [hkey]
  have heq : gap * ∑ s, |coeff s| = sep metric :=
    le_antisymm hlower (by linarith [hupper])
  refine ⟨fun s ↦ coeff s / (∑ t, |coeff t|), ?_, ?_, ?_⟩
  · have h1 : ∀ s : S, abs (coeff s / (∑ t, |coeff t|)) =
        |coeff s| / (∑ t, |coeff t|) := fun s ↦ by
      rw [abs_div, abs_of_nonneg htotal_nonneg]
    rw [Finset.sum_congr rfl fun s _ ↦ h1 s, ← Finset.sum_div,
      div_self (ne_of_gt htotal_pos)]
  · intro g hg
    have h1 : ∀ s : S, coeff s / (∑ t, |coeff t|) * g s =
        coeff s * g s / (∑ t, |coeff t|) := fun s ↦ by ring
    rw [Finset.sum_congr rfl fun s _ ↦ h1 s, ← Finset.sum_div, hpair g,
      hzeroFeature g hg, zero_div]
  · have h1 : ∀ s : S, coeff s / (∑ t, |coeff t|) * metric s =
        coeff s * metric s / (∑ t, |coeff t|) := fun s ↦ by ring
    rw [Finset.sum_congr rfl fun s _ ↦ h1 s, ← Finset.sum_div, hpair metric, ← heq,
      mul_div_assoc, div_self (ne_of_gt htotal_pos), mul_one]

/-- UPT (9.3): the worst summary-invisible disagreement is exactly twice the gap, and it is
attained by an explicit pair of genuine probability laws with identical summaries. -/
theorem exists_attaining_pair [DecidableEq S] (features : Submodule ℝ (S → ℝ))
    (metric : S → ℝ) (hone : (fun _ ↦ (1 : ℝ)) ∈ features)
    (hpos : 0 < summaryGap features metric) :
    ∃ p q : FiniteReportLaw S, (∀ g ∈ features, p.expectation g = q.expectation g) ∧
      p.expectation metric - q.expectation metric = 2 * summaryGap features metric := by
  obtain ⟨best, hbest, hattained, hfar⟩ := exists_best_approximation features metric
  obtain ⟨dir, hdirone, hdirfeature, hdirmetric⟩ :=
    exists_dual_direction features metric best _ hbest hattained hfar hpos
  have hdirzero : ∑ s, dir s = 0 := by
    have hmass := hdirfeature _ hone
    simpa using hmass
  refine ⟨positiveHalf dir hdirzero hdirone, negativeHalf dir hdirzero hdirone, ?_, ?_⟩
  · intro g hg
    have hsplit := half_expectation_sub dir hdirzero hdirone g
    rw [hdirfeature g hg] at hsplit
    linarith
  · have hsplit := half_expectation_sub dir hdirzero hdirone metric
    rw [hdirmetric] at hsplit
    linarith

/-- The upper half of UPT (9.4): the best uniform approximation used as a linear summary
estimator has error at most the gap on every probability law. -/
theorem linear_estimator_error_le_summaryGap (features : Submodule ℝ (S → ℝ))
    (metric : S → ℝ) (best : S → ℝ) (hnorm : ‖metric - best‖ = summaryGap features metric)
    (p : FiniteReportLaw S) :
    |p.expectation metric - p.expectation best| ≤ summaryGap features metric := by
  rw [← expectation_sub_metric, ← hnorm]
  exact abs_expectation_le_norm p (metric - best)

/-- The lower half of UPT (9.4): every estimator that reads only the summary, nonlinear ones
included, has worst-case error at least the gap. -/
theorem summary_estimator_error_ge_summaryGap [DecidableEq S]
    (features : Submodule ℝ (S → ℝ)) (metric : S → ℝ)
    (hone : (fun _ ↦ (1 : ℝ)) ∈ features) (hpos : 0 < summaryGap features metric)
    (estimate : FiniteReportLaw S → ℝ)
    (hsummary : ∀ p q : FiniteReportLaw S,
      (∀ g ∈ features, p.expectation g = q.expectation g) → estimate p = estimate q) :
    ∃ p : FiniteReportLaw S,
      summaryGap features metric ≤ |p.expectation metric - estimate p| := by
  obtain ⟨p, q, hsame, hdiff⟩ := exists_attaining_pair features metric hone hpos
  have hval : estimate p = estimate q := hsummary p q hsame
  by_contra hcon
  push_neg at hcon
  have hp := hcon p
  have hq := hcon q
  rw [hval] at hp
  have hpb := abs_lt.1 hp
  have hqb := abs_lt.1 hq
  linarith [hpb.1, hpb.2, hqb.1, hqb.2, hdiff]

/-- Exact identification on all probability laws holds precisely when the metric already
lies in the feature span, the closing sentence of UPT Theorem 9.2. -/
theorem identified_iff_mem_features [DecidableEq S] (features : Submodule ℝ (S → ℝ))
    (metric : S → ℝ) (hone : (fun _ ↦ (1 : ℝ)) ∈ features) :
    (∀ p q : FiniteReportLaw S, (∀ g ∈ features, p.expectation g = q.expectation g) →
        p.expectation metric = q.expectation metric) ↔ metric ∈ features := by
  constructor
  · intro hident
    by_contra hnot
    have hpos : 0 < summaryGap features metric := by
      rcases lt_or_eq_of_le (summaryGap_nonneg features metric) with h | h
      · exact h
      · refine absurd ?_ hnot
        have hclosure : metric ∈ closure (features : Set (S → ℝ)) :=
          (Metric.mem_closure_iff_infDist_zero ⟨0, features.zero_mem⟩).2 h.symm
        rwa [features.closed_of_finiteDimensional.closure_eq] at hclosure
    obtain ⟨p, q, hsame, hdiff⟩ := exists_attaining_pair features metric hone hpos
    have hzero := hident p q hsame
    linarith
  · intro hmem p q hsame
    exact hsame metric hmem

end

end Descent.Portability.SummaryInvisibleDiameter
