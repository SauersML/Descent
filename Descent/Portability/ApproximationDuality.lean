/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

assert_below Descent.Decision Descent.Program

/-!
# Information diameter equals twice the best uniform approximation error

PL Theorem 8.1. For a report `f` on a finite state space and a space `V` of supplied
observables containing the constants, the supremum of the report difference over pairs
of probability laws that agree on every expectation in `V` is exactly twice the best
uniform approximation error of `f` by `V`. The easy inequality is the triangle
inequality; the converse is a separating-hyperplane construction producing an explicit
moment-matched pair, so no attainment is assumed. The hypotheses are the domain
conditions of the manuscript: a finite state space, a subspace of observables, and the
constant function among them.

PL Theorem 8.1's optimal-recovery half is proved here too: no rule reading only the
`V`-expectations beats half the diameter, and the affine rule `E v` attains the uniform
residual. The laws are `Portability.weightedExp` probability vectors, tied to the
report-gap set by `weightedExp_report_gap_mem`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ApproximationDuality

open Foundations

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The report differences realized by two finitely supported probability laws that
agree on every expectation in `V`. -/
def reportGaps (V : Submodule ℝ (S → ℝ)) (f : S → ℝ) : Set ℝ :=
  {t | ∃ p q : S → ℝ, (∀ s, 0 ≤ p s) ∧ (∀ s, 0 ≤ q s) ∧
    ∑ s, p s = 1 ∧ ∑ s, q s = 1 ∧
    (∀ v ∈ V, ∑ s, p s * v s = ∑ s, q s * v s) ∧
    t = (∑ s, p s * f s) - ∑ s, q s * f s}

/-- The gap set is symmetric: exchanging the two laws negates the report difference, so
the supremum of the signed gap is the supremum of its absolute value. -/
theorem reportGaps_neg (V : Submodule ℝ (S → ℝ)) (f : S → ℝ) {t : ℝ}
    (ht : t ∈ reportGaps V f) : -t ∈ reportGaps V f := by
  obtain ⟨p, q, hp, hq, hps, hqs, hmatch, rfl⟩ := ht
  exact ⟨q, p, hq, hp, hqs, hps, fun v hv ↦ (hmatch v hv).symm, by ring⟩

/-- The zero gap is always realized, by taking the two laws equal. -/
theorem zero_mem_reportGaps [Nonempty S] (V : Submodule ℝ (S → ℝ)) (f : S → ℝ) :
    (0 : ℝ) ∈ reportGaps V f := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  refine ⟨fun s ↦ if s = s₀ then 1 else 0, fun s ↦ if s = s₀ then 1 else 0,
    fun s ↦ by split <;> norm_num, fun s ↦ by split <;> norm_num, by simp, by simp,
    fun v _ ↦ rfl, by ring⟩

/-- A probability average of `f - v` never exceeds the uniform norm of `f - v`. -/
theorem abs_average_le_norm (f v : S → ℝ) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hps : ∑ s, p s = 1) : |∑ s, p s * (f s - v s)| ≤ ‖f - v‖ := by
  calc |∑ s, p s * (f s - v s)| ≤ ∑ s, |p s * (f s - v s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, p s * |f s - v s| := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hp s)]
    _ ≤ ∑ s, p s * ‖f - v‖ := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        have hs : |f s - v s| ≤ ‖f - v‖ := by
          have hb := norm_le_pi_norm (f - v) s
          simpa [Real.norm_eq_abs] using hb
        exact mul_le_mul_of_nonneg_left hs (hp s)
    _ = ‖f - v‖ := by rw [← Finset.sum_mul, hps, one_mul]

/-- **Weak duality.** Every moment-matched report gap is at most twice the uniform
residual of any element of `V`. -/
theorem reportGap_le_two_mul_norm (V : Submodule ℝ (S → ℝ)) (f : S → ℝ) {t : ℝ}
    (ht : t ∈ reportGaps V f) {v : S → ℝ} (hv : v ∈ V) : t ≤ 2 * ‖f - v‖ := by
  obtain ⟨p, q, hp, hq, hps, hqs, hmatch, rfl⟩ := ht
  have hsplit : ∀ w : S → ℝ, ∑ s, w s * (f s - v s) =
      (∑ s, w s * f s) - ∑ s, w s * v s := by
    intro w
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hkey : (∑ s, p s * f s) - ∑ s, q s * f s =
      (∑ s, p s * (f s - v s)) - ∑ s, q s * (f s - v s) := by
    rw [hsplit, hsplit, hmatch v hv]; ring
  have h1 := abs_le.mp (abs_average_le_norm f v p hp hps)
  have h2 := abs_le.mp (abs_average_le_norm f v q hq hqs)
  rw [hkey]
  linarith [h1.2, h2.1]

/-- Every moment-matched report gap is at most twice the best uniform approximation
error of `f` by `V`. -/
theorem reportGap_le_two_mul_infDist (V : Submodule ℝ (S → ℝ)) (f : S → ℝ) {t : ℝ}
    (ht : t ∈ reportGaps V f) : t ≤ 2 * Metric.infDist f (V : Set (S → ℝ)) := by
  have hne : (V : Set (S → ℝ)).Nonempty := ⟨0, V.zero_mem⟩
  by_contra hcon
  push_neg at hcon
  have hlt : Metric.infDist f (V : Set (S → ℝ)) < t / 2 := by linarith
  obtain ⟨v, hv, hvd⟩ := (Metric.infDist_lt_iff hne).mp hlt
  have hle := reportGap_le_two_mul_norm V f ht hv
  rw [dist_eq_norm] at hvd
  linarith

/-- The coordinate indicator of a state, the dual basis used to read off a linear
functional on the finite state space. -/
def stdBasis (s : S) : S → ℝ := fun u ↦ if u = s then 1 else 0

/-- A continuous linear functional on the finite state space is the inner product with
its values on the coordinate indicators. -/
theorem eval_as_sum (φ : (S → ℝ) →L[ℝ] ℝ) (g : S → ℝ) :
    φ g = ∑ s, g s * φ (stdBasis s) := by
  have hrep : g = ∑ s, g s • (stdBasis s : S → ℝ) := by
    funext u
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem u (Finset.mem_univ u)]
    · simp [stdBasis]
    · intro b _ hb
      simp [stdBasis, Ne.symm hb]
  conv_lhs => rw [hrep]
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [map_smul]; simp [smul_eq_mul]

/-- The open `r`-neighbourhood of `V` inside the uniform norm. -/
def approxNbhd (V : Submodule ℝ (S → ℝ)) (r : ℝ) : Set (S → ℝ) :=
  {g : S → ℝ | ∃ v ∈ V, ‖g - v‖ < r}

/-- The neighbourhood of a subspace is open. -/
theorem isOpen_approxNbhd (V : Submodule ℝ (S → ℝ)) (r : ℝ) :
    IsOpen (approxNbhd V r) := by
  have hEq : approxNbhd V r = ⋃ v ∈ (V : Set (S → ℝ)), Metric.ball v r := by
    ext g
    simp [approxNbhd, Set.mem_iUnion₂, Metric.mem_ball, dist_eq_norm]
  rw [hEq]
  exact isOpen_biUnion fun v _ ↦ Metric.isOpen_ball

/-- The neighbourhood of a subspace is convex. -/
theorem convex_approxNbhd (V : Submodule ℝ (S → ℝ)) (r : ℝ) :
    Convex ℝ (approxNbhd V r) := by
  rintro g₁ ⟨v₁, hv₁, h₁⟩ g₂ ⟨v₂, hv₂, h₂⟩ a b ha hb hab
  refine ⟨a • v₁ + b • v₂, V.add_mem (V.smul_mem a hv₁) (V.smul_mem b hv₂), ?_⟩
  have hEq : a • g₁ + b • g₂ - (a • v₁ + b • v₂) = a • (g₁ - v₁) + b • (g₂ - v₂) := by
    simp only [smul_sub]; abel
  rw [hEq]
  have hm1 : a * ‖g₁ - v₁‖ ≤ a * max ‖g₁ - v₁‖ ‖g₂ - v₂‖ :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) ha
  have hm2 : b * ‖g₂ - v₂‖ ≤ b * max ‖g₁ - v₁‖ ‖g₂ - v₂‖ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hb
  have hsum : a * max ‖g₁ - v₁‖ ‖g₂ - v₂‖ + b * max ‖g₁ - v₁‖ ‖g₂ - v₂‖ =
      max ‖g₁ - v₁‖ ‖g₂ - v₂‖ := by
    rw [← add_mul, hab, one_mul]
  have htri : ‖a • (g₁ - v₁) + b • (g₂ - v₂)‖ ≤ a * ‖g₁ - v₁‖ + b * ‖g₂ - v₂‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb]
  have hmax : max ‖g₁ - v₁‖ ‖g₂ - v₂‖ < r := max_lt h₁ h₂
  linarith

/-- **The dual certificate.** If no element of `V` approximates `f` to within `r` and
`0 < c < r`, separation of `f` from the `r`-neighbourhood of `V` yields a signed weight
that annihilates `V`, has zero total mass, and pairs with `f` above `c` times its total
variation. -/
theorem exists_dual_sign (V : Submodule ℝ (S → ℝ))
    (hconst : ∀ a : ℝ, (fun _ : S ↦ a) ∈ V) (f : S → ℝ) {c r : ℝ}
    (hc : 0 < c) (hcr : c < r) (hr : ∀ v ∈ V, r ≤ ‖f - v‖) :
    ∃ σ : S → ℝ, (∀ v ∈ V, ∑ s, v s * σ s = 0) ∧ ∑ s, σ s = 0 ∧
      0 < ∑ s, |σ s| ∧ c * (∑ s, |σ s|) < ∑ s, f s * σ s := by
  have hr0 : 0 < r := hc.trans hcr
  have hfC : f ∉ approxNbhd V r := by
    rintro ⟨v, hv, hlt⟩
    exact absurd (hr v hv) (not_le.mpr hlt)
  obtain ⟨φ, hφ⟩ :=
    geometric_hahn_banach_open_point (convex_approxNbhd V r) (isOpen_approxNbhd V r) hfC
  have hmemC : ∀ g : S → ℝ, ‖g‖ < r → g ∈ approxNbhd V r := fun g hg ↦
    ⟨0, V.zero_mem, by simpa using hg⟩
  have hzero : (0 : ℝ) < φ f := by
    have h0 : (0 : S → ℝ) ∈ approxNbhd V r := hmemC 0 (by simpa using hr0)
    simpa using hφ 0 h0
  have hVzero : ∀ v ∈ V, ∑ s, v s * φ (stdBasis s) = 0 := by
    intro v hv
    have hall : ∀ τ : ℝ, τ * φ v < φ f := by
      intro τ
      have hmem : τ • v ∈ approxNbhd V r := ⟨τ • v, V.smul_mem τ hv, by simpa using hr0⟩
      have hlt := hφ (τ • v) hmem
      rwa [map_smul, smul_eq_mul] at hlt
    have hφv : φ v = 0 := by
      by_contra hne
      have h := hall ((φ f + 1) / φ v)
      rw [div_mul_cancel₀ _ hne] at h
      linarith
    rw [← eval_as_sum φ v, hφv]
  refine ⟨fun s ↦ φ (stdBasis s), hVzero, ?_, ?_, ?_⟩
  · have h1 := hVzero (fun _ ↦ (1 : ℝ)) (hconst 1)
    simpa using h1
  · by_contra hcon
    push_neg at hcon
    have hnn : (0 : ℝ) ≤ ∑ s, |φ (stdBasis s)| :=
      Finset.sum_nonneg fun s _ ↦ abs_nonneg _
    have hz : ∑ s, |φ (stdBasis s)| = 0 := le_antisymm hcon hnn
    have hσ0 : ∀ s : S, φ (stdBasis s) = 0 := by
      intro s
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ ↦ abs_nonneg (φ (stdBasis s)))).mp hz s (Finset.mem_univ s)
      exact abs_eq_zero.mp this
    have : φ f = 0 := by
      rw [eval_as_sum φ f]
      exact Finset.sum_eq_zero fun s _ ↦ by rw [hσ0 s, mul_zero]
    linarith
  · have hwnorm : ‖fun s ↦ if 0 ≤ φ (stdBasis s) then c else -c‖ ≤ c := by
      rw [pi_norm_le_iff_of_nonneg hc.le]
      intro s
      have habs : |if 0 ≤ φ (stdBasis s) then c else -c| = c := by
        split
        · exact abs_of_nonneg hc.le
        · rw [abs_neg]; exact abs_of_nonneg hc.le
      simpa [Real.norm_eq_abs] using habs.le
    have hwmem : (fun s ↦ if 0 ≤ φ (stdBasis s) then c else -c) ∈ approxNbhd V r :=
      hmemC _ (lt_of_le_of_lt hwnorm hcr)
    have hlt := hφ _ hwmem
    rw [eval_as_sum φ (fun s ↦ if 0 ≤ φ (stdBasis s) then c else -c)] at hlt
    have hterm : ∀ s : S,
        (if 0 ≤ φ (stdBasis s) then c else -c) * φ (stdBasis s) =
          c * |φ (stdBasis s)| := by
      intro s
      split
      · next h => rw [abs_of_nonneg h]
      · next h => rw [abs_of_neg (not_le.mp h)]; ring
    calc c * ∑ s, |φ (stdBasis s)| = ∑ s, c * |φ (stdBasis s)| := by rw [Finset.mul_sum]
      _ = ∑ s, (if 0 ≤ φ (stdBasis s) then c else -c) * φ (stdBasis s) :=
          (Finset.sum_congr rfl fun s _ ↦ hterm s).symm
      _ < φ f := hlt
      _ = ∑ s, f s * φ (stdBasis s) := eval_as_sum φ f

/-- **Strong duality, constructive half.** If every element of `V` leaves uniform
residual at least `r` and `0 < c < r`, then an explicit moment-matched pair of
probability laws has report difference at least `2c`. -/
theorem exists_reportGap_ge (V : Submodule ℝ (S → ℝ))
    (hconst : ∀ a : ℝ, (fun _ : S ↦ a) ∈ V) (f : S → ℝ) {c r : ℝ}
    (hc : 0 < c) (hcr : c < r) (hr : ∀ v ∈ V, r ≤ ‖f - v‖) :
    ∃ t ∈ reportGaps V f, 2 * c ≤ t := by
  obtain ⟨σ, hVσ, hσsum, hApos, hbump⟩ := exists_dual_sign V hconst f hc hcr hr
  have hsplit : ∀ w : S → ℝ,
      (∑ s, ((|σ s| + σ s) / ∑ u, |σ u|) * w s) -
          ∑ s, ((|σ s| - σ s) / ∑ u, |σ u|) * w s =
        (2 / ∑ u, |σ u|) * ∑ s, w s * σ s := by
    intro w
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    field_simp
    ring
  refine ⟨(2 / ∑ u, |σ u|) * ∑ s, f s * σ s, ?_, ?_⟩
  · refine ⟨fun s ↦ (|σ s| + σ s) / ∑ u, |σ u|, fun s ↦ (|σ s| - σ s) / ∑ u, |σ u|,
      fun s ↦ div_nonneg (by linarith [neg_abs_le (σ s)]) hApos.le,
      fun s ↦ div_nonneg (by linarith [le_abs_self (σ s)]) hApos.le, ?_, ?_, ?_, ?_⟩
    · rw [← Finset.sum_div, Finset.sum_add_distrib, hσsum, add_zero, div_self hApos.ne']
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, hσsum, sub_zero, div_self hApos.ne']
    · intro v hv
      have h := hsplit v
      rw [hVσ v hv, mul_zero] at h
      linarith
    · exact (hsplit f).symm
  · rw [div_mul_eq_mul_div, le_div_iff₀ hApos]
    nlinarith [hbump, hApos]

/-- **PL Theorem 8.1.** The information diameter of a bounded report over laws matched on
`V` is exactly twice the best uniform approximation error of the report by `V`. -/
theorem information_diameter_duality [Nonempty S]
    (V : Submodule ℝ (S → ℝ)) (hconst : ∀ a : ℝ, (fun _ : S ↦ a) ∈ V) (f : S → ℝ) :
    IsLUB (reportGaps V f) (2 * Metric.infDist f (V : Set (S → ℝ))) := by
  constructor
  · intro t ht
    exact reportGap_le_two_mul_infDist V f ht
  · intro ub hub
    have hub0 : 0 ≤ ub := hub (zero_mem_reportGaps V f)
    by_contra hcon
    push_neg at hcon
    have he0 : 0 < Metric.infDist f (V : Set (S → ℝ)) := by
      have := Metric.infDist_nonneg (x := f) (s := (V : Set (S → ℝ)))
      rcases this.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hcon; linarith
    obtain ⟨c, hc1, hc2⟩ :=
      exists_between (max_lt he0 (by linarith :
        ub / 2 < Metric.infDist f (V : Set (S → ℝ))))
    have hcpos : 0 < c := lt_of_le_of_lt (le_max_left _ _) hc1
    have hcub : ub / 2 < c := lt_of_le_of_lt (le_max_right _ _) hc1
    have hr : ∀ v ∈ V, Metric.infDist f (V : Set (S → ℝ)) ≤ ‖f - v‖ := by
      intro v hv
      have := Metric.infDist_le_dist_of_mem (x := f) hv
      rwa [dist_eq_norm] at this
    obtain ⟨t, ht, hge⟩ := exists_reportGap_ge V hconst f hcpos hc2 hr
    have := hub ht
    linarith

/-- The information diameter as a supremum. -/
theorem information_diameter_sSup [Nonempty S] (V : Submodule ℝ (S → ℝ))
    (hconst : ∀ a : ℝ, (fun _ : S ↦ a) ∈ V) (f : S → ℝ) :
    sSup (reportGaps V f) = 2 * Metric.infDist f (V : Set (S → ℝ)) :=
  (information_diameter_duality V hconst f).csSup_eq
    ⟨0, zero_mem_reportGaps V f⟩

/-- A report gap between two `weightedExp` laws matched on `V` lies in `reportGaps`,
which is what ties the duality to the corpus' finitely supported expectations. -/
theorem weightedExp_report_gap_mem (V : Submodule ℝ (S → ℝ)) (f : S → ℝ)
    (p q : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hps : ∑ s, p s = 1) (hqs : ∑ s, q s = 1)
    (hmatch : ∀ v ∈ V, weightedExp p hp hps v = weightedExp q hq hqs v) :
    weightedExp p hp hps f - weightedExp q hq hqs f ∈ reportGaps V f :=
  ⟨p, q, hp, hq, hps, hqs, hmatch, rfl⟩

/-- **Optimal recovery, lower half.** Any single reported number incurs, on one of a
moment-matched pair, at least half their report difference. -/
theorem recovery_error_lower (f : S → ℝ) (p q : S → ℝ) (θ : ℝ) :
    ((∑ s, p s * f s) - ∑ s, q s * f s) / 2 ≤
      max |(∑ s, p s * f s) - θ| |(∑ s, q s * f s) - θ| := by
  have h1 : (∑ s, p s * f s) - θ ≤ max |(∑ s, p s * f s) - θ| |(∑ s, q s * f s) - θ| :=
    le_trans (le_abs_self _) (le_max_left _ _)
  have h2 : -((∑ s, q s * f s) - θ) ≤
      max |(∑ s, p s * f s) - θ| |(∑ s, q s * f s) - θ| :=
    le_trans (neg_le_abs _) (le_max_right _ _)
  linarith

/-- **Optimal recovery, upper half.** The affine rule that reports the expectation of a
uniform approximant errs by at most that approximant's uniform residual. -/
theorem recovery_error_upper (f v : S → ℝ) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hps : ∑ s, p s = 1) :
    |(∑ s, p s * v s) - ∑ s, p s * f s| ≤ ‖f - v‖ := by
  have hsplit : ∑ s, p s * (f s - v s) = (∑ s, p s * f s) - ∑ s, p s * v s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have h := abs_average_le_norm f v p hp hps
  rw [hsplit] at h
  rwa [abs_sub_comm]

end

end Descent.Portability.ApproximationDuality
