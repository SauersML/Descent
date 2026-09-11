/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverTrajectoryRegion
import Mathlib.Analysis.Calculus.Deriv.MeanValue

assert_below Descent.Decision Descent.Program

/-!
# The continuous-time turnover-trajectory envelope

UPT Theorem 5.4's continuous-time version bounds the agreement path of two
equal-effect loci whose conditional flip rate is `lam`: starting from perfect
agreement, the path obeys `-2λ a(t) ≤ a'(t) ≤ 2λ(1 - a(t))`, and consequently
the terminal agreement lies in `[e^{-2λt}, 1]`.

Both halves of that consequence are proved here at the level of paths. Every
admissible path is trapped in the interval, by comparing `a(t)e^{2λt}` and
`(a(t)-1)e^{2λt}` with the mean value theorem; and every value of the interval is
the terminal value of an explicit admissible path, the mixture of total decay
with perfect synchrony. So the interval is exactly the attainable set of terminal
agreements over admissible paths, and multiplying by the accuracy ceiling gives
the expected-accuracy form.

Scope: the paths here are differentiable on the nonnegative half line rather than
absolutely continuous with the inequalities holding almost everywhere, and the
statement is about paths rather than about the coadapted continuous-time
couplings that generate them. The discrete-time counterpart in
`TurnoverTrajectoryRegion` is the one proved at process level.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ContinuousTrajectoryRegion

open Foundations

noncomputable section

section Envelope

/-- The exponential integrating factor of the agreement equation. -/
def growth (lam t : ℝ) : ℝ := Real.exp (2 * lam * t)

/-- The integrating factor is positive and cancels the decay exponential. -/
theorem growth_pos (lam t : ℝ) : 0 < growth lam t := Real.exp_pos _

/-- The integrating factor inverts the decay exponential. -/
theorem growth_mul_decay (lam t : ℝ) :
    growth lam t * Real.exp (-(2 * lam * t)) = 1 := by
  rw [growth, ← Real.exp_add]
  simp

/-- Derivative of a path multiplied by the integrating factor. -/
theorem hasDerivAt_growth_mul {a : ℝ → ℝ} {d : ℝ} {lam t : ℝ} (h : HasDerivAt a d t)
    (c : ℝ) : HasDerivAt (fun s ↦ (a s - c) * growth lam s)
      (d * growth lam t + (a t - c) * (growth lam t * (2 * lam))) t := by
  have hlin : HasDerivAt (fun s : ℝ ↦ 2 * lam * s) (2 * lam) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * lam)
  have hexp : HasDerivAt (fun s : ℝ ↦ growth lam s) (growth lam t * (2 * lam)) t :=
    (Real.hasDerivAt_exp _).comp t hlin
  exact ((h.sub_const c).mul hexp)

/-- **UPT (5.10), the consequence.**  An agreement path that starts at one and obeys the
two rate inequalities on the nonnegative half line stays in `[e^{-2λt}, 1]`. -/
theorem admissible_path_bounds (lam : ℝ) (hlam : 0 ≤ lam) (a d : ℝ → ℝ) (ha0 : a 0 = 1)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt a (d t) t)
    (hlow : ∀ t, 0 ≤ t → -(2 * lam) * a t ≤ d t)
    (hhigh : ∀ t, 0 ≤ t → d t ≤ 2 * lam * (1 - a t)) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(2 * lam * t)) ≤ a t ∧ a t ≤ 1 := by
  have hgrow : ∀ (c s : ℝ), 0 ≤ s →
      HasDerivAt (fun r ↦ (a r - c) * growth lam r)
        (d s * growth lam s + (a s - c) * (growth lam s * (2 * lam))) s :=
    fun c s hs ↦ hasDerivAt_growth_mul (hderiv s hs) c
  have hdiff : ∀ c : ℝ, DifferentiableOn ℝ (fun r ↦ (a r - c) * growth lam r) (Set.Ici 0) :=
    fun c s hs ↦ (hgrow c s hs).differentiableAt.differentiableWithinAt
  have hcont : ∀ c : ℝ, ContinuousOn (fun r ↦ (a r - c) * growth lam r) (Set.Ici 0) :=
    fun c ↦ (hdiff c).continuousOn
  constructor
  · have hmono : MonotoneOn (fun r ↦ (a r - 0) * growth lam r) (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (hcont 0) ?_ ?_
      · rw [interior_Ici]
        exact fun s hs ↦ (hgrow 0 s (le_of_lt hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
        rw [(hgrow 0 s hs0).deriv]
        have hg := growth_pos lam s
        nlinarith [hlow s hs0]
    have hkey := hmono Set.left_mem_Ici (Set.mem_Ici.mpr ht) ht
    have hg0 : growth lam 0 = 1 := by
      rw [growth]
      simp
    rw [ha0, hg0] at hkey
    simp only [sub_zero, one_mul] at hkey
    have h2 := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-(2 * lam * t))).le
    rw [one_mul, mul_assoc, growth_mul_decay, mul_one] at h2
    exact h2
  · have hanti : AntitoneOn (fun r ↦ (a r - 1) * growth lam r) (Set.Ici 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (hcont 1) ?_ ?_
      · rw [interior_Ici]
        exact fun s hs ↦ (hgrow 1 s (le_of_lt hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
        rw [(hgrow 1 s hs0).deriv]
        have hg := growth_pos lam s
        nlinarith [hhigh s hs0]
    have hkey := hanti Set.left_mem_Ici (Set.mem_Ici.mpr ht) ht
    have hg0 : growth lam 0 = 1 := by
      rw [growth]
      simp
    rw [ha0, hg0] at hkey
    simp only [sub_self, zero_mul] at hkey
    nlinarith [growth_pos lam t, hkey]

end Envelope

section Attainment

/-- The one-parameter family of admissible agreement paths interpolating between total
decay and perfect synchrony. -/
def mixPath (lam θ t : ℝ) : ℝ := θ * Real.exp (-(2 * lam * t)) + (1 - θ)

/-- The derivative of the interpolating path. -/
def mixPathDeriv (lam θ t : ℝ) : ℝ := -(2 * lam) * (θ * Real.exp (-(2 * lam * t)))

/-- The interpolating path starts at perfect agreement. -/
theorem mixPath_zero (lam θ : ℝ) : mixPath lam θ 0 = 1 := by
  rw [mixPath]
  simp

/-- The interpolating path has the stated derivative. -/
theorem mixPath_hasDerivAt (lam θ t : ℝ) :
    HasDerivAt (mixPath lam θ) (mixPathDeriv lam θ t) t := by
  have hlin : HasDerivAt (fun s : ℝ ↦ -(2 * lam * s)) (-(2 * lam)) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * lam)).neg
  have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(2 * lam * s)))
      (Real.exp (-(2 * lam * t)) * -(2 * lam)) t := (Real.hasDerivAt_exp _).comp t hlin
  have hval : mixPathDeriv lam θ t = θ * (Real.exp (-(2 * lam * t)) * -(2 * lam)) := by
    rw [mixPathDeriv]
    ring
  rw [hval]
  exact (hexp.const_mul θ).add_const (1 - θ)

/-- **The interpolating path is admissible** for every mixing weight in the unit
interval. -/
theorem mixPath_admissible (lam θ : ℝ) (hlam : 0 ≤ lam) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (t : ℝ) :
    -(2 * lam) * mixPath lam θ t ≤ mixPathDeriv lam θ t ∧
      mixPathDeriv lam θ t ≤ 2 * lam * (1 - mixPath lam θ t) := by
  have hepos : 0 < Real.exp (-(2 * lam * t)) := Real.exp_pos _
  rw [mixPath, mixPathDeriv]
  constructor <;> nlinarith [hepos, hlam, hθ0, hθ1]

/-- **UPT (5.10), attainment.**  Every value of `[e^{-2λT}, 1]` is the terminal agreement of
an admissible path. -/
theorem mixPath_terminal_attained (lam : ℝ) (hlam : 0 ≤ lam) (T y : ℝ)
    (hy1 : Real.exp (-(2 * lam * T)) ≤ y) (hy2 : y ≤ 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ mixPath lam θ T = y := by
  have hepos : 0 < Real.exp (-(2 * lam * T)) := Real.exp_pos _
  by_cases hdeg : Real.exp (-(2 * lam * T)) = 1
  · refine ⟨0, le_refl 0, by norm_num, ?_⟩
    rw [mixPath]
    rw [hdeg] at hy1
    have : y = 1 := le_antisymm hy2 hy1
    rw [this]
    ring
  · have hlt : Real.exp (-(2 * lam * T)) < 1 := lt_of_le_of_ne (le_trans hy1 hy2) hdeg
    have hden : (0 : ℝ) < 1 - Real.exp (-(2 * lam * T)) := by linarith
    have hdenne : (1 : ℝ) - Real.exp (-(2 * lam * T)) ≠ 0 := ne_of_gt hden
    refine ⟨(1 - y) / (1 - Real.exp (-(2 * lam * T))), div_nonneg (by linarith) hden.le, ?_, ?_⟩
    · rw [div_le_one hden]
      linarith
    · rw [mixPath]
      have hstep : (1 - y) / (1 - Real.exp (-(2 * lam * T)))
          * (1 - Real.exp (-(2 * lam * T))) = 1 - y := by
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self hdenne, mul_one]
      have hexpand : (1 - y) / (1 - Real.exp (-(2 * lam * T))) * Real.exp (-(2 * lam * T))
          + (1 - (1 - y) / (1 - Real.exp (-(2 * lam * T))))
          = 1 - (1 - y) / (1 - Real.exp (-(2 * lam * T)))
            * (1 - Real.exp (-(2 * lam * T))) := by ring
      rw [hexpand, hstep]
      ring

end Attainment

section AccuracyScale

/-- **The expected-accuracy form of UPT (5.10).**  In the two-equal-effect architecture the
expected accuracy is the ceiling of `TurnoverDependence` times the agreement path, so every
accuracy of `[Q₀ e^{-2λT}, Q₀]` is attained by an admissible path and none outside it is. -/
theorem ceiling_mixPath_terminal_attained (H sigma lam : ℝ) (hlam : 0 ≤ lam) (T y : ℝ)
    (hy1 : Real.exp (-(2 * lam * T)) ≤ y) (hy2 : y ≤ 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      TurnoverDependence.ceiling H sigma * mixPath lam θ T
        = TurnoverDependence.ceiling H sigma * y := by
  obtain ⟨θ, hθ0, hθ1, hval⟩ := mixPath_terminal_attained lam hlam T y hy1 hy2
  exact ⟨θ, hθ0, hθ1, by rw [hval]⟩

/-- The accuracy scale of the envelope bound. -/
theorem ceiling_admissible_path_bounds (H sigma lam : ℝ) (hH : 0 < H) (hlam : 0 ≤ lam)
    (a d : ℝ → ℝ) (ha0 : a 0 = 1) (hderiv : ∀ t, 0 ≤ t → HasDerivAt a (d t) t)
    (hlow : ∀ t, 0 ≤ t → -(2 * lam) * a t ≤ d t)
    (hhigh : ∀ t, 0 ≤ t → d t ≤ 2 * lam * (1 - a t)) (t : ℝ) (ht : 0 ≤ t) :
    TurnoverDependence.ceiling H sigma * Real.exp (-(2 * lam * t))
        ≤ TurnoverDependence.ceiling H sigma * a t ∧
      TurnoverDependence.ceiling H sigma * a t ≤ TurnoverDependence.ceiling H sigma := by
  have hV : (0 : ℝ) < H + sigma ^ 2 := by nlinarith [sq_nonneg sigma]
  have hQ : 0 < TurnoverDependence.ceiling H sigma := div_pos hH hV
  obtain ⟨h1, h2⟩ := admissible_path_bounds lam hlam a d ha0 hderiv hlow hhigh t ht
  constructor
  · exact mul_le_mul_of_nonneg_left h1 hQ.le
  · have h := mul_le_mul_of_nonneg_left h2 hQ.le
    linarith

end AccuracyScale

end

end Descent.Portability.ContinuousTrajectoryRegion
