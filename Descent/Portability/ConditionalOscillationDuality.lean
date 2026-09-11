/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ApproximationDuality

assert_below Descent.Decision Descent.Program

/-!
# The exact conditional-oscillation formula and its noisy dual price

PL Theorem 8.2 and Corollary 8.3. The pre-outcome marginal `μ` is held fixed and
strictly positive, the conditional outcome kernel is the unknown, and the supplied
features are a finite family `g`. The report diameter over kernel pairs whose feature
expectations agree coordinatewise to within `2ε` is exactly the infimum over multiplier
vectors of the `μ`-weighted conditional oscillation of `f - λᵀg` plus `2ε‖λ‖₁`. Taking
`ε = 0` is Theorem 8.2, equation (8.2); a positive `ε` is Corollary 8.3, equation (8.4).

The upper bound is the row-wise oscillation inequality. The lower bound separates the
report from an explicitly convex open neighbourhood of the feature span and turns the
separating functional into an explicit pair of kernels, so nothing is assumed attainable.
Equation (8.3)'s recovery rule and its worst-case error `Δ/2` are proved directly.

This module reuses `ApproximationDuality.eval_as_sum` and `stdBasis` to read off the
separating functional, and ties the kernels to the corpus through
`jointLaw_expectation`, which evaluates `Portability.weightedExp` on the joint mass.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalOscillationDuality

open Foundations

noncomputable section

variable {W Y F : Type*} [Fintype W] [Fintype Y] [Fintype F] [DecidableEq W] [DecidableEq Y]
variable [Nonempty Y]

/-- The `μ`-weighted total conditional oscillation of an observable. -/
def oscTotal (μ : W → ℝ) (h : W × Y → ℝ) : ℝ :=
  ∑ w, μ w * (Finset.univ.sup' Finset.univ_nonempty (fun y ↦ h (w, y)) -
    Finset.univ.inf' Finset.univ_nonempty (fun y ↦ h (w, y)))

/-- The supplied feature combination `λᵀg`. -/
def featureCombo (g : F → W × Y → ℝ) (lam : F → ℝ) : W × Y → ℝ :=
  fun z ↦ ∑ i, lam i * g i z

/-- The joint mass of a pre-outcome marginal and a conditional kernel. -/
def jointLaw (μ : W → ℝ) (K : W → Y → ℝ) : W × Y → ℝ := fun z ↦ μ z.1 * K z.1 z.2

/-- The report differences realized by two conditional kernels whose feature
expectations agree coordinatewise to within `2ε`, over a fixed pre-outcome marginal. -/
def kernelGaps (μ : W → ℝ) (g : F → W × Y → ℝ) (f : W × Y → ℝ) (ε : ℝ) : Set ℝ :=
  {t | ∃ K L : W → Y → ℝ, (∀ w y, 0 ≤ K w y) ∧ (∀ w y, 0 ≤ L w y) ∧
    (∀ w, ∑ y, K w y = 1) ∧ (∀ w, ∑ y, L w y = 1) ∧
    (∀ i, |(∑ w, μ w * ∑ y, K w y * g i (w, y)) -
      ∑ w, μ w * ∑ y, L w y * g i (w, y)| ≤ 2 * ε) ∧
    t = (∑ w, μ w * ∑ y, K w y * f (w, y)) - ∑ w, μ w * ∑ y, L w y * f (w, y)}

/-- The dual objective of PL equations (8.2) and (8.4). -/
def dualValues (μ : W → ℝ) (g : F → W × Y → ℝ) (f : W × Y → ℝ) (ε : ℝ) : Set ℝ :=
  {s | ∃ lam : F → ℝ, s = oscTotal μ (f - featureCombo g lam) + 2 * ε * ∑ i, |lam i|}

/-- Expectation of the joint mass against the corpus' finitely supported expectation. -/
theorem jointLaw_expectation (μ : W → ℝ) (K : W → Y → ℝ)
    (hp : ∀ z, 0 ≤ jointLaw μ K z) (hs : ∑ z, jointLaw μ K z = 1) (G : W × Y → ℝ) :
    weightedExp (jointLaw μ K) hp hs G = ∑ w, μ w * ∑ y, K w y * G (w, y) := by
  rw [weightedExp_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ ↦ by simp [jointLaw]; ring

/-- A kernel average never exceeds the row supremum. -/
theorem kernel_average_le_sup (K : Y → ℝ) (hK : ∀ y, 0 ≤ K y) (hKs : ∑ y, K y = 1)
    (h : Y → ℝ) : ∑ y, K y * h y ≤ Finset.univ.sup' Finset.univ_nonempty h := by
  calc ∑ y, K y * h y ≤ ∑ y, K y * Finset.univ.sup' Finset.univ_nonempty h := by
        refine Finset.sum_le_sum fun y _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' h (Finset.mem_univ y)) (hK y)
    _ = Finset.univ.sup' Finset.univ_nonempty h := by rw [← Finset.sum_mul, hKs, one_mul]

/-- A kernel average is never below the row infimum. -/
theorem inf_le_kernel_average (K : Y → ℝ) (hK : ∀ y, 0 ≤ K y) (hKs : ∑ y, K y = 1)
    (h : Y → ℝ) : Finset.univ.inf' Finset.univ_nonempty h ≤ ∑ y, K y * h y := by
  calc Finset.univ.inf' Finset.univ_nonempty h
      = ∑ y, K y * Finset.univ.inf' Finset.univ_nonempty h := by
        rw [← Finset.sum_mul, hKs, one_mul]
    _ ≤ ∑ y, K y * h y := by
        refine Finset.sum_le_sum fun y _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le h (Finset.mem_univ y)) (hK y)

/-- Expectation of a feature combination splits into the supplied feature moments. -/
theorem combo_expectation (μ : W → ℝ) (g : F → W × Y → ℝ) (lam : F → ℝ)
    (M : W → Y → ℝ) :
    (∑ w, μ w * ∑ y, M w y * featureCombo g lam (w, y)) =
      ∑ i, lam i * ∑ w, μ w * ∑ y, M w y * g i (w, y) := by
  have h1 : ∀ w, (∑ y, M w y * featureCombo g lam (w, y)) =
      ∑ i, lam i * ∑ y, M w y * g i (w, y) := by
    intro w
    simp only [featureCombo, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring
  rw [Finset.sum_congr rfl fun w _ ↦ by rw [h1 w]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦ by ring

/-- **PL Theorem 8.2, upper bound.** Every feasible report gap is at most the dual
objective at every multiplier vector. -/
theorem kernelGap_le_dual (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (g : F → W × Y → ℝ)
    (f : W × Y → ℝ) (ε : ℝ) {t : ℝ} (ht : t ∈ kernelGaps μ g f ε) (lam : F → ℝ) :
    t ≤ oscTotal μ (f - featureCombo g lam) + 2 * ε * ∑ i, |lam i| := by
  obtain ⟨K, L, hK, hL, hKs, hLs, hmom, rfl⟩ := ht
  have hsplit : ∀ M : W → Y → ℝ,
      (∑ w, μ w * ∑ y, M w y * f (w, y)) =
        (∑ w, μ w * ∑ y, M w y * (f - featureCombo g lam) (w, y)) +
          ∑ i, lam i * ∑ w, μ w * ∑ y, M w y * g i (w, y) := by
    intro M
    rw [← combo_expectation μ g lam M, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun s ↦ μ w * s) (Finset.sum_congr rfl fun y _ ↦ ?_)
    simp [Pi.sub_apply]
    ring
  rw [hsplit K, hsplit L]
  have hosc : (∑ w, μ w * ∑ y, K w y * (f - featureCombo g lam) (w, y)) -
      (∑ w, μ w * ∑ y, L w y * (f - featureCombo g lam) (w, y)) ≤
        oscTotal μ (f - featureCombo g lam) := by
    rw [oscTotal, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun w _ ↦ ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hμ w)
    have h1 := kernel_average_le_sup (K w) (fun y ↦ hK w y) (hKs w)
      (fun y ↦ (f - featureCombo g lam) (w, y))
    have h2 := inf_le_kernel_average (L w) (fun y ↦ hL w y) (hLs w)
      (fun y ↦ (f - featureCombo g lam) (w, y))
    linarith
  have hfeat : (∑ i, lam i * ∑ w, μ w * ∑ y, K w y * g i (w, y)) -
      ∑ i, lam i * ∑ w, μ w * ∑ y, L w y * g i (w, y) ≤ 2 * ε * ∑ i, |lam i| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hb := hmom i
    have habs : |lam i * ((∑ w, μ w * ∑ y, K w y * g i (w, y)) -
        ∑ w, μ w * ∑ y, L w y * g i (w, y))| ≤ |lam i| * (2 * ε) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have hle := (abs_le.mp habs).2
    calc lam i * (∑ w, μ w * ∑ y, K w y * g i (w, y)) -
          lam i * ∑ w, μ w * ∑ y, L w y * g i (w, y)
        = lam i * ((∑ w, μ w * ∑ y, K w y * g i (w, y)) -
            ∑ w, μ w * ∑ y, L w y * g i (w, y)) := by ring
      _ ≤ |lam i| * (2 * ε) := hle
      _ = 2 * ε * |lam i| := by ring
  linarith

/-- The explicitly convex open neighbourhood separating the report from the feature
span: observables within total oscillation budget `r` of a feature combination, with the
noise allowance charged at `2ε` per unit of multiplier. -/
def oscNbhd (μ : W → ℝ) (g : F → W × Y → ℝ) (ε r : ℝ) : Set (W × Y → ℝ) :=
  {h | ∃ lam : F → ℝ, ∃ u l : W → ℝ,
    (∀ w y, l w ≤ h (w, y) - featureCombo g lam (w, y)) ∧
    (∀ w y, h (w, y) - featureCombo g lam (w, y) ≤ u w) ∧
    (∑ w, μ w * (u w - l w)) + 2 * ε * ∑ i, |lam i| < r}

/-- The oscillation neighbourhood is convex. -/
theorem convex_oscNbhd (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (g : F → W × Y → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (r : ℝ) : Convex ℝ (oscNbhd μ g ε r) := by
  rintro h₁ ⟨lam₁, u₁, l₁, hl₁, hu₁, hs₁⟩ h₂ ⟨lam₂, u₂, l₂, hl₂, hu₂, hs₂⟩ a b ha hb hab
  refine ⟨fun i ↦ a * lam₁ i + b * lam₂ i, fun w ↦ a * u₁ w + b * u₂ w,
    fun w ↦ a * l₁ w + b * l₂ w, ?_, ?_, ?_⟩
  · intro w y
    have hc : featureCombo g (fun i ↦ a * lam₁ i + b * lam₂ i) (w, y) =
        a * featureCombo g lam₁ (w, y) + b * featureCombo g lam₂ (w, y) := by
      simp only [featureCombo, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hc]
    have e1 := mul_le_mul_of_nonneg_left (hl₁ w y) ha
    have e2 := mul_le_mul_of_nonneg_left (hl₂ w y) hb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [e1, e2]
  · intro w y
    have hc : featureCombo g (fun i ↦ a * lam₁ i + b * lam₂ i) (w, y) =
        a * featureCombo g lam₁ (w, y) + b * featureCombo g lam₂ (w, y) := by
      simp only [featureCombo, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hc]
    have e1 := mul_le_mul_of_nonneg_left (hu₁ w y) ha
    have e2 := mul_le_mul_of_nonneg_left (hu₂ w y) hb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [e1, e2]
  · have hnorm : (∑ i, |a * lam₁ i + b * lam₂ i|) ≤
        a * (∑ i, |lam₁ i|) + b * ∑ i, |lam₂ i| := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have htri : |a * lam₁ i + b * lam₂ i| ≤ |a * lam₁ i| + |b * lam₂ i| :=
        abs_le.mpr ⟨by linarith [neg_abs_le (a * lam₁ i), neg_abs_le (b * lam₂ i)],
          by linarith [le_abs_self (a * lam₁ i), le_abs_self (b * lam₂ i)]⟩
      calc |a * lam₁ i + b * lam₂ i| ≤ |a * lam₁ i| + |b * lam₂ i| := htri
        _ = a * |lam₁ i| + b * |lam₂ i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hsum : (∑ w, μ w * (a * u₁ w + b * u₂ w - (a * l₁ w + b * l₂ w))) =
        a * (∑ w, μ w * (u₁ w - l₁ w)) + b * ∑ w, μ w * (u₂ w - l₂ w) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    rw [hsum]
    have hεn : 0 ≤ 2 * ε := by linarith
    have hp3 : 2 * ε * (∑ i, |a * lam₁ i + b * lam₂ i|) ≤
        2 * ε * (a * (∑ i, |lam₁ i|) + b * ∑ i, |lam₂ i|) :=
      mul_le_mul_of_nonneg_left hnorm hεn
    have hmax : max ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|)
        ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) < r := max_lt hs₁ hs₂
    have hq1 : a * ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|) ≤
        a * max ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|)
          ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have hq2 : b * ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) ≤
        b * max ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|)
          ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hb
    have hqsum : a * max ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|)
          ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) +
        b * max ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|)
          ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) =
        max ((∑ w, μ w * (u₁ w - l₁ w)) + 2 * ε * ∑ i, |lam₁ i|)
          ((∑ w, μ w * (u₂ w - l₂ w)) + 2 * ε * ∑ i, |lam₂ i|) := by
      rw [← add_mul, hab, one_mul]
    nlinarith [hp3, hq1, hq2, hqsum, hmax]

/-- Shifting the bracketing functions by a small amount keeps an observable inside the
oscillation neighbourhood. -/
theorem oscNbhd_mem_of_close (μ : W → ℝ) (g : F → W × Y → ℝ) (ε r : ℝ)
    (h h' : W × Y → ℝ) (lam : F → ℝ) (u l : W → ℝ) (ρ : ℝ)
    (hl : ∀ w y, l w ≤ h (w, y) - featureCombo g lam (w, y))
    (hu : ∀ w y, h (w, y) - featureCombo g lam (w, y) ≤ u w)
    (hbound : ∀ z, |h' z - h z| ≤ ρ)
    (hsum : (∑ w, μ w * (u w - l w)) + 2 * ρ * (∑ w, μ w) +
      2 * ε * ∑ i, |lam i| < r) :
    h' ∈ oscNbhd μ g ε r := by
  refine ⟨lam, fun w ↦ u w + ρ, fun w ↦ l w - ρ, ?_, ?_, ?_⟩
  · intro w y
    have hz := (abs_le.mp (hbound (w, y))).1
    linarith [hl w y]
  · intro w y
    have hz := (abs_le.mp (hbound (w, y))).2
    linarith [hu w y]
  · have hexp : (∑ w, μ w * (u w + ρ - (l w - ρ))) =
        (∑ w, μ w * (u w - l w)) + 2 * ρ * ∑ w, μ w := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    rw [hexp]
    linarith

/-- A positive slack admits a positive radius whose doubled weight fits inside it. -/
theorem exists_radius (s S : ℝ) (hs : 0 < s) (hS : 0 ≤ S) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ * S < s := by
  refine ⟨s / (2 * S + 2), by positivity, ?_⟩
  have hD : (0 : ℝ) < 2 * S + 2 := by linarith
  have h1 : s / (2 * S + 2) * (2 * S) < s / (2 * S + 2) * (2 * S + 2) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  rw [div_mul_cancel₀ _ hD.ne'] at h1
  linarith

/-- The oscillation neighbourhood is open. -/
theorem isOpen_oscNbhd (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (g : F → W × Y → ℝ)
    (ε r : ℝ) : IsOpen (oscNbhd μ g ε r) := by
  rw [Metric.isOpen_iff]
  rintro h ⟨lam, u, l, hl, hu, hs⟩
  have hSnn : (0 : ℝ) ≤ ∑ w, μ w := Finset.sum_nonneg fun w _ ↦ hμ w
  obtain ⟨ρ, hρpos, hρlt⟩ := exists_radius
    (r - ((∑ w, μ w * (u w - l w)) + 2 * ε * ∑ i, |lam i|)) (∑ w, μ w)
    (by linarith) hSnn
  refine ⟨ρ, hρpos, ?_⟩
  intro h' hh'
  have hd : ‖h' - h‖ < ρ := by
    have hdd := Metric.mem_ball.mp hh'
    rwa [dist_eq_norm] at hdd
  refine oscNbhd_mem_of_close μ g ε r h h' lam u l ρ hl hu (fun z ↦ ?_) (by linarith)
  have hn := norm_le_pi_norm (h' - h) z
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hn
  linarith

/-- Feasibility of the dual objective rules out membership of the report in the
oscillation neighbourhood. -/
theorem notMem_oscNbhd (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (g : F → W × Y → ℝ)
    (f : W × Y → ℝ) (ε r : ℝ)
    (hr : ∀ lam : F → ℝ,
      r ≤ oscTotal μ (f - featureCombo g lam) + 2 * ε * ∑ i, |lam i|) :
    f ∉ oscNbhd μ g ε r := by
  rintro ⟨lam, u, l, hl, hu, hs⟩
  have hbound : oscTotal μ (f - featureCombo g lam) ≤ ∑ w, μ w * (u w - l w) := by
    rw [oscTotal]
    refine Finset.sum_le_sum fun w _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (hμ w)
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun y ↦ (f - featureCombo g lam) (w, y)) ≤ u w :=
      Finset.sup'_le _ _ fun y _ ↦ by simpa [Pi.sub_apply] using hu w y
    have hinf : l w ≤ Finset.univ.inf' Finset.univ_nonempty
        (fun y ↦ (f - featureCombo g lam) (w, y)) :=
      Finset.le_inf' _ _ fun y _ ↦ by simpa [Pi.sub_apply] using hl w y
    linarith
  linarith [hr lam]

end

end Descent.Portability.ConditionalOscillationDuality
