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
`jointLaw_expectation`, which evaluates `Portability.weightedExp` on the joint mass. The
extremal kernels and the shrinking radius are named definitions, not existentials.

## Empirical status

None. The bodies here are algebra: a report diameter over a kernel class and a weighted
oscillation are claims about a model, and what carries an empirical status is a named
quantity in a subsystem module asserting that this algebra computes something measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalOscillationDuality

open Foundations

noncomputable section

variable {W Y F : Type*} [Fintype W] [Fintype Y] [Fintype F]
variable [DecidableEq W] [DecidableEq Y] [DecidableEq F]
variable [Nonempty Y]

/-- The `μ`-weighted total conditional oscillation of an observable. -/
def oscTotal (μ : W → ℝ) (h : W × Y → ℝ) : ℝ :=
  ∑ w, μ w * (Finset.univ.sup' Finset.univ_nonempty (fun y ↦ h (w, y)) -
    Finset.univ.inf' Finset.univ_nonempty (fun y ↦ h (w, y)))

/-- The supplied feature combination `λᵀg`. -/
def featureCombo (g : F → W × Y → ℝ) (lam : F → ℝ) : W × Y → ℝ :=
  fun z ↦ ∑ i, lam i * g i z

/-- A convex combination of multiplier vectors combines the feature combinations the
same way. -/
theorem featureCombo_combo (g : F → W × Y → ℝ) (lam₁ lam₂ : F → ℝ) (a b : ℝ)
    (z : W × Y) :
    featureCombo g (fun i ↦ a * lam₁ i + b * lam₂ i) z =
      a * featureCombo g lam₁ z + b * featureCombo g lam₂ z := by
  simp only [featureCombo, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

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
    rw [featureCombo_combo g lam₁ lam₂ a b (w, y)]
    have e1 := mul_le_mul_of_nonneg_left (hl₁ w y) ha
    have e2 := mul_le_mul_of_nonneg_left (hl₂ w y) hb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [e1, e2]
  · intro w y
    rw [featureCombo_combo g lam₁ lam₂ a b (w, y)]
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

/-- The radius whose doubled weighted total fits inside a given slack. -/
def shrinkRadius (s S : ℝ) : ℝ := s / (2 * S + 2)

/-- The shrinking radius is positive. -/
theorem shrinkRadius_pos (s S : ℝ) (hs : 0 < s) (hS : 0 ≤ S) : 0 < shrinkRadius s S := by
  unfold shrinkRadius
  positivity

/-- Twice the shrinking radius, weighted, stays inside the slack. -/
theorem shrinkRadius_spec (s S : ℝ) (hs : 0 < s) (hS : 0 ≤ S) :
    2 * shrinkRadius s S * S < s := by
  have hD : (0 : ℝ) < 2 * S + 2 := by linarith
  have h1 : s / (2 * S + 2) * (2 * S) < s / (2 * S + 2) * (2 * S + 2) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  rw [div_mul_cancel₀ _ hD.ne'] at h1
  unfold shrinkRadius
  linarith

/-- A positive slack admits a positive radius whose doubled weight fits inside it. -/
theorem exists_radius (s S : ℝ) (hs : 0 < s) (hS : 0 ≤ S) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ * S < s :=
  ⟨shrinkRadius s S, shrinkRadius_pos s S hs hS, shrinkRadius_spec s S hs hS⟩

/-- The oscillation neighbourhood is open. -/
theorem isOpen_oscNbhd (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (g : F → W × Y → ℝ)
    (ε r : ℝ) : IsOpen (oscNbhd μ g ε r) := by
  rw [Metric.isOpen_iff]
  rintro h ⟨lam, u, l, hl, hu, hs⟩
  have hSnn : (0 : ℝ) ≤ ∑ w, μ w := Finset.sum_nonneg fun w _ ↦ hμ w
  have hslack : 0 < r - ((∑ w, μ w * (u w - l w)) + 2 * ε * ∑ i, |lam i|) := by linarith
  have hρpos := shrinkRadius_pos
    (r - ((∑ w, μ w * (u w - l w)) + 2 * ε * ∑ i, |lam i|)) (∑ w, μ w) hslack hSnn
  have hρlt := shrinkRadius_spec
    (r - ((∑ w, μ w * (u w - l w)) + 2 * ε * ∑ i, |lam i|)) (∑ w, μ w) hslack hSnn
  set ρ := shrinkRadius
    (r - ((∑ w, μ w * (u w - l w)) + 2 * ε * ∑ i, |lam i|)) (∑ w, μ w) with hρdef
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

/-- The row-indicator pairing with a signed weight. -/
theorem sum_row_indicator (σ : W × Y → ℝ) (w : W) (t : ℝ) :
    ∑ z : W × Y, (if z.1 = w then t else 0) * σ z = t * ∑ y, σ (w, y) := by
  rw [Fintype.sum_prod_type]
  have h : ∀ w' : W, (∑ y, (if ((w', y) : W × Y).1 = w then t else 0) * σ (w', y)) =
      if w' = w then t * ∑ y, σ (w, y) else 0 := by
    intro w'
    by_cases hw : w' = w
    · subst hw; simp [Finset.mul_sum]
    · simp [hw]
  rw [Finset.sum_congr rfl fun w' _ ↦ h w', Finset.sum_ite_eq' Finset.univ w]
  simp

/-- The positive-part bump pairing with a signed weight. -/
theorem sum_pos_bump (σ : W × Y → ℝ) (w : W) (a : ℝ) :
    ∑ z : W × Y, (if z.1 = w then a * (if 0 ≤ σ z then 1 else 0) else 0) * σ z =
      a * ∑ y, (|σ (w, y)| + σ (w, y)) / 2 := by
  have hterm : ∀ x : ℝ, (if 0 ≤ x then (1 : ℝ) else 0) * x = (|x| + x) / 2 := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, one_mul, abs_of_nonneg hx]; ring
    · rw [if_neg hx, zero_mul, abs_of_neg (not_le.mp hx)]; ring
  rw [Fintype.sum_prod_type]
  have h : ∀ w' : W, (∑ y, (if ((w', y) : W × Y).1 = w then
      a * (if 0 ≤ σ (w', y) then 1 else 0) else 0) * σ (w', y)) =
      if w' = w then a * ∑ y, (|σ (w, y)| + σ (w, y)) / 2 else 0 := by
    intro w'
    by_cases hw : w' = w
    · rw [if_pos hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [if_pos (show ((w', y) : W × Y).1 = w from hw), mul_assoc, hterm, hw]
    · simp [hw]
  rw [Finset.sum_congr rfl fun w' _ ↦ h w', Finset.sum_ite_eq' Finset.univ w]
  simp

/-- The single-feature pairing with a signed weight. -/
theorem sum_feature_combo (σ : W × Y → ℝ) (g : F → W × Y → ℝ) (i : F) (t : ℝ) :
    ∑ z : W × Y, featureCombo g (fun j ↦ if j = i then t else 0) z * σ z =
      t * ∑ z : W × Y, g i z * σ z := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hc : featureCombo g (fun j ↦ if j = i then t else 0) z = t * g i z := by
    simp only [featureCombo]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro b _ hb
      simp [hb]
  rw [hc]
  ring

/-- The total conditional oscillation is nonnegative. -/
theorem oscTotal_nonneg (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (h : W × Y → ℝ) :
    0 ≤ oscTotal μ h := by
  refine Finset.sum_nonneg fun w _ ↦ mul_nonneg (hμ w) ?_
  have h1 := Finset.inf'_le (fun y ↦ h (w, y)) (Finset.mem_univ (Classical.arbitrary Y))
  have h2 := Finset.le_sup' (fun y ↦ h (w, y)) (Finset.mem_univ (Classical.arbitrary Y))
  linarith

/-- A kernel pair whose weighted difference is a prescribed signed weight reproduces that
weight's pairing with every observable. -/
theorem kernel_pair_difference (μ : W → ℝ) (K L : W → Y → ℝ) (τ : W × Y → ℝ)
    (hdiff : ∀ w y, μ w * (K w y - L w y) = τ (w, y)) (G : W × Y → ℝ) :
    (∑ w, μ w * ∑ y, K w y * G (w, y)) - ∑ w, μ w * ∑ y, L w y * G (w, y) =
      ∑ z : W × Y, τ z * G z := by
  rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← sub_mul, ← mul_assoc, hdiff w y]

/-- The negative part of a row with vanishing total equals its positive part. -/
theorem negPart_sum (τ : W × Y → ℝ) (w : W) (hrow : ∑ y, τ (w, y) = 0) :
    (∑ y, (|τ (w, y)| - τ (w, y)) / 2) = ∑ y, (|τ (w, y)| + τ (w, y)) / 2 := by
  have hsplit : ∀ y : Y, (|τ (w, y)| - τ (w, y)) / 2 =
      (|τ (w, y)| + τ (w, y)) / 2 - τ (w, y) := by intro y; ring
  rw [Finset.sum_congr rfl fun y _ ↦ hsplit y, Finset.sum_sub_distrib, hrow, sub_zero]

/-- A row topped up on one outcome to its prescribed mass is nonnegative. -/
theorem topUp_nonneg (μ : W → ℝ) (hμ : ∀ w, 0 < μ w) (y₀ : Y) (w : W) (y : Y)
    (aw pv : ℝ) (hpv : 0 ≤ pv) (haw : aw ≤ μ w) :
    0 ≤ (pv + (μ w - aw) * (if y = y₀ then 1 else 0)) / μ w := by
  have h3 : (0 : ℝ) ≤ (if y = y₀ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  exact div_nonneg (by nlinarith) (hμ w).le

/-- A row topped up on one outcome to its prescribed mass is a probability row. -/
theorem topUp_sum (μ : W → ℝ) (hμ : ∀ w, 0 < μ w) (y₀ : Y) (w : W) (aw : ℝ)
    (p : Y → ℝ) (hp : ∑ y, p y = aw) :
    (∑ y, (p y + (μ w - aw) * (if y = y₀ then 1 else 0)) / μ w) = 1 := by
  have hμne : μ w ≠ 0 := (hμ w).ne'
  have hind : (∑ y, (if y = y₀ then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ y₀]
    simp
  have hstep : (∑ y, (p y + (μ w - aw) * (if y = y₀ then 1 else 0))) = μ w := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hind, mul_one, hp]
    ring
  calc (∑ y, (p y + (μ w - aw) * (if y = y₀ then 1 else 0)) / μ w)
      = (∑ y, (p y + (μ w - aw) * (if y = y₀ then 1 else 0))) / μ w := by
        rw [Finset.sum_div]
    _ = 1 := by rw [hstep, div_self hμne]

/-- **The extremal conditional kernels.** The sign parts of a signed weight, topped up on
a fixed outcome so that each row carries the prescribed pre-outcome mass. -/
def extremalKernel (μ : W → ℝ) (τ : W × Y → ℝ) (y₀ : Y) (s : Bool) : W → Y → ℝ :=
  fun w y ↦ ((|τ (w, y)| + (if s then -τ (w, y) else τ (w, y))) / 2 +
    (μ w - ∑ y', (|τ (w, y')| + τ (w, y')) / 2) * (if y = y₀ then 1 else 0)) / μ w

/-- The extremal kernels are nonnegative. -/
theorem extremalKernel_nonneg (μ : W → ℝ) (hμ : ∀ w, 0 < μ w) (τ : W × Y → ℝ) (y₀ : Y)
    (s : Bool) (hτpos : ∀ w, (∑ y, (|τ (w, y)| + τ (w, y)) / 2) ≤ μ w) (w : W) (y : Y) :
    0 ≤ extremalKernel μ τ y₀ s w y := by
  cases s
  · exact topUp_nonneg μ hμ y₀ w y (∑ y', (|τ (w, y')| + τ (w, y')) / 2)
      ((|τ (w, y)| + τ (w, y)) / 2) (by linarith [neg_abs_le (τ (w, y))]) (hτpos w)
  · exact topUp_nonneg μ hμ y₀ w y (∑ y', (|τ (w, y')| + τ (w, y')) / 2)
      ((|τ (w, y)| - τ (w, y)) / 2) (by linarith [le_abs_self (τ (w, y))]) (hτpos w)

/-- The extremal kernels are probability kernels. -/
theorem extremalKernel_sum (μ : W → ℝ) (hμ : ∀ w, 0 < μ w) (τ : W × Y → ℝ) (y₀ : Y)
    (s : Bool) (hτrow : ∀ w, ∑ y, τ (w, y) = 0) (w : W) :
    ∑ y, extremalKernel μ τ y₀ s w y = 1 := by
  cases s
  · have hK : ∀ y, extremalKernel μ τ y₀ false w y =
        ((|τ (w, y)| + τ (w, y)) / 2 +
          (μ w - ∑ y', (|τ (w, y')| + τ (w, y')) / 2) *
            (if y = y₀ then 1 else 0)) / μ w := fun _ ↦ rfl
    simp only [hK]
    exact topUp_sum μ hμ y₀ w _ (fun y ↦ (|τ (w, y)| + τ (w, y)) / 2) rfl
  · have hK : ∀ y, extremalKernel μ τ y₀ true w y =
        ((|τ (w, y)| - τ (w, y)) / 2 +
          (μ w - ∑ y', (|τ (w, y')| + τ (w, y')) / 2) *
            (if y = y₀ then 1 else 0)) / μ w := fun _ ↦ rfl
    simp only [hK]
    exact topUp_sum μ hμ y₀ w _ (fun y ↦ (|τ (w, y)| - τ (w, y)) / 2)
      (negPart_sum τ w (hτrow w))

/-- The weighted difference of the extremal kernels is the signed weight. -/
theorem extremalKernel_diff (μ : W → ℝ) (hμ : ∀ w, 0 < μ w) (τ : W × Y → ℝ) (y₀ : Y)
    (w : W) (y : Y) :
    μ w * (extremalKernel μ τ y₀ false w y - extremalKernel μ τ y₀ true w y) =
      τ (w, y) := by
  have hμne : μ w ≠ 0 := (hμ w).ne'
  show μ w * (((|τ (w, y)| + τ (w, y)) / 2 +
      (μ w - ∑ y', (|τ (w, y')| + τ (w, y')) / 2) * (if y = y₀ then 1 else 0)) / μ w -
    ((|τ (w, y)| - τ (w, y)) / 2 +
      (μ w - ∑ y', (|τ (w, y')| + τ (w, y')) / 2) * (if y = y₀ then 1 else 0)) / μ w) = _
  field_simp
  ring

/-- **PL Theorem 8.2, lower bound.** If the dual objective is bounded below by `r`, then
every `c` in `(0, r)` is attained by an explicit feasible pair of conditional kernels,
built from the separating functional. -/
theorem exists_kernelGap_ge (μ : W → ℝ) (hμ : ∀ w, 0 < μ w) (g : F → W × Y → ℝ)
    (f : W × Y → ℝ) (ε : ℝ) (hε : 0 ≤ ε) {c r : ℝ} (hc : 0 < c) (hcr : c < r)
    (hr : ∀ lam : F → ℝ,
      r ≤ oscTotal μ (f - featureCombo g lam) + 2 * ε * ∑ i, |lam i|) :
    ∃ t ∈ kernelGaps μ g f ε, c ≤ t := by
  classical
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hμ0 : ∀ w, 0 ≤ μ w := fun w ↦ (hμ w).le
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point
    (convex_oscNbhd μ hμ0 g ε hε r) (isOpen_oscNbhd μ hμ0 g ε r)
    (notMem_oscNbhd μ hμ0 g f ε r hr)
  have hcombo0 : ∀ z : W × Y, featureCombo g (fun _ : F ↦ (0 : ℝ)) z = 0 := by
    intro z; simp [featureCombo]
  obtain ⟨σ, hφeval⟩ : ∃ σ : W × Y → ℝ, ∀ h : W × Y → ℝ, φ h = ∑ z, h z * σ z :=
    ⟨fun z ↦ φ (ApproximationDuality.stdBasis z),
      fun h ↦ ApproximationDuality.eval_as_sum φ h⟩
  have hzero : (0 : W × Y → ℝ) ∈ oscNbhd μ g ε r := by
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_, ?_⟩
    · intro w y; simp [hcombo0]
    · intro w y; simp [hcombo0]
    · simp
      linarith
  have hpos : 0 < φ f := by simpa using hφ 0 hzero
  have hrow : ∀ w, ∑ y, σ (w, y) = 0 := by
    intro w
    have hmem : ∀ t : ℝ, (fun z : W × Y ↦ if z.1 = w then t else 0) ∈ oscNbhd μ g ε r := by
      intro t
      refine ⟨fun _ ↦ 0, fun w' ↦ if w' = w then t else 0,
        fun w' ↦ if w' = w then t else 0, ?_, ?_, ?_⟩
      · intro w' y; simp [hcombo0]
      · intro w' y; simp [hcombo0]
      · simp
        linarith
    have hall : ∀ t : ℝ, t * (∑ y, σ (w, y)) < φ f := by
      intro t
      have h1 := hφ _ (hmem t)
      rw [hφeval, sum_row_indicator σ w t] at h1
      exact h1
    by_contra hne
    have h := hall ((φ f + 1) / (∑ y, σ (w, y)))
    rw [div_mul_cancel₀ _ hne] at h
    linarith
  have hfeat : ∀ i : F, |∑ z, g i z * σ z| ≤ 2 * ε * (φ f / c) := by
    intro i
    have hmem : ∀ t : ℝ, 2 * ε * |t| < r →
        featureCombo g (fun j ↦ if j = i then t else 0) ∈ oscNbhd μ g ε r := by
      intro t ht
      refine ⟨fun j ↦ if j = i then t else 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_, ?_⟩
      · intro w y; simp
      · intro w y; simp
      · have hnorm : (∑ j, |if j = i then t else 0|) = |t| := by
          rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
          · simp
          · intro b _ hb; simp [hb]
        rw [hnorm]
        simp
        linarith
    have hall : ∀ t : ℝ, 2 * ε * |t| < r → t * (∑ z, g i z * σ z) < φ f := by
      intro t ht
      have h1 := hφ _ (hmem t ht)
      rw [hφeval, sum_feature_combo σ g i t] at h1
      exact h1
    by_contra hcon
    push_neg at hcon
    have hdiv : (0 : ℝ) ≤ φ f / c := (div_pos hpos hc).le
    have hnn : (0 : ℝ) ≤ 2 * ε * (φ f / c) := by nlinarith
    have hAabs : 0 < |∑ z, g i z * σ z| := lt_of_le_of_lt hnn hcon
    have hAne : (∑ z, g i z * σ z) ≠ 0 := by
      intro h0
      rw [h0] at hAabs
      simp at hAabs
    have hta : (φ f / (∑ z, g i z * σ z)) * (∑ z, g i z * σ z) = φ f :=
      div_mul_cancel₀ _ hAne
    have htbound : 2 * ε * |φ f / (∑ z, g i z * σ z)| < r := by
      have habs : |φ f / (∑ z, g i z * σ z)| = φ f / |∑ z, g i z * σ z| := by
        rw [abs_div, abs_of_pos hpos]
      rcases eq_or_lt_of_le hε with h0 | h0
      · rw [← h0]
        simp
        linarith
      · rw [habs]
        have hmul : 2 * ε * φ f < c * |∑ z, g i z * σ z| := by
          have h2 := mul_lt_mul_of_pos_right hcon hc
          rw [mul_assoc, div_mul_cancel₀ _ hc.ne'] at h2
          linarith
        have hkey : 2 * ε * (φ f / |∑ z, g i z * σ z|) * |∑ z, g i z * σ z| <
            c * |∑ z, g i z * σ z| := by
          rw [mul_assoc, div_mul_cancel₀ _ hAabs.ne']
          exact hmul
        have hlt := lt_of_mul_lt_mul_right hkey hAabs.le
        linarith
    have hfin := hall (φ f / (∑ z, g i z * σ z)) htbound
    rw [hta] at hfin
    linarith
  have hpospart : ∀ w, (∑ y, (|σ (w, y)| + σ (w, y)) / 2) ≤ μ w * (φ f / c) := by
    intro w
    have hμne : μ w ≠ 0 := (hμ w).ne'
    have hcμ : 0 < c / μ w := div_pos hc (hμ w)
    have hmem : (fun z : W × Y ↦ if z.1 = w then (c / μ w) * (if 0 ≤ σ z then 1 else 0)
        else 0) ∈ oscNbhd μ g ε r := by
      refine ⟨fun _ ↦ 0, fun w' ↦ if w' = w then c / μ w else 0, fun _ ↦ 0, ?_, ?_, ?_⟩
      · intro w' y
        simp only [hcombo0, sub_zero]
        split_ifs <;> simp <;> linarith
      · intro w' y
        simp only [hcombo0, sub_zero]
        by_cases hw : w' = w
        · subst hw
          simp only [if_pos rfl]
          split_ifs <;> simp <;> linarith
        · simp [hw]
      · have hs : (∑ w', μ w' * ((if w' = w then c / μ w else 0) - 0)) = c := by
          have hterm : ∀ w' : W, μ w' * ((if w' = w then c / μ w else 0) - 0) =
              if w' = w then c else 0 := by
            intro w'
            by_cases hw : w' = w
            · subst hw; simp; field_simp
            · simp [hw]
          rw [Finset.sum_congr rfl fun w' _ ↦ hterm w',
            Finset.sum_ite_eq' Finset.univ w]
          simp
        rw [hs]
        simp
        linarith
    have h1 := hφ _ hmem
    rw [hφeval, sum_pos_bump σ w (c / μ w)] at h1
    have hmul := mul_lt_mul_of_pos_right h1 (div_pos (hμ w) hc)
    have hid : c / μ w * (∑ y, (|σ (w, y)| + σ (w, y)) / 2) * (μ w / c) =
        ∑ y, (|σ (w, y)| + σ (w, y)) / 2 := by field_simp
    rw [hid] at hmul
    have hcomm : φ f * (μ w / c) = μ w * (φ f / c) := by ring
    linarith [hmul, hcomm]
  have hKpos : 0 < φ f / c := div_pos hpos hc
  obtain ⟨τ, hτrow, hτpos, hτfeat, hτf⟩ :
      ∃ τ : W × Y → ℝ, (∀ w, ∑ y, τ (w, y) = 0) ∧
        (∀ w, (∑ y, (|τ (w, y)| + τ (w, y)) / 2) ≤ μ w) ∧
        (∀ i, |∑ z, g i z * τ z| ≤ 2 * ε) ∧ (∑ z, f z * τ z) = c := by
    refine ⟨fun z ↦ σ z / (φ f / c), fun w ↦ ?_, fun w ↦ ?_, fun i ↦ ?_, ?_⟩
    · have hid : (∑ y, σ (w, y) / (φ f / c)) = (∑ y, σ (w, y)) / (φ f / c) := by
        rw [Finset.sum_div]
      rw [hid, hrow w, zero_div]
    · have hKne : (φ f / c) ≠ 0 := hKpos.ne'
      have hid : (∑ y, (|σ (w, y) / (φ f / c)| + σ (w, y) / (φ f / c)) / 2) =
          (∑ y, (|σ (w, y)| + σ (w, y)) / 2) / (φ f / c) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [abs_div, abs_of_pos hKpos]
        field_simp
      rw [hid, div_le_iff₀ hKpos]
      have h := hpospart w
      linarith
    · have hid : (∑ z, g i z * (σ z / (φ f / c))) = (∑ z, g i z * σ z) / (φ f / c) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun z _ ↦ (mul_div_assoc _ _ _).symm
      rw [hid, abs_div, abs_of_pos hKpos, div_le_iff₀ hKpos]
      have h := hfeat i
      linarith
    · have hfne : φ f ≠ 0 := hpos.ne'
      have hcne : c ≠ 0 := hc.ne'
      have hid : (∑ z, f z * (σ z / (φ f / c))) = (∑ z, f z * σ z) / (φ f / c) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun z _ ↦ (mul_div_assoc _ _ _).symm
      rw [hid, ← hφeval f]
      field_simp
  refine ⟨∑ z, τ z * f z,
    ⟨extremalKernel μ τ y₀ false, extremalKernel μ τ y₀ true,
      fun w y ↦ extremalKernel_nonneg μ hμ τ y₀ false hτpos w y,
      fun w y ↦ extremalKernel_nonneg μ hμ τ y₀ true hτpos w y,
      fun w ↦ extremalKernel_sum μ hμ τ y₀ false hτrow w,
      fun w ↦ extremalKernel_sum μ hμ τ y₀ true hτrow w, ?_, ?_⟩, ?_⟩
  · intro i
    rw [kernel_pair_difference μ _ _ τ (extremalKernel_diff μ hμ τ y₀) (g i)]
    have hcomm : (∑ z, τ z * g i z) = ∑ z, g i z * τ z :=
      Finset.sum_congr rfl fun z _ ↦ by ring
    rw [hcomm]
    exact hτfeat i
  · exact (kernel_pair_difference μ _ _ τ (extremalKernel_diff μ hμ τ y₀) f).symm
  · have hcomm : (∑ z, τ z * f z) = ∑ z, f z * τ z :=
      Finset.sum_congr rfl fun z _ ↦ by ring
    rw [hcomm, hτf]

/-- **PL Theorem 8.2 and Corollary 8.3.** The report diameter over conditional kernel
pairs whose supplied feature expectations agree coordinatewise to within `2ε` is exactly
the infimum of the dual objective. With `ε = 0` this is equation (8.2); with `ε > 0`
it is equation (8.4). -/
theorem conditional_oscillation_duality (μ : W → ℝ) (hμ : ∀ w, 0 < μ w)
    (g : F → W × Y → ℝ) (f : W × Y → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    IsLUB (kernelGaps μ g f ε) (sInf (dualValues μ g f ε)) := by
  classical
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hμ0 : ∀ w, 0 ≤ μ w := fun w ↦ (hμ w).le
  have hne : (dualValues μ g f ε).Nonempty := ⟨_, ⟨fun _ ↦ 0, rfl⟩⟩
  have hbdd : BddBelow (dualValues μ g f ε) := by
    refine ⟨0, ?_⟩
    rintro s ⟨lam, rfl⟩
    have h1 := oscTotal_nonneg μ hμ0 (f - featureCombo g lam)
    have hs : (0 : ℝ) ≤ ∑ i, |lam i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    nlinarith
  constructor
  · intro t ht
    refine le_csInf hne ?_
    rintro s ⟨lam, rfl⟩
    exact kernelGap_le_dual μ hμ0 g f ε ht lam
  · intro ub hub
    have hzeroGap : (0 : ℝ) ∈ kernelGaps μ g f ε := by
      refine ⟨fun _ y ↦ if y = y₀ then 1 else 0, fun _ y ↦ if y = y₀ then 1 else 0,
        fun w y ↦ by by_cases h : y = y₀ <;> simp [h],
        fun w y ↦ by by_cases h : y = y₀ <;> simp [h],
        fun w ↦ by rw [Finset.sum_ite_eq' Finset.univ y₀]; simp,
        fun w ↦ by rw [Finset.sum_ite_eq' Finset.univ y₀]; simp, fun i ↦ ?_, by ring⟩
      simp
      linarith
    have hub0 : 0 ≤ ub := hub hzeroGap
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    have hcpos : 0 < c := lt_of_le_of_lt hub0 hc1
    have hr : ∀ lam : F → ℝ, sInf (dualValues μ g f ε) ≤
        oscTotal μ (f - featureCombo g lam) + 2 * ε * ∑ i, |lam i| :=
      fun lam ↦ csInf_le hbdd ⟨lam, rfl⟩
    obtain ⟨t, ht, hge⟩ := exists_kernelGap_ge μ hμ g f ε hε hcpos hc2 hr
    have hle := hub ht
    linarith

/-- The midpoint of the conditional range, the constant in PL equation (8.3). -/
def oscMidpoint (μ : W → ℝ) (h : W × Y → ℝ) : ℝ :=
  ∑ w, μ w * (Finset.univ.sup' Finset.univ_nonempty (fun y ↦ h (w, y)) +
    Finset.univ.inf' Finset.univ_nonempty (fun y ↦ h (w, y))) / 2

/-- The report expectation splits into the residual expectation and the supplied feature
moments. -/
theorem kernel_report_split (μ : W → ℝ) (g : F → W × Y → ℝ) (f : W × Y → ℝ)
    (lam : F → ℝ) (M : W → Y → ℝ) :
    (∑ w, μ w * ∑ y, M w y * f (w, y)) =
      (∑ w, μ w * ∑ y, M w y * (f - featureCombo g lam) (w, y)) +
        ∑ i, lam i * ∑ w, μ w * ∑ y, M w y * g i (w, y) := by
  rw [← combo_expectation μ g lam M, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg (fun s ↦ μ w * s) (Finset.sum_congr rfl fun y _ ↦ ?_)
  simp [Pi.sub_apply]
  ring

/-- **PL equation (8.3).** The affine rule built from a multiplier vector has worst-case
absolute error at most half the dual objective at that vector, uniformly over conditional
kernels. -/
theorem oscillation_rule_error (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (g : F → W × Y → ℝ)
    (f : W × Y → ℝ) (lam : F → ℝ) (K : W → Y → ℝ) (hK : ∀ w y, 0 ≤ K w y)
    (hKs : ∀ w, ∑ y, K w y = 1) :
    |(∑ w, μ w * ∑ y, K w y * f (w, y)) -
        ((∑ i, lam i * ∑ w, μ w * ∑ y, K w y * g i (w, y)) +
          oscMidpoint μ (f - featureCombo g lam))| ≤
      oscTotal μ (f - featureCombo g lam) / 2 := by
  have hsup : (∑ w, μ w * ∑ y, K w y * (f - featureCombo g lam) (w, y)) ≤
      ∑ w, μ w * Finset.univ.sup' Finset.univ_nonempty
        (fun y ↦ (f - featureCombo g lam) (w, y)) :=
    Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left
      (kernel_average_le_sup (K w) (fun y ↦ hK w y) (hKs w) _) (hμ w)
  have hinf : (∑ w, μ w * Finset.univ.inf' Finset.univ_nonempty
        (fun y ↦ (f - featureCombo g lam) (w, y))) ≤
      ∑ w, μ w * ∑ y, K w y * (f - featureCombo g lam) (w, y) :=
    Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left
      (inf_le_kernel_average (K w) (fun y ↦ hK w y) (hKs w) _) (hμ w)
  have hmid : oscMidpoint μ (f - featureCombo g lam) =
      ((∑ w, μ w * Finset.univ.sup' Finset.univ_nonempty
          (fun y ↦ (f - featureCombo g lam) (w, y))) +
        ∑ w, μ w * Finset.univ.inf' Finset.univ_nonempty
          (fun y ↦ (f - featureCombo g lam) (w, y))) / 2 := by
    rw [oscMidpoint, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  have hosc : oscTotal μ (f - featureCombo g lam) =
      (∑ w, μ w * Finset.univ.sup' Finset.univ_nonempty
          (fun y ↦ (f - featureCombo g lam) (w, y))) -
        ∑ w, μ w * Finset.univ.inf' Finset.univ_nonempty
          (fun y ↦ (f - featureCombo g lam) (w, y)) := by
    rw [oscTotal, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  rw [kernel_report_split μ g f lam K, hmid, hosc, abs_le]
  constructor <;> linarith

/-- **PL Theorem 8.2, exact-moment form.** At `ε = 0` the feasible pairs are exactly the
kernel pairs with identical supplied feature expectations. -/
theorem kernelGaps_zero_iff (μ : W → ℝ) (g : F → W × Y → ℝ) (f : W × Y → ℝ) (t : ℝ) :
    t ∈ kernelGaps μ g f 0 ↔ ∃ K L : W → Y → ℝ, (∀ w y, 0 ≤ K w y) ∧ (∀ w y, 0 ≤ L w y) ∧
      (∀ w, ∑ y, K w y = 1) ∧ (∀ w, ∑ y, L w y = 1) ∧
      (∀ i, (∑ w, μ w * ∑ y, K w y * g i (w, y)) =
        ∑ w, μ w * ∑ y, L w y * g i (w, y)) ∧
      t = (∑ w, μ w * ∑ y, K w y * f (w, y)) - ∑ w, μ w * ∑ y, L w y * f (w, y) := by
  constructor
  · rintro ⟨K, L, hK, hL, hKs, hLs, hmom, ht⟩
    refine ⟨K, L, hK, hL, hKs, hLs, fun i ↦ ?_, ht⟩
    have h := hmom i
    rw [mul_zero] at h
    have h2 := abs_nonneg ((∑ w, μ w * ∑ y, K w y * g i (w, y)) -
      ∑ w, μ w * ∑ y, L w y * g i (w, y))
    have h3 : |(∑ w, μ w * ∑ y, K w y * g i (w, y)) -
      ∑ w, μ w * ∑ y, L w y * g i (w, y)| = 0 := le_antisymm h h2
    have := abs_eq_zero.mp h3
    linarith
  · rintro ⟨K, L, hK, hL, hKs, hLs, hmom, ht⟩
    refine ⟨K, L, hK, hL, hKs, hLs, fun i ↦ ?_, ht⟩
    rw [hmom i]
    simp

end

end Descent.Portability.ConditionalOscillationDuality
