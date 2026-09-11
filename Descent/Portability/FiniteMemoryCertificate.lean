/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMemoryLaw
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed

assert_below Descent.Decision Descent.Program

/-!
Local finite-memory truncation bounds on the exact retained history. Hidden
initial-state forcing has its own bound; no global approximate-trajectory
stability is inferred from these one-step residual certificates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteMemoryCertificate

open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hidden_power_bound (hidden : F →L[ℝ] F) (rho : ℝ) (hhidden : ‖hidden‖ ≤ rho)
    (lag : ℕ) (v : F) : ‖(hidden ^ lag) v‖ ≤ rho ^ lag * ‖v‖ := by
  have hrho : 0 ≤ rho := (norm_nonneg _).trans hhidden
  induction lag with
  | zero => simp
  | succ lag ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    calc
      _ ≤ ‖hidden‖ * ‖(hidden ^ lag) v‖ := hidden.le_opNorm _
      _ ≤ rho * ‖(hidden ^ lag) v‖ := mul_le_mul_of_nonneg_right hhidden (norm_nonneg _)
      _ ≤ rho * (rho ^ lag * ‖v‖) := mul_le_mul_of_nonneg_left ih hrho
      _ = _ := by rw [pow_succ']; ring

noncomputable def memoryTerm (feedback : F →L[ℝ] E) (coupling : E →L[ℝ] F)
    (hidden : F →L[ℝ] F) (retained : ℕ → E) (time lag : ℕ) : E :=
  feedback ((hidden ^ lag) (coupling (retained (time - 1 - lag))))

theorem memoryTerm_bound (feedback : F →L[ℝ] E) (coupling : E →L[ℝ] F)
    (hidden : F →L[ℝ] F) (retained : ℕ → E) (rho M : ℝ)
    (hhidden : ‖hidden‖ ≤ rho) (hretained : ∀ j, ‖retained j‖ ≤ M) (time lag : ℕ) :
    ‖memoryTerm feedback coupling hidden retained time lag‖ ≤
      (‖feedback‖ * ‖coupling‖ * M) * rho ^ lag := by
  have hrho : 0 ≤ rho := (norm_nonneg _).trans hhidden
  calc
    _ ≤ ‖feedback‖ * ‖(hidden ^ lag) (coupling (retained (time - 1 - lag)))‖ :=
      feedback.le_opNorm _
    _ ≤ ‖feedback‖ * (rho ^ lag * ‖coupling (retained (time - 1 - lag))‖) :=
      mul_le_mul_of_nonneg_left (hidden_power_bound hidden rho hhidden lag _) (norm_nonneg _)
    _ ≤ ‖feedback‖ * (rho ^ lag * (‖coupling‖ * M)) := by
      gcongr
      exact (coupling.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hretained _) (norm_nonneg _))
    _ = _ := by ring

theorem geometric_tail_bound (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho < 1) (m time : ℕ) :
    (∑ lag ∈ Finset.Ico m time, rho ^ lag) ≤ rho ^ m / (1 - rho) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [pow_add, ← Finset.mul_sum]
  have hsum := (summable_geometric_of_lt_one hrho hrho1).sum_le_tsum
    (Finset.range (time - m)) (fun n _ ↦ pow_nonneg hrho n)
  rw [tsum_geometric_of_lt_one hrho hrho1] at hsum
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hsum (pow_nonneg hrho m)

theorem memory_tail_bound (feedback : F →L[ℝ] E) (coupling : E →L[ℝ] F)
    (hidden : F →L[ℝ] F) (retained : ℕ → E) (rho M : ℝ)
    (hhidden : ‖hidden‖ ≤ rho) (hrho1 : rho < 1) (hretained : ∀ j, ‖retained j‖ ≤ M)
    (m time : ℕ) :
    ‖∑ lag ∈ Finset.Ico m time, memoryTerm feedback coupling hidden retained time lag‖ ≤
      ‖feedback‖ * ‖coupling‖ * M * rho ^ m / (1 - rho) := by
  have hrho : 0 ≤ rho := (norm_nonneg _).trans hhidden
  have hM : 0 ≤ M := (norm_nonneg (retained 0)).trans (hretained 0)
  calc
    _ ≤ ∑ lag ∈ Finset.Ico m time,
        ‖memoryTerm feedback coupling hidden retained time lag‖ := norm_sum_le _ _
    _ ≤ ∑ lag ∈ Finset.Ico m time, (‖feedback‖ * ‖coupling‖ * M) * rho ^ lag :=
      Finset.sum_le_sum (fun lag _ ↦ memoryTerm_bound feedback coupling hidden retained
        rho M hhidden hretained time lag)
    _ = (‖feedback‖ * ‖coupling‖ * M) * (∑ lag ∈ Finset.Ico m time, rho ^ lag) := by
      rw [Finset.mul_sum]
    _ ≤ (‖feedback‖ * ‖coupling‖ * M) * (rho ^ m / (1 - rho)) :=
      mul_le_mul_of_nonneg_left (geometric_tail_bound rho hrho hrho1 m time) (by positivity)
    _ = _ := by ring

theorem initial_forcing_bound (feedback : F →L[ℝ] E) (hidden : F →L[ℝ] F)
    (rho : ℝ) (hhidden : ‖hidden‖ ≤ rho) (time : ℕ) (initial : F) :
    ‖feedback ((hidden ^ time) initial)‖ ≤ ‖feedback‖ * rho ^ time * ‖initial‖ := by
  calc
    _ ≤ ‖feedback‖ * ‖(hidden ^ time) initial‖ := feedback.le_opNorm _
    _ ≤ ‖feedback‖ * (rho ^ time * ‖initial‖) :=
      mul_le_mul_of_nonneg_left (hidden_power_bound hidden rho hhidden time initial)
        (norm_nonneg _)
    _ = _ := by ring

theorem retained_memory_lags (direct : E →L[ℝ] E) (feedback : F →L[ℝ] E)
    (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F) (retained : ℕ → E) (discarded : ℕ → F)
    (hretained : ∀ t, retained (t + 1) = direct (retained t) + feedback (discarded t))
    (hdiscarded : ∀ t, discarded (t + 1) = coupling (retained t) + hidden (discarded t))
    (time : ℕ) :
    retained (time + 1) = direct (retained time) + feedback ((hidden ^ time) (discarded 0)) +
      ∑ lag ∈ Finset.range time, memoryTerm feedback coupling hidden retained time lag := by
  have hh := ExactMemoryLaw.retained_memory direct.toLinearMap feedback.toLinearMap
    coupling.toLinearMap hidden.toLinearMap retained discarded hretained hdiscarded time
  simp only [Module.End.coe_pow, ContinuousLinearMap.coe_coe] at hh
  simp only [ContinuousLinearMap.coe_pow]
  rw [hh]
  congr 1
  calc
    _ = ∑ j ∈ Finset.range time,
        memoryTerm feedback coupling hidden retained time (time - 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [memoryTerm, ContinuousLinearMap.coe_pow,
        show time - 1 - (time - 1 - j) = j by omega]
    _ = _ := Finset.sum_range_reflect _ time

noncomputable def truncatedUpdate (direct : E →L[ℝ] E) (feedback : F →L[ℝ] E)
    (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F) (retained : ℕ → E) (initial : F)
    (m time : ℕ) : E :=
  direct (retained time) + feedback ((hidden ^ time) initial) +
    ∑ lag ∈ Finset.range (min m time), memoryTerm feedback coupling hidden retained time lag

/-- The error of retaining only the most recent m lags, evaluated on the
exact history, with the hidden initial forcing still included. -/
theorem truncated_update_bound (direct : E →L[ℝ] E) (feedback : F →L[ℝ] E)
    (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F) (retained : ℕ → E) (discarded : ℕ → F)
    (hretained : ∀ t, retained (t + 1) = direct (retained t) + feedback (discarded t))
    (hdiscarded : ∀ t, discarded (t + 1) = coupling (retained t) + hidden (discarded t))
    (rho M : ℝ) (hhidden : ‖hidden‖ ≤ rho) (hrho1 : rho < 1)
    (hbound : ∀ j, ‖retained j‖ ≤ M) (m time : ℕ) :
    ‖retained (time + 1) - truncatedUpdate direct feedback coupling hidden retained
        (discarded 0) m time‖ ≤ ‖feedback‖ * ‖coupling‖ * M * rho ^ m / (1 - rho) := by
  rw [retained_memory_lags direct feedback coupling hidden retained discarded
    hretained hdiscarded time]
  unfold truncatedUpdate
  by_cases hm : m ≤ time
  · rw [min_eq_left hm, ← Finset.sum_range_add_sum_Ico _ hm]
    have he : ∀ a b c : E, a + (b + c) - (a + b) = c := by intros; abel
    rw [he]
    exact memory_tail_bound feedback coupling hidden retained rho M hhidden hrho1 hbound m time
  · rw [min_eq_right (Nat.le_of_not_ge hm), sub_self, norm_zero]
    have hrho : 0 ≤ rho := (norm_nonneg _).trans hhidden
    have hM : 0 ≤ M := (norm_nonneg (retained 0)).trans (hbound 0)
    have hden : 0 < 1 - rho := sub_pos.mpr hrho1
    positivity

end Descent.Portability.FiniteMemoryCertificate
