/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 25. The median is the middle value
of an actual sorted odd tuple, retaining repeated values. If that median
misses an interval, at least half of the original observations miss it.
No majority property is supplied as a hypothesis about an unspecified estimator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteMedianGeometry

open scoped BigOperators

/-- The actual middle order statistic of an odd tuple, with repetitions retained. -/
noncomputable def median {m : ℕ} (x : Fin (2 * m + 1) → ℝ) : ℝ :=
  x (Tuple.sort x ⟨m, by omega⟩)

/-- A median below the requested interval forces at least m+1 failures. -/
theorem lower_failure {m : ℕ} (x : Fin (2 * m + 1) → ℝ) (γ r : ℝ)
    (h : median x < γ - r) :
    m + 1 ≤ (Finset.univ.filter (fun i ↦ r < |x i - γ|)).card := by
  classical
  let j : Fin (2 * m + 1) := ⟨m, by omega⟩
  have hs : (Finset.Iic j).image (Tuple.sort x) ⊆
      Finset.univ.filter (fun i ↦ r < |x i - γ|) := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    have ho := Tuple.monotone_sort x (Finset.mem_Iic.mp hk)
    change x (Tuple.sort x k) ≤ median x at ho
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have ha := neg_le_abs (x (Tuple.sort x k) - γ)
    linarith
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (Tuple.sort x).injective, Fin.card_Iic] at hc
  exact hc

/-- A median above the requested interval forces at least m+1 failures. -/
theorem upper_failure {m : ℕ} (x : Fin (2 * m + 1) → ℝ) (γ r : ℝ)
    (h : γ + r < median x) :
    m + 1 ≤ (Finset.univ.filter (fun i ↦ r < |x i - γ|)).card := by
  classical
  let j : Fin (2 * m + 1) := ⟨m, by omega⟩
  have hs : (Finset.Ici j).image (Tuple.sort x) ⊆
      Finset.univ.filter (fun i ↦ r < |x i - γ|) := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    have ho := Tuple.monotone_sort x (Finset.mem_Ici.mp hk)
    change median x ≤ x (Tuple.sort x k) at ho
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have ha := le_abs_self (x (Tuple.sort x k) - γ)
    linarith
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (Tuple.sort x).injective, Fin.card_Ici] at hc
  dsimp [j] at hc
  omega

/-- A failed median requires a strict majority of failed original values. -/
theorem failure_majority {m : ℕ} (x : Fin (2 * m + 1) → ℝ) (γ r : ℝ)
    (h : r < |median x - γ|) :
    m + 1 ≤ (Finset.univ.filter (fun i ↦ r < |x i - γ|)).card := by
  rcases lt_abs.mp h with hl | hu
  · exact upper_failure x γ r (by linarith)
  · exact lower_failure x γ r (by linarith)

/-- The same necessary majority condition expressed as the sum of binary failure indicators. -/
theorem failure_sum {m : ℕ} (x : Fin (2 * m + 1) → ℝ) (γ r : ℝ)
    (h : r < |median x - γ|) :
    ((2 * m + 1 : ℕ) : ℝ) / 2 ≤ ∑ i, if r < |x i - γ| then (1 : ℝ) else 0 := by
  classical
  have hc : ((m + 1 : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i ↦ r < |x i - γ|)).card : ℝ) := by
    exact_mod_cast failure_majority x γ r h
  have he : (∑ i, if r < |x i - γ| then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i ↦ r < |x i - γ|)).card : ℝ) := by simp
  rw [he]
  push_cast at hc ⊢
  linarith

end Descent.Portability.FiniteMedianGeometry
