/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteCountTail
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
Convergence of every count layer plus a uniform inverse-cutoff truncation error
implies convergence of the complete observable to the convergent layer series.
The proof explicitly controls both the finite-array and limiting-series tails.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CountTailConvergence

open scoped BigOperators Topology
open Filter

/-- A uniform count-tail certificate justifies summing the individual layer limits. -/
theorem tendsto_of_layer_truncation (a : ℕ → ℕ → ℂ) (g : ℕ → ℂ) (f : ℕ → ℂ)
    (ha : ∀ r, Tendsto (a r) atTop (𝓝 (f r))) (hf : Summable f) (C : ℝ)
    (ht : ∀ R : ℕ, 0 < R → ∀ᶠ m in atTop,
      ‖g m - ∑ r ∈ Finset.range R, a r m‖ ≤ C / (R : ℝ)) :
    Tendsto g atTop (𝓝 (∑' r, f r)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hp := hf.hasSum.tendsto_sum_nat
  have hc : Tendsto (fun R : ℕ ↦ C / (R : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  have hex : ∀ᶠ R : ℕ in atTop, 0 < R ∧ C / (R : ℝ) < ε / 3 ∧
      dist (∑ r ∈ Finset.range R, f r) (∑' r, f r) < ε / 3 := by
    filter_upwards [eventually_gt_atTop 0,
      hc.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity)),
      hp.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < ε / 3 by positivity))]
      with R hR hcR hpR
    exact ⟨hR, hcR, hpR⟩
  obtain ⟨R, hR, hcR, hpR⟩ := hex.exists
  have hs : Tendsto (fun m ↦ ∑ r ∈ Finset.range R, a r m) atTop
      (𝓝 (∑ r ∈ Finset.range R, f r)) := tendsto_finset_sum _ (fun r _ ↦ ha r)
  have hev : ∀ᶠ m in atTop, dist (g m) (∑' r, f r) < ε := by
    filter_upwards [ht R hR,
      hs.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < ε / 3 by positivity))]
      with m hm hsM
    have hd := dist_triangle (g m) (∑ r ∈ Finset.range R, a r m) (∑' r, f r)
    have he := dist_triangle (∑ r ∈ Finset.range R, a r m)
      (∑ r ∈ Finset.range R, f r) (∑' r, f r)
    change dist (∑ r ∈ Finset.range R, a r m) (∑ r ∈ Finset.range R, f r) < ε / 3 at hsM
    simp only [dist_eq_norm] at hd he hsM hpR ⊢
    linarith
  exact eventually_atTop.1 hev

end Descent.Portability.CountTailConvergence
