/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conditional rate consequences for deterministic-driving candidates

This module is **self-contained: it imports only Mathlib**.

This file contains two elementary implications used when analysing a concrete driving
system. It does not prove an entropy classification of deterministic dynamics.

## Positive entropy: full linear gain, refuting the plausible claim

The claim one would expect, and which is **false**: deterministic driving is not fresh, so
positive-entropy driving gives `D = 0` and no decay.

`linear_gain_of_uniform_factor` is the quantitative form: a uniform factor `ρ < 1` per step
gives gain at least `n · log(1/ρ)`, which is linear in `n`.

## Zero entropy: fluctuation collapse, a third failure mode

`sublinear_rate_of_bounded` says only that a bounded nonnegative gain has `Γ n / n → 0`.
That conclusion does not rule out every possible normalization, nor does it connect gain
to variance without an additional theorem. A Denjoy--Koksma or digit-factor application
must therefore be supplied separately and with its actual coding hypotheses.
-/

namespace Descent.BundleRigidity

open scoped BigOperators

/-! ## Positive entropy: linear gain -/

/-- **A uniform per-step conditional factor below one gives linear gain.**

If the modulus of the expectation is bounded by `ρ^n` with `0 < ρ < 1`, then the gain
`-log|E|` is at least `n · log(1/ρ)` — linear in the number of steps.

The result is agnostic about the source of the bound. In a symbolic dynamical application,
decodability and a genuine partial-expectation contraction must be proved first. -/
theorem linear_gain_of_uniform_factor (ρ E : ℝ) (n : ℕ)
    (hE : 0 < E) (hbound : E ≤ ρ ^ n) :
    (n : ℝ) * Real.log (1 / ρ) ≤ -Real.log E := by
  have hlog : Real.log E ≤ Real.log (ρ ^ n) := Real.log_le_log hE hbound
  rw [Real.log_pow] at hlog
  have hinv : Real.log (1 / ρ) = -Real.log ρ := by
    rw [one_div, Real.log_inv]
  rw [hinv]
  linarith

/-- The per-step factor for a doubling-map block factor is a cosine modulus, hence at most
one. That it is bounded *strictly* below one off the lattice is analysis and is carried as
`factorBoundedOffLattice`, not proved here. -/
theorem cos_factor_le_one (x : ℝ) : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x

/-! ## Bounded gain has zero linear rate -/

/-- A bounded nonnegative gain sequence has vanishing gain per coordinate.

This is a rate statement only; no variance or central-limit conclusion follows from it. -/
theorem sublinear_rate_of_bounded (Γ : ℕ → ℝ) (B : ℝ)
    (hnonneg : ∀ n, 0 ≤ Γ n) (hbdd : ∀ n, Γ n ≤ B) :
    Filter.Tendsto (fun n : ℕ ↦ Γ n / n) Filter.atTop (nhds 0) := by
  have hB : 0 ≤ B := le_trans (hnonneg 0) (hbdd 0)
  apply squeeze_zero (fun n ↦ div_nonneg (hnonneg n) (Nat.cast_nonneg n))
    (fun n ↦ div_le_div_of_nonneg_right (hbdd n) (Nat.cast_nonneg n))
  simpa using tendsto_const_div_atTop_nhds_zero_nat B

end Descent.BundleRigidity
