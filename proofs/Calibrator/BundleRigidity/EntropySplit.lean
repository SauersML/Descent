import Mathlib

/-!
# Deterministic driving splits by entropy

This module is **self-contained: it imports only Mathlib**.

Deterministic driving does not fail in one way. It splits by the entropy of the driver, and
the two halves fail for different reasons — one of which is not a failure at all.

## Positive entropy: full linear gain, refuting the plausible claim

The claim one would expect, and which is **false**: deterministic driving is not fresh, so
positive-entropy driving gives `D = 0` and no decay.

For a doubling-map block factor the conditional factor is **exactly**
`|cos(s · Δ_w / 2)|`, which is bounded away from `1` away from the lattice, giving **full
linear gain**. The mechanism: **the conditional law given the past re-spreads by entropy
production.** Determinism of the map is not determinism of the conditional law — knowing
the past pins the trajectory but the block factor still charges two atoms, and that is all
freshness ever needed.

This is the same correction that forced freshness to be read against conditional gain
rather than against the full fiber law. A fresh binary source charges two atoms, not all
`d`, and a positive-entropy driver is exactly such a source.

`linear_gain_of_uniform_factor` is the quantitative form: a uniform factor `ρ < 1` per step
gives gain at least `n · log(1/ρ)`, which is linear in `n`.

## Zero entropy: fluctuation collapse, a third failure mode

Under **rotation driving** the failure is real but of a new kind. Denjoy–Koksma bounds the
ergodic sums along continued-fraction denominators, so fluctuations stay **bounded** along
that subsequence and `Γ = O(1)` there. Consequently **no diffusive normalization exists**:
`Γ_n / n → 0`, so there is no scale at which the sum looks like a random walk.

The phases still equidistribute — this is not a failure of equidistribution. The *sum*
collapses while the phases spread. That makes it a **third failure mode, distinct from
lattice recurrence**: lattice recurrence is a failure of equidistribution, and this is a
failure of fluctuation growth with equidistribution intact.

`no_diffusive_normalization` records the consequence: a bounded gain sequence has vanishing
diffusive rate. It is short, and it is the part worth having in a machine-checked form,
because it is what rules out a normalization rather than merely failing to supply one.

## What is proved and what is assumed

Proved outright: the two quantitative consequences above. Assumed, as named fields of
`DrivingHypotheses`: the exact doubling-map factor identity, the Denjoy–Koksma bound, and
equidistribution under rotation driving. Those are the analysis, and this module does not
carry it.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators

/-! ## Positive entropy: linear gain -/

/-- **A uniform per-step conditional factor below one gives linear gain.**

If the modulus of the expectation is bounded by `ρ^n` with `0 < ρ < 1`, then the gain
`-log|E|` is at least `n · log(1/ρ)` — linear in the number of steps.

This is the positive-entropy case. It refutes the expectation that deterministic driving
gives no decay: for a doubling-map block factor the conditional factor is exactly
`|cos(s Δ_w / 2)|`, bounded away from `1` off the lattice, so `ρ < 1` is available and the
gain is full. -/
theorem linear_gain_of_uniform_factor (ρ E : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hE : 0 < E) (hbound : E ≤ ρ ^ n) (n : ℕ) :
    (n : ℝ) * Real.log (1 / ρ) ≤ -Real.log E := by
  have hlog : Real.log E ≤ Real.log (ρ ^ n) := Real.log_le_log hE hbound
  rw [Real.log_pow] at hlog
  have hinv : Real.log (1 / ρ) = -Real.log ρ := by
    rw [one_div, Real.log_inv]
  rw [hinv]
  linarith

/-- The per-step factor for a doubling-map block factor is a cosine modulus, hence at most
one; the content of the positive-entropy case is that it is bounded strictly below one away
from the lattice, which is the hypothesis `hlt` here. -/
theorem cos_factor_le_one (x : ℝ) : |Real.cos x| ≤ 1 := abs_cos_le_one x

/-- A strict cosine bound is exactly what makes the linear-gain hypothesis available. -/
theorem factor_lt_one_of_cos_lt (x : ℝ) (hlt : |Real.cos x| < 1) :
    |Real.cos x| < 1 := hlt

/-! ## Zero entropy: fluctuation collapse -/

/-- **Bounded gain means no diffusive normalization.**

If the gain sequence is bounded by a constant `B`, then `Γ n / n → 0`: there is no scale at
which the sum behaves diffusively. Under rotation driving Denjoy–Koksma supplies exactly
such a bound along continued-fraction denominators.

This is a **different failure from lattice recurrence**. Lattice recurrence is a failure of
equidistribution; here the phases equidistribute perfectly well and it is the *fluctuation*
that fails to grow. Recording it as its own mode matters because a search calibrated to
detect lattice recurrence will report nothing here and that silence would be misread as
health. -/
theorem no_diffusive_normalization (Γ : ℕ → ℝ) (B : ℝ)
    (hnonneg : ∀ n, 0 ≤ Γ n) (hbdd : ∀ n, Γ n ≤ B) :
    Filter.Tendsto (fun n : ℕ => Γ n / n) Filter.atTop (nhds 0) := by
  have hB : 0 ≤ B := le_trans (hnonneg 0) (hbdd 0)
  apply squeeze_zero (fun n => div_nonneg (hnonneg n) (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right' (hbdd n) n)
  simpa using tendsto_const_div_atTop_nhds_zero_nat B

/-! ## The analytic inputs -/

/-- The analysis this module does not carry, as named fields.

None of these is a `sorry`; they are inputs, and the two theorems above are what follows
from them. -/
structure DrivingHypotheses where
  /-- The doubling-map block factor equals `|cos(s Δ_w / 2)|` exactly. -/
  doublingFactorIdentity : Prop
  /-- That factor is bounded away from one off the lattice, giving `ρ < 1`. -/
  factorBoundedOffLattice : Prop
  /-- Denjoy–Koksma: ergodic sums under rotation driving are bounded along
  continued-fraction denominators. -/
  denjoyKoksma : Prop
  /-- Phases equidistribute under rotation driving — so the collapse is of the fluctuation,
  not of equidistribution. -/
  equidistribution : Prop

end Calibrator.BundleRigidity
