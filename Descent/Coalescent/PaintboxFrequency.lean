/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Paintbox
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic

namespace Descent

/-!
# Paintbox frequencies exist

K-C Theorem 2 has two halves.  The hard half is that EVERY exchangeable random equivalence
relation on `ℕ` is a paintbox mixture, and it goes through a reversed martingale convergence
theorem (K-C cites Doob VII.4.25); that is untouched here.  The other half -- that a paintbox
HAS asymptotic frequencies, and that they are the paintbox's own parameters -- is the strong
law of large numbers, and that is in Mathlib.

K-C (3.8) asks for `X_r = lim n⁻¹ λ_r(n)`, the limiting size of the `r`-th class of `ρ_n R`.
For the paintbox construction of K-C (3.4) the class of colour `r` is `{i ; Z_i = r}`, so
`λ_r(n)` counts how many of the first `n` balls got colour `r`, and the limit is `P{Z = r}`
by the strong law.  `tendsto_colourFrequency` is that statement, and
`integral_colourIndicator` identifies the limit as the colour's own probability -- so for a
paintbox the frequencies not only exist but are the `x_r` the box was built from.

What this does not do is run K-C's argument in the other direction, which is the whole
content of Theorem 2 and stays open.

## Main results

- `colourIndicator`: the indicator that ball `i` got colour `r`.
- `integral_colourIndicator`: its mean is the colour's probability.
- `tendsto_colourFrequency`: **K-C (3.8) for the paintbox** -- the frequency of colour `r`
  among the first `n` balls converges almost surely to `P{Z = r}`.
-/

namespace Coalescent

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*}

/-- The indicator that ball `i` received colour `r`.  Summed over `i < n` it is `λ_r(n)`,
the size of the `r`-th class of `ρ_n R`. -/
noncomputable def colourIndicator (Z : ℕ → Ω → ℕ) (r i : ℕ) : Ω → ℝ :=
  fun ω => if Z i ω = r then (1 : ℝ) else 0

theorem measurable_colourIndicator [MeasurableSpace Ω] {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i))
    (r i : ℕ) : Measurable (colourIndicator Z r i) := by
  unfold colourIndicator
  exact measurable_const.ite ((hZ i) (measurableSet_singleton r)) measurable_const

theorem colourIndicator_le_one {Z : ℕ → Ω → ℕ} (r i : ℕ) (ω : Ω) :
    ‖colourIndicator Z r i ω‖ ≤ 1 := by
  unfold colourIndicator
  by_cases h : Z i ω = r <;> simp [h]

theorem integrable_colourIndicator [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i)) (r i : ℕ) :
    Integrable (colourIndicator Z r i) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_colourIndicator hZ r i).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω => colourIndicator_le_one r i ω

/-- The mean of the indicator is the colour's probability, so the limit below is the paintbox
parameter and not merely some number. -/
theorem integral_colourIndicator [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i)) (r i : ℕ) :
    ∫ ω, colourIndicator Z r i ω = (ℙ {ω | Z i ω = r}).toReal := by
  have hmeas : MeasurableSet {ω | Z i ω = r} := (hZ i) (measurableSet_singleton r)
  have hind : colourIndicator Z r i = Set.indicator {ω | Z i ω = r} (1 : Ω → ℝ) := by
    funext ω
    simp only [colourIndicator, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [hind, integral_indicator_one hmeas]
  simp [MeasureTheory.measureReal_def]

/-- **K-C (3.8) for the paintbox.**  The frequency of colour `r` among the first `n` balls
converges almost surely, and its limit is the colour's own probability.

For an i.i.d. colouring the classes of the paintbox relation K-C (3.4) are the colour
classes, so this says the asymptotic class frequencies `X_r` exist and equal the `x_r` the
box was built from.  Theorem 2's content is the converse -- that an arbitrary exchangeable
relation is such a box -- and that is not this. -/
theorem tendsto_colourFrequency [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i))
    (hindep : Pairwise fun i j => IndepFun (Z i) (Z j))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0))
    (r : ℕ) :
    ∀ᵐ ω, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, colourIndicator Z r i ω)
      atTop (nhds ((ℙ {ω | Z 0 ω = r}).toReal)) := by
  have hindep' : Pairwise fun i j => IndepFun (colourIndicator Z r i) (colourIndicator Z r j) := by
    intro i j hij
    exact (hindep hij).comp
      (measurable_const.ite (measurable_id (measurableSet_singleton r)) measurable_const)
      (measurable_const.ite (measurable_id (measurableSet_singleton r)) measurable_const)
  have hident' : ∀ i, IdentDistrib (colourIndicator Z r i) (colourIndicator Z r 0) := by
    intro i
    exact (hident i).comp
      (measurable_const.ite (measurable_id (measurableSet_singleton r)) measurable_const)
  have hlaw := ProbabilityTheory.strong_law_ae (X := colourIndicator Z r)
    (integrable_colourIndicator hZ r 0) hindep' hident'
  have hmean := integral_colourIndicator hZ r 0
  filter_upwards [hlaw] with ω hω
  rw [← hmean]
  exact hω

end Coalescent

end Descent
