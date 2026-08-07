/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.DescentTime
import Descent.Coalescent.HoldingTime
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Coming down from infinity, almost surely

`Descent.Coalescent.DescentTime` identifies Schweinsberg's `Σ γ_k⁻¹` as the MEAN time to
descend from infinity, and records the missing step: the passage from a finite mean to an
almost-sure statement about the process.  `Descent.Coalescent.TrajectoryLaw` supplied a
process for the jump chain.  This file supplies the clock, and takes the step.

The clock is an infinite product of holding-time laws -- one per level, at that level's rate
-- which is `Measure.infinitePi` applied to `HoldingTime.holdMeasure`.  The total descent
time is then the sum of the coordinates, and the theorem is the standard one about
nonnegative series:

  if the means are summable, the series is finite almost surely.

Tonelli exchanges the sum and the integral, each coordinate's integral is that level's mean
sojourn `γ_k⁻¹`, and a nonnegative function with finite integral is finite almost everywhere.
So `ae_totalDescentTime_lt_top` says: **a coalescent satisfying Schweinsberg's condition comes
down from infinity in finite time, almost surely.**

That is the forward direction of the equivalence `Descent.Coalescent.Program` recorded as
open.  The converse -- that failing the condition forces an infinite descent time almost
surely -- is Kolmogorov's three-series theorem applied to independent exponentials, and is not
here; nor is the multiple-merger correction, where `γ_b` is an expected decrease rate rather
than a rate of leaving a level.

## Main results

- `holdProduct`: the clock, an infinite product of `HoldingTime.holdMeasure`s.
- `lintegral_id_holdMeasure`: **`E τ = 1/d` in the form Tonelli needs**, from
  `HoldingTime.integral_id_mul_holdDensity`.
- `ae_tsum_lt_top_of_lintegral_ne_top`: a nonnegative independent series with summable means
  is almost surely finite.
- `ae_totalDescentTime_lt_top`: **Schweinsberg's condition gives a finite descent time,
  almost surely**.
-/

namespace Coalescent

open MeasureTheory Set

/-! ### The mean sojourn, as a lower integral -/

/-- **`∫⁻ t · (holding density) = 1/d`.**  `HoldingTime.integral_id_mul_holdDensity` proves
this as a Bochner integral; Tonelli needs it as a lower integral of an `ℝ≥0∞`-valued
function, and the passage between them is the standard one for a nonnegative integrable
function. -/
theorem lintegral_id_holdMeasure {d : ℝ} (hd : 0 < d) :
    ∫⁻ t, ENNReal.ofReal t ∂(holdMeasure d) = ENNReal.ofReal (1 / d) := by
  have hmeas : Measurable (holdDensity d) := by
    unfold holdDensity
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    exact (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)).ennreal_ofReal
  have hid : Measurable fun t : ℝ ↦ ENNReal.ofReal t := measurable_id.ennreal_ofReal
  have hint : IntegrableOn (fun t : ℝ ↦ t * (d * Real.exp (-(d * t)))) (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi (0 : ℝ)) :=
      Real.GammaIntegral_convergent (by norm_num)
    have hscale : IntegrableOn
        (fun x : ℝ ↦ Real.exp (-(d * x)) * (d * x) ^ ((2 : ℝ) - 1)) (Ioi (0 : ℝ)) := by
      refine (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ ↦ Real.exp (-x) * x ^ ((2 : ℝ) - 1)) 0 hd).mpr ?_
      simpa using hg
    refine hscale.congr_fun ?_ measurableSet_Ioi
    intro t _
    norm_num
    ring
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ t * (d * Real.exp (-(d * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    positivity
  have hind : ∀ t : ℝ, holdDensity d t * ENNReal.ofReal t
      = (Ioi (0 : ℝ)).indicator (fun t ↦ ENNReal.ofReal (t * (d * Real.exp (-(d * t))))) t := by
    intro t
    unfold holdDensity
    by_cases ht : 0 < t
    · rw [if_pos ht, Set.indicator_of_mem (mem_Ioi.mpr ht), ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    · rw [if_neg ht, Set.indicator_of_not_mem (by simpa using le_of_not_lt ht), zero_mul]
  calc ∫⁻ t, ENNReal.ofReal t ∂(holdMeasure d)
      = ∫⁻ t, holdDensity d t * ENNReal.ofReal t := by
        rw [holdMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas hid]
        rfl
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t * (d * Real.exp (-(d * t)))) := by
        simp only [hind]
        rw [lintegral_indicator measurableSet_Ioi]
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), t * (d * Real.exp (-(d * t)))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    _ = ENNReal.ofReal (1 / d) := by
        rw [integral_id_mul_holdDensity hd]

/-! ### The clock -/

/-- The clock: one holding time per level, independent, at that level's rate. -/
noncomputable def holdProduct (γ : ℕ → ℝ) (hγ : ∀ k, 0 < γ (k + 2)) : Measure (ℕ → ℝ) :=
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (γ (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (hγ k)
  Measure.infinitePi (fun k : ℕ ↦ holdMeasure (γ (k + 2)))

/-! ### Almost-sure finiteness -/

/-- **A nonnegative independent series with summable means is almost surely finite.**  Tonelli
exchanges the sum and the integral; a nonnegative function with finite integral is finite
almost everywhere. -/
theorem ae_tsum_lt_top_of_lintegral_ne_top {μ : ℕ → Measure ℝ}
    [∀ k, IsProbabilityMeasure (μ k)]
    (hfin : (∑' k : ℕ, ∫⁻ t, ENNReal.ofReal t ∂(μ k)) ≠ ⊤) :
    ∀ᵐ ω ∂(Measure.infinitePi μ), (∑' k : ℕ, ENNReal.ofReal (ω k)) < ⊤ := by
  have hmeas : ∀ k : ℕ, Measurable fun ω : ℕ → ℝ ↦ ENNReal.ofReal (ω k) := fun k ↦
    (measurable_pi_apply k).ennreal_ofReal
  have hsum : Measurable fun ω : ℕ → ℝ ↦ ∑' k : ℕ, ENNReal.ofReal (ω k) :=
    Measurable.ennreal_tsum hmeas
  refine ae_lt_top hsum ?_
  rw [lintegral_tsum fun k ↦ (hmeas k).aemeasurable]
  have hco : ∀ k : ℕ, ∫⁻ ω : ℕ → ℝ, ENNReal.ofReal (ω k) ∂(Measure.infinitePi μ)
      = ∫⁻ t, ENNReal.ofReal t ∂(μ k) := by
    intro k
    exact (measurePreserving_eval_infinitePi μ k).lintegral_comp measurable_id.ennreal_ofReal
  simp only [hco]
  exact hfin

/-- **Schweinsberg's condition gives a finite descent time, almost surely.**

The mean sojourn at level `k` is `γ_k⁻¹` (`lintegral_id_holdMeasure`), the condition is that
those are summable (`ComingDownCriterion.comesDownFromInfinity`), and a nonnegative series
with summable means is almost surely finite.  So a coalescent satisfying the condition passes
through every level in finite total time, with probability one -- it comes down from
infinity.

This is the forward direction of the equivalence.  The converse needs Kolmogorov's
three-series theorem, and the multiple-merger correction needs `γ_b` to be a rate of leaving
rather than an expected decrease. -/
theorem ae_totalDescentTime_lt_top {γ : ℕ → ℝ} (hγ : ∀ k, 0 < γ (k + 2))
    (h : comesDownFromInfinity γ) :
    ∀ᵐ ω ∂(holdProduct γ hγ), (∑' k : ℕ, ENNReal.ofReal (ω k)) < ⊤ := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (γ (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (hγ k)
  refine ae_tsum_lt_top_of_lintegral_ne_top (μ := fun k ↦ holdMeasure (γ (k + 2))) ?_
  have hval : ∀ k : ℕ, ∫⁻ t, ENNReal.ofReal t ∂(holdMeasure (γ (k + 2)))
      = ENNReal.ofReal (1 / γ (k + 2)) := fun k ↦ lintegral_id_holdMeasure (hγ k)
  simp only [hval]
  have hnn : ∀ k : ℕ, 0 ≤ 1 / γ (k + 2) := fun k ↦ le_of_lt (one_div_pos.mpr (hγ k))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn h]
  exact ENNReal.ofReal_ne_top

/-- **Kingman's coalescent comes down from infinity, almost surely.**

`ComingDownCriterion.kingman_comesDownFromInfinity` verifies the condition for the ladder
`d_k = k(k-1)/2`, so the total time to pass through every level is finite with probability
one.  `ComingDownFromInfinity.descentCurve` describes the rate at which it does so, and
`Rates.tsum_one_div_deathRate_tail` gives the mean, `2/(k-1)`; this says the event itself has
probability one.

It is the statement K-C (2.8) and K-G (6.1) rely on when they start the death process from
infinity, and until now the corpus had it only in expectation. -/
theorem kingman_ae_comesDownFromInfinity :
    ∀ᵐ ω ∂(holdProduct deathRate (fun k ↦ deathRate_pos (by omega))),
      (∑' k : ℕ, ENNReal.ofReal (ω k)) < ⊤ :=
  ae_totalDescentTime_lt_top _ kingman_comesDownFromInfinity

end Coalescent

end Descent
