/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TransitTransform
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# The converse: failing Schweinsberg's condition means never coming down

`Descent.Coalescent.EntranceLaw` proves the forward half -- summable `γ_k⁻¹` gives an almost
surely finite descent from infinity.  This file proves the other half for a block count that
drops one level at a time: if the reciprocal rates are NOT summable, the descent time is
infinite almost surely, so the process does not come down at all.

The instrument is `Descent.Coalescent.TransitTransform`'s product.  At `θ = 1`,

  `E(e^{-Σ_{k<m} τ_k}) = ∏_{k<m} γ_k/(γ_k + 1)`,

and `1 - x ≤ e^{-x}` bounds that product by `exp(-Σ_{k<m} (γ_k+1)⁻¹)`.  When the reciprocals
diverge so does that sum, so the products tend to zero; monotone convergence over the
decreasing sequence carries the limit inside the integral, and a nonnegative function with zero
integral is zero almost everywhere.  A vanishing `e^{-S}` is an infinite `S`.

Together with `EntranceLaw.ae_totalDescentTime_lt_top` this is an equivalence:

  **the descent time is almost surely finite exactly when `Σ γ_k⁻¹` converges.**

## The hypothesis `1 ≤ γ_k`

Every rate this corpus decides the criterion for satisfies it -- Kingman's `d_k = k(k-1)/2`
from `k = 2`, the star's `b - 1` from `b = 2`, Bolthausen-Sznitman's `b(H_b - 1)`.  It is used
once, to pass from `Σ γ_k⁻¹ = ∞` to `Σ (γ_k+1)⁻¹ = ∞`, and could be dropped at the cost of a
case split on whether infinitely many rates are below one.

## What this still does not close

The multiple-merger correction.  For a `Λ`-coalescent that can drop several levels at once,
`γ_b` is the expected DECREASE rate rather than the rate of leaving level `b`, so the mean
sojourn is not `γ_b⁻¹` and the identity between the series and the descent time becomes an
inequality.  Schweinsberg's theorem proper is that inequality being tight enough; it is not
here, and `Descent.Coalescent.Program` says so.

## Main results

- `prod_le_exp_neg_sum`: `∏ (1 - a_k) ≤ exp(-Σ a_k)`.
- `tendsto_prod_ratio_zero`: the products vanish when the reciprocals diverge.
- `ae_totalDescentTime_eq_top`: **the descent time is infinite, almost surely**.
-/

namespace Coalescent

open MeasureTheory Filter Finset

/-- `∏ (1 - a_k) ≤ exp(-Σ a_k)` for `a_k ∈ [0,1]`: the elementary bound `1 - x ≤ e^{-x}`,
multiplied. -/
theorem prod_le_exp_neg_sum (a : ℕ → ℝ) (h0 : ∀ k, 0 ≤ a k) (h1 : ∀ k, a k ≤ 1) (m : ℕ) :
    ∏ k ∈ range m, (1 - a k) ≤ Real.exp (-∑ k ∈ range m, a k) := by
  induction m with
  | zero => simp
  | succ p ih =>
      have hstep : 1 - a p ≤ Real.exp (-a p) := by
        have h := Real.add_one_le_exp (-a p)
        linarith
      have hnn : (0 : ℝ) ≤ ∏ k ∈ range p, (1 - a k) :=
        Finset.prod_nonneg fun k _ ↦ by linarith [h1 k]
      have hexp : (0 : ℝ) < Real.exp (-a p) := Real.exp_pos _
      calc ∏ k ∈ range (p + 1), (1 - a k)
          = (∏ k ∈ range p, (1 - a k)) * (1 - a p) := by rw [Finset.prod_range_succ]
        _ ≤ Real.exp (-∑ k ∈ range p, a k) * Real.exp (-a p) := by
            refine mul_le_mul ih hstep (by linarith [h1 p]) (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-∑ k ∈ range (p + 1), a k) := by
            rw [← Real.exp_add, Finset.sum_range_succ]
            congr 1
            ring

/-- The ratios `γ_k/(γ_k+1)` are `1 - (γ_k+1)⁻¹`, so their products are bounded by the
exponential of the negated partial sums. -/
theorem prod_ratio_le_exp {γ : ℕ → ℝ} (hγ : ∀ k, 1 ≤ γ (k + 2)) (m : ℕ) :
    ∏ k ∈ range m, (γ (k + 2) / (γ (k + 2) + 1))
      ≤ Real.exp (-∑ k ∈ range m, 1 / (γ (k + 2) + 1)) := by
  have hratio : ∀ k : ℕ, γ (k + 2) / (γ (k + 2) + 1) = 1 - 1 / (γ (k + 2) + 1) := by
    intro k
    have hpos : (0 : ℝ) < γ (k + 2) + 1 := by linarith [hγ k]
    field_simp
    ring
  have h0 : ∀ k : ℕ, (0 : ℝ) ≤ 1 / (γ (k + 2) + 1) := by
    intro k
    have hpos : (0 : ℝ) < γ (k + 2) + 1 := by linarith [hγ k]
    positivity
  have h1 : ∀ k : ℕ, 1 / (γ (k + 2) + 1) ≤ 1 := by
    intro k
    have hpos : (0 : ℝ) < γ (k + 2) + 1 := by linarith [hγ k]
    rw [div_le_one hpos]
    linarith [hγ k]
  simp only [hratio]
  exact prod_le_exp_neg_sum (fun k ↦ 1 / (γ (k + 2) + 1)) h0 h1 m

/-- **Non-summable reciprocals make the partial sums of `(γ_k+1)⁻¹` diverge.**  With
`γ_k ≥ 1` the two series differ by at most a factor of two. -/
theorem tendsto_sum_inv_succ_atTop {γ : ℕ → ℝ} (hγ : ∀ k, 1 ≤ γ (k + 2))
    (h : ¬ comesDownFromInfinity γ) :
    Tendsto (fun m : ℕ ↦ ∑ k ∈ range m, 1 / (γ (k + 2) + 1)) atTop atTop := by
  have hpos : ∀ k : ℕ, (0 : ℝ) < γ (k + 2) := fun k ↦ lt_of_lt_of_le zero_lt_one (hγ k)
  have hnot : ¬ Summable fun k : ℕ ↦ 1 / (γ (k + 2) + 1) := by
    intro hs
    refine h ?_
    have hcmp : ∀ k : ℕ, 1 / γ (k + 2) ≤ 2 * (1 / (γ (k + 2) + 1)) := by
      intro k
      have h1 : (0 : ℝ) < γ (k + 2) := hpos k
      have h2 : (0 : ℝ) < γ (k + 2) + 1 := by linarith
      have hr : 2 * (1 / (γ (k + 2) + 1)) = 2 / (γ (k + 2) + 1) := by ring
      rw [hr, div_le_div_iff₀ h1 h2]
      nlinarith [hγ k]
    exact Summable.of_nonneg_of_le (fun k ↦ le_of_lt (one_div_pos.mpr (hpos k))) hcmp
      (hs.mul_left 2)
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ 1 / (γ (k + 2) + 1) := by
    intro k
    have h2 : (0 : ℝ) < γ (k + 2) + 1 := by linarith [hpos k]
    positivity
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hnot

/-- **The products vanish.**  Bounded by `exp` of a divergent negated sum. -/
theorem tendsto_prod_ratio_zero {γ : ℕ → ℝ} (hγ : ∀ k, 1 ≤ γ (k + 2))
    (h : ¬ comesDownFromInfinity γ) :
    Tendsto (fun m : ℕ ↦ ∏ k ∈ range m, (γ (k + 2) / (γ (k + 2) + 1)))
      atTop (nhds 0) := by
  have hdiv := tendsto_sum_inv_succ_atTop hγ h
  have hneg : Tendsto (fun m : ℕ ↦ -∑ k ∈ range m, 1 / (γ (k + 2) + 1)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hdiv
  have hexp : Tendsto (fun m : ℕ ↦ Real.exp (-∑ k ∈ range m, 1 / (γ (k + 2) + 1)))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  refine squeeze_zero (fun m ↦ ?_) (fun m ↦ prod_ratio_le_exp hγ m) hexp
  refine Finset.prod_nonneg fun k _ ↦ ?_
  have hpos : (0 : ℝ) < γ (k + 2) := lt_of_lt_of_le zero_lt_one (hγ k)
  positivity

/-! ### The clock is positive -/

/-- The holding law puts no mass on `t ≤ 0`: a sojourn is positive, which K-C (1.7)'s density
says by vanishing there. -/
theorem holdMeasure_nonpos {d : ℝ} : holdMeasure d {t : ℝ | t ≤ 0} = 0 := by
  have hmeas : MeasurableSet {t : ℝ | t ≤ 0} := measurableSet_le measurable_id measurable_const
  have hdens : Measurable (holdDensity d) := by
    unfold holdDensity
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    exact (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)).ennreal_ofReal
  rw [holdMeasure, withDensity_apply _ hmeas]
  refine setLIntegral_eq_zero hmeas fun t ht ↦ ?_
  have ht0 : t ≤ 0 := ht
  unfold holdDensity
  rw [if_neg (by linarith : ¬ (0 : ℝ) < t)]
  simp

/-- **Every coordinate of the clock is positive, almost surely.** -/
theorem ae_holdProduct_pos {γ : ℕ → ℝ} (hγ : ∀ k, 0 < γ (k + 2)) :
    ∀ᵐ ω ∂(holdProduct γ hγ), ∀ k : ℕ, 0 < ω k := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (γ (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (hγ k)
  rw [ae_all_iff]
  intro k
  have hmeas : MeasurableSet {t : ℝ | t ≤ 0} := measurableSet_le measurable_id measurable_const
  have hnull : (holdProduct γ hγ) {ω : ℕ → ℝ | ω k ≤ 0} = 0 := by
    have hmap : Measure.map (Function.eval k) (holdProduct γ hγ)
        = holdMeasure (γ (k + 2)) := by
      unfold holdProduct
      exact (measurePreserving_eval_infinitePi
        (fun k : ℕ ↦ holdMeasure (γ (k + 2))) k).map_eq
    have hpre : {ω : ℕ → ℝ | ω k ≤ 0} = (Function.eval k) ⁻¹' {t : ℝ | t ≤ 0} := rfl
    rw [hpre, ← Measure.map_apply (by fun_prop) hmeas, hmap]
    exact holdMeasure_nonpos
  filter_upwards [measure_zero_iff_ae_notMem.mp hnull] with ω hω
  exact lt_of_not_ge hω

/-! ### From the vanishing products to an infinite descent time -/

/-- The truncated transform, with the coordinates clipped at zero so the sequence is
decreasing everywhere rather than only almost everywhere.  Clipping changes nothing on the
full-measure set where the clock is positive (`ae_holdProduct_pos`). -/
noncomputable def clippedTransform (m : ℕ) (ω : ℕ → ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-∑ k ∈ range m, max (ω k) 0))

theorem clippedTransform_measurable (m : ℕ) : Measurable (clippedTransform m) := by
  unfold clippedTransform
  refine (Measurable.exp ?_).ennreal_ofReal
  exact (Finset.measurable_sum _ fun k _ ↦ (measurable_pi_apply k).max measurable_const).neg

theorem clippedTransform_antitone : Antitone clippedTransform := by
  intro a b hab ω
  unfold clippedTransform
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hsub : range a ⊆ range b := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hab)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ le_max_right _ _)

/-- The clipped transform integrates to the same product: it agrees almost everywhere with the
transform `TransitTransform` computes. -/
theorem lintegral_clippedTransform {γ : ℕ → ℝ} (hγ : ∀ k, 0 < γ (k + 2)) (m : ℕ) :
    ∫⁻ ω, clippedTransform m ω ∂(holdProduct γ hγ)
      = ∏ k ∈ range m, ENNReal.ofReal (γ (k + 2) / (γ (k + 2) + 1)) := by
  rw [← lintegral_exp_neg_partialSum hγ (θ := 1) zero_le_one m]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_holdProduct_pos hγ] with ω hω
  unfold clippedTransform
  congr 2
  rw [one_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦ max_eq_left (le_of_lt (hω k))

/-- **The descent time is infinite, almost surely, when the condition fails.**

The products vanish (`tendsto_prod_ratio_zero`), monotone convergence over the decreasing
clipped transforms carries that inside the integral, and a nonnegative function with zero
integral is zero almost everywhere.  A vanishing `e^{-S}` is an infinite `S`.

With `EntranceLaw.ae_totalDescentTime_lt_top` this is an equivalence: the descent time is
almost surely finite exactly when `Σ γ_k⁻¹` converges. -/
theorem ae_totalDescentTime_eq_top {γ : ℕ → ℝ} (hγ1 : ∀ k, 1 ≤ γ (k + 2))
    (h : ¬ comesDownFromInfinity γ) :
    ∀ᵐ ω ∂(holdProduct γ (fun k ↦ lt_of_lt_of_le zero_lt_one (hγ1 k))),
      (∑' k : ℕ, ENNReal.ofReal (ω k)) = ⊤ := by
  set hγ : ∀ k, 0 < γ (k + 2) := fun k ↦ lt_of_lt_of_le zero_lt_one (hγ1 k) with hγdef
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (γ (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (hγ k)
  -- the products vanish, in `ℝ≥0∞`
  have hreal := tendsto_prod_ratio_zero hγ1 h
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ γ (k + 2) / (γ (k + 2) + 1) := by
    intro k
    have h1 : (0 : ℝ) < γ (k + 2) := hγ k
    have h2 : (0 : ℝ) < γ (k + 2) + 1 := by linarith
    positivity
  have hEN : Filter.Tendsto
      (fun m : ℕ ↦ ∏ k ∈ range m, ENNReal.ofReal (γ (k + 2) / (γ (k + 2) + 1)))
      Filter.atTop (nhds 0) := by
    have hof : ∀ m : ℕ, ∏ k ∈ range m, ENNReal.ofReal (γ (k + 2) / (γ (k + 2) + 1))
        = ENNReal.ofReal (∏ k ∈ range m, (γ (k + 2) / (γ (k + 2) + 1))) := by
      intro m
      rw [ENNReal.ofReal_prod_of_nonneg (fun k _ ↦ hnn k)]
    simp only [hof]
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa using this
  -- monotone convergence over the decreasing clipped transforms
  have hfin : ∫⁻ ω, clippedTransform 0 ω ∂(holdProduct γ hγ) ≠ ⊤ := by
    rw [lintegral_clippedTransform hγ 0]
    simp
  have hiInf : ∫⁻ ω, (⨅ m : ℕ, clippedTransform m ω) ∂(holdProduct γ hγ) = 0 := by
    rw [lintegral_iInf clippedTransform_measurable clippedTransform_antitone hfin]
    have hanti : Antitone fun m : ℕ ↦
        ∫⁻ ω, clippedTransform m ω ∂(holdProduct γ hγ) := by
      intro a b hab
      exact lintegral_mono (clippedTransform_antitone hab)
    have hlim := tendsto_atTop_iInf hanti
    have hlim2 : Filter.Tendsto
        (fun m : ℕ ↦ ∫⁻ ω, clippedTransform m ω ∂(holdProduct γ hγ))
        Filter.atTop (nhds 0) := by
      refine hEN.congr fun m ↦ ?_
      exact (lintegral_clippedTransform hγ m).symm
    exact tendsto_nhds_unique hlim hlim2
  have hzero : ∀ᵐ ω ∂(holdProduct γ hγ), (⨅ m : ℕ, clippedTransform m ω) = 0 := by
    have h0 := (lintegral_eq_zero_iff
      (Measurable.iInf clippedTransform_measurable)).mp hiInf
    filter_upwards [h0] with ω hω
    exact hω
  -- a vanishing infimum forces unbounded partial sums
  filter_upwards [hzero, ae_holdProduct_pos hγ] with ω hω hpos
  by_contra hfinite
  have hlt : (∑' k : ℕ, ENNReal.ofReal (ω k)) < ⊤ := lt_of_le_of_ne le_top hfinite
  set C : ℝ := (∑' k : ℕ, ENNReal.ofReal (ω k)).toReal with hC
  have hbound : ∀ m : ℕ, ∑ k ∈ range m, max (ω k) 0 ≤ C := by
    intro m
    have hpart : (∑ k ∈ range m, ENNReal.ofReal (ω k))
        ≤ ∑' k : ℕ, ENNReal.ofReal (ω k) := ENNReal.sum_le_tsum _
    have hsum : ENNReal.ofReal (∑ k ∈ range m, max (ω k) 0)
        = ∑ k ∈ range m, ENNReal.ofReal (ω k) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ le_max_right _ _)]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [max_eq_left (le_of_lt (hpos k))]
    rw [hC]
    refine (ENNReal.ofReal_le_iff_le_toReal hlt.ne).mp ?_
    rw [hsum]
    exact hpart
  have hlow : ∀ m : ℕ, ENNReal.ofReal (Real.exp (-C)) ≤ clippedTransform m ω := by
    intro m
    unfold clippedTransform
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.exp_le_exp, neg_le_neg_iff]
    exact hbound m
  have hpos' : (0 : ENNReal) < ENNReal.ofReal (Real.exp (-C)) := by
    simp [ENNReal.ofReal_pos, Real.exp_pos]
  have : ENNReal.ofReal (Real.exp (-C)) ≤ ⨅ m : ℕ, clippedTransform m ω :=
    le_iInf hlow
  rw [hω] at this
  exact absurd (le_antisymm this (zero_le _)) (ne_of_gt hpos')

/-- **The dichotomy, both directions.**  For a block count that drops one level at a time at
rate `γ_k`, the descent time from infinity is almost surely finite when `Σ γ_k⁻¹` converges
and almost surely infinite when it does not.  There is no middle case, and no set of positive
probability on which the answer differs from the series'.

`EntranceLaw.ae_totalDescentTime_lt_top` is the first half and `ae_totalDescentTime_eq_top`
the second.  Together they are Schweinsberg's criterion, for the binary case, as a statement
about the process rather than about its mean. -/
theorem ae_descent_dichotomy {γ : ℕ → ℝ} (hγ1 : ∀ k, 1 ≤ γ (k + 2)) :
    (comesDownFromInfinity γ →
        ∀ᵐ ω ∂(holdProduct γ (fun k ↦ lt_of_lt_of_le zero_lt_one (hγ1 k))),
          (∑' k : ℕ, ENNReal.ofReal (ω k)) < ⊤)
      ∧ (¬ comesDownFromInfinity γ →
        ∀ᵐ ω ∂(holdProduct γ (fun k ↦ lt_of_lt_of_le zero_lt_one (hγ1 k))),
          (∑' k : ℕ, ENNReal.ofReal (ω k)) = ⊤) :=
  ⟨fun h ↦ ae_totalDescentTime_lt_top _ h, fun h ↦ ae_totalDescentTime_eq_top hγ1 h⟩

/-- **The star coalescent does not come down from infinity, almost surely.**  Its rate is
`γ_b = b - 1`, at least one from `b = 2`, and the harmonic series diverges. -/
theorem star_ae_totalDescentTime_eq_top :
    ∀ᵐ ω ∂(holdProduct (fun b : ℕ ↦ (b : ℝ) - 1)
        (fun k ↦ lt_of_lt_of_le zero_lt_one (by push_cast; linarith))),
      (∑' k : ℕ, ENNReal.ofReal (ω k)) = ⊤ :=
  ae_totalDescentTime_eq_top (fun k ↦ by push_cast; linarith)
    star_not_comesDownFromInfinity

end Coalescent

end Descent
