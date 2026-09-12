/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw
import Mathlib.Probability.Distributions.Exponential

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Toward (C2) as a stochastic order: survival functions of the connection-time law

`Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw` builds the law of the time until a
pangenome report connects and proves the Laplace-transform order implied by (C2) of
`PANGENOME_HIDDEN_CLOCK.md` §5. The note states (C2) as a stochastic order,
`τ_q ≤_st Σ_{r=2}^{w} Exp(d_r)`. This file prepares that statement on survival functions.

## What is proved

* `survivalAt μ c = μ {y | c < y}`, the survival function of a law on durations at a real
  threshold, is antitone in the threshold (`survivalAt_antitone`) and certain below zero
  (`survivalAt_of_neg`).
* `survivalAt_conv`: the survival function of a convolution, `P(X + Y > c) = E_X P(Y > c - X)`.
* `survivalAt_bind_jumpStep`: the survival function of a mixture over one uniform jump is the
  average over the covers.
* `kingmanTransitLaw r`, the law of K-G's `T_r = Σ_{j=2}^{r} Exp(d_j)` built from the corpus holding
  law, is a probability law (`kingmanTransitLaw_isProbabilityMeasure`) and is stochastically
  increasing in `r` (`survivalAt_kingmanTransitLaw_le_succ`).
* `holdMeasure_eq_expMeasure`: the corpus holding law is Mathlib's exponential law.

## What is not yet proved

The thinning identity `Exp(d_r) = Exp(d_K) ∗ (p δ₀ + (1 - p) Exp(d_r))` with `p = d_r / d_K`, and
the stochastic domination of `connectionTimeLaw` by `kingmanTransitLaw` it gives, together with
`VisibleIntensityClock.deathRate_le_visibleIntensity`, by induction along covers.

## Empirical status

None. The bodies here are survival functions of supplied laws and identities between measures
built from the corpus holding law; no measurement can bear on them.
-/

set_option autoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset MeasureTheory
open scoped MeasureTheory NNReal ENNReal Classical

noncomputable section

/-! ### Survival functions -/

/-- **The survival function of a law on durations**, at a real threshold: `μ {y | c < y}`. -/
def survivalAt (μ : Measure ℝ≥0) (c : ℝ) : ℝ≥0∞ :=
  μ {y : ℝ≥0 | c < (y : ℝ)}

theorem measurableSet_survival (c : ℝ) : MeasurableSet {y : ℝ≥0 | c < (y : ℝ)} :=
  measurableSet_lt measurable_const measurable_coe_nnreal_real

/-- A survival function is antitone in the threshold. -/
theorem survivalAt_antitone (μ : Measure ℝ≥0) {c c' : ℝ} (h : c ≤ c') :
    survivalAt μ c' ≤ survivalAt μ c :=
  measure_mono fun _ hy ↦ lt_of_le_of_lt h hy

/-- A negative threshold is exceeded surely. -/
theorem survivalAt_of_neg {μ : Measure ℝ≥0} [IsProbabilityMeasure μ] {c : ℝ} (hc : c < 0) :
    survivalAt μ c = 1 := by
  have hset : {y : ℝ≥0 | c < (y : ℝ)} = Set.univ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact lt_of_lt_of_le hc y.2
  rw [survivalAt, hset, measure_univ]

/-- **The survival function of a convolution**: `P(X + Y > c) = E_X P(Y > c - X)`. -/
theorem survivalAt_conv (μ ν : Measure ℝ≥0) [SFinite ν] (c : ℝ) :
    survivalAt (μ ∗ ν) c = ∫⁻ x, survivalAt ν (c - x) ∂μ := by
  rw [survivalAt, ← lintegral_indicator_one (measurableSet_survival c),
    Measure.lintegral_conv (measurable_one.indicator (measurableSet_survival c))]
  refine lintegral_congr fun x ↦ ?_
  rw [survivalAt, ← lintegral_indicator_one (measurableSet_survival (c - x))]
  refine lintegral_congr fun y ↦ ?_
  simp only [Set.indicator, Set.mem_setOf_eq, NNReal.coe_add, sub_lt_iff_lt_add', Pi.one_apply]

/-- **The survival function of a mixture over one uniform jump** is the average over the covers. -/
theorem survivalAt_bind_jumpStep {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (μ : {η : ER n // Covers ξ η} → Measure ℝ≥0) (c : ℝ) :
    survivalAt ((jumpStep ξ hk).toMeasure.bind μ) c
      = (∑ η, survivalAt (μ η) c) * (((blocks ξ).choose 2 : ℕ) : ℝ≥0∞)⁻¹ := by
  haveI := measurableSingletonClass_ER n
  rw [survivalAt,
    Measure.bind_apply (measurableSet_survival c) (measurable_of_finite μ).aemeasurable,
    lintegral_jumpStep ξ hk]
  rfl

/-! ### Kingman's transit time -/

/-- **The law of K-G's transit time `T_r = Σ_{j=2}^{r} Exp(d_j)`**, one independent holding
duration per level. -/
def kingmanTransitLaw : ℕ → Measure ℝ≥0
  | 0 => Measure.dirac 0
  | 1 => Measure.dirac 0
  | m + 2 => holdDuration (deathRate (m + 2)) ∗ kingmanTransitLaw (m + 1)

theorem kingmanTransitLaw_isProbabilityMeasure :
    ∀ m : ℕ, IsProbabilityMeasure (kingmanTransitLaw m)
  | 0 => show IsProbabilityMeasure (Measure.dirac (0 : ℝ≥0)) from inferInstance
  | 1 => show IsProbabilityMeasure (Measure.dirac (0 : ℝ≥0)) from inferInstance
  | m + 2 => by
      haveI := holdDuration_isProbabilityMeasure (deathRate_add_two_pos m)
      haveI := kingmanTransitLaw_isProbabilityMeasure (m + 1)
      show IsProbabilityMeasure
        (holdDuration (deathRate (m + 2)) ∗ kingmanTransitLaw (m + 1))
      infer_instance

/-- **`T_r` is stochastically increasing in `r`**: one more level adds a nonnegative holding
duration. -/
theorem survivalAt_kingmanTransitLaw_le_succ (m : ℕ) (c : ℝ) :
    survivalAt (kingmanTransitLaw m) c ≤ survivalAt (kingmanTransitLaw (m + 1)) c := by
  rcases m with _ | m
  · exact le_rfl
  · haveI := holdDuration_isProbabilityMeasure (deathRate_add_two_pos m)
    haveI := kingmanTransitLaw_isProbabilityMeasure (m + 1)
    rw [show kingmanTransitLaw (m + 1 + 1)
        = holdDuration (deathRate (m + 2)) ∗ kingmanTransitLaw (m + 1) from rfl,
      survivalAt_conv]
    calc survivalAt (kingmanTransitLaw (m + 1)) c
        = ∫⁻ _x, survivalAt (kingmanTransitLaw (m + 1)) c
            ∂(holdDuration (deathRate (m + 2))) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ x, survivalAt (kingmanTransitLaw (m + 1)) (c - x)
            ∂(holdDuration (deathRate (m + 2))) :=
          lintegral_mono fun x ↦ survivalAt_antitone _ (by linarith [NNReal.coe_nonneg x])

/-! ### The corpus holding law is the exponential law -/

/-- **`holdMeasure d` is Mathlib's `expMeasure d`**: the two densities differ only at `t = 0`. -/
theorem holdMeasure_eq_expMeasure (d : ℝ) : holdMeasure d = ProbabilityTheory.expMeasure d := by
  rw [holdMeasure, ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  refine withDensity_congr_ae ?_
  have hnull : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun t ht ↦ ?_) hnull
  simp only [Set.mem_setOf_eq] at ht
  by_contra h0
  have hne : t ≠ 0 := h0
  apply ht
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · simp only [holdDensity, if_neg (not_lt.mpr hneg.le), ProbabilityTheory.gammaPDF,
      ProbabilityTheory.gammaPDFReal, if_neg (not_le.mpr hneg), ENNReal.ofReal_zero]
  · simp only [holdDensity, if_pos hpos, ProbabilityTheory.gammaPDF,
      ProbabilityTheory.gammaPDFReal, if_pos hpos.le, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one]

/-! ### The tails of a holding duration -/

theorem measurable_holdDensity (d : ℝ) : Measurable (holdDensity d) := by
  unfold holdDensity
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)).ennreal_ofReal

/-- The left tail of the holding law: `P(H ≤ c) = 1 - e^{-dc}`, Mathlib's exponential CDF. -/
theorem holdMeasure_Iic {d c : ℝ} (hd : 0 < d) (hc : 0 ≤ c) :
    holdMeasure d (Set.Iic c) = ENNReal.ofReal (1 - Real.exp (-(d * c))) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure hd
  rw [holdMeasure_eq_expMeasure, ← ProbabilityTheory.ofReal_cdf,
    ProbabilityTheory.cdf_expMeasure_eq hd, if_pos hc]

/-- The right tail of the holding law: `P(H > c) = e^{-dc}`. -/
theorem holdMeasure_Ioi {d c : ℝ} (hd : 0 < d) (hc : 0 ≤ c) :
    holdMeasure d (Set.Ioi c) = ENNReal.ofReal (Real.exp (-(d * c))) := by
  haveI := holdMeasure_isProbabilityMeasure hd
  have hle : Real.exp (-(d * c)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hd.le hc))
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, holdMeasure_Iic hd hc,
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by linarith : (0 : ℝ) ≤ 1 - Real.exp (-(d * c))), sub_sub_cancel]

/-- **The survival function of a holding duration**: `P(H > c) = e^{-dc}` for `c ≥ 0`. -/
theorem survivalAt_holdDuration {d c : ℝ} (hd : 0 < d) (hc : 0 ≤ c) :
    survivalAt (holdDuration d) c = ENNReal.ofReal (Real.exp (-(d * c))) := by
  have hpre : Real.toNNReal ⁻¹' {y : ℝ≥0 | c < (y : ℝ)} = Set.Ioi c := by
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.coe_toNNReal', Set.mem_Ioi]
    constructor
    · intro h
      by_contra ht
      have hmax : max t 0 ≤ c := max_le (not_lt.mp ht) hc
      linarith
    · intro h
      exact lt_of_lt_of_le h (le_max_left t 0)
  rw [survivalAt, holdDuration,
    Measure.map_apply measurable_real_toNNReal (measurableSet_survival c), hpre,
    holdMeasure_Ioi hd hc]

/-! ### Two holding durations in sequence -/

/-- A holding density at rate `dK` tilted by `e^{dr t}` is a multiple of the holding density at
rate `dK - dr`. -/
theorem holdDensity_mul_exp {dK dr c : ℝ} (hr : 0 < dr) (hK : dr < dK) (t : ℝ) :
    holdDensity dK t * ENNReal.ofReal (Real.exp (-(dr * (c - t))))
      = ENNReal.ofReal (dK / (dK - dr) * Real.exp (-(dr * c))) * holdDensity (dK - dr) t := by
  have hgap : dK - dr ≠ 0 := by linarith
  unfold holdDensity
  by_cases ht : 0 < t
  · have h1 : 0 ≤ dK * Real.exp (-(dK * t)) := mul_nonneg (by linarith) (Real.exp_pos _).le
    have h2 : 0 ≤ dK / (dK - dr) * Real.exp (-(dr * c)) :=
      mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le
    rw [if_pos ht, if_pos ht, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
    congr 1
    have e1 : Real.exp (-(dK * t)) * Real.exp (-(dr * (c - t)))
        = Real.exp (-(dr * c)) * Real.exp (-((dK - dr) * t)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [show dK / (dK - dr) * Real.exp (-(dr * c)) * ((dK - dr) * Real.exp (-((dK - dr) * t)))
        = dK / (dK - dr) * (dK - dr) * (Real.exp (-(dr * c)) * Real.exp (-((dK - dr) * t))) by
          ring,
      div_mul_cancel₀ dK hgap, ← e1]
    ring
  · rw [if_neg ht, if_neg ht, zero_mul, mul_zero]

/-- The tilted holding density integrated up to `c`. -/
theorem setLIntegral_Iic_holdDensity_mul_exp {dK dr c : ℝ} (hr : 0 < dr) (hK : dr < dK) :
    ∫⁻ t in Set.Iic c, holdDensity dK t * ENNReal.ofReal (Real.exp (-(dr * (c - t))))
      = ENNReal.ofReal (dK / (dK - dr) * Real.exp (-(dr * c)))
        * holdMeasure (dK - dr) (Set.Iic c) := by
  rw [holdMeasure, withDensity_apply _ measurableSet_Iic,
    ← lintegral_const_mul _ (measurable_holdDensity _)]
  exact setLIntegral_congr_fun measurableSet_Iic fun t _ ↦ holdDensity_mul_exp hr hK t

/-- **The survival function of two holding durations in sequence**, rates `dK > dr > 0`:
`P(H_K + H_r > c) = (dK/(dK - dr)) e^{-dr c} (1 - e^{-(dK - dr) c}) + e^{-dK c}`. -/
theorem survivalAt_holdDuration_conv {dK dr c : ℝ} (hr : 0 < dr) (hK : dr < dK) (hc : 0 ≤ c) :
    survivalAt (holdDuration dK ∗ holdDuration dr) c
      = ENNReal.ofReal (dK / (dK - dr) * Real.exp (-(dr * c)))
          * ENNReal.ofReal (1 - Real.exp (-((dK - dr) * c)))
        + ENNReal.ofReal (Real.exp (-(dK * c))) := by
  haveI := holdDuration_isProbabilityMeasure hr
  have hmono : Monotone fun x : ℝ≥0 ↦ survivalAt (holdDuration dr) (c - x) := fun x x' hxx' ↦
    survivalAt_antitone _ (by linarith [(NNReal.coe_le_coe.mpr hxx' : (x : ℝ) ≤ x')])
  have hF := hmono.measurable
  have hG : Measurable fun t : ℝ ↦ survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ)) :=
    hF.comp measurable_real_toNNReal
  have hsplit : ∫⁻ t, holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ))
      = ∫⁻ t in Set.Iic c,
          holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ))
        + ∫⁻ t in Set.Ioi c,
          holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ)) := by
    rw [← Set.compl_Iic]
    exact (lintegral_add_compl _ measurableSet_Iic).symm
  have hleft : ∫⁻ t in Set.Iic c,
        holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ))
      = ∫⁻ t in Set.Iic c, holdDensity dK t * ENNReal.ofReal (Real.exp (-(dr * (c - t)))) := by
    refine setLIntegral_congr_fun measurableSet_Iic fun t ht ↦ ?_
    by_cases ht0 : 0 < t
    · rw [Real.coe_toNNReal t ht0.le, survivalAt_holdDuration hr (sub_nonneg.mpr ht)]
    · simp only [holdDensity, if_neg ht0, zero_mul]
  have hright : ∫⁻ t in Set.Ioi c,
        holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ))
      = ∫⁻ t in Set.Ioi c, holdDensity dK t := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : 0 ≤ t := hc.trans (le_of_lt ht)
    have hneg : c - (Real.toNNReal t : ℝ) < 0 := by
      rw [Real.coe_toNNReal t ht0]
      linarith [Set.mem_Ioi.mp ht]
    rw [survivalAt_of_neg hneg, mul_one]
  calc survivalAt (holdDuration dK ∗ holdDuration dr) c
      = ∫⁻ x, survivalAt (holdDuration dr) (c - x) ∂(holdDuration dK) := survivalAt_conv _ _ c
    _ = ∫⁻ t, holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ)) := by
        rw [show holdDuration dK = (holdMeasure dK).map Real.toNNReal from rfl,
          lintegral_map hF measurable_real_toNNReal,
          show holdMeasure dK = volume.withDensity (holdDensity dK) from rfl,
          lintegral_withDensity_eq_lintegral_mul _ (measurable_holdDensity dK) hG]
        rfl
    _ = _ := by
        refine hsplit.trans ?_
        have hgap : 0 < dK - dr := by linarith
        have hdK : 0 < dK := by linarith
        have hA := (hleft.trans (setLIntegral_Iic_holdDensity_mul_exp hr hK)).trans
          (congrArg (fun z ↦ ENNReal.ofReal (dK / (dK - dr) * Real.exp (-(dr * c))) * z)
            (holdMeasure_Iic hgap hc))
        have hB : ∫⁻ t in Set.Ioi c, holdDensity dK t = ENNReal.ofReal (Real.exp (-(dK * c))) :=
          (withDensity_apply _ measurableSet_Ioi).symm.trans (holdMeasure_Ioi hdK hc)
        exact congrArg₂ (· + ·) hA (hright.trans hB)

end

end Descent.Pangenome.GraphCoalescent
