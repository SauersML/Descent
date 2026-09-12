/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw
import Mathlib.Probability.Distributions.Exponential

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# (C2) as a stochastic order: the report connects no later than Kingman's transit time

`Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw` builds the law of the time until a
pangenome report connects and proves the Laplace-transform order implied by (C2) of
`PANGENOME_HIDDEN_CLOCK.md` §5. The note states (C2) as a stochastic order,
`τ_q ≤_st Σ_{r=2}^{w} Exp(d_r)`. This file proves it, on survival functions.

## What is proved

* `survivalAt μ c = μ {y | c < y}`, the survival function of a law on durations at a real
  threshold, is antitone in the threshold (`survivalAt_antitone`) and certain below zero
  (`survivalAt_of_neg`). Convolution and one-jump mixtures act on it by integration and averaging
  (`survivalAt_conv`, `survivalAt_bind_jumpStep`, `survivalAt_add_smul`).
* `kingmanTransitLaw r`, the law of K-G's `T_r = Σ_{j=2}^{r} Exp(d_j)` built from the corpus holding
  law, is a probability law and is stochastically increasing in `r`
  (`survivalAt_kingmanTransitLaw_le_succ`).
* The corpus holding law is Mathlib's exponential law (`holdMeasure_eq_expMeasure`), so its tails
  are `e^{-dc}` and `1 - e^{-dc}` (`holdMeasure_Ioi`, `holdMeasure_Iic`,
  `survivalAt_holdDuration`); two holding durations in sequence survive as
  `survivalAt_holdDuration_conv` says.
* **The thinning identity** `Exp(d_r) = p Exp(d_K) + (1 - p) Exp(d_K) ∗ Exp(d_r)` with `p = d_r/d_K`,
  `d_r < d_K` (`holdDuration_thinning`): a slow clock is a fast clock that rings through with
  probability `p`. Applied to `T_r = Exp(d_r) ∗ T_{r-1}` it thins Kingman's transit time at the
  faster rate of the labeled chain (`survivalAt_kingmanTransitLaw_thinning`).
* **(C2)**, `survivalAt_connectionTimeLaw_le`: from every labeled state `ξ`,
  `P(τ_q > c) ≤ P(T_r > c)` for all `c`, with `r` the report width. By induction along covers: one
  holding step at rate `d_K`, then at least `C(r, 2)` of the `C(K, 2)` covers are visible
  (`VisibleIntensityClock.choose_two_le_visibleIntensity`), and moving weight from `T_r` to the
  shorter `T_{r-1}` can only lower the survival (`sum_survivalAt_kingmanTransitLaw_le`); the
  thinning identity closes the step. At the panel, `survivalAt_connectionTimeLaw_bot_le` is
  `τ_q ≤_st T_w`.

## What is narrower than the note

The note derives (C2) through conditional quantile couplings of the continuous-time chain. What is
proved is the survival-function inequality for `ConnectionClockPathLaw.connectionTimeLaw`, the law
built by first-step recursion from the corpus jump and holding laws; no coupling is constructed.

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
      = (∫⁻ t in Set.Iic c,
          holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ)))
        + ∫⁻ t in Set.Ioi c,
          holdDensity dK t * survivalAt (holdDuration dr) (c - (Real.toNNReal t : ℝ)) := by
    rw [← Set.compl_Iic]
    exact (lintegral_add_compl _ (measurableSet_Iic (a := c))).symm
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

/-! ### The thinning identity -/

/-- The survival function of a mixture of two laws. -/
theorem survivalAt_add_smul (p q : ℝ≥0∞) (μ ν : Measure ℝ≥0) (c : ℝ) :
    survivalAt (p • μ + q • ν) c = p * survivalAt μ c + q * survivalAt ν c := by
  simp only [survivalAt, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- Delaying the threshold by a duration can only raise the survival probability. -/
theorem monotone_survivalAt_sub (ν : Measure ℝ≥0) (c : ℝ) :
    Monotone fun x : ℝ≥0 ↦ survivalAt ν (c - x) := fun x x' hxx' ↦
  survivalAt_antitone _ (by linarith [(NNReal.coe_le_coe.mpr hxx' : (x : ℝ) ≤ x')])

/-- Kingman's death rate is monotone on the informative range. -/
theorem deathRate_le_deathRate {m K : ℕ} (hmK : m + 2 ≤ K) :
    deathRate (m + 2) ≤ deathRate K := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmK
  rw [deathRate_succ_succ, show m + 2 + j = (m + j) + 2 by ring, deathRate_succ_succ]
  push_cast
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- **The thinning identity.** A holding duration at rate `dr` is, with probability `p = dr/dK`,
one holding duration at the faster rate `dK`, and otherwise one at rate `dK` followed by a fresh
one at rate `dr`. -/
theorem holdDuration_thinning {dK dr : ℝ} (hr : 0 < dr) (hK : dr < dK) :
    holdDuration dr = ENNReal.ofReal (dr / dK) • holdDuration dK
      + ENNReal.ofReal (1 - dr / dK) • (holdDuration dK ∗ holdDuration dr) := by
  have hdK : 0 < dK := by linarith
  have hgap : 0 < dK - dr := by linarith
  haveI := holdDuration_isProbabilityMeasure hr
  haveI := holdDuration_isProbabilityMeasure hdK
  have hp0 : 0 ≤ dr / dK := div_nonneg hr.le hdK.le
  have hq0 : 0 ≤ 1 - dr / dK := by
    rw [sub_nonneg, div_le_one hdK]
    exact hK.le
  have hsurv : ∀ a : ℝ≥0, survivalAt (holdDuration dr) a
      = survivalAt (ENNReal.ofReal (dr / dK) • holdDuration dK
          + ENNReal.ofReal (1 - dr / dK) • (holdDuration dK ∗ holdDuration dr)) a := by
    intro a
    have ha : (0 : ℝ) ≤ a := NNReal.coe_nonneg a
    rw [survivalAt_add_smul, survivalAt_holdDuration hr ha, survivalAt_holdDuration hdK ha,
      survivalAt_holdDuration_conv hr hK ha]
    have hEl : Real.exp (-((dK - dr) * a)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hgap.le ha))
    have h1 : 0 ≤ dK / (dK - dr) * Real.exp (-(dr * a)) :=
      mul_nonneg (div_nonneg hdK.le hgap.le) (Real.exp_pos _).le
    have h2 : 0 ≤ dK / (dK - dr) * Real.exp (-(dr * a)) * (1 - Real.exp (-((dK - dr) * a))) :=
      mul_nonneg h1 (by linarith)
    have h3 : 0 ≤ dr / dK * Real.exp (-(dK * a)) := mul_nonneg hp0 (Real.exp_pos _).le
    have h4 : 0 ≤ (1 - dr / dK)
        * (dK / (dK - dr) * Real.exp (-(dr * a)) * (1 - Real.exp (-((dK - dr) * a)))
          + Real.exp (-(dK * a))) :=
      mul_nonneg hq0 (add_nonneg h2 (Real.exp_pos _).le)
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add h2 (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_add h3 h4]
    congr 1
    have hexp : Real.exp (-(dr * a)) * Real.exp (-((dK - dr) * a)) = Real.exp (-(dK * a)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hi1 : dK * dK⁻¹ = 1 := mul_inv_cancel₀ hdK.ne'
    have hi2 : (dK - dr) * (dK - dr)⁻¹ = 1 := mul_inv_cancel₀ hgap.ne'
    linear_combination hexp
      - Real.exp (-(dr * a)) * (1 - Real.exp (-((dK - dr) * a))) * hi2
      + Real.exp (-(dr * a)) * (1 - Real.exp (-((dK - dr) * a))) * dr * (dK - dr)⁻¹ * hi1
  have hmass : (ENNReal.ofReal (dr / dK) • holdDuration dK
      + ENNReal.ofReal (1 - dr / dK) • (holdDuration dK ∗ holdDuration dr)) Set.univ = 1 := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add hp0 hq0,
      show dr / dK + (1 - dr / dK) = 1 by ring, ENNReal.ofReal_one]
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  have hIoi : {y : ℝ≥0 | ((a : ℝ≥0) : ℝ) < (y : ℝ)} = Set.Ioi a := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, NNReal.coe_lt_coe]
  have hS := hsurv a
  rw [survivalAt, survivalAt, hIoi] at hS
  have hfin : (ENNReal.ofReal (dr / dK) • holdDuration dK
      + ENNReal.ofReal (1 - dr / dK) • (holdDuration dK ∗ holdDuration dr)) (Set.Ioi a) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hmass]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ _))
  rw [← Set.compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi hfin, measure_univ, hmass, hS]

/-- **Kingman's transit time, thinned at a faster rate.** For `r = m + 2 ≤ K` and `p = d_r/d_K`,
`P(T_r > c) = E[p P(T_{r-1} > c - H) + (1 - p) P(T_r > c - H)]` with `H` a holding duration at rate
`d_K`. -/
theorem survivalAt_kingmanTransitLaw_thinning {K m : ℕ} (hmK : m + 2 ≤ K) (c : ℝ) :
    ∫⁻ x, (ENNReal.ofReal (deathRate (m + 2) / deathRate K)
          * survivalAt (kingmanTransitLaw (m + 1)) (c - x)
        + ENNReal.ofReal (1 - deathRate (m + 2) / deathRate K)
          * survivalAt (kingmanTransitLaw (m + 2)) (c - x)) ∂(holdDuration (deathRate K))
      = survivalAt (kingmanTransitLaw (m + 2)) c := by
  have hr := deathRate_add_two_pos m
  have hdK := deathRate_pos (show 2 ≤ K by omega)
  haveI := holdDuration_isProbabilityMeasure hr
  haveI := holdDuration_isProbabilityMeasure hdK
  haveI := kingmanTransitLaw_isProbabilityMeasure (m + 1)
  haveI := kingmanTransitLaw_isProbabilityMeasure (m + 2)
  have hT : kingmanTransitLaw (m + 2)
      = holdDuration (deathRate (m + 2)) ∗ kingmanTransitLaw (m + 1) := rfl
  rw [lintegral_add_left ((monotone_survivalAt_sub _ c).measurable.const_mul _),
    lintegral_const_mul _ (monotone_survivalAt_sub _ c).measurable,
    lintegral_const_mul _ (monotone_survivalAt_sub _ c).measurable,
    ← survivalAt_conv, ← survivalAt_conv, ← survivalAt_add_smul]
  rcases (deathRate_le_deathRate hmK).lt_or_eq with hlt | heq
  · rw [hT, ← Measure.conv_assoc, ← Measure.conv_smul_left, ← Measure.conv_smul_left,
      ← Measure.add_conv, ← holdDuration_thinning hr hlt]
  · rw [heq, div_self hdK.ne', sub_self, ENNReal.ofReal_one, ENNReal.ofReal_zero, one_smul,
      zero_smul, add_zero, hT, heq]

/-! ### The stochastic domination -/

/-- The pair count, as an extended real, is Kingman's death rate. -/
theorem choose_two_eq_ofReal_deathRate (k : ℕ) :
    ((k.choose 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (deathRate k) := by
  have h := card_covers_eq_deathRate (Delta k)
  rw [card_covers, blocks_bot] at h
  rw [← h, ENNReal.ofReal_natCast]

/-- The visible weight of the thinning, as a ratio of pair counts. -/
theorem choose_two_mul_inv_choose_two {m K : ℕ} (hmK : m + 2 ≤ K) :
    (((m + 2).choose 2 : ℕ) : ℝ≥0∞) * ((K.choose 2 : ℕ) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal (deathRate (m + 2) / deathRate K) := by
  rw [choose_two_eq_ofReal_deathRate, choose_two_eq_ofReal_deathRate,
    ENNReal.ofReal_div_of_pos (deathRate_pos (show 2 ≤ K by omega)), div_eq_mul_inv]

/-- The invisible weight of the thinning, as a ratio of pair counts. -/
theorem choose_two_sub_mul_inv_choose_two {m K : ℕ} (hmK : m + 2 ≤ K) :
    ((K.choose 2 - (m + 2).choose 2 : ℕ) : ℝ≥0∞) * ((K.choose 2 : ℕ) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal (1 - deathRate (m + 2) / deathRate K) := by
  have hdK := deathRate_pos (show 2 ≤ K by omega)
  have hM0 : ((K.choose 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [choose_two_eq_ofReal_deathRate]
    exact ENNReal.ofReal_pos.mpr hdK |>.ne'
  have hMt : ((K.choose 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.natCast_sub, ENNReal.sub_mul fun _ _ ↦ ENNReal.inv_ne_top.mpr hM0,
    ENNReal.mul_inv_cancel hM0 hMt, choose_two_mul_inv_choose_two hmK,
    ENNReal.ofReal_sub 1 (div_nonneg (deathRate_add_two_pos m).le hdK.le), ENNReal.ofReal_one]

/-- **The covers of a state average the Kingman survivals below the thinning weights.** The
visible covers take the report to `r - 1` components and the invisible ones keep `r`; there are
at least `C(r, 2)` visible covers, and `T_{r-1}` survives no longer than `T_r`. -/
theorem sum_survivalAt_kingmanTransitLaw_le {n m : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hr : blocks (observed s ξ) = m + 2) (c : ℝ) :
    ∑ η : {η : ER n // Covers ξ η}, survivalAt (kingmanTransitLaw (blocks (observed s η.1))) c
      ≤ (((m + 2).choose 2 : ℕ) : ℝ≥0∞) * survivalAt (kingmanTransitLaw (m + 1)) c
        + (((blocks ξ).choose 2 - (m + 2).choose 2 : ℕ) : ℝ≥0∞)
          * survivalAt (kingmanTransitLaw (m + 2)) c := by
  have hterm : ∀ η : {η : ER n // Covers ξ η},
      survivalAt (kingmanTransitLaw (blocks (observed s η.1))) c
        = if Covers (observed s ξ) (observed s η.1)
          then survivalAt (kingmanTransitLaw (m + 1)) c
          else survivalAt (kingmanTransitLaw (m + 2)) c := by
    intro η
    by_cases hvis : Covers (observed s ξ) (observed s η.1)
    · rw [if_pos hvis, show blocks (observed s η.1) = m + 1 by have := hvis.2; omega]
    · rw [if_neg hvis]
      rcases observed_eq_or_covers s η.2 with heq | hcov
      · rw [heq, hr]
      · exact absurd hcov hvis
  have hsplit := filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset {η : ER n // Covers ξ η}))
    fun η : {η : ER n // Covers ξ η} ↦ Covers (observed s ξ) (observed s η.1)
  rw [card_univ, card_covers_fintype] at hsplit
  have hlow : (m + 2).choose 2 ≤ visibleIntensity s ξ := by
    have h := choose_two_le_visibleIntensity s ξ
    rwa [hr] at h
  have hS := survivalAt_kingmanTransitLaw_le_succ (m + 1) c
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hlow
  have hvisCard : (univ.filter fun η : {η : ER n // Covers ξ η} ↦
      Covers (observed s ξ) (observed s η.1)).card = (m + 2).choose 2 + e := he
  have hinvCard : (univ.filter fun η : {η : ER n // Covers ξ η} ↦
      ¬ Covers (observed s ξ) (observed s η.1)).card + e
        = (blocks ξ).choose 2 - (m + 2).choose 2 := by
    omega
  rw [sum_congr rfl fun η _ ↦ hterm η, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    hvisCard, ← hinvCard, Nat.cast_add, Nat.cast_add, add_mul, add_mul]
  calc (((m + 2).choose 2 : ℕ) : ℝ≥0∞) * survivalAt (kingmanTransitLaw (m + 1)) c
        + (e : ℝ≥0∞) * survivalAt (kingmanTransitLaw (m + 1)) c
        + (((univ.filter fun η : {η : ER n // Covers ξ η} ↦
            ¬ Covers (observed s ξ) (observed s η.1)).card : ℕ) : ℝ≥0∞)
          * survivalAt (kingmanTransitLaw (m + 2)) c
      ≤ (((m + 2).choose 2 : ℕ) : ℝ≥0∞) * survivalAt (kingmanTransitLaw (m + 1)) c
        + (e : ℝ≥0∞) * survivalAt (kingmanTransitLaw (m + 2)) c
        + (((univ.filter fun η : {η : ER n // Covers ξ η} ↦
            ¬ Covers (observed s ξ) (observed s η.1)).card : ℕ) : ℝ≥0∞)
          * survivalAt (kingmanTransitLaw (m + 2)) c := by
        gcongr
    _ = _ := by ring

/-- **(C2), the stochastic order.** From any labeled state the report connects no later, in the
stochastic order, than Kingman's transit time at the report width:
`P(τ_q > c) ≤ P(T_r > c)` for every threshold `c`. -/
theorem survivalAt_connectionTimeLaw_le {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∀ c : ℝ, survivalAt (connectionTimeLaw s ξ) c
      ≤ survivalAt (kingmanTransitLaw (blocks (observed s ξ))) c := by
  induction ξ using covers_induction with
  | step ξ ih =>
    intro c
    rw [connectionTimeLaw_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [dif_pos hr]
      have hT : kingmanTransitLaw (blocks (observed s ξ)) = Measure.dirac 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with h | h <;> rw [h] <;> rfl
      rw [hT]
    · rw [dif_neg hr]
      obtain ⟨m, hm⟩ : ∃ m, blocks (observed s ξ) = m + 2 := ⟨blocks (observed s ξ) - 2, by omega⟩
      have hk := two_le_blocks_of_not_le_one s hr
      have hmK : m + 2 ≤ blocks ξ := hm ▸ blocks_antitone (le_observed s ξ)
      haveI := measurableSingletonClass_ER n
      haveI := isProbabilityMeasure_bind_jumpStep ξ hk (fun η ↦ connectionTimeLaw s η.1)
        fun η ↦ connectionTimeLaw_isProbabilityMeasure s η.1
      rw [survivalAt_conv, hm, ← survivalAt_kingmanTransitLaw_thinning hmK c]
      refine lintegral_mono fun x ↦ ?_
      rw [survivalAt_bind_jumpStep, ← choose_two_mul_inv_choose_two hmK,
        ← choose_two_sub_mul_inv_choose_two hmK]
      calc (∑ η : {η : ER n // Covers ξ η}, survivalAt (connectionTimeLaw s η.1) (c - x))
            * ((((blocks ξ).choose 2 : ℕ) : ℝ≥0∞))⁻¹
          ≤ (∑ η : {η : ER n // Covers ξ η},
              survivalAt (kingmanTransitLaw (blocks (observed s η.1))) (c - x))
            * ((((blocks ξ).choose 2 : ℕ) : ℝ≥0∞))⁻¹ :=
            mul_le_mul_right' (sum_le_sum fun η _ ↦ ih η.1 η.2 (c - x)) _
        _ ≤ ((((m + 2).choose 2 : ℕ) : ℝ≥0∞) * survivalAt (kingmanTransitLaw (m + 1)) (c - x)
              + (((blocks ξ).choose 2 - (m + 2).choose 2 : ℕ) : ℝ≥0∞)
                * survivalAt (kingmanTransitLaw (m + 2)) (c - x))
            * ((((blocks ξ).choose 2 : ℕ) : ℝ≥0∞))⁻¹ :=
            mul_le_mul_right' (sum_survivalAt_kingmanTransitLaw_le s hm (c - x)) _
        _ = _ := by ring

/-- **(C2) at the panel**: `P(τ_q > c) ≤ P(T_w > c)`, the report of the panel's coalescent connects
no later, in the stochastic order, than the Kingman `w`-coalescent of
`Descent.Pangenome.GraphCoalescent.Reduction` reaches its root. -/
theorem survivalAt_connectionTimeLaw_bot_le {n : ℕ} (s : Fin n → Fin n) (c : ℝ) :
    survivalAt (connectionTimeLaw s ⊥) c ≤ survivalAt (kingmanTransitLaw (Linkage.width s)) c := by
  have h := survivalAt_connectionTimeLaw_le s ⊥ c
  rw [observed_bot, blocks_graphKer] at h
  exact h

end

end Descent.Pangenome.GraphCoalescent
