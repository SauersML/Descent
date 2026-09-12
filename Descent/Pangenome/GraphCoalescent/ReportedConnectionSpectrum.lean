/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockStochasticOrder

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The spectrum of the reported connection clock

§6 of the pangenome hidden-clock note ends with a spectral remark: the survival function of the
reported connection time `τ_q` is a linear combination of `e^{-d_k t}` for `k = 2, …, n`, with
`d_k = C(k, 2)`.  This file proves it for the law of the connection time that
`Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw` builds from the holding-time
decomposition.  From a state with `K` blocks and an unconnected report, that law is a holding
duration of rate `d_K` convolved with the connection time from a uniformly chosen cover.

## The analytic step

`survivalAt_holdDuration_conv_combination`: suppose the survival function of `ν` is
`∑_k a_k e^{-r_k u}` for `u ≥ 0`, with `0 < r_k < d` and real coefficients of any sign.  Then the
survival function of `holdDuration d ∗ ν` is `e^{-dc} + ∑_k a_k d/(d - r_k) (e^{-r_k c} - e^{-dc})`.
The coefficients can be negative, so the proof goes through real integrals.  Each exponential term
integrates the tilted holding density of
`ConnectionClockStochasticOrder.setLIntegral_Iic_holdDensity_mul_exp`, and the threshold is
exceeded surely once the holding time passes it (`survivalAt_of_neg`).

## The coefficients

`spectralCoeff s ξ k` is defined by recursion along covers, with the block count as fuel.  It
vanishes on a connected report.  Otherwise, with `K = blocks ξ` and `coverAverage s ξ k` the
average of the covers' coefficients,

  `spectralCoeff s ξ k = d_K/(d_K - d_k) · coverAverage s ξ k` for `k < K`, and
  `spectralCoeff s ξ K = 1 - ∑_{k=2}^{K-1} d_K/(d_K - d_k) · coverAverage s ξ k`
  (`spectralCoeff_eq`).

`survivalAt_connectionTimeLaw_toReal` proves `P(τ_q > c) = ∑_{k=2}^{K} spectralCoeff s ξ k e^{-d_k c}`
from `ξ`, for `c ≥ 0`.  `survivalAt_connectionTimeLaw_bot` is the note's statement from `⊥`, over
`k = 2, …, n`.  The rates are distinct because the death rates increase strictly
(`deathRate_lt_deathRate`), and that is what the convolution step needs.

## Scope

The law here is the first-step law `ConnectionClockPathLaw.connectionTimeLaw`.  Its mean is the
mean under the trajectory-and-clock law of `ReportedConnectionClock`
(`ReportedConnectionTies.connectionTime_mean_eq_lintegral_connectionTimeLaw`).  The survival
functions of the two laws are not identified here.

## Empirical status

None.  The bodies are survival functions of measures built from the corpus holding and jump laws,
a finite recursion along covers, and real integrals of exponentials, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset MeasureTheory
open scoped NNReal ENNReal Classical

/-- The death rates increase strictly from one block on. -/
theorem deathRate_lt_deathRate {k K : ℕ} (hk : 1 ≤ k) (hkK : k < K) :
    deathRate k < deathRate K := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK' : (k : ℝ) + 1 ≤ K := by exact_mod_cast hkK
  have hpos : 0 < ((K : ℝ) - k) * ((K : ℝ) + k - 1) := mul_pos (by linarith) (by linarith)
  unfold deathRate Descent.Core.pairCount
  nlinarith [hpos]

/-! ### A holding duration convolved with an exponential mixture -/

/-- **The convolution step.**  If the survival function of `ν` is `∑_{k∈T} a_k e^{-r_k u}` on
`u ≥ 0`, with `0 < r_k < d`, then the survival function of `holdDuration d ∗ ν` at `c ≥ 0` is
`e^{-dc} + ∑_k a_k d/(d - r_k) (e^{-r_k c} - e^{-dc})`. -/
theorem survivalAt_holdDuration_conv_combination {d : ℝ} (hd : 0 < d) {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {T : Finset ℕ} {r a : ℕ → ℝ} (hr : ∀ k ∈ T, 0 < r k)
    (hrd : ∀ k ∈ T, r k < d)
    (hν : ∀ u : ℝ, 0 ≤ u → (survivalAt ν u).toReal = ∑ k ∈ T, a k * Real.exp (-(r k * u)))
    {c : ℝ} (hc : 0 ≤ c) :
    (survivalAt (holdDuration d ∗ ν) c).toReal
      = Real.exp (-(d * c))
        + ∑ k ∈ T, a k * (d / (d - r k)) * (Real.exp (-(r k * c)) - Real.exp (-(d * c))) := by
  haveI := holdDuration_isProbabilityMeasure hd
  have hanti : Monotone fun x : ℝ≥0 ↦ survivalAt ν (c - x) := fun x x' hxx' ↦
    survivalAt_antitone ν (by linarith [(NNReal.coe_le_coe.mpr hxx' : (x : ℝ) ≤ x')])
  have hG : Measurable fun t : ℝ ↦ survivalAt ν (c - (Real.toNNReal t : ℝ)) :=
    hanti.measurable.comp measurable_real_toNNReal
  have hlebesgue : survivalAt (holdDuration d ∗ ν) c
      = ∫⁻ t, holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ)) := by
    rw [survivalAt_conv, holdDuration, lintegral_map hanti.measurable measurable_real_toNNReal,
      holdMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_holdDensity d) hG]
    rfl
  have hsplit : ∫⁻ t, holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ))
      = ∫⁻ t in Set.Iic c, holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ))
        + ∫⁻ t in Set.Ioi c, holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ)) := by
    rw [← Set.compl_Iic, lintegral_add_compl _ measurableSet_Iic]
  -- past the threshold the holding time alone exceeds it
  have hright : ∫⁻ t in Set.Ioi c, holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ))
      = ENNReal.ofReal (Real.exp (-(d * c))) := by
    have hone : ∀ t ∈ Set.Ioi c,
        holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ)) = holdDensity d t := by
      intro t ht
      have ht' : c < t := ht
      rw [Real.coe_toNNReal t (hc.trans ht'.le), survivalAt_of_neg (by linarith), mul_one]
    rw [setLIntegral_congr_fun measurableSet_Ioi hone, ← withDensity_apply _ measurableSet_Ioi]
    exact holdMeasure_Ioi hd hc
  -- below the threshold the survival of `ν` is the exponential mixture
  have hsurv : ∀ u : ℝ, 0 ≤ u →
      survivalAt ν u = ENNReal.ofReal (∑ k ∈ T, a k * Real.exp (-(r k * u))) := by
    intro u hu
    have hne : survivalAt ν u ≠ ⊤ := measure_ne_top ν _
    rw [← hν u hu, ENNReal.ofReal_toReal hne]
  have hSnonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ ∑ k ∈ T, a k * Real.exp (-(r k * u)) := by
    intro u hu
    rw [← hν u hu]
    exact ENNReal.toReal_nonneg
  have hleft_pt : ∀ t ∈ Set.Iic c,
      holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ))
        = ENNReal.ofReal ((if 0 < t then d * Real.exp (-(d * t)) else 0)
            * ∑ k ∈ T, a k * Real.exp (-(r k * (c - t)))) := by
    intro t ht
    have ht' : t ≤ c := ht
    by_cases ht0 : 0 < t
    · rw [Real.coe_toNNReal t ht0.le, hsurv (c - t) (by linarith), holdDensity, if_pos ht0,
        if_pos ht0, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ d * Real.exp (-(d * t)) by positivity)]
    · rw [holdDensity, if_neg ht0, if_neg ht0, zero_mul, zero_mul, ENNReal.ofReal_zero]
  have hmeas_dens : Measurable fun t : ℝ ↦ (if 0 < t then d * Real.exp (-(d * t)) else 0) :=
    Measurable.ite measurableSet_Ioi
      (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)) measurable_const
  have hdens_nonneg : ∀ t : ℝ, 0 ≤ (if 0 < t then d * Real.exp (-(d * t)) else 0) := by
    intro t
    split_ifs
    · exact mul_nonneg hd.le (Real.exp_pos _).le
    · exact le_rfl
  -- each exponential term integrates the tilted holding density
  have hlint : ∀ k ∈ T, ∫⁻ t in Set.Iic c,
        ENNReal.ofReal ((if 0 < t then d * Real.exp (-(d * t)) else 0)
          * Real.exp (-(r k * (c - t))))
      = ENNReal.ofReal (d / (d - r k) * Real.exp (-(r k * c)))
        * ENNReal.ofReal (1 - Real.exp (-((d - r k) * c))) := by
    intro k hk
    have hgap : 0 < d - r k := by linarith [hrd k hk]
    rw [← holdMeasure_Iic hgap hc, ← setLIntegral_Iic_holdDensity_mul_exp (hr k hk) (hrd k hk)]
    refine setLIntegral_congr_fun measurableSet_Iic fun t _ ↦ ?_
    by_cases ht0 : 0 < t
    · rw [holdDensity, if_pos ht0, if_pos ht0,
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ d * Real.exp (-(d * t)) by positivity)]
    · rw [holdDensity, if_neg ht0, if_neg ht0, zero_mul, zero_mul, ENNReal.ofReal_zero]
  have hterm_meas : ∀ k : ℕ, Measurable fun t : ℝ ↦
      (if 0 < t then d * Real.exp (-(d * t)) else 0) * Real.exp (-(r k * (c - t))) := fun k ↦
    hmeas_dens.mul ((measurable_const.mul (measurable_const.sub measurable_id)).neg.exp)
  have hterm_nn : ∀ k : ℕ, 0 ≤ᵐ[volume.restrict (Set.Iic c)] fun t : ℝ ↦
      (if 0 < t then d * Real.exp (-(d * t)) else 0) * Real.exp (-(r k * (c - t))) := fun k ↦
    Filter.Eventually.of_forall fun t ↦ mul_nonneg (hdens_nonneg t) (Real.exp_pos _).le
  have hterm_int : ∀ k ∈ T, Integrable (fun t : ℝ ↦
      (if 0 < t then d * Real.exp (-(d * t)) else 0) * Real.exp (-(r k * (c - t))))
      (volume.restrict (Set.Iic c)) := by
    intro k hk
    refine ⟨(hterm_meas k).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (hterm_nn k)).mpr ?_⟩
    rw [hlint k hk]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hterm_val : ∀ k ∈ T, ∫ t in Set.Iic c,
        (if 0 < t then d * Real.exp (-(d * t)) else 0) * Real.exp (-(r k * (c - t)))
      = d / (d - r k) * Real.exp (-(r k * c)) * (1 - Real.exp (-((d - r k) * c))) := by
    intro k hk
    have hgap : 0 < d - r k := by linarith [hrd k hk]
    have hle : Real.exp (-((d - r k) * c)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hgap.le hc))
    rw [integral_eq_lintegral_of_nonneg_ae (hterm_nn k) (hterm_meas k).aestronglyMeasurable,
      hlint k hk, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg (div_nonneg hd.le hgap.le) (Real.exp_pos _).le),
      ENNReal.toReal_ofReal (by linarith)]
  have hmix_nn : 0 ≤ᵐ[volume.restrict (Set.Iic c)] fun t : ℝ ↦
      (if 0 < t then d * Real.exp (-(d * t)) else 0)
        * ∑ k ∈ T, a k * Real.exp (-(r k * (c - t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    show 0 ≤ (if 0 < t then d * Real.exp (-(d * t)) else 0)
      * ∑ k ∈ T, a k * Real.exp (-(r k * (c - t)))
    by_cases ht0 : 0 < t
    · have ht' : t ≤ c := ht
      exact mul_nonneg (hdens_nonneg t) (hSnonneg _ (sub_nonneg.mpr ht'))
    · rw [if_neg ht0, zero_mul]
  have hmix_meas : Measurable fun t : ℝ ↦
      (if 0 < t then d * Real.exp (-(d * t)) else 0)
        * ∑ k ∈ T, a k * Real.exp (-(r k * (c - t))) :=
    hmeas_dens.mul (continuous_finset_sum _ fun k _ ↦ by fun_prop).measurable
  have hleft : (∫⁻ t in Set.Iic c,
        holdDensity d t * survivalAt ν (c - (Real.toNNReal t : ℝ))).toReal
      = ∑ k ∈ T, a k * (d / (d - r k) * Real.exp (-(r k * c))
          * (1 - Real.exp (-((d - r k) * c)))) := by
    rw [setLIntegral_congr_fun measurableSet_Iic hleft_pt,
      ← integral_eq_lintegral_of_nonneg_ae hmix_nn hmix_meas.aestronglyMeasurable]
    have hpt : (fun t : ℝ ↦ (if 0 < t then d * Real.exp (-(d * t)) else 0)
          * ∑ k ∈ T, a k * Real.exp (-(r k * (c - t))))
        = fun t ↦ ∑ k ∈ T, a k * ((if 0 < t then d * Real.exp (-(d * t)) else 0)
          * Real.exp (-(r k * (c - t)))) := by
      funext t
      rw [mul_sum]
      exact sum_congr rfl fun k _ ↦ by ring
    rw [hpt, integral_finset_sum _ fun k hk ↦ (hterm_int k hk).const_mul (a k)]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [integral_const_mul, hterm_val k hk]
  have hsum : ∑ k ∈ T, a k * (d / (d - r k) * Real.exp (-(r k * c))
        * (1 - Real.exp (-((d - r k) * c))))
      = ∑ k ∈ T, a k * (d / (d - r k)) * (Real.exp (-(r k * c)) - Real.exp (-(d * c))) := by
    refine sum_congr rfl fun k _ ↦ ?_
    have hexp : Real.exp (-(r k * c)) * Real.exp (-((d - r k) * c)) = Real.exp (-(d * c)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linear_combination (-(a k * (d / (d - r k)))) * hexp
  have htot : survivalAt (holdDuration d ∗ ν) c ≠ ⊤ := measure_ne_top _ _
  rw [hlebesgue, hsplit] at htot ⊢
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp htot).1 (ENNReal.add_ne_top.mp htot).2, hleft,
    hright, ENNReal.toReal_ofReal (Real.exp_pos _).le, hsum]
  ring

/-! ### The spectral coefficients of the connection-time law -/

/-- The spectral coefficients with `m` steps of fuel.  They vanish on a connected report.  From an
unconnected one, a holding duration at `d_K` convolved with the average over covers scales the
coefficient of each lower rate by `d_K/(d_K - d_k)` and puts the remainder on `d_K`. -/
noncomputable def spectralStep {n : ℕ} (s : Fin n → Fin n) : ℕ → ER n → ℕ → ℝ
  | 0, _, _ => 0
  | m + 1, ξ, k =>
      if blocks (observed s ξ) ≤ 1 then 0
      else if k < blocks ξ then
        deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k)
          * ((∑ η : {η : ER n // Covers ξ η}, spectralStep s m η.1 k) / deathRate (blocks ξ))
      else if k = blocks ξ then
        1 - ∑ j ∈ Ioc 1 (blocks ξ - 1),
          deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j)
            * ((∑ η : {η : ER n // Covers ξ η}, spectralStep s m η.1 j) / deathRate (blocks ξ))
      else 0

theorem spectralStep_succ {n : ℕ} (s : Fin n → Fin n) (m : ℕ) (ξ : ER n) (k : ℕ) :
    spectralStep s (m + 1) ξ k =
      if blocks (observed s ξ) ≤ 1 then 0
      else if k < blocks ξ then
        deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k)
          * ((∑ η : {η : ER n // Covers ξ η}, spectralStep s m η.1 k) / deathRate (blocks ξ))
      else if k = blocks ξ then
        1 - ∑ j ∈ Ioc 1 (blocks ξ - 1),
          deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j)
            * ((∑ η : {η : ER n // Covers ξ η}, spectralStep s m η.1 j) / deathRate (blocks ξ))
      else 0 := rfl

/-- **The spectral coefficients of the connection-time law** from `ξ`, at rate index `k`. -/
noncomputable def spectralCoeff {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (k : ℕ) : ℝ :=
  spectralStep s (blocks ξ) ξ k

/-- The average over the covers of `ξ` of their spectral coefficients at rate index `k`. -/
noncomputable def coverAverage {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (k : ℕ) : ℝ :=
  (∑ η : {η : ER n // Covers ξ η}, spectralCoeff s η.1 k) / deathRate (blocks ξ)

/-- **The recursion of the spectral coefficients.** -/
theorem spectralCoeff_eq {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (k : ℕ) :
    spectralCoeff s ξ k =
      if blocks (observed s ξ) ≤ 1 then 0
      else if k < blocks ξ then
        deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k) * coverAverage s ξ k
      else if k = blocks ξ then
        1 - ∑ j ∈ Ioc 1 (blocks ξ - 1),
          deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j
      else 0 := by
  rcases Nat.eq_zero_or_pos (blocks ξ) with h0 | hpos
  · have hr : blocks (observed s ξ) ≤ 1 := by
      have := blocks_antitone (le_observed s ξ)
      omega
    rw [if_pos hr, spectralCoeff, h0]
    rfl
  · obtain ⟨m, hm⟩ : ∃ m, blocks ξ = m + 1 := ⟨blocks ξ - 1, by omega⟩
    have hcover : ∀ j, (∑ η : {η : ER n // Covers ξ η}, spectralStep s m η.1 j)
        / deathRate (blocks ξ) = coverAverage s ξ j := by
      intro j
      unfold coverAverage
      congr 1
      refine sum_congr rfl fun η _ ↦ ?_
      have hη : blocks η.1 = m := by
        have := η.2.2
        omega
      rw [spectralCoeff, hη]
    calc spectralCoeff s ξ k = spectralStep s (m + 1) ξ k := by rw [spectralCoeff, hm]
      _ = _ := by
          rw [spectralStep_succ]
          simp only [hcover]

/-- **The survival function of the connection-time law is a combination of Kingman
exponentials.**  From a state with `K` blocks, `P(τ_q > c) = ∑_{k=2}^{K} spectralCoeff s ξ k ·
e^{-d_k c}` for `c ≥ 0`. -/
theorem survivalAt_connectionTimeLaw_toReal {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∀ c : ℝ, 0 ≤ c → (survivalAt (connectionTimeLaw s ξ) c).toReal
      = ∑ k ∈ Ioc 1 (blocks ξ), spectralCoeff s ξ k * Real.exp (-(deathRate k * c)) := by
  induction ξ using covers_induction with
  | step ξ ih =>
    intro c hc
    rw [connectionTimeLaw_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [dif_pos hr]
      have hdirac : survivalAt (Measure.dirac (0 : ℝ≥0)) c = 0 := by
        rw [survivalAt, Measure.dirac_apply' _ (measurableSet_survival c)]
        simp [Set.indicator, not_lt.mpr hc]
      rw [hdirac, ENNReal.toReal_zero]
      refine (sum_eq_zero fun k _ ↦ ?_).symm
      rw [spectralCoeff_eq, if_pos hr, zero_mul]
    · rw [dif_neg hr]
      have hk := two_le_blocks_of_not_le_one s hr
      have hd := deathRate_pos hk
      haveI := isProbabilityMeasure_bind_jumpStep ξ hk (fun η ↦ connectionTimeLaw s η.1)
        fun η ↦ connectionTimeLaw_isProbabilityMeasure s η.1
      have hmix : ∀ u : ℝ, 0 ≤ u →
          (survivalAt ((jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1) u).toReal
            = ∑ j ∈ Ioc 1 (blocks ξ - 1), coverAverage s ξ j * Real.exp (-(deathRate j * u)) := by
        intro u hu
        have hrow : ∀ η : {η : ER n // Covers ξ η},
            (survivalAt (connectionTimeLaw s η.1) u).toReal
              = ∑ j ∈ Ioc 1 (blocks ξ - 1),
                spectralCoeff s η.1 j * Real.exp (-(deathRate j * u)) := by
          intro η
          have hη : blocks η.1 = blocks ξ - 1 := by
            have := η.2.2
            omega
          rw [ih η.1 η.2 u hu, hη]
        have hfin : ∀ η ∈ (univ : Finset {η : ER n // Covers ξ η}),
            survivalAt (connectionTimeLaw s η.1) u ≠ ⊤ := fun η _ ↦ by
          haveI := connectionTimeLaw_isProbabilityMeasure s η.1
          exact measure_ne_top _ _
        rw [survivalAt_bind_jumpStep, ENNReal.toReal_mul, ENNReal.toReal_sum hfin,
          ENNReal.toReal_inv, choose_two_blocks_eq_ofReal_deathRate, ENNReal.toReal_ofReal hd.le,
          sum_congr rfl fun η _ ↦ hrow η, sum_comm, sum_mul]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [← sum_mul, coverAverage]
        ring
      have hr2 : ∀ j ∈ Ioc 1 (blocks ξ - 1), 0 < deathRate j := fun j hj ↦
        deathRate_pos (by have := (mem_Ioc.mp hj).1; omega)
      have hrd : ∀ j ∈ Ioc 1 (blocks ξ - 1), deathRate j < deathRate (blocks ξ) := fun j hj ↦
        deathRate_lt_deathRate (by have := (mem_Ioc.mp hj).1; omega)
          (by have := (mem_Ioc.mp hj).2; omega)
      rw [survivalAt_holdDuration_conv_combination hd hr2 hrd hmix hc]
      have hsplitTop : ∑ k ∈ Ioc 1 (blocks ξ), spectralCoeff s ξ k * Real.exp (-(deathRate k * c))
          = ∑ k ∈ Ioc 1 (blocks ξ - 1), spectralCoeff s ξ k * Real.exp (-(deathRate k * c))
            + spectralCoeff s ξ (blocks ξ) * Real.exp (-(deathRate (blocks ξ) * c)) := by
        have h := sum_Ioc_succ_top (show 1 ≤ blocks ξ - 1 by omega)
          (fun k ↦ spectralCoeff s ξ k * Real.exp (-(deathRate k * c)))
        rwa [Nat.sub_add_cancel (show 1 ≤ blocks ξ by omega)] at h
      have hlow : ∀ k ∈ Ioc 1 (blocks ξ - 1),
          spectralCoeff s ξ k * Real.exp (-(deathRate k * c))
            = deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k) * coverAverage s ξ k
              * Real.exp (-(deathRate k * c)) := by
        intro k hk'
        have hkK : k < blocks ξ := by
          have := (mem_Ioc.mp hk').2
          omega
        rw [spectralCoeff_eq, if_neg hr, if_pos hkK]
      have htop : spectralCoeff s ξ (blocks ξ)
          = 1 - ∑ j ∈ Ioc 1 (blocks ξ - 1),
            deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate j) * coverAverage s ξ j := by
        rw [spectralCoeff_eq, if_neg hr, if_neg (lt_irrefl _), if_pos rfl]
      have hA : ∑ k ∈ Ioc 1 (blocks ξ - 1), coverAverage s ξ k
            * (deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k))
            * (Real.exp (-(deathRate k * c)) - Real.exp (-(deathRate (blocks ξ) * c)))
          = ∑ k ∈ Ioc 1 (blocks ξ - 1),
              deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k) * coverAverage s ξ k
                * Real.exp (-(deathRate k * c))
            - (∑ k ∈ Ioc 1 (blocks ξ - 1),
                deathRate (blocks ξ) / (deathRate (blocks ξ) - deathRate k) * coverAverage s ξ k)
              * Real.exp (-(deathRate (blocks ξ) * c)) := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun k _ ↦ by ring
      rw [hsplitTop, sum_congr rfl hlow, htop, hA]
      ring

/-- **The spectral statement of §6.**  From `⊥`, for `c ≥ 0`, the survival function of the
reported connection time is `∑_{k=2}^{n} spectralCoeff s ⊥ k · e^{-d_k c}`. -/
theorem survivalAt_connectionTimeLaw_bot {n : ℕ} (s : Fin n → Fin n) {c : ℝ} (hc : 0 ≤ c) :
    survivalAt (connectionTimeLaw s ⊥) c
      = ENNReal.ofReal (∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * Real.exp (-(deathRate k * c))) := by
  haveI := connectionTimeLaw_isProbabilityMeasure s (⊥ : ER n)
  have h := survivalAt_connectionTimeLaw_toReal s ⊥ c hc
  rw [blocks_bot] at h
  have hne : survivalAt (connectionTimeLaw s ⊥) c ≠ ⊤ := measure_ne_top _ _
  rw [← h, ENNReal.ofReal_toReal hne]

end Descent.Pangenome.GraphCoalescent
