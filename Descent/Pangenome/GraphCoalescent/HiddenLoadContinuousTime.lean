/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenStateChain
import Descent.Pangenome.GraphCoalescent.ConnectionClockHittingTime
import Descent.Pangenome.GraphCoalescent.ConnectionClockStochasticOrder

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Theorem A in continuous time: the hidden-load process on the trajectory-and-clock law

The spec is `PANGENOME_HIDDEN_CLOCK.md` §3, Theorem A. `HiddenStateChain` proves that the hidden
state is a Markov chain under the corpus jump chain; its scope line says the continuous-time
holding times are not constructed. This file puts the hidden state on the path law of
`ReportedConnectionClock`, the jump-chain trajectory with an independent Kingman clock, and
derives its one-dimensional law in continuous time.

## The death process of the clock

The path sits at level `k` at time `u` exactly when the descent to `k` has elapsed and the
holding time at `k` has not (`blockCountAt_clockHold_eq_iff`). The descent to `k + 1` is a sum of
clock coordinates disjoint from the holding time at `k + 1`, so the two are independent
(`indepFun_descentTime_clockHold`). A holding time of rate `d` independent of a nonnegative delay
`D` satisfies the window identity `∫_0^t d P(D ≤ u < D + H) du = P(D + H ≤ t)`
(`lintegral_rate_mul_measure_between`), which gives the integrated forward equation of the death
process: the probability of having descended to `k` by time `t` is the integral of the rate
`d_{k+1}` times the probability of sitting at level `k + 1` (`kingmanClock_descentTime_le`).

## Empirical status

None. The bodies here are integrals against the product of the corpus jump law and the corpus
exponential holding law, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal

noncomputable section

/-! ### A holding time against a window -/

/-- `∫_x^t d e^{-d(u - x)} du = 1 - e^{-d(t - x)}`. -/
theorem lintegral_Icc_rate_exp {d x t : ℝ} (hd : 0 < d) (hxt : x ≤ t) :
    ∫⁻ u in Set.Icc x t, ENNReal.ofReal (d * Real.exp (-(d * (u - x))))
      = ENNReal.ofReal (1 - Real.exp (-(d * (t - x)))) := by
  have hcont : Continuous fun u : ℝ ↦ d * Real.exp (-(d * (u - x))) := by fun_prop
  have hderiv : ∀ u ∈ Set.uIcc x t,
      HasDerivAt (fun u : ℝ ↦ -Real.exp (-(d * (u - x)))) (d * Real.exp (-(d * (u - x)))) u := by
    intro u _
    have h : HasDerivAt (fun u : ℝ ↦ -Real.exp (-(d * (u - x))))
        (-(Real.exp (-(d * (u - x))) * -(d * 1))) u :=
      ((((hasDerivAt_id' u).sub_const x).const_mul d).neg.exp).neg
    convert h using 1
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable x t)
  rw [← ofReal_integral_eq_lintegral_ofReal hcont.continuousOn.integrableOn_Icc
      (Filter.Eventually.of_forall fun u ↦ mul_nonneg hd.le (Real.exp_pos _).le),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxt, hint]
  congr 1
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- The rate-weighted indicator of a sojourn `[X, X + Y)` at the time `U` is measurable. -/
theorem measurable_sojourn_indicator {α : Type*} [MeasurableSpace α] {X Y U : α → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable U) (c : ℝ≥0∞) :
    Measurable fun a ↦ (Set.Ico (X a) (X a + Y a)).indicator (fun _ ↦ c) (U a) := by
  have hs : MeasurableSet {a | X a ≤ U a ∧ U a < X a + Y a} :=
    (measurableSet_le hX hU).inter (measurableSet_lt hU (hX.add hY))
  have hfun : (fun a ↦ (Set.Ico (X a) (X a + Y a)).indicator (fun _ ↦ c) (U a))
      = {a | X a ≤ U a ∧ U a < X a + Y a}.indicator fun _ ↦ c := by
    funext a
    simp only [Set.indicator_apply, Set.mem_Ico, Set.mem_setOf_eq]
  rw [hfun]
  exact measurable_const.indicator hs

/-- **A holding time against a window.** For `x ≥ 0`, the expected rate-weighted time that a
sojourn `[x, x + H)` of rate `d` spends in `[0, t]` is `P(x + H ≤ t)`. -/
theorem lintegral_holdMeasure_window {d x t : ℝ} (hd : 0 < d) (hx : 0 ≤ x) :
    ∫⁻ h, (∫⁻ u in Set.Icc 0 t, (Set.Ico x (x + h)).indicator (fun _ ↦ ENNReal.ofReal d) u)
        ∂(holdMeasure d)
      = holdMeasure d (Set.Iic (t - x)) := by
  haveI := holdMeasure_isProbabilityMeasure hd
  have hmeas : Measurable (Function.uncurry fun (h : ℝ) (u : ℝ) ↦
      (Set.Ico x (x + h)).indicator (fun _ ↦ ENNReal.ofReal d) u) :=
    measurable_sojourn_indicator measurable_const measurable_fst measurable_snd _
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hinner : ∀ u : ℝ,
      ∫⁻ h, (Set.Ico x (x + h)).indicator (fun _ ↦ ENNReal.ofReal d) u ∂(holdMeasure d)
        = (Set.Ici x).indicator (fun u ↦ ENNReal.ofReal (d * Real.exp (-(d * (u - x))))) u := by
    intro u
    by_cases hxu : x ≤ u
    · have hfun : (fun h ↦ (Set.Ico x (x + h)).indicator (fun _ ↦ ENNReal.ofReal d) u)
          = (Set.Ioi (u - x)).indicator fun _ ↦ ENNReal.ofReal d := by
        funext h
        simp only [Set.indicator_apply, Set.mem_Ico, Set.mem_Ioi, hxu, true_and,
          sub_lt_iff_lt_add']
      rw [hfun, lintegral_indicator_const measurableSet_Ioi,
        holdMeasure_Ioi hd (sub_nonneg.mpr hxu), ← ENNReal.ofReal_mul hd.le,
        Set.indicator_of_mem (Set.mem_Ici.mpr hxu)]
    · simp [hxu]
  refine (lintegral_congr hinner).trans ?_
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : Set.Ici x ∩ Set.Icc 0 t = Set.Icc x t := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, hx.trans h1, h3⟩
  rw [hset]
  by_cases hxt : x ≤ t
  · rw [lintegral_Icc_rate_exp hd hxt, holdMeasure_Iic hd (sub_nonneg.mpr hxt)]
  · rw [Set.Icc_eq_empty hxt, Measure.restrict_empty, lintegral_zero_measure]
    exact (measure_mono_null (Set.Iic_subset_Iio.mpr (by linarith [not_le.mp hxt]))
      (holdMeasure_Iio_zero d)).symm

/-- **The window identity.** If a nonnegative delay `D` and a holding time `H` of rate `d` are
independent, then `∫_0^t d P(D ≤ u < D + H) du = P(D + H ≤ t)`. -/
theorem lintegral_rate_mul_measure_between {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D H : Ω → ℝ} (hDm : Measurable D) (hHm : Measurable H)
    (hind : IndepFun D H μ) {d : ℝ} (hd : 0 < d) (hH : μ.map H = holdMeasure d)
    (hD : ∀ᵐ ω ∂μ, 0 ≤ D ω) (t : ℝ) :
    ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal d * μ {ω | D ω ≤ u ∧ u < D ω + H ω}
      = μ {ω | D ω + H ω ≤ t} := by
  haveI := holdMeasure_isProbabilityMeasure hd
  have hpair : Measurable fun ω ↦ (D ω, H ω) := hDm.prodMk hHm
  have hjoint : μ.map (fun ω ↦ (D ω, H ω)) = (μ.map D).prod (holdMeasure d) := by
    rw [← hH]
    exact (indepFun_iff_map_prod_eq_prod_map_map hDm.aemeasurable hHm.aemeasurable).mp hind
  have hcomp : ∀ u : ℝ, ENNReal.ofReal d * μ {ω | D ω ≤ u ∧ u < D ω + H ω}
      = ∫⁻ ω, (Set.Ico (D ω) (D ω + H ω)).indicator (fun _ ↦ ENNReal.ofReal d) u ∂μ := by
    intro u
    have hs : MeasurableSet {ω | D ω ≤ u ∧ u < D ω + H ω} :=
      (measurableSet_le hDm measurable_const).inter
        (measurableSet_lt measurable_const (hDm.add hHm))
    rw [← lintegral_indicator_const hs]
    refine lintegral_congr fun ω ↦ ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ico]
  have hW : Measurable fun p : ℝ × ℝ ↦
      ∫⁻ u in Set.Icc 0 t, (Set.Ico p.1 (p.1 + p.2)).indicator (fun _ ↦ ENNReal.ofReal d) u :=
    (measurable_sojourn_indicator (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst) measurable_snd _).lintegral_prod_right'
  have hRHS : μ {ω | D ω + H ω ≤ t} = ∫⁻ x, holdMeasure d (Set.Iic (t - x)) ∂(μ.map D) := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ t} :=
      measurableSet_le (measurable_fst.add measurable_snd) measurable_const
    rw [show {ω | D ω + H ω ≤ t} = (fun ω ↦ (D ω, H ω)) ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ≤ t} from rfl,
      ← Measure.map_apply hpair hs, hjoint, Measure.prod_apply hs]
    refine lintegral_congr fun x ↦ ?_
    congr 1
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic]
    constructor <;> intro hh <;> linarith
  have hDmap : ∀ᵐ x ∂(μ.map D), 0 ≤ x :=
    (ae_map_iff hDm.aemeasurable measurableSet_Ici).mpr hD
  simp only [hcomp]
  calc ∫⁻ u in Set.Icc 0 t, ∫⁻ ω,
        (Set.Ico (D ω) (D ω + H ω)).indicator (fun _ ↦ ENNReal.ofReal d) u ∂μ
      = ∫⁻ ω, (∫⁻ u in Set.Icc 0 t,
          (Set.Ico (D ω) (D ω + H ω)).indicator (fun _ ↦ ENNReal.ofReal d) u) ∂μ :=
        lintegral_lintegral_swap
          (f := fun (u : ℝ) (ω : Ω) ↦
            (Set.Ico (D ω) (D ω + H ω)).indicator (fun _ ↦ ENNReal.ofReal d) u)
          (measurable_sojourn_indicator (hDm.comp measurable_snd) (hHm.comp measurable_snd)
            measurable_fst _).aemeasurable
    _ = ∫⁻ p, (∫⁻ u in Set.Icc 0 t,
          (Set.Ico p.1 (p.1 + p.2)).indicator (fun _ ↦ ENNReal.ofReal d) u)
          ∂(μ.map fun ω ↦ (D ω, H ω)) := (lintegral_map hW hpair).symm
    _ = ∫⁻ x, (∫⁻ h, (∫⁻ u in Set.Icc 0 t,
          (Set.Ico x (x + h)).indicator (fun _ ↦ ENNReal.ofReal d) u)
          ∂(holdMeasure d)) ∂(μ.map D) := by
        rw [hjoint]
        exact lintegral_prod _ hW.aemeasurable
    _ = ∫⁻ x, holdMeasure d (Set.Iic (t - x)) ∂(μ.map D) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hDmap] with x hx
        exact lintegral_holdMeasure_window hd hx
    _ = μ {ω | D ω + H ω ≤ t} := hRHS.symm

/-! ### The death process of Kingman's clock -/

/-- The descent to `k + 1` timed by the clock is the sum of the clock coordinates `k, …, n - 2`. -/
theorem descentTime_clockHold_eq_sum (n k : ℕ) (hkn : k + 1 ≤ n) (ω : ℕ → ℝ) :
    descentTime n (clockHold ω) (k + 1) = ∑ j ∈ Finset.Ico k (n - 1), ω j := by
  rw [descentTime, ico_succ_eq_ioc,
    ← sum_Ico_pred (clockHold ω) (by omega : 1 ≤ k + 1) (by omega : 1 ≤ n)]
  rfl

/-- The descent to `k` is the descent to `k + 1` followed by the holding time at `k + 1`. -/
theorem descentTime_clockHold_succ (n k : ℕ) (_hk : 1 ≤ k) (hkn : k < n) (ω : ℕ → ℝ) :
    descentTime n (clockHold ω) k = descentTime n (clockHold ω) (k + 1) + ω (k - 1) := by
  unfold descentTime
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k + 1 < n + 1)]
  exact add_comm _ _

/-- **The descent to `k + 1` and the holding time at `k + 1` are independent.** -/
theorem indepFun_descentTime_clockHold (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    IndepFun (fun ω : ℕ → ℝ ↦ descentTime n (clockHold ω) (k + 1)) (fun ω ↦ ω (k - 1))
      kingmanClock := by
  haveI : ∀ j : ℕ, IsProbabilityMeasure (holdMeasure (deathRate (j + 2))) := fun j ↦
    holdMeasure_isProbabilityMeasure (deathRate_add_two_pos j)
  have hind : iIndepFun (fun (j : ℕ) (ω : ℕ → ℝ) ↦ ω j) kingmanClock :=
    iIndepFun_infinitePi (X := fun _ (t : ℝ) ↦ t) fun _ ↦ measurable_id
  have hnot : k - 1 ∉ Finset.Ico k (n - 1) := by
    simp only [Finset.mem_Ico, not_and, not_lt]
    intro h
    omega
  have h : IndepFun (∑ j ∈ Finset.Ico k (n - 1), fun ω : ℕ → ℝ ↦ ω j)
      (fun ω : ℕ → ℝ ↦ ω (k - 1)) kingmanClock :=
    hind.indepFun_finset_sum_of_notMem (fun j ↦ measurable_pi_apply j) hnot
  have hfun : (∑ j ∈ Finset.Ico k (n - 1), fun ω : ℕ → ℝ ↦ ω j)
      = fun ω ↦ descentTime n (clockHold ω) (k + 1) := by
    funext ω
    rw [Finset.sum_apply, descentTime_clockHold_eq_sum n k hkn ω]
  rwa [hfun] at h

/-- The path sits at level `k + 1` exactly while the descent to `k + 1` has elapsed and the
holding time at `k + 1` has not. -/
theorem blockCountAt_clockHold_eq_iff {n k : ℕ} {ω : ℕ → ℝ} (hω : ∀ j, 0 ≤ ω j) (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) (u : ℝ) :
    blockCountAt n (clockHold ω) u = k + 1 ↔
      descentTime n (clockHold ω) (k + 1) ≤ u
        ∧ u < descentTime n (clockHold ω) (k + 1) + ω (k - 1) := by
  have hpos : ∀ j, 0 ≤ clockHold ω j := fun j ↦ hω (j - 2)
  rw [← descentTime_clockHold_succ n k hk (by omega) ω]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hlt
      have := lt_blockCountAt_of_lt_descentTime n hpos (by omega) hkn (not_le.mp hlt)
      omega
    · by_contra hle
      have := blockCountAt_le_of_descentTime_le n hpos hk (by omega) (not_lt.mp hle)
      omega
  · rintro ⟨hle, hlt⟩
    refine blockCountAt_eq n hpos (by omega) hkn hle fun j _ hjk ↦ ?_
    exact lt_of_lt_of_le hlt (descentTime_antitone n hpos (by omega))

/-- **The integrated forward equation of the death process.** The probability of having descended
to level `k` by time `t` is `∫_0^t d_{k+1} P(D(n, u) = k + 1) du`. -/
theorem kingmanClock_descentTime_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (t : ℝ) :
    kingmanClock {ω | descentTime n (clockHold ω) k ≤ t}
      = ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (deathRate (k + 1))
          * kingmanClock {ω | blockCountAt n (clockHold ω) u = k + 1} := by
  have hrate : 0 < deathRate (k + 1) := by
    have h := deathRate_add_two_pos (k - 1)
    rwa [show k - 1 + 2 = k + 1 by omega] at h
  have hmap : kingmanClock.map (fun ω : ℕ → ℝ ↦ ω (k - 1)) = holdMeasure (deathRate (k + 1)) := by
    have h := (kingmanClock_eval (k - 1)).map_eq
    rwa [show k - 1 + 2 = k + 1 by omega] at h
  have hDm : Measurable fun ω : ℕ → ℝ ↦ descentTime n (clockHold ω) (k + 1) := by
    simp only [descentTime_clockHold_eq_sum n k hkn]
    exact Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  have hD : ∀ᵐ ω ∂kingmanClock, 0 ≤ descentTime n (clockHold ω) (k + 1) := by
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    exact descentTime_nonneg n (fun j ↦ hω (j - 2)) _
  have hsets : ∀ u : ℝ, kingmanClock {ω | blockCountAt n (clockHold ω) u = k + 1}
      = kingmanClock {ω | descentTime n (clockHold ω) (k + 1) ≤ u
          ∧ u < descentTime n (clockHold ω) (k + 1) + ω (k - 1)} := by
    intro u
    refine measure_congr ?_
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    exact propext (blockCountAt_clockHold_eq_iff hω hk hkn u)
  simp only [hsets]
  have hleft : {ω : ℕ → ℝ | descentTime n (clockHold ω) k ≤ t}
      = {ω | descentTime n (clockHold ω) (k + 1) + ω (k - 1) ≤ t} := by
    ext ω
    simp only [Set.mem_setOf_eq, descentTime_clockHold_succ n k hk (by omega) ω]
  rw [hleft]
  exact (lintegral_rate_mul_measure_between hDm (measurable_pi_apply (k - 1))
    (indepFun_descentTime_clockHold n k hk hkn) hrate hmap hD t).symm

/-! ### The level probabilities -/

/-- The probability that the path has `k` blocks at time `u`. -/
def levelProb (n k : ℕ) (u : ℝ) : ℝ≥0∞ :=
  kingmanClock {ω | blockCountAt n (clockHold ω) u = k}

theorem measurable_descentTime_clockHold (n k : ℕ) :
    Measurable fun ω : ℕ → ℝ ↦ descentTime n (clockHold ω) k := by
  show Measurable fun ω : ℕ → ℝ ↦ ∑ j ∈ Finset.Ico (k + 1) (n + 1), ω (j - 2)
  exact Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply (j - 2)

/-- The block count of the path at a fixed time is a measurable function of the clock. -/
theorem measurable_blockCountAt_clockHold (n : ℕ) (t : ℝ) :
    Measurable fun ω : ℕ → ℝ ↦ blockCountAt n (clockHold ω) t := by
  have h : (fun ω : ℕ → ℝ ↦ blockCountAt n (clockHold ω) t)
      = fun ω ↦ (∑ j ∈ Finset.Icc 1 n,
          if t < descentTime n (clockHold ω) j then 1 else 0) + 1 := by
    funext ω
    rw [blockCountAt, Finset.card_filter]
  rw [h]
  refine (Finset.measurable_sum _ fun j _ ↦ ?_).add_const 1
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_descentTime_clockHold n j))
    measurable_const measurable_const

/-- The path has reached level `1` exactly once the descent to `1` has elapsed. -/
theorem kingmanClock_descentTime_one_le (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    kingmanClock {ω | descentTime n (clockHold ω) 1 ≤ t} = levelProb n 1 t := by
  refine measure_congr ?_
  filter_upwards [ae_nonneg_kingmanClock] with ω hω
  have hpos : ∀ j, 0 ≤ clockHold ω j := fun j ↦ hω (j - 2)
  apply propext
  constructor
  · intro h
    exact le_antisymm (blockCountAt_le_of_descentTime_le n hpos le_rfl hn h)
      (one_le_blockCountAt n _ t)
  · intro h
    have h' : blockCountAt n (clockHold ω) t = 1 := h
    by_contra hlt
    have := lt_blockCountAt_of_lt_descentTime n hpos le_rfl hn (not_le.mp hlt)
    omega

/-- Having descended to `k + 1` is sitting at `k + 1` or having descended further, almost
surely. -/
theorem kingmanClock_descentTime_succ_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (t : ℝ) :
    kingmanClock {ω | descentTime n (clockHold ω) (k + 1) ≤ t}
      = levelProb n (k + 1) t + kingmanClock {ω | descentTime n (clockHold ω) k ≤ t} := by
  have hnull : kingmanClock {ω : ℕ → ℝ | ¬ ∀ j, 0 ≤ ω j} = 0 := ae_iff.mp ae_nonneg_kingmanClock
  have hae : {ω : ℕ → ℝ | descentTime n (clockHold ω) (k + 1) ≤ t}
      =ᵐ[kingmanClock] {ω | blockCountAt n (clockHold ω) t = k + 1}
        ∪ {ω | descentTime n (clockHold ω) k ≤ t} := by
    filter_upwards [ae_nonneg_kingmanClock] with ω hω
    have hsucc := descentTime_clockHold_succ n k hk (by omega) ω
    have hstep : 0 ≤ ω (k - 1) := hω (k - 1)
    have hiff := blockCountAt_clockHold_eq_iff hω hk hkn t
    apply propext
    constructor
    · intro h
      have h' : descentTime n (clockHold ω) (k + 1) ≤ t := h
      by_cases hlt : t < descentTime n (clockHold ω) (k + 1) + ω (k - 1)
      · exact Or.inl (hiff.mpr ⟨h', hlt⟩)
      · have hle : descentTime n (clockHold ω) k ≤ t := by
          rw [hsucc]
          exact not_lt.mp hlt
        exact Or.inr hle
    · rintro (h | h)
      · exact (hiff.mp h).1
      · have h' : descentTime n (clockHold ω) k ≤ t := h
        show descentTime n (clockHold ω) (k + 1) ≤ t
        rw [hsucc] at h'
        linarith
  have hdisj : AEDisjoint kingmanClock {ω : ℕ → ℝ | blockCountAt n (clockHold ω) t = k + 1}
      {ω | descentTime n (clockHold ω) k ≤ t} := by
    refine measure_mono_null (fun ω hω ↦ ?_) hnull
    obtain ⟨h1, h2⟩ := hω
    have h1' : blockCountAt n (clockHold ω) t = k + 1 := h1
    have h2' : descentTime n (clockHold ω) k ≤ t := h2
    intro hpos
    have := blockCountAt_le_of_descentTime_le n (fun j ↦ hpos (j - 2)) hk (by omega) h2'
    omega
  rw [measure_congr hae, measure_union₀
    (measurableSet_le (measurable_descentTime_clockHold n k) measurable_const).nullMeasurableSet
    hdisj]
  rfl

/-- **The balance of the level probabilities.** For `1 ≤ k ≤ n` and `t ≥ 0`, the probability of
sitting at level `k` plus the rate-weighted time spent at `k` is the initial mass at `k` plus the
rate-weighted time spent at `k + 1`. -/
theorem levelProb_balance {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) {t : ℝ}
    (ht : 0 ≤ t) :
    levelProb n k t + ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (deathRate k) * levelProb n k u
      = (if k = n then 1 else 0)
        + if k < n then
            ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (deathRate (k + 1)) * levelProb n (k + 1) u
          else 0 := by
  rcases Nat.lt_or_ge k n with hlt | hge
  · rw [if_neg hlt.ne, if_pos hlt, zero_add]
    rcases Nat.eq_or_lt_of_le hk with h1 | h1
    · rw [← h1, deathRate_one, ENNReal.ofReal_zero]
      simp only [zero_mul, lintegral_zero, add_zero]
      rw [← kingmanClock_descentTime_one_le n (by omega) t]
      exact kingmanClock_descentTime_le n 1 le_rfl (by omega) t
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj1 := kingmanClock_descentTime_le n j (by omega) (by omega) t
      have hj2 := kingmanClock_descentTime_le n (j + 1) (by omega) hlt t
      have hj3 := kingmanClock_descentTime_succ_le n j (by omega) (by omega) t
      calc levelProb n (j + 1) t
            + ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (deathRate (j + 1)) * levelProb n (j + 1) u
          = levelProb n (j + 1) t + kingmanClock {ω | descentTime n (clockHold ω) j ≤ t} := by
            rw [hj1]
            rfl
        _ = kingmanClock {ω | descentTime n (clockHold ω) (j + 1) ≤ t} := hj3.symm
        _ = _ := hj2
  · have hkeq : k = n := le_antisymm hkn hge
    rw [if_pos hkeq, if_neg (by omega : ¬ k < n), add_zero, hkeq]
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hall : kingmanClock {ω : ℕ → ℝ | descentTime n (clockHold ω) n ≤ t} = 1 := by
      have huniv : {ω : ℕ → ℝ | descentTime n (clockHold ω) n ≤ t} = Set.univ := by
        ext ω
        simp only [descentTime_self, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact ht
      rw [huniv, measure_univ]
    have hj3 := kingmanClock_descentTime_succ_le n j (by omega) (by omega) t
    have hj1 := kingmanClock_descentTime_le n j (by omega) (by omega) t
    rw [← hj] at hj3 hj1
    calc levelProb n n t + ∫⁻ u in Set.Icc 0 t, ENNReal.ofReal (deathRate n) * levelProb n n u
        = levelProb n n t + kingmanClock {ω | descentTime n (clockHold ω) j ≤ t} := by
          rw [hj1]
          rfl
      _ = kingmanClock {ω | descentTime n (clockHold ω) n ≤ t} := hj3.symm
      _ = 1 := hall

/-! ### The hidden-load process -/

/-- **The hidden-load process**: the hidden state of the coalescent path at time `t`, on a
trajectory and a clock. -/
def hiddenLoadAt {n : ℕ} (s : Fin n → Fin n) (p : List (ER n) × (ℕ → ℝ)) (t : ℝ) :
    ER n × (Fin n → ℕ) :=
  hiddenState s (pathState n (chainOfList p.1) (clockHold p.2) t)

/-- The law of the hidden state after `j` jumps of the labeled chain. -/
def hiddenHeadLaw {n : ℕ} (s : Fin n → Fin n) (j : ℕ) : PMF (ER n × (Fin n → ℕ)) :=
  (blockLaw n j).map (hiddenState s)

/-- Reading a full trajectory at level `k` and taking the hidden state gives the hidden law after
`n - k` jumps. -/
theorem toMeasure_hiddenState_chainOfList {n k : ℕ} (s : Fin n → Fin n) (hk : 1 ≤ k)
    (hkn : k ≤ n) (y : ER n × (Fin n → ℕ)) :
    (chainLaw n (n - 1)).toMeasure {l | hiddenState s (chainOfList l k) = y}
      = hiddenHeadLaw s (n - k) y := by
  have hmap : (chainLaw n (n - 1)).map (fun l ↦ hiddenState s (chainOfList l k))
      = hiddenHeadLaw s (n - k) := by
    have h := congrArg (PMF.map (hiddenState s))
      (chainLaw_map_getD (n := n) (n - 1) (k - 1) (by omega))
    rw [PMF.map_comp, show n - 1 - (k - 1) = n - k by omega] at h
    exact h
  rw [← hmap, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSpace.measurableSet_top,
    PMF.toOuterMeasure_apply, PMF.map_apply]
  refine tsum_congr fun l ↦ ?_
  by_cases h : hiddenState s (chainOfList l k) = y
  · rw [Set.indicator_of_mem (show l ∈ {l | hiddenState s (chainOfList l k) = y} from h),
      if_pos h.symm]
  · rw [Set.indicator_of_notMem (show l ∉ {l | hiddenState s (chainOfList l k) = y} from h),
      if_neg fun h' ↦ h h'.symm]

/-- **The law of the hidden-load process factorizes over the level.** At a time `t ≥ 0` the
hidden-load process takes the value `y` with probability `Σ_k P(D(n, t) = k) μ_{n-k}(y)`, `μ_j`
being the hidden law after `j` jumps. -/
theorem trajectoryClockLaw_hiddenLoadAt {n : ℕ} (hn : 1 ≤ n) (s : Fin n → Fin n) {t : ℝ}
    (ht : 0 ≤ t) (y : ER n × (Fin n → ℕ)) :
    trajectoryClockLaw n {p | hiddenLoadAt s p t = y}
      = ∑ k ∈ Finset.Icc 1 n, hiddenHeadLaw s (n - k) y * levelProb n k t := by
  have hset : {p : List (ER n) × (ℕ → ℝ) | hiddenLoadAt s p t = y}
      = ⋃ k ∈ Finset.Icc 1 n, {l : List (ER n) | hiddenState s (chainOfList l k) = y}
          ×ˢ {ω : ℕ → ℝ | blockCountAt n (clockHold ω) t = k} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Finset.mem_Icc, exists_prop,
      hiddenLoadAt, pathState]
    constructor
    · intro h
      exact ⟨blockCountAt n (clockHold p.2) t,
        ⟨one_le_blockCountAt n _ t, blockCountAt_le n ht hn⟩, h, rfl⟩
    · rintro ⟨k, -, h, hk⟩
      rw [hk]
      exact h
  rw [hset, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_Icc] at hk
    rw [trajectoryClockLaw_prod, toMeasure_hiddenState_chainOfList s hk.1 hk.2]
    rfl
  · exact fun k _ k' _ hkk' ↦ Set.disjoint_left.mpr fun p hp hp' ↦ hkk' (hp.2.symm.trans hp'.2)
  · exact fun k _ ↦ MeasurableSpace.measurableSet_top.prod
      (measurable_blockCountAt_clockHold n t (measurableSet_singleton k))

end

end Descent.Pangenome.GraphCoalescent
