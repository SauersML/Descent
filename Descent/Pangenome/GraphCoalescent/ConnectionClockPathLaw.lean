/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TransitTransform
import Descent.Pangenome.GraphCoalescent.VisibleIntensityClock

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The report's connection time as a law built on the Kingman chain

`Descent.Pangenome.GraphCoalescent.VisibleIntensityClock` defines the mean connection time and its
Laplace transform as first-step values, the solutions of a backward equation. This file builds the
LAW of the connection time from the corpus's own Kingman chain and identifies both first-step values
as integrals against it. So (C2)-(C4) and the correction identity (C3) of
`PANGENOME_HIDDEN_CLOCK.md` §5 become statements about the chain.

## The law

From a labeled coalescent state `ξ` whose report is not connected, the chain waits a holding time
of rate `d_K = C(K, 2)` (K-C (1.7), `Descent.Coalescent.HoldingTime.holdMeasure`) and then jumps to
a uniformly chosen cover (K-C (2.2), `Descent.Coalescent.Process.jumpStep`), independently of the
holding time. From a state whose report is connected the time is zero. `connectionTimeLaw s ξ` is
the law of the resulting time until connection, built by recursion along covers:

  `law(ξ) = holdDuration d_K ∗ (jumpStep ξ).bind law`,

the convolution of the holding law with the mixture, over the first jump, of the law from the next
state (`connectionTimeLaw_eq`). The independence of holding time and jump is arranged, as in K-C
Theorem 3 and in `Descent.Coalescent.Law`; it is not derived from a factorization of a path-space
law.

## What is proved

* `connectionTimeLaw_isProbabilityMeasure`: the law is a probability measure.
* `lintegral_coe_connectionTimeLaw`: **its mean is `meanConnectionTime`**, the first-step value of
  `VisibleIntensityClock`.
* `lintegral_exp_connectionTimeLaw`: **its Laplace transform is `connectionLaplace`**.
* (C3) for the law, `lintegral_add_correction_bot`: `E τ_q + V(0, λ_vis/d_r - 1)(⊥) = 2 - 2/w`,
  with `E τ_q` the integral against the law. (C4): `lintegral_coe_connectionTimeLaw_bot_le`,
  `lintegral_coe_connectionTimeLaw_bot_lt` and `ofReal_le_lintegral_coe_connectionTimeLaw_bot`.
  (C2) in Laplace order: `kingmanLaplace_width_le_lintegral_exp_connectionTimeLaw_bot`.
* `lintegral_exp_connectionTimeLaw_graphKer`: entered at `graphKer s`, the connection time has the
  transform of K-G's transit time `T_w` under the corpus clock `EntranceLaw.holdProduct`
  (`TransitTransform.kingman_transitTransform`); `lintegral_coe_connectionTimeLaw_graphKer` is its
  mean `2 - 2/w`.

## What is not proved

The law is built by first-step recursion from the jump law and the holding law. It is not
identified with the image of a path-space measure, such as `TrajectoryLaw.chainTrajFrom` producted
with an independent clock. The stochastic order of (C2) is not formalized; what is proved is the
Laplace-transform order it implies.

## Empirical status

None. The bodies here are finite recursions over the equivalence relations of a finite set and
lower integrals against measures built from the corpus holding law and jump law; no measurement can
bear on the integral of a supplied law.
-/

set_option autoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset MeasureTheory
open scoped MeasureTheory NNReal ENNReal Classical

noncomputable section

/-! ### Holding durations -/

/-- The corpus holding law is carried by positive times. -/
theorem ae_pos_holdMeasure (d : ℝ) : ∀ᵐ t ∂(holdMeasure d), 0 < t := by
  have hmeas : Measurable (holdDensity d) := by
    unfold holdDensity
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    exact (measurable_const.mul ((measurable_const.mul measurable_id).neg.exp)).ennreal_ofReal
  rw [holdMeasure, ae_withDensity_iff hmeas]
  refine Filter.Eventually.of_forall fun t ht ↦ ?_
  by_contra hneg
  exact ht (by simp only [holdDensity, if_neg hneg])

/-- **K-C (1.7)'s holding law, as a nonnegative duration.** -/
def holdDuration (d : ℝ) : Measure ℝ≥0 :=
  (holdMeasure d).map Real.toNNReal

theorem holdDuration_isProbabilityMeasure {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure (holdDuration d) := by
  haveI := holdMeasure_isProbabilityMeasure hd
  exact isProbabilityMeasure_map measurable_real_toNNReal.aemeasurable

/-- The mean holding duration is `1/d`, `EntranceLaw.lintegral_id_holdMeasure`. -/
theorem lintegral_coe_holdDuration {d : ℝ} (hd : 0 < d) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(holdDuration d) = ENNReal.ofReal (1 / d) := by
  rw [holdDuration, lintegral_map measurable_coe_nnreal_ennreal measurable_real_toNNReal]
  exact lintegral_id_holdMeasure hd

/-- The transform of a holding duration is `d/(d + t)`,
`LaplaceTransform.lintegral_exp_neg_holdMeasure`. -/
theorem lintegral_exp_holdDuration {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * (x : ℝ)))) ∂(holdDuration d)
      = ENNReal.ofReal (d / (d + t)) := by
  rw [holdDuration,
    lintegral_map (measurable_const.mul measurable_coe_nnreal_real).neg.exp.ennreal_ofReal
      measurable_real_toNNReal,
    ← lintegral_exp_neg_holdMeasure hd ht]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_holdMeasure d] with a ha
  rw [Real.coe_toNNReal a ha.le]

/-! ### Expectations under a jump -/

/-- `𝓔ₙ` carries the discrete σ-algebra, so its singletons are measurable. -/
theorem measurableSingletonClass_ER (n : ℕ) : MeasurableSingletonClass (ER n) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

/-- **A uniform jump averages over the covers**:
`∫ f d(jumpStep ξ) = (Σ_{ξ ⋖ η} f(η)) / C(K, 2)`. -/
theorem lintegral_jumpStep {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (f : {η : ER n // Covers ξ η} → ℝ≥0∞) :
    ∫⁻ η, f η ∂(jumpStep ξ hk).toMeasure
      = (∑ η, f η) * (((blocks ξ).choose 2 : ℕ) : ℝ≥0∞)⁻¹ := by
  haveI := measurableSingletonClass_ER n
  rw [lintegral_fintype, sum_mul]
  refine sum_congr rfl fun η _ ↦ ?_
  rw [(jumpStep ξ hk).toMeasure_apply_singleton η (measurableSet_singleton η), jumpStep_apply]

/-- A mixture of probability laws over one jump is a probability law. -/
theorem isProbabilityMeasure_bind_jumpStep {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (μ : {η : ER n // Covers ξ η} → Measure ℝ≥0) (hμ : ∀ η, IsProbabilityMeasure (μ η)) :
    IsProbabilityMeasure ((jumpStep ξ hk).toMeasure.bind μ) := by
  haveI := measurableSingletonClass_ER n
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (measurable_of_finite μ).aemeasurable,
    lintegral_congr fun η ↦ (hμ η).measure_univ, lintegral_const, measure_univ, one_mul]

/-- The number of covers the jump divides by is the death rate, as an extended real. -/
theorem choose_two_blocks_eq_ofReal_deathRate {n : ℕ} (ξ : ER n) :
    (((blocks ξ).choose 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (deathRate (blocks ξ)) := by
  have h := card_covers_eq_deathRate ξ
  rw [card_covers] at h
  rw [← h, ENNReal.ofReal_natCast]

/-- A nonnegative average over the covers, as an extended real. -/
theorem sum_ofReal_mul_inv_choose_two {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (v : {η : ER n // Covers ξ η} → ℝ) (hv : ∀ η, 0 ≤ v η) :
    (∑ η, ENNReal.ofReal (v η)) * (((blocks ξ).choose 2 : ℕ) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal ((∑ η, v η) / deathRate (blocks ξ)) := by
  rw [ENNReal.ofReal_div_of_pos (deathRate_pos hk),
    ENNReal.ofReal_sum_of_nonneg fun η _ ↦ hv η, div_eq_mul_inv,
    choose_two_blocks_eq_ofReal_deathRate]

/-! ### The law of the connection time -/

/-- A state whose report is not connected has at least two true blocks. -/
theorem two_le_blocks_of_not_le_one {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (h : ¬ blocks (observed s ξ) ≤ 1) : 2 ≤ blocks ξ := by
  have := blocks_antitone (le_observed s ξ)
  omega

/-- The recursion for the connection-time law with `k` steps of fuel. -/
def connectionTimeStep {n : ℕ} (s : Fin n → Fin n) : ℕ → ER n → Measure ℝ≥0
  | 0, _ => Measure.dirac 0
  | k + 1, ξ =>
      if h : blocks (observed s ξ) ≤ 1 then Measure.dirac 0
      else holdDuration (deathRate (blocks ξ)) ∗
        (jumpStep ξ (two_le_blocks_of_not_le_one s h)).toMeasure.bind
          fun η ↦ connectionTimeStep s k η.1

theorem connectionTimeStep_succ {n : ℕ} (s : Fin n → Fin n) (k : ℕ) (ξ : ER n) :
    connectionTimeStep s (k + 1) ξ =
      if h : blocks (observed s ξ) ≤ 1 then Measure.dirac 0
      else holdDuration (deathRate (blocks ξ)) ∗
        (jumpStep ξ (two_le_blocks_of_not_le_one s h)).toMeasure.bind
          fun η ↦ connectionTimeStep s k η.1 := rfl

/-- **The law of the time until the report connects**, from the labeled state `ξ`: a Kingman
holding time at the current block count, followed by the connection time from a uniformly chosen
cover. The fuel is the block count, which every cover lowers by one. -/
def connectionTimeLaw {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : Measure ℝ≥0 :=
  connectionTimeStep s (blocks ξ) ξ

/-- **The first-step decomposition of the law.** -/
theorem connectionTimeLaw_eq {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    connectionTimeLaw s ξ =
      if h : blocks (observed s ξ) ≤ 1 then Measure.dirac 0
      else holdDuration (deathRate (blocks ξ)) ∗
        (jumpStep ξ (two_le_blocks_of_not_le_one s h)).toMeasure.bind
          fun η ↦ connectionTimeLaw s η.1 := by
  rcases Nat.eq_zero_or_pos (blocks ξ) with h0 | hpos
  · have hr : blocks (observed s ξ) ≤ 1 := by
      have := blocks_antitone (le_observed s ξ)
      omega
    rw [dif_pos hr, connectionTimeLaw, h0]
    rfl
  · obtain ⟨k, hk⟩ : ∃ k, blocks ξ = k + 1 := ⟨blocks ξ - 1, by omega⟩
    have hfun : (fun η : {η : ER n // Covers ξ η} ↦ connectionTimeStep s k η.1)
        = fun η ↦ connectionTimeLaw s η.1 := by
      funext η
      have hη : blocks η.1 = k := by
        have := η.2.2
        omega
      rw [connectionTimeLaw, hη]
    calc connectionTimeLaw s ξ = connectionTimeStep s (k + 1) ξ := by
          rw [connectionTimeLaw, hk]
      _ = _ := by rw [connectionTimeStep_succ, hfun]

/-- **The connection-time law is a probability law.** -/
theorem connectionTimeLaw_isProbabilityMeasure {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    IsProbabilityMeasure (connectionTimeLaw s ξ) := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [connectionTimeLaw_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [dif_pos hr]
      infer_instance
    · rw [dif_neg hr]
      haveI := holdDuration_isProbabilityMeasure
        (deathRate_pos (two_le_blocks_of_not_le_one s hr))
      haveI := isProbabilityMeasure_bind_jumpStep ξ (two_le_blocks_of_not_le_one s hr)
        (fun η ↦ connectionTimeLaw s η.1) fun η ↦ ih η.1 η.2
      infer_instance

/-- **The mean of the connection-time law is the first-step mean connection time.** -/
theorem lintegral_coe_connectionTimeLaw {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ξ) = ENNReal.ofReal (meanConnectionTime s ξ) := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [connectionTimeLaw_eq, meanConnectionTime_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · simp only [dif_pos hr, if_pos hr, lintegral_dirac, ENNReal.coe_zero, ENNReal.ofReal_zero]
    · rw [dif_neg hr, if_neg hr]
      have hk := two_le_blocks_of_not_le_one s hr
      have hd := deathRate_pos hk
      haveI := measurableSingletonClass_ER n
      haveI := holdDuration_isProbabilityMeasure hd
      haveI := isProbabilityMeasure_bind_jumpStep ξ hk (fun η ↦ connectionTimeLaw s η.1)
        fun η ↦ connectionTimeLaw_isProbabilityMeasure s η.1
      have hnn : ∀ η : {η : ER n // Covers ξ η}, 0 ≤ meanConnectionTime s η.1 := fun η ↦
        connectionValue_nonneg s (t := 0) (b := 0) (g := 1) le_rfl
          (fun _ _ ↦ le_refl (0 : ℝ)) (fun _ _ ↦ zero_le_one) η.1
      have hnext : ∫⁻ y, (y : ℝ≥0∞)
          ∂((jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1)
          = ENNReal.ofReal ((∑ η : {η : ER n // Covers ξ η}, meanConnectionTime s η.1)
            / deathRate (blocks ξ)) := by
        rw [Measure.lintegral_bind (measurable_of_finite _).aemeasurable
            measurable_coe_nnreal_ennreal.aemeasurable,
          lintegral_congr fun η ↦ ih η.1 η.2, lintegral_jumpStep ξ hk,
          sum_ofReal_mul_inv_choose_two ξ hk _ hnn]
      have hconv : ∫⁻ x, (x : ℝ≥0∞)
          ∂(holdDuration (deathRate (blocks ξ)) ∗
            (jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1)
          = ∫⁻ x, (x : ℝ≥0∞) ∂(holdDuration (deathRate (blocks ξ)))
            + ∫⁻ y, (y : ℝ≥0∞)
              ∂((jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1) := by
        rw [lintegral_conv measurable_coe_nnreal_ennreal]
        have hin : ∀ x : ℝ≥0, ∫⁻ y, ((x + y : ℝ≥0) : ℝ≥0∞)
            ∂((jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1)
            = (x : ℝ≥0∞) + ∫⁻ y, (y : ℝ≥0∞)
              ∂((jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1) := by
          intro x
          simp only [ENNReal.coe_add]
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        rw [lintegral_congr hin, lintegral_add_right _ measurable_const, lintegral_const,
          measure_univ, mul_one]
      rw [hconv, lintegral_coe_holdDuration hd, hnext,
        ← ENNReal.ofReal_add (div_nonneg zero_le_one hd.le)
          (div_nonneg (sum_nonneg fun η _ ↦ hnn η) hd.le), add_div]

/-- **The Laplace transform of the connection-time law is the first-step transform.** -/
theorem lintegral_exp_connectionTimeLaw {n : ℕ} (s : Fin n → Fin n) {t : ℝ} (ht : 0 ≤ t)
    (ξ : ER n) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * (x : ℝ)))) ∂(connectionTimeLaw s ξ)
      = ENNReal.ofReal (connectionLaplace s t ξ) := by
  have hfm : Measurable fun x : ℝ≥0 ↦ ENNReal.ofReal (Real.exp (-(t * (x : ℝ)))) :=
    (measurable_const.mul measurable_coe_nnreal_real).neg.exp.ennreal_ofReal
  induction ξ using covers_induction with
  | step ξ ih =>
    unfold connectionLaplace at ih ⊢
    rw [connectionTimeLaw_eq, connectionValue_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · simp only [dif_pos hr, if_pos hr, lintegral_dirac, Pi.one_apply, NNReal.coe_zero, mul_zero,
        neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    · rw [dif_neg hr, if_neg hr, Pi.zero_apply, zero_add]
      have hk := two_le_blocks_of_not_le_one s hr
      have hd := deathRate_pos hk
      have hdt : 0 < deathRate (blocks ξ) + t := by linarith
      haveI := measurableSingletonClass_ER n
      haveI := holdDuration_isProbabilityMeasure hd
      have hnn : ∀ η : {η : ER n // Covers ξ η}, 0 ≤ connectionValue s t 1 0 η.1 := fun η ↦
        connectionValue_nonneg s ht (b := 1) (g := 0) (fun _ _ ↦ zero_le_one)
          (fun _ _ ↦ le_refl (0 : ℝ)) η.1
      have hsplit : ∀ x y : ℝ≥0, ENNReal.ofReal (Real.exp (-(t * ((x + y : ℝ≥0) : ℝ))))
          = ENNReal.ofReal (Real.exp (-(t * (x : ℝ))))
            * ENNReal.ofReal (Real.exp (-(t * (y : ℝ)))) := by
        intro x y
        rw [NNReal.coe_add, mul_add, neg_add, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hnext : ∫⁻ y, ENNReal.ofReal (Real.exp (-(t * (y : ℝ))))
          ∂((jumpStep ξ hk).toMeasure.bind fun η ↦ connectionTimeLaw s η.1)
          = ENNReal.ofReal ((∑ η : {η : ER n // Covers ξ η}, connectionValue s t 1 0 η.1)
            / deathRate (blocks ξ)) := by
        rw [Measure.lintegral_bind (measurable_of_finite _).aemeasurable hfm.aemeasurable,
          lintegral_congr fun η ↦ ih η.1 η.2, lintegral_jumpStep ξ hk,
          sum_ofReal_mul_inv_choose_two ξ hk _ hnn]
      have hreal : (∑ η : {η : ER n // Covers ξ η}, connectionValue s t 1 0 η.1)
            / (deathRate (blocks ξ) + t)
          = deathRate (blocks ξ) / (deathRate (blocks ξ) + t)
            * ((∑ η : {η : ER n // Covers ξ η}, connectionValue s t 1 0 η.1)
              / deathRate (blocks ξ)) := by
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hdt.ne' hd.ne'), div_mul_eq_mul_div,
          div_eq_iff hdt.ne']
        ring
      rw [lintegral_conv hfm]
      simp only [hsplit, lintegral_const_mul _ hfm]
      rw [lintegral_mul_const _ hfm, lintegral_exp_holdDuration hd ht, hnext,
        ← ENNReal.ofReal_mul (div_nonneg hd.le hdt.le), ← hreal]

/-! ### The clock bounds, as statements about the law -/

/-- **(C3) for the law**: the mean connection time plus the first-step value of the correction
rate is `E(T_w) = 2 - 2/w`. -/
theorem lintegral_add_correction_bot {n : ℕ} (s : Fin n → Fin n) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ⊥)
      + ENNReal.ofReal (connectionValue s 0 0 (clockCorrectionRate s) ⊥)
      = ENNReal.ofReal (graphMeanTransitTime s) := by
  have h := meanTransitTime_sub_meanConnectionTime s ⊥
  rw [observed_bot, blocks_graphKer] at h
  have hmean : 0 ≤ meanConnectionTime s ⊥ :=
    connectionValue_nonneg s (t := 0) (b := 0) (g := 1) le_rfl
      (fun _ _ ↦ le_refl (0 : ℝ)) (fun _ _ ↦ zero_le_one) ⊥
  have hcorr := connectionValue_nonneg s (t := 0) (b := 0) (g := clockCorrectionRate s) le_rfl
    (fun _ _ ↦ le_refl (0 : ℝ)) (fun ζ hζ ↦ clockCorrectionRate_nonneg s hζ) ⊥
  rw [lintegral_coe_connectionTimeLaw, ← ENNReal.ofReal_add hmean hcorr, graphMeanTransitTime]
  congr 1
  linarith

/-- **(C4), upper bound, for the law**: `E τ_q ≤ 2 - 2/w`.

Assumes: `1 ≤ Linkage.width s`. -/
theorem lintegral_coe_connectionTimeLaw_bot_le {n : ℕ} (s : Fin n → Fin n)
    (hw : 1 ≤ Linkage.width s) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ⊥)
      ≤ ENNReal.ofReal (2 - 2 / (Linkage.width s : ℝ)) := by
  rw [lintegral_coe_connectionTimeLaw]
  exact ENNReal.ofReal_le_ofReal (meanConnectionTime_bot_le_two_sub s hw)

/-- **The upper bound is strict when `n > w ≥ 2`.** -/
theorem lintegral_coe_connectionTimeLaw_bot_lt {n : ℕ} (s : Fin n → Fin n)
    (hw : 2 ≤ Linkage.width s) (hlt : Linkage.width s < n) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ⊥) < ENNReal.ofReal (graphMeanTransitTime s) := by
  have hmean : 0 ≤ meanConnectionTime s ⊥ :=
    connectionValue_nonneg s (t := 0) (b := 0) (g := 1) le_rfl
      (fun _ _ ↦ le_refl (0 : ℝ)) (fun _ _ ↦ zero_le_one) ⊥
  have hstrict := meanConnectionTime_bot_lt s hw hlt
  rw [lintegral_coe_connectionTimeLaw]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hmean hstrict)).mpr hstrict

/-- **(C4), lower bound, for the law**: `2/(n - w + 1) - 2/n ≤ E τ_q`.

Assumes: `1 ≤ n`. -/
theorem ofReal_le_lintegral_coe_connectionTimeLaw_bot {n : ℕ} (s : Fin n → Fin n)
    (hn : 1 ≤ n) :
    ENNReal.ofReal (2 / ((n : ℝ) - Linkage.width s + 1) - 2 / (n : ℝ))
      ≤ ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ⊥) := by
  rw [lintegral_coe_connectionTimeLaw]
  exact ENNReal.ofReal_le_ofReal (two_div_sub_two_div_le_meanConnectionTime_bot s hn)

/-- **(C2), in Laplace order, for the law**: `E e^{-t τ_q} ≥ E e^{-t T_w}`. -/
theorem kingmanLaplace_width_le_lintegral_exp_connectionTimeLaw_bot {n : ℕ}
    (s : Fin n → Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (kingmanLaplace t (Linkage.width s))
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * (x : ℝ)))) ∂(connectionTimeLaw s ⊥) := by
  rw [lintegral_exp_connectionTimeLaw s ht]
  exact ENNReal.ofReal_le_ofReal (kingmanLaplace_width_le_connectionLaplace_bot s ht)

/-- **Entered at `graphKer s`, the mean connection time is `E(T_w)`.** -/
theorem lintegral_coe_connectionTimeLaw_graphKer {n : ℕ} (s : Fin n → Fin n) :
    ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s (graphKer s))
      = ENNReal.ofReal (graphMeanTransitTime s) := by
  rw [lintegral_coe_connectionTimeLaw, meanConnectionTime_graphKer]

/-- **Entered at `graphKer s`, the connection time has the transform of K-G's transit time `T_w`**
under the corpus clock of independent holding times, K-G (5.9). -/
theorem lintegral_exp_connectionTimeLaw_graphKer {n : ℕ} (s : Fin n → Fin n) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * (x : ℝ)))) ∂(connectionTimeLaw s (graphKer s))
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (-(t * ∑ k ∈ range (Linkage.width s - 1), ω k)))
          ∂(holdProduct deathRate fun k ↦ deathRate_pos (by omega)) := by
  rw [lintegral_exp_connectionTimeLaw s ht, connectionLaplace_graphKer s ht,
    kingman_transitTransform ht, kingmanLaplace, ENNReal.ofReal_prod_of_nonneg]
  intro k _
  exact div_nonneg (deathRate_add_two_pos k).le (add_nonneg (deathRate_add_two_pos k).le ht)

end

end Descent.Pangenome.GraphCoalescent
