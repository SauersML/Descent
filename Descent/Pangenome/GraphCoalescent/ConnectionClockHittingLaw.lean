/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockHittingTime
import Descent.Pangenome.GraphCoalescent.ReportedConnectionSpectrum
import Descent.Pangenome.GraphCoalescent.ReportedConnectionTies

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The law of the first hitting time of `⊤` by the report of the path

`Descent.Pangenome.GraphCoalescent.ConnectionClockHittingTime` proves that, on every trajectory of
the corpus path, the first time the report of `Path.pathState` reaches `⊤` is the reported
connection time `connectionTime s p`, and that the two have one mean. This file identifies the
law. Under the path law `trajectoryClockLaw n` (a jump-chain trajectory with an independent Kingman
clock) the hitting time has the first-step law `ConnectionClockPathLaw.connectionTimeLaw s ⊥` as a
measure (`map_reportHittingTime_eq_connectionTimeLaw`).

## The route

* `levelTransitLaw b K` is the time to descend from `K` blocks to `b` blocks: one holding duration
  at each level `b + 1, …, K`. The clock coordinates of those levels add up to it
  (`map_sum_kingmanClock`), by the independence of the coordinates of `Measure.infinitePi`.
* The path law of the connection time mixes these laws over the stopping level:
  `P(τ_q ∈ ·) = ∑_{b=1}^{n} p_b · levelTransitLaw b n` (`map_connectionTime_eq_sum`).
* The first-step law unrolls level by level from `⊥` (`connectionTimeLaw_bot_unroll`). After `j`
  jumps it is the mixture over the levels passed, plus the descent to level `n - j` followed by the
  connection-time laws of the unconnected states there, weighted by the head law
  (`unconnectedMix`). One more level splits off the mass that connects on the next jump
  (`unconnectedMix_succ`). That mass is `FirstConnectionLaw.firstConnectionProbability`, which
  `ReportedConnectionTies` identifies with `p_b`. At level `1` every report is connected, so
  `connectionTimeLaw s ⊥` is the same mixture (`connectionTimeLaw_bot_eq_sum`).

With the law identified, the spectral form of §6
(`ReportedConnectionSpectrum.survivalAt_connectionTimeLaw_bot`) and the stochastic order (C2)
(`ConnectionClockStochasticOrder.survivalAt_connectionTimeLaw_bot_le`) hold for the hitting time
itself (`survivalAt_reportHittingTime`, `survivalAt_reportHittingTime_le`).

## Empirical status

None. The bodies are identities between measures built from the corpus jump law, holding law and
product clock, and finite sums over the equivalence relations of a finite set; no measurement can
bear on them.
-/

set_option autoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset MeasureTheory
open scoped Classical NNReal ENNReal

noncomputable section

/-! ### Finite mixtures of measures -/

/-- A finite weighted sum of s-finite measures is s-finite. -/
theorem sFinite_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (μ : ι → Measure ℝ≥0)
    (hμ : ∀ i, SFinite (μ i)) : SFinite (∑ i, c i • μ i) := by
  rw [← Measure.sum_fintype]
  haveI := hμ
  infer_instance

/-- A finite sum of s-finite measures is s-finite. -/
theorem sFinite_finset_sum {ι : Type*} (t : Finset ι) (μ : ι → Measure ℝ≥0)
    (hμ : ∀ i, SFinite (μ i)) : SFinite (∑ i ∈ t, μ i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [sum_empty]
      infer_instance
  | insert i t hi ih =>
      rw [sum_insert hi]
      haveI := hμ i
      haveI := ih
      infer_instance

/-- Convolution distributes over finite sums. -/
theorem conv_finset_sum {ι : Type*} (t : Finset ι) (ν : Measure ℝ≥0) [SFinite ν]
    (μ : ι → Measure ℝ≥0) (hμ : ∀ i, SFinite (μ i)) :
    ν ∗ (∑ i ∈ t, μ i) = ∑ i ∈ t, ν ∗ μ i := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, Measure.conv_zero]
  | insert i t hi ih =>
      haveI := hμ i
      haveI := sFinite_finset_sum t μ hμ
      rw [sum_insert hi, sum_insert hi, Measure.conv_add, ih]

/-- **A uniform jump is the mixture of the targets under the jump law.** -/
theorem bind_jumpStep_eq_sum {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ) (μ : ER n → Measure ℝ≥0) :
    (jumpStep ξ hk).toMeasure.bind (fun η ↦ μ η.1) = ∑ η : ER n, jumpLaw ξ η • μ η := by
  haveI := measurableSingletonClass_ER n
  ext A hA
  rw [Measure.bind_apply hA (measurable_of_finite _).aemeasurable, lintegral_jumpStep ξ hk,
    Measure.finset_sum_apply, sum_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hcov : ∀ η : ER n, jumpLaw ξ η * μ η A
      = if Covers ξ η then μ η A * (((blocks ξ).choose 2 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
    intro η
    by_cases h : Covers ξ η
    · rw [if_pos h, jumpLaw_apply_cover hk h, mul_comm]
    · rw [if_neg h, (PMF.apply_eq_zero_iff _ _).mpr fun hmem ↦ h ((mem_support_jumpLaw hk).mp hmem),
        zero_mul]
  rw [sum_congr rfl fun η _ ↦ hcov η, ← sum_filter]
  exact (sum_subtype _ (fun η ↦ by simp) fun η ↦ μ η A * (((blocks ξ).choose 2 : ℕ) : ℝ≥0∞)⁻¹).symm

/-- The first-step law from an unconnected state, with the jump written as a mixture. -/
theorem connectionTimeLaw_of_ne_top {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) {ξ : ER n}
    (hξ : observed s ξ ≠ ⊤) :
    connectionTimeLaw s ξ
      = holdDuration (deathRate (blocks ξ))
        ∗ (∑ η : ER n, jumpLaw ξ η • connectionTimeLaw s η) := by
  have hr : ¬ blocks (observed s ξ) ≤ 1 := fun h ↦ hξ ((blocks_observed_le_one_iff hn s ξ).mp h)
  rw [connectionTimeLaw_eq, dif_neg hr,
    bind_jumpStep_eq_sum ξ (two_le_blocks_of_not_le_one s hr) (connectionTimeLaw s)]

/-! ### The holding times of a block of levels -/

/-- **The time to descend from `K` blocks to `b` blocks**: one independent holding duration at
each level `b + 1, …, K`, at that level's death rate. -/
def levelTransitLaw (b : ℕ) : ℕ → Measure ℝ≥0
  | 0 => Measure.dirac 0
  | K + 1 =>
      if K + 1 ≤ b then Measure.dirac 0
      else holdDuration (deathRate (K + 1)) ∗ levelTransitLaw b K

theorem levelTransitLaw_succ_eq (b K : ℕ) :
    levelTransitLaw b (K + 1)
      = if K + 1 ≤ b then Measure.dirac 0
        else holdDuration (deathRate (K + 1)) ∗ levelTransitLaw b K := rfl

theorem levelTransitLaw_of_le {b K : ℕ} (hK : K ≤ b) : levelTransitLaw b K = Measure.dirac 0 := by
  cases K with
  | zero => rfl
  | succ K => rw [levelTransitLaw_succ_eq, if_pos hK]

theorem levelTransitLaw_succ {b K : ℕ} (hbK : b ≤ K) :
    levelTransitLaw b (K + 1) = holdDuration (deathRate (K + 1)) ∗ levelTransitLaw b K := by
  rw [levelTransitLaw_succ_eq, if_neg (by omega)]

theorem levelTransitLaw_isProbabilityMeasure {b : ℕ} (hb : 1 ≤ b) :
    ∀ K, IsProbabilityMeasure (levelTransitLaw b K)
  | 0 => show IsProbabilityMeasure (Measure.dirac (0 : ℝ≥0)) from inferInstance
  | K + 1 => by
      by_cases hK : K + 1 ≤ b
      · rw [levelTransitLaw_of_le hK]
        infer_instance
      · rw [levelTransitLaw_succ (show b ≤ K by omega)]
        haveI := holdDuration_isProbabilityMeasure (deathRate_pos (show 2 ≤ K + 1 by omega))
        haveI := levelTransitLaw_isProbabilityMeasure hb K
        infer_instance

/-- **Peeling the lowest level**: the descent to `b` is the descent to `b + 1` followed by the
holding time at level `b + 1`. -/
theorem levelTransitLaw_pred {b : ℕ} (hb : 1 ≤ b) {K : ℕ} (hbK : b + 1 ≤ K) :
    levelTransitLaw b K = levelTransitLaw (b + 1) K ∗ holdDuration (deathRate (b + 1)) := by
  haveI := holdDuration_isProbabilityMeasure (deathRate_pos (show 2 ≤ b + 1 by omega))
  induction K, hbK using Nat.le_induction with
  | base =>
      rw [levelTransitLaw_succ le_rfl, levelTransitLaw_of_le le_rfl, levelTransitLaw_of_le le_rfl,
        Measure.conv_dirac_zero, Measure.dirac_zero_conv]
  | succ K hK ih =>
      haveI := levelTransitLaw_isProbabilityMeasure (show 1 ≤ b + 1 by omega) K
      rw [levelTransitLaw_succ (b := b) (K := K) (by omega), ih, levelTransitLaw_succ hK,
        Measure.conv_assoc]

/-- The clock's coordinates are independent. -/
theorem iIndepFun_kingmanClock :
    ProbabilityTheory.iIndepFun (fun (j : ℕ) (ω : ℕ → ℝ) ↦ ω j) kingmanClock := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (deathRate (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (deathRate_add_two_pos k)
  unfold kingmanClock holdProduct
  exact ProbabilityTheory.iIndepFun_infinitePi (X := fun _ (t : ℝ) ↦ t) fun _ ↦ measurable_id

/-- A clock coordinate, read as a duration, is a holding duration. -/
theorem map_toNNReal_coord_kingmanClock (j : ℕ) :
    kingmanClock.map (fun ω : ℕ → ℝ ↦ Real.toNNReal (ω j)) = holdDuration (deathRate (j + 2)) := by
  have h := Measure.map_map (μ := kingmanClock) measurable_real_toNNReal (measurable_pi_apply j)
  rw [(kingmanClock_eval j).map_eq] at h
  exact h.symm

/-- **The law of a block of clock coordinates.** The coordinates `b - 1, …, K - 2`, the holding
times at levels `b + 1, …, K`, add up to `levelTransitLaw b K`. -/
theorem map_sum_kingmanClock {b : ℕ} (hb : 1 ≤ b) {K : ℕ} (hbK : b ≤ K) :
    kingmanClock.map (fun ω : ℕ → ℝ ↦ Real.toNNReal (∑ j ∈ Ico (b - 1) (K - 1), ω j))
      = levelTransitLaw b K := by
  induction K, hbK using Nat.le_induction with
  | base =>
      rw [levelTransitLaw_of_le le_rfl]
      simp only [Ico_self, sum_empty, Real.toNNReal_zero]
      rw [Measure.map_const, measure_univ, one_smul]
  | succ K hK ih =>
      have hK1 : K + 1 - 1 = K - 1 + 1 := by omega
      have hsplit : ∀ ω : ℕ → ℝ, ∑ j ∈ Ico (b - 1) (K + 1 - 1), ω j
          = ∑ j ∈ Ico (b - 1) (K - 1), ω j + ω (K - 1) := fun ω ↦ by
        rw [hK1, sum_Ico_succ_top (show b - 1 ≤ K - 1 by omega)]
      have hae : (fun ω : ℕ → ℝ ↦ Real.toNNReal (∑ j ∈ Ico (b - 1) (K + 1 - 1), ω j))
          =ᵐ[kingmanClock] (fun ω ↦ Real.toNNReal (ω (K - 1)))
            + fun ω ↦ Real.toNNReal (∑ j ∈ Ico (b - 1) (K - 1), ω j) := by
        filter_upwards [ae_nonneg_kingmanClock] with ω hω
        show Real.toNNReal (∑ j ∈ Ico (b - 1) (K + 1 - 1), ω j)
          = Real.toNNReal (ω (K - 1)) + Real.toNNReal (∑ j ∈ Ico (b - 1) (K - 1), ω j)
        rw [hsplit ω, add_comm (∑ j ∈ Ico (b - 1) (K - 1), ω j) (ω (K - 1)),
          Real.toNNReal_add (hω _) (sum_nonneg fun j _ ↦ hω j)]
      have hf : Measurable fun ω : ℕ → ℝ ↦ Real.toNNReal (ω (K - 1)) :=
        measurable_real_toNNReal.comp (measurable_pi_apply _)
      have hg : Measurable fun ω : ℕ → ℝ ↦ Real.toNNReal (∑ j ∈ Ico (b - 1) (K - 1), ω j) :=
        measurable_real_toNNReal.comp (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)
      have hind : ProbabilityTheory.IndepFun (fun ω : ℕ → ℝ ↦ Real.toNNReal (ω (K - 1)))
          (fun ω ↦ Real.toNNReal (∑ j ∈ Ico (b - 1) (K - 1), ω j)) kingmanClock := by
        have h := iIndepFun_kingmanClock.indepFun_finset_sum_of_notMem
          (fun j ↦ measurable_pi_apply j) (s := Ico (b - 1) (K - 1)) (i := K - 1)
          (by rw [mem_Ico]; omega)
        have hfun : (∑ j ∈ Ico (b - 1) (K - 1), fun ω : ℕ → ℝ ↦ ω j)
            = fun ω ↦ ∑ j ∈ Ico (b - 1) (K - 1), ω j := by
          funext ω
          simp only [Finset.sum_apply]
        rw [hfun] at h
        exact h.symm.comp measurable_real_toNNReal measurable_real_toNNReal
      rw [Measure.map_congr hae, hind.map_add_eq_map_conv_map hf hg,
        map_toNNReal_coord_kingmanClock, ih, levelTransitLaw_succ hK,
        show K - 1 + 2 = K + 1 by omega]

/-! ### The path law as a mixture over the stopping level -/

/-- The connection time, as a duration, is a measurable function of the path. -/
theorem measurable_toNNReal_connectionTime {n : ℕ} (s : Fin n → Fin n) :
    Measurable fun p : List (ER n) × (ℕ → ℝ) ↦ Real.toNNReal (connectionTime s p) := by
  have hsum : ∀ b : ℕ, Measurable fun ω : ℕ → ℝ ↦
      Real.toNNReal (∑ j ∈ Ico (b - 1) (n - 1), ω j) := fun b ↦
    measurable_real_toNNReal.comp (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)
  have hswap : Measurable fun q : (ℕ → ℝ) × List (ER n) ↦
      Real.toNNReal (∑ j ∈ Ico (stoppingLevel s q.2 - 1) (n - 1), q.1 j) :=
    measurable_from_prod_countable_left fun l ↦ hsum (stoppingLevel s l)
  -- composed without an expected type: propagating `Measurable (toNNReal ∘ connectionTime s)`
  -- into `?g ∘ ?f` splits it at `toNNReal` and times out
  have h := hswap.comp measurable_swap
  exact h

/-- **One level of the mixture**: integrating against `levelTransitLaw b n` is integrating the
block of clock coordinates it collects. -/
theorem lintegral_levelTransitLaw {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) {g : ℝ≥0 → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(levelTransitLaw b n)
      = ∫⁻ ω, g (Real.toNNReal (∑ j ∈ Ico (b - 1) (n - 1), ω j)) ∂kingmanClock := by
  have hmeas : Measurable fun ω : ℕ → ℝ ↦ Real.toNNReal (∑ j ∈ Ico (b - 1) (n - 1), ω j) :=
    measurable_real_toNNReal.comp (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)
  rw [← map_sum_kingmanClock hb hbn, lintegral_map hg hmeas]

/-- **The path law of the connection time mixes the level-transit laws over the stopping
level**: `P(τ_q ∈ ·) = ∑_{b=1}^{n} p_b · levelTransitLaw b n`. -/
theorem map_connectionTime_eq_sum {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (trajectoryClockLaw n).map (fun p ↦ Real.toNNReal (connectionTime s p))
      = ∑ b ∈ Icc 1 n, stoppingLaw s b • levelTransitLaw b n := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  have hF : ∀ b : ℕ, Measurable fun ω : ℕ → ℝ ↦
      g (Real.toNNReal (∑ j ∈ Ico (b - 1) (n - 1), ω j)) := fun b ↦
    hg.comp (measurable_real_toNNReal.comp
      (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j))
  have hmix := lintegral_trajectoryClockLaw hn s
    (fun b ω ↦ g (Real.toNNReal (∑ j ∈ Ico (b - 1) (n - 1), ω j))) hF
  rw [lintegral_map hg (measurable_toNNReal_connectionTime s), lintegral_finset_sum_measure]
  simp only [connectionTime]
  refine hmix.trans (sum_congr rfl fun b hb ↦ ?_)
  rw [lintegral_smul_measure, lintegral_levelTransitLaw (mem_Icc.mp hb).1 (mem_Icc.mp hb).2 hg,
    smul_eq_mul]

/-! ### The first-step law as the same mixture -/

/-- The connection-time laws of the unconnected states after `j` jumps, weighted by the head
law. -/
def unconnectedMix {n : ℕ} (s : Fin n → Fin n) (j : ℕ) : Measure ℝ≥0 :=
  ∑ ξ : ER n, (if observed s ξ = ⊤ then 0 else blockLaw n j ξ) • connectionTimeLaw s ξ

theorem unconnectedMix_sFinite {n : ℕ} (s : Fin n → Fin n) (j : ℕ) :
    SFinite (unconnectedMix s j) := by
  unfold unconnectedMix
  exact sFinite_sum_smul _ _ fun ξ ↦ by
    haveI := connectionTimeLaw_isProbabilityMeasure s ξ
    infer_instance

/-- The mass that is unconnected after `j` jumps and connected after one more. -/
def firstConnectionMass {n : ℕ} (s : Fin n → Fin n) (j : ℕ) : ℝ≥0∞ :=
  ∑ ξ : ER n, ∑ η : ER n, blockLaw n j ξ * jumpLaw ξ η *
    if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0

theorem ofReal_firstConnectionProbability {n : ℕ} (s : Fin n → Fin n) (b : ℕ) :
    ENNReal.ofReal (firstConnectionProbability s b) = firstConnectionMass s (n - (b + 1)) := by
  have hterm : ∀ ξ η : ER n,
      ENNReal.ofReal ((blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal *
        if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0)
      = blockLaw n (n - (b + 1)) ξ * jumpLaw ξ η *
        if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0 := by
    intro ξ η
    split_ifs
    · rw [mul_one, mul_one, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    · rw [mul_zero, mul_zero, ENNReal.ofReal_zero]
  have hnn : ∀ ξ η : ER n, 0 ≤ (blockLaw n (n - (b + 1)) ξ).toReal * (jumpLaw ξ η).toReal *
      if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then (1 : ℝ) else 0 := fun ξ η ↦
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by split_ifs <;> norm_num)
  unfold firstConnectionProbability firstConnectionMass
  rw [ENNReal.ofReal_sum_of_nonneg fun ξ _ ↦ sum_nonneg fun η _ ↦ hnn ξ η]
  refine sum_congr rfl fun ξ _ ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun η _ ↦ hnn ξ η]
  exact sum_congr rfl fun η _ ↦ hterm ξ η

/-- **`p_b` is the mass that first connects on the jump to `b` blocks.** -/
theorem stoppingLaw_eq_firstConnectionMass {n b : ℕ} (s : Fin n → Fin n) (hb : 1 ≤ b)
    (hbn : b < n) : stoppingLaw s b = firstConnectionMass s (n - (b + 1)) := by
  rw [← ofReal_firstConnectionProbability, ← stoppingProb_eq_firstConnectionProbability s hb hbn,
    stoppingProb, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- `p_n` is the indicator that the report of `⊥` is connected. -/
theorem stoppingLaw_self_eq {n : ℕ} (hn : 1 ≤ n) (s : Fin n → Fin n) :
    stoppingLaw s n = if observed s ⊥ = ⊤ then 1 else 0 := by
  have h : stoppingLaw s n = ENNReal.ofReal (connectedProb s n) := by
    rw [stoppingLaw_apply, ofReal_connectedProb s hn le_rfl]
    congr 1
    ext l
    exact stoppingLevel_eq_self_iff hn
  have hlaw : blockLaw n 0 = PMF.pure (Delta n) := by
    rw [blockLaw_eq_map, chainLaw, PMF.pure_map]
    rfl
  rw [h, connectedProb, Nat.sub_self, hlaw]
  by_cases hc : observed s ⊥ = ⊤
  · have hmem : (⊥ : ER n) ∈ univ.filter (fun π : ER n ↦ observed s π = ⊤) :=
      mem_filter.mpr ⟨mem_univ _, hc⟩
    have hzero : ∀ π ∈ univ.filter (fun π : ER n ↦ observed s π = ⊤), π ≠ ⊥ →
        (PMF.pure (Delta n) π).toReal = 0 := fun π _ hπ ↦ by
      rw [PMF.pure_apply, if_neg hπ, ENNReal.toReal_zero]
    rw [if_pos hc, sum_eq_single_of_mem _ hmem hzero, PMF.pure_apply, if_pos rfl,
      ENNReal.toReal_one, ENNReal.ofReal_one]
  · have hzero : ∀ π ∈ univ.filter (fun π : ER n ↦ observed s π = ⊤),
        (PMF.pure (Delta n) π).toReal = 0 := by
      intro π hπ
      have hπ' : π ≠ ⊥ := fun h ↦ hc (by subst h; exact (mem_filter.mp hπ).2)
      rw [PMF.pure_apply, if_neg hπ', ENNReal.toReal_zero]
    rw [if_neg hc, sum_eq_zero hzero, ENNReal.ofReal_zero]

/-- Before any jump, the unconnected mixture is the law from `⊥` when its report is not
connected. -/
theorem unconnectedMix_zero {n : ℕ} (s : Fin n → Fin n) :
    unconnectedMix s 0 = (if observed s ⊥ = ⊤ then (0 : ℝ≥0∞) else 1) • connectionTimeLaw s ⊥ := by
  have hlaw : blockLaw n 0 = PMF.pure (Delta n) := by
    rw [blockLaw_eq_map, chainLaw, PMF.pure_map]
    rfl
  have hzero : ∀ ξ ∈ (univ : Finset (ER n)), ξ ≠ ⊥ →
      (if observed s ξ = ⊤ then 0 else PMF.pure (Delta n) ξ) • connectionTimeLaw s ξ = 0 := by
    intro ξ _ hξ
    rw [PMF.pure_apply, if_neg hξ, ite_self, zero_smul]
  unfold unconnectedMix
  rw [hlaw, sum_eq_single_of_mem _ (mem_univ _) hzero, PMF.pure_apply, if_pos rfl]

/-- **One level of the unrolling.** The unconnected states after `j` jumps hold at rate `d_{n-j}`
and jump; the covers that connect contribute a point mass at `0`, and the others are the
unconnected states after `j + 1` jumps. -/
theorem unconnectedMix_succ {n : ℕ} (s : Fin n → Fin n) {j : ℕ} (hj : j + 2 ≤ n) :
    unconnectedMix s j = holdDuration (deathRate (n - j))
      ∗ (firstConnectionMass s j • Measure.dirac 0 + unconnectedMix s (j + 1)) := by
  have hn : 0 < n := by omega
  have hsf : ∀ ξ : ER n, SFinite (connectionTimeLaw s ξ) := fun ξ ↦ by
    haveI := connectionTimeLaw_isProbabilityMeasure s ξ
    infer_instance
  haveI := holdDuration_isProbabilityMeasure (deathRate_pos (show 2 ≤ n - j by omega))
  -- one holding time and one jump from each unconnected state
  have hrow : ∀ ξ : ER n,
      (if observed s ξ = ⊤ then 0 else blockLaw n j ξ) • connectionTimeLaw s ξ
        = holdDuration (deathRate (n - j))
          ∗ (∑ η : ER n, ((if observed s ξ = ⊤ then 0 else blockLaw n j ξ) * jumpLaw ξ η)
            • connectionTimeLaw s η) := by
    intro ξ
    by_cases hc : observed s ξ = ⊤
    · simp only [if_pos hc, zero_smul, zero_mul, sum_const_zero, Measure.conv_zero]
    · by_cases hmem : ξ ∈ (blockLaw n j).support
      · have hb : blocks ξ = n - j := by
          have := blocks_of_mem_support_blockLaw (show j < n by omega) hmem
          omega
        haveI : SFinite (∑ η : ER n, jumpLaw ξ η • connectionTimeLaw s η) :=
          sFinite_sum_smul _ _ hsf
        rw [if_neg hc, connectionTimeLaw_of_ne_top hn s hc, hb, ← Measure.conv_smul_right,
          Finset.smul_sum]
        simp only [smul_smul]
      · have hzero : blockLaw n j ξ = 0 := (PMF.apply_eq_zero_iff _ _).mpr hmem
        simp only [if_neg hc, hzero, zero_smul, zero_mul, sum_const_zero, Measure.conv_zero]
  have hX : ∀ ξ : ER n, SFinite (∑ η : ER n,
      ((if observed s ξ = ⊤ then 0 else blockLaw n j ξ) * jumpLaw ξ η) • connectionTimeLaw s η) :=
    fun ξ ↦ sFinite_sum_smul _ _ hsf
  -- exchange the two sums
  have hswap : ∑ ξ : ER n, ∑ η : ER n,
        ((if observed s ξ = ⊤ then 0 else blockLaw n j ξ) * jumpLaw ξ η) • connectionTimeLaw s η
      = ∑ η : ER n, (∑ ξ : ER n, (if observed s ξ = ⊤ then 0 else blockLaw n j ξ) * jumpLaw ξ η)
          • connectionTimeLaw s η := by
    rw [sum_comm]
    simp only [Finset.sum_smul]
  -- a connected cover contributes a point mass, an unconnected one its own law
  have hcol : ∀ η : ER n,
      (∑ ξ : ER n, (if observed s ξ = ⊤ then 0 else blockLaw n j ξ) * jumpLaw ξ η)
          • connectionTimeLaw s η
        = (∑ ξ : ER n, blockLaw n j ξ * jumpLaw ξ η
            * if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0) • Measure.dirac 0
          + (if observed s η = ⊤ then 0 else blockLaw n (j + 1) η) • connectionTimeLaw s η := by
    intro η
    by_cases hη : observed s η = ⊤
    · have hdirac : connectionTimeLaw s η = Measure.dirac 0 := by
        rw [connectionTimeLaw_eq, dif_pos ((blocks_observed_le_one_iff hn s η).mpr hη)]
      rw [if_pos hη, zero_smul, add_zero, hdirac]
      congr 1
      refine sum_congr rfl fun ξ _ ↦ ?_
      by_cases hξ : observed s ξ = ⊤
      · rw [if_pos hξ, if_neg (show ¬(observed s ξ ≠ ⊤ ∧ observed s η = ⊤) from fun h ↦ h.1 hξ),
          zero_mul, mul_zero]
      · rw [if_neg hξ, if_pos (show observed s ξ ≠ ⊤ ∧ observed s η = ⊤ from ⟨hξ, hη⟩), mul_one]
    · have hsum : ∑ ξ : ER n, (if observed s ξ = ⊤ then 0 else blockLaw n j ξ) * jumpLaw ξ η
          = blockLaw n (j + 1) η := by
        rw [blockLaw_succ, PMF.bind_apply, tsum_fintype]
        refine sum_congr rfl fun ξ _ ↦ ?_
        by_cases hξ : observed s ξ = ⊤
        · have hjump : jumpLaw ξ η = 0 := (PMF.apply_eq_zero_iff _ _).mpr fun hmem ↦
            hη (top_unique (hξ.symm.le.trans (observed_mono s (le_of_mem_support_jumpLaw hmem))))
          rw [if_pos hξ, hjump, mul_zero, mul_zero]
        · rw [if_neg hξ]
      have hterm : ∀ ξ : ER n, blockLaw n j ξ * jumpLaw ξ η
          * (if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0) = 0 := fun ξ ↦ by
        rw [if_neg (show ¬(observed s ξ ≠ ⊤ ∧ observed s η = ⊤) from fun h ↦ hη h.2), mul_zero]
      rw [if_neg hη, hsum, sum_congr rfl fun ξ _ ↦ hterm ξ, sum_const_zero, zero_smul, zero_add]
  have hmass : ∑ η : ER n, ∑ ξ : ER n, blockLaw n j ξ * jumpLaw ξ η
      * (if observed s ξ ≠ ⊤ ∧ observed s η = ⊤ then 1 else 0) = firstConnectionMass s j := by
    rw [firstConnectionMass, sum_comm]
  unfold unconnectedMix
  rw [sum_congr rfl fun ξ _ ↦ hrow ξ,
    ← conv_finset_sum univ (holdDuration (deathRate (n - j))) _ hX, hswap,
    sum_congr rfl fun η _ ↦ hcol η, sum_add_distrib, ← Finset.sum_smul, hmass]

/-- **The level-by-level unrolling from `⊥`.** After `j` jumps, the first-step law from `⊥` is the
first-connection mixture over the levels passed, plus the descent to level `n - j` followed by the
unconnected mixture there. -/
theorem connectionTimeLaw_bot_unroll {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    ∀ j, j + 1 ≤ n → connectionTimeLaw s ⊥
      = (∑ b ∈ Ico (n - j) (n + 1), stoppingLaw s b • levelTransitLaw b n)
        + levelTransitLaw (n - j) n ∗ unconnectedMix s j := by
  intro j
  induction j with
  | zero =>
      intro _
      haveI := connectionTimeLaw_isProbabilityMeasure s (⊥ : ER n)
      rw [Nat.sub_zero, Nat.Ico_succ_singleton, sum_singleton, levelTransitLaw_of_le le_rfl,
        stoppingLaw_self_eq (show 1 ≤ n by omega) s, unconnectedMix_zero s, Measure.dirac_zero_conv]
      by_cases hc : observed s ⊥ = ⊤
      · rw [if_pos hc, if_pos hc, one_smul, zero_smul, add_zero, connectionTimeLaw_eq,
          dif_pos ((blocks_observed_le_one_iff (show 0 < n by omega) s ⊥).mpr hc)]
      · rw [if_neg hc, if_neg hc, zero_smul, one_smul, zero_add]
  | succ j ih =>
      intro hj
      have hb1 : 1 ≤ n - (j + 1) := by omega
      have hbn : n - (j + 1) < n := by omega
      have hmass : firstConnectionMass s j = stoppingLaw s (n - (j + 1)) := by
        rw [stoppingLaw_eq_firstConnectionMass s hb1 hbn, show n - (n - (j + 1) + 1) = j by omega]
      haveI := holdDuration_isProbabilityMeasure (deathRate_pos (show 2 ≤ n - j by omega))
      haveI := levelTransitLaw_isProbabilityMeasure (show 1 ≤ n - j by omega) n
      haveI := levelTransitLaw_isProbabilityMeasure hb1 n
      haveI := unconnectedMix_sFinite s (j + 1)
      rw [ih (by omega), unconnectedMix_succ s (show j + 2 ≤ n by omega), ← Measure.conv_assoc,
        show n - j = n - (j + 1) + 1 by omega,
        ← levelTransitLaw_pred hb1 (show n - (j + 1) + 1 ≤ n by omega), Measure.conv_add,
        Measure.conv_smul_right, Measure.conv_dirac_zero, hmass,
        sum_eq_sum_Ico_succ_bot (show n - (j + 1) < n + 1 by omega), add_assoc, add_left_comm]

/-- **The first-step law from `⊥` mixes the level-transit laws over the stopping level.** -/
theorem connectionTimeLaw_bot_eq_sum {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    connectionTimeLaw s ⊥ = ∑ b ∈ Icc 1 n, stoppingLaw s b • levelTransitLaw b n := by
  have hzero : unconnectedMix s (n - 1) = 0 := by
    unfold unconnectedMix
    refine sum_eq_zero fun ξ _ ↦ ?_
    by_cases hmem : ξ ∈ (blockLaw n (n - 1)).support
    · have hb : blocks ξ = 1 := by
        have := blocks_of_mem_support_blockLaw (show n - 1 < n by omega) hmem
        omega
      have hc : observed s ξ = ⊤ := (blocks_observed_le_one_iff (show 0 < n by omega) s ξ).mp
        ((blocks_antitone (le_observed s ξ)).trans hb.le)
      rw [if_pos hc, zero_smul]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, ite_self, zero_smul]
  have hIcc : Ico 1 (n + 1) = Icc 1 n := by
    ext b
    simp only [mem_Ico, mem_Icc]
    omega
  rw [connectionTimeLaw_bot_unroll hn s (n - 1) (by omega), hzero, Measure.conv_zero, add_zero,
    show n - (n - 1) = 1 by omega, hIcc]

/-! ### The law of the hitting time -/

/-- **The path law of the connection time is the first-step law from `⊥`.** -/
theorem map_connectionTime_eq_connectionTimeLaw {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (trajectoryClockLaw n).map (fun p ↦ Real.toNNReal (connectionTime s p))
      = connectionTimeLaw s ⊥ := by
  rw [map_connectionTime_eq_sum hn s, connectionTimeLaw_bot_eq_sum hn s]

/-- **The first hitting time of `⊤` by the report of the path has law
`connectionTimeLaw s ⊥`.** -/
theorem map_reportHittingTime_eq_connectionTimeLaw {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) :
    (trajectoryClockLaw n).map (fun p ↦ Real.toNNReal (reportHittingTime s p.1 (clockHold p.2)))
      = connectionTimeLaw s ⊥ := by
  rw [map_reportHittingTime_eq_map_connectionTime hn s,
    map_connectionTime_eq_connectionTimeLaw hn s]

/-- **The spectral statement of §6 for the hitting time**: for `c ≥ 0`, the probability that the
report of the path is not yet connected at time `c` is `∑_{k=2}^{n} spectralCoeff s ⊥ k e^{-d_k c}`.
-/
theorem survivalAt_reportHittingTime {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) {c : ℝ}
    (hc : 0 ≤ c) :
    survivalAt ((trajectoryClockLaw n).map
        fun p ↦ Real.toNNReal (reportHittingTime s p.1 (clockHold p.2))) c
      = ENNReal.ofReal (∑ k ∈ Ioc 1 n, spectralCoeff s ⊥ k * Real.exp (-(deathRate k * c))) := by
  rw [map_reportHittingTime_eq_connectionTimeLaw hn s, survivalAt_connectionTimeLaw_bot s hc]

/-- **(C2) for the hitting time**: it is stochastically dominated by K-G's transit time from the
interface width. -/
theorem survivalAt_reportHittingTime_le {n : ℕ} (hn : 2 ≤ n) (s : Fin n → Fin n) (c : ℝ) :
    survivalAt ((trajectoryClockLaw n).map
        fun p ↦ Real.toNNReal (reportHittingTime s p.1 (clockHold p.2))) c
      ≤ survivalAt (kingmanTransitLaw (Linkage.width s)) c := by
  rw [map_reportHittingTime_eq_connectionTimeLaw hn s]
  exact survivalAt_connectionTimeLaw_bot_le s c

end

end Descent.Pangenome.GraphCoalescent
