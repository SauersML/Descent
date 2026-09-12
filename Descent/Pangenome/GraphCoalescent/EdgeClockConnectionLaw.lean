/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionExamples
import Descent.Pangenome.GraphCoalescent.ScaledConnectionLimit
import Mathlib.Probability.Distributions.Exponential

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The connection time `T_p` as a function of independent exponential edge clocks

(F3) of the hidden-clock note names its limit `T_p`: the connection time of the random graph on
the `w` fibers whose edge `{i, j}` switches on at an independent exponential clock of rate
`p_i p_j`.  `MultiplicativeConnectionLaw.connectionProbability p u` is the probability that the
edges switched on by time `u` connect the fibers, computed from the configuration at the fixed
time `u`, and `MultiplicativeConnectionInLaw.randomGraphConnectionLaw` is the probability measure
with that distribution function.  This file builds the clocks and the connection time itself,
and proves that the law of the connection time is that measure.

## The construction

`edgeClockLaw p` is the product of the exponential laws `expMeasure (p_i p_j)` over the edges.  A
point `ω` of it assigns a ringing time to every edge; `rungEdges ω u` is the configuration of the
edges that have rung by `u`, and `edgeConnectionTime ω` is the least time at which some
connected configuration has entirely rung, the least over connected configurations `G` of the
latest clock of `G`.

## Main results

- `edgeConnectionTime_le_iff`: `T_p ≤ u` exactly when `u ≥ 0` and the edges rung by `u` connect
  the fibers.
- `measurable_edgeConnectionTime`: `T_p` is a random variable.
- `expMeasure_Iic_eq`, `expMeasure_Ioi_eq`: an exponential clock has rung by `u` with probability
  `1 - e^{-u r}`.
- `edgeClockLaw_preimage_Iic`: **`Pr(T_p ≤ u) = connectionProbability p u`** for `u ≥ 0`, by the
  independence of the clocks.
- `cdf_map_edgeConnectionTime`: the distribution function of `T_p` is `connectionTimeCDF p`.
- `map_edgeConnectionTime_edgeClockLaw`: **the law of `T_p` is `randomGraphConnectionLaw p`**.
- `map_edgeConnectionTime_edgeClockLaw_two`: with two fibers `T_p` is exponential with rate
  `p₀ p₁`, as a law.

## Scope

Every `p_i > 0`, so that every clock is a probability law; the identification with
`randomGraphConnectionLaw` carries that definition's premise `∑ p_i ≤ 1`.

## Empirical status

None.  Every declaration here is a product of exponential laws on a finite set of edges, a
measurable function of the clocks, or its distribution function.  The masses `p` are parameters,
not estimates from any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent MeasureTheory ProbabilityTheory

open scoped Classical

noncomputable section

/-! ### Clocks and the connection time -/

/-- **The independent exponential edge clocks**: the edge `{i, j}` rings at an exponential time
of rate `p_i p_j`, independently of the other edges.

Empirical status: NOT AN EMPIRICAL CLAIM.  A product of exponential laws. -/
def edgeClockLaw {w : ℕ} (p : Fin w → ℝ) : Measure (FiberPair w → ℝ) :=
  Measure.pi fun e ↦ expMeasure (pairRate p e)

/-- **The edges whose clocks have rung by time `u`.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A comparison of the clocks with a time. -/
def rungEdges {w : ℕ} (ω : FiberPair w → ℝ) (u : ℝ) : FiberPair w → Bool :=
  fun e ↦ decide (ω e ≤ u)

/-- **The latest clock of a configuration**, and zero for the empty configuration.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite maximum. -/
def latestClock {w : ℕ} (ω : FiberPair w → ℝ) (G : FiberPair w → Bool) : NNReal :=
  (Finset.univ.filter fun e ↦ G e = true).sup fun e ↦ (ω e).toNNReal

/-- The complete graph connects the fibers. -/
theorem componentPartition_all_true (w : ℕ) :
    componentPartition (fun _ : FiberPair w ↦ true) = ⊤ := by
  refine top_unique ?_
  intro i j _
  rcases lt_trichotomy i j with h | rfl | h
  · exact Relation.EqvGen.rel _ _ ⟨⟨(i, j), h⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ ⟨⟨(j, i), h⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- **The connection time `T_p`**: the least, over the configurations connecting the fibers, of
the time at which the whole configuration has rung.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite minimum of finite maxima of the clocks. -/
def edgeConnectionTime {w : ℕ} (ω : FiberPair w → ℝ) : ℝ :=
  ((Finset.univ.filter fun G : FiberPair w → Bool ↦ componentPartition G = ⊤).inf'
    ⟨fun _ ↦ true, Finset.mem_filter.mpr ⟨Finset.mem_univ _, componentPartition_all_true w⟩⟩
    (latestClock ω) : NNReal)

theorem edgeConnectionTime_nonneg {w : ℕ} (ω : FiberPair w → ℝ) : 0 ≤ edgeConnectionTime ω :=
  NNReal.coe_nonneg _

/-- **`T_p ≤ u` exactly when the edges rung by `u` connect the fibers**, at nonnegative times. -/
theorem edgeConnectionTime_le_iff {w : ℕ} (ω : FiberPair w → ℝ) (u : ℝ) :
    edgeConnectionTime ω ≤ u ↔ 0 ≤ u ∧ componentPartition (rungEdges ω u) = ⊤ := by
  by_cases hu : 0 ≤ u
  · have hcoe : (u.toNNReal : ℝ) = u := Real.coe_toNNReal u hu
    have hlatest : ∀ G, latestClock ω G ≤ u.toNNReal ↔ ∀ e, G e = true → ω e ≤ u := by
      intro G
      rw [latestClock, Finset.sup_le_iff]
      refine ⟨fun h e he ↦ ?_, fun h e he ↦ ?_⟩
      · have h' := h e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
        rwa [Real.toNNReal_le_iff_le_coe, hcoe] at h'
      · rw [Real.toNNReal_le_iff_le_coe, hcoe]
        exact h e (Finset.mem_filter.mp he).2
    have hkey : edgeConnectionTime ω ≤ u
        ↔ (Finset.univ.filter fun G : FiberPair w → Bool ↦ componentPartition G = ⊤).inf'
          ⟨fun _ ↦ true, Finset.mem_filter.mpr ⟨Finset.mem_univ _, componentPartition_all_true w⟩⟩
          (latestClock ω) ≤ u.toNNReal := by
      rw [edgeConnectionTime, ← NNReal.coe_le_coe, hcoe]
    rw [hkey, Finset.inf'_le_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlatest]
    constructor
    · rintro ⟨G, hG, hle⟩
      refine ⟨hu, top_unique ?_⟩
      rw [← hG]
      exact componentPartition_mono fun e he ↦ decide_eq_true (hle e he)
    · rintro ⟨-, h⟩
      exact ⟨rungEdges ω u, h, fun e he ↦ of_decide_eq_true he⟩
  · exact ⟨fun h ↦ absurd ((edgeConnectionTime_nonneg ω).trans h) hu, fun h ↦ absurd h.1 hu⟩

/-! ### Measurability -/

/-- The clocks that produce a given configuration at time `u` form a box. -/
theorem preimage_rungEdges_eq_pi {w : ℕ} (u : ℝ) (G : FiberPair w → Bool) :
    (fun ω : FiberPair w → ℝ ↦ rungEdges ω u) ⁻¹' {G}
      = Set.pi Set.univ fun e ↦ if G e then Set.Iic u else Set.Ioi u := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro rfl e
    by_cases h : ω e ≤ u
    · rw [if_pos (show rungEdges ω u e = true from decide_eq_true h)]
      exact Set.mem_Iic.mpr h
    · rw [if_neg (show ¬ rungEdges ω u e = true from fun h' ↦ h (of_decide_eq_true h'))]
      exact Set.mem_Ioi.mpr (not_le.mp h)
  · intro h
    funext e
    have he := h e
    by_cases hG : G e = true
    · rw [if_pos hG] at he
      rw [hG]
      exact decide_eq_true (Set.mem_Iic.mp he)
    · rw [if_neg hG] at he
      rw [Bool.not_eq_true] at hG
      rw [hG]
      exact decide_eq_false (not_le.mpr (Set.mem_Ioi.mp he))

theorem measurableSet_ite_Iic_Ioi (b : Bool) (u : ℝ) :
    MeasurableSet (if b then Set.Iic u else Set.Ioi u) := by
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ioi

theorem measurableSet_preimage_rungEdges {w : ℕ} (u : ℝ) (G : FiberPair w → Bool) :
    MeasurableSet ((fun ω : FiberPair w → ℝ ↦ rungEdges ω u) ⁻¹' {G}) := by
  rw [preimage_rungEdges_eq_pi]
  exact MeasurableSet.univ_pi fun e ↦ measurableSet_ite_Iic_Ioi (G e) u

/-- The event `T_p ≤ u` is the event that the configuration at `u` is connected. -/
theorem preimage_Iic_edgeConnectionTime {w : ℕ} (u : ℝ) :
    edgeConnectionTime ⁻¹' Set.Iic u
      = if 0 ≤ u then (fun ω : FiberPair w → ℝ ↦ rungEdges ω u) ⁻¹'
          ↑(Finset.univ.filter fun G : FiberPair w → Bool ↦ componentPartition G = ⊤)
        else ∅ := by
  ext ω
  split_ifs with hu
  · simp only [Set.mem_preimage, Set.mem_Iic, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [edgeConnectionTime_le_iff]
    exact and_iff_right hu
  · simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    rw [edgeConnectionTime_le_iff]
    exact fun h ↦ hu h.1

/-- **`T_p` is a random variable.** -/
theorem measurable_edgeConnectionTime (w : ℕ) :
    Measurable (edgeConnectionTime : (FiberPair w → ℝ) → ℝ) := by
  refine measurable_of_Iic fun u ↦ ?_
  rw [preimage_Iic_edgeConnectionTime]
  split_ifs
  · rw [← Finset.set_biUnion_preimage_singleton]
    exact Finset.measurableSet_biUnion _ fun G _ ↦ measurableSet_preimage_rungEdges u G
  · exact MeasurableSet.empty

/-! ### The law of `T_p` -/

/-- **An exponential clock of rate `r` has rung by time `u ≥ 0` with probability
`1 - e^{-u r}`.**

Assumes: `0 < r` and `0 ≤ u`. -/
theorem expMeasure_Iic_eq {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    expMeasure r (Set.Iic u) = ENNReal.ofReal (1 - Real.exp (-(u * r))) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hu, mul_comm r u]

/-- **An exponential clock of rate `r` has not rung by time `u ≥ 0` with probability
`e^{-u r}`.**

Assumes: `0 < r` and `0 ≤ u`. -/
theorem expMeasure_Ioi_eq {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    expMeasure r (Set.Ioi u) = ENNReal.ofReal (Real.exp (-(u * r))) := by
  haveI := isProbabilityMeasure_expMeasure hr
  have hle : Real.exp (-(u * r)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith [mul_nonneg hu hr.le])
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, expMeasure_Iic_eq hr hu,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sub_nonneg.mpr hle), sub_sub_cancel]

/-- The edge clocks form a probability law when every fiber has positive mass. -/
theorem isProbabilityMeasure_edgeClockLaw {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 < p i) :
    IsProbabilityMeasure (edgeClockLaw p) := by
  haveI : ∀ e : FiberPair w, IsProbabilityMeasure (expMeasure (pairRate p e)) := fun e ↦
    isProbabilityMeasure_expMeasure (mul_pos (hp _) (hp _))
  unfold edgeClockLaw
  infer_instance

/-- **`Pr(T_p ≤ u)` is the random-graph connection probability**: by independence, the
configuration at time `u` has probability `configMass p u G`.

Assumes: every `p_i > 0`, and `0 ≤ u`. -/
theorem edgeClockLaw_preimage_Iic {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 < p i) {u : ℝ}
    (hu : 0 ≤ u) :
    edgeClockLaw p (edgeConnectionTime ⁻¹' Set.Iic u)
      = ENNReal.ofReal (connectionProbability p u) := by
  have hr : ∀ e : FiberPair w, 0 < pairRate p e := fun e ↦ mul_pos (hp _) (hp _)
  haveI : ∀ e : FiberPair w, IsProbabilityMeasure (expMeasure (pairRate p e)) := fun e ↦
    isProbabilityMeasure_expMeasure (hr e)
  have hfactor : ∀ (e : FiberPair w) (b : Bool),
      0 ≤ if b then 1 - Real.exp (-(u * pairRate p e)) else Real.exp (-(u * pairRate p e)) := by
    intro e b
    have hrate : 0 ≤ u * pairRate p e := mul_nonneg hu (hr e).le
    have hexp : Real.exp (-(u * pairRate p e)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    split_ifs
    · linarith
    · exact (Real.exp_pos _).le
  have hconfig : ∀ G : FiberPair w → Bool,
      edgeClockLaw p ((fun ω : FiberPair w → ℝ ↦ rungEdges ω u) ⁻¹' {G})
        = ENNReal.ofReal (configMass p u G) := by
    intro G
    simp only [preimage_rungEdges_eq_pi, edgeClockLaw, Measure.pi_pi]
    rw [configMass, ENNReal.ofReal_prod_of_nonneg fun e _ ↦ hfactor e (G e)]
    refine Finset.prod_congr rfl fun e _ ↦ ?_
    split_ifs
    · exact expMeasure_Iic_eq (hr e) hu
    · exact expMeasure_Ioi_eq (hr e) hu
  rw [preimage_Iic_edgeConnectionTime, if_pos hu,
    ← sum_measure_preimage_singleton (μ := edgeClockLaw p)
      (Finset.univ.filter fun G : FiberPair w → Bool ↦ componentPartition G = ⊤)
      (f := fun ω : FiberPair w → ℝ ↦ rungEdges ω u)
      fun G _ ↦ measurableSet_preimage_rungEdges u G,
    Finset.sum_congr rfl fun G _ ↦ hconfig G,
    ← ENNReal.ofReal_sum_of_nonneg fun G _ ↦ configMass_nonneg (fun i ↦ (hp i).le) hu G]
  congr 1
  rw [connectionProbability, Finset.sum_filter]
  exact Finset.sum_congr rfl fun G _ ↦ by split_ifs <;> simp

/-- **The distribution function of `T_p` is `connectionTimeCDF p`.**

Assumes: every `p_i > 0`. -/
theorem cdf_map_edgeConnectionTime {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 < p i) (x : ℝ) :
    cdf ((edgeClockLaw p).map edgeConnectionTime) x = connectionTimeCDF p x := by
  haveI := isProbabilityMeasure_edgeClockLaw hp
  haveI : IsProbabilityMeasure ((edgeClockLaw p).map edgeConnectionTime) :=
    Measure.isProbabilityMeasure_map (measurable_edgeConnectionTime w).aemeasurable
  rw [cdf_eq_real, measureReal_def,
    Measure.map_apply (measurable_edgeConnectionTime w) measurableSet_Iic, connectionTimeCDF]
  split_ifs with hx
  · rw [preimage_Iic_edgeConnectionTime, if_neg (not_le.mpr hx), measure_empty,
      ENNReal.toReal_zero]
  · rw [edgeClockLaw_preimage_Iic hp (not_lt.mp hx),
      ENNReal.toReal_ofReal (connectionProbability_mem_Icc (fun i ↦ (hp i).le)
        (not_lt.mp hx)).1]

/-- **The law of `T_p` is the image of the exponential edge clocks**: pushing `edgeClockLaw p`
forward along the connection time gives `randomGraphConnectionLaw p`.

Assumes: every `p_i > 0` and `∑ p_i ≤ 1`, the premises of `randomGraphConnectionLaw`. -/
theorem map_edgeConnectionTime_edgeClockLaw {w : ℕ} [NeZero w] {p : Fin w → ℝ}
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i ≤ 1) :
    (edgeClockLaw p).map edgeConnectionTime = (randomGraphConnectionLaw p hp hp1 : Measure ℝ) := by
  haveI := isProbabilityMeasure_edgeClockLaw hp
  haveI : IsProbabilityMeasure ((edgeClockLaw p).map edgeConnectionTime) :=
    Measure.isProbabilityMeasure_map (measurable_edgeConnectionTime w).aemeasurable
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun x ↦ ?_)
  rw [cdf_map_edgeConnectionTime hp x, cdf_randomGraphConnectionLaw]

/-- **Two fibers: `T_p` is exponential with rate `p₀ p₁`**, as a law: the connection time is the
clock of the single edge.

Assumes: every `p_i > 0`. -/
theorem map_edgeConnectionTime_edgeClockLaw_two {p : Fin 2 → ℝ} (hp : ∀ i, 0 < p i) :
    (edgeClockLaw p).map edgeConnectionTime = expMeasure (p 0 * p 1) := by
  have hr : 0 < p 0 * p 1 := mul_pos (hp 0) (hp 1)
  haveI := isProbabilityMeasure_edgeClockLaw hp
  haveI : IsProbabilityMeasure ((edgeClockLaw p).map edgeConnectionTime) :=
    Measure.isProbabilityMeasure_map (measurable_edgeConnectionTime 2).aemeasurable
  haveI := isProbabilityMeasure_expMeasure hr
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun x ↦ ?_)
  rw [cdf_map_edgeConnectionTime hp x, cdf_expMeasure_eq hr, connectionTimeCDF]
  by_cases hx : x < 0
  · rw [if_pos hx, if_neg (not_le.mpr hx)]
  · rw [if_neg hx, if_pos (not_lt.mp hx), connectionProbability_two, mul_comm x]

end

end Descent.Pangenome.GraphCoalescent
