/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockStochasticOrder

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# A quantile coupling for the stochastic order (C2)

`ConnectionClockStochasticOrder.survivalAt_connectionTimeLaw_bot_le` proves (C2) of the pangenome
hidden-clock note as an inequality of survival functions, `P(τ_q > c) ≤ P(T_w > c)` for every
threshold `c`. Here `τ_q` has the first-step law `ConnectionClockPathLaw.connectionTimeLaw s ⊥` and
`T_w = Σ_{r=2}^{w} Exp(d_r)` has the law `kingmanTransitLaw w` at the interface width `w`. This file
constructs a coupling that realizes the order pointwise.

## The quantile transform

For a probability law `μ` on `ℝ≥0`, `quantileTransform μ u = inf {x | u ≤ μ [0, x]}`.

* `quantileTransform_le_iff`: `Q(u) ≤ x ↔ u ≤ μ [0, x]` for `u < 1`. The one analytic input is
  the right continuity of the distribution function (`le_measure_Iic_quantileTransform`).
* `map_quantileTransform`: under Lebesgue measure on `(0, 1)` the transform has law `μ`.
* `quantileTransform_le_of_survivalAt_le`: if `P_μ(X > c) ≤ P_ν(Y > c)` for every `c`, then
  `Q_μ(u) ≤ Q_ν(u)` at every `u < 1`.
* `quantileCoupling` bundles the three statements, and `exists_quantileCoupling` states them as
  the existence of a coupling.

## (C2) as a coupling

`connectionTimeLaw_quantileCoupling`: on `(0, 1)` with Lebesgue measure, the quantile transforms of
`connectionTimeLaw s ⊥` and of `kingmanTransitLaw (Linkage.width s)` have those two laws, and the
first is at most the second at every point of `(0, 1)`
(`exists_coupling_connectionTime_le_transitTime`).

## Scope

The coupled pair lives on the unit interval. It is the coupling that every stochastic order admits,
not the note's conditional quantile coupling along the continuous-time chain, and it is built for
the first-step law of `ConnectionClockPathLaw`.

## Empirical status

None. The bodies are the quantile construction under Lebesgue measure applied to laws built from
the corpus holding and jump laws; no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent MeasureTheory Set
open scoped NNReal ENNReal

/-! ### The quantile transform -/

/-- **The quantile transform** of a law on `ℝ≥0`: `Q(u) = inf {x | u ≤ μ [0, x]}`. -/
noncomputable def quantileTransform (μ : Measure ℝ≥0) (u : ℝ) : ℝ≥0 :=
  sInf {x : ℝ≥0 | ENNReal.ofReal u ≤ μ (Iic x)}

/-- Below level one, some threshold carries mass at least `u`. -/
theorem quantileSet_nonempty (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {u : ℝ} (hu : u < 1) :
    {x : ℝ≥0 | ENNReal.ofReal u ≤ μ (Iic x)}.Nonempty := by
  have hunion : ⋃ k : ℕ, Iic (k : ℝ≥0) = univ := by
    refine eq_univ_of_forall fun y ↦ mem_iUnion.mpr ?_
    obtain ⟨k, hk⟩ := exists_nat_ge y
    exact ⟨k, hk⟩
  have hmono : Monotone fun k : ℕ ↦ Iic (k : ℝ≥0) := fun i j hij ↦
    Iic_subset_Iic.mpr (Nat.cast_le.mpr hij)
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion, measure_univ] at htend
  have hlt : ENNReal.ofReal u < 1 := ENNReal.ofReal_lt_one.mpr hu
  obtain ⟨k, hk⟩ := (htend.eventually (lt_mem_nhds hlt)).exists
  exact ⟨k, hk.le⟩

/-- **The distribution function is right-continuous at the quantile**: `u ≤ μ [0, Q(u)]`. -/
theorem le_measure_Iic_quantileTransform (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u < 1) : ENNReal.ofReal u ≤ μ (Iic (quantileTransform μ u)) := by
  have hne := quantileSet_nonempty μ hu
  have hstep : ∀ k : ℕ,
      ENNReal.ofReal u ≤ μ (Iic (quantileTransform μ u + 1 / ((k : ℝ≥0) + 1))) := by
    intro k
    have hlt : quantileTransform μ u < quantileTransform μ u + 1 / ((k : ℝ≥0) + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨a, ha, hab⟩ := exists_lt_of_csInf_lt hne hlt
    have ha' : ENNReal.ofReal u ≤ μ (Iic a) := ha
    exact ha'.trans (measure_mono (Iic_subset_Iic.mpr hab.le))
  have hinter : ⋂ k : ℕ, Iic (quantileTransform μ u + 1 / ((k : ℝ≥0) + 1))
      = Iic (quantileTransform μ u) := by
    ext y
    simp only [mem_iInter, mem_Iic]
    refine ⟨fun h ↦ ?_, fun h k ↦ h.trans le_self_add⟩
    by_contra hyQ
    push_neg at hyQ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hyQ)
    exact not_le.mpr (lt_tsub_iff_left.mp hk) (h k)
  have hanti : Antitone fun k : ℕ ↦ Iic (quantileTransform μ u + 1 / ((k : ℝ≥0) + 1)) := by
    intro i j hij
    refine Iic_subset_Iic.mpr (add_le_add_left ?_ _)
    exact one_div_le_one_div_of_le (by positivity) (add_le_add_right (Nat.cast_le.mpr hij) 1)
  have htend := tendsto_measure_iInter_atTop (μ := μ)
    (fun k ↦ measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter] at htend
  exact ge_of_tendsto' htend hstep

/-- **The Galois connection of the quantile transform**: `Q(u) ≤ x ↔ u ≤ μ [0, x]` for `u < 1`. -/
theorem quantileTransform_le_iff (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {u : ℝ} (hu : u < 1)
    (x : ℝ≥0) : quantileTransform μ u ≤ x ↔ ENNReal.ofReal u ≤ μ (Iic x) :=
  ⟨fun h ↦ (le_measure_Iic_quantileTransform μ hu).trans (measure_mono (Iic_subset_Iic.mpr h)),
    fun h ↦ csInf_le (OrderBot.bddBelow _) h⟩

/-- Below level one the quantile transform is monotone. -/
theorem monotoneOn_quantileTransform (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    MonotoneOn (quantileTransform μ) (Iio 1) := by
  intro u _ v hv huv
  refine csInf_le_csInf (OrderBot.bddBelow _) (quantileSet_nonempty μ hv) fun x hx ↦ ?_
  have hx' : ENNReal.ofReal v ≤ μ (Iic x) := hx
  exact le_trans (ENNReal.ofReal_le_ofReal huv) hx'

/-- The quantile transform is measurable for Lebesgue measure on `(0, 1)`. -/
theorem aemeasurable_quantileTransform (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    AEMeasurable (quantileTransform μ) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
    ((monotoneOn_quantileTransform μ).mono Ioo_subset_Iio_self)

/-- **The quantile transform has law `μ`** under Lebesgue measure on `(0, 1)`. -/
theorem map_quantileTransform (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (quantileTransform μ) = μ := by
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_quantileTransform μ) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo]
  have hfin : μ (Iic x) ≠ ⊤ := measure_ne_top μ _
  have hle : (μ (Iic x)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := Iic x))
  have hset : quantileTransform μ ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (μ (Iic x)).toReal := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · rintro ⟨hQ, hu0, hu1⟩
      exact ⟨⟨hu0, hu1⟩,
        (ENNReal.ofReal_le_iff_le_toReal hfin).mp ((quantileTransform_le_iff μ hu1 x).mp hQ)⟩
    · rintro ⟨⟨hu0, hu1⟩, hut⟩
      exact ⟨(quantileTransform_le_iff μ hu1 x).mpr
        ((ENNReal.ofReal_le_iff_le_toReal hfin).mpr hut), hu0, hu1⟩
  rw [hset]
  rcases hle.lt_or_eq with hlt | heq
  · have hIoc : Ioo (0 : ℝ) 1 ∩ Iic (μ (Iic x)).toReal = Ioc 0 (μ (Iic x)).toReal := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨hu0, -⟩, hut⟩
        exact ⟨hu0, hut⟩
      · rintro ⟨hu0, hut⟩
        exact ⟨⟨hu0, hut.trans_lt hlt⟩, hut⟩
    rw [hIoc, Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal hfin]
  · have hIoo : Ioo (0 : ℝ) 1 ∩ Iic (μ (Iic x)).toReal = Ioo 0 1 := by
      rw [heq]
      exact inter_eq_left.mpr (Ioo_subset_Iio_self.trans Iio_subset_Iic_self)
    have hone : μ (Iic x) = 1 := by
      rw [← ENNReal.ofReal_toReal hfin, heq, ENNReal.ofReal_one]
    rw [hIoo, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, hone]

/-! ### The stochastic order becomes a pointwise order -/

/-- If `P_μ(X > c) ≤ P_ν(Y > c)` for every `c`, the distribution functions are ordered the other
way: `ν [0, x] ≤ μ [0, x]`. -/
theorem measure_Iic_le_of_survivalAt_le {μ ν : Measure ℝ≥0} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ c : ℝ, survivalAt μ c ≤ survivalAt ν c) (x : ℝ≥0) :
    ν (Iic x) ≤ μ (Iic x) := by
  have hset : {y : ℝ≥0 | (x : ℝ) < y} = (Iic x)ᶜ := by
    ext y
    simp only [mem_setOf_eq, mem_compl_iff, mem_Iic, not_le, NNReal.coe_lt_coe]
  have hc := h x
  rw [survivalAt, survivalAt, hset, prob_compl_eq_one_sub measurableSet_Iic,
    prob_compl_eq_one_sub measurableSet_Iic] at hc
  exact (ENNReal.sub_le_sub_iff_left (prob_le_one (μ := ν) (s := Iic x))
    ENNReal.one_ne_top).mp hc

/-- **The stochastic order is the pointwise order of the quantile transforms.** -/
theorem quantileTransform_le_of_survivalAt_le {μ ν : Measure ℝ≥0} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ c : ℝ, survivalAt μ c ≤ survivalAt ν c) {u : ℝ}
    (hu : u < 1) : quantileTransform μ u ≤ quantileTransform ν u := by
  refine csInf_le_csInf (OrderBot.bddBelow _) (quantileSet_nonempty ν hu) fun x hx ↦ ?_
  have hx' : ENNReal.ofReal u ≤ ν (Iic x) := hx
  exact le_trans hx' (measure_Iic_le_of_survivalAt_le h x)

/-- **The quantile coupling.** Two laws on `ℝ≥0` ordered by their survival functions are the laws,
under Lebesgue measure on `(0, 1)`, of their quantile transforms, which are ordered at every point
of `(0, 1)`. -/
theorem quantileCoupling {μ ν : Measure ℝ≥0} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ c : ℝ, survivalAt μ c ≤ survivalAt ν c) :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (quantileTransform μ) = μ
      ∧ (volume.restrict (Ioo (0 : ℝ) 1)).map (quantileTransform ν) = ν
      ∧ ∀ u ∈ Ioo (0 : ℝ) 1, quantileTransform μ u ≤ quantileTransform ν u :=
  ⟨map_quantileTransform μ, map_quantileTransform ν,
    fun _ hu ↦ quantileTransform_le_of_survivalAt_le h hu.2⟩

/-- **A coupling that realizes the stochastic order pointwise exists.** -/
theorem exists_quantileCoupling {μ ν : Measure ℝ≥0} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ c : ℝ, survivalAt μ c ≤ survivalAt ν c) :
    ∃ X Y : ℝ → ℝ≥0, AEMeasurable X (volume.restrict (Ioo (0 : ℝ) 1))
      ∧ AEMeasurable Y (volume.restrict (Ioo (0 : ℝ) 1))
      ∧ (volume.restrict (Ioo (0 : ℝ) 1)).map X = μ
      ∧ (volume.restrict (Ioo (0 : ℝ) 1)).map Y = ν
      ∧ ∀ u ∈ Ioo (0 : ℝ) 1, X u ≤ Y u :=
  ⟨quantileTransform μ, quantileTransform ν, aemeasurable_quantileTransform μ,
    aemeasurable_quantileTransform ν, quantileCoupling h⟩

/-! ### (C2) as a coupling -/

/-- **(C2) as a coupling.** On `(0, 1)` with Lebesgue measure, the quantile transforms of the
connection-time law from `⊥` and of K-G's transit time `T_w = Σ_{r=2}^{w} Exp(d_r)` at the interface
width have those two laws, and the connection time is at most the transit time at every point. -/
theorem connectionTimeLaw_quantileCoupling {n : ℕ} (s : Fin n → Fin n) :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (quantileTransform (connectionTimeLaw s ⊥))
        = connectionTimeLaw s ⊥
      ∧ (volume.restrict (Ioo (0 : ℝ) 1)).map
          (quantileTransform (kingmanTransitLaw (Linkage.width s)))
        = kingmanTransitLaw (Linkage.width s)
      ∧ ∀ u ∈ Ioo (0 : ℝ) 1, quantileTransform (connectionTimeLaw s ⊥) u
          ≤ quantileTransform (kingmanTransitLaw (Linkage.width s)) u := by
  haveI := connectionTimeLaw_isProbabilityMeasure s (⊥ : ER n)
  haveI := kingmanTransitLaw_isProbabilityMeasure (Linkage.width s)
  exact quantileCoupling (survivalAt_connectionTimeLaw_bot_le s)

/-- **The reported connection time and K-G's transit time can be coupled so that
`τ_q ≤ T_w` at every point.** -/
theorem exists_coupling_connectionTime_le_transitTime {n : ℕ} (s : Fin n → Fin n) :
    ∃ X Y : ℝ → ℝ≥0, (volume.restrict (Ioo (0 : ℝ) 1)).map X = connectionTimeLaw s ⊥
      ∧ (volume.restrict (Ioo (0 : ℝ) 1)).map Y = kingmanTransitLaw (Linkage.width s)
      ∧ ∀ u ∈ Ioo (0 : ℝ) 1, X u ≤ Y u :=
  ⟨_, _, connectionTimeLaw_quantileCoupling s⟩

end Descent.Pangenome.GraphCoalescent
