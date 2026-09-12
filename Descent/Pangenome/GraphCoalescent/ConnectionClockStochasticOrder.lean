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
theorem holdMeasure_eq_expMeasure {d : ℝ} (hd : 0 < d) :
    holdMeasure d = ProbabilityTheory.expMeasure d := by
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

end

end Descent.Pangenome.GraphCoalescent
