/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityIdentification
import Descent.Portability.PortabilityMinimaxLowerBound
import Descent.Portability.PortabilityTwoHistoryInstance

assert_below Descent.Decision Descent.Program

/-!
# The minimax rate of portability estimation: `count^(-1/2)` with the coupling, a floor without

`PortabilityIdentification` estimates a target expectation in NOTE1's chronology model from
`count` replicas of the frozen discovery law `chronologyLaw p 1`, with the coupling `C` supplied.
Its plug-in estimator misses a metric bounded by `B` by at most `2B √(3/count)` in expectation.
This module proves that the order `count^(-1/2)` cannot be improved. It then sets the rate beside
the floors that hold when the coupling is not supplied. Below, `metric(1,1)` abbreviates
`metric (true, true)`, and so on for the other cells.

## Statement

**Which parameter the functional moves with.** The target squared correlation, AUC, slope and
portability ratio are functions of `C` alone (`PortabilityIdentification.targetLaw_metrics`). With
`C` supplied their minimax risk is zero at every `count`, so they have no rate to find. The source
replicas carry only the donor fraction `p`, and the rate belongs to the metrics that move with
`p`. At the symmetric pair `p = 1/2 ∓ h` with one coupling, the target expectations of a metric
differ by exactly `2h (metric(1,1) - metric(0,0))`, whatever `C` is
(`expectation_chronologyLaw_symmetricPair_sub`).

**The source laws tensorize.** The frozen discovery laws at `1/2 ∓ h` put masses `1/2 ± h` on
the two concordant cells and nothing on the discordant cells. Their squared Hellinger affinity is
`1 - 4h²` (`hellingerAffinity_sq_symmetricPair`). The affinity of `count` replicas is its
`count`-th power (`PortabilityMinimaxLowerBound.hellingerAffinity_cohortLaw`), and Bernoulli's
inequality keeps `(1 - 4h²)^count ≥ 1 - 4 count h²`, which is `3/4` at `h = 1/(4√count)`. The
total-variation form of Le Cam's bound sees only `count` times the one-record distance `2h`. That
forces `h` of order `1/count` and gives only a `count^(-1)` floor.

**Lower bound.** For every estimator from `count` replicas, one of the donor fractions `1/2 ∓ h`
forces an expected absolute error of at least `(h/2) |metric(1,1) - metric(0,0)| (1 - 4h²)^count`
(`le_max_chronologyRisk_symmetricPair`). At `h = 1/(4√count)`, for every supplied coupling, some
donor fraction forces at least `3 |metric(1,1) - metric(0,0)| / (32 √count)`
(`exists_le_chronologyRisk`). The plug-in estimator has risk at most `2B √(3/count)` at every
donor fraction (`chronologyRisk_plugIn_le`).

**Without the coupling.** The source law does not depend on `C`. For every `count` and every
estimator, one of two couplings at one donor fraction forces half the separation of the target
expectations (`half_separation_le_max_chronologyRisk`). That separation is `p(1 - p)|C₁ - C₀|`
times the concordance contrast `metric(0,0) + metric(1,1) - metric(0,1) - metric(1,0)`
(`expectation_chronologyLaw_coupling_sub`).

**The dichotomy** (`minimaxRate_dichotomy`). Take the target frequency of the doubly donor cell,
the metric `singletonMetric (true, true)`. It is bounded by one and both of its contrasts are one.
- With `C` supplied, the plug-in risk is at most `2 √(3/count)` at every donor fraction, and every
  estimator has risk at least `3 / (32 √count)` at some donor fraction. The minimax rate is
  `count^(-1/2)`.
- An estimator that does not read `C` has risk at least `1/8` at some chronology.
- On the NOTE2 section 9 experiment the two histories share one source-panel law. There every
  estimator of the expected target squared correlation given definedness has worst risk above
  `0.00725` (`PortabilityTwoHistoryInstance.minimax_floor_r2`).

## Significance

This makes the sample complexity of portability estimation exact in the chronology model. With
the coupling supplied, a bounded target expectation is estimated at the rate of a Bernoulli mean.
Error `ε` needs a number of replicas of order `1/ε²`, and that many suffice, up to the factor
`64√3/3` between the two constants. Without the coupling, no number of replicas brings the error
below a fixed floor. Supplying the one number `C = L_ν(1)` of NOTE1 (29) is the difference between
no rate at all and exactly `count^(-1/2)`.

## Scope

Estimators are deterministic functions of the replicas, as in `PortabilityMinimaxLowerBound`. The
lower bound is a two-point bound at `p = 1/2` for one metric at a time. Its contrast
`metric(1,1) - metric(0,0)` is the derivative of the target expectation in `p` at `p = 1/2`.
Metrics whose contrast vanishes there, such as the concordance indicator, need an asymmetric pair,
which is not formalized. The constants `2√3` and `3/32` are not optimized, and every risk is an
expectation, not a tail probability.

## Empirical status

None. The theorems are finite-sum inequalities about stated laws and the constructed replica law,
so no measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMinimaxRate

open Descent.Portability.ChronologyReportLaw (chronologyMass chronologyLaw chronologyLaw_mass
  chronologyMass_false_false chronologyMass_false_true chronologyMass_true_false
  chronologyMass_true_true)
open Descent.Portability.EmpiricalLawLipschitzBound (replicaLaw empiricalMass)
open Descent.Portability.FourCellCohortLaw (cohortLaw)
open Descent.Portability.PortabilityIdentification (transportExpectation)
open Descent.Portability.PortabilityMinimaxLowerBound (hellingerAffinity)

noncomputable section

section Risk

/-- The risk of an estimator of the target expectation of a metric at coupling `C`, from `count`
replicas of the frozen discovery law at donor fraction `p`: its expected absolute error. -/
def chronologyRisk (count : ℕ) (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (metric : Bool × Bool → ℝ) (estimator : (Fin count → Bool × Bool) → ℝ) : ℝ :=
  (replicaLaw count (chronologyLaw p 1 hp0 hp1 zero_le_one le_rfl)).expectation
    fun draw ↦ |estimator draw - (chronologyLaw p C hp0 hp1 hC0 hC1).expectation metric|

/-- A block of replicas is the cohort law of `PortabilityMinimaxLowerBound`: both put the product
of the one-record masses on every sample. -/
theorem replicaLaw_eq_cohortLaw (count : ℕ) (q : FiniteReportLaw (Bool × Bool)) :
    replicaLaw count q = cohortLaw q count :=
  FiniteReportLaw.ext fun _ ↦ rfl

/-- **The upper half of the rate.** The plug-in estimator of `PortabilityIdentification` keeps
the supplied coupling and transports the empirical law of the replicas. Its risk is at most
`2 bound √(3/count)` at every donor fraction. Assumes: `0 < count`, `0 ≤ p ≤ 1`, `0 ≤ C ≤ 1` and a
metric bounded by `bound`. -/
theorem chronologyRisk_plugIn_le (count : ℕ) (hcount : 0 < count) (p C : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) {metric : Bool × Bool → ℝ} {bound : ℝ}
    (hmetric : ∀ cell, |metric cell| ≤ bound) :
    chronologyRisk count p C hp0 hp1 hC0 hC1 metric
        (fun draw ↦ transportExpectation (empiricalMass draw) C metric) ≤
      2 * bound * Real.sqrt (3 / count) :=
  PortabilityIdentification.expectation_abs_plugIn_chronologyLaw_sub_le count hcount p C hp0 hp1
    hC0 hC1 hmetric

end Risk

section Contrasts

/-- **The target moves with the donor fraction.** At donor fractions `1/2 - h` and `1/2 + h` with
one coupling `C`, the target expectations of a metric differ by `2h (metric(1,1) - metric(0,0))`,
whatever `C` is. Assumes: `0 ≤ h ≤ 1/2` and `0 ≤ C ≤ 1`. -/
theorem expectation_chronologyLaw_symmetricPair_sub (h C : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (metric : Bool × Bool → ℝ) :
    (chronologyLaw (1 / 2 + h) C (by linarith) (by linarith) hC0 hC1).expectation metric -
        (chronologyLaw (1 / 2 - h) C (by linarith) (by linarith) hC0 hC1).expectation metric =
      2 * h * (metric (true, true) - metric (false, false)) := by
  simp only [ChronologyReportLaw.expectation_cells, chronologyLaw_mass, chronologyMass_false_false,
    chronologyMass_false_true, chronologyMass_true_false, chronologyMass_true_true]
  ring

/-- **The target moves with the coupling.** At one donor fraction, the target expectations at
couplings `C₀` and `C₁` differ by `p(1 - p)(C₁ - C₀)` times the concordance contrast
`metric(0,0) + metric(1,1) - metric(0,1) - metric(1,0)`. Assumes: `0 ≤ p ≤ 1` and both couplings
in `[0, 1]`. -/
theorem expectation_chronologyLaw_coupling_sub (p C₀ C₁ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC₀0 : 0 ≤ C₀) (hC₀1 : C₀ ≤ 1) (hC₁0 : 0 ≤ C₁) (hC₁1 : C₁ ≤ 1) (metric : Bool × Bool → ℝ) :
    (chronologyLaw p C₁ hp0 hp1 hC₁0 hC₁1).expectation metric -
        (chronologyLaw p C₀ hp0 hp1 hC₀0 hC₀1).expectation metric =
      p * (1 - p) * (C₁ - C₀) *
        (metric (false, false) + metric (true, true) - metric (false, true) -
          metric (true, false)) := by
  rw [FiniteReportLaw.expectation_sub]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, chronologyLaw_mass,
    chronologyMass_false_false, chronologyMass_false_true, chronologyMass_true_false,
    chronologyMass_true_true]
  ring

end Contrasts

section SymmetricPair

/-- **The source laws barely move.** The frozen discovery laws at donor fractions `1/2 - h` and
`1/2 + h` put masses `1/2 ∓ h` and `1/2 ± h` on the two concordant cells and nothing on the
discordant cells, so their squared Hellinger affinity is `1 - 4h²`. Assumes: `0 ≤ h ≤ 1/2`. -/
theorem hellingerAffinity_sq_symmetricPair (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) :
    hellingerAffinity (chronologyLaw (1 / 2 - h) 1 (by linarith) (by linarith) zero_le_one le_rfl)
        (chronologyLaw (1 / 2 + h) 1 (by linarith) (by linarith) zero_le_one le_rfl) ^ 2 =
      1 - 4 * h ^ 2 := by
  have hroot : Real.sqrt (1 / 4 - h ^ 2) ^ 2 = 1 / 4 - h ^ 2 :=
    Real.sq_sqrt (by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh1)])
  have hff : chronologyMass (1 / 2 - h) 1 (false, false) *
      chronologyMass (1 / 2 + h) 1 (false, false) = 1 / 4 - h ^ 2 := by
    simp only [chronologyMass_false_false]
    ring
  have hft : chronologyMass (1 / 2 - h) 1 (false, true) *
      chronologyMass (1 / 2 + h) 1 (false, true) = 0 := by
    simp only [chronologyMass_false_true]
    ring
  have htf : chronologyMass (1 / 2 - h) 1 (true, false) *
      chronologyMass (1 / 2 + h) 1 (true, false) = 0 := by
    simp only [chronologyMass_true_false]
    ring
  have htt : chronologyMass (1 / 2 - h) 1 (true, true) *
      chronologyMass (1 / 2 + h) 1 (true, true) = 1 / 4 - h ^ 2 := by
    simp only [chronologyMass_true_true]
    ring
  simp only [hellingerAffinity, Fintype.sum_prod_type, Fintype.sum_bool, chronologyLaw_mass]
  rw [hff, hft, htf, htt, Real.sqrt_zero]
  linear_combination 4 * hroot

/-- **Le Cam at the symmetric pair.** For every estimator that reads `count` source replicas, one
of the donor fractions `1/2 ∓ h` forces an expected absolute error of at least
`(h/2) |metric(1,1) - metric(0,0)| (1 - 4h²)^count` against the target expectation at coupling
`C`. Assumes: `0 ≤ h ≤ 1/2` and `0 ≤ C ≤ 1`. -/
theorem le_max_chronologyRisk_symmetricPair (count : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (metric : Bool × Bool → ℝ)
    (estimator : (Fin count → Bool × Bool) → ℝ) :
    h / 2 * |metric (true, true) - metric (false, false)| * (1 - 4 * h ^ 2) ^ count ≤
      max (chronologyRisk count (1 / 2 - h) C (by linarith) (by linarith) hC0 hC1 metric
          estimator)
        (chronologyRisk count (1 / 2 + h) C (by linarith) (by linarith) hC0 hC1 metric
          estimator) := by
  have hsep :
      |(chronologyLaw (1 / 2 - h) C (by linarith) (by linarith) hC0 hC1).expectation metric -
        (chronologyLaw (1 / 2 + h) C (by linarith) (by linarith) hC0 hC1).expectation metric| =
      2 * h * |metric (true, true) - metric (false, false)| := by
    rw [abs_sub_comm, expectation_chronologyLaw_symmetricPair_sub h C hh0 hh1 hC0 hC1 metric,
      abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * h)]
  have hbound := PortabilityMinimaxLowerBound.lowerBound_cohortLaw_hellingerAffinity
    (chronologyLaw (1 / 2 - h) 1 (by linarith) (by linarith) zero_le_one le_rfl)
    (chronologyLaw (1 / 2 + h) 1 (by linarith) (by linarith) zero_le_one le_rfl) count
    ((chronologyLaw (1 / 2 - h) C (by linarith) (by linarith) hC0 hC1).expectation metric)
    ((chronologyLaw (1 / 2 + h) C (by linarith) (by linarith) hC0 hC1).expectation metric)
    estimator
  rw [pow_mul, hellingerAffinity_sq_symmetricPair h hh0 hh1, hsep] at hbound
  simp only [chronologyRisk, replicaLaw_eq_cohortLaw]
  refine le_trans (le_of_eq ?_) hbound
  ring

/-- **The lower half of the rate.** For every supplied coupling and every estimator of the target
expectation of a metric from `count ≥ 1` source replicas, some donor fraction forces an expected
absolute error of at least `3 |metric(1,1) - metric(0,0)| / (32 √count)`. The donor fraction is
one of `1/2 ∓ 1/(4 √count)`. Assumes: `0 < count` and `0 ≤ C ≤ 1`. -/
theorem exists_le_chronologyRisk (count : ℕ) (hcount : 0 < count) (C : ℝ) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (metric : Bool × Bool → ℝ) (estimator : (Fin count → Bool × Bool) → ℝ) :
    ∃ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
      3 * |metric (true, true) - metric (false, false)| / (32 * Real.sqrt count) ≤
        chronologyRisk count p C hp0 hp1 hC0 hC1 metric estimator := by
  have hroot1 : 1 ≤ Real.sqrt count := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hcount)
  have hrootsq : Real.sqrt count ^ 2 = count := Real.sq_sqrt (Nat.cast_nonneg count)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / (4 * Real.sqrt count) := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by
    rw [hh]
    positivity
  have hprod : h * (4 * Real.sqrt count) = 1 := by
    rw [hh]
    exact one_div_mul_cancel (by linarith : (0 : ℝ) < 4 * Real.sqrt count).ne'
  have hh1 : h ≤ 1 / 2 := by
    linarith [mul_le_mul_of_nonneg_left hroot1 hh0]
  have hpow : 3 / 4 ≤ (1 - 4 * h ^ 2) ^ count := by
    have hbern := one_add_mul_le_pow
      (by linarith [mul_le_mul_of_nonneg_left hh1 hh0] : (-2 : ℝ) ≤ -(4 * h ^ 2)) count
    have hscale : (count : ℝ) * (4 * h ^ 2) = 1 / 4 := by
      rw [← hrootsq]
      linear_combination (h * (4 * Real.sqrt count) + 1) / 4 * hprod
    rw [← sub_eq_add_neg] at hbern
    linarith
  have hfloor : 3 * |metric (true, true) - metric (false, false)| / (32 * Real.sqrt count) ≤
      h / 2 * |metric (true, true) - metric (false, false)| * (1 - 4 * h ^ 2) ^ count := by
    have hscale : 3 * |metric (true, true) - metric (false, false)| / (32 * Real.sqrt count) =
        h / 2 * |metric (true, true) - metric (false, false)| * (3 / 4) := by
      rw [hh]
      ring
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (by linarith) (abs_nonneg _))
  have hwide := hfloor.trans
    (le_max_chronologyRisk_symmetricPair count h hh0 hh1 C hC0 hC1 metric estimator)
  rcases le_max_iff.mp hwide with hlow | hhigh
  · exact ⟨1 / 2 - h, by linarith, by linarith, hlow⟩
  · exact ⟨1 / 2 + h, by linarith, by linarith, hhigh⟩

end SymmetricPair

section NoCoupling

/-- **Without the coupling there is no rate.** The source law does not depend on the coupling. So
for every number of replicas and every estimator, one of two couplings at one donor fraction
forces an expected absolute error of at least half the separation of the two target
expectations. Assumes: `0 ≤ p ≤ 1` and both couplings in `[0, 1]`. -/
theorem half_separation_le_max_chronologyRisk (count : ℕ) (p C₀ C₁ : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hC₀0 : 0 ≤ C₀) (hC₀1 : C₀ ≤ 1) (hC₁0 : 0 ≤ C₁) (hC₁1 : C₁ ≤ 1)
    (metric : Bool × Bool → ℝ) (estimator : (Fin count → Bool × Bool) → ℝ) :
    |(chronologyLaw p C₀ hp0 hp1 hC₀0 hC₀1).expectation metric -
        (chronologyLaw p C₁ hp0 hp1 hC₁0 hC₁1).expectation metric| / 2 ≤
      max (chronologyRisk count p C₀ hp0 hp1 hC₀0 hC₀1 metric estimator)
        (chronologyRisk count p C₁ hp0 hp1 hC₁0 hC₁1 metric estimator) := by
  simp only [chronologyRisk, replicaLaw_eq_cohortLaw]
  exact PortabilityMinimaxLowerBound.lowerBound_cohortLaw_of_eq _ count _ _ estimator

end NoCoupling

section Dichotomy

/-- **The minimax dichotomy of portability estimation.** Estimate the target frequency of the
doubly donor cell, the metric `singletonMetric (true, true)`, from `count` replicas of the frozen
discovery law.
- With the coupling supplied, the plug-in estimator has risk at most `2 √(3/count)` at every donor
  fraction, and every estimator has risk at least `3 / (32 √count)` at some donor fraction. The
  minimax rate is `count^(-1/2)`.
- An estimator that does not read the coupling has risk at least `1/8` at some chronology.
- On the NOTE2 section 9 experiment, where the two histories share one source-panel law, every
  estimator of the expected target squared correlation given definedness has worst risk above
  `0.00725`.
Assumes: `0 < count`. -/
theorem minimaxRate_dichotomy (count : ℕ) (hcount : 0 < count) :
    (∀ (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1),
        chronologyRisk count p C hp0 hp1 hC0 hC1 (FiniteReportLaw.singletonMetric (true, true))
            (fun draw ↦ transportExpectation (empiricalMass draw) C
              (FiniteReportLaw.singletonMetric (true, true))) ≤
          2 * Real.sqrt (3 / count)) ∧
      (∀ (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (estimator : (Fin count → Bool × Bool) → ℝ),
        ∃ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
          3 / (32 * Real.sqrt count) ≤ chronologyRisk count p C hp0 hp1 hC0 hC1
            (FiniteReportLaw.singletonMetric (true, true)) estimator) ∧
      (∀ estimator : (Fin count → Bool × Bool) → ℝ,
        ∃ (p C : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1),
          1 / 8 ≤ chronologyRisk count p C hp0 hp1 hC0 hC1
            (FiniteReportLaw.singletonMetric (true, true)) estimator) ∧
      ∀ estimator : (Fin count → ReferenceExperimentLaw.SourceStudy) → ℝ,
        (7250008 / 10 ^ 9 : ℝ) <
          PortabilityTwoHistoryInstance.worstRisk ReferenceExperimentLaw.studyLaw Prod.fst
            (fun late ↦ (PortabilityTwoHistoryInstance.givenDefined late
              ReferenceExperimentRegion.r2Weighted ReferenceExperimentRegion.r2Defined : ℝ))
            count estimator := by
  have hvalue : |FiniteReportLaw.singletonMetric (true, true) (true, true) -
      FiniteReportLaw.singletonMetric (true, true) (false, false)| = 1 := by
    simp [FiniteReportLaw.singletonMetric]
  have hhalf0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  refine ⟨fun p C hp0 hp1 hC0 hC1 ↦ ?_, fun C hC0 hC1 estimator ↦ ?_, fun estimator ↦ ?_,
    fun estimator ↦ PortabilityTwoHistoryInstance.minimax_floor_r2 count estimator⟩
  · have hbound : ∀ cell, |FiniteReportLaw.singletonMetric (true, true) cell| ≤ 1 := by
      intro cell
      obtain ⟨hlow, hhigh⟩ := FiniteReportLaw.singletonMetric_bounded (true, true) cell
      exact abs_le.mpr ⟨by linarith, hhigh⟩
    have hplug := chronologyRisk_plugIn_le count hcount p C hp0 hp1 hC0 hC1
      (metric := FiniteReportLaw.singletonMetric (true, true)) hbound
    rwa [mul_one] at hplug
  · obtain ⟨p, hp0, hp1, hp⟩ := exists_le_chronologyRisk count hcount C hC0 hC1
      (FiniteReportLaw.singletonMetric (true, true)) estimator
    rw [hvalue, mul_one] at hp
    exact ⟨p, hp0, hp1, hp⟩
  · have hE₀ : (chronologyLaw (1 / 2) 0 hhalf0 hhalf1 le_rfl zero_le_one).expectation
        (FiniteReportLaw.singletonMetric (true, true)) = 1 / 4 := by
      rw [FiniteReportLaw.expectation_singletonMetric, chronologyLaw_mass,
        chronologyMass_true_true]
      norm_num
    have hE₁ : (chronologyLaw (1 / 2) 1 hhalf0 hhalf1 zero_le_one le_rfl).expectation
        (FiniteReportLaw.singletonMetric (true, true)) = 1 / 2 := by
      rw [FiniteReportLaw.expectation_singletonMetric, chronologyLaw_mass,
        chronologyMass_true_true]
      norm_num
    have hfloor := half_separation_le_max_chronologyRisk count (1 / 2) 0 1 hhalf0 hhalf1 le_rfl
      zero_le_one zero_le_one le_rfl (FiniteReportLaw.singletonMetric (true, true)) estimator
    rw [hE₀, hE₁, abs_of_neg (by norm_num : (1 / 4 : ℝ) - 1 / 2 < 0)] at hfloor
    rcases le_max_iff.mp hfloor with h0 | h1
    · exact ⟨1 / 2, 0, hhalf0, hhalf1, le_rfl, zero_le_one, le_trans (by norm_num) h0⟩
    · exact ⟨1 / 2, 1, hhalf0, hhalf1, zero_le_one, le_rfl, le_trans (by norm_num) h1⟩

end Dichotomy

end

end Descent.Portability.PortabilityMinimaxRate
