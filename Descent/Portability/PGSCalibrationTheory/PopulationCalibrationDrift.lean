/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DriftingConditional
import Descent.Foundations.Probability
import Descent.Portability.PGSCalibrationTheory.CalibrationVsDiscrimination
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Sigmoid

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory
open PopGen.TransportedMetrics (equalVarianceGaussianAUCFromSignalVariance)

/-!
# `PGSCalibrationTheory.PopulationCalibrationDrift`

Part of the split of `Descent/Portability/PGSCalibrationTheory.lean`, which was 3,689 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

/-!
## Population-Specific Calibration Drift

When a PGS trained in one population is applied to another,
calibration drifts systematically.
-/

section PopulationCalibrationDrift

/-- Shared logistic-scale calibration profile induced by a prevalence shift.

    **This profile's `citl` is a difference of MARGINAL prevalence logits, and
    that is not the intercept correction a deployment needs.** The two coincide
    only when the score is constant, because `logit E[p]` is not `E[logit p]`.

    Empirical status: **FALSIFIED** as the deployment
    calibration-in-the-large, and exact for a constant predictor
    (`validation/empirical/simcov/battery_pgscal01.py`). Two million
    individuals per arm, a logistic risk model, and a target differing from the
    source by a baseline-risk (intercept) shift and nothing else — the one
    regime the phrase "induced by a prevalence shift" names. The oracle is the
    intercept correction the target actually needs: the `a` solving
    `Σᵢ (yᵢ - expit(ηᵢ + a)) = 0` with the source linear predictor held as an
    offset. Both prevalences are fed at their realised cohort values.

      score sd   true intercept shift   this citl   fitted correction   sems
      1.2              0.80              0.66237    0.79967±0.00204     67.2
      1.5              0.60              0.42940    0.60007±0.00181     94.4
      2.0              1.50              0.94064    1.49676±0.00149    374.0
      1.0             -0.90             -0.75407   -0.89961±0.00190     76.4

    The failure is one-directional: `|citl|` is 17% to 37% SMALLER than the
    correction required, so a deployment sized from this number under-corrects.
    The gap grows with the spread of the score and vanishes with it — the
    positive control is a zero-variance score, where the fitted correction
    returns the 0.7 intercept shift it was given at 0.26 sems and this body
    returns 0.7 as well. The identity-scale reading `π_target - π_source` is
    rejected on the same cells at up to 878 sems, so the failure is not an
    artefact of comparing across links.

    Consumers that read this `citl` as the recalibration a target population
    needs — rather than as the shift in marginal log-odds, which is what it is —
    are reading an attenuated number. -/
noncomputable def prevalenceLogisticCalibrationProfile
    (pi_source pi_target slope : ℝ) : CalibrationProfile :=
  logisticCalibrationProfile (prevalenceLogit pi_target) (prevalenceLogit pi_source) slope

@[simp] theorem prevalenceLogisticCalibrationProfile_citl
    (pi_source pi_target slope : ℝ) :
    (prevalenceLogisticCalibrationProfile pi_source pi_target slope).citl =
      prevalenceCITLShift pi_source pi_target := by
  unfold prevalenceLogisticCalibrationProfile prevalenceCITLShift
    logisticCalibrationProfile calibrationProfile prevalenceLogit
    calibrationInTheLarge Descent.Core.difference
  ring

@[simp] theorem prevalenceLogisticCalibrationProfile_slope
    (pi_source pi_target slope : ℝ) :
    (prevalenceLogisticCalibrationProfile pi_source pi_target slope).slope = slope := by
  rfl

/-- CITL shift is zero when prevalences match. -/
theorem no_citl_shift_same_prevalence (pi : ℝ) :
    prevalenceCITLShift pi pi = 0 := by
  rw [← prevalenceLogisticCalibrationProfile_citl pi pi (1 : ℝ)]
  simp [prevalenceLogisticCalibrationProfile, logisticCalibrationProfile,
    calibrationProfile, calibrationInTheLarge,
      Descent.Core.difference]

/-- CITL shift is positive when target has higher prevalence. -/
theorem citl_shift_positive_higher_prevalence
    (pi_s pi_t : ℝ) (h_s : 0 < pi_s)
    (h_higher : pi_s < pi_t)
    (h_t : pi_t < 1) :
    0 < prevalenceCITLShift pi_s pi_t := by
  have h_t_pos : 0 < pi_t := lt_trans h_s h_higher
  have h_den_s : 0 < 1 - pi_s := by linarith
  have h_den_t : 0 < 1 - pi_t := by linarith
  have h_odds_pos_s : 0 < pi_s / (1 - pi_s) :=
    div_pos h_s h_den_s
  have h_odds_lt : pi_s / (1 - pi_s) < pi_t / (1 - pi_t) := by
    rw [div_lt_div_iff₀ h_den_s h_den_t]
    nlinarith
  unfold prevalenceCITLShift prevalenceLogit
  apply sub_pos.mpr
  exact Real.log_lt_log h_odds_pos_s h_odds_lt

/-- **Environmental confounding shifts calibration.**
    If environmental risk factors change the population mean outcome by
    `env_effect` while the model's mean prediction is unchanged, then
    calibration-in-the-large shifts by exactly `env_effect`. -/
theorem env_differences_shift_calibration
    (mean_obs mean_pred env_effect : ℝ) :
    calibrationInTheLarge (mean_obs + env_effect) mean_pred =
      calibrationInTheLarge mean_obs mean_pred + env_effect := by
  unfold calibrationInTheLarge Descent.Core.difference
  ring

/-- Under a source model calibrated in the large, any nonzero environmental
    shift induces nonzero target CITL. -/
theorem env_differences_shift_calibration_nonzero_of_calibrated_source
    (mean_obs mean_pred env_effect : ℝ)
    (h_src_cal : calibrationInTheLarge mean_obs mean_pred = 0)
    (h_effect : env_effect ≠ 0) :
    calibrationInTheLarge (mean_obs + env_effect) mean_pred ≠ 0 := by
  rw [env_differences_shift_calibration]
  rw [h_src_cal]
  simpa using h_effect

/-- **Genetic risk distribution shift.**
    If the PGS mean shifts by Δμ in the target population, the CITL
    shifts correspondingly. Using calibrationInTheLarge:
    CITL_target = (mean_obs_target) - (mean_pred), where mean_pred
    was calibrated to source. The shift in mean PGS creates a CITL
    equal to the mean difference when the model was calibrated (CITL=0) in source.
    CITL_target = mean_obs_target - mean_obs_source + (mean_pgs_source - mean_pgs_target). -/
theorem genetic_distribution_shift
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ) :
    calibrationInTheLarge mean_obs_t mean_pgs_t =
      calibrationInTheLarge mean_obs_s mean_pgs_s +
        (mean_obs_t - mean_obs_s) + (mean_pgs_s - mean_pgs_t) := by
  unfold calibrationInTheLarge Descent.Core.difference
  ring

/-- If the source model is calibrated in the large, the target CITL equals the
    observed-mean shift plus the PGS-mean shift exactly. -/
theorem genetic_distribution_shift_of_calibrated_source
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ)
    (h_calibrated_source : calibrationInTheLarge mean_obs_s mean_pgs_s = 0) :
    calibrationInTheLarge mean_obs_t mean_pgs_t =
      mean_obs_t - mean_obs_s + (mean_pgs_s - mean_pgs_t) := by
  rw [genetic_distribution_shift]
  rw [h_calibrated_source]
  ring

/-- Under a calibrated source model, any nonzero net mean shift induces
    nonzero target CITL. -/
theorem genetic_distribution_shift_nonzero_of_calibrated_source
    (mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t : ℝ)
    (h_calibrated_source : calibrationInTheLarge mean_obs_s mean_pgs_s = 0)
    (h_net_shift : mean_obs_t - mean_obs_s + (mean_pgs_s - mean_pgs_t) ≠ 0) :
    calibrationInTheLarge mean_obs_t mean_pgs_t ≠ 0 := by
  rw [genetic_distribution_shift_of_calibrated_source
    mean_obs_s mean_obs_t mean_pgs_s mean_pgs_t h_calibrated_source]
  exact h_net_shift

/-!
## Why the Δ-logit intercept shift under-corrects

`prevalenceLogisticCalibrationProfile` above is FALSIFIED as the deployment intercept
correction, and the recorded failure is one-directional: the shift it prescribes moves the
marginal prevalence by LESS than it promises, by 17% to 37% on the measured cells, with the
gap growing in the spread of the score. This section derives that direction instead of citing
it. The mechanism is three short facts. A logistic intercept shift `δ` acts on every
subpopulation's risk by multiplying its odds by `exp δ` (`sigmoid_add_eq_oddsScale`). The
odds-multiplier action is strictly concave in the risk when the odds go up
(`oddsScale_strictConcaveOn`) and strictly convex when they go down
(`oddsScale_strictConvexOn`). Jensen's inequality then puts the achieved marginal prevalence
strictly on the near side of the promised one whenever two subpopulations differ in risk
(`prevalenceCITLShift_undercorrects_upward`, `_downward`) — for ANY mixture, any number of
subpopulations, any weights. The measured 17–37% is a magnitude this argument does not fix;
the direction is universal, which is what makes the recipe an under-correction rather than a
noisy one.
-/

/-- The action of an odds multiplier on a risk: `oddsScale c p` is the probability whose odds
    are `c` times the odds of `p`, i.e. `c·p/(1-p) / (1 + c·p/(1-p))` cleared of the inner
    division. A logistic intercept shift `δ` acts on risks as `oddsScale (exp δ)`
    (`sigmoid_add_eq_oddsScale`), so this is the map through which
    `prevalenceLogisticCalibrationProfile`'s `citl` reaches a deployment's predictions.

    Empirical status: NOT AN EMPIRICAL CLAIM — a reparameterisation map, not a quantity; it
    asserts nothing about any population. The empirical content of what this map does to a
    deployed correction is recorded on `prevalenceLogisticCalibrationProfile`, whose FALSIFIED
    verdict the theorems below derive. -/
noncomputable def oddsScale (c p : ℝ) : ℝ :=
  c * p / (1 + (c - 1) * p)

/-- The denominator of `oddsScale` is positive on the risk interval: `1 + (c-1)·p` is
    `(1-p) + c·p`, a positive combination whenever `0 < c` and `p ∈ [0,1]`. -/
theorem oddsScale_denom_pos (c p : ℝ) (hc : 0 < c) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 < 1 + (c - 1) * p := by
  rcases lt_or_ge p 1 with h | h
  · nlinarith [mul_nonneg hc.le h0]
  · have hp1 : p = 1 := le_antisymm h1 h
    rw [hp1]
    nlinarith

/-- `oddsScale` fixes the endpoints: an impossible event stays impossible. -/
@[simp] theorem oddsScale_zero (c : ℝ) : oddsScale c 0 = 0 := by
  unfold oddsScale
  ring

/-- `oddsScale` fixes the endpoints: a certain event stays certain (for a nonzero
    multiplier, which `exp δ` always is). -/
theorem oddsScale_one (c : ℝ) (hc : c ≠ 0) : oddsScale c 1 = 1 := by
  unfold oddsScale
  rw [mul_one, show 1 + (c - 1) * 1 = c by ring, div_self hc]

/-- A unit odds multiplier is the identity on risks. -/
@[simp] theorem oddsScale_one_left (p : ℝ) : oddsScale 1 p = p := by
  unfold oddsScale
  norm_num

/-- **Successive intercept shifts compose by multiplying their odds multipliers.** Applying
    `oddsScale c'` and then `oddsScale c` to a risk is applying `oddsScale (c * c')` once. Via
    `sigmoid_add_eq_oddsScale` this is the statement that a logistic recalibration applied on
    top of another is a single recalibration by the sum of the two intercept shifts, so the
    under-correction theorems below cannot be escaped by iterating the Δ-logit recipe: two
    passes of the recipe are one pass at a different multiplier, and
    `required_odds_multiplier_exceeds_deltaLogit` bounds every multiplier the recipe can
    name. -/
theorem oddsScale_comp (c c' p : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    oddsScale c (oddsScale c' p) = oddsScale (c * c') p := by
  have hD' : 0 < 1 + (c' - 1) * p := oddsScale_denom_pos c' p hc' h0 h1
  have hD : 0 < 1 + (c * c' - 1) * p :=
    oddsScale_denom_pos (c * c') p (mul_pos hc hc') h0 h1
  have hD'0 : (1 : ℝ) + (c' - 1) * p ≠ 0 := hD'.ne'
  have hden : 1 + (c - 1) * (c' * p / (1 + (c' - 1) * p))
      = (1 + (c * c' - 1) * p) / (1 + (c' - 1) * p) := by
    rw [eq_div_iff hD'0, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hD'0]
    ring
  unfold oddsScale
  rw [hden, div_eq_div_iff (div_pos hD hD').ne' hD.ne']
  field_simp

/-- **A logistic intercept shift acts on risks by scaling odds.** Shifting the linear
    predictor by `δ` carries the risk `sigmoid x` to `oddsScale (exp δ) (sigmoid x)`: the
    intercept correction of a logistic recalibration IS an odds multiplier, applied to every
    individual's predicted risk at once. -/
theorem sigmoid_add_eq_oddsScale (x δ : ℝ) :
    Real.sigmoid (x + δ) = oddsScale (Real.exp δ) (Real.sigmoid x) := by
  unfold oddsScale
  rw [Real.sigmoid_def, Real.sigmoid_def]
  have hx : 0 < 1 + Real.exp (-x) := by positivity
  have hxd : 0 < 1 + Real.exp (-(x + δ)) := by positivity
  have hden : 1 + (Real.exp δ - 1) * (1 + Real.exp (-x))⁻¹ =
      (Real.exp δ + Real.exp (-x)) / (1 + Real.exp (-x)) := by
    field_simp
    ring
  rw [hden]
  have hsum : 0 < Real.exp δ + Real.exp (-x) := by positivity
  have hkey : Real.exp δ * Real.exp (-(x + δ)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    ring_nf
  field_simp
  nlinarith [hkey]

/-- **The Δ-logit recipe's promise, exactly.** Scaling the odds of the source prevalence by
    the odds ratio of target to source lands exactly on the target prevalence: this is the
    sense in which `prevalenceCITLShift` is the right correction for a CONSTANT predictor,
    the regime `battery_pgscal01`'s positive control confirms at 0.26 sems. The theorems
    below show a mixture never reaches this value. -/
theorem oddsScale_citl_exact (ps pt : ℝ)
    (hs0 : 0 < ps) (hs1 : ps < 1) (ht0 : 0 < pt) (ht1 : pt < 1) :
    oddsScale (Real.exp (prevalenceCITLShift ps pt)) ps = pt := by
  have hos : 0 < ps / (1 - ps) := div_pos hs0 (by linarith)
  have hot : 0 < pt / (1 - pt) := div_pos ht0 (by linarith)
  have h1s : (1 : ℝ) - ps ≠ 0 := by linarith
  have h1t : (1 : ℝ) - pt ≠ 0 := by linarith
  have hexp : Real.exp (prevalenceCITLShift ps pt) = (pt * (1 - ps)) / (ps * (1 - pt)) := by
    unfold prevalenceCITLShift prevalenceLogit
    rw [Real.exp_sub, Real.exp_log hot, Real.exp_log hos]
    field_simp
  rw [hexp]
  unfold oddsScale
  have hden : 1 + ((pt * (1 - ps)) / (ps * (1 - pt)) - 1) * ps = (1 - ps) / (1 - pt) := by
    field_simp
    ring
  rw [hden]
  have hq : (0 : ℝ) < (1 - ps) / (1 - pt) := div_pos (by linarith) (by linarith)
  rw [div_eq_iff hq.ne']
  field_simp

/-- **Raising odds is strictly concave in the risk.** For an odds multiplier `c > 1` the map
    `p ↦ oddsScale c p` is strictly concave on `[0,1]`: it lifts middling risks
    proportionally more than it lifts a mixture's extremes. This is the entire mechanism of
    the Δ-logit under-correction; Jensen does the rest. -/
theorem oddsScale_strictConcaveOn (c : ℝ) (hc : 1 < c) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (oddsScale c) := by
  have hc0 : 0 < c := by linarith
  refine ⟨convex_Icc 0 1, ?_⟩
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ hxy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have hDx : 0 < 1 + (c - 1) * x := oddsScale_denom_pos c x hc0 hx0 hx1
  have hDy : 0 < 1 + (c - 1) * y := oddsScale_denom_pos c y hc0 hy0 hy1
  have hz0 : 0 ≤ a * x + (1 - a) * y := by nlinarith
  have hz1 : a * x + (1 - a) * y ≤ 1 := by nlinarith
  have hDz : 0 < 1 + (c - 1) * (a * x + (1 - a) * y) :=
    oddsScale_denom_pos c _ hc0 hz0 hz1
  have hsq : 0 < (x - y) ^ 2 := by
    have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  have hgap : 0 < c * (c - 1) * (a * (1 - a)) * (x - y) ^ 2 := by
    have : 0 < a * (1 - a) := mul_pos ha hb
    have : 0 < c - 1 := by linarith
    positivity
  simp only [smul_eq_mul]
  unfold oddsScale
  rw [← mul_div_assoc, ← mul_div_assoc,
    div_add_div _ _ hDx.ne' hDy.ne', div_lt_div_iff₀ (mul_pos hDx hDy) hDz]
  nlinarith [hgap, mul_pos hDx hDy, mul_pos hDy hDz, mul_pos hDx hDz]

/-- **Lowering odds is strictly convex in the risk** — the mirror of
    `oddsScale_strictConcaveOn` for `c < 1`, carrying the downward-shift case of the same
    under-correction. -/
theorem oddsScale_strictConvexOn (c : ℝ) (hc0 : 0 < c) (hc : c < 1) :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (oddsScale c) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ hxy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have hDx : 0 < 1 + (c - 1) * x := oddsScale_denom_pos c x hc0 hx0 hx1
  have hDy : 0 < 1 + (c - 1) * y := oddsScale_denom_pos c y hc0 hy0 hy1
  have hz0 : 0 ≤ a * x + (1 - a) * y := by nlinarith
  have hz1 : a * x + (1 - a) * y ≤ 1 := by nlinarith
  have hDz : 0 < 1 + (c - 1) * (a * x + (1 - a) * y) :=
    oddsScale_denom_pos c _ hc0 hz0 hz1
  have hsq : 0 < (x - y) ^ 2 := by
    have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  have hgap : 0 < c * (1 - c) * (a * (1 - a)) * (x - y) ^ 2 := by
    have : 0 < a * (1 - a) := mul_pos ha hb
    have : 0 < 1 - c := by linarith
    positivity
  simp only [smul_eq_mul]
  unfold oddsScale
  rw [← mul_div_assoc, ← mul_div_assoc,
    div_add_div _ _ hDx.ne' hDy.ne', div_lt_div_iff₀ hDz (mul_pos hDx hDy)]
  nlinarith [hgap, mul_pos hDx hDy, mul_pos hDy hDz, mul_pos hDx hDz]

/-- **The Δ-logit intercept shift under-corrects, upward case.** Take any finite mixture of
    subpopulations with weights `w` and per-subpopulation risks `p` averaging to the source
    prevalence `ps`, and any target prevalence `pt > ps`. Applying the intercept shift
    `prevalenceCITLShift ps pt` — which multiplies every subpopulation's odds by its `exp` —
    achieves a marginal prevalence STRICTLY BELOW `pt` whenever any two subpopulations differ
    in risk. The promise `oddsScale_citl_exact` is met only by a constant predictor; a score
    with any spread converts the strict concavity of `oddsScale` into a one-directional
    shortfall. This derives the direction of `battery_pgscal01`'s falsification of
    `prevalenceLogisticCalibrationProfile` for every mixture at once: the fitted correction
    can only exceed the Δ-logit `citl`. -/
theorem prevalenceCITLShift_undercorrects_upward {ι : Type*} (t : Finset ι)
    (w p : ι → ℝ) (ps pt : ℝ)
    (hw : ∀ i ∈ t, 0 < w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hp : ∀ i ∈ t, p i ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∑ i ∈ t, w i * p i = ps)
    (hne : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k)
    (hs0 : 0 < ps) (hs1 : ps < 1) (ht1 : pt < 1) (hlt : ps < pt) :
    ∑ i ∈ t, w i * oddsScale (Real.exp (prevalenceCITLShift ps pt)) (p i) < pt := by
  have ht0 : 0 < pt := lt_trans hs0 hlt
  have hc : 1 < Real.exp (prevalenceCITLShift ps pt) := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (citl_shift_positive_higher_prevalence ps pt hs0 hlt ht1)
  calc ∑ i ∈ t, w i * oddsScale (Real.exp (prevalenceCITLShift ps pt)) (p i)
      < oddsScale (Real.exp (prevalenceCITLShift ps pt)) (∑ i ∈ t, w i * p i) := by
        simpa [smul_eq_mul] using
          (oddsScale_strictConcaveOn _ hc).lt_map_sum hw hw1 hp hne
    _ = pt := by rw [hmean]; exact oddsScale_citl_exact ps pt hs0 hs1 ht0 ht1

/-- **The Δ-logit intercept shift under-corrects, downward case.** The mirror of
    `prevalenceCITLShift_undercorrects_upward`: aiming at a LOWER target prevalence, the
    recipe's downward shift leaves the achieved marginal prevalence STRICTLY ABOVE `pt` for
    any mixture whose risks differ, by the strict convexity of a shrinking odds multiplier.
    Together the two theorems say `|citl|` is an under-estimate of the needed correction in
    BOTH directions — the one-directional gap `battery_pgscal01` measured at 17–37%. -/
theorem prevalenceCITLShift_undercorrects_downward {ι : Type*} (t : Finset ι)
    (w p : ι → ℝ) (ps pt : ℝ)
    (hw : ∀ i ∈ t, 0 < w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hp : ∀ i ∈ t, p i ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∑ i ∈ t, w i * p i = ps)
    (hne : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k)
    (hs1 : ps < 1) (ht0 : 0 < pt) (hlt : pt < ps) :
    pt < ∑ i ∈ t, w i * oddsScale (Real.exp (prevalenceCITLShift ps pt)) (p i) := by
  have hs0 : 0 < ps := lt_trans ht0 hlt
  have ht1 : pt < 1 := lt_trans hlt hs1
  have hcitl : prevalenceCITLShift ps pt < 0 := by
    have := citl_shift_positive_higher_prevalence pt ps ht0 hlt hs1
    unfold prevalenceCITLShift at this ⊢
    linarith
  have hc1 : Real.exp (prevalenceCITLShift ps pt) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr hcitl
  have hc0 : 0 < Real.exp (prevalenceCITLShift ps pt) := Real.exp_pos _
  calc pt = oddsScale (Real.exp (prevalenceCITLShift ps pt)) (∑ i ∈ t, w i * p i) := by
        rw [hmean]; exact (oddsScale_citl_exact ps pt hs0 hs1 ht0 ht1).symm
    _ < ∑ i ∈ t, w i * oddsScale (Real.exp (prevalenceCITLShift ps pt)) (p i) := by
        simpa [smul_eq_mul] using
          (oddsScale_strictConvexOn _ hc0 hc1).map_sum_lt hw hw1 hp hne

/-- `oddsScale` is monotone in the multiplier on the risk interval: raising the odds ratio
    never lowers the risk. The difference is `(c' - c)·p·(1-p)` over positive denominators,
    so it is strict exactly on interior risks (`oddsScale_lt_oddsScale_left`). -/
theorem oddsScale_le_oddsScale_left (c c' p : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (hcc : c ≤ c') (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    oddsScale c p ≤ oddsScale c' p := by
  have hD : 0 < 1 + (c - 1) * p := oddsScale_denom_pos c p hc h0 h1
  have hD' : 0 < 1 + (c' - 1) * p := oddsScale_denom_pos c' p hc' h0 h1
  unfold oddsScale
  rw [div_le_div_iff₀ hD hD']
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hcc) h0) (sub_nonneg.mpr h1)]

/-- Strict version of `oddsScale_le_oddsScale_left` on interior risks. -/
theorem oddsScale_lt_oddsScale_left (c c' p : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (hcc : c < c') (h0 : 0 < p) (h1 : p < 1) :
    oddsScale c p < oddsScale c' p := by
  have hD : 0 < 1 + (c - 1) * p := oddsScale_denom_pos c p hc h0.le h1.le
  have hD' : 0 < 1 + (c' - 1) * p := oddsScale_denom_pos c' p hc' h0.le h1.le
  unfold oddsScale
  rw [div_lt_div_iff₀ hD hD']
  nlinarith [mul_pos (mul_pos (sub_pos.mpr hcc) h0) (sub_pos.mpr h1)]

/-- **The correction a deployment actually needs strictly exceeds the Δ-logit recipe.** If
    some odds multiplier `cstar` really does move the mixture's marginal prevalence from
    `ps` to `pt > ps`, then `cstar` is strictly larger than the recipe's
    `exp (prevalenceCITLShift ps pt)` whenever two subpopulations differ in risk: the recipe
    lands short (`prevalenceCITLShift_undercorrects_upward`), and `oddsScale` is monotone in
    the multiplier, so no multiplier at or below the recipe's can reach the target. This is
    the theorem form of `battery_pgscal01`'s fitted corrections exceeding `citl` on every
    cell: 0.79967 needed against 0.66237 prescribed, 1.49676 against 0.94064. -/
theorem required_odds_multiplier_exceeds_deltaLogit {ι : Type*} (t : Finset ι)
    (w p : ι → ℝ) (ps pt cstar : ℝ)
    (hw : ∀ i ∈ t, 0 < w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hp : ∀ i ∈ t, p i ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∑ i ∈ t, w i * p i = ps)
    (hne : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k)
    (hs0 : 0 < ps) (hs1 : ps < 1) (ht1 : pt < 1) (hlt : ps < pt)
    (hcstar : 0 < cstar)
    (hachieves : ∑ i ∈ t, w i * oddsScale cstar (p i) = pt) :
    Real.exp (prevalenceCITLShift ps pt) < cstar := by
  by_contra hle
  push_neg at hle
  have hshort := prevalenceCITLShift_undercorrects_upward t w p ps pt
    hw hw1 hp hmean hne hs0 hs1 ht1 hlt
  have hmono : ∑ i ∈ t, w i * oddsScale cstar (p i) ≤
      ∑ i ∈ t, w i * oddsScale (Real.exp (prevalenceCITLShift ps pt)) (p i) := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hpi := hp i hi
    exact mul_le_mul_of_nonneg_left
      (oddsScale_le_oddsScale_left cstar _ (p i) hcstar (Real.exp_pos _) hle
        hpi.1 hpi.2) (hw i hi).le
  linarith [hachieves ▸ hmono]

/-!
## The probit marginal-slope parameterisation: exact marginal calibration, identifiability

The Δ-logit correction above under-corrects because `logit E[p] ≠ E[logit p]` — the logistic
baseline parameter does not commute with mixing over the score. The probit marginal-slope
parameterisation `Pr(Y = 1 | z) = Φ(q·√(1+b²) + b·z)` is built so the corresponding gap is
zero: marginalising over a standard-normal score returns `Φ(q)` exactly
(`marginalSlope_marginal_prevalence`), so `q` is the baseline-prevalence parameter with no
Jensen correction owed at any accuracy `b`. The pair `(q, b)` is also identified by the risk
curve alone (`marginalSlope_identified`): two parameterisations agreeing at every score agree
parameter by parameter, so a baseline surface and a score-accuracy surface fitted jointly
from phenotype data cannot trade off against each other inside one ancestry's risk curve.
-/

open ProbabilityTheory in
/-- **Marginalising the probit marginal-slope model returns its baseline exactly.** With a
    standard-normal score `z`, the parameterisation `Φ(q·√(1+b²) + b·z)` has marginal
    prevalence `Φ(q)` — for every score accuracy `b`, with no correction term. This is the
    probit counterpart of the Δ-logit failure derived above: here the baseline parameter
    commutes with mixing over the score, which is exactly the property
    `prevalenceLogisticCalibrationProfile` is FALSIFIED for lacking. Instance of
    `Conditionals.gaussianAverage_probit` at `α = q·√(1+b²)`, `β = b`. -/
theorem marginalSlope_marginal_prevalence (q b : ℝ) :
    ∫ z, Foundations.Phi (q * Real.sqrt (1 + b ^ 2) + b * z)
      ∂(gaussianReal 0 1) = Foundations.Phi q := by
  rw [Conditionals.gaussianAverage_probit (q * Real.sqrt (1 + b ^ 2)) b]
  have hs : Real.sqrt (1 + b ^ 2) ≠ 0 := by positivity
  rw [mul_div_assoc, div_self hs, mul_one]

/-- **The baseline and accuracy parameters are identified by the risk curve.** Two
    marginal-slope parameterisations that agree at every score value agree parameter by
    parameter: the probit index is affine in the score, an affine map is determined by two
    evaluations, and `Φ` is strictly monotone (`Foundations.strictMono_Phi`), so nothing
    else can produce the same risk curve. Fitting a baseline surface `q(PC)` and an accuracy
    surface `b(PC)` from outcome data is therefore estimating a well-posed target: within
    any one ancestry position the two surfaces cannot compensate for each other. -/
theorem marginalSlope_identified (q b q' b' : ℝ)
    (h : ∀ z : ℝ, Foundations.Phi (q * Real.sqrt (1 + b ^ 2) + b * z)
      = Foundations.Phi (q' * Real.sqrt (1 + b' ^ 2) + b' * z)) :
    q = q' ∧ b = b' := by
  have hinj := Foundations.strictMono_Phi.injective
  have h0 : q * Real.sqrt (1 + b ^ 2) = q' * Real.sqrt (1 + b' ^ 2) := by
    have := hinj (h 0)
    simpa using this
  have h1 : q * Real.sqrt (1 + b ^ 2) + b = q' * Real.sqrt (1 + b' ^ 2) + b' := by
    have := hinj (h 1)
    simpa using this
  have hb : b = b' := by linarith
  subst hb
  refine ⟨?_, rfl⟩
  have hs : (0 : ℝ) < Real.sqrt (1 + b ^ 2) := by positivity
  exact mul_right_cancel₀ hs.ne' h0

end PopulationCalibrationDrift

end Descent.Portability
