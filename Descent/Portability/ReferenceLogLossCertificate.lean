/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.LogLossSeriesCertificate
import Descent.Portability.ReferenceExperimentLaw

assert_below Descent.Decision Descent.Program

/-!
# Rational log-loss certificates and their eighty-term width in the reference experiment

NOTE 2 section 9 reports that the expected target log loss of the reference experiment is
represented exactly by a rational linear combination of negative logarithms, and that
eighty-term rational certificates have widths below `10^-10`. This module proves both claims,
in a form that holds for every target history rather than only the two the note executes.

`expectation_neg_log_eq_fiber_sum` is the representation: for a rational report law and a
rational forecast of the realized outcome, the expected negative logarithm is the sum over the
finitely many forecast values of the rational probability of that value times its negative
logarithm. `logLossLowerCertificate` and `logLossCertificateWidth` are the two rationals a
`K`-term certificate computes: the expectation of the truncated series of NOTE 2 equation (30)
and the expectation of its tail bound. `logLossCertificate_enclosure` shows they bracket the
expected loss, by `LogLossSeriesCertificate.expectation_log_loss_enclosure`. The width is
controlled by the smallest forecast alone: the tail bound decreases in the forecast
(`logTailBound_le_of_floor`), so the width is at most `(1 - ρ)^(K+1) / ((K+1) ρ)` whenever
every forecast is at least `ρ > 0` (`logLossCertificateWidth_le_of_floor`).

The reference learner of `ReferenceExperimentLaw` fits Laplace-smoothed risks from two
training draws, so every group risk lies in `[1/4, 3/4]` (`groupRisk_mem_Icc`), and so does
the forecast it gives the realized outcome of any genotype (`realizedForecast_mem_Icc`). The
smallest forecast is therefore `1/4`, the width after `K` terms is at most
`(3/4)^(K+1) / ((K+1)/4)` (`reference_logLossCertificateWidth_le`), and at eighty terms that
bound is `3^77 / 4^80`, about `3.8 · 10^-12` and below `10^-10`
(`reference_logLoss_eighty_term_certificate`). The learner never rules out an outcome, so the
extended-valued expected loss of `LogLossSeriesCertificate.expectedLogLoss` is finite and
equals the real expectation (`reference_expectedLogLoss_eq_ofReal`).

Scope. The target histories of section 9 and their terminal laws are not formalized in the
corpus, so the claims are proved for an arbitrary rational law over any finite observation
type, projected to a study's training and validation draws, a genotype and an outcome. The
decimal endpoints the note renders need the target law itself and are not reproduced.

## Empirical status

None. The bodies here are rational arithmetic and elementary inequalities: sums of the
supplied masses times powers and quotients of the forecasts, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceLogLossCertificate

open LogLossSeriesCertificate RationalReportClosure ReferenceExperimentLaw

section Certificate

variable {Outcome : Type*} [Fintype Outcome]

/-- **NOTE 2 section 9, exact representation.** For a rational report law and a rational
forecast of the realized outcome, the expected negative logarithm is a rational linear
combination of negative logarithms: the sum over the forecast values of the rational
probability that the forecast takes that value, times the negative logarithm of the value. -/
theorem expectation_neg_log_eq_fiber_sum (law : RationalReportLaw Outcome)
    (forecast : Outcome → ℚ) :
    law.toReal.expectation (fun outcome ↦ -Real.log (forecast outcome)) =
      ∑ value ∈ Finset.univ.image forecast,
        ((∑ outcome ∈ Finset.univ.filter (fun outcome ↦ forecast outcome = value),
          law.mass outcome : ℚ) : ℝ) * -Real.log value := by
  unfold FiniteReportLaw.expectation
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun outcome _ ↦ Finset.mem_image_of_mem forecast (Finset.mem_univ outcome))]
  refine Finset.sum_congr rfl fun value _ ↦ ?_
  rw [Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun outcome houtcome ↦ ?_
  show (law.mass outcome : ℝ) * -Real.log (forecast outcome) = _
  rw [(Finset.mem_filter.mp houtcome).2]

/-- The rational lower certificate of a `K`-term log-loss enclosure: the expectation of the
truncated series of NOTE 2 equation (30) at the forecast of the realized outcome. -/
def logLossLowerCertificate (law : RationalReportLaw Outcome) (forecast : Outcome → ℚ)
    (terms : ℕ) : ℚ :=
  law.expectation fun outcome ↦
    ∑ index ∈ Finset.range terms, (1 - forecast outcome) ^ (index + 1) / ((index : ℚ) + 1)

/-- The rational width of a `K`-term log-loss enclosure: the expectation of the tail bound of
NOTE 2 equation (30) at the forecast of the realized outcome. -/
def logLossCertificateWidth (law : RationalReportLaw Outcome) (forecast : Outcome → ℚ)
    (terms : ℕ) : ℚ :=
  law.expectation fun outcome ↦
    (1 - forecast outcome) ^ (terms + 1) / (((terms : ℚ) + 1) * forecast outcome)

/-- The rational lower certificate is the real expectation of the truncated series. -/
theorem logLossLowerCertificate_cast (law : RationalReportLaw Outcome) (forecast : Outcome → ℚ)
    (terms : ℕ) :
    ((logLossLowerCertificate law forecast terms : ℚ) : ℝ) =
      law.toReal.expectation fun outcome ↦ ∑ index ∈ Finset.range terms,
        (1 - (forecast outcome : ℝ)) ^ (index + 1) / ((index : ℝ) + 1) := by
  rw [logLossLowerCertificate, ← RationalReportLaw.expectation_toReal]
  congr 1
  funext outcome
  push_cast
  rfl

/-- The rational width is the real expectation of the tail bound. -/
theorem logLossCertificateWidth_cast (law : RationalReportLaw Outcome) (forecast : Outcome → ℚ)
    (terms : ℕ) :
    ((logLossCertificateWidth law forecast terms : ℚ) : ℝ) =
      law.toReal.expectation fun outcome ↦
        (1 - (forecast outcome : ℝ)) ^ (terms + 1) / (((terms : ℝ) + 1) * forecast outcome) := by
  rw [logLossCertificateWidth, ← RationalReportLaw.expectation_toReal]
  congr 1
  funext outcome
  push_cast
  rfl

/-- **NOTE 2 equation (30) as a rational certificate.** For a rational law whose forecasts of
the realized outcome lie in `(0, 1]`, the expected negative logarithm lies between the `K`-term
rational lower certificate and that certificate increased by the rational width. -/
theorem logLossCertificate_enclosure (law : RationalReportLaw Outcome) (forecast : Outcome → ℚ)
    (hpos : ∀ outcome, 0 < forecast outcome) (hle : ∀ outcome, forecast outcome ≤ 1)
    (terms : ℕ) :
    ((logLossLowerCertificate law forecast terms : ℚ) : ℝ) ≤
        law.toReal.expectation (fun outcome ↦ -Real.log (forecast outcome)) ∧
      law.toReal.expectation (fun outcome ↦ -Real.log (forecast outcome)) ≤
        ((logLossLowerCertificate law forecast terms +
          logLossCertificateWidth law forecast terms : ℚ) : ℝ) := by
  have hposReal : ∀ outcome, (0 : ℝ) < forecast outcome := fun outcome ↦ by
    exact_mod_cast hpos outcome
  have hleReal : ∀ outcome, (forecast outcome : ℝ) ≤ 1 := fun outcome ↦ by
    exact_mod_cast hle outcome
  obtain ⟨hlower, hgap⟩ := expectation_log_loss_enclosure law.toReal
    (fun outcome ↦ (forecast outcome : ℝ)) hposReal hleReal terms
  rw [Rat.cast_add, logLossLowerCertificate_cast, logLossCertificateWidth_cast]
  exact ⟨hlower, by linarith⟩

/-- The tail bound of NOTE 2 equation (30) decreases in the forecast: at a forecast `r ≥ ρ > 0`
it is at most its value at `ρ`. -/
theorem logTailBound_le_of_floor (floor rate : ℝ) (hfloor : 0 < floor) (hrate : floor ≤ rate)
    (hle : rate ≤ 1) (terms : ℕ) :
    (1 - rate) ^ (terms + 1) / (((terms : ℝ) + 1) * rate) ≤
      (1 - floor) ^ (terms + 1) / (((terms : ℝ) + 1) * floor) := by
  have horder : (0 : ℝ) < (terms : ℝ) + 1 := by positivity
  exact div_le_div₀ (pow_nonneg (by linarith) _)
    (pow_le_pow_left₀ (by linarith) (by linarith) _) (mul_pos horder hfloor)
    (mul_le_mul_of_nonneg_left hrate horder.le)

/-- **The certificate width in general form.** If every forecast of the realized outcome is at
least `ρ > 0` and at most one, the `K`-term rational width is at most
`(1 - ρ)^(K+1) / ((K+1) ρ)`, the tail bound at the smallest forecast. -/
theorem logLossCertificateWidth_le_of_floor (law : RationalReportLaw Outcome)
    (forecast : Outcome → ℚ) (floor : ℚ) (hfloor : 0 < floor)
    (hforecast : ∀ outcome, floor ≤ forecast outcome) (hle : ∀ outcome, forecast outcome ≤ 1)
    (terms : ℕ) :
    logLossCertificateWidth law forecast terms ≤
      (1 - floor) ^ (terms + 1) / (((terms : ℚ) + 1) * floor) := by
  have hreal : ((logLossCertificateWidth law forecast terms : ℚ) : ℝ) ≤
      (1 - (floor : ℝ)) ^ (terms + 1) / (((terms : ℝ) + 1) * floor) := by
    rw [logLossCertificateWidth_cast]
    calc law.toReal.expectation (fun outcome ↦
          (1 - (forecast outcome : ℝ)) ^ (terms + 1) / (((terms : ℝ) + 1) * forecast outcome))
        ≤ law.toReal.expectation (fun _ ↦
          (1 - (floor : ℝ)) ^ (terms + 1) / (((terms : ℝ) + 1) * floor)) :=
          BellmanReportBounds.expectation_mono law.toReal _ _ fun outcome ↦
            logTailBound_le_of_floor floor (forecast outcome) (by exact_mod_cast hfloor)
              (by exact_mod_cast hforecast outcome) (by exact_mod_cast hle outcome) terms
      _ = (1 - (floor : ℝ)) ^ (terms + 1) / (((terms : ℝ) + 1) * floor) :=
          FiniteIndependentMoments.expectation_const law.toReal _
  exact_mod_cast hreal

end Certificate

section Reference

/-- NOTE 2 section 9: every Laplace-smoothed group risk of the reference learner lies in
`[1/4, 3/4]`, one pseudocount for each outcome over at most two training draws. -/
theorem groupRisk_mem_Icc : ∀ (training : Training) (locus : Fin 2) (group : Bool),
    1 / 4 ≤ groupRisk training locus group ∧ groupRisk training locus group ≤ 3 / 4 := by
  decide +kernel

/-- A target observation of the reference experiment: a study's two training draws and its
validation draw, the genotype of a target individual, and that individual's outcome. -/
abbrev TargetObservation : Type := Training × (Fin 3 × Bool) × Genotype × Bool

/-- The forecast probability the frozen reference learner gives the realized outcome of a
target observation: the fitted score for a case and its complement for a control. -/
def realizedForecast (observation : TargetObservation) : ℚ :=
  if observation.2.2.2 then fittedScore observation.1 observation.2.1 observation.2.2.1
  else 1 - fittedScore observation.1 observation.2.1 observation.2.2.1

/-- Every realized forecast of the reference learner lies in `[1/4, 3/4]`, whatever the target
genotype and outcome, so the smallest forecast its log loss can meet is `1/4`. -/
theorem realizedForecast_mem_Icc (observation : TargetObservation) :
    1 / 4 ≤ realizedForecast observation ∧ realizedForecast observation ≤ 3 / 4 := by
  obtain ⟨hlow, hhigh⟩ := groupRisk_mem_Icc observation.1
    (selectedLocus observation.1 observation.2.1)
    (carrier observation.2.2.1 (selectedLocus observation.1 observation.2.1))
  unfold realizedForecast fittedScore
  split_ifs
  · exact ⟨hlow, hhigh⟩
  · constructor <;> linarith

/-- The realized forecasts of the reference learner lie in the half-open unit interval, so the
logarithmic series of NOTE 2 equation (30) applies at every one of them. -/
theorem realizedForecast_pos_le_one (observation : TargetObservation) :
    0 < realizedForecast observation ∧ realizedForecast observation ≤ 1 := by
  obtain ⟨hlow, hhigh⟩ := realizedForecast_mem_Icc observation
  exact ⟨by linarith, by linarith⟩

/-- **NOTE 2 section 9, the reference width in general form.** For any rational law over a
finite observation type projected to target observations, the `K`-term certificate width of
the expected target log loss of the frozen reference learner is at most
`(3/4)^(K+1) / ((K+1)/4)`, the tail bound at the smallest forecast `1/4`. -/
theorem reference_logLossCertificateWidth_le {Observation : Type*} [Fintype Observation]
    (law : RationalReportLaw Observation) (project : Observation → TargetObservation)
    (terms : ℕ) :
    logLossCertificateWidth law (fun observation ↦ realizedForecast (project observation))
        terms ≤
      (1 - 1 / 4) ^ (terms + 1) / (((terms : ℚ) + 1) * (1 / 4)) :=
  logLossCertificateWidth_le_of_floor law _ (1 / 4) (by norm_num)
    (fun observation ↦ (realizedForecast_mem_Icc (project observation)).1)
    (fun observation ↦ (realizedForecast_pos_le_one (project observation)).2) terms

/-- At eighty terms the tail bound at the forecast `1/4` equals `3^77 / 4^80`, which is below
`10^-10`. -/
theorem logTailBound_eighty_quarter :
    (1 - 1 / 4 : ℚ) ^ (80 + 1) / ((((80 : ℕ) : ℚ) + 1) * (1 / 4)) = 3 ^ 77 / 4 ^ 80 ∧
      (3 : ℚ) ^ 77 / 4 ^ 80 < 1 / 10 ^ 10 := by
  norm_num

/-- **NOTE 2 section 9, eighty-term rational certificates.** For any rational law over a finite
observation type projected to target observations of the frozen reference learner, the
eighty-term rational lower certificate `L` and width `W` bracket the expected target log loss,
`L ≤ E[-log r] ≤ L + W`, and the width is below `10^-10`. -/
theorem reference_logLoss_eighty_term_certificate {Observation : Type*} [Fintype Observation]
    (law : RationalReportLaw Observation) (project : Observation → TargetObservation) :
    ((logLossLowerCertificate law (fun observation ↦ realizedForecast (project observation))
        80 : ℚ) : ℝ) ≤
        law.toReal.expectation
          (fun observation ↦ -Real.log (realizedForecast (project observation))) ∧
      law.toReal.expectation
          (fun observation ↦ -Real.log (realizedForecast (project observation))) ≤
        ((logLossLowerCertificate law (fun observation ↦ realizedForecast (project observation))
            80 +
          logLossCertificateWidth law (fun observation ↦ realizedForecast (project observation))
            80 : ℚ) : ℝ) ∧
      logLossCertificateWidth law (fun observation ↦ realizedForecast (project observation))
        80 < 1 / 10 ^ 10 := by
  obtain ⟨hlower, hupper⟩ := logLossCertificate_enclosure law
    (fun observation ↦ realizedForecast (project observation))
    (fun observation ↦ (realizedForecast_pos_le_one (project observation)).1)
    (fun observation ↦ (realizedForecast_pos_le_one (project observation)).2) 80
  obtain ⟨hvalue, hsmall⟩ := logTailBound_eighty_quarter
  exact ⟨hlower, hupper,
    (reference_logLossCertificateWidth_le law project 80).trans_lt (hvalue.trans_lt hsmall)⟩

/-- The frozen reference learner never rules out an outcome, so the extended-valued expected
target log loss of `LogLossSeriesCertificate.expectedLogLoss` is finite and equals the real
expectation of the pointwise loss. -/
theorem reference_expectedLogLoss_eq_ofReal {Observation : Type*} [Fintype Observation]
    (law : RationalReportLaw Observation) (project : Observation → TargetObservation) :
    expectedLogLoss law.toReal
        (fun observation ↦ (realizedForecast (project observation) : ℝ)) =
      ENNReal.ofReal (law.toReal.expectation
        (fun observation ↦ -Real.log (realizedForecast (project observation)))) :=
  expectedLogLoss_eq_ofReal law.toReal _
    (fun observation ↦ by exact_mod_cast (realizedForecast_pos_le_one (project observation)).1)
    (fun observation ↦ by exact_mod_cast (realizedForecast_pos_le_one (project observation)).2)

end Reference

end Descent.Portability.ReferenceLogLossCertificate
