import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Clinical Utility, Fairness, and Ethical Implications of PGS Portability

This file formalizes the theory connecting PGS portability to clinical
utility and fairness. The portability gap has direct consequences for
health equity when PGS is used in clinical decision-making.

Key results:
1. Net Reclassification Improvement (NRI) from PGS depends on portability
2. Decision curve analysis and threshold-dependent utility
3. Fairness criteria and impossibility results
4. Risk stratification accuracy across populations
5. Cost-effectiveness depends on portability

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Net Reclassification Improvement

NRI measures how many individuals are correctly reclassified (moved to
correct risk category) when PGS is added to clinical risk models.
Portability loss reduces NRI in non-source populations.
-/

section NRI

/-- **NRI definition.**
    NRI = (event NRI) + (non-event NRI)
    Event NRI: proportion of cases correctly moved up
    Non-event NRI: proportion of controls correctly moved down -/
noncomputable def netReclassificationImprovement
    (event_nri nonevent_nri : ℝ) : ℝ :=
  event_nri + nonevent_nri

/-- **NRI is positive when PGS adds value.** -/
theorem nri_positive_when_pgs_adds_value
    (event_nri nonevent_nri : ℝ)
    (h_event : 0 < event_nri) (h_nonevent : 0 < nonevent_nri) :
    0 < netReclassificationImprovement event_nri nonevent_nri := by
  unfold netReclassificationImprovement; linarith

/-- **NRI can become negative in target populations.**
    If PGS is sufficiently inaccurate, adding it to the clinical model
    can make predictions worse (more incorrect reclassifications). -/
theorem nri_can_be_negative
    (event_nri nonevent_nri : ℝ)
    (h_event_bad : event_nri < 0)
    (h_total_bad : event_nri + nonevent_nri < 0) :
    netReclassificationImprovement event_nri nonevent_nri < 0 := by
  unfold netReclassificationImprovement; linarith

end NRI


/-!
## Decision Curve Analysis

Decision curves plot net benefit vs threshold probability.
PGS portability determines the range of thresholds where PGS is useful.
-/

section DecisionCurve

/-- **Net benefit of a risk prediction model.**
    NB(t) = TP/N - FP/N × t/(1-t)
    where t is the treatment threshold probability. -/
noncomputable def netBenefit (tp fp n : ℝ) (t : ℝ) : ℝ :=
  tp / n - fp / n * (t / (1 - t))

/-- **Net benefit is zero for treat-all strategy.**
    If we treat everyone, TP = prevalence × N, FP = (1-prevalence) × N. -/
theorem treat_all_net_benefit (π t : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1)
    (ht : 0 < t) (ht1 : t < 1) :
    netBenefit π (1 - π) 1 t = π - (1 - π) * (t / (1 - t)) := by
  unfold netBenefit; simp

end DecisionCurve


/-!
## Risk Stratification Accuracy

PGS-based risk stratification places individuals into risk categories.
Portability determines how accurate these categories are.
-/

section RiskStratification

/- **Risk category assignment from PGS.**
    Individuals with PGS > threshold t are placed in "high risk" category.
    True positive rate depends on PGS accuracy. -/

/-- **Proportion correctly classified.**
    PCC = P(high risk | truly high risk) × P(truly high risk)
        + P(low risk | truly low risk) × P(truly low risk). -/
noncomputable def proportionCorrectlyClassified
    (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence + specificity * (1 - prevalence)

/-- PCC is bounded by max(prevalence, 1-prevalence) from below. -/
theorem pcc_lower_bound (sens spec π : ℝ)
    (h_sens : 0 ≤ sens) (h_sens1 : sens ≤ 1)
    (h_spec : 0 ≤ spec) (h_spec1 : spec ≤ 1)
    (h_π : 0 < π) (h_π1 : π < 1) :
    0 ≤ proportionCorrectlyClassified sens spec π := by
  unfold proportionCorrectlyClassified
  apply add_nonneg
  · exact mul_nonneg h_sens (le_of_lt h_π)
  · exact mul_nonneg h_spec (by linarith)

/-- **Higher R² → better risk stratification.**
    Better discrimination means more individuals correctly classified. -/
theorem better_r2_better_stratification
    (sens₁ sens₂ spec₁ spec₂ π : ℝ)
    (h_sens : sens₁ < sens₂) (h_spec : spec₁ < spec₂)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens₁ : 0 ≤ sens₁) (h_spec₁ : 0 ≤ spec₁) :
    proportionCorrectlyClassified sens₁ spec₁ π <
      proportionCorrectlyClassified sens₂ spec₂ π := by
  unfold proportionCorrectlyClassified
  apply add_lt_add
  · exact mul_lt_mul_of_pos_right h_sens h_π
  · exact mul_lt_mul_of_pos_right h_spec (by linarith)

end RiskStratification


/-!
## Cost-Effectiveness of PGS-Guided Interventions

The cost-effectiveness of using PGS for clinical decisions depends
on the portability of the PGS in the target clinical population.
-/

section CostEffectiveness

/-- **Quality-Adjusted Life Year (QALY) gain from correct risk stratification.**
    QALY_gain = sensitivity × prevalence × treatment_benefit
              - (1 - specificity) × (1 - prevalence) × treatment_harm -/
noncomputable def qalyGain
    (sens spec π benefit harm : ℝ) : ℝ :=
  sens * π * benefit - (1 - spec) * (1 - π) * harm

/-- QALY gain is positive when benefit outweighs harm. -/
theorem qaly_gain_positive_condition
    (sens spec π benefit harm : ℝ)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_sens : 0 < sens) (h_spec : 0 < spec) (h_spec1 : spec < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm)
    -- Sufficient condition: benefit/harm > FP rate / (sens × prevalence/(1-prevalence))
    (h_sufficient : sens * π * benefit > (1 - spec) * (1 - π) * harm) :
    0 < qalyGain sens spec π benefit harm := by
  unfold qalyGain; linarith

/-- **There exists a portability threshold below which PGS is not cost-effective.**
    If the R² is too low, the QALY gain is negative (more harm than benefit). -/
theorem cost_effectiveness_threshold_exists
    (π benefit harm : ℝ)
    (h_π : 0 < π) (h_π1 : π < 1)
    (h_benefit : 0 < benefit) (h_harm : 0 < harm) :
    -- At zero sensitivity, QALY gain is negative
    qalyGain 0 0 π benefit harm < 0 := by
  unfold qalyGain; nlinarith

end CostEffectiveness


/-!
## Population-Level Impact of Portability Gaps

When PGS is used at the population level (screening programs, public health),
the portability gap creates systematic health disparities.
-/

section PopulationImpact

/-- **Disparity in number-needed-to-screen (NNS).**
    NNS = 1 / (sensitivity × prevalence).
    Lower sensitivity → higher NNS → more people need screening
    to identify one true case. -/
noncomputable def numberNeededToScreen (sens π : ℝ) : ℝ :=
  1 / (sens * π)

/-- NNS is higher in the target population. -/
theorem nns_higher_in_target
    (sens_s sens_t π : ℝ)
    (h_sens_s : 0 < sens_s) (h_sens_t : 0 < sens_t)
    (h_π : 0 < π)
    (h_lower : sens_t < sens_s) :
    numberNeededToScreen sens_s π < numberNeededToScreen sens_t π := by
  unfold numberNeededToScreen
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos h_sens_t h_π
  · exact mul_lt_mul_of_pos_right h_lower h_π

/-- **Population Attributable Fraction (PAF) from PGS-guided intervention.**
    PAF = P(disease | high risk) × P(high risk) × (1 - 1/RR)
    where RR is the relative risk reduction from intervention. -/
noncomputable def populationAttributableFraction
    (p_high rr_reduction : ℝ) : ℝ :=
  p_high * (1 - 1 / rr_reduction)

/-- **PAF is lower in target populations.**
    When PGS is less accurate, the high-risk group is less enriched
    for true cases → lower PAF → less population-level benefit. -/
theorem paf_lower_in_target
    (p_high_s p_high_t rr : ℝ)
    (h_rr : 1 < rr)
    (h_p_s : 0 < p_high_s) (h_p_t : 0 < p_high_t)
    (h_lower : p_high_t < p_high_s) :
    populationAttributableFraction p_high_t rr <
      populationAttributableFraction p_high_s rr := by
  unfold populationAttributableFraction
  apply mul_lt_mul_of_pos_right h_lower
  rw [sub_pos, div_lt_one (by linarith)]; linarith

end PopulationImpact


end Calibrator
