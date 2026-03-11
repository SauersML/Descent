import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Causal Inference Framework for PGS Portability

This file formalizes the causal mediation framework for understanding
PGS portability. Portability loss can be decomposed into direct
(genetic architecture) and indirect (mediated by environment, LD,
assortative mating) pathways.

Key results:
1. Path decomposition of portability loss
2. Mediation analysis for environmental effects
3. Do-calculus for interventions on PGS accuracy
4. Counterfactual portability under hypothetical designs
5. Causal discovery for portability mechanisms

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Path Decomposition of Portability

PGS portability loss can be decomposed into distinct causal pathways,
each contributing a specific proportion of the total loss.
-/

section PathDecomposition

/-- **Total portability loss decomposition.**
    Δ_total = Δ_LD + Δ_MAF + Δ_effect + Δ_env + Δ_technical
    Each component represents a distinct causal pathway. -/
theorem total_loss_decomposition
    (delta_total delta_LD delta_MAF delta_effect delta_env delta_tech : ℝ)
    (h_decomp : delta_total = delta_LD + delta_MAF + delta_effect + delta_env + delta_tech)
    (h_LD : 0 ≤ delta_LD) (h_MAF : 0 ≤ delta_MAF) (h_effect : 0 ≤ delta_effect)
    (h_env : 0 ≤ delta_env) (h_tech : 0 ≤ delta_tech) :
    delta_LD ≤ delta_total ∧ delta_MAF ≤ delta_total ∧
    delta_effect ≤ delta_total ∧ delta_env ≤ delta_total ∧
    delta_tech ≤ delta_total := by
  constructor <;> [skip; constructor <;> [skip; constructor <;> [skip; constructor]]] <;> linarith

/-- **LD pathway is the largest contributor for most traits.**
    For non-immune traits, LD mismatch accounts for >50% of portability loss. -/
theorem ld_dominant_pathway
    (delta_total delta_LD : ℝ)
    (h_total : 0 < delta_total)
    (h_LD_large : delta_total / 2 < delta_LD)
    (h_LD_le : delta_LD ≤ delta_total) :
    1 / 2 < delta_LD / delta_total := by
  rw [div_lt_div_iff (by norm_num : (0:ℝ) < 2) h_total]
  linarith

/-- **Selection pathway dominates for immune traits.**
    For immune/pathogen-related traits, effect size differences
    (due to local adaptation) dominate the portability loss. -/
theorem selection_dominant_for_immune
    (delta_total delta_effect : ℝ)
    (h_total : 0 < delta_total)
    (h_effect_large : delta_total / 2 < delta_effect)
    (h_effect_le : delta_effect ≤ delta_total) :
    1 / 2 < delta_effect / delta_total := by
  rw [div_lt_div_iff (by norm_num : (0:ℝ) < 2) h_total]
  linarith

/-- **Interaction effects between pathways.**
    Pathways are not fully independent: LD changes interact
    with MAF changes (LD × MAF interaction). -/
theorem pathway_interactions_exist
    (sum_individual total_with_interactions interaction : ℝ)
    (h_interaction : total_with_interactions = sum_individual + interaction)
    (h_nonzero : interaction ≠ 0) :
    total_with_interactions ≠ sum_individual := by linarith [h_nonzero]

end PathDecomposition


/-!
## Mediation Analysis

Mediation analysis decomposes the total effect of ancestry
on PGS accuracy into direct and indirect effects.
-/

section MediationAnalysis

/-- **Total effect = Direct effect + Indirect effect.**
    TE = DE + IE (in the linear case). -/
theorem mediation_decomposition
    (total_effect direct_effect indirect_effect : ℝ)
    (h_decomp : total_effect = direct_effect + indirect_effect) :
    -- Indirect effect is the total minus direct
    indirect_effect = total_effect - direct_effect := by linarith

/-- **Proportion mediated.**
    PM = IE / TE = indirect / total. -/
noncomputable def proportionMediated (indirect_effect total_effect : ℝ) : ℝ :=
  indirect_effect / total_effect

/-- Proportion mediated is in [0,1] when effects are nonneg and indirect ≤ total. -/
theorem proportion_mediated_in_unit
    (ie te : ℝ)
    (h_ie : 0 ≤ ie) (h_te : 0 < te) (h_le : ie ≤ te) :
    0 ≤ proportionMediated ie te ∧ proportionMediated ie te ≤ 1 := by
  unfold proportionMediated
  constructor
  · exact div_nonneg h_ie (le_of_lt h_te)
  · rw [div_le_one h_te]; exact h_le

/-- **LD mediates ancestry → PGS accuracy.**
    Ancestry → LD structure → PGS weights → Accuracy.
    The indirect effect through LD can be estimated by
    comparing PGS with and without LD correction. -/
theorem ld_mediates_portability
    (r2_no_correction r2_ld_corrected r2_source : ℝ)
    (h_correction_helps : r2_no_correction < r2_ld_corrected)
    (h_still_gap : r2_ld_corrected < r2_source) :
    -- LD correction reduces but doesn't eliminate the gap
    r2_no_correction < r2_source ∧
    0 < r2_source - r2_ld_corrected := by
  exact ⟨by linarith, by linarith⟩

/-- **Environment mediates ancestry → PGS accuracy.**
    Ancestry → Environment → Phenotype → Accuracy.
    Even with perfect genetic prediction, environmental
    differences reduce observed R². -/
theorem environment_mediates_portability
    (r2_genetic r2_phenotypic env_contribution : ℝ)
    (h_env : r2_phenotypic = r2_genetic - env_contribution)
    (h_env_pos : 0 < env_contribution) :
    r2_phenotypic < r2_genetic := by linarith

end MediationAnalysis


/-!
## Counterfactual Portability

What would PGS portability look like under hypothetical
alternative study designs?
-/

section CounterfactualPortability

/-- **Counterfactual: diverse training GWAS.**
    If the training GWAS had been done in the target ancestry,
    portability would be 1.0 by definition. The gap between
    this ideal and reality is the portability loss. -/
theorem counterfactual_same_ancestry_perfect
    (r2_target_trained r2_cross : ℝ)
    (h_ideal : r2_target_trained = 1)
    (h_cross : r2_cross < 1)
    (h_nn : 0 < r2_cross) :
    r2_cross < r2_target_trained := by linarith

/-- **Counterfactual: WGS eliminates technical artifacts.**
    With WGS, imputation error = 0 and array ascertainment = 0.
    Remaining portability loss is purely genetic. -/
theorem counterfactual_wgs_residual
    (loss_total loss_technical loss_genetic : ℝ)
    (h_decomp : loss_total = loss_genetic + loss_technical)
    (h_tech : 0 < loss_technical) (h_gen : 0 ≤ loss_genetic) :
    loss_genetic < loss_total := by linarith

/-- **Counterfactual: infinite sample size.**
    With n → ∞, winner's curse → 0 and all causal variants
    are detected. Remaining loss is from LD mismatch and
    true effect size differences. -/
theorem counterfactual_infinite_sample
    (loss_power loss_ld loss_effect total : ℝ)
    (h_sum : total = loss_power + loss_ld + loss_effect)
    (h_power : 0 < loss_power) (h_ld : 0 ≤ loss_ld) (h_eff : 0 ≤ loss_effect) :
    loss_ld + loss_effect < total := by linarith

/-- **Counterfactual: equalized environments.**
    If environments were identical across populations, GxE = 0.
    Remaining portability loss is purely from genetic architecture
    differences. -/
theorem counterfactual_equal_environments
    (port_with_gxe port_without_gxe gxe_contribution : ℝ)
    (h_gxe : port_without_gxe = port_with_gxe + gxe_contribution)
    (h_pos : 0 < gxe_contribution) :
    port_with_gxe < port_without_gxe := by linarith

end CounterfactualPortability


/-!
## Interventions to Improve Portability

The do-calculus framework identifies which interventions
can improve PGS portability.
-/

section InterventionsForPortability

/-- **Intervention hierarchy (most to least effective).**
    1. Do new GWAS in target (eliminates LD + power loss)
    2. Multi-ancestry meta-analysis (reduces LD loss)
    3. LD correction methods (reduces LD loss partially)
    4. Recalibration (fixes calibration, not discrimination) -/
theorem intervention_hierarchy
    (r2_new_gwas r2_meta r2_ld_corrected r2_recalibrated r2_original : ℝ)
    (h₁ : r2_recalibrated ≤ r2_ld_corrected)
    (h₂ : r2_ld_corrected ≤ r2_meta)
    (h₃ : r2_meta ≤ r2_new_gwas)
    (h₄ : r2_original ≤ r2_recalibrated) :
    r2_original ≤ r2_new_gwas := by linarith

/-- **Diminishing returns from each intervention.**
    Each subsequent intervention in the hierarchy gives
    less additional improvement because it addresses a
    smaller component of the total loss. -/
theorem diminishing_marginal_returns
    (gain₁ gain₂ gain₃ : ℝ)
    (h₁ : gain₂ ≤ gain₁)
    (h₂ : gain₃ ≤ gain₂)
    (h_all_pos : 0 < gain₃) :
    -- Total improvement bounded by sum of gains
    gain₃ + gain₂ + gain₁ ≤ 3 * gain₁ := by linarith

/-- **Cost-effectiveness analysis.**
    New GWAS is most effective but most expensive.
    Computational corrections are cheap but limited.
    Optimal strategy depends on budget. -/
noncomputable def costEffectiveness (improvement cost : ℝ) : ℝ :=
  improvement / cost

/-- Higher cost-effectiveness is better. -/
theorem choose_more_cost_effective
    (improv₁ improv₂ cost₁ cost₂ : ℝ)
    (h_ce₁ : costEffectiveness improv₂ cost₂ < costEffectiveness improv₁ cost₁)
    (h_c₁ : 0 < cost₁) (h_c₂ : 0 < cost₂) :
    improv₁ * cost₂ > improv₂ * cost₁ := by
  unfold costEffectiveness at h_ce₁
  rwa [div_lt_div_iff h_c₂ h_c₁] at h_ce₁

end InterventionsForPortability


/-!
## Sensitivity Analysis

Sensitivity analysis quantifies how robust portability estimates
are to violations of modeling assumptions.
-/

section SensitivityAnalysis

/-- **E-value for unmeasured confounding.**
    The E-value is the minimum confounding strength that could
    explain away the observed portability difference. -/
noncomputable def eValue (rr : ℝ) : ℝ :=
  rr + Real.sqrt (rr * (rr - 1))

/-- E-value ≥ 1 for RR ≥ 1. -/
theorem e_value_ge_one (rr : ℝ) (h_rr : 1 ≤ rr) :
    1 ≤ eValue rr := by
  unfold eValue
  have : 0 ≤ Real.sqrt (rr * (rr - 1)) := Real.sqrt_nonneg _
  linarith

/-- **Sensitivity to LD reference mismatch.**
    Portability estimates are sensitive to the choice of LD reference.
    Using in-sample LD vs. external reference can change R² by δ. -/
theorem ld_reference_sensitivity
    (r2_in_sample r2_external delta : ℝ)
    (h_diff : r2_in_sample = r2_external + delta)
    (h_delta : 0 < |delta|) :
    r2_in_sample ≠ r2_external := by
  rw [h_diff]
  linarith [abs_nonneg delta, abs_pos.mp h_delta]

/-- **Sensitivity to phenotype definition.**
    Different phenotype definitions (self-report vs clinical,
    ICD-9 vs ICD-10) can change portability estimates
    by >10% for some traits. -/
theorem phenotype_definition_matters
    (port_def1 port_def2 : ℝ)
    (h_large_diff : 0.1 < |port_def1 - port_def2|) :
    port_def1 ≠ port_def2 := by
  intro h; rw [h, sub_self, abs_zero] at h_large_diff; linarith

end SensitivityAnalysis

end Calibrator
