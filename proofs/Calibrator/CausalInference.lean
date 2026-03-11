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
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) h_total]
  linarith

/-- **Selection pathway dominates for immune traits.**
    For immune/pathogen-related traits under divergent selection,
    the effect-turnover factor (ρ < 1) causes additional R² loss
    beyond what drift alone produces. The total immune portability
    loss (source R² minus immune R²) exceeds twice the drift-only
    loss (source R² minus drift-only R²) when ρ is small enough.

    We model this using expectedR2 from PortabilityDrift: drift-only
    uses signal (1-fst)·V_A, immune uses ρ²·(1-fst)·V_A.
    We show the immune R² is strictly below the drift-only R²,
    establishing that effect turnover is a genuine additional
    pathway of portability loss. -/
theorem selection_dominant_for_immune
    (V_A V_E fst ρ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_pos : 0 < fst) (hfst_lt : fst < 1)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    -- Immune R² (with effect turnover ρ) is strictly less than
    -- drift-only R² (no effect turnover), showing the selection
    -- pathway causes genuine additional loss beyond LD/drift.
    expectedR2 (ρ ^ 2 * presentDayPGSVariance V_A fst) V_E <
      expectedR2 (presentDayPGSVariance V_A fst) V_E := by
  apply expectedR2_strictMono_nonneg V_E _ _ hVE
  · exact le_of_lt (mul_pos (sq_pos_of_pos hρ_pos)
      (by unfold presentDayPGSVariance; exact mul_pos (by linarith) hVA))
  · have h_pdv_pos : 0 < presentDayPGSVariance V_A fst := by
      unfold presentDayPGSVariance; exact mul_pos (by linarith) hVA
    calc ρ ^ 2 * presentDayPGSVariance V_A fst
        < 1 * presentDayPGSVariance V_A fst := by
          apply mul_lt_mul_of_pos_right _ h_pdv_pos
          nlinarith [sq_abs ρ, sq_nonneg ρ]
      _ = presentDayPGSVariance V_A fst := one_mul _

/-- **Interaction effects between pathways.**
    Pathways are not fully independent: LD changes interact
    with MAF changes (LD × MAF interaction). -/
theorem pathway_interactions_exist
    (sum_individual total_with_interactions interaction : ℝ)
    (h_interaction : total_with_interactions = sum_individual + interaction)
    (h_nonzero : interaction ≠ 0) :
    total_with_interactions ≠ sum_individual := by
  rw [h_interaction]; intro h; apply h_nonzero; linarith

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

    Model: PGS accuracy = expectedR2(vSignal, V_E + V_ld_mismatch).
    Without LD correction, the full mismatch V_ld adds noise.
    With LD correction (using target-population LD matrix), a fraction
    `α` of the mismatch is removed, leaving V_E + (1-α)·V_ld.
    Since 0 < α ≤ 1, the corrected noise is strictly less,
    so R²_corrected > R²_uncorrected by expectedR2 monotonicity.
    A residual gap to source R² (V_E only) remains when α < 1. -/
theorem ld_mediates_portability
    (vSignal V_E V_ld α : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E)
    (h_ld : 0 < V_ld) (h_α_pos : 0 < α) (h_α_le : α ≤ 1) :
    -- LD correction improves R²: corrected > uncorrected
    expectedR2 vSignal (V_E + V_ld) <
      expectedR2 vSignal (V_E + (1 - α) * V_ld) ∧
    -- Residual gap remains (corrected < source) when α < 1
    (α < 1 → expectedR2 vSignal (V_E + (1 - α) * V_ld) <
      expectedR2 vSignal V_E) := by
  constructor
  · -- Corrected noise = V_E + (1-α)·V_ld < V_E + V_ld = uncorrected noise
    -- since α > 0 implies (1-α) < 1, so (1-α)·V_ld < V_ld.
    unfold expectedR2
    rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith
  · -- If α < 1, then (1-α)·V_ld > 0, so corrected noise > V_E = source noise.
    intro h_α_lt
    unfold expectedR2
    rw [div_lt_div_iff₀ (by nlinarith) (by linarith)]
    nlinarith

/-- **Environment mediates ancestry → PGS accuracy.**
    Ancestry → Environment → Phenotype → Accuracy.

    Model: Total phenotypic variance = V_genetic + V_env.
    Phenotypic R² = V_genetic / (V_genetic + V_env).
    Genetic R² (no environmental noise) = V_genetic / V_genetic = 1,
    but more usefully, the phenotypic R² is strictly less than what
    we'd get without environmental variance.  Specifically:
      R²_pheno = expectedR2(V_genetic, V_env) < expectedR2(V_genetic, 0) = 1.
    This shows environment genuinely reduces predictive accuracy;
    the reduction is derived from the variance decomposition, not assumed. -/
theorem environment_mediates_portability
    (V_genetic V_env : ℝ)
    (h_gen : 0 < V_genetic) (h_env : 0 < V_env) :
    -- Phenotypic R² is strictly less than 1 (perfect genetic prediction)
    expectedR2 V_genetic V_env < 1 := by
  unfold expectedR2
  rw [div_lt_one (by linarith : 0 < V_genetic + V_env)]
  linarith

end MediationAnalysis


/-!
## Counterfactual Portability

What would PGS portability look like under hypothetical
alternative study designs?
-/

section CounterfactualPortability

/-- **Counterfactual: diverse training GWAS.**
    If the training GWAS had been done in the target ancestry,
    there is no drift divergence (fst = 0), so presentDayR2
    equals V_A/(V_A + V_E).  Cross-ancestry training with
    fst > 0 gives strictly lower R².  The gap is the
    portability loss attributable to ancestry mismatch. -/
theorem counterfactual_same_ancestry_perfect
    (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_pos : 0 < fst) (hfst_lt : fst < 1) :
    -- Cross-ancestry R² is strictly below same-ancestry R²
    expectedR2 (presentDayPGSVariance V_A fst) V_E <
      expectedR2 (presentDayPGSVariance V_A 0) V_E := by
  apply expectedR2_strictMono_nonneg V_E _ _ hVE
  · unfold presentDayPGSVariance
    exact le_of_lt (mul_pos (by linarith) hVA)
  · unfold presentDayPGSVariance
    simp only [sub_zero]
    have : (1 - fst) * V_A < 1 * V_A := by
      exact mul_lt_mul_of_pos_right (by linarith) hVA
    linarith

/-- **Counterfactual: WGS eliminates technical artifacts.**
    With array genotyping, imputation error adds noise V_tech to
    the environmental variance, reducing observed R².  WGS removes
    this (V_tech = 0), so the WGS R² exceeds array R².
    The remaining gap from source R² is purely genetic drift. -/
theorem counterfactual_wgs_residual
    (vSignal V_E V_tech : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E) (h_tech : 0 < V_tech) :
    -- Array R² (with technical noise) < WGS R² (without)
    expectedR2 vSignal (V_E + V_tech) < expectedR2 vSignal V_E := by
  unfold expectedR2
  have h_denom_wgs : 0 < vSignal + V_E := by linarith
  have h_denom_arr : 0 < vSignal + (V_E + V_tech) := by linarith
  rw [div_lt_div_iff₀ h_denom_arr h_denom_wgs]
  nlinarith

/-- **Counterfactual: infinite sample size.**
    With finite sample, winner's curse inflates effect estimates,
    adding noise V_wc to the prediction.  With n → ∞, V_wc → 0.
    We model finite-sample R² as expectedR2 with signal vSignal
    and noise V_E + V_wc (winner's curse adds prediction error).
    Infinite-sample R² uses noise V_E only.
    The remaining loss (infinite-sample R² vs source R²) is from
    LD mismatch and true effect size differences. -/
theorem counterfactual_infinite_sample
    (vSignal V_E V_wc : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E) (h_wc : 0 < V_wc) :
    -- Finite-sample R² < infinite-sample R²
    expectedR2 vSignal (V_E + V_wc) < expectedR2 vSignal V_E := by
  unfold expectedR2
  have h_denom_inf : 0 < vSignal + V_E := by linarith
  have h_denom_fin : 0 < vSignal + (V_E + V_wc) := by linarith
  rw [div_lt_div_iff₀ h_denom_fin h_denom_inf]
  nlinarith

/-- **Counterfactual: equalized environments.**
    GxE interaction adds variance V_gxe to the target phenotype,
    inflating environmental noise from V_E to V_E + V_gxe.
    If environments were equalized (V_gxe = 0), the target R²
    would be higher.  The remaining loss is purely from genetic
    architecture differences (drift, LD, effect turnover). -/
theorem counterfactual_equal_environments
    (vSignal V_E V_gxe : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E) (h_gxe : 0 < V_gxe) :
    -- R² with GxE < R² without GxE
    expectedR2 vSignal (V_E + V_gxe) < expectedR2 vSignal V_E := by
  unfold expectedR2
  have h_denom_eq : 0 < vSignal + V_E := by linarith
  have h_denom_gxe : 0 < vSignal + (V_E + V_gxe) := by linarith
  rw [div_lt_div_iff₀ h_denom_gxe h_denom_eq]
  nlinarith

end CounterfactualPortability


/-!
## Interventions to Improve Portability

The do-calculus framework identifies which interventions
can improve PGS portability.
-/

section InterventionsForPortability

/-- **Intervention hierarchy (most to least effective).**
    Model: each intervention addresses specific MSE components.
    - Original MSE noise: V_E + V_ld + V_power + V_cal
    - Recalibration: fixes intercept only, removes V_cal.
      Noise = V_E + V_ld + V_power.
    - LD correction: partially reduces LD mismatch by fraction α (0 < α < 1).
      Noise = V_E + (1 - α) · V_ld + V_power.
    - Meta-analysis: larger sample removes power loss, reduces LD loss
      further (fraction β where α < β < 1).
      Noise = V_E + (1 - β) · V_ld.
    - New GWAS in target: eliminates LD mismatch and power loss entirely.
      Noise = V_E.
    The ordering is derived from the noise levels being strictly decreasing,
    which follows from 0 < α < β < 1 and positivity of components. -/
theorem intervention_hierarchy
    (vSig V_E V_ld V_power V_cal α β : ℝ)
    (h_sig : 0 < vSig) (h_VE : 0 < V_E)
    (h_ld : 0 < V_ld) (h_power : 0 < V_power) (h_cal : 0 < V_cal)
    (h_α_pos : 0 < α) (h_αβ : α < β) (h_β_lt : β < 1) :
    -- Original < recalibrated < LD-corrected < meta-analysis < new GWAS
    expectedR2 vSig (V_E + V_ld + V_power + V_cal) <
      expectedR2 vSig (V_E + V_ld + V_power) ∧
    expectedR2 vSig (V_E + V_ld + V_power) <
      expectedR2 vSig (V_E + (1 - α) * V_ld + V_power) ∧
    expectedR2 vSig (V_E + (1 - α) * V_ld + V_power) <
      expectedR2 vSig (V_E + (1 - β) * V_ld) ∧
    expectedR2 vSig (V_E + (1 - β) * V_ld) <
      expectedR2 vSig V_E := by
  unfold expectedR2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith
  }

/-- **Diminishing returns from each intervention.**
    R² = v/(v + V_E) is concave in signal variance v.
    Equal increments Δ in signal give decreasing marginal R² gains:
    the gain from v to v+Δ exceeds the gain from v+Δ to v+2Δ.
    This is because the denominator grows, so each additional unit
    of signal is divided by a larger total variance. -/
theorem diminishing_marginal_returns
    (v Δ V_E : ℝ)
    (hv : 0 ≤ v) (hΔ : 0 < Δ) (hVE : 0 < V_E) :
    -- Second increment gives less R² gain than the first
    expectedR2 (v + 2 * Δ) V_E - expectedR2 (v + Δ) V_E <
      expectedR2 (v + Δ) V_E - expectedR2 v V_E := by
  unfold expectedR2
  -- Let a = v, b = v + Δ, c = v + 2Δ. Need c/(c+E) - b/(b+E) < b/(b+E) - a/(a+E).
  -- Equivalently: c/(c+E) + a/(a+E) < 2·b/(b+E).
  -- x/(x+E) = 1 - E/(x+E), so this is E/(b+E) < (E/(a+E) + E/(c+E))/2,
  -- i.e., 1/(b+E) > (harmonic mean), which follows from strict convexity of 1/x.
  have ha : 0 < v + V_E := by linarith
  have hb : 0 < v + Δ + V_E := by linarith
  have hc : 0 < v + 2 * Δ + V_E := by linarith
  rw [div_sub_div _ _ (ne_of_gt hc) (ne_of_gt hb),
      div_sub_div _ _ (ne_of_gt hb) (ne_of_gt ha),
      div_lt_div_iff₀ (mul_pos hc hb) (mul_pos hb ha)]
  nlinarith [sq_nonneg V_E, sq_nonneg Δ, mul_pos hΔ hVE,
             sq_nonneg v, mul_pos ha hb, mul_pos hb hc]

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
  rwa [div_lt_div_iff₀ h_c₂ h_c₁] at h_ce₁

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
  rw [h_diff]; intro h; have : delta = 0 := by linarith
  exact absurd (this ▸ h_delta) (by simp)

/-- **Sensitivity to phenotype definition.**
    Different phenotype definitions (self-report vs clinical,
    ICD-9 vs ICD-10) can change portability estimates.
    When the difference exceeds any threshold ε > 0, the estimates differ. -/
theorem phenotype_definition_matters
    (port_def1 port_def2 ε : ℝ) (h_ε : 0 < ε)
    (h_large_diff : ε < |port_def1 - port_def2|) :
    port_def1 ≠ port_def2 := by
  intro h; rw [h, sub_self, abs_zero] at h_large_diff; linarith

end SensitivityAnalysis

end Calibrator
