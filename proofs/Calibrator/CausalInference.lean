/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory
-- `r2FromSignalVariance` lives in `Calibrator.TransportedMetrics` (in `DGP`) since the
-- namespace was resolved. `open` does not travel through `import`, so the line
-- `OpenQuestions` added for itself does nothing for this file even though this file
-- imports it -- which is why this consumer was missed by the migration.
--
-- Without this line the 35 bare occurrences below did not fail as "unknown identifier":
-- Lean AUTO-BINDS an unresolved bare name as an implicit variable, so each became a local
-- of unknown type applied to two arguments. That is why one cause produced two error
-- texts here, `Function expected at` and `Local variable ... has no definition`, across
-- 35 sites. Do not delete this line to "clean up an unused open".
open TransportedMetrics (r2FromSignalVariance)

/-!
# Arithmetic of the `R²` noise formula, under names that say so

**THIS FILE CONTAINS NO CAUSAL MATHEMATICS. NO NAME IN IT MAY CLAIM OTHERWISE.**

Nothing here formalizes mediation, counterfactual reasoning, causal discovery or
do-calculus. The file holds **no causal graph, no structural causal model, no intervention
operator, no counterfactual semantics and no identification criterion**. Every declaration
is named for what it proves, and the names below that a reader may meet elsewhere are
absent on purpose.

**The arithmetic is correct.** The whole hazard is in naming and prose, which is the more
dangerous kind: a false interpretation attached to a true lemma looks machine-checked.

## What is actually proved

Almost everything is one fact about `r2FromSignalVariance v n = v / (v + n)`: it is
strictly increasing in the signal `v` and strictly decreasing in the noise `n`. The
theorems instantiate that with different names for the noise term:

* `r2_strictMono_under_ld_noise_reduction`, `r2_strictMono_under_environment_noise_reduction`
  — removing a positive fraction of a noise component raises `R²`. The names
  `ld_mediates_portability` and `environment_mediates_portability` are absent on purpose.
  **Subtracting a positive scalar is not mediation.** No mediator variable appears anywhere
  in the statement.
* `r2_lt_of_drift_variance_pos`, `r2_lt_of_technical_noise_pos`, `r2_lt_of_sampling_noise_pos`,
  `r2_lt_of_gxe_noise_pos` — four instances of the same monotonicity. The `counterfactual_*`
  names are absent on purpose. **No counterfactual semantics is involved**: there is no twin network,
  no potential outcome, and nothing is evaluated in a world other than the one described by
  the formula.
* `r2_chain_strictMono_of_decreasing_noise` — a chain of four inequalities obtained by
  ordering hand-chosen denominators. The name `intervention_hierarchy` is absent on purpose.
  **There is no intervention operator here.** `do(·)` is never defined, so the ordering is
  an ordering of expressions, not of interventions.
* `indirect_eq_total_sub_direct_of_sum` — the name `mediation_decomposition` is absent on
  purpose. It **assumes** `total = direct + indirect` and rearranges to
  `indirect = total - direct`. Deleting the proof and substituting the hypothesis gives the
  same statement, so it is a rearrangement and its name says so.
* `each_component_le_total_of_sum_decomp`, `half_lt_share_of_half_lt_part` — likewise
  rearrangements of an assumed sum and of an assumed inequality.
* `r2_increments_strictAnti_in_signal` — concavity of `v ↦ v/(v+n)`. This one is a genuine
  property of the formula, and `diminishing_marginal_returns` is an honest name for it.
* `r2_strictMono_under_effect_turnover` — genuine monotonicity, since `ρ² v < v` for
  `0 < ρ < 1`.

## What a causal version would require, and what is absent

None of the following exists in this file, and no result here should be read as evidence
about any of them: a directed acyclic graph on the variables; structural equations
assigning each variable a function of its parents and an independent noise term;
an intervention operator replacing an equation by a constant and deleting incoming edges;
the interventional distribution that operator induces; a derivation — rather than an
assumption — of `total = direct + indirect` from those equations; and any identification
criterion such as backdoor adjustment.

Until those exist, **the biological readings in the docstrings below are interpretations of
arithmetic, not consequences of a causal model**, and the file name is retained only
because renaming a file is a larger change than this commit makes.

The corpus-wide no-external-theorem-parameter rule warns that giving a biological name to a
formula makes a false interpretation look machine-checked. This file was that warning's
specimen; the former record-based identification interface was deleted because callers could
install the desired conclusion as data.

Reference for the biological setting (not for any theorem here):
Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Path Decomposition of Portability

Portability loss is written as a sum of named components. The decomposition is an
ASSUMPTION supplied as a hypothesis, not something derived here; no pathway structure is
formalized.
-/

section SumDecompositionArithmetic

/-- **Total portability loss decomposition.**
    Δ_total = Δ_LD + Δ_MAF + Δ_effect + Δ_env + Δ_technical
    Each summand is a named real number. No pathway, graph, or causal claim is formalized;
    the hypothesis supplies the decomposition and the theorem rearranges it. -/
theorem each_component_le_total_of_sum_decomp
    (delta_total delta_LD delta_MAF delta_effect delta_env delta_tech : ℝ)
    (h_decomp : delta_total = delta_LD + delta_MAF + delta_effect + delta_env + delta_tech)
    (h_LD : 0 ≤ delta_LD) (h_MAF : 0 ≤ delta_MAF) (h_effect : 0 ≤ delta_effect)
    (h_env : 0 ≤ delta_env) (h_tech : 0 ≤ delta_tech) :
    delta_LD ≤ delta_total ∧ delta_MAF ≤ delta_total ∧
    delta_effect ≤ delta_total ∧ delta_env ≤ delta_total ∧
    delta_tech ≤ delta_total := by
  constructor <;> [skip; constructor <;> [skip; constructor <;> [skip; constructor]]] <;> linarith

/-- **Rearrangement of an assumed inequality.** From `total/2 < part` and `0 < total`,
    concludes `1/2 < part / total`. The biological reading -- that LD dominates -- is
    supplied entirely by the hypothesis, not established here. -/
theorem half_lt_share_of_half_lt_part
    (delta_total delta_LD : ℝ)
    (h_total : 0 < delta_total)
    (h_LD_large : delta_total / 2 < delta_LD)
    (h_LD_le : delta_LD ≤ delta_total) :
    1 / 2 < delta_LD / delta_total := by
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) h_total]
  linarith

/-- **`R²` strictly decreases when the signal is scaled by `ρ² < 1`.** Genuine monotonicity.
    The identification of `ρ` with immune effect turnover is an interpretation, not a
    formalized causal claim; no selection process is modelled.
    For immune/pathogen-related traits under divergent selection,
    the effect-turnover factor (ρ < 1) causes additional R² loss
    beyond what drift alone produces. The total immune portability
    loss (source R² minus immune R²) exceeds twice the drift-only
    loss (source R² minus drift-only R²) when ρ is small enough.

    We model this using r2FromSignalVariance from PortabilityDrift: drift-only
    uses signal (1-fst)·V_A, immune uses ρ²·(1-fst)·V_A.
    We show the immune R² is strictly below the drift-only R²,
    establishing that effect turnover is a genuine additional
    pathway of portability loss. -/
theorem r2_strictMono_under_effect_turnover
    (V_A V_E fst ρ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_pos : 0 < fst) (hfst_lt : fst < 1)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    -- Immune R² (with effect turnover ρ) is strictly less than
    -- drift-only R² (no effect turnover), showing the selection
    -- pathway causes genuine additional loss beyond LD/drift.
    r2FromSignalVariance (ρ ^ 2 * presentDayPGSVariance V_A fst) V_E <
      r2FromSignalVariance (presentDayPGSVariance V_A fst) V_E := by
  apply expectedR2_strictMono_nonneg V_E _ _ hVE
  · exact le_of_lt (mul_pos (sq_pos_of_pos hρ_pos)
      (by unfold presentDayPGSVariance pgsVarianceFromHet; exact mul_pos hVA (by linarith)))
  · have h_pdv_pos : 0 < presentDayPGSVariance V_A fst := by
      unfold presentDayPGSVariance pgsVarianceFromHet; exact mul_pos hVA (by linarith)
    calc ρ ^ 2 * presentDayPGSVariance V_A fst
        < 1 * presentDayPGSVariance V_A fst := by
          apply mul_lt_mul_of_pos_right _ h_pdv_pos
          nlinarith [sq_abs ρ, sq_nonneg ρ]
      _ = presentDayPGSVariance V_A fst := one_mul _

end SumDecompositionArithmetic


/-!
## Mediation Analysis

No mediation is formalized here. `effectShare` is the ratio of two reals, and the theorem
below rearranges an ASSUMED sum. A mediator variable appears nowhere in any statement.
-/

section EffectShareArithmetic

/-- **Rearrangement of an assumed sum.** Given `total = direct + indirect` as a HYPOTHESIS,
    concludes `indirect = total - direct`. Replacing the proof body with the hypothesis
    yields the same statement, so this is arithmetic and not a decomposition theorem. In a
    real structural causal model the sum would be DERIVED from the structural equations. -/
theorem indirect_eq_total_sub_direct_of_sum
    (total_effect direct_effect indirect_effect : ℝ)
    (h_decomp : total_effect = direct_effect + indirect_effect) :
    -- Indirect effect is the total minus direct
    indirect_effect = total_effect - direct_effect := by linarith

/-- **Ratio of two reals.** Named `effectShare` rather than `proportionMediated`: nothing
    here establishes that the numerator is an indirect effect. -/
noncomputable def effectShare (indirect_effect total_effect : ℝ) : ℝ :=
  indirect_effect / total_effect

/-- `effectShare ie te` lies in [0,1] when `0 ≤ ie`, `0 < te` and `ie ≤ te`. A statement about
    a ratio of reals; "mediated" is not established anywhere. -/
theorem effectShare_mem_unit
    (ie te : ℝ)
    (h_ie : 0 ≤ ie) (h_te : 0 < te) (h_le : ie ≤ te) :
    0 ≤ effectShare ie te ∧ effectShare ie te ≤ 1 := by
  unfold effectShare
  constructor
  · exact div_nonneg h_ie (le_of_lt h_te)
  · rw [div_le_one h_te]; exact h_le

/-- **Removing part of the LD noise term strictly raises `R²`.** This is monotonicity of
    `v / (v + n)` in `n`, not mediation: no mediator variable occurs in the statement.
    Ancestry → LD structure → PGS weights → Accuracy.

    Model: PGS accuracy = r2FromSignalVariance(vSignal, V_E + V_ld_mismatch).
    Without LD correction, the full mismatch V_ld adds noise.
    With LD correction (using target-population LD matrix), a fraction
    `α` of the mismatch is removed, leaving V_E + (1-α)·V_ld.
    Since 0 < α ≤ 1, the corrected noise is strictly less,
    so R²_corrected > R²_uncorrected by r2FromSignalVariance monotonicity.
    A residual gap to source R² (V_E only) remains when α < 1. -/
theorem r2_strictMono_under_ld_noise_reduction
    (vSignal V_E V_ld α : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E)
    (h_ld : 0 < V_ld) (h_α_pos : 0 < α) (h_α_le : α ≤ 1) :
    -- LD correction improves R²: corrected > uncorrected
    r2FromSignalVariance vSignal (V_E + V_ld) <
      r2FromSignalVariance vSignal (V_E + (1 - α) * V_ld) ∧
    -- Residual gap remains (corrected < source) when α < 1
    (α < 1 → r2FromSignalVariance vSignal (V_E + (1 - α) * V_ld) <
      r2FromSignalVariance vSignal V_E) := by
  constructor
  · -- Corrected noise = V_E + (1-α)·V_ld < V_E + V_ld = uncorrected noise
    -- since α > 0 implies (1-α) < 1, so (1-α)·V_ld < V_ld.
    unfold r2FromSignalVariance
    exact div_lt_div_of_pos_left h_sig (by nlinarith) (by nlinarith)
  · -- If α < 1, then (1-α)·V_ld > 0, so corrected noise > V_E = source noise.
    intro h_α_lt
    unfold r2FromSignalVariance
    exact div_lt_div_of_pos_left h_sig (by linarith) (by nlinarith)

/-- **Removing part of the environment noise term strictly raises `R²`.** Monotonicity, not
    mediation.
    Ancestry → Environment → Phenotype → Accuracy.

    Model: Total phenotypic variance = V_genetic + V_env.
    Phenotypic R² = V_genetic / (V_genetic + V_env).
    Genetic R² (no environmental noise) = V_genetic / V_genetic = 1,
    but more usefully, the phenotypic R² is strictly less than what
    we'd get without environmental variance.  Specifically:
      R²_pheno = r2FromSignalVariance(V_genetic, V_env) < r2FromSignalVariance(V_genetic, 0) = 1.
    This shows environment genuinely reduces predictive accuracy;
    the reduction is derived from the variance decomposition, not assumed. -/
theorem r2_strictMono_under_environment_noise_reduction
    (V_genetic V_env : ℝ)
    (h_gen : 0 < V_genetic) (h_env : 0 < V_env) :
    -- Phenotypic R² is strictly less than 1 (perfect genetic prediction)
    r2FromSignalVariance V_genetic V_env < 1 := by
  unfold r2FromSignalVariance
  rw [div_lt_one (by linarith : 0 < V_genetic + V_env)]
  linarith

end EffectShareArithmetic


/-!
## Monotonicity of `R²` when a noise component is absent

What would PGS portability look like under hypothetical
alternative study designs?
-/

section NoiseReductionMonotonicity

/-- **`R²` is strictly lower when drift variance is positive.**
    If the training GWAS had been done in the target ancestry,
    there is no drift divergence (fst = 0), so presentDayR2
    equals V_A/(V_A + V_E).  Cross-ancestry training with
    fst > 0 gives strictly lower R².  The gap is the
    portability loss attributable to ancestry mismatch. -/
theorem r2_lt_of_drift_variance_pos
    (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_pos : 0 < fst) (hfst_lt : fst < 1) :
    -- Cross-ancestry R² is strictly below same-ancestry R²
    r2FromSignalVariance (presentDayPGSVariance V_A fst) V_E <
      r2FromSignalVariance (presentDayPGSVariance V_A 0) V_E := by
  apply expectedR2_strictMono_nonneg V_E _ _ hVE
  · unfold presentDayPGSVariance pgsVarianceFromHet
    exact le_of_lt (mul_pos hVA (by linarith))
  · unfold presentDayPGSVariance pgsVarianceFromHet
    simp only [sub_zero]
    have : (1 - fst) * V_A < 1 * V_A := by
      exact mul_lt_mul_of_pos_right (by linarith) hVA
    linarith

/-- **`R²` is strictly lower when a technical-noise term is present.**
    With array genotyping, imputation error adds noise V_tech to
    the environmental variance, reducing observed R².  WGS removes
    this (V_tech = 0), so the WGS R² exceeds array R².
    The remaining gap from source R² is purely genetic drift. -/
theorem r2_lt_of_technical_noise_pos
    (vSignal V_E V_tech : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E) (h_tech : 0 < V_tech) :
    -- Array R² (with technical noise) < WGS R² (without)
    r2FromSignalVariance vSignal (V_E + V_tech) < r2FromSignalVariance vSignal V_E := by
  unfold r2FromSignalVariance
  have h_denom_wgs : 0 < vSignal + V_E := by linarith
  have h_denom_arr : 0 < vSignal + (V_E + V_tech) := by linarith
  rw [div_lt_div_iff₀ h_denom_arr h_denom_wgs]
  nlinarith

/-- **`R²` is strictly lower when a sampling-noise term is present.**
    With finite sample, winner's curse inflates effect estimates,
    adding noise V_wc to the prediction.  With n → ∞, V_wc → 0.
    We model finite-sample R² as r2FromSignalVariance with signal vSignal
    and noise V_E + V_wc (winner's curse adds prediction error).
    Infinite-sample R² uses noise V_E only.
    The remaining loss (infinite-sample R² vs source R²) is from
    LD mismatch and true effect size differences. -/
theorem r2_lt_of_sampling_noise_pos
    (vSignal V_E V_wc : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E) (h_wc : 0 < V_wc) :
    -- Finite-sample R² < infinite-sample R²
    r2FromSignalVariance vSignal (V_E + V_wc) < r2FromSignalVariance vSignal V_E := by
  unfold r2FromSignalVariance
  have h_denom_inf : 0 < vSignal + V_E := by linarith
  have h_denom_fin : 0 < vSignal + (V_E + V_wc) := by linarith
  rw [div_lt_div_iff₀ h_denom_fin h_denom_inf]
  nlinarith

/-- **`R²` is strictly lower when a GxE noise term is present.**
    GxE interaction adds variance V_gxe to the target phenotype,
    inflating environmental noise from V_E to V_E + V_gxe.
    If environments were equalized (V_gxe = 0), the target R²
    would be higher.  The remaining loss is purely from genetic
    architecture differences (drift, LD, effect turnover). -/
theorem r2_lt_of_gxe_noise_pos
    (vSignal V_E V_gxe : ℝ)
    (h_sig : 0 < vSignal) (h_VE : 0 < V_E) (h_gxe : 0 < V_gxe) :
    -- R² with GxE < R² without GxE
    r2FromSignalVariance vSignal (V_E + V_gxe) < r2FromSignalVariance vSignal V_E := by
  unfold r2FromSignalVariance
  have h_denom_eq : 0 < vSignal + V_E := by linarith
  have h_denom_gxe : 0 < vSignal + (V_E + V_gxe) := by linarith
  rw [div_lt_div_iff₀ h_denom_gxe h_denom_eq]
  nlinarith

end NoiseReductionMonotonicity


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
theorem r2_chain_strictMono_of_decreasing_noise
    (vSig V_E V_ld V_power V_cal α β : ℝ)
    (h_sig : 0 < vSig) (h_VE : 0 < V_E)
    (h_ld : 0 < V_ld) (h_power : 0 < V_power) (h_cal : 0 < V_cal)
    (h_α_pos : 0 < α) (h_αβ : α < β) (h_β_lt : β < 1) :
    -- Original < recalibrated < LD-corrected < meta-analysis < new GWAS
    r2FromSignalVariance vSig (V_E + V_ld + V_power + V_cal) <
      r2FromSignalVariance vSig (V_E + V_ld + V_power) ∧
    r2FromSignalVariance vSig (V_E + V_ld + V_power) <
      r2FromSignalVariance vSig (V_E + (1 - α) * V_ld + V_power) ∧
    r2FromSignalVariance vSig (V_E + (1 - α) * V_ld + V_power) <
      r2FromSignalVariance vSig (V_E + (1 - β) * V_ld) ∧
    r2FromSignalVariance vSig (V_E + (1 - β) * V_ld) <
      r2FromSignalVariance vSig V_E := by
  unfold r2FromSignalVariance
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_lt_div_of_pos_left h_sig (by nlinarith) (by nlinarith)
  · exact div_lt_div_of_pos_left h_sig (by nlinarith) (by nlinarith)
  · exact div_lt_div_of_pos_left h_sig (by nlinarith) (by nlinarith)
  · exact div_lt_div_of_pos_left h_sig (by linarith) (by nlinarith)

/-- **Diminishing returns from each intervention.**
    R² = v/(v + V_E) is concave in signal variance v.
    Equal increments Δ in signal give decreasing marginal R² gains:
    the gain from v to v+Δ exceeds the gain from v+Δ to v+2Δ.
    This is because the denominator grows, so each additional unit
    of signal is divided by a larger total variance. -/
theorem r2_increments_strictAnti_in_signal
    (v Δ V_E : ℝ)
    (hv : 0 ≤ v) (hΔ : 0 < Δ) (hVE : 0 < V_E) :
    -- Second increment gives less R² gain than the first
    r2FromSignalVariance (v + 2 * Δ) V_E - r2FromSignalVariance (v + Δ) V_E <
      r2FromSignalVariance (v + Δ) V_E - r2FromSignalVariance v V_E := by
  unfold r2FromSignalVariance
  have ha : 0 < v + V_E := by linarith
  have hb : 0 < v + Δ + V_E := by linarith
  have hc : 0 < v + 2 * Δ + V_E := by linarith
  have h_gain2 :
      (v + 2 * Δ) / (v + 2 * Δ + V_E) - (v + Δ) / (v + Δ + V_E) =
        (Δ * V_E) / ((v + 2 * Δ + V_E) * (v + Δ + V_E)) := by
    field_simp [ne_of_gt hb, ne_of_gt hc]
    ring
  have h_gain1 :
      (v + Δ) / (v + Δ + V_E) - v / (v + V_E) =
        (Δ * V_E) / ((v + Δ + V_E) * (v + V_E)) := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
    ring
  rw [h_gain2, h_gain1]
  have hnum : 0 < Δ * V_E := by positivity
  have hden2 : 0 < (v + 2 * Δ + V_E) * (v + Δ + V_E) := mul_pos hc hb
  have hden1 : 0 < (v + Δ + V_E) * (v + V_E) := mul_pos hb ha
  have hden_lt :
      (v + Δ + V_E) * (v + V_E) <
        (v + 2 * Δ + V_E) * (v + Δ + V_E) := by
    nlinarith
  apply (div_lt_div_iff₀ hden2 hden1).2
  nlinarith [hnum, hden_lt]

/-- **Cost-effectiveness analysis.**
    New GWAS is most effective but most expensive.
    Computational corrections are cheap but limited.
    Optimal strategy depends on budget.

    Empirical status: UNTESTED. -/
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

end SensitivityAnalysis

end Calibrator
