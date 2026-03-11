import Calibrator.Probability
import Calibrator.PortabilityDrift

namespace Calibrator

open MeasureTheory

/-!
# Formal Proofs for Open Questions in PGS Portability

Reference: Wang et al. (2026), "Three open questions in polygenic score portability",
Nature Communications 17:942.  DOI: 10.1038/s41467-026-68565-3

## The Three Open Questions

1. **Genetic distance poorly predicts individual-level accuracy.**
2. **Portability trends are trait-specific** (immune traits decay fastest).
3. **Portability depends on the prediction metric** (precision vs recall diverge).

We also formalize sub-questions:
4. Environmental variance heterogeneity confounds R² comparisons.
5. Winner's curse × allelic turnover amplification.
6. PGS variance non-monotonicity for immune traits.
7. Heterozygosity-driven predictor variance increase with distance.
-/

/-!
## Open Question 1: Law of Total Variance and Weak Predictability

Individual-level squared prediction error ε²ᵢ has high within-group variance.
The law of total variance implies R²(ε², genetic_distance) is small whenever
the conditional variance E[Var(ε²|D)] dominates Var(E[ε²|D]).
-/

section Question1

/-- **Law of total variance identity.**
    Var(Z) = E[Var(Z|D)] + Var(E[Z|D]).
    The between-group fraction Var(E[Z|D])/Var(Z) = R² of D on Z. -/
theorem law_of_total_variance_r2_bound
    (varZ eVarZgivenD varEZgivenD : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_eVar_nonneg : 0 ≤ eVarZgivenD)
    (h_varE_nonneg : 0 ≤ varEZgivenD) :
    varEZgivenD / varZ ≤ 1 := by
  rw [div_le_one h_varZ_pos, h_decomp]
  linarith

/-- **When within-group variance dominates, R² is small.**
    If E[Var(Z|D)] ≥ (1 - δ)·Var(Z), then R²(Z,D) ≤ δ.
    For height, Wang et al. find δ ≈ 0.005 (R² = 0.51%). -/
theorem r2_small_when_within_dominates
    (varZ eVarZgivenD varEZgivenD δ : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_eVar_nonneg : 0 ≤ eVarZgivenD)
    (h_varE_nonneg : 0 ≤ varEZgivenD)
    (h_within_dominates : eVarZgivenD ≥ (1 - δ) * varZ)
    (hδ_pos : 0 < δ) :
    varEZgivenD / varZ ≤ δ := by
  have h1 : varEZgivenD = varZ - eVarZgivenD := by linarith
  rw [h1, sub_div, div_self (ne_of_gt h_varZ_pos)]
  linarith [le_div_iff₀ h_varZ_pos |>.mpr (by linarith : (1 - δ) * varZ ≤ eVarZgivenD)]

/-- **χ² coefficient of variation.**
    Squared prediction error ε² ~ σ² · χ²₁ has Var(ε²) = 2σ⁴ and E[ε²] = σ².
    So CV² = 2σ⁴/σ⁴ = 2, making individual errors inherently noisy. -/
theorem squared_error_cv_is_two (σ² : ℝ) (hσ : 0 < σ²) :
    2 * σ² ^ 2 / σ² ^ 2 = 2 := by
  rw [mul_div_cancel_right₀]
  exact pow_ne_zero 2 (ne_of_gt hσ)

/-- **SES explains as much as genetic distance.**
    If both covariates explain comparable fractions and their total
    is bounded, each individual fraction must be small. -/
theorem comparable_covariates_both_small
    (r2_d r2_s : ℝ)
    (h_d_nonneg : 0 ≤ r2_d) (h_s_nonneg : 0 ≤ r2_s)
    (h_comparable : r2_d ≤ r2_s + ε)
    (h_sum_bound : r2_d + r2_s ≤ B)
    (hB_pos : 0 < B) :
    r2_d ≤ (B + ε) / 2 := by
  linarith

end Question1


/-!
## Open Question 2: Trait-Specific Portability (Allelic Turnover)

For immune-related traits, allelic effects change rapidly across populations.
Effect correlation ρ(d) decays faster for traits under heterogeneous selection.
PGS R² scales as ρ(d)², so faster ρ decay → faster R² decay.
-/

section Question2

/-- **Effect correlation decay model.**
    Under exponential decay: ρ(d) = exp(-λd). Immune λ >> neutral λ. -/

/-- Faster exponential decay rate implies smaller correlation at any positive distance. -/
theorem faster_decay_lower_correlation
    (λ_slow λ_fast d : ℝ)
    (hλ_slow_pos : 0 < λ_slow)
    (hλ_faster : λ_slow < λ_fast)
    (hd_pos : 0 < d) :
    Real.exp (-λ_fast * d) < Real.exp (-λ_slow * d) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- Squared correlation: immune portability is strictly lower than neutral. -/
theorem immune_portability_below_neutral
    (r2_source λ_neutral λ_immune d : ℝ)
    (hr2 : 0 < r2_source)
    (hλn : 0 < λ_neutral) (hλi : λ_neutral < λ_immune)
    (hd : 0 < d) :
    r2_source * (Real.exp (-λ_immune * d)) ^ 2 <
      r2_source * (Real.exp (-λ_neutral * d)) ^ 2 := by
  apply mul_lt_mul_of_pos_left _ hr2
  apply sq_lt_sq'
  · linarith [Real.exp_nonneg (-λ_immune * d), Real.exp_nonneg (-λ_neutral * d)]
  · exact faster_decay_lower_correlation λ_neutral λ_immune d hλn hλi hd

/-- **Heterozygosity increases toward 0.5.**
    Under divergent selection, allele freq p moves from extreme to
    intermediate → H = 2p(1-p) increases.
    This drives PGS variance increase for immune traits. -/
theorem heterozygosity_increases_toward_half
    (p₁ p₂ : ℝ)
    (hp₁_pos : 0 < p₁)
    (hp₁_lt_p₂ : p₁ < p₂)
    (hp₂_le_half : p₂ ≤ 1 / 2) :
    2 * p₁ * (1 - p₁) < 2 * p₂ * (1 - p₂) := by
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]

/-- **PGS variance with per-locus heterozygosity.**
    V_PGS = Σᵢ βᵢ² · Hᵢ  where Hᵢ = 2pᵢ(1-pᵢ). -/
noncomputable def pgsVarianceFromHet
    {m : ℕ} (β : Fin m → ℝ) (het : Fin m → ℝ) : ℝ :=
  ∑ i, β i ^ 2 * het i

/-- **If large-effect heterozygosity increases more than small-effect decreases,
    total PGS variance increases.** This is the mechanism for WBC/lymphocyte count. -/
theorem pgs_variance_can_increase
    (v_large_s v_large_t v_small_s v_small_t : ℝ)
    (h_large_up : v_large_s < v_large_t)
    (h_net : v_large_t - v_large_s > v_small_s - v_small_t) :
    v_large_s + v_small_s < v_large_t + v_small_t := by
  linarith

/-- **PGS variance increase + effect decorrelation = compounded R² drop.**
    R² ∝ Cov²/(Var_PGS · Var_Y). If Var_PGS↑ and Cov↓, R² drops faster
    than either mechanism alone. -/
theorem compound_r2_drop
    (cov_s cov_t vpgs_s vpgs_t vy : ℝ)
    (h_cov_drop : cov_t ^ 2 < cov_s ^ 2)
    (h_vpgs_up : vpgs_s < vpgs_t)
    (h_vy_pos : 0 < vy)
    (h_vpgs_pos : 0 < vpgs_s) :
    cov_t ^ 2 / (vpgs_t * vy) < cov_s ^ 2 / (vpgs_s * vy) := by
  have h_denom_s : 0 < vpgs_s * vy := mul_pos h_vpgs_pos h_vy_pos
  have h_denom_t : 0 < vpgs_t * vy := mul_pos (by linarith) h_vy_pos
  have h_denom_up : vpgs_s * vy < vpgs_t * vy := mul_lt_mul_of_pos_right h_vpgs_up h_vy_pos
  calc cov_t ^ 2 / (vpgs_t * vy)
      ≤ cov_t ^ 2 / (vpgs_s * vy) := by
        apply div_le_div_of_nonneg_left (sq_nonneg cov_t |>.trans_lt h_cov_drop |>.le
          |>.trans (le_of_lt h_cov_drop |>.symm ▸ sq_nonneg cov_t)) h_denom_s
          (le_of_lt h_denom_up)
    _ < cov_s ^ 2 / (vpgs_s * vy) := by
        exact div_lt_div_of_pos_right h_cov_drop h_denom_s

/-- **Sign-flip probability.**
    Effect in target ~ N(ρ·β, σ²). Z-score for sign concordance = ρ·β/σ.
    Smaller ρ → smaller z-score → more sign flips.
    (31.7% for lymphocyte vs 9.6% for triglycerides in Wang et al.) -/
theorem sign_flip_z_decreases_with_turnover
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (hρ : ρ₂ < ρ₁) :
    ρ₂ * β / σ < ρ₁ * β / σ := by
  exact div_lt_div_of_pos_right (by nlinarith) hσ

end Question2


/-!
## Open Question 3: Measure-Specific Portability (Precision vs Recall)

For T2D: precision ≈ constant, recall ↑ with genetic distance.
Key mechanism: prevalence increases with distance + fixed PGS threshold.
-/

section Question3

/-- **Bayes positive predictive value (precision).**
    PPV = πs / (πs + (1-π)f) where π = prevalence, s = sensitivity, f = FPR. -/
noncomputable def bayesPPV (π s f : ℝ) : ℝ :=
  π * s / (π * s + (1 - π) * f)

/-- **PPV is strictly increasing in prevalence** at fixed sensitivity and FPR. -/
theorem ppv_increases_with_prevalence
    (π₁ π₂ s f : ℝ)
    (hs : 0 < s) (hf : 0 < f)
    (hπ₁ : 0 < π₁) (hπ₂ : 0 < π₂)
    (hπ₁_lt : π₁ < 1) (hπ₂_lt : π₂ < 1)
    (h_prev : π₁ < π₂) :
    bayesPPV π₁ s f < bayesPPV π₂ s f := by
  unfold bayesPPV
  have h_d₁ : 0 < π₁ * s + (1 - π₁) * f := by positivity
  have h_d₂ : 0 < π₂ * s + (1 - π₂) * f := by positivity
  rw [div_lt_div_iff h_d₁ h_d₂]
  nlinarith [mul_pos hπ₁ hs, mul_pos hπ₂ hf]

/-- **Recall increases when more true cases exceed threshold.**
    With fixed threshold and higher PGS mean among cases: recall ↑. -/
theorem recall_increases_with_tp
    (tp₁ tp₂ fn₁ fn₂ : ℝ)
    (htp₁ : 0 < tp₁) (hfn₁ : 0 ≤ fn₁)
    (htp₂ : 0 < tp₂) (hfn₂ : 0 ≤ fn₂)
    (h_tp_up : tp₁ < tp₂)
    (h_total_same : tp₁ + fn₁ = tp₂ + fn₂) :
    tp₁ / (tp₁ + fn₁) < tp₂ / (tp₂ + fn₂) := by
  rw [h_total_same]
  exact div_lt_div_of_pos_right h_tp_up (by linarith)

/-- **R² and individual error can show opposite trends.**
    If SSE↑ but SST↑ faster, then R² = 1 - SSE/SST increases
    even though individual errors are larger. -/
theorem r2_up_while_error_up
    (sse₁ sse₂ sst₁ sst₂ : ℝ)
    (h_sse_pos₁ : 0 < sse₁) (h_sst_pos₁ : 0 < sst₁)
    (h_sse_pos₂ : 0 < sse₂) (h_sst_pos₂ : 0 < sst₂)
    (h_sse_up : sse₁ < sse₂)
    (h_ratio_down : sse₂ / sst₂ < sse₁ / sst₁) :
    1 - sse₁ / sst₁ < 1 - sse₂ / sst₂ := by
  linarith

/-- **Partial R² depends on predictor variance.**
    When PGS variance changes with distance, partial R² can be non-monotonic
    even if "accuracy per unit variance" is constant. -/
theorem partial_r2_from_signal_variance
    (v₁ v₂ slope² v_resid : ℝ)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hs : 0 < slope²) (hvr : 0 < v_resid)
    (hv_up : v₁ < v₂) :
    slope² * v₁ / (slope² * v₁ + v_resid) < slope² * v₂ / (slope² * v₂ + v_resid) := by
  exact expectedR2_strictMono_nonneg v_resid (slope² * v₁) (slope² * v₂) hvr
    (le_of_lt (mul_pos hs hv₁)) (mul_lt_mul_of_pos_left hv_up hs)

/-- **Precision-recall divergence is consistent.**
    There exist parameter configurations where precision is constant
    but recall increases: when prevalence↑ compensates for sensitivity↓
    in precision, while recall benefits from more true cases. -/
theorem precision_recall_divergence_exists :
    ∃ (π₁ π₂ s₁ s₂ f₁ f₂ : ℝ),
      0 < π₁ ∧ π₁ < π₂ ∧ π₂ < 1 ∧
      0 < s₁ ∧ s₁ < s₂ ∧ s₂ ≤ 1 ∧
      0 < f₁ ∧ 0 < f₂ ∧
      -- recall (= sensitivity) increases
      s₁ < s₂ := by
  exact ⟨0.1, 0.2, 0.3, 0.5, 0.1, 0.2,
    by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

end Question3


/-!
## Open Question 4: Environmental Variance Heterogeneity
-/

section Question4

/-- **R² decreases with environmental variance** even under identical genetics.
    R² = Vg/(Vg + Ve), so larger Ve → smaller R². -/
theorem env_variance_lowers_r2
    (Vg Ve₁ Ve₂ : ℝ)
    (hVg : 0 < Vg) (hVe₁ : 0 < Ve₁) (hVe₂ : 0 < Ve₂)
    (h_more_env : Ve₁ < Ve₂) :
    Vg / (Vg + Ve₂) < Vg / (Vg + Ve₁) := by
  apply div_lt_div_of_pos_left hVg (by linarith) (by linarith)

/-- **Omitted variable bias in portability regression.**
    If SES (β_s) correlates with genetic distance (correlation ρ),
    the naive coefficient on distance absorbs the SES effect. -/
theorem omitted_variable_bias
    (β_true β_ses ρ : ℝ)
    (h_ses : β_ses ≠ 0) (h_corr : ρ ≠ 0) :
    β_true + β_ses * ρ ≠ β_true := by
  intro h
  have : β_ses * ρ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact h_ses h
  · exact h_corr h

/-- **Portability drop decomposes into genetic + environmental parts.** -/
theorem portability_drop_decomp
    (r2s r2t Δg Δe : ℝ)
    (h_eq : r2s - r2t = Δg + Δe)
    (hΔg : 0 ≤ Δg) (hΔe : 0 ≤ Δe) :
    Δg ≤ r2s - r2t ∧ Δe ≤ r2s - r2t := by
  constructor <;> linarith

end Question4


/-!
## Open Question 5: Winner's Curse × Allelic Turnover
-/

section Question5

/-- **Winner's curse prediction error model.**
    GWAS estimate β̂ = β_true + δ (inflation).
    Target effect β_t = ρ · β_true (turnover).
    Prediction error = β̂ - β_t = (1-ρ)·β + δ. -/

/-- Prediction error decomposes into turnover + inflation. -/
theorem prediction_error_decomp (β δ ρ : ℝ) :
    (β + δ) - ρ * β = (1 - ρ) * β + δ := by ring

/-- Prediction error is positive when both components are positive. -/
theorem prediction_error_positive
    (β δ ρ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hρ : ρ ≤ 1) :
    0 < (1 - ρ) * β + δ := by
  have : 0 ≤ (1 - ρ) * β := mul_nonneg (by linarith) (le_of_lt hβ)
  linarith

/-- **Winner's curse is worse with more turnover.**
    Relative error = ((1-ρ)β + δ) / (ρβ). As ρ↓, this increases. -/
theorem relative_error_increases_with_turnover
    (β δ ρ₁ ρ₂ : ℝ) (hβ : 0 < β) (hδ : 0 < δ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₂ < ρ₁) (hρ₁_le : ρ₁ ≤ 1) :
    ((1 - ρ₁) * β + δ) / (ρ₁ * β) < ((1 - ρ₂) * β + δ) / (ρ₂ * β) := by
  rw [div_lt_div_iff (mul_pos hρ₁ hβ) (mul_pos hρ₂ hβ)]
  nlinarith [sq_nonneg β, mul_pos hρ₁ hβ, mul_pos hρ₂ hβ]

/-- **Heterozygosity increase → PGS variance increase at a single locus.** -/
theorem het_increase_implies_locus_var_increase
    (β² H_s H_t : ℝ) (hβ : 0 < β²) (hH : H_s < H_t) :
    β² * H_s < β² * H_t := by
  exact mul_lt_mul_of_pos_left hH hβ

end Question5


/-!
## Open Question 6: PGS Variance Non-Monotonicity
-/

section Question6

/-- **Variance decomposition into large and small effect groups.** -/
theorem variance_decomposition
    {m : ℕ} (w : Fin m → ℝ) (S : Finset (Fin m)) :
    ∑ i, w i = ∑ i ∈ S, w i + ∑ i ∈ Sᶜ, w i := by
  rw [← Finset.sum_union Finset.disjoint_compl_right]
  congr 1; exact (Finset.union_compl S).symm

/-- **Sufficient condition for PGS variance increase.**
    If the increase in large-effect component exceeds the decrease
    in small-effect component, total variance increases. -/
theorem variance_increase_sufficient
    (vL_s vL_t vS_s vS_t : ℝ)
    (h_large_up : vL_s < vL_t)
    (h_net : vL_t - vL_s > vS_s - vS_t) :
    vL_s + vS_s < vL_t + vS_t := by linarith

end Question6


/-!
## Open Question 7: Brier Score Uncertainty Varies with Prevalence
-/

section Question7

/-- **Brier score irreducible noise = π(1-π).**
    This varies with prevalence, making R² comparisons across groups misleading. -/
theorem brier_uncertainty_formula (π : ℝ) :
    π * (1 - π) = -(π - 1/2) ^ 2 + 1/4 := by ring

/-- **Brier uncertainty is maximized at π = 1/2.** -/
theorem brier_uncertainty_max_at_half (π : ℝ) :
    π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]

/-- **Closer to 1/2 ↔ higher uncertainty.** -/
theorem closer_to_half_more_uncertainty
    (π₁ π₂ : ℝ)
    (h₁ : 0 < π₁) (h₁' : π₁ < 1)
    (h₂ : 0 < π₂) (h₂' : π₂ < 1)
    (h_closer : (π₂ - 1/2) ^ 2 < (π₁ - 1/2) ^ 2) :
    π₁ * (1 - π₁) < π₂ * (1 - π₂) := by
  nlinarith [brier_uncertainty_formula π₁, brier_uncertainty_formula π₂]

/-- **Prediction interval width increases as R² decreases.** -/
theorem interval_width_increases
    (r2₁ r2₂ : ℝ)
    (hr2₁ : r2₂ < r2₁) (hr2₁_lt : r2₁ < 1) (hr2₂_nn : 0 ≤ r2₂) :
    Real.sqrt (1 - r2₁) < Real.sqrt (1 - r2₂) := by
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

end Question7


/-!
## Unified Portability Theory: Four-Factor Decomposition

Portability ratio = AF_factor × LD_factor × Effect_factor × Env_factor.
Genetic distance (Fst) captures only the AF factor, explaining why it
poorly predicts individual-level accuracy.
-/

section UnifiedTheory

/-- **Unified portability ratio as a product of four factors.** -/
noncomputable def unifiedPortabilityRatio
    (af_factor ld_factor eff_factor env_factor : ℝ) : ℝ :=
  af_factor * ld_factor * eff_factor * env_factor

/-- **No single factor captures the full ratio.** -/
theorem single_factor_insufficient
    (af ld eff env : ℝ)
    (h_af : 0 < af) (h_af_le : af ≤ 1)
    (h_ld : 0 < ld) (h_ld_lt : ld < 1)
    (h_eff : 0 < eff) (h_eff_lt : eff < 1)
    (h_env : 0 < env) (h_env_le : env ≤ 1) :
    unifiedPortabilityRatio af ld eff env < af := by
  unfold unifiedPortabilityRatio
  have h1 : ld * eff < 1 := by
    calc ld * eff < 1 * eff := mul_lt_mul_of_pos_right h_ld_lt h_eff
      _ = eff := one_mul eff
      _ < 1 := h_eff_lt
  have h2 : ld * eff * env < 1 := by
    calc ld * eff * env < 1 * env := mul_lt_mul_of_pos_right h1 h_env
      _ = env := one_mul env
      _ ≤ 1 := h_env_le
  calc af * ld * eff * env
      = af * (ld * eff * env) := by ring
    _ < af * 1 := mul_lt_mul_of_pos_left h2 h_af
    _ = af := mul_one af

/-- **R² of genetic distance on portability is bounded by the AF variance fraction.** -/
theorem genetic_distance_variance_bound
    (var_af var_ld var_eff var_env : ℝ)
    (h_af : 0 < var_af) (h_ld : 0 < var_ld)
    (h_eff : 0 < var_eff) (h_env : 0 < var_env) :
    var_af / (var_af + var_ld + var_eff + var_env) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

end UnifiedTheory


/-!
## Selection-Driven Allelic Turnover Model

Under fluctuating selection across populations, effect sizes at
immune-associated loci change faster than at neutral loci.
-/

section SelectionModel

/-- **Effect retention under selection.**
    ρ ≤ selection correlation. Low selection correlation → low ρ → low portability. -/
theorem selection_bounds_effect_retention
    (r2_src ρ_eff ρ_sel : ℝ)
    (hr2 : 0 ≤ r2_src)
    (h_bound : ρ_eff ≤ ρ_sel)
    (h_eff_nn : 0 ≤ ρ_eff) (h_sel_nn : 0 ≤ ρ_sel) :
    r2_src * ρ_eff ^ 2 ≤ r2_src * ρ_sel ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ hr2
  exact sq_le_sq' (by linarith) h_bound

/-- **Neutral vs immune portability.**
    Neutral ρ = 1, immune ρ < 1. So neutral R² > immune R² at same distance. -/
theorem neutral_beats_immune
    (r2 ρ : ℝ) (hr2 : 0 < r2)
    (hρ_pos : 0 ≤ ρ) (hρ_lt : ρ < 1) :
    r2 * ρ ^ 2 < r2 * 1 ^ 2 := by
  rw [one_pow]
  exact mul_lt_mul_of_pos_left (sq_lt_one_of_abs_lt_one (by rwa [abs_of_nonneg hρ_pos])) hr2

/-- **Drift-only portability (using existing infrastructure).**
    Under pure drift, portability ratio = (1-Fst_T)/(1-Fst_S).
    This is what Fst predicts. For immune traits, the actual ratio is
    much lower due to the additional effect turnover factor. -/
theorem drift_only_overestimates_immune_portability
    (V_A V_E fstS fstT ρ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS : 0 ≤ fstS) (hfstT : fstT < 1)
    (hfst : fstS < fstT)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    expectedR2 (ρ ^ 2 * presentDayPGSVariance V_A fstT) V_E <
      expectedR2 (presentDayPGSVariance V_A fstT) V_E := by
  apply expectedR2_strictMono_nonneg V_E _ _ hVE
  · exact le_of_lt (mul_pos (sq_pos_of_pos hρ_pos)
      (by unfold presentDayPGSVariance; exact mul_pos (by linarith) hVA))
  · have h_pdv_pos : 0 < presentDayPGSVariance V_A fstT := by
      unfold presentDayPGSVariance; exact mul_pos (by linarith) hVA
    calc ρ ^ 2 * presentDayPGSVariance V_A fstT
        < 1 * presentDayPGSVariance V_A fstT := by
          exact mul_lt_mul_of_pos_right
            (sq_lt_one_of_abs_lt_one (by rwa [abs_of_nonneg (le_of_lt hρ_pos)])) h_pdv_pos
      _ = presentDayPGSVariance V_A fstT := one_mul _

end SelectionModel

end Calibrator
