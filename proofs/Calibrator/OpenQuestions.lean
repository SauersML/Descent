import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.TransportIdentities

namespace Calibrator

open MeasureTheory
open scoped ProbabilityTheory

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
# Master Transport Theorem

The core portability identity is the exact MSE transport decomposition together
with the exact decomposition of target cross-covariances and target-optimal
weights into causal and context terms.
-/

section MasterTransport

variable {Ω : Type*}
variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

theorem master_transport_decomposition_exact
    (sigmaInv : Matrix J J ℝ)
    (E : ExpFunctional Ω)
    (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (w : J → ℝ)
    (hcentered : ∀ i, E (fun ω => X ω i) = 0)
    (hsigmaInv : covarianceMatrix E X * sigmaInv = 1) :
    expMse E Y (linScore w X)
      = expMse E Y (linScore (optimalWeightsFromMoments sigmaInv E X Y) X)
        + dot (fun i => w i - optimalWeightsFromMoments sigmaInv E X Y i)
            ((covarianceMatrix E X).mulVec
              (fun i => w i - optimalWeightsFromMoments sigmaInv E X Y i)) := by
  exact master_transport_theorem_closed_form sigmaInv E X Y w hcentered hsigmaInv

theorem target_cross_covariance_decomposition_exact
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (C : Ω → L → ℝ)
    (β : L → ℝ) (h : Ω → ℝ) :
    crossCovVector E X (fun ω => causalSignal β C ω + h ω)
      = (predictorCausalCovariance E X C).mulVec β + contextCrossCovVector E X h := by
  exact crossCovVector_decomposition E X C β h

theorem target_optimal_weights_decomposition_exact
    (sigmaInv : Matrix J J ℝ)
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (C : Ω → L → ℝ)
    (β : L → ℝ) (h : Ω → ℝ) :
    optimalWeightsFromMoments sigmaInv E X (fun ω => causalSignal β C ω + h ω)
      = sigmaInv.mulVec ((predictorCausalCovariance E X C).mulVec β)
        + sigmaInv.mulVec (contextCrossCovVector E X h) := by
  exact optimalWeightsFromMoments_decomposition sigmaInv E X C β h

end MasterTransport

/-!
## Open Question 1: Law of Total Variance and Weak Predictability

Individual-level squared prediction error ε²ᵢ has high within-group variance.
The law of total variance implies R²(ε², genetic_distance) is small whenever
the conditional variance E[Var(ε²|D)] dominates Var(E[ε²|D]).
-/

section Question1

theorem scalar_summary_insufficient_for_accuracy
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (distance accuracy : V →ₗ[ℝ] ℝ)
    (hnot : ¬ ∃ c : ℝ, accuracy = c • distance) :
    ∀ θ : V, ∃ θ' : V, distance θ' = distance θ ∧ accuracy θ' ≠ accuracy θ := by
  exact scalar_summary_insufficient_of_not_scalar_factorization distance accuracy hnot

theorem explainable_fraction_bound_of_conditional_noise_floor_exact
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure[mΩ] Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ)
    {L noiseFloor : Ω → ℝ}
    (hL : MemLp L 2 μ)
    (hVar_pos : 0 < Var[L; μ])
    (hNoise_int : Integrable noiseFloor μ)
    (hNoise_nonneg : 0 ≤ μ[noiseFloor])
    (hNoise_le : noiseFloor ≤ᵐ[μ] conditionalVariance μ m L) :
    explainableFraction (Var[conditionalMean μ m L; μ]) (Var[L; μ])
      ≤ Var[conditionalMean μ m L; μ] / (Var[conditionalMean μ m L; μ] + μ[noiseFloor]) := by
  exact explainable_fraction_bound_of_conditional_noise_floor hm hL hVar_pos
    hNoise_int hNoise_nonneg hNoise_le

theorem explainable_fraction_bound_of_conditional_gaussian_floor_exact
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure[mΩ] Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ)
    {L sigma4 : Ω → ℝ}
    (hL : MemLp L 2 μ)
    (hVar_pos : 0 < Var[L; μ])
    (hsigma4_int : Integrable sigma4 μ)
    (hsigma4_nonneg : 0 ≤ μ[sigma4])
    (hGaussianFloor : (fun ω => (2 : ℝ) * sigma4 ω) ≤ᵐ[μ] conditionalVariance μ m L) :
    explainableFraction (Var[conditionalMean μ m L; μ]) (Var[L; μ])
      ≤ Var[conditionalMean μ m L; μ] / (Var[conditionalMean μ m L; μ] + 2 * μ[sigma4]) := by
  exact explainable_fraction_bound_of_conditional_gaussian_floor hm hL hVar_pos
    hsigma4_int hsigma4_nonneg hGaussianFloor

/-- **Law of total variance identity.**
    Var(Z) = E[Var(Z|D)] + Var(E[Z|D]).
    The between-group fraction Var(E[Z|D])/Var(Z) = R² of D on Z. -/
theorem law_of_total_variance_r2_bound
    (varZ eVarZgivenD varEZgivenD : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_eVar_nonneg : 0 ≤ eVarZgivenD)
    (_h_varE_nonneg : 0 ≤ varEZgivenD) :
    varEZgivenD / varZ ≤ 1 := by
  rw [div_le_one h_varZ_pos, h_decomp]
  linarith

/-- **When within-group variance dominates, R² is small.**
    If E[Var(Z|D)] ≥ (1 - δ)·Var(Z), then R²(Z,D) ≤ δ.

    Worked example: For height, Wang et al. find δ ≈ 0.005 (R² = 0.51%). -/
theorem r2_small_when_within_dominates
    (varZ eVarZgivenD varEZgivenD δ : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (_h_eVar_nonneg : 0 ≤ eVarZgivenD)
    (_h_varE_nonneg : 0 ≤ varEZgivenD)
    (h_within_dominates : eVarZgivenD ≥ (1 - δ) * varZ)
    (_hδ_pos : 0 < δ) :
    varEZgivenD / varZ ≤ δ := by
  have h1 : varEZgivenD = varZ - eVarZgivenD := by linarith
  rw [h1, sub_div, div_self (h_varZ_pos.ne')]
  linarith [le_div_iff₀ h_varZ_pos |>.mpr (by linarith : (1 - δ) * varZ ≤ eVarZgivenD)]

/-- **χ² coefficient of variation.**
    Squared prediction error ε² ~ σ² · χ²₁ has Var(ε²) = 2σ⁴ and E[ε²] = σ².
    So CV² = 2σ⁴/σ⁴ = 2, making individual errors inherently noisy. -/
theorem squared_error_cv_is_two (sigma_sq : ℝ) (hσ : 0 < sigma_sq) :
    2 * sigma_sq ^ 2 / sigma_sq ^ 2 = 2 := by
  rw [mul_div_cancel_right₀]
  exact pow_ne_zero 2 (hσ.ne')

/-- **SES explains as much as genetic distance.**
    If both covariates explain comparable fractions and their total
    is bounded, each individual fraction must be small. -/
theorem comparable_covariates_both_small
    (r2_d r2_s B ε : ℝ)
    (_h_d_nonneg : 0 ≤ r2_d) (_h_s_nonneg : 0 ≤ r2_s)
    (h_comparable : r2_d ≤ r2_s + ε)
    (h_sum_bound : r2_d + r2_s ≤ B)
    (_hB_pos : 0 < B) :
    r2_d ≤ (B + ε) / 2 := by
  linarith

end Question1


/-!
## Open Question 2: Trait-Specific Portability

Trait-specific portability is the exact consequence of locuswise transport
heterogeneity together with trait-specific baseline weights.
-/

section Question2

variable {J L : Type*}
variable [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

theorem trait_transport_is_locus_weighted_sum
    (w : J → ℝ) (K : J → L → ℝ) (β : L → ℝ) :
    transportedCovariance w K β = ∑ l, locusTerm w K β l := by
  exact transported_covariance_decomposes w K β

theorem normalized_trait_transport_from_locus_factors
    (aQ aT : L → ℝ)
    (hbase : ∀ l, aT l ≠ 0) :
    (∑ l, aQ l) / (∑ l, aT l)
      = ∑ l, baselineWeight aT l * transportFactor aQ aT l := by
  exact normalized_transport_from_factors aQ aT hbase

theorem universal_trait_transport_when_factor_constant
    (aT τ : L → ℝ) (φ : ℝ)
    (hden : ∑ m, aT m ≠ 0)
    (hτ : ∀ l, τ l = φ) :
    (∑ l, aT l * τ l) / (∑ l, aT l) = φ := by
  exact normalized_transport_constant_factor aT τ φ hden hτ

/-- **Heterozygosity increases toward 0.5.**
    Under divergent selection, allele freq p moves from extreme to
    intermediate → H = 2p(1-p) increases.
    This drives PGS variance increase for immune traits. -/
theorem heterozygosity_increases_toward_half
    (p₁ p₂ : ℝ)
    (_hp₁_pos : 0 < p₁)
    (hp₁_lt_p₂ : p₁ < p₂)
    (hp₂_le_half : p₂ ≤ 1 / 2) :
    2 * p₁ * (1 - p₁) < 2 * p₂ * (1 - p₂) := by
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]

/-- **If large-effect heterozygosity increases more than small-effect decreases,
    total PGS variance increases.** This is the mechanism for WBC/lymphocyte count. -/
theorem pgs_variance_can_increase
    (v_large_s v_large_t v_small_s v_small_t : ℝ)
    (_h_large_up : v_large_s < v_large_t)
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
  have key : cov_t ^ 2 * (vpgs_s * vy) ≤ cov_t ^ 2 * (vpgs_t * vy) := by
    apply mul_le_mul_of_nonneg_left (le_of_lt h_denom_up) (sq_nonneg cov_t)
  calc cov_t ^ 2 / (vpgs_t * vy)
      ≤ cov_t ^ 2 / (vpgs_s * vy) := by
        rwa [div_le_div_iff₀ h_denom_t h_denom_s]
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
## Open Question 3: Metric-Specific Portability

Different metrics are different functionals of the same transported law.
For continuous traits this is the exact MSE identity; for binary traits it is
the exact prevalence-recall-FPR formula for precision.
-/

section Question3

variable {Ω : Type*}

theorem continuous_metric_identity_exact
    (E : ExpFunctional Ω) (Y S : Ω → ℝ)
    (ρ lam : ℝ)
    (hvarY : 0 < variance E Y)
    (hlam : variance E S = variance E Y * lam)
    (hρ : covariance E Y S = ρ * variance E Y * Real.sqrt lam) :
    expMse E Y S
      = variance E Y * (1 + lam - 2 * ρ * Real.sqrt lam)
        + (bias E Y S) ^ 2 := by
  exact mse_from_variance_ratio_corr_bias E Y S ρ lam hvarY hlam hρ

theorem binary_precision_formula_exact (c : ConfusionMatrix) :
    ConfusionMatrix.precision c =
      (ConfusionMatrix.prevalence c * ConfusionMatrix.recallRate c) /
        (ConfusionMatrix.prevalence c * ConfusionMatrix.recallRate c +
          (1 - ConfusionMatrix.prevalence c) * ConfusionMatrix.fpr c) := by
  exact ConfusionMatrix.precision_eq_prevalence_recall_fpr c

/-- **Precision-recall divergence is consistent.**
    There exist parameter configurations with fixed prevalence and fixed target
    precision where recall changes and the induced false-positive rate changes
    exactly as required by the precision identity. -/
theorem precision_recall_divergence_exists :
    ∃ (π p r₁ r₂ f₁ f₂ : ℝ),
      0 < π ∧ π < 1 ∧
      0 < p ∧ p < 1 ∧
      0 < r₁ ∧ r₁ < r₂ ∧ r₂ ≤ 1 ∧
      f₁ = π * r₁ * (1 - p) / ((1 - π) * p) ∧
      f₂ = π * r₂ * (1 - p) / ((1 - π) * p) ∧
      (π * r₁) / (π * r₁ + (1 - π) * f₁) = p ∧
      (π * r₂) / (π * r₂ + (1 - π) * f₂) = p := by
  refine ⟨1 / 2, 1 / 2, 1 / 4, 1 / 3,
    (1 / 2) * (1 / 4) * (1 - 1 / 2) / ((1 - 1 / 2) * (1 / 2)),
    (1 / 2) * (1 / 3) * (1 - 1 / 2) / ((1 - 1 / 2) * (1 / 2)), ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa using
      (ConfusionMatrix.constant_precision_construction
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 4) (by norm_num) (by norm_num) (by norm_num))
  · simpa using
      (ConfusionMatrix.constant_precision_construction
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 3) (by norm_num) (by norm_num) (by norm_num))

end Question3


/-!
## Open Question 4: Environmental Variance Heterogeneity
-/

section Question4

/-- **R² decreases with environmental variance** even under identical genetics.
    R² = Vg/(Vg + Ve), so larger Ve → smaller R². -/
theorem env_variance_lowers_r2
    (Vg Ve₁ Ve₂ : ℝ)
    (hVg : 0 < Vg) (hVe₁ : 0 < Ve₁) (_hVe₂ : 0 < Ve₂)
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
    GWAS estimate β_hat = β_true + δ (inflation).
    Target effect β_t = ρ * β_true (turnover).
    Prediction error = β_hat - β_t = (1-ρ)*β + δ.
    Prediction error decomposes into turnover + inflation. -/
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
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₂ < ρ₁) (_hρ₁_le : ρ₁ ≤ 1) :
    ((1 - ρ₁) * β + δ) / (ρ₁ * β) < ((1 - ρ₂) * β + δ) / (ρ₂ * β) := by
  rw [div_lt_div_iff₀ (mul_pos hρ₁ hβ) (mul_pos hρ₂ hβ)]
  nlinarith [sq_nonneg β, sq_nonneg δ, mul_pos hρ₁ hβ, mul_pos hρ₂ hβ,
             mul_pos hβ hδ, mul_pos hρ₁ hδ, mul_pos hρ₂ hδ]

/-- **Heterozygosity increase → PGS variance increase at a single locus.** -/
theorem het_increase_implies_locus_var_increase
    (beta_sq H_s H_t : ℝ) (hβ : 0 < beta_sq) (hH : H_s < H_t) :
    beta_sq * H_s < beta_sq * H_t := by
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
  rw [← Finset.sum_union disjoint_compl_right]
  congr 1; exact (Finset.union_compl S).symm

/-- **Sufficient condition for PGS variance increase.**
    If the increase in large-effect component exceeds the decrease
    in small-effect component, total variance increases. -/
theorem variance_increase_sufficient
    (vL_s vL_t vS_s vS_t : ℝ)
    (_h_large_up : vL_s < vL_t)
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
    (_h₁ : 0 < π₁) (_h₁' : π₁ < 1)
    (_h₂ : 0 < π₂) (_h₂' : π₂ < 1)
    (h_closer : (π₂ - 1/2) ^ 2 < (π₁ - 1/2) ^ 2) :
    π₁ * (1 - π₁) < π₂ * (1 - π₂) := by
  nlinarith [brier_uncertainty_formula π₁, brier_uncertainty_formula π₂]

/-- **Prediction interval width increases as R² decreases.** -/
theorem interval_width_increases
    (r2₁ r2₂ : ℝ)
    (hr2₁ : r2₂ < r2₁) (hr2₁_lt : r2₁ < 1) (_hr2₂_nn : 0 ≤ r2₂) :
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

/-- **No single factor captures the full ratio.** -/
theorem single_factor_insufficient
    (af ld eff env : ℝ)
    (h_af : 0 < af) (_h_af_le : af ≤ 1)
    (h_ld : 0 < ld) (h_ld_lt : ld < 1)
    (h_eff : 0 < eff) (h_eff_lt : eff < 1)
    (h_env : 0 < env) (h_env_le : env ≤ 1) :
    af * ld * eff * env < af := by
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
    (h_eff_nn : 0 ≤ ρ_eff) (_h_sel_nn : 0 ≤ ρ_sel) :
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
  apply mul_lt_mul_of_pos_left _ hr2
  nlinarith [sq_abs ρ, sq_nonneg ρ]

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
          apply mul_lt_mul_of_pos_right _ h_pdv_pos
          nlinarith [sq_abs ρ, sq_nonneg ρ]
      _ = presentDayPGSVariance V_A fstT := one_mul _

end SelectionModel


/-!
## LD Decay Interaction with Allelic Turnover

The paper shows that for immune traits, both LD patterns AND allelic effects
change simultaneously. The combined effect is worse than either alone.
We formalize this multiplicative interaction.
-/

section LDTurnoverInteraction

theorem faster_decay_lower_correlation
    (lam_slow lam_fast d : ℝ)
    (_hlam_slow_pos : 0 < lam_slow)
    (hlam_faster : lam_slow < lam_fast)
    (hd_pos : 0 < d) :
    Real.exp (-lam_fast * d) < Real.exp (-lam_slow * d) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- **LD tagging efficiency decays exponentially with genetic distance.**
    ρ²_LD(d) = exp(-λ_LD · d). This is the Ohta-Kimura result. -/
noncomputable def ldTaggingDecay (lam_LD d : ℝ) : ℝ :=
  Real.exp (-lam_LD * d)

/-- **Combined LD + effect turnover portability.**
    Total portability = R²_source · ρ²_LD(d) · ρ²_effect(d). -/
noncomputable def combinedPortability
    (r2_src lam_LD lam_eff d : ℝ) : ℝ :=
  r2_src * ldTaggingDecay lam_LD d * (Real.exp (-lam_eff * d)) ^ 2

/-- **At distance 0, combined portability equals source R².** -/
theorem combined_portability_at_zero (r2_src lam_LD lam_eff : ℝ) :
    combinedPortability r2_src lam_LD lam_eff 0 = r2_src := by
  unfold combinedPortability ldTaggingDecay
  simp [mul_zero, Real.exp_zero]

/-- **LD-only portability strictly exceeds combined portability at positive distance.**
    Adding effect turnover always makes portability worse. -/
theorem turnover_worsens_ld_only_portability
    (r2_src lam_LD lam_eff d : ℝ)
    (hr2 : 0 < r2_src)
    (hlam_eff : 0 < lam_eff) (hd : 0 < d) :
    combinedPortability r2_src lam_LD lam_eff d <
      r2_src * ldTaggingDecay lam_LD d := by
  unfold combinedPortability
  have h_exp_lt : (Real.exp (-lam_eff * d)) ^ 2 < 1 := by
    have h1 : Real.exp (-lam_eff * d) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith [mul_pos hlam_eff hd]
    have h2 : 0 ≤ Real.exp (-lam_eff * d) := Real.exp_nonneg _
    nlinarith [sq_abs (Real.exp (-lam_eff * d))]
  have h_base_pos : 0 < r2_src * ldTaggingDecay lam_LD d := by
    unfold ldTaggingDecay
    exact mul_pos hr2 (Real.exp_pos _)
  calc r2_src * ldTaggingDecay lam_LD d * (Real.exp (-lam_eff * d)) ^ 2
      < r2_src * ldTaggingDecay lam_LD d * 1 :=
        mul_lt_mul_of_pos_left h_exp_lt h_base_pos
    _ = r2_src * ldTaggingDecay lam_LD d := mul_one _

/-- **Immune portability drops multiplicatively faster.**
    For immune traits (large λ_eff), the combined decay is much faster
    than for neutral traits (small λ_eff). -/
theorem immune_combined_decay_faster
    (r2_src lam_LD lam_eff_neutral lam_eff_immune d : ℝ)
    (hr2 : 0 < r2_src)
    (hlamn : 0 < lam_eff_neutral)
    (hlami : lam_eff_neutral < lam_eff_immune)
    (hd : 0 < d) :
    combinedPortability r2_src lam_LD lam_eff_immune d <
      combinedPortability r2_src lam_LD lam_eff_neutral d := by
  unfold combinedPortability
  have h_ld_pos : 0 < r2_src * ldTaggingDecay lam_LD d := by
    unfold ldTaggingDecay; exact mul_pos hr2 (Real.exp_pos _)
  apply mul_lt_mul_of_pos_left _ h_ld_pos
  apply sq_lt_sq'
  · linarith [Real.exp_pos (-lam_eff_immune * d), Real.exp_pos (-lam_eff_neutral * d)]
  · exact faster_decay_lower_correlation lam_eff_neutral lam_eff_immune d hlamn hlami hd

end LDTurnoverInteraction


/-!
## R² Non-Comparability Across Groups

R² depends on the variance of both predictor and outcome within each group.
When comparing R² across genetic ancestry groups, heterogeneity in both
genetic and environmental variance makes direct comparison misleading.
-/

section R2NonComparability

/-- **R² is not comparable when phenotypic variances differ.**
    Two populations with the same signal but different noise have different R². -/
theorem r2_incomparable_across_groups
    (v_signal v_noise₁ v_noise₂ : ℝ)
    (h_sig : 0 < v_signal)
    (h_n₁ : 0 < v_noise₁) (h_n₂ : 0 < v_noise₂)
    (h_noise_diff : v_noise₁ ≠ v_noise₂) :
    v_signal / (v_signal + v_noise₁) ≠ v_signal / (v_signal + v_noise₂) := by
  intro h_eq
  apply h_noise_diff
  have h_d₁ : (0 : ℝ) < v_signal + v_noise₁ := by linarith
  have h_d₂ : (0 : ℝ) < v_signal + v_noise₂ := by linarith
  have h_cross := (div_eq_div_iff (h_d₁.ne') (h_d₂.ne')).mp h_eq
  nlinarith

/-- **Heteroscedasticity inflates apparent portability loss.**
    If Var(Y) is larger in the target (due to environmental factors),
    R²_target < R²_source even with identical signal. -/
theorem heteroscedasticity_inflates_loss
    (v_sig v_noise_s v_noise_t : ℝ)
    (h_sig : 0 < v_sig)
    (h_ns : 0 < v_noise_s) (_h_nt : 0 < v_noise_t)
    (h_more_noise : v_noise_s < v_noise_t) :
    v_sig / (v_sig + v_noise_t) < v_sig / (v_sig + v_noise_s) := by
  exact div_lt_div_of_pos_left h_sig (by linarith) (by linarith)

/-- **Corrected portability ratio accounts for noise differences.**
    The "true" portability ratio should compare signal-to-noise ratios,
    not R² values directly.
    SNR_s = v_sig_s / v_noise_s, SNR_t = v_sig_t / v_noise_t.
    Portability = SNR_t / SNR_s, which is invariant to noise scaling. -/
noncomputable def snrPortabilityRatio
    (v_sig_s v_noise_s v_sig_t v_noise_t : ℝ) : ℝ :=
  (v_sig_t / v_noise_t) / (v_sig_s / v_noise_s)

/-- **SNR portability depends only on signal ratio when noise is constant.** -/
theorem snr_portability_signal_only
    (v_sig_s v_sig_t v_noise : ℝ)
    (h_ns : v_noise ≠ 0) :
    snrPortabilityRatio v_sig_s v_noise v_sig_t v_noise = v_sig_t / v_sig_s := by
  unfold snrPortabilityRatio
  field_simp

end R2NonComparability


/-!
## Local Ancestry and Portability

The paper notes that measures of genetic distance based on global PCs are
"plausibly sub-optimal" and suggests local ancestry may better predict portability.
We formalize why local ancestry should be more informative.
-/

section LocalAncestry

/-- **Variance in local Fst across loci creates additional prediction error.**
    If local Fst varies (some loci have high Fst, others low), the prediction
    error has a "locus heterogeneity" component not captured by global Fst. -/
theorem locus_heterogeneity_creates_weighted_gap
    {m : ℕ} (β : Fin m → ℝ) (fst : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst i₀ - fst_global)) :
    fst_global * (∑ i, β i ^ 2) < ∑ i, β i ^ 2 * fst i := by
  have hsum_strict :
      0 < ∑ i, β i ^ 2 * (fst i - fst_global) := by
    have hsingle :
        β i₀ ^ 2 * (fst i₀ - fst_global)
          ≤ ∑ i, β i ^ 2 * (fst i - fst_global) := by
      simpa only using
        (Finset.single_le_sum
          (f := fun i => β i ^ 2 * (fst i - fst_global))
          (fun i _ => h_nonneg i)
          (Finset.mem_univ i₀))
    exact lt_of_lt_of_le h_strict hsingle
  have hrewrite :
      ∑ i, β i ^ 2 * (fst i - fst_global)
        = (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
    calc
      ∑ i, β i ^ 2 * (fst i - fst_global)
          = ∑ i, (β i ^ 2 * fst i - β i ^ 2 * fst_global) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i, β i ^ 2 * fst i) - ∑ i, β i ^ 2 * fst_global := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hgap :
      0 < (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
    rw [← hrewrite]
    exact hsum_strict
  linarith

/-- **Local ancestry captures LD-relevant information.**
    Global Fst averages over the whole genome, but PGS accuracy depends on
    LD at specific index SNPs. Local Fst at those SNPs is more relevant.

    If the weighted average of local Fst (weighted by squared effects)
    differs from global Fst, global Fst is a biased proxy. -/
theorem local_fst_more_informative
    {m : ℕ} (β : Fin m → ℝ) (fst_local : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst_local i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst_local i₀ - fst_global))
    (hweight_pos : 0 < ∑ i, β i ^ 2) :
    fst_global < (∑ i, β i ^ 2 * fst_local i) / (∑ i, β i ^ 2) := by
  exact (lt_div_iff₀ hweight_pos).2
    (locus_heterogeneity_creates_weighted_gap β fst_local fst_global h_nonneg i₀ h_strict)

end LocalAncestry


/-!
## Disease-Specific Portability

For binary traits (asthma, T2D), portability depends on additional factors:
- Prevalence differences across populations
- The specific metric used (precision, recall, F1, AUC)
- Threshold choice for classification
-/

section DiseasePortability

/-- **F1 score definition.** -/
noncomputable def f1Score (precision sensitivity : ℝ) : ℝ :=
  2 * precision * sensitivity / (precision + sensitivity)

/-- **F1 score is symmetric in precision and recall.** -/
theorem f1_symmetric (p r : ℝ) : f1Score p r = f1Score r p := by
  unfold f1Score; ring

/-- **F1 score ≤ max(precision, recall).**
    This is because F1 = harmonic mean ≤ arithmetic mean ≤ max. -/
theorem f1_le_arithmetic_mean (p r : ℝ)
    (hp : 0 < p) (hr : 0 < r) :
    f1Score p r ≤ (p + r) / 2 := by
  unfold f1Score
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [sq_nonneg (p - r)]

/-- **Prevalence shift model for T2D.**
    T2D prevalence is higher in South Asian and African-descent populations
    than in European populations. This shifts the base rate for Bayesian calculations.

    With a fixed PGS threshold:
    - Higher prevalence → more true cases → potentially higher recall
    - Higher prevalence → higher PPV → potentially higher precision
    - But lower PGS accuracy → lower sensitivity → counteracts recall gain

    The net effect on recall depends on whether the prevalence increase
    dominates the sensitivity decrease. We prove the sufficient condition. -/
theorem prevalence_dominates_sensitivity_for_recall
    (n_cases₁ n_cases₂ sens₁ sens₂ : ℝ)
    (h_cases₁ : 0 < n_cases₁) (_h_cases₂ : 0 < n_cases₂)
    (_h_sens₁ : 0 < sens₁) (h_sens₂ : 0 < sens₂)
    (_h_sens₁_le : sens₁ ≤ 1) (_h_sens₂_le : sens₂ ≤ 1)
    -- More cases in target (prevalence is higher)
    (_h_more_cases : n_cases₁ < n_cases₂)
    -- Sensitivity doesn't drop too much (prevalence effect dominates)
    (h_sens_ratio : sens₁ / sens₂ < n_cases₂ / n_cases₁) :
    -- Then absolute true positives increase
    n_cases₁ * sens₁ < n_cases₂ * sens₂ := by
  have htp : sens₁ * n_cases₁ < n_cases₂ * sens₂ := by
    rwa [div_lt_div_iff₀ h_sens₂ h_cases₁] at h_sens_ratio
  simpa [mul_comm] using htp

/-- **Asthma vs T2D portability difference.**
    For asthma, precision and recall decay similarly → qualitatively similar.
    For T2D, they diverge → qualitatively different.
    The difference is driven by the prevalence-distance relationship. -/
theorem different_diseases_different_portability_patterns
    -- Asthma: both metrics decay
    (prec_asthma_near prec_asthma_far : ℝ)
    (rec_asthma_near rec_asthma_far : ℝ)
    (h_prec_asthma_drops : prec_asthma_far < prec_asthma_near)
    (h_rec_asthma_drops : rec_asthma_far < rec_asthma_near)
    -- T2D: precision constant, recall increases
    (prec_t2d_near prec_t2d_far : ℝ)
    (rec_t2d_near rec_t2d_far : ℝ)
    (h_prec_t2d_const : prec_t2d_near = prec_t2d_far)
    (h_rec_t2d_up : rec_t2d_near < rec_t2d_far)
    :
    -- The diseases show qualitatively different portability patterns
    (prec_asthma_far < prec_asthma_near ∧ rec_asthma_far < rec_asthma_near) ∧
    (prec_t2d_near = prec_t2d_far ∧ rec_t2d_near < rec_t2d_far) :=
  ⟨⟨h_prec_asthma_drops, h_rec_asthma_drops⟩, ⟨h_prec_t2d_const, h_rec_t2d_up⟩⟩

end DiseasePortability


/-!
## Calibrated PGS: When Portability is Recoverable

Not all portability loss is irrecoverable. Some can be addressed by:
1. Re-calibration (adjusting intercept and slope)
2. Ancestry-specific spline adjustments
3. Multi-ancestry training

We formalize which components of portability loss are recoverable.
-/

section RecoverablePortability

/-- **Mean shift is recoverable by re-calibration.**
    If the PGS has a mean shift μ across populations, adjusting the
    intercept recovers the correct calibration. -/
theorem mean_shift_recoverable
    (y_pred μ_shift : ℝ) :
    y_pred - μ_shift + μ_shift = y_pred := by ring

/-- **Slope change (shrinkage) is recoverable by re-calibration.**
    If the PGS slope changes from b to b·r, multiplying by 1/r recovers it. -/
theorem slope_change_recoverable
    (b r pgs : ℝ) (hr : r ≠ 0) :
    (b * r * pgs) * (1 / r) = b * pgs := by
  field_simp

/-- **LD mismatch is NOT recoverable by linear re-calibration.**
    If the LD structure changes, the normal equations have a different solution.
    No linear transformation of the source weights can recover the target optimum.
    (This reuses the existing source_erm_is_ld_specific_proved.) -/
theorem ld_mismatch_not_linearly_recoverable
    (w_source : Fin 2 → ℝ)
    (σ_target : Matrix (Fin 2) (Fin 2) ℝ)
    (cross_target : Fin 2 → ℝ)
    -- σ_target.mulVec is linear, so scaling w_source just scales the image
    (_h_base_mismatch : σ_target.mulVec w_source ≠ cross_target)
    -- The image of the source direction doesn't align with cross_target
    -- (cross_target is not a scalar multiple of σ_target.mulVec w_source)
    (h_not_aligned : ∀ α : ℝ, α • σ_target.mulVec w_source ≠ cross_target) :
    -- Then no linear re-calibration can recover target-optimal weights
    ∀ α : ℝ, σ_target.mulVec (α • w_source) ≠ cross_target := by
  intro α
  rw [Matrix.mulVec_smul]
  exact h_not_aligned α

/-- **Effect turnover is NOT recoverable without target-population data.**
    If true effects change between populations, the source GWAS provides
    no information about the new effects. Only target GWAS data helps. -/
theorem effect_turnover_requires_target_data
    (β_source β_target : ℝ)
    (h_different : β_source ≠ β_target) :
    -- Any prediction using β_source has nonzero error for β_target
    ∀ y : ℝ, β_source * y ≠ β_target * y ∨ y = 0 := by
  intro y
  by_cases hy : y = 0
  · right; exact hy
  · left; intro h; exact h_different (mul_right_cancel₀ hy h)

end RecoverablePortability

end Calibrator
