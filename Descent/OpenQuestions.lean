/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PortabilityDrift

namespace Descent

open MeasureTheory
open scoped ProbabilityTheory
open TransportedMetrics (r2FromSignalVariance)

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

theorem scalar_summary_insufficient_for_accuracy
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (distance accuracy : V →ₗ[ℝ] ℝ)
    (hnot : ¬ ∃ c : ℝ, accuracy = c • distance) :
    ∀ θ : V, ∃ θ' : V, distance θ' = distance θ ∧ accuracy θ' ≠ accuracy θ :=
  scalar_summary_insufficient_of_not_scalar_factorization distance accuracy hnot

/-! The conditional-noise-floor and Gaussian-floor bounds on the explainable fraction answer
this question, and they are `explainable_fraction_bound_of_conditional_noise_floor` and
`explainable_fraction_bound_of_conditional_gaussian_floor` in `Descent.TransportIdentities`.

They were also restated here, suffixed `_exact`, each copying its original's eight-line
measure-theoretic binder block and citing the original as its proof.  Both live in the
`Descent` namespace already, so the copies renamed nothing and reached no reader the
originals did not; what they added was a second block of hypotheses to keep in step. -/

/-- **The between-group fraction of an assumed variance decomposition is at most one.**

    Previously `law_of_total_variance_r2_bound`, documented as the law of total variance
    identity `Var(Z) = E[Var(Z|D)] + Var(E[Z|D])`. The law is not proved here: it is the
    hypothesis `h_decomp`, three unrelated reals related by an equation. What remains after
    it is assumed is that a nonnegative summand's share of a positive total is at most one,
    which is `div_le_one` plus `linarith`.

    The real conditional-variance statements in this file are
    `explainable_fraction_bound_of_conditional_noise_floor_exact` and its Gaussian
    companion, which work against `conditionalVariance` and `conditionalMean` on an actual
    measure rather than against three scalars. Those are where the law of total variance
    is genuinely used. -/
theorem between_group_variance_fraction_le_one
    (varZ eVarZgivenD varEZgivenD : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_eVar_nonneg : 0 ≤ eVarZgivenD)
    :
    varEZgivenD / varZ ≤ 1 := by
  rw [div_le_one h_varZ_pos, h_decomp]
  linarith

/-- **The complementary share of a two-part decomposition:** if
    `varZ = a + b` with `varZ > 0` and `a ≥ (1 - δ)·varZ`, then `b/varZ ≤ δ`.

    Read as the law of total variance, `a` is `E[Var(Z|D)]`, `b` is
    `Var(E[Z|D])`, and the conclusion is a bound on `R²(Z,D)`. That reading is
    supplied entirely by `h_decomp`, which stipulates the decomposition: there
    is no `Z`, no `D`, no conditional expectation and no `R²` below, and the
    law of total variance is not invoked, only assumed in the shape of an
    equation between three reals. A measured `δ` for a fitted model is not an
    instance of this, whose variables are free. -/
theorem div_le_of_ge_one_sub_mul
    (varZ eVarZgivenD varEZgivenD δ : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_within_dominates : eVarZgivenD ≥ (1 - δ) * varZ)
    :
    varEZgivenD / varZ ≤ δ := by
  have h1 : varEZgivenD = varZ - eVarZgivenD := by linarith
  rw [h1, sub_div, div_self (h_varZ_pos.ne')]
  linarith [le_div_iff₀ h_varZ_pos |>.mpr (by linarith : (1 - δ) * varZ ≤ eVarZgivenD)]


/-- **SES explains as much as genetic distance.**
    If both covariates explain comparable fractions and their total
    is bounded, each individual fraction must be small. -/
theorem comparable_covariates_both_small
    (r2_d r2_s B ε : ℝ)
    (h_comparable : r2_d ≤ r2_s + ε)
    (h_sum_bound : r2_d + r2_s ≤ B)
    :
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

/-- **Heterozygosity increases toward 0.5.**
    Under divergent selection, allele freq p moves from extreme to
    intermediate → H = 2p(1-p) increases.
    This drives PGS variance increase for immune traits. -/
theorem two_mul_one_sub_lt_of_lt_of_le_half
    (p₁ p₂ : ℝ)
    (hp₁_lt_p₂ : p₁ < p₂)
    (hp₂_le_half : p₂ ≤ 1 / 2) :
    2 * p₁ * (1 - p₁) < 2 * p₂ * (1 - p₂) := by
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]

/-- **PGS variance increases when the large-effect locus gains more heterozygosity than the
small-effect locus loses.** This is the mechanism proposed for WBC/lymphocyte count.

    A statement taking `h_net : v_large_t - v_large_s > v_small_s - v_small_t` and
    concluding `v_large_s + v_small_s < v_large_t + v_small_t` would be no mechanism at all:
    those two inequalities are the *same inequality rearranged*, so the hypothesis would be
    the conclusion and the proof the rearrangement.

    This one cannot be rearranged into its own hypotheses, because the hypotheses
    are about **effect sizes and heterozygosities separately** and the conclusion is about
    the variance sum they generate. A locus at frequency `p` with effect `β` contributes
    `2β²p(1-p)` to score variance, so the claim has content precisely when the weighting by
    `β²` is doing work: the large-effect locus must actually be the larger-effect one
    (`hβ`), and its heterozygosity gain must exceed the small locus's loss
    (`hlarge_gains_more`). Neither follows from the conclusion.

    Use `two_mul_one_sub_lt_of_lt_of_le_half` to discharge the gain hypothesis from allele
    frequencies moving toward `1/2` under divergent selection, which is the biological step
    the prose describes. -/
theorem two_term_weighted_sum_lt_of_larger_weight_gain
    (βL βS pL pL' pS pS' : ℝ)
    (hβ : βS ^ 2 ≤ βL ^ 2)
    (hβL : 0 < βL ^ 2)
    (hsmall_loses : pS' * (1 - pS') ≤ pS * (1 - pS))
    (hlarge_gains_more :
      pS * (1 - pS) - pS' * (1 - pS') < pL' * (1 - pL') - pL * (1 - pL)) :
    2 * βS ^ 2 * (pS * (1 - pS)) + 2 * βL ^ 2 * (pL * (1 - pL)) <
      2 * βS ^ 2 * (pS' * (1 - pS')) + 2 * βL ^ 2 * (pL' * (1 - pL')) := by
  have hloss_nonneg : 0 ≤ pS * (1 - pS) - pS' * (1 - pS') := by linarith
  -- The small locus's loss is weighted by the smaller squared effect ...
  have hweighted : βS ^ 2 * (pS * (1 - pS) - pS' * (1 - pS'))
      ≤ βL ^ 2 * (pS * (1 - pS) - pS' * (1 - pS')) :=
    mul_le_mul_of_nonneg_right hβ hloss_nonneg
  -- ... and that loss is strictly smaller than the large locus's gain.
  have hgain : βL ^ 2 * (pS * (1 - pS) - pS' * (1 - pS'))
      < βL ^ 2 * (pL' * (1 - pL') - pL * (1 - pL)) :=
    (mul_lt_mul_iff_right₀ hβL).mpr hlarge_gains_more
  nlinarith [hweighted, hgain]

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
    _ < cov_s ^ 2 / (vpgs_s * vy) :=
        div_lt_div_of_pos_right h_cov_drop h_denom_s

/-- **Sign-flip probability.**
    Effect in target ~ N(ρ·β, σ²). Z-score for sign concordance = ρ·β/σ.
    Smaller ρ → smaller z-score → more sign flips.
    (31.7% for lymphocyte vs 9.6% for triglycerides in Wang et al.) -/
theorem sign_flip_z_decreases_with_turnover
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (hρ : ρ₂ < ρ₁) :
    ρ₂ * β / σ < ρ₁ * β / σ :=
  div_lt_div_of_pos_right (by nlinarith) hσ

end Question2


/-!
## Open Question 3: Metric-Specific Portability

Different metrics are different functionals of the same transported law.
For continuous traits this is the exact MSE identity; for binary traits it is
the exact prevalence-recall-FPR formula for precision.
-/

section Question3

variable {Ω : Type*}

theorem binary_precision_formula_exact (c : ConfusionMatrix) :
    ConfusionMatrix.precision c =
      (ConfusionMatrix.prevalence c * ConfusionMatrix.recallRate c) /
        (ConfusionMatrix.prevalence c * ConfusionMatrix.recallRate c +
          (1 - ConfusionMatrix.prevalence c) * ConfusionMatrix.fpr c) :=
  ConfusionMatrix.precision_eq_prevalence_recall_fpr c

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
      (ConfusionMatrix.constant_precision_of_fpr_choice
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 4) (by norm_num) (by norm_num) (by norm_num))
  · simpa using
      (ConfusionMatrix.constant_precision_of_fpr_choice
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 3) (by norm_num) (by norm_num) (by norm_num))

end Question3


/-!
## Open Question 4: Environmental Variance Heterogeneity
-/

section Question4

/-- **`Vg/(Vg + Ve)` decreases as `Ve` grows.**

    Read as `R²` under identical genetics, or as heritability, or as the attainable ceiling:
    they are one inequality. `Descent.GeneEnvironmentInterplay.env_variance_reduces_h2` is the
    same statement, kept there because that file's discussion needs it locally; this is not an
    independent result and should not be cited as one. -/
theorem env_variance_lowers_r2
    (Vg Ve₁ Ve₂ : ℝ)
    (hVg : 0 < Vg) (hVe₁ : 0 < Ve₁)
    (h_more_env : Ve₁ < Ve₂) :
    Vg / (Vg + Ve₂) < Vg / (Vg + Ve₁) := by
  apply div_lt_div_of_pos_left hVg (by linarith) (by linarith)

/-- **A nonzero product added to a coefficient changes it.**

    Kept under its old name because the arithmetic is what the surrounding discussion of
    omitted-variable bias appeals to, but read it as what it is: no regression, no
    estimator and no correlation appears in the statement. That the naive coefficient on
    genetic distance picks up exactly `β_ses · ρ` when SES is omitted is the standard
    omitted-variable formula, asserted in this docstring and derived nowhere in this
    corpus. What is proved is that adding a nonzero product to a number changes it. -/
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
theorem both_le_of_add_eq_of_nonneg
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
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₂ < ρ₁) :
    ((1 - ρ₁) * β + δ) / (ρ₁ * β) < ((1 - ρ₂) * β + δ) / (ρ₂ * β) := by
  rw [div_lt_div_iff₀ (mul_pos hρ₁ hβ) (mul_pos hρ₂ hβ)]
  nlinarith [sq_nonneg β, sq_nonneg δ, mul_pos hρ₁ hβ, mul_pos hρ₂ hβ,
             mul_pos hβ hδ, mul_pos hρ₁ hδ, mul_pos hρ₂ hδ]

/-- **Multiplying by a positive number preserves strict order:**
    `H_s < H_t` gives `β²·H_s < β²·H_t`.

    Read as genetics the two sides are one locus's contribution to score
    variance at two heterozygosities. That reading is the choice to call the
    factors `beta_sq` and `H`; no locus, no genotype and no score appears
    below. -/
theorem mul_lt_mul_left_of_pos'
    (beta_sq H_s H_t : ℝ) (hβ : 0 < beta_sq) (hH : H_s < H_t) :
    beta_sq * H_s < beta_sq * H_t :=
  mul_lt_mul_of_pos_left hH hβ

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

/-- **A net gain on a subset raises the total:** if the increase over `S`
    exceeds the decrease over `Sᶜ`, then `∑ w_s < ∑ w_t`.

    The genetics reading partitions loci into a highlighted set and its
    complement and reads the sums as predictor variance. Below there are no
    loci and no variance — `w_s` and `w_t` are arbitrary functions into `ℝ`,
    not constrained to be nonnegative or to be per-locus contributions of
    anything. Splitting a sum over a finset and its complement, plus
    `linarith`. -/
theorem sum_lt_sum_of_net_gain_on_subset
    {m : ℕ} (w_s w_t : Fin m → ℝ) (S : Finset (Fin m))
    (h_net :
      (∑ i ∈ S, w_t i) - (∑ i ∈ S, w_s i) >
        (∑ i ∈ Sᶜ, w_s i) - (∑ i ∈ Sᶜ, w_t i)) :
    ∑ i, w_s i < ∑ i, w_t i := by
  rw [variance_decomposition w_s S, variance_decomposition w_t S]
  linarith

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
    (h_closer : (π₂ - 1/2) ^ 2 < (π₁ - 1/2) ^ 2) :
    π₁ * (1 - π₁) < π₂ * (1 - π₂) := by
  nlinarith [brier_uncertainty_formula π₁, brier_uncertainty_formula π₂]

/-- **Prediction interval width increases as R² decreases.** -/
theorem interval_width_increases
    (r2₁ r2₂ : ℝ)
    (hr2₁ : r2₂ < r2₁) (hr2₁_lt : r2₁ < 1) :
    Real.sqrt (1 - r2₁) < Real.sqrt (1 - r2₂) :=
  Real.sqrt_lt_sqrt (by linarith) (by linarith)

end Question7


/-!
## Portability: the four-factor decomposition

Portability ratio = AF_factor × LD_factor × Effect_factor × Env_factor.
Genetic distance (Fst) captures only the AF factor, explaining why it
poorly predicts individual-level accuracy.
-/

section FourFactorDecomposition

/-- **The four-factor product is strictly below its AF factor alone.**

    Previously `single_factor_insufficient`, "No single factor captures the full ratio".
    Insufficiency of a single factor is a claim about approximation error, or about a
    factor failing to determine the product; neither is stated. What is proved is one
    strict inequality between the product and one of its factors, which is what you get
    from the other three being below one. It supports the surrounding argument — an Fst
    proxy that sees only the AF factor overstates portability — without being that
    argument. -/
theorem four_factor_product_lt_af_factor
    (af ld eff env : ℝ)
    (h_af : 0 < af)
    (h_ld_lt : ld < 1)
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

/-- **One positive summand's share of a sum of four positive summands is below one.**

    Previously `genetic_distance_variance_bound`, "R² of genetic distance on portability is
    bounded by the AF variance fraction". No R², no genetic distance and no portability
    appears in the statement, and no bound *by* the AF fraction is proved — what is proved
    is a bound *on* it, namely that it is under one, which holds of any of the four
    fractions and is `div_lt_one`. The variance-decomposition reading, in which these four
    numbers are the variances of independent contributions to portability, is asserted in
    the section prose and formalised nowhere. -/
theorem af_variance_fraction_lt_one
    (var_af var_ld var_eff var_env : ℝ)
    (h_af : 0 < var_af) (h_ld : 0 < var_ld)
    (h_eff : 0 < var_eff) (h_env : 0 < var_env) :
    var_af / (var_af + var_ld + var_eff + var_env) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

end FourFactorDecomposition


/-!
## Selection-Driven Allelic Turnover Model

Under fluctuating selection across populations, effect sizes at
immune-associated loci change faster than at neutral loci.
-/

section SelectionModel

/-- **Effect retention under selection.**
    ρ ≤ selection correlation. Low selection correlation → low ρ → low portability. -/
theorem mul_sq_le_mul_sq_of_le_of_nonneg
    (r2_src ρ_eff ρ_sel : ℝ)
    (hr2 : 0 ≤ r2_src)
    (h_bound : ρ_eff ≤ ρ_sel)
    (h_eff_nn : 0 ≤ ρ_eff) :
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

/-- **An effect-retention factor `ρ² < 1` strictly lowers target R² at a fixed target Fst.**

    Previously `drift_only_overestimates_immune_portability`, documented as "Under pure
    drift, portability ratio = (1-Fst_T)/(1-Fst_S). This is what Fst predicts." No ratio of
    source to target appears in the conclusion: **both sides are evaluated at `fstT`**, and
    the comparison is between including the turnover factor `ρ²` and omitting it. The
    source Fst enters no term.

    The linter caught it. The hypotheses `0 ≤ fstS` and `fstS < fstT` — the ones that made
    the statement look like a source-versus-target comparison — occurred in no proof term,
    and `fstS` itself occurred nowhere else, so all three are gone from the signature. What
    the theorem says is that a drift-only prediction, which omits `ρ²`, is higher than one
    that includes it; that supports the surrounding claim about immune traits without being
    a statement about genetic distance at all. -/
theorem effect_retention_lowers_target_r2_at_fixed_fst
    (V_A V_E fstT ρ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstT : fstT < 1)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    r2FromSignalVariance (ρ ^ 2 * presentDayPGSVariance V_A fstT) V_E <
      r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E := by
  apply expectedR2_strictMono_nonneg V_E _ _ hVE
  · exact le_of_lt (mul_pos (sq_pos_of_pos hρ_pos)
      (by unfold presentDayPGSVariance pgsVarianceFromHet; exact mul_pos hVA (by linarith)))
  · have h_pdv_pos : 0 < presentDayPGSVariance V_A fstT := by
      unfold presentDayPGSVariance pgsVarianceFromHet; exact mul_pos hVA (by linarith)
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
    (hlam_faster : lam_slow < lam_fast)
    (hd_pos : 0 < d) :
    Real.exp (-lam_fast * d) < Real.exp (-lam_slow * d) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- **LD tagging efficiency decays exponentially with genetic distance.**
    ρ²_LD(d) = exp(-λ_LD · d).

    **Attribution, corrected: this is NOT the Ohta-Kimura result**, which the
    docstring previously claimed. Ohta and Kimura (1971) give
    `σ_d² ≈ (10 + ρ)/((2 + ρ)(11 + ρ))` with `ρ = 4·Nₑ·c`, formalized at
    `LDDecayTheory.ohtaKimuraSigmaDSq`; that is HYPERBOLIC in the scaled
    recombination rate, not exponential in it, and so is Sved's
    `r² ≈ 1/(1 + 4·Nₑ·c)`. No published neutral two-locus theory in this
    corpus's reference set predicts an exponential in genetic distance. The
    exponential here is a phenomenological one-parameter chart, and it is only
    that.

    Regime: `d` is genetic distance, `λ_LD` a fitted rate with no derivation.
    Nothing identifies `λ_LD` with `Nₑ` or with a recombination rate, so this
    body cannot be inverted for a demographic parameter.

    Empirical status: **FALSIFIED as a shape**
    (`validation/empirical/popgensel/ldshapecell.py`, cell I). This
    supersedes the LEAD the sibling body `PortabilityDrift.ldCorrelationDecay`
    carried -- the same exponential chart, fitted against the same kind of
    simulated `r²` curve, missing at BOTH ends at 21.7 and 14.2 sems. That run
    was recorded as a lead rather than a verdict for one reason: it carried no
    valid positive control. Cell I supplies exactly that control and changes
    nothing else.

    Both shapes are fitted to the SAME binned msprime `r²` values with a free
    amplitude AND a free rate each, so neither is handicapped and any upward
    bias in the `r²` estimator is common to both. The discrimination is the
    shape, which no estimator convention moves.

    | design | exponential χ²/point | hyperbolic χ²/point | worst exp. residual | worst hyp. |
    |---|---|---|---|---|
    | `Nₑ = 2000`, 4 Mb | 28.49 | 4.16 | 8.87 sems | 3.91 sems |
    | `Nₑ = 5000`, 2 Mb | 79.66 | 1.95 | 12.56 sems | 3.46 sems |

    **The positive control, which is the whole point of this cell.** A fitter
    that prefers the hyperbolic on real data proves nothing unless it prefers the
    EXPONENTIAL on data that is genuinely exponential. Run on a true exponential
    with the same `x` grid and matched per-point noise, the same fitter prefers
    the exponential by a sum-of-squares ratio of 168 and 197. So the preference
    reported above is the data's and not the fitter's, and the lead becomes a
    verdict.

    This does not identify the hyperbolic's fitted rate with `4·Nₑ`: at
    `Nₑ = 5000` the fit returns `b = 6572` against Sved's `20000`. What is
    established is that the decay is hyperbolic in genetic distance and not
    exponential in it, which is what this body gets wrong -- and, as the
    paragraph above already says, no choice of `λ_LD` repairs a two-sided
    failure. -/
noncomputable def ldTaggingDecay (lam_LD d : ℝ) : ℝ :=
  Real.exp (-lam_LD * d)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem ldTaggingDecay_at_reference_point :
    ldTaggingDecay 0 0 = 1 := by
  norm_num [ldTaggingDecay]



/-- **Combined LD + effect turnover portability.**
    Total portability = R²_source · ρ²_LD(d) · ρ²_effect(d). -/
noncomputable def combinedPortability
    (r2_src lam_LD lam_eff d : ℝ) : ℝ :=
  r2_src * ldTaggingDecay lam_LD d * (Real.exp (-lam_eff * d)) ^ 2

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem combinedPortability_at_reference_point :
    combinedPortability 1 0 0 1 = 1 := by
  norm_num [combinedPortability, ldTaggingDecay]



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
  · exact faster_decay_lower_correlation lam_eff_neutral lam_eff_immune d hlami hd

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
    (h_ns : 0 < v_noise_s)
    (h_more_noise : v_noise_s < v_noise_t) :
    v_sig / (v_sig + v_noise_t) < v_sig / (v_sig + v_noise_s) :=
  div_lt_div_of_pos_left h_sig (by linarith) (by linarith)

/-- **Corrected portability ratio accounts for noise differences.**
    The "true" portability ratio should compare signal-to-noise ratios,
    not R² values directly.
    SNR_s = v_sig_s / v_noise_s, SNR_t = v_sig_t / v_noise_t.
    Portability = SNR_t / SNR_s, which is invariant to noise scaling. -/
noncomputable def snrPortabilityRatio
    (v_sig_s v_noise_s v_sig_t v_noise_t : ℝ) : ℝ :=
  (v_sig_t / v_noise_t) / (v_sig_s / v_noise_s)

/-- **snrPortabilityRatio where its denominator vanishes, named.** The guard `v_sig_s / v_noise_s`
is zero at `v_sig_s = 0`, `v_noise_s = 1`. Lean returns `0` there rather than the value the
modelled quantity takes, and no type error marks the point. Consumers must require `v_sig_s /
v_noise_s ≠ 0`. -/
theorem snrPortabilityRatio_at_vsigs0vnoises1_is_junk (v_sig_t : ℝ) (v_noise_t : ℝ) :
    snrPortabilityRatio 0 1 v_sig_t v_noise_t = 0 := by
  unfold snrPortabilityRatio
  norm_num

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
theorem mul_sum_lt_sum_mul_of_nonneg_of_exists_pos
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
          (f := fun i ↦ β i ^ 2 * (fst i - fst_global))
          (fun i _ ↦ h_nonneg i)
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

/-- **A weighted average exceeds a constant when the weighted deviations from
    it are positive:** `c < (∑ β² x) / (∑ β²)`.

    The genetics reading is that a genome-wide `F_ST` is a biased proxy for the
    effect-weighted average of local `F_ST`, so global and local carry
    different information. What is proved is that the weighted mean of `x`
    exceeds `c` when `∑ β²(x - c) > 0` — an arithmetic fact about weights, with
    no ancestry, no locus, no LD and no accuracy in it, and in particular no
    comparison of how informative two quantities are. -/
theorem lt_weighted_mean_of_weighted_deviation_pos
    {m : ℕ} (β : Fin m → ℝ) (fst_local : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst_local i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst_local i₀ - fst_global))
    (hweight_pos : 0 < ∑ i, β i ^ 2) :
    fst_global < (∑ i, β i ^ 2 * fst_local i) / (∑ i, β i ^ 2) :=
  (lt_div_iff₀ hweight_pos).2
    (mul_sum_lt_sum_mul_of_nonneg_of_exists_pos β fst_local fst_global h_nonneg i₀ h_strict)

end LocalAncestry


/-!
## Disease-Specific Portability

For binary traits (asthma, T2D), portability depends on additional factors:
- Prevalence differences across populations
- The specific metric used (precision, recall, F1, AUC)
- Threshold choice for classification
-/

section DiseasePortability

/-- **F1 score definition.**

    Empirical status: UNTESTED. -/
noncomputable def f1Score (precision sensitivity : ℝ) : ℝ :=
  2 * precision * sensitivity / (precision + sensitivity)

/-- **f1Score where its denominator vanishes, named.** The guard `precision + sensitivity` is zero
at `precision = 0`, `sensitivity = 0`. A classifier with neither precision nor sensitivity has
no F1 score; the value returned is indistinguishable from a classifier that fires and is always
wrong. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point. Consumers must require `precision + sensitivity ≠ 0`. -/
theorem f1Score_at_precision0sensitivity0_is_junk :
    f1Score 0 0 = 0 := by
  unfold f1Score
  norm_num

/-- **F1 score is symmetric in precision and recall.** -/
theorem f1_symmetric (p r : ℝ) : f1Score p r = f1Score r p := by
  unfold f1Score; ring

/-- **F1 score ≤ arithmetic mean of precision and recall**, the harmonic-arithmetic mean
    inequality for two positive reals.

    Do not head this "F1 score ≤ max(precision, recall)". Of the chain
    `harmonic ≤ arithmetic ≤ max`, only the first inequality is proved. The bound by the
    max is strictly weaker and no theorem here establishes it. The name states exactly
    what is proved. -/
theorem f1_le_arithmetic_mean (p r : ℝ)
    (hp : 0 < p) (hr : 0 < r) :
    f1Score p r ≤ (p + r) / 2 := by
  unfold f1Score
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [sq_nonneg (p - r)]

/-
Two theorems were deleted from this section rather than renamed.

`prevalence_dominates_sensitivity_for_recall` assumed
`sens₁ / sens₂ < n_cases₂ / n_cases₁` and concluded `n_cases₁ * sens₁ < n_cases₂ * sens₂`.
Those are the same inequality: the proof was `rwa [div_lt_div_iff₀ ...] at h_sens_ratio`,
cross-multiplication and nothing else. The docstring said "The net effect on recall depends
on whether the prevalence increase dominates the sensitivity decrease. We prove the
sufficient condition" — but the sufficient condition *is* the conclusion, restated as a
ratio, so proving it from itself decides nothing about which effect dominates. Four of its
eight hypotheses, including the one saying the target has more cases, were unused.

`different_diseases_different_portability_patterns` took four inequalities as hypotheses
and returned their conjunction, `⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩`. Conjunction-introduction over
one's own premises is the case the corpus proof policy names explicitly. Nothing about
asthma, T2D, or a prevalence-distance relationship enters; the statement is true of any
four numbers with those orderings, which is what "qualitatively different patterns" was
being read off from.

The genuine metric-divergence result for this section is
`precision_recall_divergence_exists` above, which exhibits explicit witnesses satisfying
the precision identity rather than assuming the divergence.
-/

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


/-- **Rescaling by `1/r` inverts a slope change by `r`.**

    The nonvanishing hypothesis is real content: no rescaling recovers a slope that has
    been multiplied by zero. Read the name narrowly all the same. This is not
    recoverability by re-calibration, because recovering the slope requires knowing `r`,
    which this statement supplies to itself. -/
theorem slope_rescaling_inverts_slope_change
    (b r pgs : ℝ) (hr : r ≠ 0) :
    (b * r * pgs) * (1 / r) = b * pgs := by
  field_simp

/-- **LD mismatch is NOT recoverable by linear re-calibration.**
    If the LD structure changes, the normal equations have a different solution.
    No linear transformation of the source weights can recover the target optimum.
    (This reuses the existing source_erm_solves_source_not_target_normal_equations.) -/
theorem mulVec_smul_ne_of_not_aligned
    (w_source : Fin 2 → ℝ)
    (σ_target : Matrix (Fin 2) (Fin 2) ℝ)
    (cross_target : Fin 2 → ℝ)
    -- σ_target.mulVec is linear, so scaling w_source just scales the image
    -- The image of the source direction doesn't align with cross_target
    -- (cross_target is not a scalar multiple of σ_target.mulVec w_source)
    (h_not_aligned : ∀ α : ℝ, α • σ_target.mulVec w_source ≠ cross_target) :
    -- Then no linear re-calibration can recover target-optimal weights
    ∀ α : ℝ, σ_target.mulVec (α • w_source) ≠ cross_target := by
  intro α
  rw [Matrix.mulVec_smul]
  exact h_not_aligned α

/-- **Distinct effects give distinct predictions at every nonzero genotype.**

    Previously `effect_turnover_requires_target_data`, "the source GWAS provides no
    information about the new effects. Only target GWAS data helps." An information claim
    needs an information measure and a claim about what data determines what; neither
    appears. The statement is cancellation in a field: if `β_source ≠ β_target` then
    `β_source · y ≠ β_target · y` unless `y = 0`.

    This does say something the section wants — the discrepancy does not vanish, so no
    amount of rescaling the *genotype* hides it — and unlike
    `mulVec_smul_ne_of_not_aligned` above, which quantifies over all linear
    recalibrations `α` and shows none succeeds, it never quantifies over corrections at
    all. That is the difference between the two, and it is why only one of them keeps a
    non-recoverability name. -/
theorem effect_mismatch_gives_prediction_mismatch_at_nonzero_genotype
    (β_source β_target : ℝ)
    (h_different : β_source ≠ β_target) :
    -- Any prediction using β_source has nonzero error for β_target
    ∀ y : ℝ, β_source * y ≠ β_target * y ∨ y = 0 := by
  intro y
  by_cases hy : y = 0
  · right; exact hy
  · left; intro h; exact h_different (mul_right_cancel₀ hy h)

end RecoverablePortability

end Descent
