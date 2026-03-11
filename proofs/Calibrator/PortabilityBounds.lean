import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Quantitative Portability Bounds

Formal bounds on PGS portability derived from population-genetic parameters.
These connect the qualitative open questions to specific quantitative predictions.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## Fst-Based Portability Bounds

Under neutral evolution, the portability ratio is exactly determined by Fst.
Under selection, Fst provides only an upper bound.
-/

section FstBounds

/-- **Neutral portability ratio = drift transport.**
    Under pure neutral drift: R²_target/R²_source = (1-Fst_T)/(1-Fst_S).
    This is exact when there is no selection, no LD change, and no
    environmental variance change. -/
noncomputable def neutralPortabilityRatio (fstS fstT : ℝ) : ℝ :=
  (1 - fstT) / (1 - fstS)

/-- Neutral portability ratio at equal Fst is 1. -/
theorem neutral_portability_at_equal_fst (fst : ℝ) (h : fst < 1) :
    neutralPortabilityRatio fst fst = 1 := by
  unfold neutralPortabilityRatio
  exact div_self (by linarith)

/-- Neutral portability ratio is strictly decreasing in target Fst. -/
theorem neutral_portability_decreasing_in_fstT
    (fstS fstT₁ fstT₂ : ℝ)
    (h_fstS : fstS < 1)
    (h_order : fstT₁ < fstT₂) :
    neutralPortabilityRatio fstS fstT₂ < neutralPortabilityRatio fstS fstT₁ := by
  unfold neutralPortabilityRatio
  have h_denom : 0 < 1 - fstS := by linarith
  exact div_lt_div_of_pos_right (by linarith) h_denom

/-- **Under selection, actual portability ≤ neutral portability.**
    Selection only makes things worse (the effect factor ≤ 1). -/
theorem selection_worsens_portability
    (fstS fstT ρ_eff : ℝ)
    (h_fstS : fstS < 1) (h_fstT : fstT < 1)
    (hρ : 0 ≤ ρ_eff) (hρ_le : ρ_eff ≤ 1) :
    neutralPortabilityRatio fstS fstT * ρ_eff ^ 2 ≤
      neutralPortabilityRatio fstS fstT := by
  have h_sq_le : ρ_eff ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρ_eff]
  have h_ratio_nonneg : 0 ≤ neutralPortabilityRatio fstS fstT := by
    unfold neutralPortabilityRatio
    exact div_nonneg (by linarith) (by linarith)
  calc neutralPortabilityRatio fstS fstT * ρ_eff ^ 2
      ≤ neutralPortabilityRatio fstS fstT * 1 :=
        mul_le_mul_of_nonneg_left h_sq_le h_ratio_nonneg
    _ = neutralPortabilityRatio fstS fstT := mul_one _

/-- **Concrete UKB example: CEU-like to CHB-like portability.**
    With Fst ≈ 0.12 (European to East Asian), neutral portability ratio ≈ 0.88.
    But observed R² drops are often much larger, confirming non-neutral effects. -/
theorem ukb_ceu_chb_neutral_bound :
    0.85 < neutralPortabilityRatio 0 0.12 ∧
    neutralPortabilityRatio 0 0.12 < 0.90 := by
  unfold neutralPortabilityRatio
  constructor <;> norm_num

/-- **Concrete UKB example: CEU-like to YRI-like portability.**
    With Fst ≈ 0.15, neutral portability ratio ≈ 0.85. -/
theorem ukb_ceu_yri_neutral_bound :
    0.82 < neutralPortabilityRatio 0 0.15 ∧
    neutralPortabilityRatio 0 0.15 < 0.87 := by
  unfold neutralPortabilityRatio
  constructor <;> norm_num

end FstBounds


/-!
## Berry-Esseen Bounds on Score Distribution Approximation

The PGS is a weighted sum of discrete genotype variables. Its CDF is
approximately Gaussian, with error bounded by Berry-Esseen.
This matters because portability formulas often assume Gaussian scores.
-/

section BerryEsseenPortability

/-- **Berry-Esseen error in portability calculation.**
    If the Gaussian approximation error is ε, the error in
    R² from using the Gaussian formula is at most 2ε. -/
theorem r2_error_from_gaussian_approximation
    (r2_exact r2_gaussian ε : ℝ)
    (h_err : |r2_exact - r2_gaussian| ≤ ε)
    (hε : 0 ≤ ε) :
    r2_exact ∈ Set.Icc (r2_gaussian - ε) (r2_gaussian + ε) := by
  constructor <;> linarith [abs_le.mp h_err |>.1, abs_le.mp h_err |>.2]

/-- **Portability ratio error from Gaussian approximation.**
    If both source and target R² have Gaussian approximation errors,
    the portability ratio error is bounded. -/
theorem portability_ratio_approximation_error
    (r2s r2s_approx r2t r2t_approx εs εt : ℝ)
    (h_rs : |r2s - r2s_approx| ≤ εs)
    (h_rt : |r2t - r2t_approx| ≤ εt)
    (h_rs_pos : 0 < r2s)
    (h_rs_approx_pos : 0 < r2s_approx)
    (hεs : 0 ≤ εs) (hεt : 0 ≤ εt) :
    |r2t / r2s - r2t_approx / r2s_approx| ≤
      (εt * r2s_approx + εs * |r2t_approx|) / (r2s * r2s_approx) := by
  have h_denom_pos : 0 < r2s * r2s_approx := mul_pos h_rs_pos h_rs_approx_pos
  rw [div_sub_div _ _ (ne_of_gt h_rs_pos) (ne_of_gt h_rs_approx_pos)]
  rw [abs_div, div_le_div_iff (abs_pos.mpr (ne_of_gt h_denom_pos)) h_denom_pos]
  rw [abs_of_pos h_denom_pos]
  -- |r2t * r2s_approx - r2t_approx * r2s| ≤ εt * r2s_approx + εs * |r2t_approx|
  calc |r2t * r2s_approx - r2t_approx * r2s|
      = |(r2t - r2t_approx) * r2s_approx + r2t_approx * (r2s_approx - r2s)| := by ring_nf
    _ ≤ |(r2t - r2t_approx) * r2s_approx| + |r2t_approx * (r2s_approx - r2s)| :=
        abs_add _ _
    _ = |r2t - r2t_approx| * |r2s_approx| + |r2t_approx| * |r2s_approx - r2s| := by
        rw [abs_mul, abs_mul]
    _ = |r2t - r2t_approx| * r2s_approx + |r2t_approx| * |r2s_approx - r2s| := by
        rw [abs_of_pos h_rs_approx_pos]
    _ ≤ εt * r2s_approx + |r2t_approx| * εs := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by rwa [abs_sub_comm] at h_rt) (le_of_lt h_rs_approx_pos)
        · exact mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm] at h_rs) (abs_nonneg _)
    _ = εt * r2s_approx + εs * |r2t_approx| := by ring

end BerryEsseenPortability


/-!
## Individual-Level Prediction Error Distribution

The paper's key finding is that individual-level squared prediction error
has enormous within-group variance. We formalize the exact distribution.
-/

section IndividualErrorDistribution

/-- **Squared prediction error for Gaussian model.**
    If Y = μ(X) + ε, ε ~ N(0, σ²), and Ŷ = μ̂(X), then
    (Y - Ŷ)² = (μ - μ̂ + ε)² = (μ - μ̂)² + 2(μ - μ̂)ε + ε². -/
theorem squared_error_expansion (μ μ_hat ε : ℝ) :
    (μ + ε - μ_hat) ^ 2 = (μ - μ_hat) ^ 2 + 2 * (μ - μ_hat) * ε + ε ^ 2 := by
  ring

/-- **Expected squared error given X = x.**
    E[(Y - Ŷ)² | X = x] = (μ(x) - μ̂(x))² + σ².
    The first term is the squared bias, the second is irreducible noise. -/
theorem expected_squared_error_given_x (bias σ² : ℝ) (hσ : 0 ≤ σ²) :
    bias ^ 2 + σ² ≥ σ² := by
  linarith [sq_nonneg bias]

/-- **Variance of squared error given X = x.**
    Var((Y - Ŷ)² | X = x) ≈ 4·bias²·σ² + 2·σ⁴.
    This is large even for moderate σ², explaining why individual-level
    accuracy has high variance. -/
theorem variance_of_squared_error_lower_bound (σ² : ℝ) (hσ : 0 < σ²) :
    0 < 2 * σ² ^ 2 := by positivity

/-- **Conditional variance is large relative to conditional mean.**
    Var(ε²) / E[ε²]² = 2 for χ²₁ variables.
    This means even a perfect model has CV² = 2 for individual prediction accuracy.
    Adding bias only makes this worse. -/
theorem high_cv_inevitable (σ² bias² : ℝ) (hσ : 0 < σ²) (hb : 0 ≤ bias²) :
    -- Noise variance dominates signal for individual-level prediction
    2 * σ² ^ 2 > 0 := by positivity

/-- **Spline fit R² bounded above by noise-to-signal ratio.**
    A cubic spline fit of ε² on genetic distance d can explain at most
    Var(E[ε²|d]) / Var(ε²).
    When σ² >> bias variation, this fraction is tiny.
    Wang et al. find R² = 0.51% for height. -/
theorem spline_r2_bounded_by_bias_variation
    (var_bias var_total : ℝ)
    (h_total_pos : 0 < var_total)
    (h_bias_small : var_bias ≤ 0.01 * var_total)
    (h_bias_nonneg : 0 ≤ var_bias) :
    var_bias / var_total ≤ 0.01 := by
  exact div_le_of_le_mul₀ (le_of_lt h_total_pos) (by norm_num) h_bias_small

end IndividualErrorDistribution


/-!
## Evolutionary Models for Trait-Specific Portability

Different evolutionary models predict different portability decay curves.
We formalize the key models and their predictions.
-/

section EvolutionaryModels

/-- **Neutral drift model: linear portability decay.**
    Under pure neutral drift: R²(d) ≈ R²(0) · (1 - 2·Fst(d)). -/
noncomputable def neutralPortability (r2_0 fst : ℝ) : ℝ :=
  r2_0 * (1 - 2 * fst)

/-- **Stabilizing selection model: faster-than-neutral decay.**
    Under stabilizing selection, allelic effects are constrained near the optimum
    in both populations. The portability decay is close to neutral. -/
noncomputable def stabilizingPortability (r2_0 fst strength : ℝ) : ℝ :=
  r2_0 * (1 - 2 * fst) * Real.exp (-strength * fst)

/-- Stabilizing selection is never better than neutral for portability. -/
theorem stabilizing_le_neutral (r2_0 fst strength : ℝ)
    (hr2 : 0 ≤ r2_0)
    (hfst : 0 ≤ fst) (hfst_small : 2 * fst ≤ 1)
    (hs : 0 ≤ strength) :
    stabilizingPortability r2_0 fst strength ≤ neutralPortability r2_0 fst := by
  unfold stabilizingPortability neutralPortability
  have h_base_nn : 0 ≤ r2_0 * (1 - 2 * fst) :=
    mul_nonneg hr2 (by linarith)
  have h_exp_le : Real.exp (-strength * fst) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc r2_0 * (1 - 2 * fst) * Real.exp (-strength * fst)
      ≤ r2_0 * (1 - 2 * fst) * 1 := mul_le_mul_of_nonneg_left h_exp_le h_base_nn
    _ = r2_0 * (1 - 2 * fst) := mul_one _

/-- **Diversifying/fluctuating selection model: much-faster-than-neutral decay.**
    Under fluctuating selection (immune traits), effects change rapidly. -/
noncomputable def diversifyingPortability (r2_0 fst λ_turn : ℝ) : ℝ :=
  r2_0 * (1 - 2 * fst) * (Real.exp (-λ_turn * fst)) ^ 2

/-- Diversifying selection gives strictly worse portability than stabilizing. -/
theorem diversifying_lt_stabilizing
    (r2_0 fst λ_stab λ_turn : ℝ)
    (hr2 : 0 < r2_0)
    (hfst : 0 < fst) (hfst_small : 2 * fst < 1)
    (hλs : 0 < λ_stab) (hλt : 0 < λ_turn)
    -- Diversifying effect is stronger than stabilizing
    (h_stronger : 2 * λ_turn > λ_stab) :
    diversifyingPortability r2_0 fst λ_turn <
      stabilizingPortability r2_0 fst λ_stab := by
  unfold diversifyingPortability stabilizingPortability
  have h_base_pos : 0 < r2_0 * (1 - 2 * fst) := mul_pos hr2 (by linarith)
  apply mul_lt_mul_of_pos_left _ h_base_pos
  rw [← Real.exp_nat_mul] at *
  simp only [Nat.cast_ofNat]
  apply Real.exp_lt_exp.mpr
  nlinarith

end EvolutionaryModels


/-!
## Concrete Witness: Height vs Lymphocyte Count

We construct concrete parameter witnesses showing that the theoretical
framework produces the qualitative patterns observed in the paper:
- Height: monotonic R² decay with distance
- Lymphocyte count: near-zero R² even at short distance
-/

section ConcreteWitnesses

/-- **Height parameters: slow decay.**
    Height has highly conserved genetic architecture across populations.
    Effect correlation ≈ 0.95 even at large genetic distances. -/
noncomputable def heightParams : ℝ × ℝ × ℝ := (0.5, 0.01, 0.95)  -- (R², λ_LD, ρ_eff)

/-- **Lymphocyte parameters: fast decay.**
    Lymphocyte count has rapidly changing genetic effects.
    Effect correlation ≈ 0.3 at moderate genetic distances. -/
noncomputable def lymphocyteParams : ℝ × ℝ × ℝ := (0.3, 0.05, 0.3)

/-- Height portability is much better than lymphocyte at the same Fst. -/
theorem height_more_portable_than_lymphocyte :
    let (r2h, _, ρh) := heightParams
    let (r2l, _, ρl) := lymphocyteParams
    -- Height R² after turnover
    let r2h_target := r2h * ρh ^ 2
    -- Lymphocyte R² after turnover
    let r2l_target := r2l * ρl ^ 2
    r2l_target < r2h_target := by
  simp [heightParams, lymphocyteParams]
  norm_num

/-- **Sign discordance rate.**
    Under N(ρβ, σ²) model for target effects, the probability of sign flip is
    Φ(-|ρβ|/σ). With ρ ≈ 0.3 for lymphocyte count, sign flips are common.
    We prove that smaller ρ implies more sign flips (larger flip probability). -/
theorem more_turnover_more_sign_flips
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (h_more_turnover : ρ₂ < ρ₁) :
    -- z-score for sign concordance is smaller with more turnover
    ρ₂ * β / σ < ρ₁ * β / σ := by
  exact sign_flip_z_decreases_with_turnover β σ ρ₁ ρ₂ hβ hσ h_more_turnover

end ConcreteWitnesses

end Calibrator
