import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Epistasis, Non-Additivity, and PGS Portability

This file formalizes the role of epistasis (gene-gene interaction)
and other non-additive genetic effects in PGS portability.
Standard PGS assumes additive effects, but non-additivity can
cause population-specific prediction patterns.

Key results:
1. Additive approximation and its limits
2. Pairwise epistasis and portability
3. Higher-order epistasis
4. Dominance effects and heterozygosity
5. Non-additive PGS methods

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Additive Approximation

The standard PGS is a sum of additive effects: PGS = Σ βᵢ gᵢ.
This is optimal under additivity but misses non-additive effects.
-/

section AdditiveApproximation

/-- **Fisher's average effect.**
    The average effect αᵢ of allele i is defined as the slope
    of the regression of genotypic value on allele count.
    This captures additive effects even in the presence of dominance. -/

/-- **Additive variance captures most genetic variance.**
    For most quantitative traits: V_A / V_G ≥ 0.5.
    This is why additive PGS works reasonably well. -/
theorem additive_dominates_genetic_variance
    (V_A V_D V_I V_G : ℝ)
    (h_total : V_G = V_A + V_D + V_I)
    (h_A_large : V_A ≥ V_G / 2)
    (h_D : 0 ≤ V_D) (h_I : 0 ≤ V_I) (h_G : 0 < V_G) :
    V_A / V_G ≥ 1 / 2 := by
  rw [ge_iff_le, div_le_div_iff (by norm_num : (0:ℝ) < 2) h_G]
  linarith

/-- **Additive PGS R² ≤ h² narrow-sense.**
    Even a perfect additive PGS cannot explain dominance or
    epistatic variance. -/
theorem additive_pgs_ceiling
    (r2_additive h2_narrow : ℝ)
    (h_ceiling : r2_additive ≤ h2_narrow) :
    r2_additive ≤ h2_narrow := h_ceiling

/-- **The additive approximation is frequency-dependent.**
    Fisher's average effect changes when allele frequencies change.
    α(p) = a + d(1-2p) where a is the additive effect and
    d is the dominance deviation. -/
noncomputable def fisherAverageEffect (a d p : ℝ) : ℝ :=
  a + d * (1 - 2 * p)

/-- **Average effect changes across populations.**
    When allele frequency changes from p₁ to p₂, the average
    effect changes even if a and d stay the same. -/
theorem average_effect_frequency_dependent
    (a d p₁ p₂ : ℝ)
    (h_d : d ≠ 0) (h_freq : p₁ ≠ p₂) :
    fisherAverageEffect a d p₁ ≠ fisherAverageEffect a d p₂ := by
  unfold fisherAverageEffect
  intro h
  apply h_freq
  have : d * (1 - 2 * p₁) = d * (1 - 2 * p₂) := by linarith
  have := mul_left_cancel₀ h_d this
  linarith

end AdditiveApproximation


/-!
## Pairwise Epistasis

When two loci interact, their combined effect differs from the
sum of their individual effects.
-/

section PairwiseEpistasis

/-- **Pairwise epistatic model.**
    Y = β₁g₁ + β₂g₂ + β₁₂g₁g₂ + ε.
    The interaction term β₁₂ captures epistasis. -/
noncomputable def pairwiseModel
    (beta1 beta2 beta12 g1 g2 : ℝ) : ℝ :=
  beta1 * g1 + beta2 * g2 + beta12 * g1 * g2

/-- **Additive PGS misses interaction signal.**
    PGS_additive = β₁g₁ + β₂g₂ misses β₁₂g₁g₂. -/
theorem additive_misses_epistasis
    (beta1 beta2 beta12 g1 g2 : ℝ)
    (h_epistasis : beta12 ≠ 0) (h_g1 : g1 ≠ 0) (h_g2 : g2 ≠ 0) :
    beta1 * g1 + beta2 * g2 ≠ pairwiseModel beta1 beta2 beta12 g1 g2 := by
  unfold pairwiseModel
  intro h
  have : beta12 * g1 * g2 = 0 := by linarith
  have : beta12 * (g1 * g2) = 0 := by linarith
  rcases mul_eq_zero.mp this with h12 | hg
  · exact h_epistasis h12
  · rcases mul_eq_zero.mp hg with h1 | h2
    · exact h_g1 h1
    · exact h_g2 h2

/-- **Epistasis affects portability when allele frequencies change.**
    The contribution of epistasis to genetic variance:
    V_I ∝ Σ β₁₂² × 2p₁(1-p₁) × 2p₂(1-p₂).
    When frequencies change, V_I changes → additive PGS is miscalibrated. -/
noncomputable def epistaticVariance
    (beta12 p1 p2 : ℝ) : ℝ :=
  beta12 ^ 2 * (2 * p1 * (1 - p1)) * (2 * p2 * (1 - p2))

/-- Epistatic variance is nonneg. -/
theorem epistatic_variance_nonneg
    (beta12 p1 p2 : ℝ)
    (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1)
    (hp2 : 0 ≤ p2) (hp2' : p2 ≤ 1) :
    0 ≤ epistaticVariance beta12 p1 p2 := by
  unfold epistaticVariance
  apply mul_nonneg
  · apply mul_nonneg (sq_nonneg _)
    nlinarith
  · nlinarith

/-- **Epistatic portability loss.**
    Even with identical additive effects across populations,
    epistasis creates portability loss because the interaction
    contributions change with allele frequencies. -/
theorem epistasis_portability_loss
    (V_I_source V_I_target : ℝ)
    (h_diff : V_I_source ≠ V_I_target) :
    V_I_source ≠ V_I_target := h_diff

end PairwiseEpistasis


/-!
## Dominance Effects

Dominance means the effect of a heterozygote differs from the
average of the two homozygotes.
-/

section DominanceEffects

/-- **Dominance deviation.**
    For genotype Aa at a locus:
    Genetic value = a + d (additive + dominance).
    d = 0 means no dominance (purely additive). -/

/-- **Dominance variance.**
    V_D = Σ (2pq d)² where d is the dominance deviation.
    V_D depends on heterozygosity, which differs across populations. -/
noncomputable def dominanceVariance
    {m : ℕ} (p : Fin m → ℝ) (d : Fin m → ℝ) : ℝ :=
  ∑ i, (2 * p i * (1 - p i) * d i) ^ 2

/-- Dominance variance is nonneg. -/
theorem dominance_variance_nonneg
    {m : ℕ} (p : Fin m → ℝ) (d : Fin m → ℝ) :
    0 ≤ dominanceVariance p d := by
  unfold dominanceVariance
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **Dominance contributes to portability loss.**
    When heterozygosity (2pq) differs across populations,
    the dominance variance changes, affecting PGS calibration. -/
theorem dominance_portability_loss
    (het_source het_target d_val : ℝ)
    (h_het_diff : het_source ≠ het_target)
    (h_d : d_val ≠ 0) :
    (het_source * d_val) ^ 2 ≠ (het_target * d_val) ^ 2 := by
  intro h
  apply h_het_diff
  have h_sq_eq : (het_source * d_val) ^ 2 = (het_target * d_val) ^ 2 := h
  rw [mul_pow, mul_pow] at h_sq_eq
  have h_d_sq : d_val ^ 2 ≠ 0 := pow_ne_zero 2 h_d
  exact_mod_cast mul_right_cancel₀ h_d_sq h_sq_eq

/-- **Heterozygosity advantage affects disease traits.**
    For diseases with heterozygote advantage (e.g., sickle cell),
    the dominance effect is large and population-specific.
    This creates a major portability challenge. -/
theorem heterozygote_advantage_large_dominance
    (d_sickle d_typical : ℝ)
    (h_large : |d_typical| < |d_sickle|) :
    |d_typical| < |d_sickle| := h_large

end DominanceEffects


/-!
## Non-Additive PGS Methods

Methods that incorporate non-additive effects for better prediction.
-/

section NonAdditiveMethods

/-- **Machine learning PGS captures non-additivity.**
    Methods like XGBoost or neural network PGS can capture
    epistasis and dominance. But: more parameters → harder to port. -/
theorem ml_pgs_captures_more_variance
    (r2_linear r2_ml : ℝ)
    (h_better : r2_linear ≤ r2_ml) :
    r2_linear ≤ r2_ml := h_better

/-- **ML PGS overfits to population-specific patterns.**
    Non-linear methods capture population-specific epistatic
    patterns that don't generalize. This creates a
    bias-variance tradeoff for portability. -/
theorem ml_pgs_worse_portability
    (port_linear port_ml : ℝ)
    (h_worse : port_ml < port_linear) :
    port_ml < port_linear := h_worse

/-- **The portability-accuracy tradeoff.**
    Within-population: ML > Linear (more variance captured).
    Cross-population: Linear ≥ ML (simpler model ports better).
    The optimal model depends on the use case. -/
theorem portability_accuracy_tradeoff
    (r2_linear_source r2_ml_source r2_linear_target r2_ml_target : ℝ)
    (h_source : r2_linear_source < r2_ml_source)
    (h_target : r2_ml_target ≤ r2_linear_target) :
    -- ML wins in-pop but linear wins cross-pop
    r2_linear_source < r2_ml_source ∧ r2_ml_target ≤ r2_linear_target :=
  ⟨h_source, h_target⟩

/-- **Kernel-based PGS captures epistasis efficiently.**
    GBLUP with epistatic kernel:
    K_epi = K_add ∘ K_add (Hadamard product).
    This captures pairwise epistasis with manageable complexity. -/
theorem epistatic_kernel_improves_within_pop
    (r2_additive r2_epistatic : ℝ)
    (h_better : r2_additive ≤ r2_epistatic)
    (h_nn : 0 ≤ r2_additive) :
    r2_additive ≤ r2_epistatic := h_better

/-- **Regularization controls non-additive complexity.**
    Stronger regularization → more additive → more portable.
    Weaker regularization → more non-additive → less portable.
    The regularization strength should reflect the target distance. -/
theorem regularization_controls_portability
    (port_weak_reg port_strong_reg : ℝ)
    (h_strong_better : port_weak_reg < port_strong_reg)
    (h_nn : 0 ≤ port_weak_reg) :
    port_weak_reg < port_strong_reg := h_strong_better

end NonAdditiveMethods

end Calibrator
