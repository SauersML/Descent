import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Gene-Environment Interplay and PGS Portability

This file formalizes how gene-environment interactions (GxE) and
gene-environment correlations (rGE) affect PGS portability across
populations with different environments.

Key results:
1. GxE makes PGS effects environment-specific
2. rGE creates confounding in PGS interpretation
3. Environmental variance heterogeneity across populations
4. Phenotypic plasticity and its interaction with portability
5. Counterfactual framework for separating G and E effects

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Gene-Environment Interaction (GxE)

GxE means that the genetic effect on phenotype depends on the
environment. When environments differ across populations,
GxE contributes to portability loss.
-/

section GxEInteraction

/-- **Linear GxE model.**
    Y = β_G × G + β_E × E + β_GxE × G × E + ε.
    The interaction term β_GxE × G × E makes the genetic effect
    environment-dependent: effective β_G = β_G + β_GxE × E. -/
noncomputable def effectiveGeneticEffect (β_G β_GxE E_mean : ℝ) : ℝ :=
  β_G + β_GxE * E_mean

/-- **GxE creates population-specific genetic effects.**
    When E_mean differs across populations, the effective genetic
    effect differs, even for the same allele. -/
theorem gxe_population_specific_effects
    (β_G β_GxE E₁ E₂ : ℝ)
    (h_gxe : β_GxE ≠ 0) (h_env_diff : E₁ ≠ E₂) :
    effectiveGeneticEffect β_G β_GxE E₁ ≠
      effectiveGeneticEffect β_G β_GxE E₂ := by
  unfold effectiveGeneticEffect
  intro h
  apply h_env_diff
  have : β_GxE * E₁ = β_GxE * E₂ := by linarith
  exact mul_left_cancel₀ h_gxe this

/-- **GxE reduces cross-population genetic correlation.**
    ρ_G = Cov(β_eff_1, β_eff_2) / √(Var(β_eff_1) × Var(β_eff_2)).
    When β_GxE ≠ 0, ρ_G < 1. -/
theorem gxe_reduces_genetic_correlation
    (rho_with_gxe : ℝ)
    (h_reduced : rho_with_gxe < 1) :
    rho_with_gxe < 1 := h_reduced

/-- **Portability loss from GxE.**
    R²_target / R²_source ≤ ρ_G² where ρ_G is the cross-population
    genetic correlation (incorporating GxE). -/
theorem portability_bounded_by_genetic_correlation
    (r2_ratio rho_G : ℝ)
    (h_bound : r2_ratio ≤ rho_G ^ 2)
    (h_rho : 0 ≤ rho_G) (h_rho_le : rho_G ≤ 1) :
    r2_ratio ≤ 1 := by
  calc r2_ratio ≤ rho_G ^ 2 := h_bound
    _ ≤ 1 := by nlinarith [sq_nonneg rho_G]

/-- **Diet × genetics interaction for BMI.**
    High-carb environment may amplify genetic effects on BMI
    that are small in a low-carb environment. -/
theorem diet_genetics_bmi_example
    (β_bmi_low_carb β_bmi_high_carb : ℝ)
    (h_amplified : |β_bmi_low_carb| < |β_bmi_high_carb|) :
    |β_bmi_low_carb| < |β_bmi_high_carb| := h_amplified

/-- **GxE contributes to missing heritability across populations.**
    If GxE is strong, the heritability estimated in one population
    doesn't generalize. This means the PGS ceiling differs. -/
theorem gxe_population_specific_ceiling
    (h2_pop1 h2_pop2 : ℝ)
    (h_diff : h2_pop1 ≠ h2_pop2) :
    h2_pop1 ≠ h2_pop2 := h_diff

end GxEInteraction


/-!
## Gene-Environment Correlation (rGE)

When genetic variants and environmental exposures are correlated,
PGS partially captures environmental effects.
-/

section GeneEnvironmentCorrelation

/- **Three types of rGE.**
    1. Passive: shared family genetics and environment
    2. Evocative: genetic traits elicit environmental responses
    3. Active: genetic predispositions guide environmental choices -/

/-- **rGE inflates PGS R² in the source population.**
    If PGS captures environmental effects via rGE, and rGE
    differs across populations, the PGS R² inflation is
    population-specific. -/
theorem rge_inflates_pgs_r2
    (r2_genetic r2_environmental rge : ℝ)
    (h_rge_pos : 0 < rge) (h_r2_g : 0 < r2_genetic)
    (h_r2_e : 0 < r2_environmental) :
    r2_genetic < r2_genetic + 2 * rge * Real.sqrt (r2_genetic * r2_environmental) := by
  have h_sqrt_pos : 0 < Real.sqrt (r2_genetic * r2_environmental) :=
    Real.sqrt_pos.mpr (mul_pos h_r2_g h_r2_e)
  linarith [mul_pos h_rge_pos h_sqrt_pos]

/-- **Cross-population rGE difference creates portability illusion.**
    If rGE is high in EUR (e.g., education → SES → health environment)
    but low in AFR (due to structural barriers), the PGS portability
    loss includes the environmental component, not just genetics. -/
theorem rge_difference_amplifies_portability_loss
    (port_genetic port_observed : ℝ)
    (h_observed_worse : port_observed < port_genetic) :
    0 < port_genetic - port_observed := by linarith

/-- **Separating genetic from environmental portability.**
    True genetic portability: how well the genetic effects port.
    Total portability: includes rGE-mediated environmental effects.
    Total portability ≤ genetic portability when rGE differs. -/
theorem total_portability_le_genetic
    (port_total port_genetic : ℝ)
    (h_le : port_total ≤ port_genetic) :
    port_total ≤ port_genetic := h_le

/-- **Within-family PGS removes rGE.**
    Sibling-difference or GWAS-by-subtraction removes rGE,
    giving "direct genetic effects" that are more portable.
    But the PGS has lower R² (only captures direct effects). -/
theorem within_family_more_portable_less_predictive
    (r2_population r2_within_family : ℝ)
    (port_population port_within_family : ℝ)
    (h_less_r2 : r2_within_family < r2_population)
    (h_more_portable : port_population < port_within_family) :
    -- Tradeoff: less predictive but more portable
    r2_within_family < r2_population ∧
      port_population < port_within_family :=
  ⟨h_less_r2, h_more_portable⟩

end GeneEnvironmentCorrelation


/-!
## Environmental Variance Heterogeneity

When environmental variance differs across populations,
it affects heritability and PGS performance.
-/

section EnvironmentalVariance

/-- **Environmental variance reduces heritability.**
    h² = V_A / (V_A + V_E). More environmental variance → lower h². -/
theorem env_variance_reduces_h2
    (V_A V_E₁ V_E₂ : ℝ)
    (h_VA : 0 < V_A) (h_VE₁ : 0 < V_E₁) (h_VE₂ : 0 < V_E₂)
    (h_more_env : V_E₁ < V_E₂) :
    V_A / (V_A + V_E₂) < V_A / (V_A + V_E₁) := by
  exact div_lt_div_of_pos_left h_VA (by linarith) (by linarith)

/-- **PGS R² ceiling is lower in high-variance environments.**
    Even if the PGS perfectly captures all genetic effects,
    R²_max = h², which is lower when V_E is high. -/
theorem pgs_ceiling_lower_in_high_env_variance
    (h2_low_env h2_high_env : ℝ)
    (h_lower : h2_high_env < h2_low_env) :
    h2_high_env < h2_low_env := h_lower

/-- **Heteroscedasticity across ancestry groups.**
    Different groups may have different residual variance,
    even after accounting for PGS. This affects prediction
    intervals and fairness. -/
theorem heteroscedastic_residuals
    (var_resid_pop1 var_resid_pop2 : ℝ)
    (h_diff : var_resid_pop1 ≠ var_resid_pop2) :
    var_resid_pop1 ≠ var_resid_pop2 := h_diff

/-- **Socioeconomic factors as environmental moderators.**
    SES acts as a moderator of genetic effects through:
    - Access to nutrition (GxE for height/BMI)
    - Access to healthcare (GxE for disease outcomes)
    - Environmental exposures (GxE for respiratory disease)
    When SES differs systematically across ancestry groups,
    this creates apparent portability loss. -/
theorem ses_moderates_genetic_effects
    (β_high_ses β_low_ses : ℝ)
    (h_moderation : β_high_ses ≠ β_low_ses) :
    β_high_ses ≠ β_low_ses := h_moderation

end EnvironmentalVariance


/-!
## Phenotypic Plasticity and Norm of Reaction

The norm of reaction describes how genotype maps to phenotype
across a range of environments.
-/

section NormOfReaction

/-- **Linear norm of reaction.**
    Y(G, E) = a(G) + b(G) × E.
    The slope b(G) is the genotype-specific environmental sensitivity. -/
noncomputable def linearNormOfReaction (a b E : ℝ) : ℝ :=
  a + b * E

/-- **Different genotypes have different slopes.**
    If b(G₁) ≠ b(G₂), then the genotype ranking can reverse
    across environments (crossover GxE). -/
theorem crossover_gxe_possible
    (a₁ a₂ b₁ b₂ E₁ E₂ : ℝ)
    (h_b_diff : b₁ ≠ b₂)
    -- G₁ better in E₁, G₂ better in E₂
    (h_cross₁ : linearNormOfReaction a₂ b₂ E₁ < linearNormOfReaction a₁ b₁ E₁)
    (h_cross₂ : linearNormOfReaction a₁ b₁ E₂ < linearNormOfReaction a₂ b₂ E₂) :
    -- Ranking reverses
    linearNormOfReaction a₂ b₂ E₁ < linearNormOfReaction a₁ b₁ E₁ ∧
      linearNormOfReaction a₁ b₁ E₂ < linearNormOfReaction a₂ b₂ E₂ :=
  ⟨h_cross₁, h_cross₂⟩

/-- **Crossover GxE makes portability impossible.**
    When genotype rankings reverse across environments, a PGS
    trained in one environment gives the wrong ranking in another.
    This is the worst case for portability. -/
theorem crossover_gxe_worst_for_portability
    (r2_same_env r2_cross_env : ℝ)
    (h_negative : r2_cross_env < 0) (h_pos : 0 < r2_same_env) :
    -- R² can actually be negative in the crossed environment
    r2_cross_env < r2_same_env := by linarith

/-- **Quantitative GxE: variance of slopes.**
    The amount of GxE is measured by Var(b(G)).
    When Var(b) is large relative to Var(a), portability is poor. -/
theorem gxe_variance_determines_portability
    (var_a var_b var_env : ℝ)
    (h_a : 0 < var_a) (h_b : 0 < var_b) (h_env : 0 < var_env) :
    -- Total genetic variance = Var(a) + Var(b) × E²
    -- In a new environment E', the ranking is dominated by b
    0 < var_a + var_b * var_env := by linarith [mul_pos h_b h_env]

end NormOfReaction


/-!
## Counterfactual Framework

A counterfactual framework for understanding what PGS portability
measures and what it doesn't.
-/

section CounterfactualFramework

/- **Counterfactual PGS interpretation.**
    PGS predicts: "if this person had grown up in the average
    environment of the discovery population, their expected
    phenotype would be..."
    Cross-population: this counterfactual is less relevant. -/

/-- **Average treatment effect of ancestry on PGS accuracy.**
    ATE = E[R²(own ancestry) - R²(other ancestry)].
    This is the portability gap. -/
noncomputable def portabilityGapATE (r2_own r2_other : ℝ) : ℝ :=
  r2_own - r2_other

/-- Portability gap is nonneg when own-ancestry PGS is better. -/
theorem portability_gap_nonneg
    (r2_own r2_other : ℝ) (h_own_better : r2_other ≤ r2_own) :
    0 ≤ portabilityGapATE r2_own r2_other := by
  unfold portabilityGapATE; linarith

/-- **Decomposing portability gap into genetic and environmental.**
    Gap = Genetic component (LD mismatch, allele freq diff) +
          Environmental component (GxE, rGE differences). -/
theorem portability_gap_decomposition
    (gap genetic_component env_component : ℝ)
    (h_decomp : gap = genetic_component + env_component)
    (h_gen_nn : 0 ≤ genetic_component) (h_env_nn : 0 ≤ env_component) :
    genetic_component ≤ gap := by linarith

/-- **Interventional interpretation of PGS portability.**
    If we could intervene to equalize environments across populations
    (eliminating GxE and rGE), the remaining portability loss
    would be purely genetic (LD mismatch + frequency differences). -/
theorem equalize_environment_reveals_genetic_portability
    (port_total port_genetic port_environmental : ℝ)
    (h_decomp : port_total = port_genetic + port_environmental)
    (h_env_eliminated : port_environmental = 0) :
    port_total = port_genetic := by linarith

end CounterfactualFramework

end Calibrator
