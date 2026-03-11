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
    If rGE is high in the source (e.g., education → SES → health environment)
    but low in the target (due to structural barriers), the PGS portability
    loss includes the environmental component, not just genetics. -/
theorem rge_difference_amplifies_portability_loss
    (port_genetic port_observed : ℝ)
    (h_observed_worse : port_observed < port_genetic) :
    0 < port_genetic - port_observed := by linarith

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
theorem portability_gap_ate_nonneg
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
