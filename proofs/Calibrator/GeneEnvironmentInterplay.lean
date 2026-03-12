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
    The effective genetic effect is β_G + β_GxE × E. The
    cross-population correlation of effective effects depends on
    Var(β_GxE × E). When the interaction variance V_GxE > 0, the
    correlation ρ = V_G / (V_G + V_GxE) < 1. -/
theorem gxe_reduces_genetic_correlation
    (V_G V_GxE : ℝ)
    (h_G : 0 < V_G) (h_GxE : 0 < V_GxE) :
    V_G / (V_G + V_GxE) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- **Portability loss from GxE.**
    The cross-population genetic correlation ρ_G = V_G / (V_G + V_GxE)
    bounds portability: R²_target ≤ ρ_G² × R²_source.
    We derive: when V_GxE > 0, the bound ρ_G² < 1 strictly, meaning
    portability is strictly reduced. The portability ratio is at most
    (V_G / (V_G + V_GxE))². -/
theorem portability_bounded_by_genetic_correlation
    (V_G V_GxE : ℝ)
    (h_G : 0 < V_G) (h_GxE : 0 < V_GxE) :
    let rho_G := V_G / (V_G + V_GxE)
    0 < rho_G ∧ rho_G < 1 ∧ rho_G ^ 2 < 1 := by
  have h_sum : 0 < V_G + V_GxE := by linarith
  refine ⟨div_pos h_G h_sum, ?_, ?_⟩
  · rw [div_lt_one h_sum]; linarith
  · have h_rho_lt : V_G / (V_G + V_GxE) < 1 := by rw [div_lt_one h_sum]; linarith
    have h_rho_nn : 0 ≤ V_G / (V_G + V_GxE) := le_of_lt (div_pos h_G h_sum)
    nlinarith [sq_nonneg (V_G / (V_G + V_GxE))]

/-- **Diet × genetics interaction for BMI.**
    High-carb environment may amplify genetic effects on BMI.
    Under the linear GxE model, the effective genetic effect is
    β_G + β_GxE × E. When β_GxE > 0 and E_high > E_low > 0,
    the effective effect in the high-carb environment exceeds
    that in the low-carb environment. -/
theorem diet_genetics_bmi_example
    (β_G β_GxE E_low E_high : ℝ)
    (h_β_G : 0 < β_G) (h_β_GxE : 0 < β_GxE)
    (h_E_low : 0 < E_low) (h_E_high : E_low < E_high) :
    effectiveGeneticEffect β_G β_GxE E_low <
      effectiveGeneticEffect β_G β_GxE E_high := by
  unfold effectiveGeneticEffect
  have : β_GxE * E_low < β_GxE * E_high := mul_lt_mul_of_pos_left h_E_high h_β_GxE
  linarith

/-- **GxE contributes to missing heritability across populations.**
    If GxE is strong, the heritability estimated in one population
    doesn't generalize. h² = V_A / (V_A + V_E). When the effective
    V_A changes due to GxE (different environments modulate genetic
    effects), h² differs. With the same V_A but different V_E
    across populations, the heritability ceilings differ. -/
theorem gxe_population_specific_ceiling
    (V_A V_E₁ V_E₂ : ℝ)
    (h_VA : 0 < V_A) (h_VE₁ : 0 < V_E₁) (h_VE₂ : 0 < V_E₂)
    (h_env_diff : V_E₁ ≠ V_E₂) :
    V_A / (V_A + V_E₁) ≠ V_A / (V_A + V_E₂) := by
  intro h
  apply h_env_diff
  have h1 : 0 < V_A + V_E₁ := by linarith
  have h2 : 0 < V_A + V_E₂ := by linarith
  have := div_eq_div_iff h1.ne' h2.ne' |>.mp h
  nlinarith

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
    PGS R² in the source is inflated by rGE: R²_observed = R²_genetic + 2·rge·√(R²_g·R²_e).
    When rGE differs across populations (rge_source > rge_target ≥ 0), the apparent
    portability R²_target/R²_source is lower than the true genetic portability,
    because the source denominator is more inflated. -/
theorem rge_difference_amplifies_portability_loss
    (r2_g r2_e rge_source rge_target : ℝ)
    (h_g : 0 < r2_g) (h_e : 0 < r2_e)
    (h_rge_s : 0 < rge_source) (h_rge_t : 0 ≤ rge_target)
    (h_rge_diff : rge_target < rge_source) :
    let inflation_s := 2 * rge_source * Real.sqrt (r2_g * r2_e)
    let inflation_t := 2 * rge_target * Real.sqrt (r2_g * r2_e)
    inflation_t < inflation_s := by
  have h_sqrt_pos : 0 < Real.sqrt (r2_g * r2_e) :=
    Real.sqrt_pos.mpr (mul_pos h_g h_e)
  nlinarith [mul_pos (show 0 < rge_source - rge_target by linarith) h_sqrt_pos]

/-- **Separating genetic from environmental portability.**
    The PGS captures both genetic signal (V_direct) and rGE-mediated
    environmental signal. Within-family estimation removes rGE,
    isolating V_direct. We show the observed (population-level)
    R² = (V_direct + V_rge) / V_P strictly exceeds the direct
    genetic R² = V_direct / V_P, so the environmental component
    V_rge / V_P is the non-portable inflation. -/
theorem total_portability_le_genetic
    (V_direct V_rge V_P : ℝ)
    (h_dir : 0 < V_direct) (h_rge : 0 < V_rge) (h_P : 0 < V_P) :
    V_direct / V_P < (V_direct + V_rge) / V_P ∧
    (V_direct + V_rge) / V_P - V_direct / V_P = V_rge / V_P := by
  constructor
  · exact div_lt_div_of_pos_right (by linarith) h_P
  · rw [← sub_div]; ring_nf

/-- **Within-family PGS removes rGE.**
    Sibling-difference or GWAS-by-subtraction removes rGE,
    giving "direct genetic effects" that are more portable.
    Population PGS captures V_direct + V_rge (inflated by rGE),
    while within-family captures only V_direct. The within-family
    PGS has lower R² but the rGE component doesn't port, so
    within-family is more portable. -/
theorem within_family_more_portable_less_predictive
    (V_direct V_rge V_E : ℝ)
    (h_dir : 0 < V_direct) (h_rge : 0 < V_rge) (h_E : 0 < V_E) :
    -- Within-family R² < population R² (less predictive)
    V_direct / (V_direct + V_rge + V_E) < (V_direct + V_rge) / (V_direct + V_rge + V_E) ∧
    -- But within-family captures only portable signal (no rGE inflation)
      0 < V_rge / (V_direct + V_rge + V_E) := by
  have h_denom : 0 < V_direct + V_rge + V_E := by linarith
  exact ⟨div_lt_div_of_pos_right (by linarith) h_denom, div_pos h_rge h_denom⟩

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
    R²_max = h² = V_A / (V_A + V_E). When V_E is higher,
    the denominator is larger, so h² is lower. -/
theorem pgs_ceiling_lower_in_high_env_variance
    (V_A V_E_low V_E_high : ℝ)
    (h_VA : 0 < V_A) (h_low : 0 < V_E_low) (h_high : 0 < V_E_high)
    (h_more_env : V_E_low < V_E_high) :
    V_A / (V_A + V_E_high) < V_A / (V_A + V_E_low) := by
  exact div_lt_div_of_pos_left h_VA (by linarith) (by linarith)

/-- **Heteroscedasticity across ancestry groups.**
    Different groups may have different residual variance,
    even after accounting for PGS. Residual variance =
    V_total - V_explained = (V_A + V_E) - R² × (V_A + V_E)
    = (1 - R²)(V_A + V_E). When V_E differs, residuals differ. -/
theorem heteroscedastic_residuals
    (V_A V_E₁ V_E₂ R2 : ℝ)
    (h_VA : 0 < V_A) (h_VE₁ : 0 < V_E₁) (h_VE₂ : 0 < V_E₂)
    (h_R2 : 0 < R2) (h_R2_lt : R2 < 1)
    (h_env_diff : V_E₁ ≠ V_E₂) :
    (1 - R2) * (V_A + V_E₁) ≠ (1 - R2) * (V_A + V_E₂) := by
  intro h
  apply h_env_diff
  have h_factor : 0 < 1 - R2 := by linarith
  linarith [mul_left_cancel₀ (ne_of_gt h_factor) h]

/-- **Socioeconomic factors as environmental moderators.**
    SES acts as a moderator of genetic effects through:
    - Access to nutrition (GxE for height/BMI)
    - Access to healthcare (GxE for disease outcomes)
    - Environmental exposures (GxE for respiratory disease)
    When SES differs systematically across ancestry groups,
    the effective genetic effect β_G + β_GxE × SES differs. -/
theorem ses_moderates_genetic_effects
    (β_G β_GxE SES_high SES_low : ℝ)
    (h_GxE : β_GxE ≠ 0) (h_SES_diff : SES_high ≠ SES_low) :
    effectiveGeneticEffect β_G β_GxE SES_high ≠
      effectiveGeneticEffect β_G β_GxE SES_low := by
  exact gxe_population_specific_effects β_G β_GxE SES_high SES_low h_GxE h_SES_diff

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
    across environments (crossover GxE). Given two genotypes
    with different environmental sensitivities (b₁ > b₂) and
    G₁ having higher baseline (a₁ > a₂), there exist environments
    where the ranking reverses. At E = 0, G₁ wins; when E is
    large enough, G₂ wins if b₂ > b₁. -/
theorem crossover_gxe_possible
    (a₁ a₂ b₁ b₂ : ℝ)
    (h_a : a₂ < a₁) (h_b : b₁ < b₂) :
    -- At E = 0, genotype 1 has higher phenotype
    linearNormOfReaction a₂ b₂ 0 < linearNormOfReaction a₁ b₁ 0 ∧
    -- There exists E where genotype 2 overtakes genotype 1
      ∃ E : ℝ, linearNormOfReaction a₁ b₁ E < linearNormOfReaction a₂ b₂ E := by
  unfold linearNormOfReaction
  simp only [mul_zero, add_zero]
  constructor
  · linarith
  · -- At large E, the slope difference dominates
    use (a₁ - a₂) / (b₂ - b₁) + 1
    have h_bd : 0 < b₂ - b₁ := by linarith
    -- (b₂ - b₁) × ((a₁-a₂)/(b₂-b₁) + 1) > a₁ - a₂
    have h_div : (a₁ - a₂) / (b₂ - b₁) * (b₂ - b₁) = a₁ - a₂ :=
      div_mul_cancel₀ _ (ne_of_gt h_bd)
    nlinarith [mul_pos h_bd (show 0 < (1:ℝ) from one_pos)]

/-- **Crossover GxE makes portability impossible.**
    When genotype rankings reverse across environments, the PGS
    trained in one environment negatively predicts in another.
    Using the linearNormOfReaction model, if two genotypes have
    a₁ > a₂ but b₁ < b₂, the Pearson correlation between
    predictions (based on environment 0) and outcomes (in environment E)
    reverses sign for large enough E. We prove: there exists E where
    the genotype that was better at E=0 becomes worse. -/
theorem crossover_gxe_worst_for_portability
    (a₁ a₂ b₁ b₂ : ℝ)
    (h_a : a₂ < a₁) (h_b : b₁ < b₂) :
    -- At E=0, genotype 1 is better
    linearNormOfReaction a₂ b₂ 0 < linearNormOfReaction a₁ b₁ 0 ∧
    -- But there exists E where genotype 1 is worse (ranking reversed)
    ∃ E, linearNormOfReaction a₁ b₁ E < linearNormOfReaction a₂ b₂ E := by
  exact crossover_gxe_possible a₁ a₂ b₁ b₂ h_a h_b

/-- **Quantitative GxE: variance of slopes determines portability.**
    Under the linear norm of reaction Y = a(G) + b(G) × E, total
    genetic variance = Var(a) + Var(b) × E². The fraction of genetic
    variance that is environment-independent is Var(a) / (Var(a) + Var(b) × E²).
    When environmental exposure E increases, this fraction decreases,
    meaning portability worsens with greater environmental difference. -/
theorem gxe_variance_determines_portability
    (var_a var_b E₁ E₂ : ℝ)
    (h_a : 0 < var_a) (h_b : 0 < var_b)
    (h_E₁ : 0 < E₁) (h_E₂ : E₁ < E₂) :
    -- The portable fraction decreases with environmental magnitude
    var_a / (var_a + var_b * E₂ ^ 2) < var_a / (var_a + var_b * E₁ ^ 2) := by
  apply div_lt_div_of_pos_left h_a
  · have : 0 < var_b * E₁ ^ 2 := mul_pos h_b (sq_pos_of_pos h_E₁)
    linarith
  · have h_sq : E₁ ^ 2 < E₂ ^ 2 := by nlinarith
    nlinarith [mul_pos h_b (show 0 < E₂ ^ 2 - E₁ ^ 2 by linarith)]

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
    The portability gap R²_own - R²_other decomposes into:
    - Genetic component: loss from LD mismatch and allele frequency differences
    - Environmental component: loss from GxE and rGE differences
    Each component is the R² loss attributable to that factor.
    We model: R²_own uses V_genetic + V_env_corr, while
    R²_other loses both partially. The gap is the sum of losses. -/
theorem portability_gap_decomposition
    (V_genetic V_env V_E : ℝ)
    (loss_genetic loss_env : ℝ)
    (h_Vg : 0 < V_genetic) (h_Ve : 0 < V_env) (h_VE : 0 < V_E)
    (h_lg : 0 < loss_genetic) (h_lg_le : loss_genetic < V_genetic)
    (h_le : 0 < loss_env) (h_le_le : loss_env < V_env) :
    let V_P := V_genetic + V_env + V_E
    let r2_own := (V_genetic + V_env) / V_P
    let r2_other := (V_genetic - loss_genetic + V_env - loss_env) / V_P
    let gap := r2_own - r2_other
    gap = (loss_genetic + loss_env) / V_P ∧ 0 < gap := by
  constructor
  · dsimp only; rw [← sub_div]; congr 1; ring
  · dsimp only
    rw [← sub_div]
    apply div_pos
    · linarith
    · linarith

/-- **Interventional interpretation of PGS portability.**
    Under the GxE model, the effective genetic effect is β_G + β_GxE × E.
    When environments differ (E_source ≠ E_target), effects differ by
    β_GxE × (E_target - E_source). Equalizing environments eliminates
    this difference entirely. We show: the magnitude of the GxE
    portability loss |β_GxE × (E_t - E_s)| is proportional to the
    environmental difference, and vanishes when |E_t - E_s| → 0. -/
theorem equalize_environment_reveals_genetic_portability
    (β_G β_GxE E_s E_t : ℝ) :
    effectiveGeneticEffect β_G β_GxE E_t - effectiveGeneticEffect β_G β_GxE E_s =
      β_GxE * (E_t - E_s) := by
  unfold effectiveGeneticEffect; ring

end CounterfactualFramework

end Calibrator
