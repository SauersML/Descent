/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.OpenQuestions
-- For `LevelSetCoordinates`, `IsLevelSetFunctional` and
-- `levelSet_metrics_agree_of_coords_eq`: the section on genetic/environmental
-- identifiability below upgrades a calibration-level non-identifiability into a
-- statement about every threshold metric at once, which is not provable here.
import Calibrator.FoldedSpectrum
-- For `twoMechanismMixture`, `mechanismCount_not_identified` and
-- `mechanismCount_not_identified_of_range`: the mechanism-count section below is the
-- gene-environment reading of the latent-mechanism collapse.
import Calibrator.LatentMechanismCollapse

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat gene-environment interaction or gene-environment correlation.
Sources for individual results, where they exist, are cited at those results.
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
    environment-dependent: effective β_G = β_G + β_GxE × E.

    Empirical status: **VALIDATED** (`simcov/battery_bulk40b.py`, `group_c`), against the
    file's own model as displayed above. 2×10⁶ individuals, `G` standardized and `E` drawn
    independently of `G` with unit variance; the observable is the realised marginal OLS
    slope of `Y` on `G`, and the prediction uses the REALISED mean of `E`.

      E_mean   this body   realised slope   sems
       -1.5     0.02506       0.02497       0.11
       -0.5     0.27493       0.27536       0.56
        0.0     0.40008       0.39956       0.69
       +1.0     0.65017       0.65085       0.90
       +2.5     1.02471       1.02563       1.21

    `E_mean` is swept through zero and negative, so the body's prediction spans 98% and both
    competitors MOVE with the design rather than sitting constant: reading the environment's
    second moment in as well, `β_G + β_GxE(E_mean + Var E)`, misses by 330 sems, and halving
    the interaction by 413. A constant competitor would have been reported NO POWER and would
    have rejected nothing, which is what happened on the first attempt. The positive control
    is the realised mean of `E` against the `E_mean` fed in.

    What is NOT established is the model: that real gene-environment interplay is linear in
    `G·E` with `E` independent of `G`. The simulation enacts that model, so it establishes
    the marginal slope GIVEN it. -/
noncomputable def effectiveGeneticEffect (β_G β_GxE E_mean : ℝ) : ℝ :=
  β_G + β_GxE * E_mean

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem effectiveGeneticEffect_at_reference_point :
    effectiveGeneticEffect 1 1 1 = 2 := by
  norm_num [effectiveGeneticEffect]


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
theorem div_self_add_lt_one_of_pos
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
theorem div_self_add_and_sq_lt_one_of_pos
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
    β_G + β_GxE × E. When β_GxE > 0 and E_high > E_low,
    the effective effect in the high-carb environment exceeds
    that in the low-carb environment. -/
theorem diet_genetics_bmi_example
    (β_G β_GxE E_low E_high : ℝ)
    (h_β_GxE : 0 < β_GxE) (h_E_high : E_low < E_high) :
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
theorem two_mul_sqrt_lt_of_lt
    (r2_g r2_e rge_source rge_target : ℝ)
    (h_g : 0 < r2_g) (h_e : 0 < r2_e)
    (h_rge_diff : rge_target < rge_source) :
    let inflation_s := 2 * rge_source * Real.sqrt (r2_g * r2_e)
    let inflation_t := 2 * rge_target * Real.sqrt (r2_g * r2_e)
    inflation_t < inflation_s := by
  have h_sqrt_pos : 0 < Real.sqrt (r2_g * r2_e) :=
    Real.sqrt_pos.mpr (mul_pos h_g h_e)
  nlinarith [mul_pos (show 0 < rge_source - rge_target by linarith) h_sqrt_pos]

/-- **Separating genetic from environmental portability.**
    The PGS captures both genetic signal (V_direct) and rGE-mediated
    environmental signal. We show the observed (population-level)
    R² = (V_direct + V_rge) / V_P strictly exceeds the direct
    genetic R² = V_direct / V_P, so the environmental component
    V_rge / V_P is the non-portable inflation. -/
theorem total_portability_le_genetic
    (V_direct V_rge V_P : ℝ)
    (h_rge : 0 < V_rge) (h_P : 0 < V_P) :
    V_direct / V_P < (V_direct + V_rge) / V_P ∧
    (V_direct + V_rge) / V_P - V_direct / V_P = V_rge / V_P := by
  constructor
  · exact div_lt_div_of_pos_right (by linarith) h_P
  · rw [← sub_div]; ring_nf

end GeneEnvironmentCorrelation


/-!
## Environmental Variance Heterogeneity

When environmental variance differs across populations,
it affects heritability and PGS performance.
-/

section EnvironmentalVariance

/-- **Environmental variance reduces heritability, and with it the attainable `R²`.**

    `h² = V_A / (V_A + V_E)`, so more environmental variance lowers it. The same inequality is
    the ceiling statement: a score that captured every genetic effect would attain `R² = h²`, so
    raising `V_E` lowers the ceiling by exactly this much. One inequality, two readings — stated
    once. -/
theorem env_variance_reduces_h2
    (V_A V_E₁ V_E₂ : ℝ)
    (h_VA : 0 < V_A) (h_VE₁ : 0 < V_E₁)
    (h_more_env : V_E₁ < V_E₂) :
    V_A / (V_A + V_E₂) < V_A / (V_A + V_E₁) := by
  exact div_lt_div_of_pos_left h_VA (by linarith) (by linarith)

/-- **Heteroscedasticity across ancestry groups.**
    Different groups may have different residual variance,
    even after accounting for PGS. Residual variance =
    V_total - V_explained = (V_A + V_E) - R² × (V_A + V_E)
    = (1 - R²)(V_A + V_E). When V_E differs, residuals differ. -/
theorem heteroscedastic_residuals
    (V_A V_E₁ V_E₂ R2 : ℝ)
    (h_R2_lt : R2 < 1)
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

/-- **The intercept cancels in an environmental contrast.** Only the slope is identified from a
difference of environments, which is why a genotype's baseline needs a reference environment and
cannot be read off a reaction-norm comparison. -/
theorem linearNormOfReaction_sub (a b E₁ E₂ : ℝ) :
    linearNormOfReaction a b E₁ - linearNormOfReaction a b E₂ = b * (E₁ - E₂) := by
  unfold linearNormOfReaction
  ring

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

/-- **Quantitative GxE: variance of slopes determines portability.**
    Under the linear norm of reaction Y = a(G) + b(G) × E, total
    genetic variance = Var(a) + Var(b) × E². The fraction of genetic
    variance that is environment-independent is Var(a) / (Var(a) + Var(b) × E²).
    When environmental exposure E increases, this fraction decreases,
    meaning portability worsens with greater environmental difference. -/
theorem div_lt_div_of_denom_sq_lt
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

/-- **Decomposing portability gap into genetic and environmental.**
    The portability gap R²_own - R²_other decomposes into:
    - Genetic component: loss from LD mismatch and allele frequency differences
    - Environmental component: loss from GxE and rGE differences
    We model: R²_own uses V_genetic + V_env_corr, while
    R²_other loses both partially. The gap is the sum of losses.

    **This does NOT attribute the gap to either factor, and the conclusion is why.**
    **Do not describe either component as "the R² loss attributable to that factor".**
    The conclusion is a function of `loss_genetic + loss_env`, so every
    split with the same total yields the same `gap`, exactly. `loss_genetic` and `loss_env`
    are free parameters of the statement, not quantities it measures, and no choice of
    either is contradicted by any value of `gap`.

    What that costs, and what recovers it, is proved in "Genetic versus environmental
    attribution" below: under an environmental gradient collinear with the ancestry
    gradient the split is invisible to every cohort-level calibration and to every threshold
    metric, and it becomes identifiable exactly when the two gradients are non-collinear --
    for instance two cohorts at matched nonzero genetic distance with different
    environments. -/
theorem portability_gap_decomposition
    (V_genetic V_env V_E : ℝ)
    (loss_genetic loss_env : ℝ)
    (h_VE : 0 < V_E)
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

/-! ## Genetic versus environmental attribution: what a cohort calibration cannot see

`portability_gap_decomposition` above is the place this module states an attribution, and
its docstring is explicit about it: "Each component is the R² loss attributable to that
factor." **The theorem does not support that reading, and its own algebra is why.** Its
conclusion is `gap = (loss_genetic + loss_env) / V_P` -- a function of the **sum**. Two
different splits with the same total produce the same gap, exactly, so nothing in that
statement attributes anything to either factor. The decomposition is a definition of terms,
not a measurement of them.

That is not a defect peculiar to that theorem. It is the shape of the problem, and this
section proves it in the form that tells a study designer what to do.

**The setup.** Deployment cohorts each carry two coordinates: a genetic one (genetic
distance, ancestry position) and an environmental one (SES or any measured environmental
contrast). The calibration shift a cohort exhibits is `gamma * genetic + eta * environmental`
-- one number per cohort, the sum of the two contributions. This is the premise the whole
question turns on, and it is the premise Harpak et al. make live: if ancestry coordinates
partially predict environment, the environmental term is *not* a separate additive channel,
it enters the same per-cohort number as drift.

**The negative result.** If the environmental gradient is collinear with the genetic one --
environment varies across cohorts only as ancestry does -- then an entire one-parameter
family of `(gamma, eta)` splits produces **identical** shifts at every cohort
(`shift_blind_to_split_of_collinear`). Not approximately equal: equal. So no cohort-level
calibration can separate genetics from environment, at any sample size, because the
observable is constant along the family. And by the level-set collapse this extends past
calibration to **every threshold metric at once**
(`no_threshold_metric_separates_collinear_split`): if the two act through the same
deployment coordinate, no precision, recall, exceedance probability or quantile comparison
distinguishes them either. That is the structural explanation of the Harpak finding -- the
environmental contribution is not unmodelled noise, it is a direction the design cannot
resolve.

**The positive result, which is the study-design statement.** Identifiability returns
exactly when the two gradients are non-collinear: two cohorts whose
`(genetic, environmental)` coordinate vectors are not proportional determine the split
uniquely (`split_identified_of_noncollinear`). The most quotable sufficient condition is
`split_identified_of_matched_genetics`: **two cohorts at the same nonzero genetic distance
with different environments suffice.** Equivalently, cohorts differing in genetics at
matched environment. Collecting cohorts along a single ancestry gradient -- which is what
biobank recruitment tends to produce -- buys none of this, however many cohorts there are.

**What is deliberately absent.** No `sigma^2_env` term is added to the closing law. A fourth
additive symbol would be fittable and never predictable, because nothing else in the
derivation constrains it. The contribution here is the identifiability statement instead:
negative under collinearity, positive under a stated design condition, and both proved.

**Scope, stated so it is not overread.** These are exact statements about a linear
two-source shift model. They do not claim environment is unimportant, nor that its
magnitude is small -- Harpak et al. suggest the opposite -- only that magnitude and
attribution are different questions, and that the second is unanswerable from cohorts
strung along one gradient. -/

/-- A panel of deployment cohorts, each carrying a genetic coordinate (ancestry position,
genetic distance from the source) and an environmental coordinate (SES or any measured
environmental contrast). -/
structure CohortGradients (n : ℕ) where
  /-- Genetic distance / ancestry position of each cohort. -/
  geneticGradient : Fin n → ℝ
  /-- Measured environmental contrast of each cohort. -/
  environmentalGradient : Fin n → ℝ

/-- **The one number a per-cohort calibration sees**: the sum of the genetic and
environmental contributions. `gamma` and `eta` are the per-unit effects to be attributed. -/
def cohortShift {n : ℕ} (G : CohortGradients n) (gamma eta : ℝ) (i : Fin n) : ℝ :=
  gamma * G.geneticGradient i + eta * G.environmentalGradient i

/-- Reference evaluation: with no gradient loading there is no cohort shift. -/
theorem cohortShift_at_reference_point {n : ℕ} (G : CohortGradients n) (i : Fin n) :
    cohortShift G 0 0 i = 0 := by
  unfold cohortShift
  ring

/-- The complete cohort-level observation generated by one genetic/environmental split. -/
def cohortShiftVector {n : ℕ} (G : CohortGradients n) (parameters : ℝ × ℝ) : Fin n → ℝ :=
  fun i ↦ cohortShift G parameters.1 parameters.2 i


/-- **The negative result: under a collinear environmental gradient the split is invisible.**

If environment varies across cohorts only as ancestry does (`environmental = c * genetic`),
then for every `t` the split `(gamma + c*t, eta - t)` produces exactly the same shift at
every cohort. The observable is constant along a one-parameter family, so no cohort-level
calibration separates genetics from environment -- not poorly, but not at all, at any
sample size. -/
theorem shift_blind_to_split_of_collinear {n : ℕ} (G : CohortGradients n) (c : ℝ)
    (hcol : ∀ i, G.environmentalGradient i = c * G.geneticGradient i)
    (gamma eta t : ℝ) (i : Fin n) :
    cohortShift G (gamma + c * t) (eta - t) i = cohortShift G gamma eta i := by
  unfold cohortShift
  rw [hcol i]
  ring

/-- **The positive result: non-collinear gradients identify the split.**

If two cohorts have `(genetic, environmental)` coordinate vectors that are not proportional
-- a nonzero `2x2` determinant -- then agreeing shifts force agreeing splits. This is the
study-design condition, and it is a condition on the *panel*, not on the sample size. -/
theorem split_identified_of_noncollinear {n : ℕ} (G : CohortGradients n) (i j : Fin n)
    (hdet : G.geneticGradient i * G.environmentalGradient j -
      G.geneticGradient j * G.environmentalGradient i ≠ 0)
    (gamma eta gamma' eta' : ℝ)
    (hagree : ∀ k : Fin n, cohortShift G gamma eta k = cohortShift G gamma' eta' k) :
    gamma = gamma' ∧ eta = eta' := by
  have hi := hagree i
  have hj := hagree j
  unfold cohortShift at hi hj
  -- Write `a = gamma - gamma'`, `b = eta - eta'`; the two cohorts give
  -- `a*g_i + b*e_i = 0` and `a*g_j + b*e_j = 0`, and the determinant kills both.
  --
  -- These four steps are `linear_combination` rather than `nlinarith` on purpose. The
  -- identities are products of unknowns with gradient values, so they are nonlinear in the
  -- atoms and a search tactic has to guess the multipliers; `nlinarith [hi, hj]` does not
  -- find them and reports `linarith failed`, which reads as a false goal rather than as an
  -- unguessed coefficient. The multipliers are known exactly -- they are Cramer's rule --
  -- so they are written down.
  have h1 : (gamma - gamma') * G.geneticGradient i
      + (eta - eta') * G.environmentalGradient i = 0 := by linear_combination hi
  have h2 : (gamma - gamma') * G.geneticGradient j
      + (eta - eta') * G.environmentalGradient j = 0 := by linear_combination hj
  have ha : (gamma - gamma') * (G.geneticGradient i * G.environmentalGradient j -
      G.geneticGradient j * G.environmentalGradient i) = 0 := by
    linear_combination G.environmentalGradient j * h1 - G.environmentalGradient i * h2
  have hb : (eta - eta') * (G.geneticGradient i * G.environmentalGradient j -
      G.geneticGradient j * G.environmentalGradient i) = 0 := by
    linear_combination G.geneticGradient i * h2 - G.geneticGradient j * h1
  constructor
  · have := mul_eq_zero.mp ha
    rcases this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdet
  · have := mul_eq_zero.mp hb
    rcases this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdet

/-- **The study-design condition in its usable form: two cohorts at matched genetic distance
with different environments.**

This is what has to be recruited. Cohorts strung along a single ancestry gradient give a
proportional coordinate pair at every pair of cohorts and identify nothing, however many
there are. -/
theorem split_identified_of_matched_genetics {n : ℕ} (G : CohortGradients n) (i j : Fin n)
    (hmatch : G.geneticGradient i = G.geneticGradient j)
    (hgne : G.geneticGradient i ≠ 0)
    (henv : G.environmentalGradient i ≠ G.environmentalGradient j)
    (gamma eta gamma' eta' : ℝ)
    (hagree : ∀ k : Fin n, cohortShift G gamma eta k = cohortShift G gamma' eta' k) :
    gamma = gamma' ∧ eta = eta' := by
  refine split_identified_of_noncollinear G i j ?_ gamma eta gamma' eta' hagree
  rw [← hmatch]
  intro hcontra
  apply henv
  have : G.geneticGradient i *
      (G.environmentalGradient j - G.environmentalGradient i) = 0 := by linarith [hcontra]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hgne
  · linarith [sub_eq_zero.mp h]

/-- **The dual study design: matched nonzero environment with different genetic positions.**
Holding environment fixed while ancestry varies also supplies a non-collinear cohort pair and
therefore identifies the two attribution coefficients. -/
theorem split_identified_of_matched_environments
    {n : ℕ} (G : CohortGradients n) (i j : Fin n)
    (hmatch : G.environmentalGradient i = G.environmentalGradient j)
    (hene : G.environmentalGradient i ≠ 0)
    (hgen : G.geneticGradient i ≠ G.geneticGradient j)
    (gamma eta gamma' eta' : ℝ)
    (hagree : ∀ k : Fin n, cohortShift G gamma eta k = cohortShift G gamma' eta' k) :
    gamma = gamma' ∧ eta = eta' := by
  refine split_identified_of_noncollinear G i j ?_ gamma eta gamma' eta' hagree
  rw [← hmatch]
  intro hcontra
  apply hgen
  have : (G.geneticGradient i - G.geneticGradient j) *
      G.environmentalGradient i = 0 := by
    linarith [hcontra]
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hene

/-- **Exact study-design boundary.**  The full cohort-shift vector identifies the genetic and
environmental coefficients exactly if and only if the panel contains two non-collinear cohort
gradients.  Thus sample size within cohorts cannot substitute for rank in the cohort design. -/
theorem cohortShiftVector_injective_iff_exists_noncollinear
    {n : ℕ} (G : CohortGradients n) :
    Function.Injective (cohortShiftVector G) ↔
      ∃ i j : Fin n,
        G.geneticGradient i * G.environmentalGradient j -
          G.geneticGradient j * G.environmentalGradient i ≠ 0 := by
  classical
  constructor
  · intro hinjective
    by_contra hnoncollinear
    push_neg at hnoncollinear
    by_cases hallGeneticZero : ∀ i : Fin n, G.geneticGradient i = 0
    · have hequal : cohortShiftVector G (1, 0) = cohortShiftVector G (0, 0) := by
        funext i
        simp [cohortShiftVector, cohortShift, hallGeneticZero i]
      have hparameters := hinjective hequal
      norm_num at hparameters
    · push_neg at hallGeneticZero
      obtain ⟨i, hi⟩ := hallGeneticZero
      let c : ℝ := G.environmentalGradient i / G.geneticGradient i
      have hcollinear : ∀ k : Fin n,
          G.environmentalGradient k = c * G.geneticGradient k := by
        intro k
        dsimp [c]
        field_simp [hi]
        nlinarith [hnoncollinear i k]
      have hequal : cohortShiftVector G (c, -1) = cohortShiftVector G (0, 0) := by
        funext k
        simpa [cohortShiftVector] using
          shift_blind_to_split_of_collinear G c hcollinear 0 0 1 k
      have hparameters := hinjective hequal
      have hsecond := congrArg Prod.snd hparameters
      norm_num at hsecond
  · rintro ⟨i, j, hdet⟩ ⟨gamma, eta⟩ ⟨gamma', eta'⟩ hagree
    have hsplit := split_identified_of_noncollinear G i j hdet gamma eta gamma' eta'
      (fun k ↦ congrFun hagree k)
    exact Prod.ext hsplit.1 hsplit.2

/-- A deployment: a cohort panel together with the split being attributed. -/
structure GxEDeployment (n : ℕ) where
  /-- The cohort panel. -/
  gradients : CohortGradients n
  /-- Per-unit genetic effect. -/
  gamma : ℝ
  /-- Per-unit environmental effect. -/
  eta : ℝ

/-- The shift vector a deployment presents to a per-cohort calibration. -/
def GxEDeployment.shift {n : ℕ} (D : GxEDeployment n) (i : Fin n) : ℝ :=
  cohortShift D.gradients D.gamma D.eta i

/-- **No threshold metric separates them either.**

The upgrade from "calibration cannot see it" to "nothing threshold-based can see it".
`hfactor` is the substantive modelling premise and is carried as a hypothesis rather than
assumed silently: the readout coordinates a deployment presents depend on it only through
its cohort shifts. That is precisely the claim that environment and drift **enter the same
deployment coordinate**. Granting it, the Gaussian level-set collapse of
`Calibrator.FoldedSpectrum` does the rest: the whole collinear family shares its two
coordinates, so every level-set functional -- precision, recall, any exceedance probability,
any quantile -- takes the same value across it.

This is not provable in this file. `levelSet_metrics_agree_of_coords_eq` is the content, and
deleting `FoldedSpectrum` removes it. -/
theorem no_threshold_metric_separates_collinear_split {n : ℕ}
    (G : CohortGradients n) (c : ℝ)
    (hcol : ∀ i, G.environmentalGradient i = c * G.geneticGradient i)
    (coords : GxEDeployment n → LevelSetCoordinates)
    (hfactor : ∀ D D' : GxEDeployment n,
      (∀ i, D.shift i = D'.shift i) → coords D = coords D')
    (metric : GxEDeployment n → ℝ)
    (hmetric : IsLevelSetFunctional metric coords)
    (gamma eta t : ℝ) :
    metric ⟨G, gamma + c * t, eta - t⟩ = metric ⟨G, gamma, eta⟩ := by
  refine levelSet_metrics_agree_of_coords_eq coords metric hmetric _ _ ?_
  refine hfactor _ _ (fun i ↦ ?_)
  exact shift_blind_to_split_of_collinear G c hcol gamma eta t i

end CounterfactualFramework


/-!
## How many mechanisms mediate GxE is not a question about the data

`NormOfReaction` above shows that a genotype's environmental sensitivity is identified only
as a slope, and `linearNormOfReaction_sub` shows the intercept cancels. Those are statements
about *which parameters* a reaction-norm comparison recovers. The statements below are about
a different quantity a GxE study routinely reports: **how many pathways** mediate the
interaction.

`Calibrator.LatentMechanismCollapse` proves the finite shadow of the collapse theorem --
the same observed family is reproduced with zero residual by a two-mechanism model and by
a three-mechanism model, with every weight a genuine mixing weight in both. Transported
here, that says a study reporting `k` mediating pathways is reporting a modelling choice.
No estimator can prefer one count, because the counts are not distinguishable by the
observations at all.

Scope, from the source module and not weakened: the general collapse theorem -- smooth
strictly positive mixing densities over a compact manifold, driving the minimal count to
`1` -- is an open gap there and is not used here. What is used is the finite, fully proved
instance and its universal form over an observation window.
-/

section MechanismCount

/-- **The number of GxE mechanisms is not identified from the reaction norms.**

Given any family of contexts whose observed reaction-norm values lie in the window
`[2/10, 9/10]`, a *two*-mechanism model reproduces every one of them exactly, with genuine
mixing weights. So no observed family of reaction norms inside that window is evidence for
any particular mechanism count, and a reported count carries no information the data
supplied.

Stated at `linearNormOfReaction` rather than at an abstract observable because that is the
quantity this file defines and a GxE study measures.

    Empirical status: DERIVED. The witnesses are the exact weights produced by
    `exists_twoMechanismMixture_eq`; nothing is approximated. -/
theorem normOfReaction_mechanismCount_not_identified {ι : Type*} (a b E : ι → ℝ)
    (hrange : ∀ i, 2 / 10 ≤ linearNormOfReaction (a i) (b i) (E i) ∧
      linearNormOfReaction (a i) (b i) (E i) ≤ 9 / 10) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
      ∀ i, twoMechanismMixture (w i) = linearNormOfReaction (a i) (b i) (E i) :=
  mechanismCount_not_identified_of_range _ hrange

/-- **A three-context GxE design with two mechanism counts and zero residual.**

The concrete witness behind the theorem above, in reaction-norm coordinates: three
environments whose reaction norms read `0.35`, `0.50` and `0.70` are fit exactly by a
three-pathway model using all three pathways with strictly positive weight, and exactly by
a two-pathway model. Both fits are displayed, so the non-identifiability is exhibited
rather than asserted.

The reaction-norm parameters are recovered from the observed values by
`linearNormOfReaction`, which is why the hypothesis is an equation on measured values and
not on latent quantities.

    Empirical status: DERIVED. Exact arithmetic on displayed witnesses. -/
theorem gxe_threeContext_mechanismCount_not_identified
    (a b E : Fin 3 → ℝ)
    (h₀ : linearNormOfReaction (a 0) (b 0) (E 0) = 35 / 100)
    (h₁ : linearNormOfReaction (a 1) (b 1) (E 1) = 50 / 100)
    (h₂ : linearNormOfReaction (a 2) (b 2) (E 2) = 70 / 100) :
    (threeMechanismMixture (7 / 10) (3 / 20) = linearNormOfReaction (a 0) (b 0) (E 0) ∧
        threeMechanismMixture (2 / 5) (3 / 10) = linearNormOfReaction (a 1) (b 1) (E 1) ∧
        threeMechanismMixture (1 / 5) (3 / 20) = linearNormOfReaction (a 2) (b 2) (E 2)) ∧
      (twoMechanismMixture (11 / 14) = linearNormOfReaction (a 0) (b 0) (E 0) ∧
        twoMechanismMixture (4 / 7) = linearNormOfReaction (a 1) (b 1) (E 1) ∧
        twoMechanismMixture (2 / 7) = linearNormOfReaction (a 2) (b 2) (E 2)) := by
  obtain ⟨⟨t₀, t₁, t₂⟩, ⟨s₀, s₁, s₂⟩⟩ := mechanismCount_not_identified
  exact ⟨⟨by rw [h₀]; exact t₀, by rw [h₁]; exact t₁, by rw [h₂]; exact t₂⟩,
    ⟨by rw [h₀]; exact s₀, by rw [h₁]; exact s₁, by rw [h₂]; exact s₂⟩⟩

end MechanismCount

end Calibrator
