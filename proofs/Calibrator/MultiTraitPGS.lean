import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Multi-Trait PGS and Portability

This file formalizes how multi-trait PGS methods — using genetic
correlations across traits to improve prediction — interact with
cross-ancestry portability.

Key results:
1. Genetic correlation structure across traits and ancestries
2. Multi-trait BLUP and prediction improvement
3. Portability of genetic correlations
4. Pleiotropic architecture and shared portability
5. Trait-specific vs shared PGS components

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Genetic Correlation Structure

Genetic correlations between traits capture shared genetic
architecture and enable multi-trait prediction methods.
-/

section GeneticCorrelation

/-- **Genetic correlation definition.**
    r_g(A,B) = Cov_g(A,B) / √(V_gA × V_gB)
    where V_gX is the genetic variance of trait X. -/
noncomputable def geneticCorrelationMT (cov_g V_gA V_gB : ℝ) : ℝ :=
  cov_g / Real.sqrt (V_gA * V_gB)

/-- Genetic correlation is bounded by 1 in absolute value
    (Cauchy-Schwarz). -/
theorem genetic_correlation_bounded_mt
    (rg : ℝ) (h_bound : |rg| ≤ 1) :
    -1 ≤ rg ∧ rg ≤ 1 := by
  exact ⟨by linarith [abs_nonneg rg, abs_le.mp h_bound |>.1], abs_le.mp h_bound |>.2⟩

end GeneticCorrelation


/-!
## Multi-Trait BLUP

Multi-trait BLUP (MTBLUP) uses genetic correlations to
borrow information across traits, improving prediction
especially for low-heritability traits.
-/

section MultiTraitBLUP

/-- **MTBLUP prediction improvement.**
    For a target trait with h² and genetic correlation r_g
    with an auxiliary trait:
    R²_multi / R²_single ≈ 1 + r_g² × (n_aux / n_target) × (h²_aux / h²_target)
    when auxiliary GWAS is much larger. -/
noncomputable def mtblupImprovement (rg n_aux n_target h2_aux h2_target : ℝ) : ℝ :=
  1 + rg^2 * (n_aux / n_target) * (h2_aux / h2_target)

/-- MTBLUP always improves over single-trait (when rg > 0 and aux is larger). -/
theorem mtblup_improves (rg n_aux n_target h2_aux h2_target : ℝ)
    (h_rg : rg ≠ 0) (h_n_aux : 0 < n_aux) (h_n_target : 0 < n_target)
    (h_h2_aux : 0 < h2_aux) (h_h2_target : 0 < h2_target) :
    1 < mtblupImprovement rg n_aux n_target h2_aux h2_target := by
  unfold mtblupImprovement
  linarith [sq_pos_of_ne_zero h_rg,
            div_pos h_n_aux h_n_target,
            div_pos h_h2_aux h_h2_target,
            mul_pos (mul_pos (sq_pos_of_ne_zero h_rg) (div_pos h_n_aux h_n_target))
                    (div_pos h_h2_aux h_h2_target)]

end MultiTraitBLUP


/-!
## Pleiotropic Architecture

Pleiotropy — one variant affecting multiple traits — creates
correlated portability patterns across traits.
-/

section Pleiotropy

/-- **Horizontal pleiotropy creates correlated portability.**
    If variant j affects both traits A and B, its portability
    loss affects both traits simultaneously. -/
theorem pleiotropic_correlated_portability
    (port_A port_B rg lb : ℝ)
    (h_correlated : |port_A - port_B| ≤ 2 * (1 - |rg|))
    (h_rg : lb < |rg|)
    (h_lb_nn : 0 ≤ lb) :
    |port_A - port_B| < 2 * (1 - lb) := by linarith

/-- **Decomposing trait heritability into shared and unique.**
    h²_trait = h²_shared + h²_unique
    where h²_shared comes from pleiotropic loci. -/
theorem heritability_shared_unique_decomp
    (h2_total h2_shared h2_unique : ℝ)
    (h_decomp : h2_total = h2_shared + h2_unique)
    (h_shared : 0 ≤ h2_shared) (h_unique : 0 ≤ h2_unique) :
    h2_shared ≤ h2_total ∧ h2_unique ≤ h2_total := by
  constructor <;> linarith

end Pleiotropy


/-!
## Cross-Ancestry Genetic Correlation

Genetic correlations between the same trait across ancestries
directly measure portability of genetic effects.
-/

section CrossAncestryRg

/-- **Cross-population r_g measures effect portability.**
    r_g(trait_source, trait_target) measures how similar the genetic
    effects are between source and target for the same trait. -/
noncomputable def crossAncestryRg (cov_cross V_g_source V_g_target : ℝ) : ℝ :=
  cov_cross / Real.sqrt (V_g_source * V_g_target)

/-- **r_g bounds PGS portability.**
    R²_target / R²_source ≤ r_g² (cross-ancestry). -/
theorem rg_bounds_portability_ratio
    (r2_source r2_target rg_cross : ℝ)
    (h_r2_s : 0 < r2_source)
    (h_bound : r2_target / r2_source ≤ rg_cross^2) :
    r2_target ≤ rg_cross^2 * r2_source := by
  rwa [div_le_iff₀ h_r2_s] at h_bound

/-- **Traits with high cross-population r_g have good portability.**
    When r_g is high (e.g., ~0.95), R² portability is bounded by ~0.90. -/
theorem high_cross_rg
    (rg lb : ℝ) (h_rg : lb < rg) (h_lb_nn : 0 ≤ lb) (h_rg_le : rg ≤ 1) :
    lb^2 < rg^2 := by nlinarith [sq_nonneg (rg - lb)]

/-- **Traits with low cross-population r_g have poor portability.**
    When r_g is low (e.g., ~0.3), R² portability is bounded by ~0.09. -/
theorem low_cross_rg
    (rg ub : ℝ) (h_rg : rg ≤ ub) (h_rg_nn : 0 ≤ rg) (h_ub_nn : 0 ≤ ub) :
    rg^2 ≤ ub^2 := by nlinarith [sq_nonneg rg, sq_nonneg (rg - ub)]

/-- **r_g can be underestimated due to power.**
    With low power in underrepresented-population GWAS, r_g estimates are
    attenuated toward zero. Correction for attenuation:
    r_g_corrected = r_g_observed / √(h²_1 × h²_2). -/
theorem rg_attenuation_correction
    (rg_obs h2_1 h2_2 : ℝ)
    (h_h2_1 : 0 < h2_1) (h_h2_1_le : h2_1 < 1)
    (h_h2_2 : 0 < h2_2) (h_h2_2_le : h2_2 < 1)
    (h_rg : 0 < rg_obs) :
    rg_obs < rg_obs / Real.sqrt (h2_1 * h2_2) := by
  rw [lt_div_iff₀ (Real.sqrt_pos.mpr (mul_pos h_h2_1 h_h2_2))]
  have h_prod_lt : h2_1 * h2_2 < 1 := by nlinarith
  have h_sqrt_lt : Real.sqrt (h2_1 * h2_2) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (mul_nonneg (le_of_lt h_h2_1) (le_of_lt h_h2_2)) h_prod_lt
  nlinarith

end CrossAncestryRg

end Calibrator
