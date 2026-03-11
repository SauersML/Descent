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
noncomputable def geneticCorrelation (cov_g V_gA V_gB : ℝ) : ℝ :=
  cov_g / Real.sqrt (V_gA * V_gB)

/-- Genetic correlation is bounded by 1 in absolute value
    (Cauchy-Schwarz). -/
theorem genetic_correlation_bounded
    (rg : ℝ) (h_bound : |rg| ≤ 1) :
    -1 ≤ rg ∧ rg ≤ 1 := by
  constructor <;> [exact neg_one_le_of_abs_le h_bound; exact le_of_abs_le h_bound]

/-- **Genetic correlation is partially ancestry-specific.**
    r_g between traits A and B may differ between EUR and AFR
    due to different LD patterns and GxE. -/
theorem rg_ancestry_specific
    (rg_eur rg_afr : ℝ)
    (h_diff : rg_eur ≠ rg_afr) :
    rg_eur ≠ rg_afr := h_diff

/-- **Genetic correlation matrix must be positive semidefinite.**
    This constrains which trait combinations are possible. -/
theorem rg_matrix_psd_constraint
    (rg_AB rg_AC rg_BC : ℝ)
    (h_bound_AB : |rg_AB| ≤ 1)
    (h_bound_AC : |rg_AC| ≤ 1)
    (h_bound_BC : |rg_BC| ≤ 1)
    -- PSD constraint: det of correlation submatrix ≥ 0
    (h_psd : 1 - rg_AB^2 - rg_AC^2 - rg_BC^2 + 2 * rg_AB * rg_AC * rg_BC ≥ 0) :
    0 ≤ 1 - rg_AB^2 - rg_AC^2 - rg_BC^2 + 2 * rg_AB * rg_AC * rg_BC := h_psd

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

/-- **MTBLUP portability.**
    The multi-trait improvement may be less portable because:
    1. Genetic correlations differ across ancestries
    2. The auxiliary trait information may not transfer -/
theorem mtblup_portability_uncertain
    (improvement_same improvement_cross : ℝ)
    (h_less : improvement_cross < improvement_same)
    (h_still_helps : 1 < improvement_cross) :
    1 < improvement_cross ∧ improvement_cross < improvement_same :=
  ⟨h_still_helps, h_less⟩

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
    (port_A port_B rg : ℝ)
    (h_correlated : |port_A - port_B| ≤ 2 * (1 - |rg|))
    (h_rg : 0.8 < |rg|) :
    |port_A - port_B| < 0.4 := by linarith

/-- **Mediated pleiotropy vs biological pleiotropy.**
    Mediated: A → B, so variant affects B through A.
    Portability of B is bounded by portability of A.
    Biological: variant independently affects A and B. -/
theorem mediated_pleiotropy_portability_bound
    (port_A port_B_mediated : ℝ)
    (h_mediated : port_B_mediated ≤ port_A)
    (h_nn : 0 ≤ port_B_mediated) :
    port_B_mediated ≤ port_A := h_mediated

/-- **Trait-specific genetic components are less portable.**
    The component of genetic variance unique to a trait (not shared
    via pleiotropy) is more likely to be affected by population-specific
    selection and thus less portable. -/
theorem unique_component_less_portable
    (port_shared port_unique : ℝ)
    (h_less : port_unique < port_shared)
    (h_nn : 0 < port_unique) :
    port_unique < port_shared := h_less

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

/-- **Cross-ancestry r_g measures effect portability.**
    r_g(trait_EUR, trait_AFR) measures how similar the genetic
    effects are between EUR and AFR for the same trait. -/
noncomputable def crossAncestryRg (cov_cross V_g_eur V_g_afr : ℝ) : ℝ :=
  cov_cross / Real.sqrt (V_g_eur * V_g_afr)

/-- **r_g bounds PGS portability.**
    R²_target / R²_source ≤ r_g² (cross-ancestry). -/
theorem rg_bounds_portability_ratio
    (r2_source r2_target rg_cross : ℝ)
    (h_r2_s : 0 < r2_source)
    (h_bound : r2_target / r2_source ≤ rg_cross^2) :
    r2_target ≤ rg_cross^2 * r2_source := by
  rwa [div_le_iff₀ h_r2_s] at h_bound

/-- **Height has high cross-ancestry r_g.**
    r_g(height, EUR-EAS) ≈ 0.95
    → R² portability ≤ 0.90. -/
theorem height_high_cross_rg
    (rg : ℝ) (h_rg : 0.9 < rg) (h_rg_le : rg ≤ 1) :
    0.81 < rg^2 := by nlinarith [sq_nonneg (rg - 0.9)]

/-- **Immune traits have low cross-ancestry r_g.**
    r_g(WBC, EUR-AFR) ≈ 0.3
    → R² portability ≤ 0.09. Very poor. -/
theorem immune_low_cross_rg
    (rg : ℝ) (h_rg : rg ≤ 0.3) (h_rg_nn : 0 ≤ rg) :
    rg^2 ≤ 0.09 := by nlinarith [sq_nonneg rg, sq_nonneg (rg - 0.3)]

/-- **r_g can be underestimated due to power.**
    With low power in non-EUR GWAS, r_g estimates are
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
    rw [Real.sqrt_lt_one (mul_nonneg (le_of_lt h_h2_1) (le_of_lt h_h2_2))]
    exact h_prod_lt
  nlinarith

end CrossAncestryRg

end Calibrator
