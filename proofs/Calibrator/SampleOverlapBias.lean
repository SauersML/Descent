import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Sample Overlap Bias in PGS Evaluation

This file formalizes how overlap between discovery GWAS and
validation samples creates upward bias in PGS R² estimates.
This bias interacts with portability assessment in subtle ways.

Key results:
1. Overfitting from sample overlap inflates R²
2. The inflation depends on sample sizes and trait architecture
3. Independent validation eliminates overlap bias
4. Cross-ancestry evaluation naturally avoids overlap
5. Leave-one-out and jackknife corrections

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Overlap-Induced R² Inflation

When the validation sample partially overlaps with the discovery
GWAS, the PGS R² is inflated because the PGS partially memorizes
individual-level noise.
-/

section OverlapInflation

/-- **R² inflation from complete overlap.**
    If the validation sample IS the discovery sample,
    the apparent R² converges to h²_SNP (not R²_PGS).
    Inflation = h²_SNP / R²_true_PGS - 1. -/
noncomputable def overlapInflation (r2_true r2_observed : ℝ) : ℝ :=
  r2_observed / r2_true - 1

/-- Inflation is positive when observed exceeds true. -/
theorem overlap_inflation_positive (r2_true r2_observed : ℝ)
    (h_true : 0 < r2_true) (h_inflated : r2_true < r2_observed) :
    0 < overlapInflation r2_true r2_observed := by
  unfold overlapInflation
  rw [sub_pos, one_lt_div₀ h_true]
  exact h_inflated

/-- **Partial overlap inflation.**
    With fraction f of validation in discovery:
    R²_observed ≈ R²_true + f × (h² - R²_true) / n_GWAS.
    The inflation is proportional to f. -/
noncomputable def partialOverlapR2 (r2_true h2 : ℝ) (f : ℝ) (n_gwas : ℕ) : ℝ :=
  r2_true + f * (h2 - r2_true) / n_gwas

/-- Zero overlap gives unbiased estimate. -/
theorem no_overlap_unbiased (r2_true h2 : ℝ) (n_gwas : ℕ) :
    partialOverlapR2 r2_true h2 0 n_gwas = r2_true := by
  unfold partialOverlapR2; ring

/-- More overlap → more inflation (when h² > R²_true). -/
theorem more_overlap_more_inflation (r2_true h2 f₁ f₂ : ℝ) (n_gwas : ℕ)
    (h_h2 : r2_true < h2) (h_n : 0 < n_gwas)
    (h_f : f₁ < f₂) :
    partialOverlapR2 r2_true h2 f₁ n_gwas <
      partialOverlapR2 r2_true h2 f₂ n_gwas := by
  unfold partialOverlapR2
  have h_diff : 0 < h2 - r2_true := by linarith
  have h_cast : (0 : ℝ) < ↑n_gwas := Nat.cast_pos.mpr h_n
  have : f₁ * (h2 - r2_true) / ↑n_gwas < f₂ * (h2 - r2_true) / ↑n_gwas :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h_f h_diff) h_cast
  linarith

/-- **Inflation decreases with GWAS sample size.**
    Larger GWAS → less overfitting → less inflation. -/
theorem inflation_decreases_with_gwas_n (r2_true h2 f : ℝ) (n₁ n₂ : ℕ)
    (h_h2 : r2_true < h2) (h_f : 0 < f)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂) (h_n : n₁ < n₂) :
    partialOverlapR2 r2_true h2 f n₂ <
      partialOverlapR2 r2_true h2 f n₁ := by
  unfold partialOverlapR2
  have h_diff : 0 < h2 - r2_true := by linarith
  have h₁ : (0 : ℝ) < n₁ := Nat.cast_pos.mpr h_n₁
  have h₂ : (0 : ℝ) < n₂ := Nat.cast_pos.mpr h_n₂
  linarith [div_lt_div_iff_of_pos_left (mul_pos h_f h_diff) h₂ h₁ |>.mpr (Nat.cast_lt.mpr h_n)]

end OverlapInflation


/-!
## Cross-Ancestry Evaluation Avoids Overlap

Cross-ancestry PGS evaluation naturally avoids sample overlap
because discovery and target samples are from different populations.
-/

section CrossAncestryNoOverlap

/-- **Same-ancestry R² is inflated relative to cross-ancestry.**
    Some apparent portability loss is actually the absence of
    overlap inflation in the cross-ancestry estimate. -/
theorem apparent_portability_loss_includes_overlap
    (r2_same_with_overlap r2_same_true r2_cross : ℝ)
    (h_overlap : r2_same_true < r2_same_with_overlap)
    (h_real_gap : r2_cross < r2_same_true) :
    r2_cross < r2_same_with_overlap ∧
    r2_same_with_overlap - r2_cross > r2_same_true - r2_cross := by
  constructor
  · linarith
  · linarith

end CrossAncestryNoOverlap


/-!
## Leave-One-Out Corrections

Methods to remove overlap bias without requiring fully
independent samples.
-/

section LOOCorrections

/- **Leave-one-out PGS.**
    For each individual i, compute PGS using GWAS that
    excludes individual i. This eliminates overfitting
    but is computationally expensive. -/

/-- **Approximate LOO using linear algebra.**
    PGS_LOO_i ≈ PGS_full_i - leverage_i × residual_i
    where leverage_i = X_i'(X'X)⁻¹X_i. -/
noncomputable def approxLOOPGS (pgs_full leverage residual : ℝ) : ℝ :=
  pgs_full - leverage * residual

/-- LOO correction reduces the PGS when leverage and residual
    have the same sign (overfitting case). -/
theorem loo_reduces_overfitting
    (pgs_full leverage residual : ℝ)
    (h_lev : 0 < leverage) (h_res : 0 < residual) :
    approxLOOPGS pgs_full leverage residual < pgs_full := by
  unfold approxLOOPGS; linarith [mul_pos h_lev h_res]

/-- **Jackknife correction for R².**
    R²_corrected = R²_full - (n-1)/n × Σ (R²_full - R²_{-block})
    where blocks are non-overlapping subsets of samples. -/
noncomputable def jackknifeR2 (r2_full jackknife_bias : ℝ) : ℝ :=
  r2_full - jackknife_bias

/-- Jackknife correction reduces R² when bias is positive. -/
theorem jackknife_reduces_r2 (r2_full bias : ℝ)
    (h_bias : 0 < bias) :
    jackknifeR2 r2_full bias < r2_full := by
  unfold jackknifeR2; linarith

/-- **GWAS-by-subtraction.**
    Run GWAS twice: once with all samples, once without
    validation samples. Use the difference to estimate
    the overlap bias. -/
theorem gwas_subtraction_estimates_bias
    (r2_full r2_excl r2_true overlap_bias : ℝ)
    (h_full : r2_full = r2_true + overlap_bias)
    (h_excl : r2_excl = r2_true)
    (h_bias : 0 < overlap_bias) :
    r2_full - r2_excl = overlap_bias := by linarith

end LOOCorrections


/-!
## Relatedness and Cryptic Overlap

Cryptic relatedness between discovery and validation creates
a more subtle form of overlap bias that is harder to detect.
-/

section CrypticRelatedness

/-- **Kinship-based inflation.**
    If individuals in validation are related to those in discovery
    (kinship coefficient K), the PGS benefits from shared
    family-level environment and rare genetic variants. -/
noncomputable def kinshipInflation (r2_true K h2_family : ℝ) : ℝ :=
  r2_true + K * h2_family

/-- Kinship inflation exceeds true R² when K > 0. -/
theorem kinship_inflates (r2_true K h2_family : ℝ)
    (h_K : 0 < K) (h_h2 : 0 < h2_family) :
    r2_true < kinshipInflation r2_true K h2_family := by
  unfold kinshipInflation; linarith [mul_pos h_K h_h2]

/-- **GRM-based exclusion.**
    Removing individuals with GRM off-diagonal > threshold
    (e.g., 0.05) removes close relatives but not distant
    population structure. -/
end CrypticRelatedness

end Calibrator
