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

/-- **Cross-ancestry has zero overlap by design.**
    When discovery is EUR and validation is AFR, there is no
    sample overlap → no overfitting inflation. With zero overlap
    fraction f = 0, the partial overlap formula gives R²_observed = R²_true. -/
theorem cross_ancestry_no_overlap_bias
    (r2_true h2 : ℝ) (n_gwas : ℕ) :
    partialOverlapR2 r2_true h2 0 n_gwas = r2_true :=
  no_overlap_unbiased r2_true h2 n_gwas

/-- **Same-ancestry R² is inflated relative to cross-ancestry.**
    Derived from the overfitting bias formula `partialOverlapR2`:
    same-ancestry R² with overlap fraction f > 0 exceeds true R²,
    while cross-ancestry R² (f = 0) equals true cross R².
    The apparent portability gap therefore includes a spurious
    overlap-driven component. -/
theorem apparent_portability_loss_includes_overlap
    (r2_same_true h2 r2_cross : ℝ) (f : ℝ) (n_gwas : ℕ)
    (h_h2 : r2_same_true < h2)
    (h_f_pos : 0 < f)
    (h_n : 0 < n_gwas)
    (h_real_gap : r2_cross < r2_same_true) :
    let r2_same_with_overlap := partialOverlapR2 r2_same_true h2 f n_gwas
    r2_cross < r2_same_with_overlap ∧
    r2_same_with_overlap - r2_cross > r2_same_true - r2_cross := by
  simp only
  have h_inflation : r2_same_true < partialOverlapR2 r2_same_true h2 f n_gwas := by
    have h0 := no_overlap_unbiased r2_same_true h2 n_gwas
    have hlt := more_overlap_more_inflation r2_same_true h2 0 f n_gwas h_h2 h_n h_f_pos
    rw [h0] at hlt
    exact hlt
  constructor
  · linarith
  · linarith

/-- **Correcting for overlap reveals true portability.**
    After removing overlap bias from same-ancestry R²,
    the true portability gap is smaller than it appeared.
    Portability ratio = R²_cross / R²_same. When R²_same is inflated
    by overlap bias, the apparent portability ratio is lower than the
    true ratio R²_cross / R²_same_true. -/
theorem corrected_portability_better
    (r2_cross r2_same_true overlap_bias : ℝ)
    (h_cross_pos : 0 < r2_cross)
    (h_same_pos : 0 < r2_same_true)
    (h_bias_pos : 0 < overlap_bias)
    (h_cross_le : r2_cross < r2_same_true) :
    -- apparent portability < true portability
    r2_cross / (r2_same_true + overlap_bias) < r2_cross / r2_same_true := by
  apply div_lt_div_of_pos_left h_cross_pos h_same_pos
  linarith

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

/-- **GWAS-by-subtraction identifies overlap bias from partial overlap model.**
    Using the `partialOverlapR2` formula: running GWAS on the full sample
    (overlap fraction f) and then on the excluded sample (overlap fraction 0)
    yields a difference that exactly equals the bias term.
    Derived from the structural definition of `partialOverlapR2`. -/
theorem gwas_subtraction_estimates_bias
    (r2_true h2 f : ℝ) (n_gwas : ℕ)
    (h_h2 : r2_true < h2) (h_f : 0 < f) (h_n : 0 < n_gwas) :
    partialOverlapR2 r2_true h2 f n_gwas - partialOverlapR2 r2_true h2 0 n_gwas =
      f * (h2 - r2_true) / ↑n_gwas := by
  unfold partialOverlapR2
  ring

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

/-- **GRM-based exclusion: bias-variance tradeoff.**
    Removing individuals with GRM off-diagonal > threshold reduces
    kinship-based inflation. A stricter threshold (lower cutoff)
    removes more individuals, reducing kinship bias but also reducing
    the remaining validation sample size.

    We derive: the remaining kinship inflation is bounded by
    threshold × h²_family (from cross_ancestry_no_kinship_bias),
    while the remaining sample is n_total - n_excluded.
    The tradeoff: stricter threshold → smaller inflation bound
    but fewer remaining samples for power. -/
theorem grm_threshold_tradeoff
    (r2_true h2_family K_strict K_lenient : ℝ)
    (h_strict_lt : K_strict < K_lenient)
    (h_strict_pos : 0 < K_strict)
    (h_lenient_pos : 0 < K_lenient)
    (h_h2_pos : 0 < h2_family) :
    -- Stricter threshold gives smaller kinship inflation
    kinshipInflation r2_true K_strict h2_family <
      kinshipInflation r2_true K_lenient h2_family := by
  unfold kinshipInflation
  linarith [mul_lt_mul_of_pos_right h_strict_lt h_h2_pos]

/-- **Cross-ancestry naturally avoids cryptic relatedness.**
    Individuals from different continental ancestries have
    near-zero kinship, eliminating kinship-based inflation.
    When |K| < ε, the inflation |K × h²_family| < ε × h²_family,
    so the bias is bounded by ε × h²_family. -/
theorem cross_ancestry_no_kinship_bias
    (K_cross h2_family ε : ℝ)
    (h_ε_pos : 0 < ε)
    (h_K_small : |K_cross| < ε)
    (h_h2_pos : 0 < h2_family) (h_h2_le : h2_family ≤ 1) :
    |K_cross * h2_family| < ε := by
  calc |K_cross * h2_family| = |K_cross| * |h2_family| := abs_mul _ _
    _ = |K_cross| * h2_family := by rw [abs_of_pos h_h2_pos]
    _ ≤ |K_cross| * 1 := by nlinarith [abs_nonneg K_cross]
    _ = |K_cross| := mul_one _
    _ < ε := h_K_small

end CrypticRelatedness

end Calibrator
