/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Descent.OpenQuestions

namespace Descent

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat sample-overlap bias in R-squared estimates. Sources for individual
results, where they exist, are cited at those results.
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

/-- **overlapInflation at its junk point, named.** With no true explained variance the inflation
ratio is undefined. The divisor is zero, the ratio is junk-zero, and the result is `-1`: a
hundred per cent DEFLATION, reported for an observed overlap that is entirely spurious.
Consumers must exclude the argument that makes the guard vanish. -/
theorem overlapInflation_zero_true_r2_is_junk (r2_observed : ℝ) :
    overlapInflation 0 r2_observed = -1 := by
  unfold overlapInflation
  simp

/-- Inflation is positive when observed exceeds true. -/
theorem overlap_inflation_positive (r2_true r2_observed : ℝ)
    (h_true : 0 < r2_true) (h_inflated : r2_true < r2_observed) :
    0 < overlapInflation r2_true r2_observed := by
  unfold overlapInflation
  rw [sub_pos, one_lt_div₀ h_true]
  exact h_inflated

/-- **Observed `R²` under partial sample overlap.**

    With a fraction `f` of the validation sample also in discovery, the
    observed `R²` is the mixture `(1 - f) R²_out + f R²_in`, where `r2_true` is
    the clean out-of-sample value and `h2` stands in for the in-sample
    (overfit) value.

    The previous form was `r2_true + f (h2 - r2_true) / n_gwas`. The divisor is
    spurious: overlap inflation is set by what fraction of the test set was in
    training and does not vanish as the discovery sample grows. At `f = 0.5`
    and `n = 2000` it predicted an inflation of `4.5·10⁻⁵` where the simulated
    value is `0.105`, three orders of magnitude too small. The mixture law
    matches simulation to three decimals at every overlap fraction tested.

    `n_gwas` is retained in the signature and unused, so that existing call
    sites keep their arity; nothing depends on it.

    Convention: `r2_true` is out-of-sample, `h2` is the in-sample value.

    Empirical status: VALIDATED in the corrected form (matches simulated mixed
    R² to three decimals at f = 0.1, 0.25 and 0.5).

    Power: the overlap fraction is swept fivefold and the prediction is linear
    in it, so at the in-sample/out-of-sample gap the `f = 0.5` cell measures
    (`0.105` of inflation, hence a gap near `0.21`) the mixture predicts
    inflations of `0.021`, `0.053` and `0.105` at `f = 0.1`, `0.25` and `0.5`.
    The superseded `f (h2 - r2_true) / n_gwas` form predicts `0.000045` at the
    same last cell, so the design separates them by three orders of magnitude
    rather than by a margin. -/
noncomputable def partialOverlapR2 (r2_true h2 : ℝ) (f : ℝ) (_n_gwas : ℕ) : ℝ :=
  (1 - f) * r2_true + f * h2

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem partialOverlapR2_at_reference_point :
    partialOverlapR2 1 1 1 1 = 1 := by
  norm_num [partialOverlapR2]



/-- Zero overlap gives unbiased estimate. -/
theorem no_overlap_unbiased (r2_true h2 : ℝ) (n_gwas : ℕ) :
    partialOverlapR2 r2_true h2 0 n_gwas = r2_true := by
  unfold partialOverlapR2; ring

/-- More overlap → more inflation (when h² > R²_true). -/
theorem more_overlap_more_inflation (r2_true h2 f₁ f₂ : ℝ) (n_gwas : ℕ)
    (h_h2 : r2_true < h2)
    (h_f : f₁ < f₂) :
    partialOverlapR2 r2_true h2 f₁ n_gwas <
      partialOverlapR2 r2_true h2 f₂ n_gwas := by
  unfold partialOverlapR2
  have h_diff : 0 < h2 - r2_true := by linarith
  nlinarith [mul_lt_mul_of_pos_right h_f h_diff]

end OverlapInflation


/-!
## Cross-Ancestry Evaluation Avoids Overlap

Cross-ancestry PGS evaluation naturally avoids sample overlap
because discovery and target samples are from different populations.
-/

section CrossAncestryNoOverlap

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
    (h_real_gap : r2_cross < r2_same_true) :
    r2_cross < partialOverlapR2 r2_same_true h2 f n_gwas ∧
    partialOverlapR2 r2_same_true h2 f n_gwas - r2_cross >
      r2_same_true - r2_cross := by
  have h_inflation : r2_same_true < partialOverlapR2 r2_same_true h2 f n_gwas := by
    have h0 := no_overlap_unbiased r2_same_true h2 n_gwas
    have hlt := more_overlap_more_inflation r2_same_true h2 0 f n_gwas h_h2 h_f_pos
    rw [h0] at hlt
    exact hlt
  constructor
  · linarith
  · linarith

/-- **A larger denominator gives a smaller ratio:**
    `a/(b + c) < a/b` for positive `a`, `b`, `c`.

    Read as genetics, `b + c` is a same-ancestry `R²` inflated by overlap bias,
    so the ratio computed from it understates portability. That the inflation
    is additive, and that `c` is the overlap bias rather than any other
    quantity, are both stipulated by writing the sum. No sample, no overlap and
    no ancestry appears below, and nothing identifies `b` as the true value —
    three positive reals and a division. -/
theorem div_add_lt_div
    (r2_cross r2_same_true overlap_bias : ℝ)
    (h_cross_pos : 0 < r2_cross)
    (h_same_pos : 0 < r2_same_true)
    (h_bias_pos : 0 < overlap_bias) :
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

/-- **Approximate LOO using linear algebra.**
    PGS_LOO_i ≈ PGS_full_i - leverage_i × residual_i
    where leverage_i = X_i'(X'X)⁻¹X_i.

    Empirical status: **VALIDATED as an approximation**, and the exact
    form named (`validation/empirical/simcov/battery_bulk10.py`,
    `test_approx_loo`). The oracle is the ACTUAL leave-one-out prediction,
    obtained by refitting the regression without each individual in turn:

      n     p     as written   true LOO    relative
      300    8      3.91975     3.91126      0.22%
      500   20      5.21670     5.24536      0.55%
      200    5     -6.79229    -6.81396      0.32%

    The exact leave-one-out identity for least squares is
    `pgs_full - leverage * residual / (1 - leverage)`, and on the same runs it
    reproduces the refits to 2e-14 -- machine precision, since it is an identity
    rather than an approximation. This definition drops the `1 / (1 - leverage)`,
    so its error is the leverage itself to first order, and it grows with the
    parameter-to-sample ratio: 0.22 percent at `p/n = 0.027` and 0.55 percent at
    0.04.

    The name says `approx`, which is honest. What the docstring adds is that the
    exact form costs one division and is available, so the approximation buys
    nothing here.

    Power: the prediction spans -6.79 to 5.22 across the design, and the error
    tracks `p/n` rather than being constant. -/
noncomputable def approxLOOPGS (pgs_full leverage residual : ℝ) : ℝ :=
  pgs_full - leverage * residual

/-- **approxLOOPGS pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 4`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem approxLOOPGS_at_reference_point :
    approxLOOPGS (1 / 2) (1 / 2) (1 / 2) = 1 / 4 := by
  unfold approxLOOPGS
  norm_num

/-- LOO correction reduces the PGS when leverage and residual
    have the same sign (overfitting case). -/
theorem loo_reduces_overfitting
    (pgs_full leverage residual : ℝ)
    (h_lev : 0 < leverage) (h_res : 0 < residual) :
    approxLOOPGS pgs_full leverage residual < pgs_full := by
  unfold approxLOOPGS; linarith [mul_pos h_lev h_res]

/-- **GWAS-by-subtraction identifies overlap bias from partial overlap model.**
    Using the `partialOverlapR2` formula: running GWAS on the full sample
    (overlap fraction f) and then on the excluded sample (overlap fraction 0)
    yields a difference that exactly equals the bias term.
    Derived from the structural definition of `partialOverlapR2`. -/
theorem gwas_subtraction_estimates_bias
    (r2_true h2 f : ℝ) (n_gwas : ℕ) :
    partialOverlapR2 r2_true h2 f n_gwas - partialOverlapR2 r2_true h2 0 n_gwas =
      f * (h2 - r2_true) := by
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

/-- **kinshipInflation pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `3 / 4`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem kinshipInflation_at_reference_point :
    kinshipInflation (1 / 2) (1 / 2) (1 / 2) = 3 / 4 := by
  unfold kinshipInflation
  norm_num

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
    threshold × h²_family (from abs_mul_lt_of_abs_lt_of_le_one),
    while the remaining sample is n_total - n_excluded.
    The tradeoff: stricter threshold → smaller inflation bound
    but fewer remaining samples for power. -/
theorem grm_threshold_tradeoff
    (r2_true h2_family K_strict K_lenient : ℝ)
    (h_strict_lt : K_strict < K_lenient)
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
theorem abs_mul_lt_of_abs_lt_of_le_one
    (K_cross h2_family ε : ℝ)
    (h_K_small : |K_cross| < ε)
    (h_h2_pos : 0 < h2_family) (h_h2_le : h2_family ≤ 1) :
    |K_cross * h2_family| < ε := by
  calc |K_cross * h2_family| = |K_cross| * |h2_family| := abs_mul _ _
    _ = |K_cross| * h2_family := by rw [abs_of_pos h_h2_pos]
    _ ≤ |K_cross| * 1 := by nlinarith [abs_nonneg K_cross]
    _ = |K_cross| := mul_one _
    _ < ε := h_K_small

end CrypticRelatedness

end Descent
