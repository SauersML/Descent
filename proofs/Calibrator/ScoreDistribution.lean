/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PGSCalibrationTheory

namespace Calibrator

/-!
# PGS Score Distribution Theory

This file formalizes the distributional properties of polygenic scores
and how these distributions change across populations. Score distribution
changes directly affect the interpretation and utility of PGS.

Key results:
1. Central limit theorem for PGS under independence
2. Score distribution shifts under allele frequency changes
3. Score variance changes and their effect on tail probabilities
4. Calibration across populations
5. Quantile-based risk and population-specific thresholds

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat score distribution theory, tail probabilities or quantile
thresholds. Sources for individual results, where they exist, are cited at those results.
-/


/-!
## Score Mean and Variance Under Hardy-Weinberg

Under HWE, each locus contributes independently to the score.
The score mean and variance are determined by allele frequencies
and effect sizes.
-/

section ScoreMeanVariance

/-- **PGS mean under HWE.**
    E[PGS] = Σᵢ βᵢ × 2pᵢ.

    Empirical status: UNTESTED. -/
noncomputable def pgsMean {m : ℕ} (β : Fin m → ℝ) (p : Fin m → ℝ) : ℝ :=
  ∑ i, β i * (2 * p i)

/-- **PGS variance under HWE and linkage equilibrium.**
    Var(PGS) = Σᵢ βᵢ² × 2pᵢ(1-pᵢ).

    Empirical status: UNTESTED. -/
noncomputable def pgsVariance {m : ℕ} (β : Fin m → ℝ) (p : Fin m → ℝ) : ℝ :=
  ∑ i, β i ^ 2 * (2 * p i * (1 - p i))

/-- PGS variance is nonneg. -/
theorem pgs_variance_nonneg {m : ℕ} (β : Fin m → ℝ) (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ pgsVariance β p := by
  unfold pgsVariance
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _)
  nlinarith [hp i, hp1 i]

/-- **Mean shift between populations.**
    Δμ = Σᵢ βᵢ × 2(p'ᵢ - pᵢ).

    Empirical status: UNTESTED. -/
noncomputable def pgsMeanShift
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ) : ℝ :=
  ∑ i, β i * (2 * (p_target i - p_source i))

/-- Mean shift equals difference of means. -/
theorem mean_shift_eq_diff {m : ℕ} (β : Fin m → ℝ)
    (p_source p_target : Fin m → ℝ) :
    pgsMeanShift β p_source p_target =
      pgsMean β p_target - pgsMean β p_source := by
  unfold pgsMeanShift pgsMean
  simp [Finset.sum_sub_distrib, mul_sub]

/-- **Variance ratio between populations.**
    Var_T / Var_S can be > 1 or < 1 depending on frequency changes. -/
theorem variance_ratio_can_exceed_one
    (var_s var_t : ℝ) (h_s : 0 < var_s) (h_t_larger : var_s < var_t) :
    1 < var_t / var_s := by
  rw [lt_div_iff₀ h_s]; linarith

theorem variance_ratio_can_be_below_one
    (var_s var_t : ℝ) (h_s : 0 < var_s) (h_t_smaller : var_t < var_s) :
    var_t / var_s < 1 := by
  rw [div_lt_one h_s]; exact h_t_smaller

end ScoreMeanVariance


/-!
## Tail Probabilities and Risk Categorization

Clinical use of PGS involves placing individuals in risk categories
based on score percentiles. Tail probabilities determine how many
individuals fall in extreme categories.
-/

section TailProbabilities


/-- Standardized benchmark threshold coordinate for a Gaussian score law with
mean `μ` and standard deviation `σ`. This is a score-summary object, not by
itself a clinical decision or misclassification theorem.

    Empirical status: UNTESTED. -/
noncomputable def thresholdStandardizedCoordinate (threshold μ σ : ℝ) : ℝ :=
  (threshold - μ) / σ

/-- **The standardized coordinate is translation equivariant and vanishes at the mean.** Shifting
the threshold and the mean together leaves it unchanged, which is what makes it a position
relative to the distribution rather than an absolute score. -/
theorem thresholdStandardizedCoordinate_shift (threshold μ σ d : ℝ) :
    thresholdStandardizedCoordinate (threshold + d) (μ + d) σ
      = thresholdStandardizedCoordinate threshold μ σ := by
  unfold thresholdStandardizedCoordinate
  congr 1
  ring

theorem thresholdStandardizedCoordinate_at_mean (μ σ : ℝ) :
    thresholdStandardizedCoordinate μ μ σ = 0 := by
  unfold thresholdStandardizedCoordinate; simp

/-- Gaussian benchmark fraction of scores above a raw threshold. This is the
deployment-relevant tail-rate object associated with the standardized
coordinate, but it is still only a benchmark score-distribution quantity. -/
noncomputable def benchmarkHighScoreRate (threshold μ σ : ℝ) : ℝ :=
  1 - Phi (thresholdStandardizedCoordinate threshold μ σ)

/-- **A rightward mean shift lowers the standardized threshold coordinate.**

    This is the coordinate step, and it says nothing about probability: `Phi` and
    `benchmarkHighScoreRate` do not appear. The tail-rate claim — that a rightward shift puts
    strictly more of the distribution above a fixed raw threshold — is
    `mean_shift_changes_benchmark_high_score_rate` below, which is this lemma composed with
    strict monotonicity of `Phi`. Read this one as arithmetic on a z-score. -/
theorem mean_shift_increases_tail
    (threshold μ₁ μ₂ σ : ℝ)
    (h_σ : 0 < σ)
    (h_shift : μ₁ < μ₂) :
    (threshold - μ₂) / σ < (threshold - μ₁) / σ := by
  exact div_lt_div_of_pos_right (by linarith) h_σ

/-- **A larger standard deviation lowers the standardized coordinate of a point above the
    mean.**

    Again the coordinate step only. "More probability in both tails" is a statement about two
    tail rates and needs `Phi` at two arguments; neither appears here, and the second tail is
    not reached by this inequality at all. The upper-tail consequence is
    `variance_change_changes_benchmark_high_score_rate` below. -/
theorem variance_increase_thickens_tails
    (x σ₁ σ₂ : ℝ) (h₁ : 0 < σ₁)
    (h_larger : σ₁ < σ₂) (h_x : 0 < x) :
    x / σ₂ < x / σ₁ := by
  exact div_lt_div_of_pos_left h_x h₁ h_larger

/-- **Threshold standardized coordinate changes under mean shift.**
    When population means differ, the standardized location of a fixed raw
    threshold differs as long as the standard deviation is shared. This is a
    score-coordinate fact, not yet a theorem about outcomes or decisions. -/
theorem threshold_standardized_coordinate_diff_of_mean_shift
    (threshold μ_S μ_T σ : ℝ)
    (h_σ : 0 < σ)
    (h_shift : μ_S ≠ μ_T) :
    thresholdStandardizedCoordinate threshold μ_S σ ≠
      thresholdStandardizedCoordinate threshold μ_T σ := by
  intro h
  apply h_shift
  have h_ne : σ ≠ 0 := h_σ.ne'
  have : (threshold - μ_S) * σ = (threshold - μ_T) * σ := by
    simpa [thresholdStandardizedCoordinate] using
      (div_eq_div_iff h_ne h_ne).mp h
  linarith [mul_right_cancel₀ h_ne this]

/-- **Threshold standardized coordinate changes under variance change.**
    When the standard deviations differ, the standardized location of a fixed
    raw threshold differs as long as the threshold is not equal to the common
    mean. This is still a score-coordinate fact rather than a full decision
    theorem. -/
theorem threshold_standardized_coordinate_diff_of_variance_change
    (threshold μ σ_S σ_T : ℝ)
    (h_σS : 0 < σ_S) (h_σT : 0 < σ_T)
    (h_σ_ne : σ_S ≠ σ_T)
    (h_thr : threshold ≠ μ) :
    thresholdStandardizedCoordinate threshold μ σ_S ≠
      thresholdStandardizedCoordinate threshold μ σ_T := by
  intro h
  apply h_σ_ne
  have h_ne : threshold - μ ≠ 0 := sub_ne_zero.mpr h_thr
  have h1 : (threshold - μ) * σ_T = (threshold - μ) * σ_S := by
    simpa [thresholdStandardizedCoordinate] using
      (div_eq_div_iff h_σS.ne' h_σT.ne').mp h
  exact (mul_left_cancel₀ h_ne h1).symm

/-- **Mean shift changes the benchmark high-score rate.**
    Under the Gaussian benchmark score law, a rightward mean shift strictly
    increases the fraction of scores above a fixed raw threshold. This is the
    deployment-relevant tail-rate statement corresponding to the raw
    standardized-coordinate algebra above. -/
theorem mean_shift_changes_benchmark_high_score_rate
    (threshold μ_S μ_T σ : ℝ)
    (h_σ : 0 < σ)
    (h_shift : μ_S < μ_T) :
    benchmarkHighScoreRate threshold μ_S σ <
      benchmarkHighScoreRate threshold μ_T σ := by
  unfold benchmarkHighScoreRate thresholdStandardizedCoordinate
  have hz : (threshold - μ_T) / σ < (threshold - μ_S) / σ := by
    exact mean_shift_increases_tail threshold μ_S μ_T σ h_σ h_shift
  have hphi : Phi ((threshold - μ_T) / σ) < Phi ((threshold - μ_S) / σ) := by
    exact strictMono_Phi hz
  linarith

/-- **Variance change changes the benchmark high-score rate.**
    If the threshold lies above the common mean, increasing the benchmark score
    standard deviation strictly increases the fraction of scores above that raw
    threshold. -/
theorem variance_change_changes_benchmark_high_score_rate
    (threshold μ σ_S σ_T : ℝ)
    (h_σS : 0 < σ_S)
    (_h_σT : 0 < σ_T)
    (h_larger : σ_S < σ_T)
    (h_thr : 0 < threshold - μ) :
    benchmarkHighScoreRate threshold μ σ_S <
      benchmarkHighScoreRate threshold μ σ_T := by
  unfold benchmarkHighScoreRate thresholdStandardizedCoordinate
  have hz : (threshold - μ) / σ_T < (threshold - μ) / σ_S := by
    exact variance_increase_thickens_tails (threshold - μ) σ_S σ_T h_σS h_larger h_thr
  have hphi : Phi ((threshold - μ) / σ_T) < Phi ((threshold - μ) / σ_S) := by
    exact strictMono_Phi hz
  linarith

end TailProbabilities


/-!
## Calibration Across Populations

A PGS is "calibrated" if the predicted risk matches the observed risk.
Calibration in the source does not imply calibration in the target.
-/

section Calibration

/-- **Nonzero PGS mean shift changes the benchmark mean prediction.**
    This is only the score-summary statement that the benchmark mean prediction
    changes when `pgsMeanShift` is nonzero. It is not itself yet a theorem about
    target calibration without specifying an observed-mean model. -/
theorem pgs_mean_shift_changes_mean_prediction
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ)
    (h_shift : pgsMeanShift β p_source p_target ≠ 0) :
    pgsMean β p_target ≠ pgsMean β p_source := by
  rw [← sub_ne_zero]
  rwa [← mean_shift_eq_diff]

/-- **Identity-link CITL shift equals the negative benchmark mean shift.**
    Holding the observed mean fixed, the change in calibration-in-the-large is
    exactly the negative of the benchmark score-mean shift. This upgrades the
    pure mean-prediction fact to an exact CITL identity. -/
theorem identity_citl_shift_eq_neg_pgsMeanShift
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ)
    (mean_observed : ℝ) :
    calibrationInTheLarge mean_observed (pgsMean β p_target) -
      calibrationInTheLarge mean_observed (pgsMean β p_source) =
        -pgsMeanShift β p_source p_target := by
  unfold calibrationInTheLarge
  rw [mean_shift_eq_diff]
  ring

/-- **Nonzero PGS mean shift changes identity-link CITL.**
    If the benchmark score mean changes while the observed mean is held fixed,
    the corresponding identity-link calibration-in-the-large changes as well. -/
theorem identity_citl_changes_of_nonzero_pgsMeanShift
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ)
    (mean_observed : ℝ)
    (h_shift : pgsMeanShift β p_source p_target ≠ 0) :
    calibrationInTheLarge mean_observed (pgsMean β p_target) ≠
      calibrationInTheLarge mean_observed (pgsMean β p_source) := by
  rw [← sub_ne_zero]
  rw [identity_citl_shift_eq_neg_pgsMeanShift]
  exact neg_ne_zero.mpr h_shift

/-- **Mechanistic target calibration slope is below `1` exactly when the
transported SNP-level score law says so.**
    This is the honest score-distribution statement: the target identity-link
    profile uses the literal transported `Cov/Var` slope from the mechanistic
    calibration model, not a neutral-AF benchmark surrogate. -/
theorem mechanistic_target_identity_calibration_slope_lt_one
    {p q : ℕ} (cal : CrossPopulationMechanisticCalibrationModel p q)
    (h_target_slope_lt : calibrationSlopeFromSourceWeights cal.metric Pop.target < 1) :
    ((cal.identityCalibrationProfile Pop.target)).slope < 1 := by
  simpa [CrossPopulationMechanisticCalibrationModel.identityCalibrationProfile,
    CrossPopulationMechanisticCalibrationModel.calibrationProfile] using
    h_target_slope_lt

/-- **Under mechanistic transport, slope deviation is exactly `1 - slope`
when the deployed target slope lies below `1`.** -/
theorem mechanistic_target_identity_calibration_slopeDeviation_eq_one_sub
    {p q : ℕ} (cal : CrossPopulationMechanisticCalibrationModel p q)
    (h_target_slope_lt : calibrationSlopeFromSourceWeights cal.metric Pop.target < 1) :
    calibrationSlopeDeviation ((cal.identityCalibrationProfile Pop.target)).slope =
      1 - ((cal.identityCalibrationProfile Pop.target)).slope := by
  exact calibrationSlopeDeviation_eq_one_sub_of_lt_one
    ((cal.identityCalibrationProfile Pop.target)).slope
    (mechanistic_target_identity_calibration_slope_lt_one cal h_target_slope_lt)

/-- **Recalibration restores calibration-in-the-large.**
    If the PGS mean in the target is `pgsMean β p_target` while the
    source-calibrated prediction assumes mean `pgsMean β p_source`,
    subtracting the mean shift `pgsMeanShift β p_source p_target`
    restores the correct mean. Derived from `mean_shift_eq_diff`. -/
theorem recalibration_restores_intercept
    {m : ℕ} (β : Fin m → ℝ) (p_source p_target : Fin m → ℝ) :
    pgsMean β p_target - pgsMeanShift β p_source p_target =
      pgsMean β p_source := by
  rw [mean_shift_eq_diff]; ring

/-- **Platt scaling is not the identity when b ≠ 1.**
    Fitting a logistic regression of Y on PGS in the target
    recovers both intercept and slope calibration.
    This requires target-population labeled data.

    When b ≠ 1, the Platt-scaled prediction a + b*x differs from x
    for at least one score value. (In fact, it agrees with x at exactly
    one point: x = a/(1-b).) -/
theorem platt_scaling_not_identity
    (a b : ℝ) (h_b_ne : b ≠ 1) :
    ∃ pgs : ℝ, a + b * pgs ≠ pgs := by
  -- If a + b*x = x for all x, then (taking x=0 and x=1) a = 0 and b = 1.
  -- Since b ≠ 1, this is impossible, so there exists x where they differ.
  by_contra h_all
  push_neg at h_all
  have h0 := h_all 0
  have h1 := h_all 1
  simp only [mul_zero, add_zero] at h0
  -- h0 : a = 0, h1 : a + b * 1 = 1
  simp only [h0, zero_add, mul_one] at h1
  exact h_b_ne h1

/-- **Platt scaling with nonzero intercept always changes the zero score.**
    When a ≠ 0, the recalibrated prediction at pgs = 0 differs from 0. -/
theorem platt_scaling_shifts_zero
    (a b : ℝ) (h_a_ne : a ≠ 0) :
    a + b * 0 ≠ 0 := by simp [h_a_ne]

end Calibration


/-!
## Gaussian Approximation Error and Berry-Esseen

The PGS is a sum of discrete (0, 1, 2) random variables.
The Gaussian approximation error affects tail probability estimates.
-/

section GaussianApproximation

/-! The Berry–Esseen statements of this section are `berryEsseenBound_antitone` for the
summand-count comparison and `berryEsseenBound_polygenic_lt_oligogenic` for the
polygenicity reading of it. Both are stated against `berryEsseenBound`, which is defined
through `Calibrator.Probability.berryEsseenErrorBound` and so cannot drift from it.

`m` is a summand count, and under linkage the count that governs is the block count `m/ℓ`.
See the block-count section below, where the count is VALIDATED and the `√ℓ` constant that
would convert one to the other is FALSIFIED. -/

/-! ### The count that decides is blocks, not markers — and the constant that does not

`berry_esseen_error_decreases_with_snps` above is stated in the **marker count**, and under
linkage that count is wrong. The freezing transition supplies the correction: a score over a
genome with correlation length `ℓ` behaves, for normal-approximation purposes, like a sum
over `m/ℓ` effectively independent **blocks**.

**The count is confirmed and the constant is refuted.** The marker-count bound does *not*
understate the true one by exactly `√ℓ`. Simulation on 1.6M individuals per configuration
(153 configurations):

* with **block-constant haplotypes and equal marker weights** the ratio is `1.00 ± 0.01` at
  every `ℓ ∈ [1,32]` and every `m ∈ [16,8192]` — there, and only there, the factor is `√ℓ`;
* with **geometric block lengths** — a genuine renewal chain, i.e. actual recombination —
  the ratio is `2.09` at `ℓ = 32`, between 25 and 240 standard errors from one.

The shortfall has a closed form. Writing `bw` for a block's summed weight, the third-moment
ratio against an equal-weight independent panel is `κ = E[bw³]/E[bw²]^{3/2}`, which for
geometric lengths of mean `ℓ` tends to `6/2^{3/2} = 2.1213`. Predicted against measured:
`1.769/1.72`, `1.971/1.96`, `2.051/2.05`, `2.087/2.07`, `2.105/2.09` — under 2% throughout.

**The same factor runs the other way for heterogeneous effect sizes**, because blocks average
weights: half-normal weights give `κ → 0.6267` (measured plateau `0.65`). Both mechanisms
together predict `2.121 × 0.6267 = 1.319`; measured `1.31 ± 0.03`. So `κ` is not a fudge
absorbing error — it is a computable property of the excursion-weight law, and it can sit on
either side of one.

`κ` is therefore an **explicit argument** below rather than a suppressed hypothesis. The old
statement, reusing one `ρ/σ³` on both sides, was a tautology whose entire content was the
unstated `κ = 1`.

**What the block reduction does and does not say.** `FoldedSpectrum` §8's `renormalization`
gives the chain's law as that of an independent panel over the **excursion bundle** — a
different family with its own moments — not as `m/ℓ` independent *markers*. Collapsing the
one to the other is exactly the `κ = 1` smuggle, and it is the step the measurement refutes.

**A warning about `ℓ` itself.** It has no operational definition here and the natural
estimators disagree. For a copying chain the mean block length is `ℓ` while the score
variance inflation is `2ℓ - 1` (measured `30.9` at `ℓ = 16`), so reading `ℓ` off variance
inflation costs a further `√2`. Worse, with sign-random effect weights the measured variance
inflation is `1.00 ± 0.01` at every `ℓ` up to 32 while the effective block count is still
`m/ℓ` — the standard estimator returns `ℓ = 1` and reports that no correction is needed.

**And the bound is not the distance.** For a lattice-valued score the two can move in
opposite directions: with unit weights the copy arm's measured Kolmogorov–Smirnov distance is
*half* the block prediction (`0.493` at `ℓ = 4`), because random block lengths destroy the
lattice term that dominates KS. Once weights are continuous the lattice term vanishes and KS
agrees with skewness (`1.31`). A Berry–Esseen bound is not a claim about measured
distributional distance.

Empirical status: **the block count is VALIDATED, the `√ℓ` constant is FALSIFIED and
replaced.** Measurements in `proofs/validation/empirical/block_count/`; positive control (`ℓ = 1`,
three independent generators) reproduces the analytic independent-panel value to
`1.001 ± 0.003`. -/

/-! ### The `σ` power, and why the guard is structural

The Berry–Esseen bound is `C·ρ/(variance·√variance) = Cρ/σ³`, and
`Calibrator.Probability` holds the one body for it. A second spelling in this file, such
as `C·ρ/(σ_sq·√m)`, is wrong in the power of `σ`.

Do not restate the bound here, even correctly. Two alpha-inequivalent bodies for the same
quantity, tied by neither a call nor a theorem, cannot disagree loudly. They just
disagree, and this corpus is more prone to that failure than to any other. So
`berryEsseenBound` below is *defined through* `Probability.berryEsseenErrorBound`, and
`berryEsseenBound_eq` recovers the closed form as a theorem. One body means the two files
cannot drift.

Empirical status: DERIVED. This is a consistency constraint between two files in this
corpus, not a claim against an experiment. -/

/-- **The Berry–Esseen bound at `m` summands**, defined *through* the existing
    `Calibrator.Probability.berryEsseenErrorBound` rather than beside it, so the two files
    share one body. `berryEsseenBound_eq` states the closed form as a theorem. -/
noncomputable def berryEsseenBound (C ρ σ_sq m : ℝ) : ℝ :=
  berryEsseenErrorBound C σ_sq ρ / Real.sqrt m

/-- The closed form, as a theorem rather than a second definition. -/
theorem berryEsseenBound_eq (C ρ σ_sq m : ℝ) :
    berryEsseenBound C ρ σ_sq m = C * ρ / (σ_sq * Real.sqrt σ_sq * Real.sqrt m) := by
  unfold berryEsseenBound berryEsseenErrorBound
  rw [div_div]

/-- The bound decreases in the summand count. -/
theorem berryEsseenBound_antitone (C ρ σ_sq m₁ m₂ : ℝ)
    (hC : 0 < C) (hρ : 0 < ρ) (hσ : 0 < σ_sq) (hm₁ : 0 < m₁) (hm : m₁ < m₂) :
    berryEsseenBound C ρ σ_sq m₂ < berryEsseenBound C ρ σ_sq m₁ := by
  have hs : 0 < Real.sqrt σ_sq := Real.sqrt_pos.mpr hσ
  have hsm₁ : 0 < Real.sqrt m₁ := Real.sqrt_pos.mpr hm₁
  have hlt : Real.sqrt m₁ < Real.sqrt m₂ :=
    Real.sqrt_lt_sqrt (le_of_lt hm₁) hm
  rw [berryEsseenBound_eq, berryEsseenBound_eq]
  apply div_lt_div_of_pos_left (mul_pos hC hρ) (by positivity)
  exact mul_lt_mul_of_pos_left hlt (by positivity)

/-- **The polygenicity reading of the bound.**

    A trait with more contributing loci has the smaller Berry–Esseen bound, all else held
    fixed.

    Two limits on how far this may be read:

    * It compares *bounds*, not approximation qualities. A smaller Berry–Esseen bound does
      not entail a smaller actual distributional distance, only a smaller certificate of one.
    * `m` is a summand count. Under linkage the markers are not the summands — the block
      count `m/ℓ` is — so applying this at marker counts requires the blocks to be the
      markers. The block-count section below is where that is treated, and the `√ℓ` constant
      that would convert between the two counts is FALSIFIED, so there is no general
      conversion to fall back on. -/
theorem berryEsseenBound_polygenic_lt_oligogenic (C ρ σ_sq m_oligo m_poly : ℝ)
    (hC : 0 < C) (hρ : 0 < ρ) (hσ : 0 < σ_sq) (h_oligo : 0 < m_oligo)
    (h_more : m_oligo < m_poly) :
    berryEsseenBound C ρ σ_sq m_poly < berryEsseenBound C ρ σ_sq m_oligo :=
  berryEsseenBound_antitone C ρ σ_sq m_oligo m_poly hC hρ hσ h_oligo h_more

section BlockCount

/-- **The effectively independent block count**: markers divided by correlation length.

    Junk-value note: at `correlationLength = 0` Lean's division returns `0`, which reads as
    "no blocks at infinite correlation" — nonsense in the wrong direction. Every theorem
    below carries `0 < correlationLength`.

        Empirical status: UNTESTED. -/
noncomputable def effectiveBlockCount (markers correlationLength : ℝ) : ℝ :=
  markers / correlationLength

/-- **The block count is a ratio of lengths, so it does not depend on the unit.** Counting
markers and correlation length in units `t` times finer leaves the number of independent blocks
unchanged, which is what makes it a count rather than a length. -/
theorem effectiveBlockCount_unit_invariant (markers correlationLength t : ℝ) (ht : t ≠ 0) :
    effectiveBlockCount (t * markers) (t * correlationLength)
      = effectiveBlockCount markers correlationLength := by
  unfold effectiveBlockCount
  exact mul_div_mul_left _ _ ht

/-- **Residual discreteness of the freezing transition.**

    The lattice ghost surviving in a block of `n` markers at correlation length `ℓ`.

    Junk-value note: natural subtraction makes `n = 0` and `n = 1` agree at `1`, so this is
    the lag-`(n-1)` quantity only for `n ≥ 1`, which every theorem below requires. -/
noncomputable def residualDiscreteness (correlationLength : ℝ) (n : ℕ) : ℝ :=
  (1 - 1 / correlationLength) ^ (n - 1)

/-- At a single marker there is no averaging and the ghost is undiminished. -/
theorem residualDiscreteness_one (correlationLength : ℝ) :
    residualDiscreteness correlationLength 1 = 1 := by
  unfold residualDiscreteness
  norm_num

/-- With no linkage the ghost is extinguished past the first marker. -/
theorem residualDiscreteness_of_no_linkage (n : ℕ) (hn : 2 ≤ n) :
    residualDiscreteness 1 n = 0 := by
  unfold residualDiscreteness
  have hpos : n - 1 ≠ 0 := by omega
  norm_num [zero_pow hpos]

/-- **The residual ghost decays exponentially in blocks, not in markers.**

    `(1 - 1/ℓ)^(n-1) ≤ exp(-(n-1)/ℓ)`. The exponent counts correlation lengths spanned, so
    the discreteness a normal approximation must overcome is governed by the block count. -/
theorem residualDiscreteness_le_exp (correlationLength : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hℓ : 1 ≤ correlationLength) :
    residualDiscreteness correlationLength n ≤
      Real.exp (-((n : ℝ) - 1) / correlationLength) := by
  have hℓ0 : (0 : ℝ) < correlationLength := by linarith
  have hinv : 1 / correlationLength ≤ 1 := by
    rw [div_le_one hℓ0]; exact hℓ
  have hbase : (0 : ℝ) ≤ 1 - 1 / correlationLength := by linarith
  have hstep : 1 - 1 / correlationLength ≤ Real.exp (-(1 / correlationLength)) := by
    have := Real.add_one_le_exp (-(1 / correlationLength))
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  unfold residualDiscreteness
  calc (1 - 1 / correlationLength) ^ (n - 1)
      ≤ (Real.exp (-(1 / correlationLength))) ^ (n - 1) :=
        pow_le_pow_left₀ hbase hstep _
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (-(1 / correlationLength))) := by
        rw [← Real.exp_nat_mul]
    _ = Real.exp (-((n : ℝ) - 1) / correlationLength) := by
        rw [hcast]
        ring_nf

/-- **The excursion-shape factor.** The third-moment ratio of a block's summed weight
    against an equal-weight independent panel. Measured `2.09` for geometric block lengths,
    `0.63` for half-normal effect weights, `1.31` for both; `1` exactly for block-constant
    haplotypes with equal weights, which is the only case in which the naive `√ℓ` holds. -/
noncomputable def excursionShapeFactor (blockThirdMoment blockSecondMoment : ℝ) : ℝ :=
  blockThirdMoment / blockSecondMoment ^ (3 / 2 : ℝ)

/-- **The block bound is `√ℓ · κ` times the marker bound.**

    `κ` appears explicitly. Setting `κ = 1` recovers the equal-weight block-constant case and
    nothing else; for a genuine renewal chain `κ ≈ 2.09`, and for heterogeneous effect sizes
    `κ ≈ 0.63`. -/
theorem berry_esseen_block_bound_eq (C ρ σ_sq b ℓ κ : ℝ)
    (hb : 0 < b) (hℓ : 0 < ℓ) (hσ : 0 < σ_sq) :
    κ * (C * ρ) / (σ_sq * Real.sqrt b) =
      Real.sqrt ℓ * (κ * (C * ρ)) / (σ_sq * Real.sqrt (b * ℓ)) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsl : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  rw [Real.sqrt_mul (le_of_lt hb) ℓ]
  field_simp

/-- **When the marker count is anti-conservative, and when it is not.**

    The marker-count bound understates the true one exactly when `κ√ℓ > 1`. That covers the
    renewal-chain case, where `κ ≈ 2.09` makes the understatement *worse* than `√ℓ`. It does
    **not** cover every case: heterogeneous effect sizes give `κ ≈ 0.63`, so at small `ℓ` the
    marker count can be conservative instead. The hypothesis is stated rather than assumed
    because the measurement found both signs. -/
theorem marker_count_understates_berry_esseen (C ρ σ_sq b ℓ κ : ℝ)
    (hC : 0 < C) (hρ : 0 < ρ) (hb : 0 < b) (hσ : 0 < σ_sq) (hℓ : 0 < ℓ)
    (hgap : 1 < κ * Real.sqrt ℓ) :
    C * ρ / (σ_sq * Real.sqrt (b * ℓ)) <
      κ * (C * ρ) / (σ_sq * Real.sqrt b) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsl : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hnum : 0 < C * ρ := mul_pos hC hρ
  have hsplit : Real.sqrt (b * ℓ) = Real.sqrt b * Real.sqrt ℓ :=
    Real.sqrt_mul (le_of_lt hb) ℓ
  rw [hsplit, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hexpand : C * ρ * (σ_sq * Real.sqrt b) * (κ * Real.sqrt ℓ)
      = κ * (C * ρ) * (σ_sq * (Real.sqrt b * Real.sqrt ℓ)) := by ring
  nlinarith [mul_pos hnum (mul_pos hσ hsb), hgap, hexpand]

/-- The effective block count is what the corrected bound consumes: at `markers = b · ℓ` it
    returns `b`. -/
theorem effectiveBlockCount_of_blocks (b ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    effectiveBlockCount (b * ℓ) ℓ = b := by
  unfold effectiveBlockCount
  field_simp

end BlockCount

end GaussianApproximation


/-!
## Score Standardization and Comparability

Different standardization choices affect the interpretation of
PGS comparisons across populations.
-/

section Standardization

/-- **External standardization (to source population).**
    PGS_std = (PGS - μ_source) / σ_source.
    In the target, this no longer has mean 0 or variance 1. -/
noncomputable def externallyStandardized
    (pgs μ_source σ_source : ℝ) : ℝ :=
  (pgs - μ_source) / σ_source

/-- **Internal standardization (to own population).**
    PGS_std = (PGS - μ_target) / σ_target.
    This always has mean 0 and variance 1 within the target. -/
noncomputable def internallyStandardized
    (pgs μ_target σ_target : ℝ) : ℝ :=
  (pgs - μ_target) / σ_target

/-- **External and internal standardization differ: equal-σ case.**
    When μ differs between populations but σ is the same,
    externally and internally standardized scores always differ. -/
theorem external_vs_internal_differ_mean
    (pgs μ_S μ_T σ : ℝ)
    (h_σ : σ ≠ 0) (h_μ : μ_S ≠ μ_T) :
    externallyStandardized pgs μ_S σ ≠
      internallyStandardized pgs μ_T σ := by
  unfold externallyStandardized internallyStandardized
  intro h
  apply h_μ
  have : (pgs - μ_S) * σ = (pgs - μ_T) * σ := by
    rwa [div_eq_div_iff h_σ h_σ] at h
  linarith [mul_right_cancel₀ h_σ this]

/-- **External and internal standardization differ: equal-μ case.**
    When σ differs between populations and the score is not at the mean,
    externally and internally standardized scores differ. -/
theorem external_vs_internal_differ_variance
    (pgs μ σ_S σ_T : ℝ)
    (h_σS : σ_S ≠ 0) (h_σT : σ_T ≠ 0)
    (h_σ : σ_S ≠ σ_T)
    (h_pgs : pgs ≠ μ) :
    externallyStandardized pgs μ σ_S ≠
      internallyStandardized pgs μ σ_T := by
  unfold externallyStandardized internallyStandardized
  intro h
  apply h_σ
  have h_ne : pgs - μ ≠ 0 := sub_ne_zero.mpr h_pgs
  have h1 : (pgs - μ) * σ_T = (pgs - μ) * σ_S := by
    rwa [div_eq_div_iff h_σS h_σT] at h
  exact (mul_left_cancel₀ h_ne h1).symm

/-- **External and internal standardization give different values (combined).**
    When σ differs between populations and the score is not at either mean,
    externally and internally standardized scores differ. When σ_S = σ_T
    but μ_S ≠ μ_T, the scores always differ (see `external_vs_internal_differ_mean`).

    Note: when both μ and σ differ, there is exactly one score value
    pgs = (μ_S σ_T - μ_T σ_S)/(σ_T - σ_S) where the standardizations agree.
    For all other scores, they differ. The equal-σ and equal-μ sub-cases
    (proven above) cover the cases most relevant to PGS portability,
    where typically either the mean shifts or the variance changes. -/
theorem external_vs_internal_differ
    (pgs μ σ_S σ_T : ℝ)
    (h_σS : σ_S ≠ 0) (h_σT : σ_T ≠ 0)
    (h_diff : σ_S ≠ σ_T)
    (h_pgs : pgs ≠ μ) :
    externallyStandardized pgs μ σ_S ≠
      internallyStandardized pgs μ σ_T :=
  external_vs_internal_differ_variance pgs μ σ_S σ_T h_σS h_σT h_diff h_pgs

/-- **Percentile rank is standardization-invariant within a population.**
    The percentile of an individual is the same regardless of
    standardization choice (it's a monotone transformation). -/
theorem percentile_invariant_to_standardization
    (μ σ : ℝ) (h_σ : 0 < σ) :
    -- Standardization is strictly increasing → preserves order
    ∀ pgs₁ pgs₂ : ℝ, pgs₁ < pgs₂ →
      externallyStandardized pgs₁ μ σ < externallyStandardized pgs₂ μ σ := by
  intro pgs₁ pgs₂ h
  unfold externallyStandardized
  exact div_lt_div_of_pos_right (by linarith) h_σ

end Standardization

end Calibrator
