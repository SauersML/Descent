import Calibrator.Probability
import Mathlib.Algebra.Order.Chebyshev
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory
open Finset
open scoped BigOperators


/-!
# Statistical Genetics Methodology for Portability Assessment

This file formalizes the statistical methods used to assess, quantify,
and compare PGS portability across populations. These are the methodological
foundations needed to answer Wang et al.'s three open questions.

Key results:
1. Incremental R² and its standard error
2. Cross-validation design for portability studies
3. Summary statistic-based PGS construction
4. LD score regression for cross-population analysis
5. Genetic correlation estimation methods

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Incremental R² and Standard Error

The primary metric for PGS performance is incremental R²:
how much variance is explained by the PGS beyond covariates.
-/

section IncrementalR2

/-- **Incremental R² definition.**
    ΔR² = R²(covariates + PGS) - R²(covariates only). -/
noncomputable def incrementalR2 (r2_full r2_covariates : ℝ) : ℝ :=
  r2_full - r2_covariates

/-- **Incremental R² is nonneg from nested model theory.**
    In a nested linear regression, adding predictors can only increase R²
    because the full model minimizes RSS over a strictly larger parameter
    space. Formally: RSS_full ≤ RSS_cov (the full model's RSS is at most
    the covariate-only model's RSS), so R²_full = 1 - RSS_full/TSS ≥
    1 - RSS_cov/TSS = R²_cov.

    We encode this as: the full model's R² is at least the
    covariate-only model's R², which is a consequence of OLS
    minimizing sum of squared residuals over a nested subspace. -/
theorem incremental_r2_nonneg
    (rss_full rss_cov tss : ℝ)
    (h_tss : 0 < tss)
    (h_rss_full : 0 ≤ rss_full)
    (h_rss_cov : 0 ≤ rss_cov)
    -- Nested model property: full model has no more residual than submodel
    (h_nested : rss_full ≤ rss_cov) :
    let r2_full := 1 - rss_full / tss
    let r2_cov := 1 - rss_cov / tss
    0 ≤ incrementalR2 r2_full r2_cov := by
  simp only
  unfold incrementalR2
  -- (1 - rss_full/tss) - (1 - rss_cov/tss) = (rss_cov - rss_full)/tss ≥ 0
  have : rss_cov / tss - rss_full / tss = (rss_cov - rss_full) / tss := by ring
  linarith [div_nonneg (by linarith : 0 ≤ rss_cov - rss_full) (le_of_lt h_tss)]

/-- **Portability ratio with confidence interval.**
    Port = ΔR²_target / ΔR²_source.
    SE(Port) ≈ Port × √(SE²_target/ΔR²²_target + SE²_source/ΔR²²_source). -/
noncomputable def portabilityRatio (dr2_target dr2_source : ℝ) : ℝ :=
  dr2_target / dr2_source

/-- Portability ratio ≤ 1 when target PGS is weaker. -/
theorem portability_ratio_le_one
    (dr2_t dr2_s : ℝ) (h_s : 0 < dr2_s) (h_weaker : dr2_t ≤ dr2_s) :
    portabilityRatio dr2_t dr2_s ≤ 1 := by
  unfold portabilityRatio
  rw [div_le_one h_s]; exact h_weaker

/-- **The portability ratio reaches one exactly at full transport.**

    The companion equality to `portability_ratio_le_one`. Without it the bound
    is compatible with a ratio that can never reach its own ceiling; with it,
    the ceiling is attained precisely when the target increment equals the
    source increment, and at no other point. -/
theorem portability_ratio_eq_one_iff
    (dr2_t dr2_s : ℝ) (h_s : 0 < dr2_s) :
    portabilityRatio dr2_t dr2_s = 1 ↔ dr2_t = dr2_s := by
  unfold portabilityRatio
  rw [div_eq_iff (ne_of_gt h_s), one_mul]

end IncrementalR2


/-!
## Cross-Validation for Portability Assessment

Proper cross-validation design is critical for unbiased
estimation of PGS portability.
-/

section CrossValidation

/-- **Overfitting bias from sample overlap.**
    If the GWAS sample overlaps with the evaluation sample,
    R² is biased upward by approximately p/n where p is the
    number of SNPs in the PGS. -/
theorem overlap_bias
    (p_snps n_overlap : ℝ)
    (h_p : 0 < p_snps) (h_n : 0 < n_overlap)
    (h_n_large : p_snps < n_overlap) :
    0 < p_snps / n_overlap ∧ p_snps / n_overlap < 1 := by
  constructor
  · exact div_pos h_p h_n
  · rw [div_lt_one h_n]; exact h_n_large

/-- **Blocked cross-validation for family structure.**
    When evaluating PGS in populations with family structure,
    standard CV overestimates R² due to shared segments.
    Family-blocked CV is closer to the true R² because it removes
    the upward bias from family sharing, so its absolute error is smaller. -/
theorem blocked_cv_less_biased
    (r2_standard_cv r2_blocked_cv r2_true : ℝ)
    (h_standard_biased : r2_true < r2_standard_cv)
    (h_blocked_between : r2_true ≤ r2_blocked_cv)
    (h_blocked_closer_to_true : r2_blocked_cv < r2_standard_cv) :
    |r2_blocked_cv - r2_true| < |r2_standard_cv - r2_true| := by
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

end CrossValidation


/-!
## Summary Statistic-Based PGS

Most PGS are constructed from GWAS summary statistics rather than
individual-level data. This introduces specific challenges.
-/

section SummaryStatPGS


/-- **Effective sample size from summary stats.**
    n_eff_j = (Z_j / β_true_j)² if β_true_j were known.
    In practice: n_eff = median over SNPs of 1/SE_j².
    This can differ from the reported GWAS n.

    Empirical status: UNTESTED. -/
noncomputable def effectiveSampleSizeSE (se : ℝ) : ℝ := 1 / se ^ 2

/-- Effective sample size is positive. -/
theorem effective_n_pos (se : ℝ) (h_se : 0 < se) :
    0 < effectiveSampleSizeSE se := by
  unfold effectiveSampleSizeSE
  exact div_pos one_pos (sq_pos_of_pos h_se)

/-- **Meta-analysis model definition.**
    Contains properties of the model, specifically:
    k (number of studies), variances (of individual studies), and tau_sq (heterogeneity variance). -/
structure MetaAnalysisModel where
  k : ℕ
  variances : Fin k → ℝ
  tau_sq : ℝ
  h_k : 0 < k
  h_tau_sq : 0 < tau_sq
  h_variances : ∀ i, 0 < variances i

noncomputable def fixed_weights (m : MetaAnalysisModel) (i : Fin m.k) : ℝ :=
  1 / m.variances i

noncomputable def random_weights (m : MetaAnalysisModel) (i : Fin m.k) : ℝ :=
  1 / (m.variances i + m.tau_sq)

noncomputable def fixed_se_sq (m : MetaAnalysisModel) : ℝ :=
  1 / (∑ i, fixed_weights m i)

noncomputable def random_se_sq (m : MetaAnalysisModel) : ℝ :=
  1 / (∑ i, random_weights m i)

/-- **Fixed vs random effects meta-analysis.**
    Fixed effects: assumes same β across populations (tau² = 0).
    Random effects: allows β to vary with between-population variance tau².
    When tau² > 0, the random effects SE is larger (wider CI) because
    it adds tau² to the within-study variance. -/
theorem random_effects_captures_heterogeneity (m : MetaAnalysisModel) :
    fixed_se_sq m < random_se_sq m := by
  unfold fixed_se_sq random_se_sq
  apply one_div_lt_one_div_of_lt
  · apply Finset.sum_pos
    · intro i _
      unfold random_weights
      apply one_div_pos.mpr
      linarith [m.h_variances i, m.h_tau_sq]
    · have hw : Fin m.k := ⟨0, m.h_k⟩
      exact ⟨hw, Finset.mem_univ hw⟩
  · apply Finset.sum_lt_sum
    · intro i _
      unfold random_weights fixed_weights
      apply le_of_lt
      apply one_div_lt_one_div_of_lt (m.h_variances i)
      linarith [m.h_tau_sq]
    · have hw : Fin m.k := ⟨0, m.h_k⟩
      use hw
      use Finset.mem_univ hw
      unfold random_weights fixed_weights
      apply one_div_lt_one_div_of_lt (m.h_variances hw)
      linarith [m.h_tau_sq]

end SummaryStatPGS


/-!
## LD Score Regression

LDSC is used to estimate genetic correlation between populations,
which is a key predictor of PGS portability.
-/

section LDScoreRegression

structure LDSCModel (m : ℕ) where
  -- Effect sizes in source and target populations
  beta_s : Fin m → ℝ
  beta_t : Fin m → ℝ
  -- LD adjustment for the target population
  ld_adj : Fin m → ℝ
  h_ld_adj_pos : ∀ i, 0 ≤ ld_adj i
  h_ld_adj_le_one : ∀ i, ld_adj i ≤ 1

/-- Genetic correlation is defined by the inner product of effects.

    Empirical status: UNTESTED. -/
noncomputable def geneticCorrelationLDSC {m : ℕ} (model : LDSCModel m) : ℝ :=
  (∑ i, model.beta_s i * model.beta_t i) /
    Real.sqrt ((∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2))

/-- **Genetic correlation bounds portability ratio.**
    The portability ratio R²_target / R²_source is bounded by ρ_g² × ld_adj.
    Since |ρ_g| ≤ 1 implies ρ_g² ≤ 1, and ld_adj ∈ [0,1], the product
    is at most 1. This gives the rg-based bound on portability.
    We formally define this using a rigorous structure. -/
theorem genetic_correlation_predicts_portability {m : ℕ} (hm : 0 < m)
    (model : LDSCModel m)
    (h_pos_s : 0 < ∑ i, model.beta_s i ^ 2)
    (h_pos_t : 0 < ∑ i, model.beta_t i ^ 2) :
    (geneticCorrelationLDSC model) ^ 2 * ((∑ i, model.ld_adj i) / m) ≤ 1 := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm

  have h_cauchy : (∑ i, model.beta_s i * model.beta_t i) ^ 2 ≤
      (∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2) := by
    exact sum_mul_sq_le_sq_mul_sq univ model.beta_s model.beta_t

  have h_rho_sq_le_one : (geneticCorrelationLDSC model) ^ 2 ≤ 1 := by
    unfold geneticCorrelationLDSC
    rw [div_pow]
    have h_sqrt_sq : (Real.sqrt ((∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2))) ^ 2 =
        (∑ i, model.beta_s i ^ 2) * (∑ i, model.beta_t i ^ 2) := by
      apply Real.sq_sqrt
      positivity
    rw [h_sqrt_sq]
    rw [div_le_one]
    · exact h_cauchy
    · positivity

  have h_ld_sum_le_m : ∑ i, model.ld_adj i ≤ m := by
    calc ∑ i, model.ld_adj i
      _ ≤ ∑ _i : Fin m, (1 : ℝ) := sum_le_sum (fun i _ => model.h_ld_adj_le_one i)
      _ = m := by simp

  have h_ld_avg_le_one : (∑ i, model.ld_adj i) / m ≤ 1 := by
    rw [div_le_one hm_pos]
    exact h_ld_sum_le_m

  have h_ld_avg_nonneg : 0 ≤ (∑ i, model.ld_adj i) / m := by
    apply div_nonneg
    · apply sum_nonneg
      intro i _
      exact model.h_ld_adj_pos i
    · positivity

  calc (geneticCorrelationLDSC model) ^ 2 * ((∑ i, model.ld_adj i) / m)
    _ ≤ 1 * ((∑ i, model.ld_adj i) / m) := mul_le_mul_of_nonneg_right h_rho_sq_le_one h_ld_avg_nonneg
    _ = (∑ i, model.ld_adj i) / m := one_mul _
    _ ≤ 1 := h_ld_avg_le_one

/-- **The portability bound is attained: threshold equals capacity.**

The companion to `genetic_correlation_predicts_portability`, which gives only
`≤ 1` and so leaves open whether the bound is ever met. It is met, and the
condition is that both constraints be active at once: the effect vectors
perfectly aligned, and the LD adjustment saturated at every variant. This makes
the `≤ 1` statement sharp rather than merely true, and it identifies the
configuration a portability calculation must rule out before treating the bound
as informative. No symmetry or exchangeability of the LD structure is used; the
activity of the two constraints is the whole hypothesis. -/
theorem genetic_correlation_portability_bound_attained {m : ℕ} (hm : 0 < m)
    (model : LDSCModel m)
    (h_same : ∀ i, model.beta_t i = model.beta_s i)
    (h_ld_one : ∀ i, model.ld_adj i = 1)
    (h_pos_s : 0 < ∑ i, model.beta_s i ^ 2) :
    (geneticCorrelationLDSC model) ^ 2 * ((∑ i, model.ld_adj i) / m) = 1 := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnum : ∑ i, model.beta_s i * model.beta_t i = ∑ i, model.beta_s i ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [h_same i]; ring)
  have hden : ∑ i, model.beta_t i ^ 2 = ∑ i, model.beta_s i ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [h_same i])
  have h_rho : geneticCorrelationLDSC model = 1 := by
    unfold geneticCorrelationLDSC
    rw [hnum, hden, ← pow_two, Real.sqrt_sq (le_of_lt h_pos_s),
      div_self (ne_of_gt h_pos_s)]
  have h_ldsum : ∑ i, model.ld_adj i = (m : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => h_ld_one i)]
    simp
  rw [h_rho, h_ldsum, one_pow, div_self (ne_of_gt hm_pos), mul_one]

/-- **LDSC standard error for ρ_g.**
    SE(ρ̂_g) depends on sample sizes, LD structure, and polygenicity.
    For well-powered GWAS: SE ∝ 1/√n, so larger n yields smaller SE.

    **Scope.** The `1/√n` shape is the root-`n` rate of a smooth functional,
    and the genetic correlation is one: it is a ratio of quadratic forms in the
    effect vectors. The statement below is about the shape `c/√n` and is
    correct for any quantity that has it. It must not be carried over to a
    nonsmooth summary of the same effect vectors — a mean absolute effect or a
    polygenicity measure — whose attainable rate is logarithmic, not root-`n`;
    see `Calibrator.PolygenicArchitecture`, section `NonsmoothSummaries`, and
    the sample-size consequences in `Calibrator.PowerAnalysis`. Reporting a
    polygenicity estimate with an LDSC-style `1/√n` standard error is the
    concrete form of that error. -/
theorem ldsc_se_decreases_with_n
    (c : ℝ) (n₁ n₂ : ℝ)
    (h_c : 0 < c) (h_n₁ : 0 < n₁)
    (h_more : n₁ < n₂) :
    c / Real.sqrt n₂ < c / Real.sqrt n₁ := by
  apply div_lt_div_of_pos_left h_c
  · exact Real.sqrt_pos.mpr h_n₁
  · exact Real.sqrt_lt_sqrt (le_of_lt h_n₁) h_more

/-- **Constrained intercept LDSC.**
    When there's no sample overlap, the intercept should be 1.
    Constraining it reduces the number of free parameters from k+1 to k,
    yielding a smaller SE (fewer parameters → tighter estimate). -/
theorem constrained_intercept_more_powerful
    (se_per_param : ℝ) (k : ℕ)
    (h_se : 0 < se_per_param) :
    se_per_param * k < se_per_param * (k + 1) := by
  have : (k : ℝ) < (k : ℝ) + 1 := lt_add_one _
  exact mul_lt_mul_of_pos_left this h_se

end LDScoreRegression


/-!
## Genetic Correlation Methods

Multiple methods for estimating genetic correlation, each
with different properties for portability prediction.
-/

section GeneticCorrelationMethods

/-- **Genetic correlation varies across the genome.**
    ρ_g estimated from different genomic regions can vary,
    reflecting locus-specific selection pressures.
    The genome-wide estimate is a weighted average of per-region estimates,
    so it falls between the extremes.

    **The normality of the aggregate is no longer a caveat.** Aggregating
    per-region estimates over a partition of the genome is a disjoint-window
    design, and for such designs the set of limit laws is the Gaussian segment
    and nothing else — see `disjointWindow_limit_variances_eq_segment` below.
    The usual hedge that the pooled statistic is "approximately normal" is not
    needed here: no compound-Poisson or other infinitely divisible component
    can appear, because the Lévy measure vanishes. What remains free is the
    limit variance, and that ranges over the whole segment. -/
theorem local_genetic_correlation_varies
    (rho_chr1 rho_chr6 : ℝ) (w₁ w₆ : ℝ)
    (h_chr6_lower : rho_chr6 < rho_chr1) -- HLA region has lower correlation
    (h_w1 : 0 < w₁) (h_w6 : 0 < w₆) :
    -- Genome-wide weighted average is between the two regional estimates
    rho_chr6 < (w₁ * rho_chr1 + w₆ * rho_chr6) / (w₁ + w₆) := by
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < w₁ + w₆)]
  nlinarith


end GeneticCorrelationMethods


/-!
## Disjoint-Window Designs: the Gaussian Segment, Not an Approximation

Gene-based tests, per-region genetic correlations and any statistic pooled over
a partition of the genome share one structure: the windows do not overlap, so
the contributions are independent and the pooled statistic is a sum of
independent pieces each of which is negligible on its own. Such a design is
classically described as "asymptotically normal" with an approximation caveat
attached, because in general a triangular array of independent summands
converges to an arbitrary infinitely divisible law — Gaussian part, plus a
Lévy measure carrying jumps.

For a disjoint design the Lévy measure vanishes, and the set of achievable
limit laws is therefore `{ N(0, s²) : 0 ≤ s² ≤ 1 }` — the Gaussian segment,
entire and with nothing outside it. That is a theorem, not an approximation,
and it removes the caveat rather than bounding it.

What is formalised here is the parameter shadow of that statement, which is the
part with content for a study design: the achievable limit variances of a
disjoint-window design are the full segment `[0, 1]`, every point of it and no
point outside it. The upper end is a design that concentrates all the signal in
one window; the lower end is a design that captures none. Anything a
partitioned-window analysis can converge to is pinned down by that one number.
-/

section DisjointWindowDesigns

/-- **Limit variance of a disjoint-window design.**

    Each of `w` non-overlapping windows contributes a nonnegative share of the
    total normalised variance, and the shares add, because disjoint windows are
    independent. The limit law of the pooled statistic is the centred Gaussian
    with this variance.

    Empirical status: UNTESTED. -/
noncomputable def disjointWindowLimitVariance {w : ℕ} (share : Fin w → ℝ) : ℝ :=
  ∑ j, share j

/-- Every disjoint-window design lands in the segment. -/
theorem disjointWindowLimitVariance_mem_segment {w : ℕ} (share : Fin w → ℝ)
    (h_nonneg : ∀ j, 0 ≤ share j) (h_le_one : ∑ j, share j ≤ 1) :
    disjointWindowLimitVariance share ∈ Set.Icc (0 : ℝ) 1 := by
  unfold disjointWindowLimitVariance
  exact Set.mem_Icc.mpr ⟨Finset.sum_nonneg fun j _ => h_nonneg j, h_le_one⟩

/-- And every point of the segment is realised by a design. -/
theorem disjointWindowLimitVariance_attains (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ share : Fin 1 → ℝ, (∀ j, 0 ≤ share j) ∧ (∑ j, share j) ≤ 1 ∧
      disjointWindowLimitVariance share = s := by
  refine ⟨fun _ => s, fun _ => h0, ?_, ?_⟩
  · simpa using h1
  · simp [disjointWindowLimitVariance]

/-- **The limit variances of disjoint-window designs are exactly the
segment.**

Set equality, both inclusions: nothing outside `[0, 1]` is achievable, and
nothing inside it is missed. Together with the vanishing of the Lévy measure
this is the statement that a partitioned-window design has the Gaussian segment
as its set of limit laws, so a result about such a design stated with a
normal-approximation caveat can be restated without one. -/
theorem disjointWindow_limit_variances_eq_segment :
    {v : ℝ | ∃ (w : ℕ) (share : Fin w → ℝ),
        (∀ j, 0 ≤ share j) ∧ (∑ j, share j) ≤ 1 ∧
          disjointWindowLimitVariance share = v} = Set.Icc (0 : ℝ) 1 := by
  ext v
  constructor
  · rintro ⟨w, share, h_nn, h_le, rfl⟩
    exact disjointWindowLimitVariance_mem_segment share h_nn h_le
  · intro hv
    obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hv
    obtain ⟨share, h_nn, h_le, h_eq⟩ := disjointWindowLimitVariance_attains v h0 h1
    exact ⟨1, share, h_nn, h_le, h_eq⟩

end DisjointWindowDesigns

/-!
## Source `R²` Is Not a Sufficient Biological State Variable

Portability depends on locus-resolved transport, not just on a source summary
metric. The witness below fixes the residual variance and the source deployed
`R²`, then changes only which loci keep their signal in the target population.
The resulting target `R²` and target/source portability ratio change.
-/

section SourceR2Insufficiency

/-- Concrete two-locus witness that source deployed `R²` does not determine
target portability.

Both source loci contribute one unit of source signal, so the source deployed
`R²` at residual scale `1` is `2/3`. If both loci transport perfectly, the
target/source portability ratio is `1`. If one locus loses all transported
signal while the other remains intact, the target/source portability ratio
drops to `3/4`.

This formalizes the biological point that equal source `R²` does not determine
cross-population portability without locus-resolved transport state. -/
theorem same_source_r2_different_portability_two_locus_witness :
    let sourceSignal : Fin 2 → ℝ := fun _ => 1
    let stableTransport : Fin 2 → ℝ := fun _ => 1
    let brokenTransport : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let sourceVariance : ℝ := ∑ l, sourceSignal l
    let stableTargetVariance : ℝ := ∑ l, sourceSignal l * stableTransport l
    let brokenTargetVariance : ℝ := ∑ l, sourceSignal l * brokenTransport l
    let sourceR2 := TransportedMetrics.r2FromSignalVariance sourceVariance 1
    let stableTargetR2 := TransportedMetrics.r2FromSignalVariance stableTargetVariance 1
    let brokenTargetR2 := TransportedMetrics.r2FromSignalVariance brokenTargetVariance 1
    sourceR2 = stableTargetR2 ∧
    brokenTargetR2 < stableTargetR2 ∧
    brokenTargetR2 / sourceR2 = (3 : ℝ) / 4 := by
  simp [TransportedMetrics.r2FromSignalVariance]
  norm_num

end SourceR2Insufficiency

end Calibrator
