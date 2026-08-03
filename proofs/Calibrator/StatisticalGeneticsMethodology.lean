/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
4. `LDSCModel` as a data record, and root-`n` standard-error shape results stated
   against it. **No LD score regression is formalized here** — nothing in this file
   regresses chi-squared statistics on LD scores or estimates an intercept.
5. **No genetic-correlation estimator is defined in this file.** Cosine similarity of
   effect vectors under an LDSC name is not one, and the measurements refuting that reading
   are recorded below. Do not read items 4 and 5 as capabilities this module provides.

Reference: Wang et al. (2026), Nature Communications 17:942 -- for the three open
questions these methods are aimed at, not for the methods themselves. Incremental
R-squared, LD score regression and genetic-correlation estimation are standard, and
what is proved about them here is derived here; that paper contains none of it.
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

/-- **Increments telescope.** The gain from covariates to full equals the gain through any
intermediate model plus the gain from there. A body that failed this would not be an increment. -/
theorem incrementalR2_telescope (a b c : ℝ) :
    incrementalR2 a b + incrementalR2 b c = incrementalR2 a c := by
  unfold incrementalR2; ring

/-- Nesting the models makes the increment nonnegative. -/
theorem incrementalR2_nonneg (r2_full r2_covariates : ℝ)
    (h : r2_covariates ≤ r2_full) : 0 ≤ incrementalR2 r2_full r2_covariates := by
  unfold incrementalR2; linarith

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

/-- **The middle of three ordered reals is nearer the lowest, in absolute
    value:** from `t ≤ b < s` and `t < s`, conclude `|b - t| < |s - t|`.

    **The claim is the hypothesis `h_blocked_closer_to_true`.** Read as
    methodology this says family-blocked cross-validation lands between the
    truth and the optimistic standard-CV estimate, so its absolute error is
    smaller. But "blocked lands below standard" is assumed by name, and
    "blocked is not below the truth" is assumed too; what the proof adds is that
    an ordering between three reals can be rewritten with absolute values. It
    does not derive the ordering from family sharing, from segment sharing, or
    from any property of a cross-validation scheme, none of which occur below. -/
theorem abs_sub_lt_abs_sub_of_between
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


/-! **Deleted: `effectiveSampleSizeSE se = 1/se^2`, together with
`effectiveSampleSizeSE_lt_corrected` and the positivity lemma stated about it.**

| `p` | `1/SE²` | `effectiveSampleSizeFromSE` | error |
|---|---|---|---|
| 0.5 | 996 | 1992 | −50.2% |
| 0.3 | 838 | 1996 | −58.1% |
| 0.1 | 359 | 1994 | −82.1% |
| 0.05 | 189 | 1993 | −90.5% |
| 0.01 | 39 | 1976 | **−98.0%** |

This is the missing-parameter class: no allele frequency appears in the signature, so no
constant repairs it. The same defect falsifies `ridgeBalance`. The expression `1/SE²` is a
correct inverse-variance meta-analysis **weight**, and where a weight is wanted
`fixed_weights` below is the declaration that says so. Measured in
`proofs/validation/empirical/popgen_diff2/`.

`effectiveSampleSizeFromSE` is the sample size. -/

/-- **Effective sample size from a standard error.**

    `n_eff = 1/(SE² · 2p(1-p))` for a standardized trait. Recovers the true `n` to about 1%
    across allele frequencies from 0.5 down to 0.01, where `1/SE²` alone understates
    it by 50% at `p = 0.5` and by 98% at `p = 0.01` (`proofs/validation/empirical/popgen_diff2/`).

    **Scope caveat:** it overstates `N` for large-effect SNPs, by `+27%` at `h²_snp = 0.10` and
    `+64%` at `0.20`. The derivation assumes the SNP explains a negligible share of variance,
    which is exactly where a GWAS hit does not sit. Ratios to the true `N` at small effect:
    `0.9965, 1.0065, 1.0966, 1.0283`.

    Empirical status: **VALIDATED at small effect**, biased upward at large effect
    (`proofs/validation/empirical/ldsc_diff/`). -/
noncomputable def effectiveSampleSizeFromSE (se p : ℝ) : ℝ :=
  1 / (se ^ 2 * (2 * p * (1 - p)))

/-- The effective sample size is positive at any polymorphic frequency. -/
theorem effective_n_pos (se p : ℝ) (h_se : 0 < se) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < effectiveSampleSizeFromSE se p := by
  have hc : 0 < 2 * p * (1 - p) := by nlinarith
  have hse2 : 0 < se ^ 2 := by positivity
  unfold effectiveSampleSizeFromSE
  exact div_pos one_pos (by positivity)

/-- **Meta-analysis model definition.**
    Contains properties of the model, specifically:
    k (number of studies), variances (of individual studies), and tau_sq
    (heterogeneity variance). -/
structure MetaAnalysisModel where
  k : ℕ
  variances : Fin k → ℝ
  tau_sq : ℝ
  h_k : 0 < k
  h_tau_sq : 0 < tau_sq
  h_variances : ∀ i, 0 < variances i

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MetaAnalysisModel.witness : MetaAnalysisModel where
  k := 1
  variances := fun _ ↦ 1
  tau_sq := 1
  h_k := by norm_num
  h_tau_sq := by norm_num
  h_variances := fun _ ↦ by norm_num

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

/-- **The class is inhabited at every panel size**, so the results over it are not
vacuous. `ld_adj = 1` is the no-LD-adjustment panel: the two bounds on `ld_adj`
are the only constraints the structure imposes, and both are attained there. -/
noncomputable def LDSCModel.witness (m : ℕ) : LDSCModel m where
  beta_s := fun _ ↦ 0
  beta_t := fun _ ↦ 0
  ld_adj := fun _ ↦ 1
  h_ld_adj_pos := fun _ ↦ by norm_num
  h_ld_adj_le_one := fun _ ↦ by norm_num

/-! **Deleted: `geneticCorrelationLDSC`, together with
`genetic_correlation_predicts_portability` and
`genetic_correlation_portability_bound_attained`.**

* **LD alone breaks it.** Two SNPs at `r = 1/2` with joint effects `(1,0)` and `(0,1)` are
  exactly orthogonal, `ρ_g = 0`. The *marginal* effects are `(1,1/2)` and `(1/2,1)`, giving
  `cos = 0.8` exactly — and marginal effects are what summary statistics supply.
* **It clashes with this corpus's own weighting.** `additiveVariance` weights per-allele
  effects by `2p(1-p)`; this body weighted uniformly: `0.4714` unweighted against `0.3739`
  HWE-weighted on the same vectors. `LDSCModel` carries no allele frequencies, so neither
  weighted estimand is even expressible.
* **It attenuates where LDSC does not.** At true `ρ_g = 0.60` with block-AR(1) LD and no
  overlap it returned `0.529, 0.461, 0.373, 0.161, 0.076` at `M/N = 0.2, 0.5, 1, 4, 10` —
  **13% of the truth at the realistic ratio** — following `ρ_g·∏ₖ√(h²L̄/(h²L̄ + M/Nₖ))`.
  Genuine bivariate LDSC does not: genetic covariance `0.311 ± 0.120` against a true `0.304`
  at `M/N = 10`. The attenuation is a pure noise effect, not an LD effect.
* **Sample overlap manufactures signal.** At true `ρ_g = 0`, `ρ_e = 0.8` it returned `0.007`
  at no overlap, `0.153` at 50%, and **`0.282` at full overlap — out of nothing** — while
  LDSC's intercept absorbs the overlap and its slope reads `-0.002`. On a real signal
  (`ρ_g = 0.30`) full overlap inflated it to `0.479`, **+60%**, in the direction of
  `sign(ρ_e)`. The bias is `(M/N)·ρ_pheno/(h²L̄ + M/N)`. A negative control confirms the
  mechanism: 100% overlap with `ρ_e = 0` gives `-0.003 ± 0.012`, so it is overlap **times**
  phenotypic correlation that bites, not overlap alone.

The two deleted theorems bounded `ρ_g² · (∑ ld_adj)/m ≤ 1` and gave its attainment. Both were
Cauchy–Schwarz on the cosine, so neither said anything about a genetic correlation estimated
from summary statistics; they are gone with the definition they were about. `LDSCModel`
itself is retained: the LDSC standard-error results below use it. -/

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

/-- **`k` parameters cost less than `k+1`, at any positive per-parameter price.**

    The statement contains no standard error. `se_per_param` is a variable name, not a
    quantity the theorem constrains, so what is proved is that `k` parameters cost less than
    `k+1` at any positive per-parameter price — arithmetic, not a statement about estimator
    variance.

    The empirical direction does hold **without** overlap: constrained was tighter in 6 of 7
    simulated arms. But the docstring's premise, "when there's no sample overlap", is exactly
    what a user cannot check from summary statistics — and constraining the intercept **under**
    full overlap returns `ρ̂_g = 1.350` where the truth is `0`. The premise is the whole
    content and it is unverifiable in the setting the definition serves.

    Empirical status: theorem **PROVED** and trivial; the SE reading is **UNDERPOWERED**
    (6/7 arms, unweighted OLS without jackknife) and the no-overlap premise is
    **unverifiable from summary statistics** (`proofs/validation/empirical/ldsc_diff/`). -/
theorem cost_of_k_params_lt_cost_of_k_succ
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

    **The normality of the aggregate remains a caveat, and this docstring used to deny
    it.** It claimed that for a disjoint-window design the set of limit laws is the
    Gaussian segment and nothing else, so no "approximately normal" hedge would be needed.
    No such theorem exists in this corpus, and the disjoint licence it would appeal to is
    not proved here. What is formalized below is the variance *parameter* of a hypothesised
    Gaussian limit. -/
theorem lt_weightedAverage_of_lt
    (rho_chr1 rho_chr6 : ℝ) (w₁ w₆ : ℝ)
    (h_chr6_lower : rho_chr6 < rho_chr1) -- HLA region has lower correlation
    (h_w1 : 0 < w₁) (h_w6 : 0 < w₆) :
    -- Genome-wide weighted average is between the two regional estimates
    rho_chr6 < (w₁ * rho_chr1 + w₆ * rho_chr6) / (w₁ + w₆) := by
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < w₁ + w₆)]
  nlinarith


end GeneticCorrelationMethods


/-!
## Disjoint-Window Designs: the variance parameter, not the limit law

Gene-based tests, per-region genetic correlations and any statistic pooled over
a partition of the genome share one structure: the windows do not overlap, so
the contributions are independent and the pooled statistic is a sum of
independent pieces each of which is negligible on its own. Such a design is
classically described as "asymptotically normal" with an approximation caveat
attached, because in general a triangular array of independent summands
converges to an arbitrary infinitely divisible law — Gaussian part, plus a
Lévy measure carrying jumps.

It is often said that for a disjoint design the Lévy measure vanishes, so the
achievable limit laws are exactly `{ N(0, s²) : 0 ≤ s² ≤ 1 }` — the Gaussian
segment, with nothing outside it. **This corpus does not prove that.** No
probabilistic object occurs in the formal statement below and the central limit
theorem is not formalized here, so nothing in this file may call the
Gaussian-segment claim a theorem rather than an approximation.

What is formalized here is only the **variance parameter** of a hypothesised
Gaussian limit: the achievable values of `∑ⱼ share j` for a disjoint-window
design are the full segment `[0, 1]`. That is a statement about a sum of
nonnegative shares. It is worth having — the upper end is a design
concentrating all signal in one window, the lower end one capturing none — but
it is not evidence that the limit is Gaussian, and nothing below supplies that.
-/

section DisjointWindowDesigns

/-- **Limit variance of a disjoint-window design.**

    Each of `w` non-overlapping windows contributes a nonnegative share of the
    total normalised variance, and the shares add, because disjoint windows are
    independent.

    **This definition is `∑ j, share j` and nothing more.** The sentence that used to
    close this docstring -- "the limit law of the pooled statistic is the centred
    Gaussian with this variance" -- is not established anywhere in this corpus. It is
    the conclusion of the disjoint licence (Theorem D in `Calibrator.EpistaticChaos`),
    which is *not formalized*: it needs a central limit theorem for low-influence
    multilinear forms, and carrying it as an interface hypothesis-field would assume it
    rather than prove it. Naming a sum "limit variance" does not supply it.

    So read this as the variance *parameter* of a hypothesised Gaussian limit, not as
    evidence that the limit is Gaussian.

    Empirical status: UNTESTED. -/
noncomputable def disjointWindowLimitVariance {w : ℕ} (share : Fin w → ℝ) : ℝ :=
  ∑ j, share j

/-- Every disjoint-window design lands in the segment. -/
theorem disjointWindowLimitVariance_mem_segment {w : ℕ} (share : Fin w → ℝ)
    (h_nonneg : ∀ j, 0 ≤ share j) (h_le_one : ∑ j, share j ≤ 1) :
    disjointWindowLimitVariance share ∈ Set.Icc (0 : ℝ) 1 := by
  unfold disjointWindowLimitVariance
  exact Set.mem_Icc.mpr ⟨Finset.sum_nonneg fun j _ ↦ h_nonneg j, h_le_one⟩

/-- And every point of the segment is realised by a design. -/
theorem disjointWindowLimitVariance_attains (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ share : Fin 1 → ℝ, (∀ j, 0 ≤ share j) ∧ (∑ j, share j) ≤ 1 ∧
      disjointWindowLimitVariance share = s := by
  refine ⟨fun _ ↦ s, fun _ ↦ h0, ?_, ?_⟩
  · simpa using h1
  · simp [disjointWindowLimitVariance]

/-- **The limit variances of disjoint-window designs are exactly the
segment.**

Set equality, both inclusions: nothing outside `[0, 1]` is achievable, and
nothing inside it is missed.

**What this is, stated exactly.** Unfolding `disjointWindowLimitVariance`, the claim is
that the set of sums of finitely many nonnegative reals with total at most one is
`[0, 1]`. That is arithmetic about the real line. No genotype, no design, no
independence and no limit theorem enters the proof, and none could -- there is no
probabilistic object in the statement.

**It therefore does not license dropping a normal-approximation caveat**, which is what
this docstring used to claim. That licence is the disjoint-limit theorem (Theorem D in
`Calibrator.EpistaticChaos`), whose Gaussian conclusion is not formalized in this corpus;
this result supplies only the range of the variance parameter *given* that conclusion.
Keeping the two apart is the point: one is a fact about `Set.Icc`, the other is a central
limit theorem nobody here has proved. -/
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
theorem same_sourceR2_different_targetR2_two_signal_witness :
    let sourceSignal : Fin 2 → ℝ := fun _ ↦ 1
    let stableTransport : Fin 2 → ℝ := fun _ ↦ 1
    let brokenTransport : Fin 2 → ℝ := fun i ↦ if i = 0 then 1 else 0
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
