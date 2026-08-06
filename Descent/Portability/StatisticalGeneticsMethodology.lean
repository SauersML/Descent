/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift
-- For `summary_statistic_coherence_not_locally_certifiable`,
-- `no_bounded_locality_hierarchy`, `nonbipartite_twin_tv_gap` and
-- `expanderAgreementFloor`: the window-audit section below is what the twin
-- construction says about neighbourhood-consistency QC.
import Descent.Conditionals.LocalToGlobalCoherence

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Program`:
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Portability

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
  Descent.Core.difference r2_full r2_covariates

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem incrementalR2_at_reference_point :
    incrementalR2 (3 / 4) (1 / 4) = 1 / 2 := by
  norm_num [incrementalR2,
      Descent.Core.difference]


/-- **Increments telescope.** The gain from covariates to full equals the gain through any
intermediate model plus the gain from there. A body that failed this would not be an increment. -/
theorem incrementalR2_telescope (a b c : ℝ) :
    incrementalR2 a b + incrementalR2 b c = incrementalR2 a c := by
  unfold incrementalR2 Descent.Core.difference; ring

/-- Incremental R² vanishes exactly when the full and covariate-only fits explain the
same fraction of variance. -/
theorem incrementalR2_eq_zero_iff (r2_full r2_covariates : ℝ) :
    incrementalR2 r2_full r2_covariates = 0 ↔ r2_full = r2_covariates := by
  unfold incrementalR2 Descent.Core.difference
  exact sub_eq_zero

/-- Nesting the models makes the increment nonnegative. -/
theorem incrementalR2_nonneg (r2_full r2_covariates : ℝ)
    (h : r2_covariates ≤ r2_full) : 0 ≤ incrementalR2 r2_full r2_covariates := by
  unfold incrementalR2 Descent.Core.difference; linarith

/-- **Incremental R² is nonneg from nested model theory.**
    In a nested linear regression, adding predictors can only increase R²
    because the full model minimizes RSS over a strictly larger parameter
    space. Formally: RSS_full ≤ RSS_cov (the full model's RSS is at most
    the covariate-only model's RSS), so R²_full = 1 - RSS_full/TSS ≥
    1 - RSS_cov/TSS = R²_cov.

    We encode this as: the full model's R² is at least the
    covariate-only model's R², which is a consequence of OLS
    minimizing sum of squared residuals over a nested subspace. -/
theorem incrementalR2_nonneg_of_rss_le
    (rss_full rss_cov tss : ℝ)
    (h_tss : 0 < tss)
    -- Nested model property: full model has no more residual than submodel
    (h_nested : rss_full ≤ rss_cov) :
    let r2_full := 1 - rss_full / tss
    let r2_cov := 1 - rss_cov / tss
    0 ≤ incrementalR2 r2_full r2_cov := by
  simp only
  unfold incrementalR2 Descent.Core.difference
  -- (1 - rss_full/tss) - (1 - rss_cov/tss) = (rss_cov - rss_full)/tss ≥ 0
  have : rss_cov / tss - rss_full / tss = (rss_cov - rss_full) / tss := by ring
  linarith [div_nonneg (by linarith : 0 ≤ rss_cov - rss_full) (le_of_lt h_tss)]

/-- **Portability ratio with confidence interval.**
    Port = ΔR²_target / ΔR²_source.
    SE(Port) ≈ Port × √(SE²_target/ΔR²²_target + SE²_source/ΔR²²_source). -/
noncomputable def portabilityRatio (dr2_target dr2_source : ℝ) : ℝ :=
  Descent.Core.ratio dr2_target dr2_source

/-- **portabilityRatio at zero dr2_source, named.** A source cohort with no explained variance
gives no baseline to be portable from. Lean returns `0`, complete failure to transfer, which is
indistinguishable from a real transfer failure against a working source. Consumers must require
`dr2_source ≠ 0`. -/
theorem portabilityRatio_zero_dr2source_is_junk (dr2_target : ℝ) :
    portabilityRatio dr2_target 0 = 0 := by
  unfold portabilityRatio Descent.Core.ratio
  simp

/-- Portability ratio ≤ 1 when target PGS is weaker. -/
theorem portabilityRatio_le_one
    (dr2_t dr2_s : ℝ) (h_s : 0 < dr2_s) (h_weaker : dr2_t ≤ dr2_s) :
    portabilityRatio dr2_t dr2_s ≤ 1 := by
  unfold portabilityRatio Descent.Core.ratio
  rw [div_le_one h_s]; exact h_weaker

/-- **The portability ratio reaches one exactly at full transport.**

    The companion equality to `portabilityRatio_le_one`. Without it the bound
    is compatible with a ratio that can never reach its own ceiling; with it,
    the ceiling is attained precisely when the target increment equals the
    source increment, and at no other point. -/
theorem portabilityRatio_eq_one_iff
    (dr2_t dr2_s : ℝ) (h_s : 0 < dr2_s) :
    portabilityRatio dr2_t dr2_s = 1 ↔ dr2_t = dr2_s := by
  unfold portabilityRatio Descent.Core.ratio
  rw [div_eq_iff (ne_of_gt h_s), one_mul]

/-- Against a nonzero source increment, zero portability is exactly zero target
increment rather than an artifact of division by zero. -/
theorem portabilityRatio_eq_zero_iff
    (dr2_t dr2_s : ℝ) (h_s : dr2_s ≠ 0) :
    portabilityRatio dr2_t dr2_s = 0 ↔ dr2_t = 0 := by
  unfold portabilityRatio Descent.Core.ratio
  constructor
  · intro h
    calc
      dr2_t = dr2_t / dr2_s * dr2_s := (div_mul_cancel₀ dr2_t h_s).symm
      _ = 0 := by rw [h]; norm_num
  · rintro rfl
    norm_num

end IncrementalR2


/-!
## Cross-Validation for Portability Assessment

Proper cross-validation design is critical for unbiased
estimation of PGS portability.
-/

section CrossValidation

/-- Approximate upward R² bias from using `predictorCount` fitted predictors in an
evaluation sample with `overlapCount` overlapping observations. -/
noncomputable def sampleOverlapBias (predictorCount overlapCount : ℝ) : ℝ :=
  Descent.Core.ratio predictorCount overlapCount

/-- The overlap-bias scale is pinned away from both denominator boundaries. -/
theorem sampleOverlapBias_at_reference_point : sampleOverlapBias 1 4 = 1 / 4 := by
  norm_num [sampleOverlapBias,
      Descent.Core.ratio]

/-- **Overfitting bias from sample overlap is positive.**
    If the GWAS sample overlaps with the evaluation sample,
    R² is biased upward by approximately p/n where p is the
    number of SNPs in the PGS. -/
theorem sampleOverlapBias_pos
    (p_snps n_overlap : ℝ)
    (h_p : 0 < p_snps) (h_n : 0 < n_overlap) :
    0 < sampleOverlapBias p_snps n_overlap := by
  unfold sampleOverlapBias Descent.Core.ratio
  exact div_pos h_p h_n

/-- The approximate overlap bias is below one exactly when the number of fitted
predictors is smaller than the positive overlap sample. -/
theorem sampleOverlapBias_lt_one_iff
    (p_snps n_overlap : ℝ) (h_n : 0 < n_overlap) :
    sampleOverlapBias p_snps n_overlap < 1 ↔ p_snps < n_overlap := by
  unfold sampleOverlapBias Descent.Core.ratio
  rw [div_lt_one h_n]

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
`validation/empirical/popgen_diff2/`.

`effectiveSampleSizeFromSE` is the sample size. -/

/-- **Effective sample size from a standard error.**

    `n_eff = 1/(SE² · 2p(1-p))` for a standardized trait. Recovers the true `n` to about 1%
    across allele frequencies from 0.5 down to 0.01, where `1/SE²` alone understates
    it by 50% at `p = 0.5` and by 98% at `p = 0.01` (`validation/empirical/popgen_diff2/`).

    **Scope caveat:** it overstates `N` for large-effect SNPs, by `+27%` at `h²_snp = 0.10` and
    `+64%` at `0.20`. The derivation assumes the SNP explains a negligible share of variance,
    which is exactly where a GWAS hit does not sit. Ratios to the true `N` at small effect:
    `0.9965, 1.0065, 1.0966, 1.0283`.

    Empirical status: **VALIDATED at small effect**, biased upward at large effect
    (`validation/empirical/ldsc_diff/`). -/
noncomputable def effectiveSampleSizeFromSE (se p : ℝ) : ℝ :=
  1 / (se ^ 2 * (2 * p * (1 - p)))

/-- **The effective sample size at a monomorphic marker, named.** With `p = 0` the dosage has no
variance, and the standard error of an effect estimated at a monomorphic marker carries no
information about sample size at all -- at fixed `se` the formula diverges. The divisor
`2 * p * (1 - p)` is zero and Lean returns `0`: the SMALLEST effective sample size, so a marker
that should be excluded from a meta-analysis instead enters it carrying weight zero, silently,
and the total effective N is understated rather than flagged. Consumers must require `p ≠ 0`. -/
theorem effectiveSampleSizeFromSE_monomorphic_is_junk (se : ℝ) :
    effectiveSampleSizeFromSE se 0 = 0 := by
  unfold effectiveSampleSizeFromSE
  simp

/-- **The effective sample size at a fixed marker, named.** The mirror branch at `p = 1`, by the
same `2 * p * (1 - p)` divisor and with the same consequence. Both ends of the frequency range
report zero effective sample size, so a marker fixed for the alternate allele and one fixed for
the reference are indistinguishable from each other and from a genuinely uninformative
polymorphic marker. Consumers must require `p ≠ 1`. -/
theorem effectiveSampleSizeFromSE_fixed_is_junk (se : ℝ) :
    effectiveSampleSizeFromSE se 1 = 0 := by
  unfold effectiveSampleSizeFromSE
  simp

/-- The SE-derived effective sample size vanishes exactly on its three singular
boundaries: zero standard error, absent allele, or fixed alternate allele. -/
theorem effectiveSampleSizeFromSE_eq_zero_iff (se p : ℝ) :
    effectiveSampleSizeFromSE se p = 0 ↔ se = 0 ∨ p = 0 ∨ p = 1 := by
  unfold effectiveSampleSizeFromSE
  constructor
  · intro h
    have h_denom : se ^ 2 * (2 * p * (1 - p)) = 0 := by
      by_contra h_ne
      exact (div_ne_zero one_ne_zero h_ne) h
    rcases mul_eq_zero.mp h_denom with h_se | h_frequency
    · exact Or.inl (sq_eq_zero_iff.mp h_se)
    · rcases mul_eq_zero.mp h_frequency with h | h
      · have h_p : p = 0 := by nlinarith
        exact Or.inr (Or.inl h_p)
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- The effective sample-size formula is positive exactly when the standard error is
nonzero and the marker is polymorphic. The sign of `se` is immaterial because it is squared. -/
theorem effectiveSampleSizeFromSE_pos_iff (se p : ℝ) :
    0 < effectiveSampleSizeFromSE se p ↔ se ≠ 0 ∧ 0 < p ∧ p < 1 := by
  unfold effectiveSampleSizeFromSE
  constructor
  · intro h
    have h_denom : 0 < se ^ 2 * (2 * p * (1 - p)) := one_div_pos.mp h
    rcases mul_pos_iff.mp h_denom with ⟨h_se_sq, h_frequency⟩ | ⟨h_se_sq, _⟩
    · refine ⟨?_, ?_⟩
      · intro h_zero
        rw [h_zero] at h_se_sq
        norm_num at h_se_sq
      · constructor <;> nlinarith
    · nlinarith [sq_nonneg se]
  · rintro ⟨h_se, hp0, hp1⟩
    apply one_div_pos.mpr
    exact mul_pos (sq_pos_of_ne_zero h_se) (by nlinarith)

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

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem fixed_weights_at_zero_denominator_is_junk (m : MetaAnalysisModel) (i : Fin m.k)
    (hzero : m.variances i = 0) :
    fixed_weights m i = 0 := by
  unfold fixed_weights
  rw [hzero, div_zero]


noncomputable def random_weights (m : MetaAnalysisModel) (i : Fin m.k) : ℝ :=
  1 / (m.variances i + m.tau_sq)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem random_weights_at_zero_denominator_is_junk (m : MetaAnalysisModel) (i : Fin m.k)
    (hzero : (m.variances i + m.tau_sq) = 0) :
    random_weights m i = 0 := by
  unfold random_weights
  rw [hzero, div_zero]


noncomputable def fixed_se_sq (m : MetaAnalysisModel) : ℝ :=
  1 / (∑ i, fixed_weights m i)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem fixed_se_sq_at_zero_denominator_is_junk (m : MetaAnalysisModel)
    (hzero : (∑ i, fixed_weights m i) = 0) :
    fixed_se_sq m = 0 := by
  unfold fixed_se_sq
  rw [hzero, div_zero]


noncomputable def random_se_sq (m : MetaAnalysisModel) : ℝ :=
  1 / (∑ i, random_weights m i)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem random_se_sq_at_zero_denominator_is_junk (m : MetaAnalysisModel)
    (hzero : (∑ i, random_weights m i) = 0) :
    random_se_sq m = 0 := by
  unfold random_se_sq
  rw [hzero, div_zero]


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

/-! **Deleted: `geneticCorrelationLDSC`, together with `genetic_correlation_predicts_portability`
and
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
    see `Descent.PopGen.PolygenicArchitecture`, section `NonsmoothSummaries`, and
    the sample-size consequences in `Descent.Decision.PowerAnalysis`. Reporting a
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

end LDScoreRegression


/-!
## Genetic Correlation Methods

Multiple methods for estimating genetic correlation, each
with different properties for portability prediction.
-/

section GeneticCorrelationMethods

/-- Two-region genome-wide genetic correlation formed with positive region weights. -/
noncomputable def twoRegionGeneticCorrelation
    (rhoFirst rhoSecond firstWeight secondWeight : ℝ) : ℝ :=
  (firstWeight * rhoFirst + secondWeight * rhoSecond) / (firstWeight + secondWeight)

/-- The regional average is pinned at equal weights between correlations zero and one-half. -/
theorem twoRegionGeneticCorrelation_at_reference_point :
    twoRegionGeneticCorrelation (1 / 2) 0 1 1 = 1 / 4 := by
  norm_num [twoRegionGeneticCorrelation]

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
theorem secondCorrelation_lt_twoRegionGeneticCorrelation
    (rho_chr1 rho_chr6 : ℝ) (w₁ w₆ : ℝ)
    (h_chr6_lower : rho_chr6 < rho_chr1) -- HLA region has lower correlation
    (h_w1 : 0 < w₁) (h_w6 : 0 < w₆) :
    rho_chr6 < twoRegionGeneticCorrelation rho_chr1 rho_chr6 w₁ w₆ := by
  unfold twoRegionGeneticCorrelation
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < w₁ + w₆)]
  nlinarith

/-- With positive weights and distinct regional correlations, the genome-wide average
is also strictly below the larger regional correlation. -/
theorem twoRegionGeneticCorrelation_lt_firstCorrelation
    (rho_chr1 rho_chr6 : ℝ) (w₁ w₆ : ℝ)
    (h_chr6_lower : rho_chr6 < rho_chr1)
    (h_w1 : 0 < w₁) (h_w6 : 0 < w₆) :
    twoRegionGeneticCorrelation rho_chr1 rho_chr6 w₁ w₆ < rho_chr1 := by
  unfold twoRegionGeneticCorrelation
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < w₁ + w₆)]
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
    the conclusion of the disjoint licence (Theorem D in `Descent.Blindness.EpistaticChaos`),
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
`Descent.Blindness.EpistaticChaos`), whose Gaussian conclusion is not formalized in this corpus;
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
## What a window audit of summary statistics can and cannot certify

The section above is about what a disjoint-window design *achieves*. This one is about what
a window-based **check** on reported summary statistics can *certify*, and the answer is
sharply less than the practice assumes.

Neighbourhood-consistency QC -- verifying that per-block marginal laws implied by reported
statistics agree wherever adjacent blocks overlap, at some window radius -- is the standard
diagnostic for whether a summary-statistic set could have come from one coherent
population. `Descent.Conditionals.LocalToGlobalCoherence` supplies a twin pair that defeats it: two
systems agreeing on every bounded-radius datum, one globally realizable and one at strictly
positive distance from every global law. Enlarging the radius does not help, and neither
does consulting every radius at once and combining the verdicts arbitrarily.

The gap is not marginal. The non-realizable twin sits at average marginal total-variation
distance at least `expanderAgreementFloor = 1/2 - sqrt 5 / 6`, which
`expanderAgreementFloor_gt` brackets above `0.127` -- a constant, not something that decays
with the window size.

Scope: the twin construction rests on Ramanujan-graph inputs that are classical and are
flagged as such in the source module. What is transported here is the packaging, not a new
expander result, and the theorem below is stated over an abstract audit so that it commits
to no particular QC procedure.
-/

section WindowAuditCeiling

/-- **A summary-statistic set can pass every window audit and still be far from coherent.**

Both halves of the twin construction at the summary-statistic reading, stated together
because either alone understates the result. The first conjunct is the impossibility: at no
radius `r` is there a certificate, computed from the audit output, that decides whether one
population generated the statistics. The second is the size of what is being missed: the
average marginal total-variation distance from every global law is strictly positive.

An audit that returns *identical output on a realizable and a non-realizable set* is not a
weak diagnostic; it is not a diagnostic. Escaping this requires data outside the window --
the joint content the marginals omit -- not a larger window or a longer hierarchy of
checks.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a transport of the twin construction
    into summary-statistic vocabulary, carrying no assertion about any released
    statistics. -/
theorem window_audit_cannot_certify_coherence
    {SummaryStatSet AuditOutput ι : Type*}
    (audit : ℕ → SummaryStatSet → AuditOutput)
    (onePopulationRealizable : SummaryStatSet → Prop)
    (coherentSet incoherentSet : SummaryStatSet)
    (hidenticalAudits : ∀ r : ℕ, audit r coherentSet = audit r incoherentSet)
    (hcoherent : onePopulationRealizable coherentSet)
    (hincoherent : ¬ onePopulationRealizable incoherentSet)
    (E : Finset ι) (hE : E.Nonempty) (agree tv : ι → ℝ) (β : ℝ)
    (hβ : β < Conditionals.expanderAgreementFloor)
    (htv : ∀ e ∈ E, agree e - β ≤ tv e)
    (hagree : Conditionals.expanderAgreementFloor * E.card ≤ ∑ e ∈ E, agree e) :
    (∀ r : ℕ, ¬ ∃ certify : AuditOutput → Prop,
        ∀ S : SummaryStatSet, onePopulationRealizable S ↔ certify (audit r S))
      ∧ 0 < (∑ e ∈ E, tv e) / E.card :=
  ⟨Conditionals.summary_statistic_coherence_not_locally_certifiable audit onePopulationRealizable
      coherentSet incoherentSet hidenticalAudits hcoherent hincoherent,
    Conditionals.nonbipartite_twin_tv_gap E hE agree tv β hβ htv hagree⟩

/-- **No hierarchy of window audits certifies coherence either.** The same twin pair is
identical on the whole radius family, so folding every radius into one verdict by any rule
whatsoever still fails to decide realizability. Recorded separately because "run the check
at every window size and combine" is the natural response to the theorem above, and it is
the response that does not work. -/
theorem window_audit_hierarchy_cannot_certify_coherence
    {SummaryStatSet AuditOutput Verdict : Type*}
    (audit : ℕ → SummaryStatSet → AuditOutput)
    (onePopulationRealizable : SummaryStatSet → Prop)
    (combine : (ℕ → AuditOutput) → Verdict) (accept : Verdict → Prop)
    (coherentSet incoherentSet : SummaryStatSet)
    (hidenticalAudits : ∀ r : ℕ, audit r coherentSet = audit r incoherentSet)
    (hcoherent : onePopulationRealizable coherentSet)
    (hincoherent : ¬ onePopulationRealizable incoherentSet) :
    ¬ ∀ S : SummaryStatSet,
        onePopulationRealizable S ↔ accept (combine (fun r ↦ audit r S)) :=
  Conditionals.no_bounded_locality_hierarchy audit onePopulationRealizable combine accept
    coherentSet incoherentSet hidenticalAudits hcoherent hincoherent

end WindowAuditCeiling

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
    let sourceR2 := PopGen.TransportedMetrics.r2FromSignalVariance sourceVariance 1
    let stableTargetR2 := PopGen.TransportedMetrics.r2FromSignalVariance stableTargetVariance 1
    let brokenTargetR2 := PopGen.TransportedMetrics.r2FromSignalVariance brokenTargetVariance 1
    sourceR2 = stableTargetR2 ∧
    brokenTargetR2 < stableTargetR2 ∧
    brokenTargetR2 / sourceR2 = (3 : ℝ) / 4 := by
  simp [PopGen.TransportedMetrics.r2FromSignalVariance, Descent.Core.share]
  norm_num

end SourceR2Insufficiency

/-- **The `2 p (1 - p)` in the effective sample size is the diploid genotype variance.**
`StatisticalGeneticsMethodology.effectiveSampleSizeFromSE` inverts `SE² · Var(dosage)`, and
`Var(dosage)` under Hardy-Weinberg proportions is `genotypeVarianceHWE`. Written inline the
two was free; here it is the ploidy, and an SE reported on a haploid dosage scale would
have to change this file rather than that definition. -/
theorem effectiveSampleSizeFromSE_uses_genotypeVarianceHWE (se p : ℝ) :
    Portability.effectiveSampleSizeFromSE se p = 1 / (se ^ 2 * genotypeVarianceHWE p) := by
  unfold Portability.effectiveSampleSizeFromSE genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

end Descent.Portability
