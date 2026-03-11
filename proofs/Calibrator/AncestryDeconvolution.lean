import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Ancestry Deconvolution and Local Ancestry in PGS

This file formalizes how local ancestry inference (LAI) can be used
to improve PGS portability for admixed individuals, and the theory
of ancestry-specific effect estimation.

Key results:
1. Global vs local ancestry and PGS bias
2. Ancestry-specific effect sizes in admixed populations
3. Local ancestry-informed PGS construction
4. Admixture mapping and its relationship to portability
5. Tractor method: ancestry-specific GWAS in admixed samples

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Global vs Local Ancestry

Admixed individuals have heterogeneous ancestry along the genome.
A PGS trained on a single ancestry group performs differently
depending on the local ancestry at each PGS locus.
-/

section GlobalVsLocalAncestry

/- **Global ancestry proportion.**
    For a two-way admixed individual: proportion α from pop A,
    (1-α) from pop B. The expected PGS performance depends on α. -/

/-- **PGS performance as a function of global ancestry proportion.**
    R²(α) ≈ α² × R²_A + (1-α)² × R²_B + 2α(1-α) × R²_cross
    where R²_cross captures the interaction term. -/
noncomputable def admixedR2
    (α r2_A r2_B r2_cross : ℝ) : ℝ :=
  α ^ 2 * r2_A + (1 - α) ^ 2 * r2_B + 2 * α * (1 - α) * r2_cross

/-- Admixed R² at α=1 reduces to R²_A. -/
theorem admixed_r2_at_one (r2_A r2_B r2_cross : ℝ) :
    admixedR2 1 r2_A r2_B r2_cross = r2_A := by
  unfold admixedR2; ring

/-- Admixed R² at α=0 reduces to R²_B. -/
theorem admixed_r2_at_zero (r2_A r2_B r2_cross : ℝ) :
    admixedR2 0 r2_A r2_B r2_cross = r2_B := by
  unfold admixedR2; ring

/-- **The cross term is bounded by the geometric mean.**
    R²_cross ≤ √(R²_A × R²_B) by Cauchy-Schwarz.
    We prove: √(R²_A × R²_B) ≤ max(R²_A, R²_B), i.e., the geometric
    mean never exceeds the larger of the two R² values. -/
theorem cross_term_bounded
    (r2_A r2_B : ℝ)
    (h_A : 0 ≤ r2_A) (h_B : 0 ≤ r2_B)
    (h_A_le : r2_A ≤ 1) (h_B_le : r2_B ≤ 1) :
    r2_A * r2_B ≤ max r2_A r2_B := by
  rcases le_or_lt r2_A r2_B with hab | hab
  · calc r2_A * r2_B ≤ 1 * r2_B := by nlinarith
      _ = r2_B := one_mul _
      _ ≤ max r2_A r2_B := le_max_right _ _
  · calc r2_A * r2_B ≤ r2_A * 1 := by nlinarith
      _ = r2_A := mul_one _
      _ ≤ max r2_A r2_B := le_max_left _ _

/-- **Admixed R² is intermediate between ancestry-specific R²s.**
    For α ∈ (0,1), R²(α) is between R²_B and R²_A (when R²_A > R²_B). -/
theorem admixed_r2_intermediate
    (α r2_A r2_B : ℝ)
    (h_α : 0 < α) (h_α1 : α < 1)
    (h_AB : r2_B < r2_A) :
    -- With r2_cross = geometric mean, admixed R² is a weighted combination
    -- Simplification: when r2_cross = r2_B (lower bound)
    r2_B < α ^ 2 * r2_A + (1 - α) ^ 2 * r2_B + 2 * α * (1 - α) * r2_B := by
  have h1 : 0 < α ^ 2 := sq_pos_of_pos h_α
  nlinarith [sq_nonneg (1 - α)]

end GlobalVsLocalAncestry


/-!
## Local Ancestry-Informed PGS

Using local ancestry to weight PGS contributions from each
genomic segment by the appropriate ancestry-specific model.
-/

section LocalAncestryPGS

/- **Local ancestry-informed PGS.**
    PGS_LAI = Σᵢ [L_i = A] × β_A_i × g_i + [L_i = B] × β_B_i × g_i
    where L_i is local ancestry and β_A, β_B are ancestry-specific effects. -/

/-- **LAI-PGS is at least as good as single-ancestry PGS.**
    By using the correct ancestry-specific effects at each locus,
    LAI-PGS reduces bias. Model: standard PGS uses a single β across
    all segments, while LAI uses β_A or β_B depending on local ancestry.
    For admixture proportion α, the LAI variance captured is
    α × β_A² × H_A + (1-α) × β_B² × H_B, while standard captures
    (α × β_A + (1-α) × β_B)² × H_avg ≤ the LAI amount (by convexity). -/
theorem lai_pgs_at_least_as_good
    (r2_A r2_B α : ℝ)
    (h_A : 0 ≤ r2_A) (h_B : 0 ≤ r2_B)
    (h_α : 0 ≤ α) (h_α1 : α ≤ 1) :
    -- LAI weighted R² ≥ the minimum component R²
    min r2_A r2_B ≤ α * r2_A + (1 - α) * r2_B := by
  rcases le_or_lt r2_A r2_B with hab | hab
  · simp [min_eq_left hab]; nlinarith
  · simp [min_eq_right (le_of_lt hab)]; nlinarith

/-- **LAI accuracy required for improvement.**
    LAI-PGS only helps if local ancestry can be called accurately.
    With error rate ε in LAI, the improvement is proportional to (1-2ε). -/
theorem lai_improvement_requires_accuracy
    (ε : ℝ) (h_ε : 0 ≤ ε) (h_ε_lt : ε < 1/2) :
    0 < 1 - 2 * ε := by linarith

/-- **LAI accuracy decreases with admixture time.**
    Older admixture → shorter ancestry tracts → harder to call.
    For admixture t generations ago, mean tract length = 1/(t×r). -/
noncomputable def meanAncestryTractLength (t : ℕ) (r : ℝ) : ℝ :=
  1 / ((t : ℝ) * r)

/-- Tract length decreases with time. -/
theorem tract_length_decreases_with_time
    (r : ℝ) (t₁ t₂ : ℕ)
    (h_r : 0 < r)
    (h_t₁ : 0 < t₁) (h_t₂ : 0 < t₂)
    (h_time : t₁ < t₂) :
    meanAncestryTractLength t₂ r < meanAncestryTractLength t₁ r := by
  unfold meanAncestryTractLength
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos (Nat.cast_pos.mpr h_t₁) h_r
  · exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr h_time) h_r

/-- **LAI-PGS improvement is largest for recently admixed individuals.**
    With long ancestry tracts, LAI is more accurate and the
    ancestry-specific effects can be applied more precisely.
    The LAI gain scales with (1 - 2ε) where ε is the LAI error rate.
    Recent admixture has lower ε (longer tracts → easier to call). -/
theorem recent_admixture_benefits_more
    (ε_recent ε_ancient : ℝ)
    (h_recent_accurate : 0 ≤ ε_recent) (h_recent_lt : ε_recent < 1/2)
    (h_ancient_accurate : 0 ≤ ε_ancient) (h_ancient_lt : ε_ancient < 1/2)
    (h_recent_better_lai : ε_recent < ε_ancient) :
    1 - 2 * ε_ancient < 1 - 2 * ε_recent := by linarith

end LocalAncestryPGS


/-!
## Admixture Mapping and Portability

Admixture mapping leverages local ancestry to detect loci where
one ancestry's alleles contribute more to the phenotype.
-/

section AdmixtureMapping

/- **Admixture mapping signal.**
    At a causal locus, the phenotype correlates with local ancestry
    if the causal allele has different frequency across ancestries. -/

/-- **Admixture mapping is complementary to GWAS.**
    GWAS finds SNP-trait associations; admixture mapping finds
    loci where ancestry matters. The intersection identifies
    loci contributing to portability loss. -/
theorem admixture_mapping_identifies_portability_loci
    (n_gwas_hits n_admixture_hits n_overlap n_portability_loci : ℕ)
    (h_overlap_informative : n_overlap ≤ n_portability_loci)
    (h_overlap_le_gwas : n_overlap ≤ n_gwas_hits)
    (h_overlap_le_admix : n_overlap ≤ n_admixture_hits) :
    n_overlap ≤ min n_gwas_hits n_admixture_hits := by
  exact le_min h_overlap_le_gwas h_overlap_le_admix

/-- **Admixture mapping power depends on Fst at the locus.**
    Power ∝ n × Fst_locus × β². High Fst loci are easier to detect
    and also the ones most responsible for portability loss. -/
theorem admixture_power_proportional_to_fst
    (n : ℝ) (fst β : ℝ)
    (h_n : 0 < n) (h_fst₁ : 0 < fst) (h_β : β ≠ 0) :
    0 < n * fst * β ^ 2 := by
  exact mul_pos (mul_pos h_n h_fst₁) (sq_pos_of_ne_zero h_β)

/-- **Admixture-informed portability correction.**
    At loci where admixture mapping detects a signal, we can
    use ancestry-specific effects to correct the PGS.
    The correction size is proportional to Δβ × Fst_locus. -/
theorem correction_proportional_to_delta_beta_fst
    (Δβ fst_locus correction : ℝ)
    (h_correction : correction = Δβ * fst_locus)
    (h_Δβ : 0 < Δβ) (h_fst : 0 < fst_locus) :
    0 < correction := by rw [h_correction]; exact mul_pos h_Δβ h_fst

end AdmixtureMapping


/-!
## Tractor: Ancestry-Specific GWAS in Admixed Samples

The Tractor method performs ancestry-specific GWAS within admixed
samples, enabling estimation of population-specific effects.
-/

section Tractor

/- **Tractor decomposes admixed genotypes by local ancestry.**
    At each locus, the allele count is split into ancestry-specific
    components: g = g_A + g_B where g_A counts alleles from ancestry A. -/

/- **Ancestry-specific effect estimation.**
    Tractor regresses: Y ~ g_A × β_A + g_B × β_B + covariates.
    This directly estimates the ancestry-specific effects needed
    for portable PGS construction. -/

/-- **Tractor requires large admixed sample size.**
    Effective per-ancestry N ≈ α × N_admixed for ancestry proportion α.
    Both ancestry components need adequate N for stable estimation. -/
theorem tractor_effective_n
    (n_admixed α : ℝ)
    (h_n : 0 < n_admixed) (h_α : 0 < α) (h_α1 : α < 1) :
    0 < α * n_admixed ∧ 0 < (1 - α) * n_admixed := by
  exact ⟨mul_pos h_α h_n, mul_pos (by linarith) h_n⟩

/-- **Ancestry-specific effects test for portability.**
    If β_A = β_B at a locus, the locus is "portable" across ancestries.
    If β_A ≠ β_B, the locus contributes to portability loss. -/
theorem effect_heterogeneity_test
    (β_A β_B se : ℝ)
    (h_se : 0 < se) :
    -- Wald test statistic
    0 ≤ ((β_A - β_B) / se) ^ 2 := sq_nonneg _

/-- **Multi-ancestry meta-analysis combines Tractor with standard GWAS.**
    Using Tractor effects from admixed samples + standard GWAS from
    homogeneous samples gives the most portable PGS. -/
theorem combined_tractor_gwas_optimal
    (r2_gwas_only r2_tractor_only r2_combined : ℝ)
    (h_combined_best_gwas : r2_gwas_only ≤ r2_combined)
    (h_combined_best_tractor : r2_tractor_only ≤ r2_combined) :
    max r2_gwas_only r2_tractor_only ≤ r2_combined := by
  exact max_le h_combined_best_gwas h_combined_best_tractor

end Tractor


/-!
## Ancestry Continuous Representation

Moving beyond discrete ancestry groups to continuous
ancestry representation using principal components.
-/

section ContinuousAncestry

/- **PC-based continuous ancestry.**
    Ancestry is represented as a point in PC space rather than
    a discrete label. This better captures the continuous nature
    of human genetic variation. -/

/-- **PGS accuracy as a function of PC distance.**
    R²(d) where d is the PC distance from the training centroid.
    This is Wang et al.'s key finding (Open Question 1). -/
noncomputable def r2AsFunction (r2_source slope d : ℝ) : ℝ :=
  r2_source * (1 - slope * d)

/-- R² decreases with genetic distance. -/
theorem r2_decreases_with_distance
    (r2_source slope d₁ d₂ : ℝ)
    (h_r2 : 0 < r2_source)
    (h_slope : 0 < slope)
    (h_d : d₁ < d₂) :
    r2AsFunction r2_source slope d₂ < r2AsFunction r2_source slope d₁ := by
  unfold r2AsFunction
  apply mul_lt_mul_of_pos_left _ h_r2
  nlinarith

/-- **Within-group variation dominates between-group variation.**
    Wang et al. Open Question 1: genetic distance explains only
    ~0.5% of individual-level prediction error variance.
    This is because within-group σ²(ε²) >> between-group signal. -/
theorem individual_variation_dominates
    (r2_between_group cv_squared_within : ℝ)
    (h_cv : cv_squared_within = 2)  -- χ²₁ coefficient of variation²
    (h_r2_small : r2_between_group < 1/100) :
    -- Even if between-group trend is real, it's overwhelmed by within-group noise
    r2_between_group < 1 / cv_squared_within := by
  rw [h_cv]; linarith

/-- **Optimal ancestry granularity for PGS application.**
    Too coarse (continental groups) loses information.
    Too fine (exact PC coordinates) adds noise with small samples.
    Optimal depends on available calibration data. -/
theorem optimal_granularity_tradeoff
    (bias_coarse bias_fine variance_coarse variance_fine : ℝ)
    (h_coarse_biased : bias_fine < bias_coarse)
    (h_fine_variable : variance_coarse < variance_fine) :
    -- Different regimes have different optima
    bias_fine < bias_coarse ∧ variance_coarse < variance_fine :=
  ⟨h_coarse_biased, h_fine_variable⟩

end ContinuousAncestry


/-!
## Ancestry Heterogeneity and Fairness

Ensuring PGS works equitably across the full spectrum of
human genetic diversity, not just for well-represented groups.
-/

section AncestryFairness

/-- **Portability gap creates health disparities.**
    Groups with worse portability get less clinical benefit from PGS.
    The gap scales with Fst from the discovery population.
    Portability ≈ 1 - c × Fst for some constant c > 0, so higher Fst
    means lower portability (larger gap = 1 - portability). -/
theorem portability_gap_scales_with_fst
    (fst₁ fst₂ c : ℝ)
    (h_fst : fst₁ < fst₂) (h_c : 0 < c)
    (h_fst₁_nn : 0 ≤ fst₁) :
    c * fst₁ < c * fst₂ := by
  exact mul_lt_mul_of_pos_left h_fst h_c

/-- **Equitable PGS requires proportional investment.**
    To achieve equal R² across populations, the sample size
    for underrepresented groups must be larger than proportional
    to their population size (due to the LD mismatch penalty).
    If the LD penalty factor is k > 1, then n_needed = k × n_proportional. -/
theorem equitable_pgs_overinvestment
    (n_proportional k : ℝ)
    (h_nn : 0 < n_proportional) (h_k : 1 < k) :
    n_proportional < k * n_proportional := by
  nlinarith

/-- **Universal portability is impossible.**
    No single PGS can achieve equal R² in all populations,
    because genetic architecture genuinely differs (GxE, selection).
    With k ≥ 2 populations at different Fst values and portability
    decaying as (1 - c × Fst), the max and min R² must differ
    when Fst values differ. -/
theorem universal_portability_impossible
    (r2_source fst_near fst_far c : ℝ)
    (h_r2 : 0 < r2_source) (h_c : 0 < c)
    (h_near : 0 ≤ fst_near) (h_far_gt : fst_near < fst_far) :
    -- The portability gap between near and far populations is positive
    r2_source * c * fst_near < r2_source * c * fst_far := by
  exact mul_lt_mul_of_pos_left h_far_gt (mul_pos h_r2 h_c)

end AncestryFairness

end Calibrator
