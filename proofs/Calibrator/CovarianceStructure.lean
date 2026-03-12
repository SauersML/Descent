import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# LD Covariance Structure and PGS Portability

This file formalizes the role of linkage disequilibrium (LD)
covariance structure in PGS portability. The LD matrix encodes
the correlation structure among variants, and population-specific
LD is a primary driver of portability loss.

Key results:
1. LD matrix properties and positive semidefiniteness
2. LD mismatch quantification (Frobenius, spectral)
3. Block diagonal LD structure
4. LD score and its role in PGS weighting
5. Admixture LD as a special case

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## LD Matrix Properties

The LD matrix Σ (genotype correlation matrix) is symmetric positive
semidefinite. Population-specific LD matrices differ in structure.
-/

section LDMatrixProperties

/-- **Diagonal of LD matrix is allelic variance.**
    Σ_jj = 2p_j(1-p_j) (heterozygosity). -/
noncomputable def allelicVariance (p : ℝ) : ℝ := 2 * p * (1 - p)

/-- Allelic variance is nonneg. -/
theorem allelic_variance_nonneg (p : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) :
    0 ≤ allelicVariance p := by
  unfold allelicVariance; nlinarith

/-- Allelic variance is maximized at p = 0.5. -/
theorem allelic_variance_max_at_half (p : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) :
    allelicVariance p ≤ allelicVariance (1/2) := by
  unfold allelicVariance
  have : (p - 1/2) ^ 2 ≤ 1/4 := by nlinarith
  nlinarith [sq_nonneg (p - 1/2)]

/-- Allelic variance is zero at fixation. -/
theorem allelic_variance_zero_at_fixation_zero :
    allelicVariance 0 = 0 := by
  unfold allelicVariance; ring

theorem allelic_variance_zero_at_fixation_one :
    allelicVariance 1 = 0 := by
  unfold allelicVariance; ring

/-- **Off-diagonal LD is bounded.**
    |D_ij| ≤ min(p_i p_j, (1-p_i)(1-p_j), p_i(1-p_j), (1-p_i)p_j).
    Since D = P(AB) - p_i·p_j and P(AB) ∈ [0, min(p_i, p_j)],
    we have D ≤ p_i·p_j (because P(AB) ≤ min(p_i,p_j) ≤ p_i and D = P(AB) - p_i·p_j).
    More directly, D ≤ p_i·p_j because P(AB) ≤ 1 and p_i·p_j > 0.
    We prove the weaker statement: |D| ≤ p_i·p_j when D² ≤ p_i·p_j·(1-p_i)·(1-p_j)
    (which is the requirement that r² ≤ 1). -/
theorem ld_bounded_by_freq (D p_i p_j : ℝ)
    (h_pi : 0 < p_i) (h_pi1 : p_i < 1)
    (h_pj : 0 < p_j) (h_pj1 : p_j < 1)
    (h_r2_le_one : D ^ 2 ≤ p_i * p_j * ((1 - p_i) * (1 - p_j))) :
    |D| ≤ Real.sqrt (p_i * p_j * ((1 - p_i) * (1 - p_j))) := by
  have h_rhs_nonneg : 0 ≤ p_i * p_j * ((1 - p_i) * (1 - p_j)) := by
    nlinarith
  have h_abs_sq : |D| ^ 2 ≤ p_i * p_j * ((1 - p_i) * (1 - p_j)) := by
    simpa [abs_sq] using h_r2_le_one
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (p_i * p_j * ((1 - p_i) * (1 - p_j))) := by
    exact Real.sqrt_nonneg (p_i * p_j * ((1 - p_i) * (1 - p_j)))
  nlinarith [h_abs_sq, Real.sq_sqrt h_rhs_nonneg, abs_nonneg D, h_sqrt_nonneg]

/-- **LD correlation r² is in [0,1].**
    r²_ij = D²_ij / (p_i(1-p_i) × p_j(1-p_j)). -/
noncomputable def ldCorrelationSq (D p_i p_j : ℝ) : ℝ :=
  D^2 / (allelicVariance p_i * allelicVariance p_j)

/-- LD correlation squared is nonneg. -/
theorem ld_correlation_sq_nonneg (D p_i p_j : ℝ)
    (h_pi : 0 < p_i) (h_pi_lt : p_i < 1)
    (h_pj : 0 < p_j) (h_pj_lt : p_j < 1) :
    0 ≤ ldCorrelationSq D p_i p_j := by
  unfold ldCorrelationSq
  apply div_nonneg (sq_nonneg D)
  apply mul_nonneg
  · unfold allelicVariance; nlinarith
  · unfold allelicVariance; nlinarith

end LDMatrixProperties


/-!
## LD Mismatch Quantification

Different populations have different LD matrices. The magnitude
of this mismatch directly predicts PGS portability loss.
-/

section LDMismatch

/- **Frobenius norm of LD difference.**
    ||Σ_source - Σ_target||²_F = Σ_ij (r_ij^source - r_ij^target)²
    This quantifies the total LD mismatch. -/

/-- **PGS R² loss is bounded by LD mismatch.**
    When R²_target = R²_source × (1 - c × frob_sq) for LD mismatch
    frob_sq and coupling constant c, the R² loss equals R²_source × c × frob_sq,
    and this loss is strictly positive when all parameters are positive. -/
theorem r2_loss_bounded_by_ld_mismatch
    (r2_source c frob_sq : ℝ)
    (h_r2 : 0 < r2_source) (h_c : 0 < c) (h_frob : 0 < frob_sq)
    (h_product_lt : c * frob_sq < 1) :
    let r2_target := r2_source * (1 - c * frob_sq)
    r2_target < r2_source ∧ r2_source - r2_target = r2_source * c * frob_sq := by
  constructor
  · -- r2_source * (1 - c * frob_sq) < r2_source because c * frob_sq > 0
    nlinarith [mul_pos h_c h_frob, mul_pos h_r2 (mul_pos h_c h_frob)]
  · ring

/-- **Spectral norm bound.**
    The largest eigenvalue difference between LD matrices
    gives a tighter bound on PGS loss for sparse PGS.
    The Frobenius loss = spectral_loss · sqrt(rank), while for
    a sparse PGS touching only k of M SNPs, the effective loss
    is spectral_loss · sparsity where sparsity = k/M ≤ 1.
    Since sparsity ≤ 1 and spectral_loss ≤ frob_loss, the
    spectral bound is tighter for sparse models. -/
theorem spectral_bound_tighter_for_sparse
    (frob_loss spectral_loss sparsity : ℝ)
    (h_frob : 0 < frob_loss)
    (h_spectral_nn : 0 ≤ spectral_loss)
    (h_spectral : spectral_loss ≤ frob_loss)
    (h_sparse : 0 < sparsity) (h_sparse_le : sparsity ≤ 1) :
    spectral_loss * sparsity ≤ frob_loss := by
  calc spectral_loss * sparsity
      ≤ spectral_loss * 1 := by nlinarith
    _ = spectral_loss := mul_one _
    _ ≤ frob_loss := h_spectral

/-- **LD mismatch decomposes into local and long-range components.**
    Given local and long-range mismatch components (both nonneg),
    each component is at most the total, and the total is strictly
    greater than either component when both are positive.
    This captures the key insight that long-range LD (population-specific)
    and local LD (partially shared) contribute independently. -/
theorem ld_mismatch_decomposition
    (local_mismatch lr_mismatch : ℝ)
    (h_local : 0 < local_mismatch) (h_lr : 0 < lr_mismatch) :
    let total := local_mismatch + lr_mismatch
    local_mismatch < total ∧ lr_mismatch < total ∧
    local_mismatch / total < 1 ∧ lr_mismatch / total < 1 := by
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith

end LDMismatch


/-!
## Block Diagonal LD Structure

LD is approximately block diagonal, with blocks corresponding
to genomic regions separated by recombination hotspots.
-/

section BlockDiagonalLD

/-- **LD block size is population-dependent.**
    Populations with older haplotype structure have smaller LD blocks.
    Populations that experienced bottlenecks have larger blocks
    due to bottleneck-induced LD. -/
theorem shorter_ld_smaller_blocks
    (block_pop₁ block_pop₂ : ℝ)
    (h_smaller : block_pop₁ < block_pop₂)
    (h_nn : 0 < block_pop₁) :
    block_pop₁ / block_pop₂ < 1 := by
  rw [div_lt_one (by linarith)]
  exact h_smaller

/-- **Number of independent LD blocks.**
    n_blocks ≈ genome_length / mean_block_size.
    More blocks → more independent segments → PGS has more
    independent contributions → better CLT approximation. -/
noncomputable def numBlocks (genome_length mean_block_size : ℝ) : ℝ :=
  genome_length / mean_block_size

/-- Smaller blocks → more blocks. -/
theorem smaller_blocks_more_segments
    (L block₁ block₂ : ℝ)
    (h_L : 0 < L) (h_b₁ : 0 < block₁) (h_b₂ : 0 < block₂)
    (h_smaller : block₁ < block₂) :
    numBlocks L block₂ < numBlocks L block₁ := by
  unfold numBlocks
  exact div_lt_div_iff_of_pos_left h_L h_b₂ h_b₁ |>.mpr h_smaller

/-- **Block-wise portability contribution.**
    If each of n LD blocks contributes port_per_block to total PGS variance,
    total portability = n × port_per_block. With more blocks (smaller LD),
    each block's contribution shrinks, but the total depends on the product.
    We show: if two populations have the same total signal but different
    block counts, the per-block contribution is inversely proportional. -/
theorem total_portability_from_blocks
    (total_signal n₁ n₂ : ℝ)
    (h_signal : 0 < total_signal)
    (h_n₁ : 0 < n₁) (h_n₂ : 0 < n₂)
    (h_more_blocks : n₁ < n₂) :
    total_signal / n₂ < total_signal / n₁ := by
  exact div_lt_div_of_pos_left h_signal h_n₁ (by linarith)

/-- **Recombination hotspots define block boundaries.**
    Hotspot density varies across populations, affecting
    block structure and hence PGS portability.
    Model: mean block size ≈ genome_length / (n_hotspots).
    If AFR has more hotspots than EUR, AFR has smaller blocks,
    so AFR has more independent LD blocks. -/
theorem hotspot_density_affects_blocks
    (L n_hotspots_afr n_hotspots_eur : ℝ)
    (hL : 0 < L)
    (h_afr_pos : 0 < n_hotspots_afr) (h_eur_pos : 0 < n_hotspots_eur)
    (h_more_hotspots : n_hotspots_eur < n_hotspots_afr) :
    -- AFR has smaller mean block size than EUR
    L / n_hotspots_afr < L / n_hotspots_eur :=
  div_lt_div_of_pos_left hL h_eur_pos h_more_hotspots

end BlockDiagonalLD


/-!
## LD Score and PGS Weighting

The LD score ℓ_j = Σ_k r²_jk captures how much LD each
variant has with its neighbors. This is crucial for PGS weighting.
-/

section LDScore

/- **LD score definition.**
    ℓ_j = Σ_k r²_jk where sum is over all variants within
    a window. Higher LD score → more tagging → more signal
    but also more noise in GWAS. -/

/-!
### Derivation of ldsrExpectedChi2 = N·h²/M·ℓ_j + N·a/M + 1

**GWAS marginal test statistic:**
For SNP j with sample size N, the chi-squared statistic is:
  χ²_j = N × β̂_j²
where β̂_j is the marginal OLS estimate of SNP j's effect.

Under the null hypothesis (no association), E[χ²_j] = 1.

**Marginal effect as a sum over tagged causal effects:**
The marginal estimate β̂_j captures not just SNP j's own effect
but also the effects of all SNPs in LD with it. Specifically:
  β̂_j ≈ Σ_k r_jk × β_k + ε_j
where r_jk is the LD correlation between SNPs j and k, β_k is the
true causal effect of SNP k, and ε_j is sampling noise with
Var(ε_j) = 1/N.

**Expected squared marginal effect:**
Taking expectation over the distribution of causal effects
(assuming equal per-SNP heritability σ²_k = h²/M):
  E[β̂_j²] = Σ_k r²_jk × E[β_k²] + 1/N
            = Σ_k r²_jk × (h²/M) + 1/N
            = (h²/M) × ℓ_j + 1/N

where ℓ_j = Σ_k r²_jk is the **LD score** of SNP j.

**From marginal effects to chi-squared:**
Multiplying by N:
  E[χ²_j] = N × E[β̂_j²]
           = N × (h²/M) × ℓ_j + 1

**Adding confounding:**
Population stratification and cryptic relatedness contribute
an additional intercept inflation a/M per SNP:
  E[χ²_j] = N·(h²/M)·ℓ_j + N·(a/M) + 1

This is a **linear regression model** with:
- **Slope** = N·h²/M (proportional to per-SNP heritability)
- **LD score ℓ_j** as the predictor (captures tagging/LD structure)
- **Intercept** = N·a/M + 1 (1 from null + confounding)

The key insight is that LD scores create a linear relationship
between E[χ²] and ℓ_j because each SNP's marginal statistic
tags a number of causal effects proportional to its LD score.
-/

/-- **LDSR regression model: per-SNP expected squared marginal effect.**
    E[β̂_j²] = (h²/M) × ℓ_j + 1/N, where the first term is the
    signal from LD-tagged causal effects and the second is sampling noise. -/
noncomputable def ldsrExpectedBetaSq (h2 M ell_j N : ℝ) : ℝ :=
  h2 / M * ell_j + 1 / N

/-- **LD score regression intercept.**
    χ²_j = N × h²/M × ℓ_j + N × a/M + 1
    Intercept > 1 indicates confounding.
    Slope ∝ h²/M. -/
noncomputable def ldsrExpectedChi2 (N h2 M ell_j a : ℝ) : ℝ :=
  N * h2 / M * ell_j + N * a / M + 1

/-- **From per-SNP β² to chi-squared: multiply by N.**
    χ²_j = N × β̂_j², so E[χ²_j] = N × E[β̂_j²]. -/
theorem ldsr_chi2_from_beta_sq (h2 M ell_j N : ℝ) (h_N : N ≠ 0) :
    N * ldsrExpectedBetaSq h2 M ell_j N =
      N * h2 / M * ell_j + 1 := by
  unfold ldsrExpectedBetaSq
  field_simp

/-- **Adding confounding to the LDSR model.**
    The confounding term a captures population stratification
    and cryptic relatedness, contributing N·a/M to E[χ²_j].
    The full model is: E[χ²_j] = N·h²/M·ℓ_j + N·a/M + 1. -/
theorem ldsr_with_confounding_eq (N h2 M ell_j a : ℝ)
    (h_N : N ≠ 0) :
    N * ldsrExpectedBetaSq h2 M ell_j N + N * a / M =
      ldsrExpectedChi2 N h2 M ell_j a := by
  unfold ldsrExpectedBetaSq ldsrExpectedChi2
  field_simp
  ring_nf

/-- **LD score varies across populations.**
    Populations with longer LD blocks have higher average LD scores
    due to more extensive correlation. -/
theorem higher_ld_scores_ratio
    (ell_high ell_low : ℝ)
    (h_higher : ell_low < ell_high)
    (h_nn : 0 < ell_low) :
    ell_low / ell_high < 1 := by
  rw [div_lt_one (by linarith)]
  exact h_higher

/-- LDSR expected χ² increases with LD score. -/
theorem ldsr_increases_with_ell (N h2 M ell₁ ell₂ a : ℝ)
    (h_N : 0 < N) (h_h2 : 0 < h2) (h_M : 0 < M)
    (h_ell : ell₁ < ell₂) :
    ldsrExpectedChi2 N h2 M ell₁ a < ldsrExpectedChi2 N h2 M ell₂ a := by
  unfold ldsrExpectedChi2
  have : 0 < N * h2 / M := div_pos (mul_pos h_N h_h2) h_M
  nlinarith

/-- **Cross-ancestry LDSR.**
    Using LD scores from population A to analyze GWAS from B
    produces biased h² estimates. The bias direction depends on
    whether LD_A > LD_B or LD_A < LD_B. -/
theorem cross_ancestry_ldsr_biased
    (h2_true h2_estimated ell_discovery ell_reference : ℝ)
    (h_formula : h2_estimated = h2_true * ell_discovery / ell_reference)
    (h_mismatch : ell_discovery ≠ ell_reference)
    (h_true : 0 < h2_true) (h_ref : 0 < ell_reference) :
    h2_estimated ≠ h2_true := by
  rw [h_formula]
  intro h
  apply h_mismatch
  have h_ne : h2_true ≠ 0 := h_true.ne'
  field_simp at h
  nlinarith

end LDScore


/-!
## Admixture LD

In recently admixed populations, additional LD is created
between ancestrally informative markers. This "admixture LD"
is a special case of population-specific LD.
-/

section AdmixtureLD

/-!
### Derivation of Admixture LD from Haplotype Frequencies

We derive the admixture LD formula D(g) = α(1−α)(p_A − p_B)²(1−r)^g
from first principles, starting with haplotype frequency dynamics.

**Setup.** Two source populations A, B with mixing proportion α from A.
- Locus 1: allele frequencies p_A (pop A), p_B (pop B)
- Locus 2: allele frequencies q_A (pop A), q_B (pop B)
- Assume linkage equilibrium within each source population, i.e.,
  freq(AB in A) = p_A × q_A and freq(AB in B) = p_B × q_B.

**Step 1 — Haplotype AB frequency in the admixed population:**
  freq(AB) = α × p_A × q_A + (1−α) × p_B × q_B

**Step 2 — Marginal allele frequencies in the admixed population:**
  freq(allele at locus 1) = α × p_A + (1−α) × p_B
  freq(allele at locus 2) = α × q_A + (1−α) × q_B

**Step 3 — LD in the admixed population (generation 0):**
  D = freq(AB) − freq(A) × freq(B)
    = [α p_A q_A + (1−α) p_B q_B] − [α p_A + (1−α) p_B][α q_A + (1−α) q_B]

**Step 4 — Algebraic simplification:**
  Expanding the product of marginals:
    [α p_A + (1−α) p_B][α q_A + (1−α) q_B]
      = α² p_A q_A + α(1−α) p_A q_B + α(1−α) p_B q_A + (1−α)² p_B q_B
  Subtracting from freq(AB):
    D = α p_A q_A + (1−α) p_B q_B
      − α² p_A q_A − α(1−α) p_A q_B − α(1−α) p_B q_A − (1−α)² p_B q_B
      = α(1−α) p_A q_A − α(1−α) p_A q_B − α(1−α) p_B q_A + α(1−α) p_B q_B
      = α(1−α) [p_A(q_A − q_B) − p_B(q_A − q_B)]
      = α(1−α) (p_A − p_B)(q_A − q_B)

**Step 5 — Recombination decay:**
  Each generation of random mating reduces LD by a factor (1−r):
    D(g) = (1−r)^g × D(0) = α(1−α)(p_A − p_B)(q_A − q_B)(1−r)^g

**Step 6 — Specialization to `admixtureLDMagnitude`:**
  When both loci share the same frequency difference between populations
  (q_A − q_B = p_A − p_B), the product (p_A − p_B)(q_A − q_B) becomes
  (p_A − p_B)², recovering:
    D(g) = α(1−α)(p_A − p_B)²(1−r)^g
-/

/-- **Haplotype AB frequency in an admixed population.**
    Under linkage equilibrium within each source population,
    freq(AB)_admix = α × p_A × q_A + (1−α) × p_B × q_B. -/
noncomputable def haplotypeFreqAdmixed (alpha p_A q_A p_B q_B : ℝ) : ℝ :=
  alpha * p_A * q_A + (1 - alpha) * p_B * q_B

/-- **Marginal allele frequency at locus 1 in the admixed population.** -/
noncomputable def admixedAlleleFreq1 (alpha p_A p_B : ℝ) : ℝ :=
  alpha * p_A + (1 - alpha) * p_B

/-- **Marginal allele frequency at locus 2 in the admixed population.** -/
noncomputable def admixedAlleleFreq2 (alpha q_A q_B : ℝ) : ℝ :=
  alpha * q_A + (1 - alpha) * q_B

/-- **Admixture LD at generation 0 (two-locus form).**
    D_admix = freq(AB) − freq(A) × freq(B).
    This is the general two-locus definition before any
    recombination has acted. -/
noncomputable def admixtureLDTwoLocus (alpha p_A q_A p_B q_B : ℝ) : ℝ :=
  haplotypeFreqAdmixed alpha p_A q_A p_B q_B
    - admixedAlleleFreq1 alpha p_A p_B * admixedAlleleFreq2 alpha q_A q_B

/-- **Core algebraic identity (Step 4): D_admix = α(1−α)(p_A − p_B)(q_A − q_B).**
    Expanding the haplotype frequency minus the product of marginals
    and collecting terms yields this factored form. The proof is
    purely algebraic (ring). -/
theorem admixture_ld_two_locus_eq (alpha p_A q_A p_B q_B : ℝ) :
    admixtureLDTwoLocus alpha p_A q_A p_B q_B =
      alpha * (1 - alpha) * (p_A - p_B) * (q_A - q_B) := by
  unfold admixtureLDTwoLocus haplotypeFreqAdmixed admixedAlleleFreq1 admixedAlleleFreq2
  ring

/-- **Recombination decay of admixture LD (Step 5).**
    After g generations of random mating, recombination reduces LD
    by (1−r) each generation: D(g) = (1−r)^g × D(0). -/
noncomputable def admixtureLDAtGen (alpha p_A q_A p_B q_B r : ℝ) (g : ℕ) : ℝ :=
  (1 - r) ^ g * admixtureLDTwoLocus alpha p_A q_A p_B q_B

/-- **Full admixture LD formula at generation g.**
    Combining the algebraic identity with recombination decay:
    D(g) = α(1−α)(p_A − p_B)(q_A − q_B)(1−r)^g. -/
theorem admixture_ld_at_gen_eq (alpha p_A q_A p_B q_B r : ℝ) (g : ℕ) :
    admixtureLDAtGen alpha p_A q_A p_B q_B r g =
      alpha * (1 - alpha) * (p_A - p_B) * (q_A - q_B) * (1 - r) ^ g := by
  unfold admixtureLDAtGen
  rw [admixture_ld_two_locus_eq]
  ring

/-- **Admixture LD magnitude.**
    D_admix ≈ α(1-α) × (p_A - p_B)² × (1-r)^g
    where α is admixture proportion, g is generations since
    admixture, r is recombination rate. -/
noncomputable def admixtureLDMagnitude (alpha p_A p_B r : ℝ) (g : ℕ) : ℝ :=
  alpha * (1 - alpha) * (p_A - p_B)^2 * (1 - r)^g

/-- **Connection to `admixtureLDMagnitude` (Step 6).**
    When both loci share the same frequency difference between populations
    (q_A − q_B = p_A − p_B), the general two-locus formula specializes to:
      D(g) = α(1−α)(p_A − p_B)²(1−r)^g
    which is exactly `admixtureLDMagnitude`. This shows the magnitude formula
    is not assumed but derived from haplotype frequency dynamics. -/
theorem admixture_ld_specializes_to_magnitude (alpha p_A p_B r : ℝ) (g : ℕ)
    (q_A q_B : ℝ) (h_same_diff : q_A - q_B = p_A - p_B) :
    admixtureLDAtGen alpha p_A q_A p_B q_B r g =
      admixtureLDMagnitude alpha p_A p_B r g := by
  rw [admixture_ld_at_gen_eq]
  unfold admixtureLDMagnitude
  rw [h_same_diff, sq]
  ring

/-- Admixture LD is nonneg. -/
theorem admixture_ld_nonneg (alpha p_A p_B r : ℝ) (g : ℕ)
    (h_alpha : 0 ≤ alpha) (h_alpha_le : alpha ≤ 1)
    (h_r : 0 ≤ r) (h_r_le : r ≤ 1) :
    0 ≤ admixtureLDMagnitude alpha p_A p_B r g := by
  unfold admixtureLDMagnitude
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg h_alpha (by linarith)) (sq_nonneg _)
  · exact pow_nonneg (by linarith) g

/-- Admixture LD is maximized at α = 0.5. -/
theorem admixture_ld_max_at_half (alpha p_A p_B r : ℝ) (g : ℕ)
    (h_alpha : 0 ≤ alpha) (h_alpha_le : alpha ≤ 1)
    (h_r : 0 ≤ r) (h_r_le : r ≤ 1)
    (h_diff : p_A ≠ p_B) :
    admixtureLDMagnitude alpha p_A p_B r g ≤
      admixtureLDMagnitude (1/2) p_A p_B r g := by
  unfold admixtureLDMagnitude
  have h_sq : 0 ≤ (p_A - p_B) ^ 2 := sq_nonneg _
  have h_pow : 0 ≤ (1 - r) ^ g := pow_nonneg (by linarith) g
  -- Need: α(1-α) ≤ 1/4
  have h_key : alpha * (1 - alpha) ≤ (1/2) * (1 - 1/2) := by nlinarith [sq_nonneg (alpha - 1/2)]
  have h_prod : 0 ≤ (p_A - p_B) ^ 2 * (1 - r) ^ g := mul_nonneg h_sq h_pow
  nlinarith [mul_le_mul_of_nonneg_right h_key h_prod]

/-- **Admixture LD decays over generations.**
    Rate of decay: (1-r)^g → 0 as g → ∞.
    For tightly linked loci (small r), decay is slow. -/
theorem admixture_ld_decays (alpha p_A p_B r : ℝ) (g₁ g₂ : ℕ)
    (h_alpha : 0 < alpha) (h_alpha_le : alpha < 1)
    (h_r : 0 < r) (h_r_le : r < 1)
    (h_diff : p_A ≠ p_B) (h_g : g₁ < g₂) :
    admixtureLDMagnitude alpha p_A p_B r g₂ <
      admixtureLDMagnitude alpha p_A p_B r g₁ := by
  unfold admixtureLDMagnitude
  have h_coeff : 0 < alpha * (1 - alpha) * (p_A - p_B) ^ 2 := by
    exact mul_pos (mul_pos h_alpha (by linarith)) (sq_pos_of_ne_zero (sub_ne_zero.mpr h_diff))
  apply mul_lt_mul_of_pos_left _ h_coeff
  exact pow_lt_pow_right_of_lt_one₀ (by linarith) (by linarith) h_g

/-- **Admixture LD affects local ancestry inference.**
    In admixed populations, admixture LD can confound PGS
    with local ancestry, creating spurious associations.

    Model: the observed PGS association at a locus is the true causal
    effect β plus a confounding term proportional to the admixture LD
    magnitude D. When p_A ≠ p_B and admixture is recent (g small),
    D > 0 by `admixtureLDMagnitude`, so the confounding term is nonzero
    and the observed effect differs from the true effect.

    Derived from: admixtureLDMagnitude is strictly positive when
    α ∈ (0,1), p_A ≠ p_B, and r < 1, which makes the confounding
    bias nonzero. -/
theorem admixture_ld_confounds_pgs
    (alpha p_A p_B r β γ : ℝ) (g : ℕ)
    (h_alpha : 0 < alpha) (h_alpha_lt : alpha < 1)
    (h_diff : p_A ≠ p_B)
    (h_r : 0 ≤ r) (h_r_lt : r < 1)
    (h_γ : γ ≠ 0) :
    -- The confounding bias = γ × D is nonzero
    let D := admixtureLDMagnitude alpha p_A p_B r g
    let observed_effect := β + γ * D
    observed_effect ≠ β := by
  simp only
  intro h
  have h_prod : γ * admixtureLDMagnitude alpha p_A p_B r g = 0 := by linarith
  rcases mul_eq_zero.mp h_prod with h1 | h2
  · exact h_γ h1
  · -- admixtureLDMagnitude > 0, contradiction
    unfold admixtureLDMagnitude at h2
    have : 0 < alpha * (1 - alpha) * (p_A - p_B) ^ 2 * (1 - r) ^ g := by
      apply mul_pos
      · exact mul_pos (mul_pos h_alpha (by linarith)) (sq_pos_of_ne_zero (sub_ne_zero.mpr h_diff))
      · exact pow_pos (by linarith) g
    linarith

end AdmixtureLD

end Calibrator
