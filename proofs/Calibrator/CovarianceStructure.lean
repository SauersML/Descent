/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Calibrator.AncestrySpecificPower
import Calibrator.DemographicHistory

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat the algebra of LD covariance matrices. Sources for individual
results, where they exist, are cited at those results.
-/


/-!
## LD Matrix Properties

The LD matrix Σ (genotype correlation matrix) is symmetric positive
semidefinite. Population-specific LD matrices differ in structure.
-/

section LDMatrixProperties

/-! **Diagonal of LD matrix is genotype variance.** `Σ_jj = 2p_j(1-p_j)`.

This is `genotypeVarianceHWE` from `Calibrator.AncestrySpecificPower`. Do not define it
here: the ploidy convention lives in a single place, and its empirical status and
`Denotes` declaration belong with that definition. -/

/-! **This is the genotype variance, not the allelic variance.** `2p(1-p)` is the
genotype variance, equivalently the Hardy-Weinberg heterozygote frequency; the allelic
variance is `p(1-p)`. Reading it as allelic is what produces the `r²/4` defect:
`ldCorrelationSq` divides by the product of two of these, which is right for a
genotype-scale `D` and wrong by four for the allele-scale `D` this same file produces. -/


/-- **Recombination hotspots define block boundaries.**
    Hotspot density varies across populations, affecting
    block structure and hence PGS portability.
    Model: mean block size ≈ genome_length / (n_hotspots).
    If AFR has more hotspots than EUR, AFR has smaller blocks,
    so AFR has more independent LD blocks. -/
theorem hotspot_density_affects_blocks
    (L n_hotspots_afr n_hotspots_eur : ℝ)
    (hL : 0 < L)
    (h_eur_pos : 0 < n_hotspots_eur)
    (h_more_hotspots : n_hotspots_eur < n_hotspots_afr) :
    -- AFR has smaller mean block size than EUR
    L / n_hotspots_afr < L / n_hotspots_eur :=
  div_lt_div_of_pos_left hL h_eur_pos h_more_hotspots

end LDMatrixProperties


/-!
## LD Score and PGS Weighting

The LD score ℓ_j = Σ_k r²_jk captures how much LD each
variant has with its neighbors. This is crucial for PGS weighting.
-/

section LDScore

/-!
### Derivation of ldsrExpectedChi2 = N·h²/M·ℓ_j + N·a + 1

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
Population stratification and cryptic relatedness inflate the intercept:
  E[χ²_j] = N·(h²/M)·ℓ_j + N·a + 1

The confounding term is **not** divided by `M`. The divided form `N·(a/M)` is
falsified: see the docstring of `ldsrExpectedChi2` below, where a sixteenfold
sweep of `M` at fixed confounding leaves the excess over one flat, so the divided
form's implied `a` grows with `M` in contradiction with its own definition, and at
`N = 8·10⁵`, `M = 9·10⁵` it reports `χ² = 1.32` against a truth of `420.8`. Do not
copy the divided form out of this file.

This is a **linear regression model** with:
- **Slope** = N·h²/M (proportional to per-SNP heritability)
- **LD score ℓ_j** as the predictor (captures tagging/LD structure)
- **Intercept** = N·a + 1 (1 from null + confounding)

The key insight is that LD scores create a linear relationship
between E[χ²] and ℓ_j because each SNP's marginal statistic
tags a number of causal effects proportional to its LD score.
-/

/-- **LDSR regression model: per-SNP expected squared marginal effect.**
    E[β̂_j²] = (h²/M) × ℓ_j + 1/N, where the first term is the
    signal from LD-tagged causal effects and the second is sampling noise.

    Empirical status: UNTESTED. -/
noncomputable def ldsrExpectedBetaSq (h2 M ell_j N : ℝ) : ℝ :=
  h2 / M * ell_j + 1 / N

/-- **ldsrExpectedBetaSq where its denominator vanishes, named.** The guard `N` is zero at `N = 0`.
Lean returns `h2 / M * ell_j` there rather than the value the modelled quantity takes, and no
type error marks the point. Consumers must require `N ≠ 0`. -/
theorem ldsrExpectedBetaSq_at_n0_is_junk (h2 : ℝ) (M : ℝ) (ell_j : ℝ) :
    ldsrExpectedBetaSq h2 M ell_j 0 = h2 / M * ell_j := by
  unfold ldsrExpectedBetaSq
  norm_num

/-- **LD score regression expectation.**
    `χ²_j = (N h²/M) ℓ_j + N a + 1`, with intercept above one indicating
    confounding and slope proportional to `h²/M`.

    **The confounding term is not divided by `M`.** Simulation with
    pure stratification and no genetic effect holds the confounding fixed and
    varies `M` sixteenfold: the excess over one is flat, so the reference law's
    `a` is constant to within noise while the divided form's implied `a` grows
    with `M`, contradicting its definition as a property of the confounding
    rather than of the marker panel. At `N = 8·10⁵` and `M = 9·10⁵` the divided
    form reports `χ² = 1.32` where the truth is `420.8`, so it declares
    stratification invisible at any severity.

    Empirical status: VALIDATED in the corrected form (implied `a` constant to
    within 15 percent across a sixteenfold range of `M`).

    Power: the design separates the two candidate forms by orders of magnitude
    rather than by a margin. At `N = 8·10⁵` and `M = 9·10⁵` the corrected form
    predicts `420.8` where the divided form predicts `1.32`; the sixteenfold
    sweep of `M` moves the divided form's implied `a` by that whole factor
    while the corrected form's stays flat. -/
noncomputable def ldsrExpectedChi2 (N h2 M ell_j a : ℝ) : ℝ :=
  N * h2 / M * ell_j + N * a + 1

/-- **ldsrExpectedChi2 at its junk point, named.** With no markers the per-marker heritability is
undefined. The divisor is zero, the genetic term vanishes, and the expected chi-squared reduces
to confounding plus one -- so an LD-score regression run against an empty reference reports the
intercept as the whole signal and attributes everything to confounding. Consumers must exclude
the argument that makes the guard vanish. -/
theorem ldsrExpectedChi2_no_markers_is_junk (N h2 ell_j a : ℝ) :
    ldsrExpectedChi2 N h2 0 ell_j a = N * a + 1 := by
  unfold ldsrExpectedChi2
  simp

/-- **The intercept is one under the null.**

At zero heritability and no confounding the expected chi-squared is exactly one, whatever the
sample size, the SNP count or the LD score. That is the whole basis of reading the LD-score
intercept as a confounding diagnostic: the additive `1` is the null expectation of a
one-degree-of-freedom statistic and not a fitted offset. The relation to `ldsrExpectedBetaSq`
proved below multiplies through by `N` and carries the `+ 1` along without constraining it, so a
body with any other constant satisfies that identity and fails here. -/
theorem ldsrExpectedChi2_null (N M ell_j : ℝ) :
    ldsrExpectedChi2 N 0 M ell_j 0 = 1 := by
  unfold ldsrExpectedChi2
  ring

/-- **From per-SNP β² to chi-squared: multiply by N.**
    χ²_j = N × β̂_j², so E[χ²_j] = N × E[β̂_j²]. -/
theorem ldsr_chi2_from_beta_sq (h2 M ell_j N : ℝ) (h_N : N ≠ 0) :
    N * ldsrExpectedBetaSq h2 M ell_j N =
      N * h2 / M * ell_j + 1 := by
  unfold ldsrExpectedBetaSq
  field_simp

/-- **Adding confounding to the LDSR model.**
    The confounding term `a` captures population stratification and cryptic relatedness,
    contributing `N·a` to `E[χ²_j]` — not `N·a/M`. The full model is
    `E[χ²_j] = N·h²/M·ℓ_j + N·a + 1`, which is what the statement below proves and what
    `ldsrExpectedChi2` computes. The divided form is falsified; the evidence is in that
    definition's docstring. -/
theorem ldsr_with_confounding_eq (N h2 M ell_j a : ℝ)
    (h_N : N ≠ 0) :
    N * ldsrExpectedBetaSq h2 M ell_j N + N * a =
      ldsrExpectedChi2 N h2 M ell_j a := by
  unfold ldsrExpectedBetaSq ldsrExpectedChi2
  field_simp
  ring_nf

/-- **LD score varies across populations.**
    Populations with longer LD blocks have higher average LD scores
    due to more extensive correlation. -/
theorem scoreRatio_lt_one_of_lt
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

/-- **Scaling by a ratio that is not one changes the quantity.**

    The name says what is proved. The cross-ancestry reading — that LD scores taken from one
    population and applied to another rescale the heritability estimate by the ratio of the two
    LD scores — is supplied as `h_formula`, not derived, and the claim about bias DIRECTION in
    the older headline is not in the statement at all. Nothing below is evidence that LDSR is
    biased across ancestries; it is arithmetic on an assumed rescaling. -/
theorem mul_div_ne_self_of_ne
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
    freq(AB)_admix = α × p_A × q_A + (1−α) × p_B × q_B.

    Empirical status: UNTESTED. -/
noncomputable def haplotypeFreqAdmixed (alpha p_A q_A p_B q_B : ℝ) : ℝ :=
  alpha * p_A * q_A + (1 - alpha) * p_B * q_B

/-- **Two identical source populations admix to themselves.** When both parental populations
carry the same haplotype frequency the admixed frequency is that value at every mixing
proportion, so admixture cannot create haplotype structure that neither source had. -/
theorem haplotypeFreqAdmixed_same (alpha p q : ℝ) :
    haplotypeFreqAdmixed alpha p q p q = p * q := by
  unfold haplotypeFreqAdmixed; ring

/-! **Marginal allele frequency at either locus in the admixed population.**

This is `admixedAlleleFreq` from `Calibrator.DemographicHistory` -- one function of a
mixing weight and two parental frequencies, applied once per locus. Do not add a
per-locus copy; two copies differing only in bound-variable names is what that invites.

    Denotes: a frequency or proportion. Other definitions share this formula
    under names from a different concept family; the formula does not fix which
    is meant.

    Empirical status: UNTESTED. -/

/-- **Admixture LD at generation 0 (two-locus form).**
    D_admix = freq(AB) − freq(A) × freq(B).
    This is the general two-locus definition before any
    recombination has acted.

    Empirical status: UNTESTED. -/
noncomputable def admixtureLDTwoLocus (alpha p_A q_A p_B q_B : ℝ) : ℝ :=
  haplotypeFreqAdmixed alpha p_A q_A p_B q_B
    - admixedAlleleFreq alpha p_A p_B * admixedAlleleFreq alpha q_A q_B

/-- **Admixture LD is the haplotype frequency minus the product of the two
marginal admixed allele frequencies**, where the marginal is
`DemographicHistory.admixedAlleleFreq` at each locus rather than a restatement
local to this file. -/
theorem admixtureLDTwoLocus_eq_haplotype_sub_marginals
    (alpha p_A q_A p_B q_B : ℝ) :
    admixtureLDTwoLocus alpha p_A q_A p_B q_B =
      haplotypeFreqAdmixed alpha p_A q_A p_B q_B
        - admixedAlleleFreq alpha p_A p_B * admixedAlleleFreq alpha q_A q_B :=
  rfl

/-- **Core algebraic identity (Step 4): D_admix = α(1−α)(p_A − p_B)(q_A − q_B).**
    Expanding the haplotype frequency minus the product of marginals
    and collecting terms yields this factored form. The proof is
    purely algebraic (ring). -/
theorem admixture_ld_two_locus_eq (alpha p_A q_A p_B q_B : ℝ) :
    admixtureLDTwoLocus alpha p_A q_A p_B q_B =
      alpha * (1 - alpha) * (p_A - p_B) * (q_A - q_B) := by
  unfold admixtureLDTwoLocus haplotypeFreqAdmixed admixedAlleleFreq
  ring

/-- **Recombination decay of admixture LD (Step 5).**
    After g generations of random mating, recombination reduces LD
    by (1−r) each generation: D(g) = (1−r)^g × D(0).

    Empirical status: UNTESTED. -/
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
    admixture, r is recombination rate.

    Empirical status: UNTESTED. -/
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
    -- The observed effect carries the confounding bias γ × D
    β + γ * admixtureLDMagnitude alpha p_A p_B r g ≠ β := by
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
