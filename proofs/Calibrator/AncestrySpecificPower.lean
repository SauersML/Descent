/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Calibrator.Permeability

namespace Calibrator

open MeasureTheory

/-!
# Statistical Power and PGS Portability

This file formalizes the statistical power framework for PGS
across different populations. Power imbalances are a
fundamental driver of portability gaps.

Key results:
1. Population-specific power curves
2. Discovery bias from single-population GWAS
3. Effective sample size across populations
4. Power-portability tradeoff
5. Optimal multi-population study design

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat power curves, Fisher information or multi-population study design.
Sources for individual results, where they exist, are cited at those results.
-/


/-!
## Population-Specific Power Curves

Power to detect a variant depends on sample size, effect size,
and allele frequency — all of which differ across populations.
-/

section PopulationPowerCurves

/-!
### Derivation of Effective Sample Size from Fisher Information

In a GWAS linear regression model Y = βG + ε, where G is the genotype
dosage (0, 1, or 2 copies of the minor allele) and ε ~ N(0, σ²), the
Fisher information for the effect size β is:

  I(β) = n × Var(G) / σ²

Under Hardy-Weinberg equilibrium at a biallelic locus with minor allele
frequency p, the genotype dosage G ~ Binomial(2, p), so:

  Var(G) = 2p(1 - p)

This is the heterozygosity — the probability that a randomly chosen
allele copy differs from another. We normalize σ² = 1 (or absorb it
into the effect size), giving:

  I(β) = n × 2p(1 - p)

When the causal variant is not directly genotyped but imperfectly tagged
by a nearby SNP with LD r², the observed association signal is attenuated.
The effective Fisher information becomes:

  I_eff(β) = n × 2p(1 - p) × r²_LD

The **effective sample size** is defined as the sample size of a
hypothetical perfectly-tagged study (r² = 1, Var(G) = 1) that yields
the same Fisher information:

  n_eff = n × 2p(1 - p) × r²_LD

This is the formula implemented below.
-/

/-- **Fisher information for β in linear regression Y = βG + ε.**
    At a biallelic locus with sample size n and genotype variance v,
    the Fisher information is n × v (with σ² = 1). -/
noncomputable def fisherInformation (n : ℕ) (v : ℝ) : ℝ := n * v

/-- **Genotype variance under HWE.**
    For a biallelic locus with MAF p, the dosage G ∈ {0, 1, 2}
    follows Binomial(2, p). Its variance is 2p(1-p), and this equals the
    per-locus information content.

    This is the corpus-wide genotype variance at a biallelic locus. It was
    written out independently in `CovarianceStructure`, `StratificationConfounding`
    and `GeneticArchitectureDiscovery`; those definitions are gone and their
    references point here, so the ploidy convention is stated in one place.
    `Conventions.genotypeVarianceHWE_eq_hwe` ties it to `hweGenotypeVariance`,
    which derives the factor of two from `ploidy`.

    Empirical status: UNTESTED.

    Denotes: a variance — the variance of the dosage `G ∈ {0, 1, 2}`. It is
    *not* the allelic variance `p(1-p)`, and it is numerically but not
    conceptually the heterozygote frequency `hweHeterozygosity`; the formula
    alone does not fix which is meant, so the identity is stated as
    `hweHeterozygosity_eq_genotypeVarianceHWE` below. -/
def genotypeVarianceHWE (p : ℝ) : ℝ := 2 * p * (1 - p)

/-- **genotypeVarianceHWE pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem genotypeVarianceHWE_at_reference_point :
    genotypeVarianceHWE (1 / 2) = 1 / 2 := by
  unfold genotypeVarianceHWE
  norm_num

/-- Genotype variance is nonnegative when 0 ≤ p ≤ 1. -/
theorem genotypeVariance_nonneg (p : ℝ) (h_p : 0 ≤ p) (h_p_le : p ≤ 1) :
    0 ≤ genotypeVarianceHWE p := by
  unfold genotypeVarianceHWE
  nlinarith

/-- Genotype variance is strictly positive when 0 < p < 1. -/
theorem genotypeVariance_pos (p : ℝ) (h_p : 0 < p) (h_p_lt : p < 1) :
    0 < genotypeVarianceHWE p := by
  unfold genotypeVarianceHWE
  nlinarith

/-- Genotype variance is maximized at p = 1/2 where it equals 1/2. -/
theorem genotypeVariance_max (p : ℝ) (h_p : 0 ≤ p) (h_p_le : p ≤ 1) :
    genotypeVarianceHWE p ≤ genotypeVarianceHWE (1/2 : ℝ) := by
  unfold genotypeVarianceHWE
  nlinarith [sq_nonneg (p - 1/2)]

/-- **Effective Fisher information under imperfect tagging.**
    When the causal variant is tagged with LD r², the Fisher information
    for the causal effect is attenuated by r²:
      I_eff = I(β) × r²_LD = n × 2p(1-p) × r²_LD

    Derivation: Under imperfect tagging, the observed genotype G_tag
    satisfies Cov(G_tag, G_causal)² / (Var(G_tag) × Var(G_causal)) = r².
    The regression of Y on G_tag recovers β_tag = β × r², and the
    information about β through G_tag is I × r².

    Empirical status: UNTESTED. -/
noncomputable def effectiveFisherInformation (n : ℕ) (p r2_ld : ℝ) : ℝ :=
  fisherInformation n (genotypeVarianceHWE p) * r2_ld

/-- Effective Fisher information equals n × 2p(1-p) × r²_LD. -/
theorem effectiveFisherInfo_eq (n : ℕ) (p r2_ld : ℝ) :
    effectiveFisherInformation n p r2_ld = n * (2 * p * (1 - p)) * r2_ld := by
  unfold effectiveFisherInformation fisherInformation genotypeVarianceHWE
  ring

/-- **Bridge between conventional LD `r²` and permeability attenuation.**
If `η` is the correlation-scale response retained by a tag, conventional regression
information is multiplied by `r² = η²`.  The covariance-channel permeability is
multiplied by the same `η²`.  The cross-multiplied identity below makes the two
normalizations agree exactly without dividing by a possibly zero information channel.

This distinction is load-bearing in cross-population design: supplying an LD `r²` value
as the *linear* response `η` would square the loss twice and incorrectly predict `r⁴`
retention. -/
theorem ld_r2_matches_covariance_response_retention
    (n : ℕ) (p covariance covarianceDerivative η : ℝ) :
    effectiveFisherInformation n p (η ^ 2) *
        scalarPermeability covariance covarianceDerivative =
      fisherInformation n (genotypeVarianceHWE p) *
        scalarPermeability covariance (η * covarianceDerivative) := by
  unfold effectiveFisherInformation
  rw [scalarPermeability_derivative_scale]
  ring

/-- Information loss from imperfect tagging: effective info ≤ full info. -/
theorem information_loss_from_tagging (n : ℕ) (p r2_ld : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) (h_r2 : 0 ≤ r2_ld) (h_r2_le : r2_ld ≤ 1) :
    effectiveFisherInformation n p r2_ld ≤ fisherInformation n (genotypeVarianceHWE p) := by
  unfold effectiveFisherInformation
  have h_info_nonneg : 0 ≤ fisherInformation n (genotypeVarianceHWE p) := by
    unfold fisherInformation
    apply mul_nonneg
    · exact Nat.cast_nonneg n
    · exact genotypeVariance_nonneg p h_p h_p_le
  nlinarith

/-!
### Derivation of the Non-Centrality Parameter (NCP)

The Wald test statistic for H₀: β = 0 in Y = βG + ε is:

  W = (β̂ / SE(β̂))²

Under the null, W ~ χ²(1). Under the alternative with true effect β:

  SE(β̂)² = σ² / (n × Var(G) × r²_LD) = 1 / n_eff

so the NCP of the non-central χ² distribution is:

  λ = (β / SE)² = β² × n_eff = β² × n × 2p(1-p) × r²_LD

Power is then P(χ²₁(λ) > χ²_α) = Φ(√λ - z_α) approximately.
-/

/-- **Standard error of β̂ from Fisher information.**
    SE² = 1 / I_eff = 1 / (n × 2p(1-p) × r²_LD) = 1 / n_eff. -/
noncomputable def standardErrorSq (n : ℕ) (p r2_ld : ℝ) : ℝ :=
  1 / effectiveFisherInformation n p r2_ld

/-- **NCP from the Wald test.**
    NCP = (β / SE)² = β² / SE² = β² × I_eff = β² × n_eff.
    This is derived, not assumed: it follows from SE² = 1/I_eff. No positivity of the
    information is needed -- at `I_eff = 0` both sides are `0` under Lean's junk-value
    convention for division -- so the identity holds for every `n`, `p`, `r2_ld`. -/
theorem ncp_from_wald_test (n : ℕ) (p r2_ld β : ℝ) :
    β ^ 2 / standardErrorSq n p r2_ld =
      β ^ 2 * effectiveFisherInformation n p r2_ld := by
  unfold standardErrorSq
  rcases eq_or_ne (effectiveFisherInformation n p r2_ld) 0 with h_zero | h_ne
  · simp [h_zero]
  · field_simp

/-- **NCP equals n_eff × β², linking Fisher information to the test statistic.**
    Combines the Wald test derivation with the effective sample size formula. -/
theorem ncp_eq_neff_times_beta_sq (n : ℕ) (p r2_ld β : ℝ) :
    β ^ 2 * effectiveFisherInformation n p r2_ld =
      (n * (2 * p * (1 - p)) * r2_ld) * β ^ 2 := by
  rw [effectiveFisherInfo_eq]
  ring

/-! `effectiveSampleSize` used to sit here, with body `n * 2p(1-p) * r2_ld`. It is
deleted: that body is `effectiveFisherInformation`, character for character, and the name
was a units error rather than a second quantity. `2p(1-p) ≤ 1/2` for every allele
frequency, so the value is below `n/2` always and equals `n` never; nothing carrying a
genotype variance is a count of individuals. `ncp_eq_neff_times_beta_sq` already treated
the two as interchangeable, because they were.

Removed in two steps deliberately. The consumers were repointed and built green first,
and only then was the declaration deleted -- because a dead-code deletion in this repo
destroyed two correct definitions on a premise that looked just as solid, and the build
did not object, since Lean auto-binds an undefined name as an implicit variable rather
than reporting it missing.

`effectiveSampleSizeSE` and `effectiveSampleSizeFromSE` were DIFFERENT declarations that
merely shared this stem, and the first was independently found numerically wrong and has
since been deleted from `StatisticalGeneticsMethodology`; `effectiveSampleSizeFromSE`
remains. A bare-stem substitution here would have corrupted both. -/

/-- Effective sample size is nonneg. -/
theorem effective_information_nonneg (n : ℕ) (p r2_ld : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) (h_r2 : 0 ≤ r2_ld) :
    0 ≤ effectiveFisherInformation n p r2_ld := by
  unfold effectiveFisherInformation fisherInformation genotypeVarianceHWE
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg n
    · nlinarith
  · exact h_r2

/-- **Effective sample size is monotone in r²_LD.**
    Holding sample size and MAF fixed, higher tagging r² gives higher n_eff.
    This is the key lemma: populations with shorter LD have lower r²_LD
    to the GWAS tag SNPs, hence lower effective sample size. -/
theorem effective_information_mono_r2 (n : ℕ) (p r2_a r2_b : ℝ)
    (h_n : 0 < n) (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2_a : 0 ≤ r2_a) (h_r2_b : 0 ≤ r2_b)
    (h_r2 : r2_a < r2_b) :
    effectiveFisherInformation n p r2_a < effectiveFisherInformation n p r2_b := by
  unfold effectiveFisherInformation fisherInformation genotypeVarianceHWE
  have h_het : 0 < 2 * p * (1 - p) := by nlinarith
  have h_coeff : 0 < ↑n * (2 * p * (1 - p)) := by
    apply mul_pos
    · exact Nat.cast_pos.mpr h_n
    · exact h_het
  exact mul_lt_mul_of_pos_left h_r2 h_coeff

/-- **Effective sample size is monotone in sample count.**
    Holding MAF and r²_LD fixed, more samples give higher n_eff. -/
theorem effective_information_mono_n (n_a n_b : ℕ) (p r2_ld : ℝ)
    (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2 : 0 < r2_ld)
    (h_n : n_a < n_b) :
    effectiveFisherInformation n_a p r2_ld < effectiveFisherInformation n_b p r2_ld := by
  unfold effectiveFisherInformation fisherInformation genotypeVarianceHWE
  have h_het : 0 < 2 * p * (1 - p) := by nlinarith
  have h_cast : (↑n_a : ℝ) < ↑n_b := Nat.cast_lt.mpr h_n
  have h_suffix : 0 < 2 * p * (1 - p) * r2_ld := mul_pos h_het h_r2
  nlinarith

/-- **Populations with shorter LD have lower effective n at same sample size.**
    Derived from monotonicity lemmas: we compose monotonicity in r² and n
    to show that when source has both more samples and better tagging,
    the effective sample size gap is strict.

    Step 1: n_target with r2_target < n_target with r2_source (mono in r²)
    Step 2: n_target with r2_source < n_source with r2_source (mono in n)
    Compose by transitivity. -/
theorem source_higher_effective_information
    (n_source n_target : ℕ) (p_source p_target r2_source r2_target : ℝ)
    (h_n : n_target < n_source) (h_r2 : r2_target < r2_source)
    (h_p_source : 0 < p_source) (h_p_source_lt : p_source < 1)
    (h_p_target : 0 < p_target) (h_p_target_lt : p_target < 1)
    (h_r2_target : 0 < r2_target)
    -- Same variant, same allele frequency for simplicity
    (h_same_p : p_source = p_target) :
    effectiveFisherInformation n_target p_target r2_target <
      effectiveFisherInformation n_source p_source r2_source := by
  rw [h_same_p]
  -- Case split: n_target = 0 vs n_target > 0
  by_cases h_nt : n_target = 0
  · -- When n_target = 0, LHS is 0; RHS is positive since n_source ≥ 1
    have h_ns_pos : 0 < n_source := by omega
    unfold effectiveFisherInformation fisherInformation genotypeVarianceHWE
    rw [h_nt]; simp
    have h_het : 0 < 2 * p_target * (1 - p_target) := by nlinarith
    have h_cast : (0 : ℝ) < ↑n_source := Nat.cast_pos.mpr h_ns_pos
    have h_r2_source : 0 < r2_source := by linarith
    exact mul_pos (mul_pos h_cast h_het) h_r2_source
  · -- When n_target > 0, compose monotonicity in r² and n
    have h_nt_pos : 0 < n_target := Nat.pos_of_ne_zero h_nt
    have step1 : effectiveFisherInformation n_target p_target r2_target <
        effectiveFisherInformation n_target p_target r2_source :=
      effective_information_mono_r2 n_target p_target r2_target r2_source
        h_nt_pos h_p_target h_p_target_lt
        (le_of_lt h_r2_target) (le_of_lt (by linarith)) h_r2
    have step2 : effectiveFisherInformation n_target p_target r2_source <
        effectiveFisherInformation n_source p_target r2_source :=
      effective_information_mono_n n_target n_source p_target r2_source
        h_p_target h_p_target_lt (by linarith) h_n
    linarith

/-- **Non-centrality parameter (NCP) for association test.**
    NCP = n_eff × β² where β is the modelled effect size.
    Power is Φ(√NCP - z_α) for threshold z_α.

    Empirical status: **VALIDATED**
    (`proofs/validation/empirical/simcov/battery_bulk2.py`, `test_ncp`).
    Measured as the mean realised Wald statistic minus one, over 3000 replicate
    GWAS studies per cell, with `n_eff` read as `n · 2p(1-p)` on the residual
    variance scale:

      n      p     beta      this def   simulated            sems
      4000   0.3   0.05       4.20000   4.20814±0.07956     0.10
      8000   0.3   0.05       8.40000   8.48391±0.10873     0.77
      4000   0.1   0.08       4.60800   4.73164±0.08485     1.46

    The design varies `n`, `p` and `beta` separately, so linearity in each is
    tested rather than one combination of them.

    Power: the prediction spans 4.20000 to 8.40000. -/
noncomputable def ncp (n_eff β : ℝ) : ℝ := n_eff * β ^ 2

/-- NCP is monotone in effective sample size. -/
theorem ncp_mono_neff (n1 n2 β : ℝ) (h_n : n1 < n2) (h_β : β ≠ 0) :
    ncp n1 β < ncp n2 β := by
  unfold ncp
  have h_β_sq : 0 < β ^ 2 := by positivity
  exact mul_lt_mul_of_pos_right h_n h_β_sq

/-- **Power gap compounds across the genome.**
    When the source has higher effective n (derived from LD and sample
    size differences via the monotonicity lemmas above), the NCP is
    higher for every variant with nonzero effect. Over M variants,
    the total NCP gap scales linearly with M.

    The power gap is derived from the NCP gap via ncp_mono_neff,
    not assumed directly. -/
theorem detected_variants_gap
    (M : ℕ) (n_eff_source n_eff_target β : ℝ)
    (h_neff : n_eff_target < n_eff_source)
    (h_β : β ≠ 0)
    (h_M : 0 < M) :
    ↑M * ncp n_eff_target β < ↑M * ncp n_eff_source β := by
  have h_ncp : ncp n_eff_target β < ncp n_eff_source β :=
    ncp_mono_neff n_eff_target n_eff_source β h_neff h_β
  exact mul_lt_mul_of_pos_left h_ncp (Nat.cast_pos.mpr h_M)

end PopulationPowerCurves


/-!
## Discovery Bias

Single-population GWAS discovers variants that are common and
well-tagged in the discovery population, creating systematic bias in PGS.
-/

section DiscoveryBias

/-- **Heterozygosity function.** het(p) = 2p(1-p) is the expected fraction of
    heterozygotes at a biallelic locus in Hardy-Weinberg proportions, and hence
    the per-variant information content for association testing.

    This is the corpus-wide heterozygote frequency. It was written out
    independently as `StratificationConfounding.heterozygosity`; that definition
    is gone and its references point here.

    Empirical status: UNTESTED.

    Denotes: a frequency — the probability that a random individual is a
    heterozygote. It is a *probability*, not a variance, and it is a different
    concept from `genotypeVarianceHWE` even though the two coincide as numbers
    under Hardy-Weinberg. That coincidence is stated as a theorem below rather
    than left implicit in the shared formula, because conflating the two with
    the allelic variance `p(1-p)` is what produced the factor-of-four defect
    this corpus already had to repair. -/
def hweHeterozygosity (p : ℝ) : ℝ := 2 * p * (1 - p)

/-- **Heterozygosity peaks at one half, where it equals one half.** The coincidence with the
genotype variance recorded below is an identity between two bodies and does not fix either of
them; the value at the interior maximum does, and it is the only point at which a mistaken factor
of two is visible. -/
theorem hweHeterozygosity_at_half : hweHeterozygosity (1 / 2) = 1 / 2 := by
  unfold hweHeterozygosity
  norm_num

/-- **The heterozygote frequency and the genotype variance coincide under
Hardy-Weinberg.** They are different quantities — one is a probability, one is
a second moment — and this is the only thing that licenses writing either
formula where the other is meant. -/
theorem hweHeterozygosity_eq_genotypeVarianceHWE (p : ℝ) :
    hweHeterozygosity p = genotypeVarianceHWE p := by
  unfold hweHeterozygosity genotypeVarianceHWE; ring

/-- Heterozygosity is strictly increasing on (0, 1/2).
    Proof: het(q) - het(p) = 2(q - p)(1 - p - q). When p < q < 1/2,
    both factors are positive so het(q) > het(p). -/
theorem het_strict_mono_on_lower_half (p q : ℝ)
    (h_p : 0 < p) (h_p_lt : p < 1/2)
    (h_q : 0 < q) (h_q_lt : q < 1/2)
    (h_pq : p < q) :
    hweHeterozygosity p < hweHeterozygosity q := by
  unfold hweHeterozygosity
  nlinarith [sq_nonneg p, sq_nonneg q]

/-- **Discovered variants are biased toward EUR-common.**
    Variants discovered in EUR GWAS have higher MAF in EUR
    than in other ancestries on average. Discovery threshold
    requires n × 2p(1-p) × β² > χ²_threshold. Since n is the EUR
    sample size, variants passing this filter satisfy 2p_EUR(1-p_EUR) > c,
    meaning p_EUR cannot be too small. After drift, E[p_AFR] ≈ p_EUR
    but Var[p_AFR] ∝ Fst, so some variants become rarer in AFR.

    We derive the stronger statement that this directly lowers the expected
    additive variance contribution `2p(1-p)β²` for any nonzero effect size. -/
theorem discovered_variants_eur_biased
    (p_eur p_afr β : ℝ)
    (h_eur : 0 < p_eur) (h_eur_lt : p_eur < 1/2)
    (h_afr : 0 < p_afr) (h_afr_lt : p_afr < 1/2)
    (h_drift_down : p_afr < p_eur)
    (h_β_ne : β ≠ 0) :
    hweHeterozygosity p_afr * β ^ 2 <
      hweHeterozygosity p_eur * β ^ 2 := by
  have h_het_lt :=
    het_strict_mono_on_lower_half p_afr p_eur h_afr h_afr_lt h_eur h_eur_lt h_drift_down
  have h_β_sq_pos : 0 < β ^ 2 := sq_pos_of_ne_zero h_β_ne
  exact mul_lt_mul_of_pos_right h_het_lt h_β_sq_pos

/-- **Discovery bias inflates apparent portability gap.**
    Model definitions (let-bindings below):
    - r²_source = r²_causal + r²_tag_bonus (source R² includes tagging bonus)
    - r²_target = r²_causal × ρ² (target gets only causal signal, attenuated)
    - apparent_gap = r²_source - r²_target
    - true_causal_gap = r²_causal × (1 - ρ²)

    Algebraic derivation (verified by `ring`):
      apparent_gap = (r²_causal + r²_tag_bonus) - r²_causal × ρ²
                   = r²_causal - r²_causal × ρ² + r²_tag_bonus
                   = r²_causal × (1 - ρ²) + r²_tag_bonus
                   = true_causal_gap + r²_tag_bonus

    The tag bonus inflates the apparent gap beyond the true causal gap.
    This is a definitional identity: the proof content is the model
    decomposition, not the algebra. -/
theorem discovery_bias_inflates_source_r2
    (r2_causal r2_tag_bonus ρ_sq : ℝ) :
    let r2_source := r2_causal + r2_tag_bonus
    let r2_target := r2_causal * ρ_sq
    let apparent_gap := r2_source - r2_target
    let true_causal_gap := r2_causal * (1 - ρ_sq)
    apparent_gap = true_causal_gap + r2_tag_bonus := by
  simp only
  ring

/-- **Proportion of portable signal.**
    Of the total source PGS signal, only a fraction is portable:
    the part that uses causal variants shared across populations.
    portable_fraction = r²_causal / r²_total. -/
noncomputable def portableFraction (r2_causal r2_total : ℝ) : ℝ :=
  r2_causal / r2_total

/-- **portableFraction at zero r2_total, named.** With no total explained variance there is
nothing to be portable, and the fraction is undefined. Lean returns `0`: none of the signal
transfers, which is the reading a consumer takes for a score that transfers badly rather than for
a score with nothing to transfer. Consumers must require `r2_total ≠ 0`. -/
theorem portableFraction_zero_r2total_is_junk (r2_causal : ℝ) :
    portableFraction r2_causal 0 = 0 := by
  unfold portableFraction
  simp

/-- Portable fraction is ≤ 1. -/
theorem portable_fraction_le_one (r2_causal r2_total : ℝ)
    (h_le : r2_causal ≤ r2_total) (h_total : 0 < r2_total) :
    portableFraction r2_causal r2_total ≤ 1 := by
  unfold portableFraction
  rw [div_le_one h_total]
  exact h_le

end DiscoveryBias


/-!
## Power-Portability Tradeoff

There is a fundamental tradeoff between maximizing power in
one population and maximizing cross-population portability.
-/

section PowerPortabilityTradeoff


/-- **Multi-ancestry tradeoff: splitting budget.**
    With total budget N and two populations, allocate fraction α to pop1
    and (1-α) to pop2. Power in pop1 ∝ αN, power in pop2 ∝ (1-α)N.

    Compared to single-ancestry (all in pop1, α = 1):
    - Pop1 R² decreases: α × N × c < N × c when α < 1
    - Pop2 R² increases from 0: (1-α) × N × c > 0 when α < 1

    Both parts are derived from the allocation model. -/
theorem mul_lt_self_and_complement_mul_pos
    (N c₁ c₂ α : ℝ)
    (h_N : 0 < N) (h_c₁ : 0 < c₁) (h_c₂ : 0 < c₂)
    (h_α_pos : 0 < α) (h_α_lt : α < 1) :
    -- Multi-ancestry reduces best-pop R² (pop1 gets αN < N)
    α * N * c₁ < N * c₁ ∧
    -- Multi-ancestry creates nonzero worst-pop R² (pop2 gets (1-α)N > 0)
    0 < (1 - α) * N * c₂ := by
  constructor
  · -- α * N * c₁ < 1 * N * c₁ because α < 1 and N * c₁ > 0
    have h_Nc : 0 < N * c₁ := mul_pos h_N h_c₁
    nlinarith
  · -- (1 - α) * N * c₂ > 0 because 1 - α > 0 and N, c₂ > 0
    have h_one_minus : 0 < 1 - α := by linarith
    positivity

/-- **Minimax criterion favors multi-ancestry design.**
    Single-ancestry worst-case: best group gets R², worst gets ρ² × R²
    where ρ² < 1 is the portability ratio. So min_single = ρ² × R².

    Multi-ancestry at equal split (α = 1/2): each group gets N/2 samples.
    Worst-case R² ≥ R²(1 + ρ²)/2 (each pop gets half the direct power
    plus half the cross-pop transfer).

    We derive: ρ² × R² < R²(1 + ρ²)/2 for any 0 < ρ² < 1.
    Proof: multiply out to get 2ρ² < 1 + ρ², i.e., ρ² < 1. -/
theorem mul_lt_mul_avg_of_lt_one
    (R2 ρ_sq : ℝ)
    (h_R2 : 0 < R2) (h_ρ : 0 < ρ_sq) (h_ρ_lt : ρ_sq < 1) :
    -- single-ancestry worst-case < multi-ancestry worst-case
    ρ_sq * R2 < R2 * (1 + ρ_sq) / 2 := by
  -- Equivalent to: 2 * ρ_sq * R2 < R2 * (1 + ρ_sq)
  -- i.e., 2 * ρ_sq < 1 + ρ_sq  (dividing by R2 > 0)
  -- i.e., ρ_sq < 1, which is h_ρ_lt
  nlinarith [sq_nonneg ρ_sq]

/-- **Pareto frontier of power vs portability.**
    The set of achievable (power, portability) pairs forms a
    Pareto frontier. No design dominates in both dimensions.

    This is the definition of Pareto incomparability: if design 2
    has strictly more power but strictly less portability than
    design 1, then neither design Pareto-dominates the other.
    The proof is elementary order logic: strict inequality in one
    dimension contradicts the weak inequality required for dominance. -/
theorem pareto_no_dominance
    (power₁ port₁ power₂ port₂ : ℝ)
    (h_more_power : power₁ < power₂)
    (h_less_port : port₂ < port₁) :
    -- Neither design dominates the other
    ¬(power₂ ≤ power₁ ∧ port₁ ≤ port₂) := by
  intro ⟨h1, h2⟩; linarith

end PowerPortabilityTradeoff


/-!
## Optimal Multi-Population Study Design

Given constraints on total sample size and budget, how should
a multi-population GWAS be designed?
-/

section OptimalDesign

/-- **Proportional allocation.**
    Allocate samples proportional to population size.
    This is equitable but not necessarily optimal for PGS. -/
noncomputable def proportionalAllocation (pop_size total_n total_pop : ℝ) : ℝ :=
  total_n * (pop_size / total_pop)

/-- **proportionalAllocation at its junk point, named.** With no total population there are no
proportions to allocate by. Lean returns `0`: every ancestry receives nothing, so a recruitment
design against a missing denominator reports a complete, self-consistent, empty allocation
rather than failing. Consumers must exclude the argument that makes the guard vanish. -/
theorem proportionalAllocation_empty_reference_is_junk (pop_size total_n : ℝ) :
    proportionalAllocation pop_size total_n 0 = 0 := by
  unfold proportionalAllocation
  simp

/-- Proportional allocation sums to total. -/
theorem proportional_sums_to_total
    (n_total pop_A pop_B : ℝ)
    (h_pos_A : 0 < pop_A) (h_pos_B : 0 < pop_B)
    (h_total : 0 < n_total) :
    proportionalAllocation pop_A n_total (pop_A + pop_B) +
      proportionalAllocation pop_B n_total (pop_A + pop_B) = n_total := by
  unfold proportionalAllocation
  field_simp


/-- **Optimal allocation depends on objective.**
    With two pops and R² ∝ n_pop × c_pop, moving Δ samples from pop1
    to pop2 changes total R² by Δ(c₂ - c₁). When c₂ > c₁ (pop2 has
    higher marginal return, e.g., due to being undersampled), rebalancing
    toward pop2 increases total R².

    This proves that EUR-maximizing and equity-maximizing allocations
    diverge whenever marginal returns differ. -/
theorem optimal_depends_on_objective
    (Δ c₁ c₂ : ℝ)
    (h_Δ : 0 < Δ) (_h_c₁ : 0 < c₁) (_h_c₂ : 0 < c₂)
    (h_c₂_gt : c₁ < c₂) :
    -- Rebalancing toward pop2 increases pop2 R² more than it decreases pop1 R²
    Δ * c₁ < Δ * c₂ := by
  exact mul_lt_mul_of_pos_left h_c₂_gt h_Δ

/-- **Matching effective sample size across populations.**
    To achieve the same effective n for a variant at the same MAF p,
    we need: n_target × r²_target = n_source × r²_source.
    If r²_target < r²_source (shorter LD in target population), then
    n_target must be n_source × (r²_source / r²_target) > n_source.

    We derive the multiplier > 1 from the r² ratio, and show that
    at equal sample sizes, shorter LD yields lower effective n. -/
theorem afr_needs_more_samples
    (n_source : ℕ) (p r2_source r2_target : ℝ)
    (h_n : 0 < n_source)
    (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2_source : 0 < r2_source)
    (h_r2_target : 0 < r2_target)
    (h_shorter_ld : r2_target < r2_source) :
    -- The multiplier needed is r²_source / r²_target > 1
    1 < r2_source / r2_target ∧
    -- At same sample size, shorter LD gives lower effective n
    effectiveFisherInformation n_source p r2_target <
      effectiveFisherInformation n_source p r2_source := by
  constructor
  · -- r²_source / r²_target > 1 because r²_source > r²_target > 0
    rw [one_lt_div h_r2_target]
    exact h_shorter_ld
  · -- Direct application of monotonicity in r²
    exact effective_information_mono_r2 n_source p r2_target r2_source
      h_n h_p h_p_lt (le_of_lt h_r2_target) (le_of_lt h_r2_source) h_shorter_ld

/-- **General version: any population with shorter LD needs more samples.**
    The multiplier r²_long / r²_short is determined by the LD structure,
    not assumed. When both populations have the same MAF and nominal
    sample size, the one with lower r²_LD has strictly lower effective
    sample size. -/
theorem shorter_ld_needs_more_samples
    (n : ℕ) (p r2_long r2_short : ℝ)
    (h_n : 0 < n)
    (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2_long : 0 < r2_long)
    (h_r2_short : 0 < r2_short)
    (h_shorter : r2_short < r2_long) :
    -- Same sample size yields lower effective n with shorter LD
    effectiveFisherInformation n p r2_short < effectiveFisherInformation n p r2_long ∧
    -- The multiplier to compensate is > 1
    1 < r2_long / r2_short := by
  constructor
  · exact effective_information_mono_r2 n p r2_short r2_long
      h_n h_p h_p_lt (le_of_lt h_r2_short) (le_of_lt h_r2_long) h_shorter
  · rw [one_lt_div h_r2_short]
    exact h_shorter

end OptimalDesign

end Calibrator
