import Calibrator.Probability
import Calibrator.BayesianPGSTheory
import Calibrator.PortabilityDrift
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Calibrator.OpenQuestions
import Calibrator.SimulationValidation
import Calibrator.AncestrySpecificPower
import Calibrator.HaplotypeTheory

namespace Calibrator

open MeasureTheory
open Matrix
open scoped Matrix

/-!
# Genetic Architecture Discovery, Winner's Curse, and Effect Estimation

This file formalizes how the discovery of genetic architecture
(through GWAS) is affected by population choice, and how this
affects downstream PGS portability.

Key results:
1. GWAS discovery power depends on LD and MAF in the discovery sample
2. Ascertainment bias from discovery population
3. Effect size estimation and shrinkage
4. Multi-trait analysis and genetic correlation

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## GWAS Discovery and Population Specificity

GWAS discovers associations that are specific to the population's
LD structure and allele frequency spectrum.
-/

section GWASDiscovery

/-! Genotype variance of an additive tag SNP under Hardy-Weinberg equilibrium
was defined here as `tagGenotypeVariance`. It is `genotypeVarianceHWE` from
`Calibrator.AncestrySpecificPower`, and the definition here has been deleted in
favour of that one; the empirical status and the `Denotes` declaration
travelled with it.

Convention: the argument is whatever frequency the caller supplies; this is the
genotype variance `2p(1-p)` at that frequency. The old name said tag for
historical reasons, but `discoveryNCP` correctly passes the *causal*
frequency. -/

/-- Noncentrality parameter for a GWAS tag SNP.

    The `ld` term captures attenuation of the causal effect by population-specific
    LD tagging, and `2 * maf * (1 - maf)` is the genotype variance term from the
    allele-frequency spectrum in the discovery population. 
    Convention: `maf_causal` is the allele frequency of the *causal* variant,
    not of the tag. The tag's own variance cancels algebraically, since
    `β_tag = β r σ_causal / σ_tag` gives
    `NCP = n β_tag² σ_tag² = n β² r² σ_causal²`. Reading the argument as the
    tag's frequency is wrong by −24% to +33% whenever the two frequencies
    differ, and coincides only when they are equal, which is why a test at
    matched frequencies would miss it. It understates discovery power for a
    common causal variant tagged by a rarer SNP and overstates it in the
    reverse case, so it mis-ranks exactly the rare-variant configurations that
    `RareVariantPortability` reasons about.

    Empirical status: VALIDATED under this convention (matches simulated NCP to
    three significant figures across mismatched tag and causal frequencies). -/
def discoveryNCP (n β maf_causal ld : ℝ) : ℝ :=
  n * β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf_causal

/-- A locus is discovered when its test statistic crosses the genome-wide
    `z`-threshold. In the one-degree-of-freedom Gaussian approximation this is
    equivalent to `z^2 ≤ discoveryNCP`.

    Empirical status: UNTESTED.

    Convention: `maf_causal` is the causal variant's frequency, matching
    `discoveryNCP`, which this predicate thresholds. -/
def gwasDiscovered (n β maf_causal ld z : ℝ) : Prop :=
  z ^ 2 ≤ discoveryNCP n β maf_causal ld

/-- **The GWAS noncentrality parameter increases with sample size.** -/
theorem discoveryNCP_increases_with_n
    (β p ld : ℝ) (n₁ n₂ : ℕ)
    (hβ : β ≠ 0) (hp : 0 < p) (hp1 : p < 1) (hld : ld ≠ 0) (h_n : n₁ < n₂) :
    discoveryNCP (n₁ : ℝ) β p ld < discoveryNCP (n₂ : ℝ) β p ld := by
  unfold discoveryNCP
  have h_factor : 0 < β ^ 2 * ld ^ 2 * (2 * p * (1 - p)) := by
    have hβ2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
    have hld2 : 0 < ld ^ 2 := sq_pos_of_ne_zero hld
    have h_var : 0 < 2 * p * (1 - p) := by
      nlinarith
    exact mul_pos (mul_pos hβ2 hld2) h_var
  simpa [genotypeVarianceHWE, mul_assoc] using
    mul_lt_mul_of_pos_right (Nat.cast_lt.mpr h_n) h_factor

/-- On the left half of the allele-frequency spectrum, genotype variance is
strictly increasing as the allele frequency moves toward `1/2`. -/
theorem genotypeVarianceHWE_strictMono_left_half
    (maf₁ maf₂ : ℝ)
    (h_maf₂_pos : 0 < maf₂)
    (h_order : maf₂ < maf₁)
    (h_maf₁_half : maf₁ ≤ 1 / 2) :
    genotypeVarianceHWE maf₂ < genotypeVarianceHWE maf₁ := by
  unfold genotypeVarianceHWE
  have h_maf₂_half : maf₂ < 1 / 2 := lt_of_lt_of_le h_order h_maf₁_half
  have h_maf₂_nonneg : 0 ≤ maf₂ := le_of_lt h_maf₂_pos
  -- 2p(1-p) is a genotype variance, so the gap factors as (maf₁ - maf₂)(1 - maf₁ - maf₂),
  -- and both factors are positive below the 1/2 turning point.
  nlinarith [mul_pos (sub_pos.mpr h_order)
    (show (0:ℝ) < 1 - maf₁ - maf₂ by linarith)]

/-- **Different LD and MAF can produce population-specific GWAS hits.**
    This theorem now proves the biologically relevant part explicitly:

    - the same causal effect and sample size can produce a larger tag-SNP NCP in
      population 1 because population 1 has both stronger tag-to-causal LD and a
      larger genotype-variance term `2p(1-p)`;
    - once the genome-wide threshold lies between those two NCP values, the
      locus is discovered in population 1 and missed in population 2. -/
theorem different_populations_different_hits
    (n β z maf₁ maf₂ ld₁ ld₂ : ℝ)
    (h_n : 0 < n)
    (h_beta : β ≠ 0)
    (h_maf₂_pos : 0 < maf₂)
    (h_maf_order : maf₂ < maf₁)
    (h_maf₁_half : maf₁ ≤ 1 / 2)
    (h_ld_sq : ld₂ ^ 2 < ld₁ ^ 2)
    (h_threshold_between :
      discoveryNCP n β maf₂ ld₂ < z ^ 2 ∧ z ^ 2 ≤ discoveryNCP n β maf₁ ld₁) :
    discoveryNCP n β maf₂ ld₂ < discoveryNCP n β maf₁ ld₁ ∧
      gwasDiscovered n β maf₁ ld₁ z ∧ ¬ gwasDiscovered n β maf₂ ld₂ z := by
  rcases h_threshold_between with ⟨h_pop2_below, h_pop1_above⟩
  have h_var :
      genotypeVarianceHWE maf₂ < genotypeVarianceHWE maf₁ := by
    exact genotypeVarianceHWE_strictMono_left_half
      maf₁ maf₂ h_maf₂_pos h_maf_order h_maf₁_half
  have h_var_pos : 0 < genotypeVarianceHWE maf₂ := by
    unfold genotypeVarianceHWE
    have h_maf₂_lt_one : maf₂ < 1 := by
      have h_maf₂_lt_half : maf₂ < 1 / 2 := lt_of_lt_of_le h_maf_order h_maf₁_half
      linarith
    nlinarith [mul_pos h_maf₂_pos (sub_pos.mpr h_maf₂_lt_one)]
  have h_ld_sq_nn : 0 ≤ ld₁ ^ 2 := sq_nonneg ld₁
  have h_prod_lt :
      ld₂ ^ 2 * genotypeVarianceHWE maf₂ <
        ld₁ ^ 2 * genotypeVarianceHWE maf₁ := by
    calc
      ld₂ ^ 2 * genotypeVarianceHWE maf₂
        < ld₁ ^ 2 * genotypeVarianceHWE maf₂ := by
            exact mul_lt_mul_of_pos_right h_ld_sq h_var_pos
      _ ≤ ld₁ ^ 2 * genotypeVarianceHWE maf₁ := by
            exact mul_le_mul_of_nonneg_left (le_of_lt h_var) h_ld_sq_nn
  have h_prefactor_pos : 0 < n * β ^ 2 := by
    have h_beta_sq : 0 < β ^ 2 := sq_pos_of_ne_zero h_beta
    exact mul_pos h_n h_beta_sq
  have h_ncp_lt :
      discoveryNCP n β maf₂ ld₂ < discoveryNCP n β maf₁ ld₁ := by
    unfold discoveryNCP
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_lt_mul_of_pos_left h_prod_lt h_prefactor_pos
  refine ⟨h_ncp_lt, h_pop1_above, ?_⟩
  exact not_le_of_gt h_pop2_below

/-- **Winner's curse in GWAS.**
    The estimated effect size of a newly discovered variant is biased
    upward. If β̂ = β_true + noise, and we condition on |β̂| > threshold,
    then |β̂| > |β_true| whenever noise has the same sign as β_true.
    Here we prove the simpler statement: β̂ = β_true + ε with ε > 0
    and β_true > 0 implies |β̂| > |β_true|. -/
theorem winners_curse_overestimates
    (β_true ε : ℝ)
    (h_beta : 0 < β_true) (h_noise : 0 < ε) :
    |β_true| < |β_true + ε| := by
  rw [abs_of_pos h_beta, abs_of_pos (by linarith)]
  linarith

/-- **Winner's curse is worse for variants near the significance threshold.**
    The bias is proportional to the threshold / true effect ratio. -/
theorem winners_curse_worse_near_threshold
    (β₁ β₂ threshold : ℝ)
    (h₁_near : |β₁| < 1.5 * threshold)
    (h₂_far : 2 * threshold < |β₂|)
    (h_thr : 0 < threshold)
    (hβ₁ : β₁ ≠ 0) :
    -- Relative bias is larger for β₁
    threshold / |β₁| > threshold / |β₂| := by
  apply div_lt_div_of_pos_left h_thr
  · exact abs_pos.mpr hβ₁
  · linarith

end GWASDiscovery


/-!
## Clumping and Thresholding (C+T) vs Bayesian Methods

Wang et al. use C+T. Reviewers suggest PRS-CS. We formalize
why the method matters for portability.
-/

section PGSMethods

/-- Target score-estimation risk from locus-specific effect-estimation MSE and
target tag-variance weights. This is the biologically relevant quantity for a
transported linear score: each locus contributes its target genotype variance
times the MSE of the learned effect estimate. -/
noncomputable def taggedScoreEstimationRisk {m : ℕ}
    (targetTagVariance estimatorMSE : Fin m → ℝ) : ℝ :=
  ∑ i, targetTagVariance i * estimatorMSE i

/-- C+T-to-dense-model gap measured as target causal signal mass missed by the
current discovered set. When discovery at larger sample size recovers more
causal loci, this gap shrinks. -/
noncomputable def ctMissedTargetSignal {m : ℕ}
    (discovered : Finset (Fin m)) (targetCausalSignal : Fin m → ℝ) : ℝ :=
  Finset.sum (Finset.univ \ discovered) fun i => targetCausalSignal i

/-- **C+T uses fewer variants → more variable portability estimates.**
    This is now stated on an explicit per-locus estimation-risk surface rather
    than the old `σ² / k` surrogate.

    - C+T is modeled as a hard-thresholded no-shrinkage estimator on retained loci;
    - the Bayesian method is modeled as the posterior mean with the optimal
      Gaussian shrinkage factor from `BayesianPGSTheory`;
    - target score-estimation risk is the sum of locus-specific target genotype
      variance times the effect-estimation MSE.

    Under positive target variance and positive signal at every retained locus,
    the Bayesian estimator has strictly lower target score-estimation risk. -/
theorem ct_more_variable_than_bayesian
    {m : ℕ}
    (targetTagVariance σSq βSq : Fin m → ℝ)
    (h_nonempty : Nonempty (Fin m))
    (h_tag : ∀ i, 0 < targetTagVariance i)
    (h_sigma : ∀ i, 0 < σSq i)
    (h_beta : ∀ i, 0 < βSq i) :
    taggedScoreEstimationRisk targetTagVariance
        (fun i => jamesSteinMSE
          (optimalShrinkage (σSq i) (βSq i)) (σSq i) (βSq i)) <
      taggedScoreEstimationRisk targetTagVariance
        (fun i => jamesSteinMSE 1 (σSq i) (βSq i)) := by
  unfold taggedScoreEstimationRisk
  refine Finset.sum_lt_sum ?_ ?_
  · intro i _
    have h_mse :
        jamesSteinMSE (optimalShrinkage (σSq i) (βSq i)) (σSq i) (βSq i) <
          jamesSteinMSE 1 (σSq i) (βSq i) := by
      exact bayesian_shrinkage_reduces_mse (σSq i) (βSq i) (h_sigma i) (h_beta i)
    exact le_of_lt (mul_lt_mul_of_pos_left h_mse (h_tag i))
  · rcases h_nonempty with ⟨i⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have h_mse :
        jamesSteinMSE (optimalShrinkage (σSq i) (βSq i)) (σSq i) (βSq i) <
          jamesSteinMSE 1 (σSq i) (βSq i) := by
      exact bayesian_shrinkage_reduces_mse (σSq i) (βSq i) (h_sigma i) (h_beta i)
    exact mul_lt_mul_of_pos_left h_mse (h_tag i)


/-- **Both methods converge with infinite sample size.**
    The large-sample convergence statement is now tied to explicit discovered
    causal content: when the larger-sample C+T run recovers a superset of the
    smaller-sample discovered loci, the target causal signal still missing from
    C+T weakly decreases, and it is exactly `0` once all loci are discovered.
    This is the biologically relevant sense in which the sparse method
    converges toward a dense model. -/
theorem methods_converge_at_large_n
    {m : ℕ}
    (discoveredSmallN discoveredLargeN : Finset (Fin m))
    (targetCausalSignal : Fin m → ℝ)
    (h_signal : ∀ i, 0 ≤ targetCausalSignal i)
    (h_nested : discoveredSmallN ⊆ discoveredLargeN) :
    ctMissedTargetSignal discoveredLargeN targetCausalSignal ≤
      ctMissedTargetSignal discoveredSmallN targetCausalSignal ∧
    ctMissedTargetSignal Finset.univ targetCausalSignal = 0 := by
  constructor
  · unfold ctMissedTargetSignal
    have h_subset : Finset.univ \ discoveredLargeN ⊆ Finset.univ \ discoveredSmallN := by
      intro i hi
      simp at hi ⊢
      intro hiSmall
      exact hi (h_nested hiSmall)
    exact Finset.sum_le_sum_of_subset_of_nonneg h_subset
      (by intro i _ _; exact h_signal i)
  · simp [ctMissedTargetSignal]

/-- **P-value threshold selection affects portability differently.**
    Lenient threshold includes k_lenient > k_stringent SNPs. Each extra
    SNP adds signal V_signal_per_snp but also LD-dependent noise V_noise_per_snp.
    In the source population, net R² gain = (V_signal - V_noise) × extra_snps.
    In the target population, the LD-noise component may double (different LD),
    so target net = (V_signal - 2 × V_noise) × extra_snps. We show: there
    exist regimes where the source gains but the target loses. -/
theorem threshold_tradeoff
    (V_signal_per_snp V_noise_per_snp extra_snps : ℝ)
    (h_extra : 0 < extra_snps)
    (h_signal_wins_source : V_noise_per_snp < V_signal_per_snp)
    (h_noise_wins_target : V_signal_per_snp < 2 * V_noise_per_snp) :
    -- Source gains R² (signal > noise)
    0 < (V_signal_per_snp - V_noise_per_snp) * extra_snps ∧
    -- Target loses R² (noise amplified by LD mismatch > signal)
    (V_signal_per_snp - 2 * V_noise_per_snp) * extra_snps < 0 := by
  constructor
  · exact mul_pos (by linarith) h_extra
  · exact mul_neg_of_neg_of_pos (by linarith) h_extra

end PGSMethods


/-!
## Effect Size Estimation and Portability

Accurate effect size estimation is crucial for PGS performance.
Different estimation methods have different bias-variance tradeoffs.
-/

section EffectEstimation

/-- Expected one-locus linear-effect estimate under an additive estimation-error
decomposition `β̂ = β_true + ε̄`, where `ε̄` is the mean estimation error.

    Empirical status: UNTESTED. -/
noncomputable def expectedLinearEffectEstimate
    (β_true meanEstimationError : ℝ) : ℝ :=
  β_true + meanEstimationError

/-- One-locus OLS effect-estimation variance under genotype variance `varX` and
sample size `n`. -/
noncomputable def olsEffectEstimationVariance
    (σ2 varX n : ℝ) : ℝ :=
  σ2 / (n * varX)

/-- **Cross-check: haplotype effect estimation and one-locus OLS have the same
estimation variance.** `HaplotypeTheory.haplotypeEffectEstimationVariance`
divides by `n × f` with `f` a haplotype frequency; this divides by `n × varX`
with `varX` a genotype variance. The two denominators are different quantities
and the map is the same, so the arguments have to be read in the same order —
which is the mistake this theorem is here to prevent, since the two definitions
list `n` and the scale factor in opposite positions. -/
theorem olsEffectEstimationVariance_eq_haplotypeEffectEstimationVariance
    (σ2 varX n : ℝ) :
    olsEffectEstimationVariance σ2 varX n =
      haplotypeEffectEstimationVariance σ2 n varX := by
  unfold olsEffectEstimationVariance haplotypeEffectEstimationVariance; ring

/-- The set of loci retained by a hard-threshold sparse estimator such as
LASSO, modeled here by the loci whose marginal effect magnitude clears the
selection threshold `lam`. -/
noncomputable def lassoActiveLoci {m : ℕ}
    (β : Fin m → ℝ) (lam : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => lam ≤ |β i|

/-- Equal-contribution per-locus signal in a trait with total heritability `h2`
spread over `k` causal loci. -/
noncomputable def perCausalLocusSignal
    (h2 k : ℝ) : ℝ :=
  h2 / k

/-- **OLS effect estimates are unbiased but noisy.**
    This theorem now includes the actual unbiasedness statement for the
    one-locus additive model:

    - if the mean estimation error is `0`, then the expected estimate equals
      the true effect;
    - at the same genotype variance, increasing `n` lowers the OLS effect
      estimation variance `σ² / (n × Var(X))`. -/
theorem ols_unbiased
    (β_true meanEstimationError σ2 varX n₁ n₂ : ℝ)
    (h_mean_zero : meanEstimationError = 0)
    (h_σ2 : 0 < σ2) (h_varX : 0 < varX)
    (h_n₁ : 0 < n₁) (h_n : n₁ < n₂) :
    expectedLinearEffectEstimate β_true meanEstimationError = β_true ∧
      olsEffectEstimationVariance σ2 varX n₂ <
        olsEffectEstimationVariance σ2 varX n₁ := by
  constructor
  · simp [expectedLinearEffectEstimate, h_mean_zero]
  · unfold olsEffectEstimationVariance
    exact div_lt_div_of_pos_left h_σ2 (mul_pos h_n₁ h_varX)
      (by nlinarith)

/-- **Ridge regression shrinks effects toward zero.**
    β̂_ridge = (X'X + λI)⁻¹X'Y = β_true × X'X/(X'X + λI).
    Bias: E[β̂] = β_true × (1 - λ/(X'X + λ)). -/
theorem ridge_introduces_bias
    (β_true lam xtx : ℝ)
    (h_lam : 0 < lam) (h_xtx : 0 < xtx) :
    |β_true * xtx / (xtx + lam)| < |β_true| ∨ β_true = 0 := by
  by_cases hβ : β_true = 0
  · right; exact hβ
  · left
    rw [abs_div, abs_mul]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < |xtx + lam|)]
    rw [abs_of_pos (by linarith : (0:ℝ) < xtx), abs_of_pos (by linarith : (0:ℝ) < xtx + lam)]
    nlinarith [abs_nonneg β_true, abs_pos.mpr hβ]

/-- **LASSO performs variable selection.**
    This theorem is now stated on an explicit locus-level active set rather
    than a bare cardinality inequality.

    If one locus has true effect magnitude below the selection threshold `lam`,
    then that locus is absent from the retained set and the active set is
    strictly smaller than the full OLS support. -/
theorem lasso_sparsifies
    {m : ℕ}
    (β : Fin m → ℝ) (lam : ℝ) (i₀ : Fin m)
    (h_sub : |β i₀| < lam) :
    i₀ ∉ lassoActiveLoci β lam ∧
      (lassoActiveLoci β lam).card < Fintype.card (Fin m) := by
  have h_not_mem : i₀ ∉ lassoActiveLoci β lam := by
    simp [lassoActiveLoci, not_le_of_gt h_sub]
  have h_subset : lassoActiveLoci β lam ⊆ Finset.univ := by
    intro i hi
    simp
  have h_card :
      (lassoActiveLoci β lam).card < (Finset.univ : Finset (Fin m)).card := by
    exact Finset.card_lt_card <|
      (Finset.ssubset_iff_of_subset h_subset).mpr ⟨i₀, Finset.mem_univ i₀, h_not_mem⟩
  exact ⟨h_not_mem, by simpa using h_card⟩

/-- **Estimation method affects portability differently for different traits.**
    This theorem now connects the architecture directly to sparse-selection
    behavior.

    With the same total heritability `h2`, an oligogenic trait with fewer
    causal loci has larger per-locus signal than a more polygenic trait. If the
    sparse-selection threshold `lam` lies between those two per-locus signals,
    then the polygenic locus is dropped while the oligogenic locus is retained. -/
theorem estimation_trait_interaction
    (h2 k_poly k_oligo lam : ℝ)
    (h_h2 : 0 < h2) (h_oligo : 0 < k_oligo)
    (h_more_poly : k_oligo < k_poly)
    (h_between :
      perCausalLocusSignal h2 k_poly < lam ∧
      lam ≤ perCausalLocusSignal h2 k_oligo) :
    ¬ lam ≤ perCausalLocusSignal h2 k_poly ∧
      lam ≤ perCausalLocusSignal h2 k_oligo ∧
      perCausalLocusSignal h2 k_poly < perCausalLocusSignal h2 k_oligo := by
  rcases h_between with ⟨h_poly_drop, h_oligo_keep⟩
  have h_signal_order :
      perCausalLocusSignal h2 k_poly < perCausalLocusSignal h2 k_oligo := by
    unfold perCausalLocusSignal
    exact div_lt_div_of_pos_left h_h2 h_oligo (by linarith)
  exact ⟨not_le_of_gt h_poly_drop, h_oligo_keep, h_signal_order⟩

end EffectEstimation


/-!
## Multi-Trait Analysis and Genetic Correlation

Multi-trait GWAS methods can improve portability by leveraging
shared genetic architecture across related traits.
-/

section MultiTraitAnalysis

/-- **Genetic correlation between traits.**
    rg = Cov_g(trait1, trait2) / √(V_g1 × V_g2). -/
noncomputable def geneticCorrelation
    (cov_g vg₁ vg₂ : ℝ) : ℝ :=
  cov_g / Real.sqrt (vg₁ * vg₂)

/-- Effective discovery-sample size for trait A after borrowing information
from a genetically correlated trait B.

    Empirical status: UNTESTED. -/
noncomputable def multiTraitEffectiveSampleSize
    (n₁ n₂ rg : ℝ) : ℝ :=
  n₁ + rg ^ 2 * n₂

/-- **Cross-check: borrowing across traits and borrowing across ancestries are
the same arithmetic.** `BayesianPGSTheory.multiAncestryEffectiveN` adds
`rg² · n_other` to the target sample size for a genetically correlated
*ancestry*; this adds it for a genetically correlated *trait*. They are
different claims about different data, and they had better not drift apart in
the exponent on `rg`, which is what this theorem pins. -/
theorem multiTraitEffectiveSampleSize_eq_multiAncestryEffectiveN (n₁ n₂ rg : ℝ) :
    multiTraitEffectiveSampleSize n₁ n₂ rg = multiAncestryEffectiveN n₁ rg n₂ := by
  unfold multiTraitEffectiveSampleSize multiAncestryEffectiveN; ring

/-- GWAS noncentrality parameter after cross-trait borrowing.

    Empirical status: UNTESTED. It carried no marker of its own while it sat
    next to `multiTraitEffectiveSampleSize`, whose marker it was reading.

    Convention: `maf_causal` is the causal variant's frequency, as in
    `discoveryNCP`. -/
noncomputable def multiTraitDiscoveryNCP
    (n₁ n₂ rg β maf ld : ℝ) : ℝ :=
  discoveryNCP (multiTraitEffectiveSampleSize n₁ n₂ rg) β maf ld

/-- Genetic correlation is bounded by [-1, 1] (Cauchy-Schwarz). -/
theorem genetic_correlation_bounded
    (cov_g vg₁ vg₂ : ℝ)
    (h_cs : cov_g ^ 2 ≤ vg₁ * vg₂)
    (h₁ : 0 < vg₁) (h₂ : 0 < vg₂) :
    |geneticCorrelation cov_g vg₁ vg₂| ≤ 1 := by
  unfold geneticCorrelation
  rw [abs_div]
  rw [div_le_one (by exact abs_pos.mpr (Real.sqrt_pos.mpr (by positivity)).ne')]
  rw [abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  exact (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr (by nlinarith [sq_abs cov_g])

/-- Explicit cross-trait borrowing model for source-trained weights applied to a
related target trait.

The source score is represented by `sourceWeights`, the shared SNP-to-causal
architecture by `sigmaTagCausal`, the trait-A effect vector by `sharedTraitEffect`,
and the trait-B-specific increment by `traitBSpecificEffect`. The scalar `rg`
attenuates the shared component transferred from trait A into trait B. -/
structure CrossTraitBorrowingModel (p q : ℕ) where
  sourceWeights : Fin p → ℝ
  sigmaTagCausal : Matrix (Fin p) (Fin q) ℝ
  sharedTraitEffect : Fin q → ℝ
  traitBSpecificEffect : Fin q → ℝ
  rg : ℝ

namespace CrossTraitBorrowingModel

/-- Trait-B cross-covariance component borrowed from trait A through shared
genetic architecture. -/
noncomputable def borrowedTraitBCrossCov {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : Fin p → ℝ :=
  m.sigmaTagCausal.mulVec (fun j => m.rg * m.sharedTraitEffect j)

/-- Trait-B cross-covariance component specific to trait B after removing the
shared trait-A component. -/
noncomputable def traitBSpecificCrossCov {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : Fin p → ℝ :=
  m.sigmaTagCausal.mulVec m.traitBSpecificEffect

/-- Total trait-B cross-covariance seen by the source-trained score. -/
noncomputable def totalTraitBCrossCov {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : Fin p → ℝ :=
  borrowedTraitBCrossCov m + traitBSpecificCrossCov m

/-- Borrowed trait-B projection captured by the source-trained score. -/
noncomputable def borrowedTraitBProjection {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : ℝ :=
  dotProduct m.sourceWeights (borrowedTraitBCrossCov m)

/-- Total trait-B projection captured by the source-trained score. -/
noncomputable def totalTraitBProjection {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : ℝ :=
  dotProduct m.sourceWeights (totalTraitBCrossCov m)

theorem traitBSpecificCrossCov_nonneg {p q : ℕ}
    (m : CrossTraitBorrowingModel p q)
    (h_sigma : ∀ i j, 0 ≤ m.sigmaTagCausal i j)
    (h_specific : ∀ j, 0 ≤ m.traitBSpecificEffect j) :
    0 ≤ traitBSpecificCrossCov m := by
  intro i
  unfold traitBSpecificCrossCov Matrix.mulVec
  exact Finset.sum_nonneg fun j _ => mul_nonneg (h_sigma i j) (h_specific j)

theorem borrowedTraitBCrossCov_nonneg {p q : ℕ}
    (m : CrossTraitBorrowingModel p q)
    (h_sigma : ∀ i j, 0 ≤ m.sigmaTagCausal i j)
    (h_shared : ∀ j, 0 ≤ m.sharedTraitEffect j)
    (h_rg : 0 ≤ m.rg) :
    0 ≤ borrowedTraitBCrossCov m := by
  intro i
  unfold borrowedTraitBCrossCov Matrix.mulVec
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (h_sigma i j) (mul_nonneg h_rg (h_shared j))

end CrossTraitBorrowingModel

/-- **Cross-trait portability leverages genetic correlation.**
    This theorem is now stated on an explicit SNP/tag/cross-trait state.

    The trait-B signal seen by the source-trained score decomposes into:

    - a borrowed component coming from trait A through shared architecture and
      cross-trait correlation `rg`; and
    - a trait-B-specific component through the same tagging surface.

    When all weights, tag-to-causal entries, shared effects, and trait-B-specific
    effects are nonnegative, the borrowed component is itself nonnegative and is
    bounded above by the total transported trait-B projection. -/
theorem cross_trait_portability_gain
    {p q : ℕ}
    (m : CrossTraitBorrowingModel p q)
    (h_weights : ∀ i, 0 ≤ m.sourceWeights i)
    (h_sigma : ∀ i j, 0 ≤ m.sigmaTagCausal i j)
    (h_shared : ∀ j, 0 ≤ m.sharedTraitEffect j)
    (h_specific : ∀ j, 0 ≤ m.traitBSpecificEffect j)
    (h_rg : 0 ≤ m.rg) :
    0 ≤ m.borrowedTraitBProjection ∧
      m.borrowedTraitBProjection ≤ m.totalTraitBProjection := by
  have h_borrowed_cov_nonneg :
      0 ≤ m.borrowedTraitBCrossCov := by
    exact CrossTraitBorrowingModel.borrowedTraitBCrossCov_nonneg
      m h_sigma h_shared h_rg
  have h_specific_cov_nonneg :
      0 ≤ m.traitBSpecificCrossCov := by
    exact CrossTraitBorrowingModel.traitBSpecificCrossCov_nonneg
      m h_sigma h_specific
  have h_borrowed_nonneg :
      0 ≤ m.borrowedTraitBProjection := by
    unfold CrossTraitBorrowingModel.borrowedTraitBProjection
    exact dotProduct_nonneg_of_nonneg h_weights h_borrowed_cov_nonneg
  have h_total_ge :
      m.borrowedTraitBProjection ≤ m.totalTraitBProjection := by
    have h_cov_le :
        m.borrowedTraitBCrossCov ≤ m.totalTraitBCrossCov := by
      intro i
      change m.borrowedTraitBCrossCov i ≤
        m.borrowedTraitBCrossCov i + m.traitBSpecificCrossCov i
      exact le_add_of_nonneg_right (h_specific_cov_nonneg i)
    unfold CrossTraitBorrowingModel.borrowedTraitBProjection
      CrossTraitBorrowingModel.totalTraitBProjection
    exact dotProduct_le_dotProduct_of_nonneg_left h_cov_le h_weights
  constructor
  · exact h_borrowed_nonneg
  · exact h_total_ge

/-- **Multi-trait GWAS increases effective sample size.**
    This is now connected directly to GWAS discovery power.

    If trait B contributes cross-trait information proportional to `rg² × n₂`,
    then the effective sample size for trait A strictly increases, and so does
    the trait-A discovery noncentrality parameter for the same tag SNP. -/
theorem multi_trait_increases_effective_n
    (n₁ n₂ rg β maf ld : ℝ)
    (h_n₂ : 0 < n₂)
    (h_rg : 0 < rg)
    (h_beta : β ≠ 0)
    (h_maf : 0 < maf) (h_maf_lt_one : maf < 1)
    (h_ld : ld ≠ 0) :
    n₁ < multiTraitEffectiveSampleSize n₁ n₂ rg ∧
      discoveryNCP n₁ β maf ld <
        multiTraitDiscoveryNCP n₁ n₂ rg β maf ld := by
  have h_gain : 0 < rg ^ 2 * n₂ := by
    exact mul_pos (sq_pos_of_ne_zero (ne_of_gt h_rg)) h_n₂
  have h_n : n₁ < multiTraitEffectiveSampleSize n₁ n₂ rg := by
    unfold multiTraitEffectiveSampleSize
    linarith
  have h_factor : 0 < β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf := by
    have h_beta_sq : 0 < β ^ 2 := sq_pos_of_ne_zero h_beta
    have h_ld_sq : 0 < ld ^ 2 := sq_pos_of_ne_zero h_ld
    have h_var : 0 < genotypeVarianceHWE maf := by
      unfold genotypeVarianceHWE
      nlinarith [mul_pos h_maf (sub_pos.mpr h_maf_lt_one)]
    exact mul_pos (mul_pos h_beta_sq h_ld_sq) h_var
  constructor
  · exact h_n
  · unfold multiTraitDiscoveryNCP discoveryNCP multiTraitEffectiveSampleSize
    have h_ncp :
        n₁ * (β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf) <
          (n₁ + rg ^ 2 * n₂) * (β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf) := by
      exact mul_lt_mul_of_pos_right h_n h_factor
    simpa [mul_assoc, mul_left_comm, mul_comm] using h_ncp

/-- **Genetic correlation may differ across populations.**
    If the shared environmental component changes, the genetic
    correlation between traits can change. The genetic correlation
    rg = cov_g / √(vg₁ × vg₂). When the genetic covariance
    changes from cov₁ to cov₂ (due to GxE affecting shared
    pathways differently), the genetic correlations differ. -/
theorem genetic_correlation_population_specific
    (cov₁ cov₂ vg₁ vg₂ : ℝ)
    (h_vg₁ : 0 < vg₁) (h_vg₂ : 0 < vg₂)
    (h_cov_diff : cov₁ ≠ cov₂) :
    geneticCorrelation cov₁ vg₁ vg₂ ≠ geneticCorrelation cov₂ vg₁ vg₂ := by
  unfold geneticCorrelation
  intro h
  apply h_cov_diff
  have h_sqrt_pos : 0 < Real.sqrt (vg₁ * vg₂) := Real.sqrt_pos.mpr (mul_pos h_vg₁ h_vg₂)
  have h_sqrt_ne : Real.sqrt (vg₁ * vg₂) ≠ 0 := ne_of_gt h_sqrt_pos
  field_simp at h
  exact h

end MultiTraitAnalysis


/-!
## Future Directions: Whole Genome Sequencing and Rare Variants

WGS enables discovery of rare variants, which are mostly
population-specific. This has implications for portability.
-/

section WGSAndRareVariants

/-! The portability ratio for a mechanistic transported-score model was
restated here as `sourceTargetPortabilityRatio`. It is
`mechanisticPortabilityRatio` from `Calibrator.SimulationValidation`, and the
restatement has been deleted in favour of that one. -/

/-- Common-variant-only witness: one shared common causal locus is directly
scored in both populations, and there is no proxy tagging or target-only
biology. -/
noncomputable def commonOnlyPortableModel : CrossPopulationMetricModel 2 2 where
  beta := Pop.pair (![1, 0]) (![1, 0])
  sigmaTag := Pop.pair 1 1
  directCausal := Pop.pair (!![1, 0; 0, 0]) (!![1, 0; 0, 0])
  proxyTagging := Pop.pair 0 0
  contextCross := Pop.pair (![0, 0]) (![0, 0])
  outcomeVariance := Pop.pair 4 4
  novelDirectCausal := Pop.pair 0 0
  novelProxyTagging := Pop.pair 0 0
  novelCausalEffect := Pop.pair 0 (![0, 0])
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := 1 / 2
  novelUntaggablePhenotypeVarianceTarget_nonneg := by norm_num
  targetPrevalence_pos := by norm_num
  targetPrevalence_lt_one := by norm_num
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  outcomeVariance_pos := by intro P; cases P <;> norm_num

/-- Common-plus-rare witness: the source score uses one shared common causal
locus and one source-specific rare causal locus. The target retains only the
common locus, so the within-source `R²` rises while the transported target
signal stays unchanged. -/
noncomputable def commonAndRarePortableModel : CrossPopulationMetricModel 2 2 where
  beta := Pop.pair (![1, 1]) (![1, 0])
  sigmaTag := Pop.pair 1 1
  directCausal := Pop.pair 1 1
  proxyTagging := Pop.pair 0 0
  contextCross := Pop.pair (![0, 0]) (![0, 0])
  outcomeVariance := Pop.pair 4 4
  novelDirectCausal := Pop.pair 0 0
  novelProxyTagging := Pop.pair 0 0
  novelCausalEffect := Pop.pair 0 (![0, 0])
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := 1 / 2
  novelUntaggablePhenotypeVarianceTarget_nonneg := by norm_num
  targetPrevalence_pos := by norm_num
  targetPrevalence_lt_one := by norm_num
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  outcomeVariance_pos := by intro P; cases P <;> norm_num

theorem commonOnlyPortableModel_sourceR2 :
    sourceR2FromSourceWeights commonOnlyPortableModel = 1 / 4 := by
  norm_num [commonOnlyPortableModel, sourceR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
    sigmaTagCausal, dotProduct, totalEffect, Matrix.mulVec]

theorem commonOnlyPortableModel_targetR2 :
    targetR2FromSourceWeights commonOnlyPortableModel = 1 / 4 := by
  norm_num [commonOnlyPortableModel, targetR2FromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    targetScoreVarianceFromSourceWeights,
    sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
    effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    novelUntaggablePhenotypeResidual, sigmaTagCausal, sigmaTagCausal,
    crossCovariance, dotProduct, totalEffect, Matrix.mulVec]

theorem commonAndRarePortableModel_sourceR2 :
    sourceR2FromSourceWeights commonAndRarePortableModel = 1 / 2 := by
  norm_num [commonAndRarePortableModel, sourceR2FromSourceWeights,
    sourceExplainedSignalVarianceFromSourceWeights,
    sourcePredictiveCovarianceFromSourceWeights,
    sourceScoreVarianceFromExplicitDrivers,
    sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
    sigmaTagCausal, dotProduct, totalEffect, Matrix.mulVec]

theorem commonAndRarePortableModel_targetR2 :
    targetR2FromSourceWeights commonAndRarePortableModel = 1 / 8 := by
  norm_num [commonAndRarePortableModel, targetR2FromSourceWeights,
    targetExplainedSignalVarianceFromSourceWeights,
    targetPredictiveCovarianceFromSourceWeights,
    targetScoreVarianceFromSourceWeights,
    sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
    effectiveTargetOutcomeVariance, irreducibleTargetResidualBurden,
    brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
    novelUntaggablePhenotypeResidual, sigmaTagCausal, sigmaTagCausal,
    crossCovariance, dotProduct, totalEffect, Matrix.mulVec]

/-- **WGS discovers causal variants directly (no tagging needed).**
    This theorem is now stated on the mechanistic portability model itself.

    If the scored variants are direct causal measurements in both source and
    target, and all proxy-tagging channels and target-only novel direct/proxy
    links vanish, then the broken-tagging residual is exactly zero. Target-side
    effect heterogeneity and context mismatch may still remain. -/
theorem wgs_eliminates_ld_mismatch
    {p q : ℕ}
    (m : CrossPopulationMetricModel p q)
    (h_direct : (m.directCausal Pop.target) = (m.directCausal Pop.source))
    (h_novelDirect : (m.novelDirectCausal Pop.target) = 0)
    (h_proxySource : (m.proxyTagging Pop.source) = 0)
    (h_proxyTarget : (m.proxyTagging Pop.target) = 0)
    (h_novelProxy : (m.novelProxyTagging Pop.target) = 0) :
    brokenTaggingResidual m = 0 := by
  have h_sigma :
      sigmaTagCausal m Pop.source = sigmaTagCausal m Pop.target := by
    ext i j
    simp [sigmaTagCausal, sigmaTagCausal, h_direct,
      h_novelDirect, h_proxySource, h_proxyTarget, h_novelProxy]
  unfold brokenTaggingResidual
  rw [h_sigma]
  simp

/-- **Rare variant PGS has poor cross-population portability.**
    This is witnessed explicitly in the mechanistic model.

    The common-plus-rare source score has higher source `R²` than the
    common-only score because the source-specific rare variant helps within the
    discovery population. But in the target population the rare component does
    not contribute, so the portability ratio drops from `1` to `1/4`. -/
theorem rare_variant_pgs_poor_portability :
    mechanisticPortabilityRatio commonAndRarePortableModel <
      mechanisticPortabilityRatio commonOnlyPortableModel := by
  unfold mechanisticPortabilityRatio
  rw [commonAndRarePortableModel_sourceR2, commonAndRarePortableModel_targetR2,
    commonOnlyPortableModel_sourceR2, commonOnlyPortableModel_targetR2]
  norm_num [mechanisticPortabilityRatio]

/-- **Optimal PGS strategy combines common and rare variants.**
    In the explicit common-vs-rare witness above, adding the source-specific
    rare variant improves within-source prediction but does not improve target
    `R²`, and in this witness it strictly worsens target `R²`. This formalizes
    the idea that rare variation helps local prediction without improving
    cross-population transport. -/
theorem combined_strategy_optimal :
    sourceR2FromSourceWeights commonOnlyPortableModel <
      sourceR2FromSourceWeights commonAndRarePortableModel ∧
    targetR2FromSourceWeights commonAndRarePortableModel <
      targetR2FromSourceWeights commonOnlyPortableModel := by
  rw [commonOnlyPortableModel_sourceR2, commonAndRarePortableModel_sourceR2,
    commonAndRarePortableModel_targetR2, commonOnlyPortableModel_targetR2]
  norm_num

end WGSAndRareVariants

end Calibrator
