/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BayesianPGSTheory
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Descent.Portability.MechanisticPortabilityWitnesses
import Descent.Portability.AncestrySpecificPower
import Descent.PopGen.HaplotypeTheory
import Descent.Core.Ratios

namespace Descent

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat the winner's curse, ascertainment bias or shrinkage estimation.
Sources for individual results, where they exist, are cited at those results.
-/


/-!
## GWAS Discovery and Population Specificity

GWAS discovers associations that are specific to the population's
LD structure and allele frequency spectrum.
-/

section GWASDiscovery

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
    three significant figures across mismatched tag and causal frequencies).

    Power: the design is the frequency mismatch itself. Read against the tag's
    frequency instead of the causal one, the predicted NCP is a factor of
    `0.76` to `1.33` of this form across that design, and exactly `1.00` where
    the two frequencies coincide, so a grid at matched frequencies would have
    had no power and this one does. -/
def discoveryNCP (n β maf_causal ld : ℝ) : ℝ :=
  n * β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf_causal

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem discoveryNCP_at_reference_point :
    discoveryNCP 1 1 (1 / 2) 1 = 1 / 2 := by
  norm_num [discoveryNCP, genotypeVarianceHWE]


/-- A locus is discovered when its test statistic crosses the genome-wide
    `z`-threshold. In the one-degree-of-freedom Gaussian approximation this is
    equivalent to `z^2 ≤ discoveryNCP`.

    Empirical status: **VALIDATED** as the FIFTY-PERCENT POWER CONTOUR, and that
    is the only reading of it that survives measurement
    (`validation/empirical/simcov/battery_dgpcov.py`, group A;
    `battery_dgpcov3.py`, group A2). 20000 replicate GWASes per cell, genotypes
    drawn and OLS actually run, `maf` REMEASURED from the draws:

      n      β     this def's λ   measured λ         sems   power at z²=λ
      2000   0.02   0.336          0.322±0.013        1.1    0.6221±0.0035
      2000   0.05   2.100          2.102±0.023        0.1    0.5032±0.0035
      4000   0.08  10.752         10.794±0.048        0.9    0.5022±0.0035
      8000   0.12  48.379         48.269±0.099        1.1    0.4981±0.0035

    Two things are measured. First the threshold: `discoveryNCP` is the realized
    noncentrality across a 144-fold span, and the halved-ploidy competitor
    `n β² ld² p(1-p)` is refuted at 12 to 244 sems on the same cells. Second, and
    this is what the predicate itself adds, WHAT CROSSING IT MEANS. The body is
    deterministic, so it reads as though discovery follows; the measured
    discovery probability at the boundary is 0.50, matching the exact
    `ncx2.sf(λ, 1, λ)` at 0.5019, 0.5000 and 0.5000. A locus satisfying this
    predicate is discovered about half the time, not certainly, and the
    certainty reading is refuted at more than a hundred sems.

    The exception is small λ: at λ = 0.336 the boundary marks 0.62 power rather
    than 0.50, because `ncx2.sf(λ, 1, λ)` tends to 0.5 only as λ grows. The
    contour reading is exact from λ ≈ 2 upward and optimistic below it.

    Convention: `maf_causal` is the causal variant's frequency, matching
    `discoveryNCP`, which this predicate thresholds. -/
def gwasDiscovered (n β maf_causal ld z : ℝ) : Prop :=
  z ^ 2 ≤ discoveryNCP n β maf_causal ld

/-! ### Metamorphic relations the noncentrality parameter must satisfy

These are transformations of the INPUT whose effect on the output is known exactly,
so a body that fails one is defective whatever convention it claims. They are stated
here because `discoveryNCP` is the corpus's power currency and every one of them is a
statement about the arithmetic rather than about a simulated number: no measurement can
excuse a failure and none is needed to establish a pass. -/

/-- **Reference/alternate allele swap leaves discovery power alone.** Relabelling the
alleles at a variant sends `β ↦ -β` and `maf ↦ 1 - maf` TOGETHER -- never one without
the other -- and the noncentrality parameter is even in the first and, through
`genotypeVarianceHWE`, even about one half in the second. Discovery power is a property
of the variant, and which allele the assembly happens to call reference is not. -/
theorem discoveryNCP_allele_swap (n β maf ld : ℝ) :
    discoveryNCP n (-β) (1 - maf) ld = discoveryNCP n β maf ld := by
  unfold discoveryNCP genotypeVarianceHWE
  ring

/-- **Rescaling every effect size by `c` scales the noncentrality parameter by `c²`.**
This is the relation that fixes the exponent on `β`: a body linear in `β` would scale
by `c`, and only the quadratic one scales by `c²`. It is also what makes the trait's
unit of measurement drop out of any power calculation that divides by a variance in the
same unit. -/
theorem discoveryNCP_scale_effect (n β maf ld c : ℝ) :
    discoveryNCP n (c * β) maf ld = c ^ 2 * discoveryNCP n β maf ld := by
  unfold discoveryNCP
  ring

/-- **Rescaling the tagging correlation by `c` scales the noncentrality parameter by
`c²`.** The same quadratic exponent on the LD term, which is what makes the power loss
from imperfect tagging `r²` rather than `r`. -/
theorem discoveryNCP_scale_ld (n β maf ld c : ℝ) :
    discoveryNCP n β maf (c * ld) = c ^ 2 * discoveryNCP n β maf ld := by
  unfold discoveryNCP
  ring

/-- **Doubling the sample doubles the noncentrality parameter.** Linear, not quadratic:
the `√n` in the standard error becomes `n` in the squared statistic. Stated as a scaling
so it constrains the exponent, which the monotonicity result below does not. -/
theorem discoveryNCP_scale_n (n β maf ld c : ℝ) :
    discoveryNCP (c * n) β maf ld = c * discoveryNCP n β maf ld := by
  unfold discoveryNCP
  ring

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
    (h_order : maf₂ < maf₁)
    (h_maf₁_half : maf₁ ≤ 1 / 2) :
    genotypeVarianceHWE maf₂ < genotypeVarianceHWE maf₁ := by
  -- The shape fact -- `2 p (1 - p)` rises with `p` below the turning point -- is
  -- `two_mul_one_sub_strictMono_le_half` in `Descent.Foundations.Probability`, where it is about a
  -- real number rather than about a minor allele.  This theorem is that fact read through
  -- the name the genotype variance carries here.
  unfold genotypeVarianceHWE
  exact two_mul_one_sub_strictMono_le_half maf₂ maf₁ h_order h_maf₁_half

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
      maf₁ maf₂ h_maf_order h_maf₁_half
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem taggedScoreEstimationRisk_at_reference_point :
    taggedScoreEstimationRisk ![1, 3] ![1, 3] = 10 := by
  norm_num [taggedScoreEstimationRisk, Fin.sum_univ_two]


/-- C+T-to-dense-model gap measured as target causal signal mass missed by the
current discovered set. When discovery at larger sample size recovers more
causal loci, this gap shrinks. -/
noncomputable def ctMissedTargetSignal {m : ℕ}
    (discovered : Finset (Fin m)) (targetCausalSignal : Fin m → ℝ) : ℝ :=
  Finset.sum (Finset.univ \ discovered) fun i ↦ targetCausalSignal i

/-- **C+T uses fewer variants → more variable portability estimates.**
    This is stated on an explicit per-locus estimation-risk surface rather than
    on a `σ² / k` surrogate.

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
        (fun i ↦ jamesSteinMSE
          (optimalShrinkage (σSq i) (βSq i)) (σSq i) (βSq i)) <
      taggedScoreEstimationRisk targetTagVariance
        (fun i ↦ jamesSteinMSE 1 (σSq i) (βSq i)) := by
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

/-- **A positive multiplier preserves the sign of both factors:** from
    `b < a < 2b` and `x > 0`, `(a - b)x > 0` and `(a - 2b)x < 0`.

    **Both signs are hypotheses.** `h_signal_wins_source` is `b < a` and
    `h_noise_wins_target` is `a < 2b`; the conclusion multiplies each by a
    positive `x`. The reading — that a lenient p-value threshold gains
    `R²` in the source and loses it in the target because the LD-noise
    component doubles — supplies the factor `2` and the additive net-gain form
    by stipulation, and nothing here derives either.

    Note also what the name promised and the statement does not deliver: this
    is not an existence result. There is no `∃`, so the regime in which the two
    sign conditions hold together is assumed rather than exhibited. -/
theorem mul_pos_and_mul_neg_of_between
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

    Empirical status: NOT AN EMPIRICAL CLAIM. The second argument is DEFINED by
    this equation and by nothing else in the corpus: no declaration computes a
    mean estimation error from a design, so `meanEstimationError` is whatever
    makes the sum come out, and every estimator on every population satisfies
    the identity at `ε̄ = E[β̂] - β`. There is no assignment of the two arguments
    that a measurement could reject. The claims a reader might expect here --
    that OLS is unbiased, or that winner's curse makes `ε̄` positive at
    discovered loci -- are claims about what `ε̄` IS, and they live at the
    definitions that produce a value for it, not at this decomposition. -/
noncomputable def expectedLinearEffectEstimate
    (β_true meanEstimationError : ℝ) : ℝ :=
  β_true + meanEstimationError

/-- **An unbiased estimator recovers the truth.** With zero mean estimation error the expected
estimate is the true effect, which is what makes the second argument a bias rather than a
variance. -/
theorem expectedLinearEffectEstimate_unbiased (β_true : ℝ) :
    expectedLinearEffectEstimate β_true 0 = β_true := by
  unfold expectedLinearEffectEstimate; ring

/-- One-locus OLS effect-estimation variance under genotype variance `varX` and
sample size `n`.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk3.py`,
    `test_ols_variance`). Against the observed scatter of a single-SNP
    regression coefficient over 4000 replicate studies:

      n      sigma2   p      this def   simulated            sems
      2000   1.0      0.3     0.00119   0.00116±0.00003      1.16
      8000   1.0      0.3     0.00030   0.00030±0.00001      0.70
      2000   4.0      0.1     0.01111   0.01101±0.00025      0.43

    The oracle is the scatter the regression actually produces, not a formula,
    so this is not a generative self-test. `n`, `sigma2` and `p` each move
    separately, so the dependence on each is tested rather than one combination.

    Power: the prediction spans 0.00030 to 0.01111, a factor of thirty-seven. -/
noncomputable def olsEffectEstimationVariance
    (σ2 varX n : ℝ) : ℝ :=
  σ2 / (n * varX)

/-- **olsEffectEstimationVariance at zero varX, named.** With no variance in the regressor the
effect is unidentified and its sampling variance is infinite. Lean returns `0` -- a perfectly
precise estimate of a quantity that cannot be estimated at all, which downstream reads as an
infinitely confident effect. Consumers must require `varX ≠ 0`. -/
theorem olsEffectEstimationVariance_zero_varx_is_junk (σ2 : ℝ) (n : ℝ) :
    olsEffectEstimationVariance σ2 0 n = 0 := by
  unfold olsEffectEstimationVariance
  simp

/-- **Cross-check: the corrected haplotype estimation variance is the one-locus OLS
variance at the binary-indicator genotype variance.** `HaplotypeTheory` divides by
`n × f × (1-f)`; this divides by `n × varX` with `varX` a genotype variance, and for a
binary haplotype indicator of frequency `f` that variance IS `f(1-f)`. Supplying it
explicitly is what makes the two sides the same statement rather than two symbols that
happen to sit in the same slot.

The two definitions still list `n` and the scale factor in opposite positions, so the
argument order is load-bearing and this theorem pins it. -/
theorem olsEffectEstimationVariance_eq_haplotypeEffectVarianceOLS
    (σ2 freq n : ℝ) :
    olsEffectEstimationVariance σ2 (freq * (1 - freq)) n =
      haplotypeEffectVarianceOLS σ2 n freq := by
  unfold olsEffectEstimationVariance haplotypeEffectVarianceOLS; ring

/-! **Do not supply a haplotype FREQUENCY to `olsEffectEstimationVariance σ2 varX n` where a
genotype VARIANCE belongs.** `HaplotypeTheory` once carried a
`haplotypeEffectEstimationVariance σ2 n freq = σ2 / (n · freq)` that made the substitution
look legitimate: the equation `olsEffectEstimationVariance σ2 varX n = σ2 / (n · varX)` is
true as arithmetic, and false as a claim, because it is reached only by that swap. For a
binary indicator of frequency `f` the variance is `f(1-f)`, not `f`, and that missing `(1-f)`
was measured at −50.4% at `f = 1/2`, worst for COMMON haplotypes, the opposite of the rarity
intuition the surrounding prose appeals to. This note stands so the pairing is not
re-derived.

The theorem above is the correct pairing: `haplotypeEffectVarianceOLS`, the VALIDATED
form, with the variance supplied explicitly as `freq * (1 - freq)` — which is what makes
the substitution legitimate rather than two symbols sharing a slot.
`olsEffectEstimationVariance` is correct as it stands and needs no change. -/

/-- The set of loci retained by a hard-threshold sparse estimator such as
LASSO, modeled here by the loci whose marginal effect magnitude clears the
selection threshold `lam`. -/
noncomputable def lassoActiveLoci {m : ℕ}
    (β : Fin m → ℝ) (lam : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ lam ≤ |β i|

/-- Equal-contribution per-locus signal in a trait with total heritability `h2`
spread over `k` causal loci. -/
noncomputable def perCausalLocusSignal
    (h2 k : ℝ) : ℝ :=
  Descent.Core.ratio h2 k

/-- **perCausalLocusSignal at zero k, named.** With no causal loci the heritability has nowhere to
sit and the per-locus signal diverges. Lean returns `0`, an infinitely polygenic architecture,
which is the opposite architecture to the one the argument describes. Consumers must require
`k ≠ 0`. -/
theorem perCausalLocusSignal_zero_k_is_junk (h2 : ℝ) :
    perCausalLocusSignal h2 0 = 0 := by
  unfold perCausalLocusSignal Descent.Core.ratio
  simp

/-- **The loci partition the heritability.** -/
theorem perCausalLocusSignal_mul_count (h2 k : ℝ) (hk : k ≠ 0) :
    perCausalLocusSignal h2 k * k = h2 := by
  unfold perCausalLocusSignal Descent.Core.ratio
  field_simp

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
    unfold perCausalLocusSignal Descent.Core.ratio
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

/-- **The genetic correlation against a trait with no genetic variance, named.** With `vg₁ = 0`
there is no genetic component to correlate with and the quantity is undefined. The square root is
zero, the divisor is zero, and Lean returns `0` -- reporting two traits with no shared genetic
basis, which is exactly the substantive conclusion someone runs this to test. The same junk value
arises from a NEGATIVE variance estimate, which REML returns routinely, so the branch is reachable
from real output. Consumers must require `0 < vg₁ * vg₂`. -/
theorem geneticCorrelation_no_genetic_variance_is_junk (cov_g vg₂ : ℝ) :
    geneticCorrelation cov_g 0 vg₂ = 0 := by
  unfold geneticCorrelation
  simp

/-- Effective discovery-sample size for trait A after borrowing information
from a genetically correlated trait B.

    Empirical status: **VALIDATED**, through
`BayesianPGSTheory.multiAncestryEffectiveN`, which is the same formula and carries the
measurement (`simcov/battery_bulk40b.py`, `group_f`). The FALSIFIED marker this line used
to carry described the SUPERSEDED body `n₁ + rg²·n₂` and was left behind when the
correction landed, so the definition read as falsified while the body it named no longer
existed -- a stale mark rather than a wrong body. The falsification is retained below as
history.

Power: the measured `N_eff` spans `6449` to `12079` across the design, a factor of 1.9,
and the competitors `n_t + rg·n_o`, `n_t + n_o` and `n_t` alone are refuted at 227, 282
and 261 sems on the same cells.

The measurement in detail: the exact contributed precision is
`n₁ + rg²/((1-rg²)·τ² + 1/n₂)` with `τ²` the effect prior variance, and this body is its
`n₂·τ² ≪ 1` limit. The error grows monotonically with `n₂·τ²` -- 2.3% at 0.18, 5.0% at 0.36,
31% at 3.60.

The MATCH previously recorded from `simcov/battery_bulk23.py` is worthless: that design set
the other trait's effect to EXACTLY `rg` times the target's, with no scatter, under which the
old body was an algebraic identity for the inverse-variance combination and no data could
have rejected it. Genetic correlation below one MEANS scatter; a design without it is testing
a different claim.

CORRECTED. The body is the exact contributed precision; `n₁ + rg²·n₂` is its
`n₂ · priorVariance → 0` limit and is recovered by `multiTraitEffectiveSampleSize_smallPrior`
below. -/
noncomputable def multiTraitEffectiveSampleSize
    (n₁ n₂ rg priorVariance : ℝ) : ℝ :=
  n₁ + rg ^ 2 / ((1 - rg ^ 2) * priorVariance + 1 / n₂)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem multiTraitEffectiveSampleSize_at_reference_point :
    multiTraitEffectiveSampleSize 1 1 1 0 = 2 := by
  norm_num [multiTraitEffectiveSampleSize]

/-- **The old body is this one's vanishing-prior limit**, as for
`BayesianPGSTheory.multiAncestryEffectiveN`.  Stating it keeps the previous form available to
a caller who knows they are in the polygenic regime `n₂ · priorVariance ≪ 1`, and keeps the
correction auditable rather than silent. -/
theorem multiTraitEffectiveSampleSize_smallPrior
    (n₁ n₂ rg : ℝ) (h_n₂ : n₂ ≠ 0) :
    multiTraitEffectiveSampleSize n₁ n₂ rg 0 = n₁ + rg ^ 2 * n₂ := by
  unfold multiTraitEffectiveSampleSize
  field_simp
  ring


/-- **Cross-check: borrowing across traits and borrowing across ancestries are
the same arithmetic, unrestrictedly.**
`BayesianPGSTheory.multiAncestryEffectiveN` contributes precision to the target
sample size from a genetically correlated *ancestry*; this contributes it from a
genetically correlated *trait*. They are different claims about different data,
and they had better not drift apart in the exponent on `rg` or in the prior
term, which is what this theorem pins.

**Why unrestricted, and why it briefly was not.** The prior-variance correction
was derived for the ancestry case and `BayesianPGSTheory` says so in as many
words: `multiTraitEffectiveSampleSize` "is the SAME formula and inherits this".
Both bodies now carry it, so the equality holds everywhere and needs no
hypothesis. It was restated at `priorVariance = 0` during the window in which
only one of the two had been corrected -- true then, and the honest statement
then, but a restriction that now hides the very agreement it was written to
record. Two concurrent repairs of one arity mismatch took opposite routes; this
is the merge, and (a) is the right one because the correction is a property of
inverse-variance borrowing and not of what is being borrowed from.

The two bodies are now the same expression up to the name and ORDER of their
arguments -- ancestry takes `(n_target, rg, n_other, priorVariance)`, trait takes
`(n₁, n₂, rg, priorVariance)` -- which is why this is proved rather than
asserted, and why it is worth keeping both names. Identical arithmetic is not
identical meaning; `hweHeterozygosity` and `genotypeVarianceHWE` are the same
`2p(1-p)` and are a heterozygosity and a dosage variance. What an equality
theorem buys over a single shared definition is that the two can be MEASURED
separately -- and they have been, against different designs -- while this
theorem is what catches them drifting apart. -/
theorem multiTraitEffectiveSampleSize_eq_multiAncestryEffectiveN
    (n₁ n₂ rg priorVariance : ℝ) :
    multiTraitEffectiveSampleSize n₁ n₂ rg priorVariance =
      multiAncestryEffectiveN n₁ rg n₂ priorVariance := by
  simp only [multiTraitEffectiveSampleSize, multiAncestryEffectiveN]

/-- GWAS noncentrality parameter after cross-trait borrowing.

    Empirical status: **VALIDATED**, and the composition needed a convention to
    be pinned before it could be
    (`validation/empirical/simcov/battery_dgpcov4.py`, group C3). It
    carried no marker of its own while it sat next to
    `multiTraitEffectiveSampleSize`, whose marker it was reading; both parts
    being measured does not measure the composition, because the two are
    expressed on different scales and only agree on one reading of
    `priorVariance`.

    The design: 8000 replicate cohort PAIRS per cell, genotypes drawn and OLS
    run in both, the borrowed estimate formed by inverse-variance combination of
    `β̂₁` with `β̂₂/rg` -- a rule fixed before any formula is evaluated, since
    `β̂₂` is an unbiased reading of `rg β₁` with variance `(1-rg²)τ² + v₂`. `β₁`
    is HELD FIXED so the statistic is a frequentist noncentrality and prior
    shrinkage is not credited as information. `maf` is swept from 0.5 to 0.1 at
    FIXED `n·2p(1-p)`, so the realized noncentrality is invariant along the
    sweep by construction and only a scale error can move with `maf`:

      p     τ²_std   measured λ      this body   sems   dosage-scale reading
      0.50  2.0e-4   7.6213±0.0631    7.7038      1.3    6.8667  (12.0 sems)
      0.30  2.0e-4   9.9827±0.0731    9.9102      1.0    8.6216  (18.6 sems)
      0.10  2.0e-4   6.5632±0.0595    6.4974      1.1    5.3583  (20.3 sems)
      0.30  2.0e-5  13.0418±0.0813   13.0376      0.1   12.1810  (10.6 sems)
      0.10  2.0e-5   9.0315±0.0686    8.9967      0.5    7.1705  (27.1 sems)

    Competitors on the same cells: `n₁` alone is refuted at 26 to 74 sems and
    the small-prior limit `n₁ + rg²n₂` at 10 to 56 sems, so the design has power
    to reject both the no-borrowing and the naive-borrowing forms.

    Convention: `maf_causal` is the causal variant's frequency, as in
    `discoveryNCP`. `priorVariance` is the prior variance of the STANDARDIZED
    effect `β √(2p(1-p))`, not of the dosage-scale `β` this definition's own `β`
    argument is on. That is forced, not chosen: `multiTraitEffectiveSampleSize`
    reads its `1/n` slots as sampling VARIANCES of an effect estimate, so its
    output is a precision on whatever scale its prior is; `discoveryNCP` takes a
    raw sample COUNT and supplies `genotypeVarianceHWE` itself. The two compose
    exactly when the prior is standardized-scale, and the dosage-scale reading
    understates the borrowed term by a factor of `2p(1-p)` -- the column above,
    off by 10 to 27 sems and growing as `maf` falls. Supplying the wrong one is
    a silent 10 to 30 percent power error, not a type error. -/
noncomputable def multiTraitDiscoveryNCP
    (n₁ n₂ rg priorVariance β maf ld : ℝ) : ℝ :=
  discoveryNCP (multiTraitEffectiveSampleSize n₁ n₂ rg priorVariance) β maf ld

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem multiTraitDiscoveryNCP_at_reference_point :
    multiTraitDiscoveryNCP 1 1 0 1 1 (1 / 2) 1 = 1 / 2 := by
  norm_num [multiTraitDiscoveryNCP, discoveryNCP, genotypeVarianceHWE,
    multiTraitEffectiveSampleSize]


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

/-- **The unshared-architecture model**: no tag-causal coupling at all, with every
other field left free.

`CrossTraitBorrowingModel` had no exhibited inhabitant, so the borrowing results
were quantified over a class nothing had been shown to belong to. This is the
null member -- the case where trait A's architecture reaches trait B through
nothing -- and it is the reference the borrowed component is measured against:
whatever `rg` is set to, no signal transfers without shared architecture to carry
it. -/
def noSharedArchitecture {p q : ℕ} (sourceWeights : Fin p → ℝ)
    (sharedTraitEffect traitBSpecificEffect : Fin q → ℝ) (rg : ℝ) :
    CrossTraitBorrowingModel p q where
  sourceWeights := sourceWeights
  sigmaTagCausal := 0
  sharedTraitEffect := sharedTraitEffect
  traitBSpecificEffect := traitBSpecificEffect
  rg := rg

instance instNonempty (p q : ℕ) : Nonempty (CrossTraitBorrowingModel p q) :=
  ⟨noSharedArchitecture (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) 0⟩

/-- Trait-B cross-covariance component borrowed from trait A through shared
genetic architecture. -/
noncomputable def borrowedTraitBCrossCov {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : Fin p → ℝ :=
  m.sigmaTagCausal.mulVec (fun j ↦ m.rg * m.sharedTraitEffect j)

/-- **Genetic correlation alone borrows nothing.** With no shared tag-causal
architecture the borrowed component vanishes at every `rg`, so `rg` is a
modifier of a transfer channel rather than a transfer channel itself. A
cross-trait method that reads `rg` without also establishing shared architecture
is reading a coefficient on zero. -/
theorem borrowedTraitBCrossCov_noSharedArchitecture {p q : ℕ}
    (sourceWeights : Fin p → ℝ) (sharedTraitEffect traitBSpecificEffect : Fin q → ℝ)
    (rg : ℝ) :
    borrowedTraitBCrossCov
        (noSharedArchitecture sourceWeights sharedTraitEffect traitBSpecificEffect rg) =
      0 := by
  unfold borrowedTraitBCrossCov noSharedArchitecture
  simp

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

/-- **A zero score projects nothing, which is a fact about `dotProduct`.**

Not a reference evaluation, and it was named as one until the collapse was
looked at: `borrowedTraitBProjection m = m.sourceWeights ⬝ᵥ borrowedTraitBCrossCov m`,
so at `sourceWeights = 0` the second argument is never evaluated. The statement
holds for EVERY function in that slot -- a transposed `sigmaTagCausal`, an
`rg` dropped or applied twice, the trait-B-specific effect substituted for the
shared one -- because none of them is consulted. It pins nothing about the
borrowing model and cannot fail unless `dotProduct` itself changes.

Renamed rather than deleted: a zero score projecting nothing is worth
recording, and the point of recording it is lost if it keeps a name that
claims it evaluates the model at a reference. The evaluation that does pin the
functional form is `borrowedTraitBProjection_at_witness` below. -/
theorem borrowedTraitBProjection_zero_weights {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) (hzero : m.sourceWeights = 0) :
    borrowedTraitBProjection m = 0 := by
  unfold borrowedTraitBProjection
  rw [hzero]
  simp


/-- Total trait-B projection captured by the source-trained score. -/
noncomputable def totalTraitBProjection {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) : ℝ :=
  dotProduct m.sourceWeights (totalTraitBCrossCov m)

/-- The same fact about `dotProduct` for the total projection, and the same
non-claim: at `sourceWeights = 0` neither the borrowed nor the specific
component is evaluated, so this holds for any pair of them. See
`totalTraitBProjection_at_witness` for the evaluation that pins the form. -/
theorem totalTraitBProjection_zero_weights {p q : ℕ}
    (m : CrossTraitBorrowingModel p q) (hzero : m.sourceWeights = 0) :
    totalTraitBProjection m = 0 := by
  unfold totalTraitBProjection
  rw [hzero]
  simp


/-- **A witness chosen so that a wrong functional form gives a wrong number.**

The zero-weight statements above are satisfied by any borrowing model at all.
This one is not. Its fields are picked so that each way the cross-covariance
could plausibly be miswritten moves the answer:

  * `rg = 1/2`, neither `0` nor `1`, so an `rg` that is dropped is visible
    (the borrowed projection would read `1` instead of `1/2`);
  * `sigmaTagCausal` is NOT symmetric, so a transposed `mulVec` is visible
    (it would read `5/2`);
  * `sharedTraitEffect` and `traitBSpecificEffect` have disjoint support, so
    substituting one for the other is visible (it would read `4`);
  * the two projections are pinned together, so `rg` wrongly applied to the
    specific component as well is visible in the total (`9/2` against `17/2`)
    even though the borrowed component alone would not move.

Pinning both values also pins the scale: a body wrong by a common factor `c`
would have to satisfy `c/2 = 1/2` and `17c/2 = 17/2` at once. That is the
weakest of the discriminations here and is listed last on purpose -- a witness
that only rejects a scale factor is a witness that has not been designed. -/
noncomputable def borrowingWitness : CrossTraitBorrowingModel 2 2 where
  sourceWeights := ![1, 2]
  sigmaTagCausal := !![1, 2; 0, 3]
  sharedTraitEffect := ![1, 0]
  traitBSpecificEffect := ![0, 1]
  rg := 1 / 2

/-- **Reference evaluation of the borrowed projection.**
`Σ (rg · β_shared) = (1/2, 0)` and `w ⬝ᵥ (1/2, 0) = 1/2`. -/
theorem borrowedTraitBProjection_at_witness :
    borrowedTraitBProjection borrowingWitness = 1 / 2 := by
  norm_num [borrowedTraitBProjection, borrowedTraitBCrossCov, borrowingWitness,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two]

/-- **Reference evaluation of the total projection.**
The specific component contributes `Σ β_specific = (2, 3)`, so the total
cross-covariance is `(5/2, 3)` and `w ⬝ᵥ (5/2, 3) = 17/2`. The gap from
`1 / 2` is exactly the trait-B-specific channel, which is what makes the pair
of evaluations separate `rg` applied to the shared component alone from `rg`
applied to both. -/
theorem totalTraitBProjection_at_witness :
    totalTraitBProjection borrowingWitness = 17 / 2 := by
  norm_num [totalTraitBProjection, totalTraitBCrossCov, borrowedTraitBCrossCov,
    traitBSpecificCrossCov, borrowingWitness, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]


theorem traitBSpecificCrossCov_nonneg {p q : ℕ}
    (m : CrossTraitBorrowingModel p q)
    (h_sigma : ∀ i j, 0 ≤ m.sigmaTagCausal i j)
    (h_specific : ∀ j, 0 ≤ m.traitBSpecificEffect j) :
    0 ≤ traitBSpecificCrossCov m := by
  intro i
  unfold traitBSpecificCrossCov Matrix.mulVec
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (h_sigma i j) (h_specific j)

theorem borrowedTraitBCrossCov_nonneg {p q : ℕ}
    (m : CrossTraitBorrowingModel p q)
    (h_sigma : ∀ i j, 0 ≤ m.sigmaTagCausal i j)
    (h_shared : ∀ j, 0 ≤ m.sharedTraitEffect j)
    (h_rg : 0 ≤ m.rg) :
    0 ≤ borrowedTraitBCrossCov m := by
  intro i
  unfold borrowedTraitBCrossCov Matrix.mulVec
  exact Finset.sum_nonneg fun j _ ↦
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
    (n₁ n₂ rg priorVariance β maf ld : ℝ)
    (h_n₂ : 0 < n₂)
    (h_rg : 0 < rg) (h_rg_le : rg ≤ 1)
    (h_pv : 0 ≤ priorVariance)
    (h_beta : β ≠ 0)
    (h_maf : 0 < maf) (h_maf_lt_one : maf < 1)
    (h_ld : ld ≠ 0) :
    n₁ < multiTraitEffectiveSampleSize n₁ n₂ rg priorVariance ∧
      discoveryNCP n₁ β maf ld <
        multiTraitDiscoveryNCP n₁ n₂ rg priorVariance β maf ld := by
  have h_den : 0 < (1 - rg ^ 2) * priorVariance + 1 / n₂ := by
    have h1 : 0 ≤ (1 - rg ^ 2) * priorVariance :=
      mul_nonneg (by nlinarith) h_pv
    have h2 : 0 < 1 / n₂ := by positivity
    linarith
  have h_gain : 0 < rg ^ 2 / ((1 - rg ^ 2) * priorVariance + 1 / n₂) :=
    div_pos (by positivity) h_den
  have h_n : n₁ < multiTraitEffectiveSampleSize n₁ n₂ rg priorVariance := by
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
  · unfold multiTraitDiscoveryNCP discoveryNCP
    have h_ncp :
        n₁ * (β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf) <
          multiTraitEffectiveSampleSize n₁ n₂ rg priorVariance *
            (β ^ 2 * ld ^ 2 * genotypeVarianceHWE maf) :=
      mul_lt_mul_of_pos_right h_n h_factor
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
noncomputable def commonAndRarePortableModel : CrossPopulationMetricModel 2 2 :=
  -- Only the effect vector and the direct-causal covariance differ from the
  -- common-variant-only witness; the other fifteen fields were copied verbatim, so the
  -- two witnesses could drift apart in a field neither of them is about.  Stated as an
  -- override, the comparison the section makes is what the definition says.
  { commonOnlyPortableModel with
    beta := Pop.pair (![1, 1]) (![1, 0])
    directCausal := Pop.pair 1 1 }

/-- Evaluate a witness model's SOURCE `R²` by unfolding the source-weight chain.

The unfolding list is the same for every witness, and it was written out once per theorem:
four copies here, differing only in which model name led the list.  A copy that drifts is a
theorem that evaluates a different chain from its neighbour while reading identically. -/
local macro "source_r2_of " m:term : tactic =>
  `(tactic| norm_num [$m:term, r2FromSourceWeights,
      commonOnlyPortableModel,
      explainedSignalVarianceFromSourceWeights,
      predictiveCovarianceFromSourceWeights,
      scoreVarianceFromSourceWeights,
      sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
      sigmaTagCausal, dotProduct, totalEffect, Matrix.mulVec])

/-- Evaluate a witness model's TARGET `R²`.  The target chain carries the residual burden
terms the source chain has no need of, and is otherwise the same list. -/
local macro "target_r2_of " m:term : tactic =>
  `(tactic| norm_num [$m:term, r2FromSourceWeights,
      commonOnlyPortableModel,
      explainedSignalVarianceFromSourceWeights,
      predictiveCovarianceFromSourceWeights,
      scoreVarianceFromSourceWeights,
      sourceWeightsFromExplicitDrivers, sourceERMWeights, crossCovariance,
      effectiveOutcomeVariance, irreducibleTargetResidualBurden,
      brokenTaggingResidual, ancestrySpecificLDResidual, sourceSpecificOverfitResidual,
      novelUntaggablePhenotypeResidual, sigmaTagCausal,
      dotProduct, totalEffect, Matrix.mulVec])

theorem commonOnlyPortableModel_sourceR2 :
    r2FromSourceWeights commonOnlyPortableModel Pop.source = 1 / 4 := by
  source_r2_of commonOnlyPortableModel

theorem commonOnlyPortableModel_targetR2 :
    r2FromSourceWeights commonOnlyPortableModel Pop.target = 1 / 4 := by
  target_r2_of commonOnlyPortableModel

theorem commonAndRarePortableModel_sourceR2 :
    r2FromSourceWeights commonAndRarePortableModel Pop.source = 1 / 2 := by
  source_r2_of commonAndRarePortableModel

theorem commonAndRarePortableModel_targetR2 :
    r2FromSourceWeights commonAndRarePortableModel Pop.target = 1 / 8 := by
  target_r2_of commonAndRarePortableModel

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
      sigmaTagCausalSourceAt m Pop.source = sigmaTagCausalSourceAt m Pop.target := by
    ext i j
    simp [sigmaTagCausalSourceAt, h_direct, m.novelDirectCausal_source,
      m.novelProxyTagging_source, h_novelDirect, h_proxySource, h_proxyTarget,
      h_novelProxy]
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
    r2FromSourceWeights commonOnlyPortableModel Pop.source <
      r2FromSourceWeights commonAndRarePortableModel Pop.source ∧
    r2FromSourceWeights commonAndRarePortableModel Pop.target <
      r2FromSourceWeights commonOnlyPortableModel Pop.target := by
  rw [commonOnlyPortableModel_sourceR2, commonAndRarePortableModel_sourceR2,
    commonAndRarePortableModel_targetR2, commonOnlyPortableModel_targetR2]
  norm_num

end WGSAndRareVariants

end Descent
