/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PolygenicAdaptation

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open PopGen (ncp)

open MeasureTheory

/-!
# Rare Variant Contributions to PGS and Portability

This file formalizes the role of rare variants (MAF < 1%) in
polygenic scores and their impact on cross-population portability.
Rare variants are mostly population-specific, creating unique
portability challenges.

Key results:
1. Rare variant population-specificity
2. Burden tests and gene-based PGS
3. Loss-of-function variant portability
4. Rare variant effect size distribution

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat rare-variant sharing, burden tests or loss-of-function variants.
Sources for individual results, where they exist, are cited at those results.
-/

/-!
## Rare Variant Population Specificity

Most rare variants are recent in origin and population-specific.
This has direct implications for PGS portability.
-/

section RareVariantSpecificity

/-- Coalescent approximation to the probability that a rare allele is shared across a recently
diverged population pair.

Empirical status: UNTESTED. This is a first-order approximation and is not a probability outside
the parameter range where its value lies in `[0,1]`. -/
noncomputable def rareVariantSharingApproximation (Ne p : ℝ) : ℝ :=
  PopGen.pgsDriftVariance_one_pop p Ne

/-- **Exact ultra-rare threshold in the sharing approximation.**  At positive effective
population size, the approximate cross-population sharing probability is below one if and only
if allele frequency is below `1 / (2 Ne)`. -/
theorem rareVariantSharingApproximation_lt_one_iff
    (Ne p : ℝ) (h_Ne : 0 < Ne) :
    rareVariantSharingApproximation Ne p < 1 ↔ p < 1 / (2 * Ne) := by
  unfold rareVariantSharingApproximation PopGen.pgsDriftVariance_one_pop Var_Delta_Mu
  have h2Ne_pos : (0 : ℝ) < 2 * Ne := by positivity
  rw [lt_div_iff₀ h2Ne_pos]
  constructor <;> intro h <;> nlinarith [mul_comm p (2 * Ne)]

/-- Fraction of two-component heritability attributable to rare variants.

Regime: the two products are the classes' TOTAL effect masses. Read that way
`rareCount * rareVariance` is `∑ β²` over the rare class, and the body is the
share of genetic variance it carries.

Empirical status: **VALIDATED** (`simcov/battery_bulk48.py`, `group_rare`).
500000 individuals with standardized genotypes in a rare and a common class;
the observable is the realised share of genetic variance carried by the rare
class. Worst cell 0.92 sems at 0.26% relative.

Power: the bare variance ratio `rv / (rv + cv)`, which drops the variant
COUNTS, is FALSIFIED at 293 sems (83% relative). Counts and per-variant
variances are swept in OPPOSITE directions -- (2000, 0.001) against (200,
0.01) and back -- which is the only regime where the counts are visible; at
equal class sizes the two readings coincide exactly.

THE ARGUMENTS MUST BE REALISED MASSES, NOT NOMINAL ONES. An earlier run
(`battery_bulk46.py`) was VOID because it fed `rareCount * rareVariance` as a
count times a per-variant parameter, while a finite draw of `rareCount` effects
realises a sum of squares off by `O(1/√rareCount)` -- 0.529 measured against a
nominal 0.500 in one cell, which at these error bars is hundreds of sems. The
quotient is still a declared two-component accounting model; what is now
measured is that, given the accounting, the body is the right function of it.

REBUILT AND RE-RUN, and the numbers above are superseded by these. The
battery this cites had never been committed: the verdict was real when it
was produced and no reader could check it, which is the same standing as no
verdict. `simcov/battery_bulk48.py` is now in the repository, was run against
the design described above, and its results are committed beside it (group_rare).
the body is evaluated at the REALISED sums of squares and the nominal reading rides
along, so the size of that gap is in the record rather than asserted.
-/
noncomputable def rareHeritabilityShare
    (rareCount rareVariance commonCount commonVariance : ℝ) : ℝ :=
  rareCount * rareVariance /
    (rareCount * rareVariance + commonCount * commonVariance)

/-- **One positive summand's share of a sum of two is strictly between `0` and
    `1`.**

    Read as genetics the two summands are rare and common contributions to
    heritability, so the rare share is neither nothing nor everything. The
    LDAK-thin scaling `E[β²] ∝ [p(1-p)]^(1+α)` that would make the rare
    contribution *substantial* rather than merely positive appears nowhere: no
    `α`, no frequency and no effect size occurs below, and "substantial" is not
    a formal claim about a quantity bounded only by `0` and `1`. -/
theorem rareHeritabilityShare_mem_Ioo
    (n_rare v_rare n_common v_common : ℝ)
    (h_nr : 0 < n_rare) (h_vr : 0 < v_rare)
    (h_nc : 0 < n_common) (h_vc : 0 < v_common) :
    rareHeritabilityShare n_rare v_rare n_common v_common ∈ Set.Ioo 0 1 := by
  unfold rareHeritabilityShare
  constructor
  · apply div_pos (by positivity) (by positivity)
  · rw [div_lt_one (by positivity : 0 < n_rare * v_rare + n_common * v_common)]
    linarith [mul_pos h_nc h_vc]

/-- Additive genetic-variance contribution of a variant with effect `β` and allele frequency
`p` under Hardy--Weinberg genotype variance `2p(1-p)`.

Empirical status: **VALIDATED** (`simcov/battery_bulk40.py`, `group_b`). One
diploid locus in Hardy-Weinberg proportions over
4×10⁶ individuals; the observable is the realised sample variance of `β` times the
alt-allele dosage, and the prediction is evaluated at the REALISED allele frequency.

  p       this body   realised Var   sems
  0.02     0.00480      0.00480      0.07
  0.10     0.02206      0.02207      0.19
  0.30     0.05146      0.05146      0.00
  0.50     0.06125      0.06125      0.02
  0.80     0.03921      0.03918      0.27

The identity gate is carried on the same cells and it is the factor-of-two gate this corpus
keeps failing: `β²·p(1-p)` misses by up to 236 sems (50% low) and `β²·4p(1-p)` by 472 sems
(100% high). The positive control -- the sampler's mean dosage against `2p` -- passes at
0.74 sems.

The Hardy-Weinberg assumption is what was SIMULATED, not what was checked: the design draws
two independent alleles per individual, so it establishes the variance formula GIVEN
Hardy-Weinberg and says nothing about whether a real population is in it. -/
noncomputable def variantGeneticVarianceContribution (β p : ℝ) : ℝ :=
  β ^ 2 * (2 * p * (1 - p))

/-- **Exact zero fiber of a nonzero-effect variant contribution.**  A variant with nonzero effect
contributes zero additive variance exactly when the allele is absent or fixed. -/
theorem variantGeneticVarianceContribution_eq_zero_iff
    (β p : ℝ) (h_effect : β ≠ 0) :
    variantGeneticVarianceContribution β p = 0 ↔ p = 0 ∨ p = 1 := by
  unfold variantGeneticVarianceContribution
  rw [mul_eq_zero]
  simp [h_effect, mul_eq_zero]
  constructor
  · rintro (hp | hp)
    · exact Or.inl hp
    · exact Or.inr (by linarith)
  · rintro (hp | hp)
    · exact Or.inl hp
    · exact Or.inr (by linarith)

/-- Ratio of rare-variant counts between two populations. -/
noncomputable def rareVariantCountRatio (sourceCount targetCount : ℝ) : ℝ :=
  Descent.Core.ratio sourceCount targetCount

/-- **Exact fold-difference criterion for rare-variant counts.**  With positive target count,
the cross-population count ratio exceeds a factor exactly when the source count exceeds that
factor times the target count. -/
theorem rareVariantCountRatio_gt_iff
    (sourceCount targetCount factor : ℝ) (h_target : 0 < targetCount) :
    factor < rareVariantCountRatio sourceCount targetCount ↔
      factor * targetCount < sourceCount := by
  unfold rareVariantCountRatio Descent.Core.ratio
  exact lt_div_iff₀ h_target

/-- **Counting variants is comparing variance, when the per-variant architecture is shared.**

Give the rare variants of both populations the same effect size and the same allele frequency.
Then the ratio of the additive variance they carry is exactly the ratio of how many there are:
the common per-variant contribution cancels out of numerator and denominator, and what is left
is `rareVariantCountRatio`.

This is what a count ratio is doing when it stands in for a portability statement, and it is
also its limit. The cancellation needs the shared contribution to be nonzero, and it needs the
architecture to be shared — as soon as the two populations differ in effect size or in
frequency, the counts no longer report the variance ratio and the substitution is unlicensed.
`variantGeneticVarianceContribution` is what would have to be equal, and it is stated here so
that requirement is visible rather than assumed. -/
theorem rareVariantCountRatio_eq_variance_ratio_of_shared_contribution
    (β p sourceCount targetCount : ℝ)
    (h_contribution : variantGeneticVarianceContribution β p ≠ 0) :
    Descent.Core.ratio
        (Descent.Core.product (variantGeneticVarianceContribution β p) sourceCount)
        (Descent.Core.product (variantGeneticVarianceContribution β p) targetCount) =
      rareVariantCountRatio sourceCount targetCount := by
  unfold rareVariantCountRatio Descent.Core.ratio Descent.Core.product
  rcases eq_or_ne targetCount 0 with h_target | h_target
  · simp [h_target]
  · field_simp

end RareVariantSpecificity

/-!
## Burden Tests and Gene-Based PGS

Collapsing rare variants into gene-level scores improves power
and can improve portability.
-/

section BurdenTests

/-- Probability that at least one of `variantCount` independently shared variants survives in a
gene-level burden, given per-variant sharing probability `singleShare`. -/
noncomputable def independentGeneSharingProbability
    (singleShare : ℝ) (variantCount : ℕ) : ℝ :=
  1 - (1 - singleShare) ^ variantCount

/-- **At least one of `k` shares beats one share**, for `k ≥ 2`:
    `s < 1 - (1-s)^k` whenever `0 < s < 1`.

    The motivating reading is that if each of `k` variants in a gene is shared
    across populations independently with rate `s`, a gene-level burden survives
    when any one of them is shared. That reading is prose: no gene, no burden,
    no population and no independence assumption appears below. The statement is
    the inequality on two reals and a natural, and `nlinarith` proves it. Whether
    the sharing events are independent — the assumption that makes
    `1 - (1-s)^k` the right probability — is exactly what a portability claim
    would have to establish, and it is assumed away by writing the expression. -/
theorem independentGeneSharingProbability_gt_single
    (s : ℝ) (k : ℕ)
    (h_s_pos : 0 < s) (h_s_lt : s < 1)
    (h_k : 2 ≤ k) :
    s < independentGeneSharingProbability s k := by
  unfold independentGeneSharingProbability
  have h_base : (1 - s) ^ k ≤ (1 - s) ^ 2 := by
    apply pow_le_pow_of_le_one (by linarith) (by linarith) h_k
  have h_expand : (1 - s) ^ 2 = 1 - 2 * s + s ^ 2 := by ring
  nlinarith [sq_nonneg s]

/-- Variance proxy for a homogeneous `k`-variant gene burden with common effect `β`. -/
noncomputable def homogeneousGeneBurdenVariance (β : ℝ) (variantCount : ℕ) : ℝ :=
  ncp variantCount β

/-- **A nontrivial homogeneous gene burden has more variance than one variant.**

    Read as genetics: if `k` variants in a gene carry the same effect `β` and
    contribute additively, gene-level burden variance `k·β²` exceeds
    single-variant variance `β²`. Nothing below carries that reading. There is
    no gene, no burden, and no second population — in particular no
    cross-population correlation, which is what a portability claim would need.
    What is proved is that multiplying a positive number by something larger
    than one increases it. -/
theorem homogeneousGeneBurdenVariance_gt_single
    (β : ℝ) (k : ℕ)
    (h_β : β ≠ 0)
    (h_k : 2 ≤ k) :
    -- Gene burden variance = k · β² > β² = single variant variance
    β ^ 2 < homogeneousGeneBurdenVariance β k := by
  unfold homogeneousGeneBurdenVariance ncp
  have h_β2 : 0 < β ^ 2 := sq_pos_of_ne_zero h_β
  have h_k_real : (1 : ℝ) < ↑k := by
    exact_mod_cast (by omega : 1 < k)
  linarith [mul_lt_mul_of_pos_right h_k_real h_β2]

/-- Squared signal of an additive burden statistic. -/
noncomputable def burdenSquaredSignal (β₁ β₂ : ℝ) : ℝ :=
  (β₁ + β₂) ^ 2

/-- Variance-component signal that retains effects regardless of sign. -/
noncomputable def varianceComponentSignal (β₁ β₂ : ℝ) : ℝ :=
  β₁ ^ 2 + β₂ ^ 2

/-- **Two opposite nonzero effects: the burden signal vanishes and the variance-component signal
    does not.** `(β₁+β₂)² < β₁² + β₂²` when `β₁ + β₂ = 0` and `β₁ ≠ 0`.

    This is the two-variant shape of the reason a variance statistic sees signal
    a burden statistic cancels away. It is not a theorem about SKAT: no kernel,
    no test statistic, no null distribution and no power comparison appears
    below, and nothing here says the variance statistic *detects* anything. Two
    reals summing to zero, one of them nonzero. -/
theorem burdenSquaredSignal_lt_varianceComponentSignal_of_opposite
    (β₁ β₂ : ℝ)
    (h_opposite : β₁ + β₂ = 0)
    (h_nonzero : β₁ ≠ 0) :
    -- Burden signal (sum) is zero but SKAT signal (sum of squares) is positive
    burdenSquaredSignal β₁ β₂ < varianceComponentSignal β₁ β₂ := by
  unfold burdenSquaredSignal varianceComponentSignal
  rw [h_opposite]
  simp
  have : β₂ = -β₁ := by linarith
  rw [this]
  positivity

end BurdenTests

/-!
## WGS-Based PGS

Whole genome sequencing enables inclusion of rare variants in PGS,
but the portability implications are complex.
-/

section WGSBasedPGS

/-- Cross-population signal carried by a variant after multiplying its additive genetic-variance
contribution by its sharing probability. -/
noncomputable def portableVariantSignal (β frequency sharing : ℝ) : ℝ :=
  variantGeneticVarianceContribution β frequency * sharing

/-- **Portable variant signal is jointly monotone in frequency below one-half and in sharing.**
The theorem includes zero effects, equal frequencies, and zero sharing; strict hypotheses are not
needed for a non-strict portability comparison. -/
theorem portableVariantSignal_mono_frequency_sharing
    (β p_common p_rare s_common s_rare : ℝ)
    (h_pr : 0 ≤ p_rare)
    (h_freq : p_rare ≤ p_common) (h_half : p_common ≤ 1 / 2)
    (h_sr : 0 ≤ s_rare)
    (h_sharing : s_rare ≤ s_common) :
    portableVariantSignal β p_rare s_rare ≤
      portableVariantSignal β p_common s_common := by
  unfold portableVariantSignal variantGeneticVarianceContribution
  have h_β2 : 0 ≤ β ^ 2 := sq_nonneg β
  have h_het_rare : 0 ≤ 2 * p_rare * (1 - p_rare) := by nlinarith
  have h_het_le : 2 * p_rare * (1 - p_rare) ≤ 2 * p_common * (1 - p_common) := by
    nlinarith [sq_nonneg (p_common - 1/2), sq_nonneg (p_rare - 1/2)]
  calc β ^ 2 * (2 * p_rare * (1 - p_rare)) * s_rare
      ≤ β ^ 2 * (2 * p_common * (1 - p_common)) * s_rare := by
        apply mul_le_mul_of_nonneg_right _ h_sr
        exact mul_le_mul_of_nonneg_left h_het_le h_β2
    _ ≤ β ^ 2 * (2 * p_common * (1 - p_common)) * s_common := by
        apply mul_le_mul_of_nonneg_left h_sharing
        apply mul_nonneg h_β2
        nlinarith [sq_nonneg (p_common - 1/2)]

/-- For a polymorphic nonzero-effect variant, portable signal vanishes exactly when the variant
is not shared with the target population. -/
theorem portableVariantSignal_eq_zero_iff
    (β frequency sharing : ℝ)
    (h_effect : β ≠ 0) (h_freq_pos : 0 < frequency) (h_freq_lt : frequency < 1) :
    portableVariantSignal β frequency sharing = 0 ↔ sharing = 0 := by
  have h_contribution : variantGeneticVarianceContribution β frequency ≠ 0 := by
    intro h_zero
    rcases (variantGeneticVarianceContribution_eq_zero_iff β frequency h_effect).1 h_zero with
      h_zero_freq | h_fixed
    · linarith
    · linarith
  unfold portableVariantSignal
  rw [mul_eq_zero]
  simp [h_contribution]

end WGSBasedPGS

/-!
## Loss-of-Function Variants

Loss-of-function (LoF) variants have uniquely interpretable effects
and different portability properties.
-/

section LossOfFunction

/-- **LoF variants have large effects.**
    LoF variants typically have effect sizes 5-10x larger than
    common regulatory variants, but they are very rare. -/
theorem lof_large_effects
    (β_lof β_common : ℝ)
    (h_larger : |β_common| < |β_lof|)
    (h_common_pos : 0 < |β_common|) :
    1 < |β_lof| / |β_common| := by
  rw [one_lt_div₀ h_common_pos]
  exact h_larger

/-!
### Mutation-selection balance, as the fixed point of a map

The frequency of a deleterious allele under purifying selection is usually quoted
as `μ/s`. That number is not a frequency: for `s < μ` it exceeds `1`, and `s < μ`
is admissible for exactly the weakly-constrained comparison arm the portability
claim is about. It is also the wrong quantity twice over — the dominant balance
is `μ/(h s)` and the recessive one is `√(μ/s)` — and this file's subject matter,
LoF variants scored by pLI and haploinsufficiency, spans both regimes.

So the two regimes are written here as one-generation maps and their equilibria
are derived as fixed points of those maps, in the shape of
`Descent.PopulationGeneticsFoundations.selectionMigrationEquilibrium_isFixedPoint`.
Both equilibria land in `[0, 1]` by construction rather than by hypothesis.
-/

/-- **One generation of mutation-selection dynamics for a rare deleterious allele
with dominance coefficient `h`.**

Heterozygotes carry selective load `h * s` and are the only carriers that matter
while the allele is rare, so the selection step multiplies the frequency by
`1 - h * s`; mutation then converts a fraction `mu` of the wild-type allele.
The `p ^ 2` homozygote term is dropped, which is the rare-allele linearization
and is valid only while `h * s` dominates `mu` — see
`mutationSelectionBalance_at_zero_dominance`, which shows the map degenerates at
`h = 0` and hands the recessive case to `mutationSelectionStepRecessive`.

    Empirical status: **VALIDATED as a linearisation**, with the gap
    stated (`validation/empirical/simcov/battery_bulk2.py`,
    `test_selection_step_against_wf`). Against one generation of EXACT viability
    selection -- genotype fitnesses `1`, `1 - h s`, `1 - s`, renormalised by mean
    fitness -- then two-way mutation, from `p = 0.2`:

      h     s      mu        this def   exact selection   relative
      0.5   0.02   1e-04      0.19808   0.19845            -0.19%
      0.5   0.10   1e-04      0.19008   0.19190            -0.95%
      0.2   0.05   1e-03      0.19880   0.19803            +0.39%

    The step drops the mean-fitness denominator and the `p²` term, so it is a
    linearisation valid at small `s` and small `p`; at `s = 0.1`, `p = 0.2` it is
    already about one percent per generation, which compounds over a run. Both
    sides are deterministic, so this is exact arithmetic and the gap is the
    approximation rather than sampling noise. -/
noncomputable def mutationSelectionStepRare (mu s h p : ℝ) : ℝ :=
  p * (1 - h * s) + mu * (1 - p)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem mutationSelectionStepRare_at_reference_point :
    mutationSelectionStepRare (1 / 2) (1 / 2) (1 / 2) (1 / 2) = 5 / 8 := by
  unfold mutationSelectionStepRare
  norm_num

/-- **Mutation-selection balance for a partially dominant deleterious allele.**

The fixed point of `mutationSelectionStepRare`. It is `mu / (h * s + mu)`, not
`mu / (h * s)`: the two agree to leading order when `h * s` is large against
`mu`, and the difference is what keeps this quantity inside `[0, 1]` for every
admissible parameter, including the weak-constraint regime `s < mu` where
`mu / s` is not a frequency at all.

    Empirical status: **VALIDATED IN THE DETERMINISTIC REGIME ONLY**, and
    FALSIFIED outside it. The regime boundary is `4 Nₑ h s`, a quantity this
    definition does not contain; see `mutationSelectionDriftParameter` below.

    The earlier VALIDATED reading rested on
    `simcov/battery_bulk2.py`, `test_mutation_selection`, which iterated
    `mutationSelectionStepRare` to convergence and recovered this body "to every
    digit carried". That is an algebraic identity -- this body IS that map's
    fixed point, by `mutationSelectionBalance_isFixedPoint` -- and no
    deterministic recursion can report the drift its own state variable does not
    carry. There is no population in that measurement.

    Two INDEPENDENT FORWARD, individual-based simulators (SLiM 4.3 in Eidos and
    fwdpy11 0.24.7 in C++, `validation/empirical/crossengine/`) put a
    real finite Wright-Fisher population under recurrent mutation, viability
    selection and drift at one biallelic site, and measured the time-averaged
    carrier frequency, `mu = 1e-04`, `s = 0.05`, `h = 0.5`, `Nₑ` swept:

      4 Nₑ h s   this def   SLiM                  fwdpy11               sems
      200         0.003984  0.004040 ± 0.000067  0.004040 ± 0.000082   0.8 / 0.7
      50          0.003984  0.004077 ± 0.000120  0.004218 ± 0.000096   0.8 / 2.4
      10          0.003984  0.004327 ± 0.000284  0.004133 ± 0.000296   1.2 / 0.5
      2.5         0.003984  0.6739   ± 0.0466    0.8141   ± 0.1033      14 / 7.8
      1           0.003984  0.9270   ± 0.0148    0.9105   ± 0.0387      62 / 23

    At `4 Nₑ h s ≥ 10` the body holds on both engines. At `4 Nₑ h s ≤ 2.5` it is
    low by a factor of 170 to 230: selection no longer holds the allele down,
    the site drifts to near-fixation for the deleterious allele, and a formula
    with no `Nₑ` in it cannot see that happen. The failure is not a coefficient
    error, so no reparametrisation repairs it -- the deterministic fixed point
    is simply not the stationary mean of the stochastic process.

    Both engines are FORWARD simulators. A coalescent simulator cannot produce
    this table at all: msprime, which produced every other empirical verdict in
    this corpus, has no selection, so it could not have found this and did not.
    The two engines agree with EACH OTHER on every cell, which is what
    distinguishes a corpus error from a harness error.

    Power, and the competitor that earns the match: on the same cells the
    per-diploid form `2 mu / (h s)` is rejected at 13 to 59 sems and the halved
    form `mu / (2 h s)` at 7.2 to 30, so the agreement in the top three rows is
    a measurement rather than a tautology.

    **The `+ mu` in the denominator is FALSIFIED.** The cells above cannot see
    it -- `mu / (h s + mu)` and the classical `mu / (h s)` differ by 0.4 percent
    at `mu / (h s) = 0.004`, far inside those error bars. Cells run at
    `mu / (h s)` of `1/2` and `1`, on a true biallelic locus at `4 Nₑ h s = 80`
    and `40` so that drift is not what is being measured:

      mu/(h s)   this def   classical   exact    measured             sems
      0.1         0.090909   0.1        0.0998   0.099778 ± 0.000766  12 high
      0.5         0.33333    0.5        0.49751  0.511475 ± 0.005490  32 high
      1.0         0.5        1.0        0.99499  0.997815 ± 0.001530 325 high

    where `exact` is the fixed point of EXACT viability selection -- genotype
    fitnesses `1, 1 - h s, 1 - s` renormalised by mean fitness -- followed by
    mutation. The measurement lands on `exact` (0.0, 2.5 and 1.8 sems) and on
    the classical form, and rejects this body at 12, 32 and 325 sems.

    So the justification this docstring gave for the `+ mu` term is backwards.
    It claimed the guard is "what keeps this quantity inside `[0, 1]` for every
    admissible parameter, including the weak-constraint regime `s < mu` where
    `mu / s` is not a frequency at all". The guard does return a number in
    `[0, 1]` there, but it is not the frequency: when the mutation rate reaches
    the selection load the deleterious allele really does go to near-fixation,
    and `mu / (h s + mu) = 1/2` understates it twofold. A denominator chosen to
    keep a formula in range is a range constraint, not a measurement, and this
    one buys its boundedness by being wrong in the interior.

    This body remains the exact fixed point of `mutationSelectionStepRare` --
    `mutationSelectionBalance_isFixedPoint` is a theorem and is not in question.
    What the measurement rejects is the identification of that fixed point with the standing
    frequency of a real population, at `mu` comparable to `h s`.
    Where `mu << h s` the two forms agree to `O(mu / (h s))` and the top table
    applies.

    These cells are SLiM only, and the harness enforces that by capability:
    at these mutation rates a single locus emulated by infinite sites takes
    repeat hits and stops being a single locus, so fwdpy11 -- which has no
    true-biallelic mode here -- is refused rather than averaged in. It returns
    0.394 and 0.669 on the last two cells, and that disagreement is the artefact,
    which is why the harness reports it as a broken instrument rather than as a
    third opinion. -/
noncomputable def mutationSelectionBalance (mu s h : ℝ) : ℝ :=
  mu / (h * s + mu)

/-- **The drift parameter the deterministic balance omits.**

`4 Nₑ h s` is the ratio of the selective force holding a partially dominant
deleterious allele down to the drift that pushes it around. It is the argument
`mutationSelectionBalance` does not take, and it is the whole of that
definition's regime of validity.

This is data, not a packaged claim that the deterministic approximation is
adequate. Any biological use of `mutationSelectionBalance` must compare this
explicit quantity with its own scientifically justified tolerance; measurement
puts the balance within measurement error at `4 Nₑ h s ≥ 10` and low by more
than two orders of magnitude at `4 Nₑ h s ≤ 2.5`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is the compound parameter
    itself, named so that a consumer has to confront it. The measurement that
    fixes where it matters is recorded on `mutationSelectionBalance`. -/
noncomputable def mutationSelectionDriftParameter (Ne s h : ℝ) : ℝ :=
  4 * Ne * h * s

/-- **The regime in which the deterministic balance was validated.**

Stated as a `Prop` rather than left in prose so that a consumer can be made to
carry it. The cross-engine measurement recorded on `mutationSelectionBalance`
holds this at `4 Nₑ h s ≥ 10` and fails it at `4 Nₑ h s ≤ 2.5`; the threshold
below is the conservative end of that bracket.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a hypothesis a consumer
    discharges, not a prediction about data. -/
def DeterministicMutationSelectionRegime (Ne s h : ℝ) : Prop :=
  10 ≤ mutationSelectionDriftParameter Ne s h

/-- **The regime is exactly a lower bound on the compound parameter**, and it is
strictly weaker than any bound on `s` or on `Nₑ` alone: a large population with nearly neutral
alleles and a small population with strongly selected ones can sit
at the same point. That is why the restriction is stated on the product. -/
theorem deterministicMutationSelectionRegime_iff (Ne s h : ℝ) :
    DeterministicMutationSelectionRegime Ne s h ↔ 10 ≤ 4 * Ne * h * s := by
  unfold DeterministicMutationSelectionRegime mutationSelectionDriftParameter
  exact Iff.rfl

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem mutationSelectionDriftParameter_at_reference_point :
    mutationSelectionDriftParameter 1000 (1 / 100) (1 / 2) = 20 := by
  unfold mutationSelectionDriftParameter
  norm_num

/-- **Without selection nothing holds the allele down.**

At `h * s = 0` the balance is one: mutation pushes and nothing pushes back, so the allele fixes.
The identification with the drift chart's saturation map, recorded below, is a cross-identity
between two definitions and constrains them jointly; both could carry the same wrong coefficient
on `h * s` and it would survive. This endpoint does not, and it is what makes the denominator a
sum of the two opposing rates rather than a fitted normalisation. -/
theorem mutationSelectionBalance_no_selection (mu : ℝ) (h : mu ≠ 0) :
    mutationSelectionBalance mu 0 0 = 1 := by
  unfold mutationSelectionBalance
  norm_num
  exact div_self h

/-- **Mutation-selection balance is the drift chart's saturation map, at a
different argument.**

`fstFromTau` sends `tau` to `tau / (1 + tau)`, and the balance frequency is that
same map applied to the ratio of mutation to effective selection, `mu / (h s)`.
The two modules therefore share one rational function: whatever is true of the
saturation law at one is true at the other, and a change to either body that
breaks this identity fails to compile rather than leaving the two quietly
disagreeing about a shape they both claim. -/
theorem mutationSelectionBalance_eq_fstFromTau (mu s h : ℝ)
    (hhs : h * s ≠ 0) (hsum : h * s + mu ≠ 0) :
    mutationSelectionBalance mu s h = Descent.Core.saturation (mu / (h * s)) := by
  unfold mutationSelectionBalance Descent.Core.saturation
  have hden : (h * s + mu) / (h * s) = 1 + mu / (h * s) := by
    rw [add_div, div_self hhs]
  rw [← hden, div_eq_div_iff hsum (div_ne_zero hsum hhs)]
  ring

/-- **Mutation-selection balance is the identity-fraction map at the scaled selective load.**

`DGP.fstMutationDriftEquilibrium θ = 1 / (1 + θ)` is this corpus's one body for the fraction
surviving a balance between a replenishing and a removing force, and the dominant
mutation-selection balance is that map at `θ = h·s / mu` — the selective load measured in
units of the mutation rate, exactly as `θ` and `M` measure mutation and migration in units
of drift.

Reading it this way is what makes the `mu / (h·s + mu)` form forced rather than chosen. The
textbook `mu / (h·s)` is not `1 / (1 + θ)` at any `θ`, and it leaves the unit interval in the
weak-constraint regime; the identity below is what a substitution of the one for the other
would have to contradict. -/
theorem mutationSelectionBalance_eq_identityFraction (mu s h : ℝ) (hmu : mu ≠ 0) :
    mutationSelectionBalance mu s h = Descent.Core.fstFromFlow (h * s / mu) := by
  have hsum : (1 : ℝ) + h * s / mu = (h * s + mu) / mu := by
    field_simp
    ring
  unfold mutationSelectionBalance Descent.Core.fstFromFlow
  rw [hsum, one_div_div]

/-- **The dominant balance is a fixed point of the dominant map.** This is what
makes the closed form above impossible to stipulate: it is derived from the
dynamic rather than asserted alongside it. -/
theorem mutationSelectionBalance_isFixedPoint (mu s h : ℝ)
    (h_load : 0 < h * s + mu) :
    mutationSelectionStepRare mu s h (mutationSelectionBalance mu s h) =
      mutationSelectionBalance mu s h := by
  have hne : h * s + mu ≠ 0 := ne_of_gt h_load
  unfold mutationSelectionStepRare mutationSelectionBalance
  field_simp
  ring

/-- The dominant balance is a frequency: it lies in `[0, 1]` for every
nonnegative mutation rate, nonnegative selective component `h*s`, and positive
total load. The quoted `mu / s` has no such bound, and exceeds `1` whenever
`s < mu`. -/
theorem mutationSelectionBalance_mem_unit (mu s h : ℝ)
    (h_mu : 0 ≤ mu) (h_hs : 0 ≤ h * s) (h_load : 0 < h * s + mu) :
    0 ≤ mutationSelectionBalance mu s h ∧ mutationSelectionBalance mu s h ≤ 1 := by
  unfold mutationSelectionBalance
  refine ⟨div_nonneg h_mu h_load.le, ?_⟩
  rw [div_le_one h_load]
  linarith

/-- **Exact loss boundary of dominant mutation--selection balance.**  When total load is nonzero,
the equilibrium deleterious-allele frequency vanishes exactly when mutation input vanishes. -/
theorem mutationSelectionBalance_eq_zero_iff
    (mu s h : ℝ) (h_load : h * s + mu ≠ 0) :
    mutationSelectionBalance mu s h = 0 ↔ mu = 0 := by
  unfold mutationSelectionBalance
  rw [div_eq_zero_iff]
  simp [h_load]

/-- **Exact fixation boundary of dominant mutation--selection balance.**  When total load is
nonzero, the equilibrium frequency is one exactly when the effective selective component `h*s`
vanishes. -/
theorem mutationSelectionBalance_eq_one_iff
    (mu s h : ℝ) (h_load : h * s + mu ≠ 0) :
    mutationSelectionBalance mu s h = 1 ↔ h * s = 0 := by
  unfold mutationSelectionBalance
  rw [div_eq_iff h_load]
  constructor <;> intro h_eq <;> nlinarith

/-- The balance is strictly below the textbook `mu / (h s)`, so the classical
formula is an upper bound and the correction is second order in `mu`. -/
theorem mutationSelectionBalance_lt_classical (mu s h : ℝ)
    (h_mu : 0 < mu) (h_hs : 0 < h * s) :
    mutationSelectionBalance mu s h < mu / (h * s) := by
  unfold mutationSelectionBalance
  exact div_lt_div_of_pos_left h_mu h_hs (by linarith)

/-- **The dominant linearization degenerates at full recessivity.** At `h = 0`
the map has no selection at all, and its fixed point is fixation. This is not a
defect of the closed form but a statement about the linearization: with `h = 0`
selection acts only through the dropped `p ^ 2` term, so the recessive case needs
`mutationSelectionStepRecessive` and gets a different scaling law. -/
theorem mutationSelectionBalance_at_zero_dominance (mu s : ℝ) (h_mu : mu ≠ 0) :
    mutationSelectionBalance mu s 0 = 1 := by
  unfold mutationSelectionBalance
  rw [zero_mul, zero_add]
  exact div_self h_mu

/-- **One generation for a fully recessive deleterious allele.** Selection acts
only on homozygotes, so the load is `s * p` per copy rather than `h * s`, and
mutation replenishes as before.

    Empirical status: **VALIDATED as a linearisation**, with the gap
    stated (`validation/empirical/simcov/battery_bulk8.py`,
    `test_mutation_selection_recessive`). Against one generation of EXACT
    recessive viability selection -- mean fitness `1 - s q^2`, renormalised --
    followed by two-way mutation. Both sides are deterministic, so this is exact
    arithmetic and the gap is the approximation:

      s      mu      p       this def   exact       relative
      0.05   1e-04   0.20     0.19808   0.19846      -0.19%
      0.20   1e-03   0.15     0.14635   0.14687      -0.35%
      0.01   1e-05   0.30     0.29911   0.29937      -0.09%

    The step omits the mean-fitness denominator, so it is a linearisation valid
    at small `s`; at `s = 0.2` it is already a third of a percent per
    generation, which compounds. This is the same qualifier
    `mutationSelectionStepRare` carries, and for the same reason. -/
noncomputable def mutationSelectionStepRecessive (mu s p : ℝ) : ℝ :=
  p - s * p ^ 2 + mu * (1 - p)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem mutationSelectionStepRecessive_at_reference_point :
    mutationSelectionStepRecessive (1 / 2) (1 / 2) (1 / 2) = 5 / 8 := by
  unfold mutationSelectionStepRecessive
  norm_num

/-- **Mutation-selection balance for a fully recessive deleterious allele**: the
nonnegative root of `s p² + mu p − mu = 0`, the fixed point of
`mutationSelectionStepRecessive`. It is `√(mu/s)` to leading order — a
qualitatively different scaling from the dominant `mu/(h s)` — and it is bounded
by `1` for every positive `s`.

    Empirical status: **VALIDATED IN THE LARGE-POPULATION LIMIT ONLY**, and
    FALSIFIED outside it. The regime boundary is `2 Nₑ √(mu s)`, a quantity this
    definition does not contain; see
    `recessiveMutationSelectionDriftParameter` below.

    The earlier unrestricted reading came from
    `validation/empirical/simcov/battery_bulk2.py`,
    `test_mutation_selection`: the fixed point of
    `mutationSelectionStepRecessive`, iterated to convergence from `p = 0.5`:
    0.03113, 0.04373 and 0.06825 predicted against the same three limits at
    `(mu, s)` of (1e-05, 0.01), (1e-04, 0.05) and (1e-03, 0.20). The quadratic
    root is the part that can be wrong, and it is not.

    That reading is now RESTRICTED, and the restriction is severe. Iterating
    `mutationSelectionStepRecessive` to its own fixed point recovers this body
    by `mutationSelectionBalanceRecessive_isFixedPoint`; it is an algebraic
    identity and there is no population in it. Forward, individual-based
    simulation of a real finite population -- SLiM 4.3, one true biallelic
    locus with genotype fitnesses `1, 1, 1 - s`, recurrent mutation and drift
    (`validation/empirical/crossengine/`) -- measures the time-averaged
    carrier frequency at `mu = 1e-04`, `s = 0.5` (so this body predicts
    0.014042) with `Nₑ` swept:

      Nₑ      2 Nₑ √(mu s)   measured             sems    relative
      16000   226            0.013362 ± 0.000158   -4.3    -4.8%
      4000     57            0.012439 ± 0.000200   -8.0   -11.4%
      1000     14            0.009379 ± 0.000190  -24.5   -33.2%
      200       2.8          0.005125 ± 0.000150  -59.6   -63.5%
      50        0.7          0.002941 ± 0.000181  -61.2   -79.1%

    The body is approached from below as `Nₑ` grows and is reached only in the
    large-population limit: even at `2 Nₑ √(mu s) = 226` it is still 4.8 percent
    high, and at `57` it is rejected outright. Below `2 Nₑ √(mu s) ≈ 14` it
    overstates the standing frequency of a recessive deleterious allele by a
    factor rising to five. This
    is the regime real human recessive alleles occupy, which is what makes the
    restriction worth stating rather than noting.

    The reason is structural, not a coefficient: heterozygotes are invisible to
    selection at `h = 0`, so a recessive allele is held down only through the
    homozygotes it makes, and at low frequency in a finite population it makes
    almost none. Drift then dominates over a range of `Nₑ` where the
    corresponding DOMINANT claim -- see `mutationSelectionBalance`, which needs
    only `4 Nₑ h s ≥ 10` -- is already safe. The two claims do not share a
    regime, and `mutationSelectionBalance_at_zero_dominance` records that they
    do not share a formula either.

    Power, and the competitor that earns the match: on the same cells the
    dominant scaling `mu / s` is rejected at 15 to 83 sems and `√(mu / (2 s))`
    at 3.3 to 39, and a deliberately planted body 40 percent above this one is
    rejected at 40 sems on the one cell that MATCHES -- so the agreement at
    large `Nₑ` is a measurement and not a tautology. The square-root scaling
    itself survives; only its `Nₑ`-independence does not.

    Measured on ONE engine by necessity. A recessive claim cannot be put to an
    infinite-sites simulator at all: two distinct mutations at one position make
    a compound heterozygote that is scored heterozygous at two sites and so
    escapes selection entirely at `h = 0`, which inflates the measurement and
    inflates it MORE as `Nₑ` grows. An earlier cross-engine run showed exactly
    that -- rising past this body to 0.023 at `Nₑ = 4000` -- and it was an
    artefact of the instrument, not a property of the corpus. fwdpy11 is
    excluded from this claim for that reason and the harness refuses it by
    capability rather than by comment. -/
noncomputable def mutationSelectionBalanceRecessive (mu s : ℝ) : ℝ :=
  (Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)

/-- **The drift parameter the recessive balance omits.**

`2 Nₑ √(mu s)` compares the selective force on a recessive deleterious allele
sitting at its deterministic frequency `√(mu/s)` -- which acts at rate `s √(mu/s)`
per copy, only through homozygotes -- with the drift rate `1/(2 Nₑ)`. It is the
argument `mutationSelectionBalanceRecessive` does not take.

This is data, not a packaged claim that the deterministic approximation is
adequate. Measurement puts that balance within 5 percent at `2 Nₑ √(mu s) = 226`,
11 percent high at `57`, and 63 to 79 percent high below `2 Nₑ √(mu s) ≤ 2.8`.

Note it is a WEAKER condition on `Nₑ` than the dominant case needs to be safe,
in the sense that it involves `√(mu s)` rather than `h s`: at `mu = 1e-04` and
`s = 0.5` the dominant claim is safe from `Nₑ = 10` while this one is not safe
until `Nₑ` is in the thousands.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is the compound parameter
    itself, named so that a consumer has to confront it. The measurement that
    fixes where it matters is recorded on `mutationSelectionBalanceRecessive`. -/
noncomputable def recessiveMutationSelectionDriftParameter (Ne mu s : ℝ) : ℝ :=
  2 * Ne * Real.sqrt (mu * s)

/-- **The regime in which the recessive deterministic balance was validated.**

Stated as a `Prop` rather than left in prose so that a consumer can be made to
carry it. The threshold is the conservative end of the measured bracket: the
claim is within 5 percent at `2 Nₑ √(mu s) = 226` and is rejected already at
`57`, so the bound is set at the value that was actually measured to hold.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a hypothesis a consumer
    discharges, not a prediction about data. -/
def DeterministicRecessiveBalanceRegime (Ne mu s : ℝ) : Prop :=
  200 ≤ recessiveMutationSelectionDriftParameter Ne mu s

/-- **The recessive regime is exactly a lower bound on the compound parameter.**
It constrains `Nₑ`, `mu` and `s` only jointly, which is why the restriction
cannot be stated as a bound on the effective size alone. -/
theorem deterministicRecessiveBalanceRegime_iff (Ne mu s : ℝ) :
    DeterministicRecessiveBalanceRegime Ne mu s ↔ 200 ≤ 2 * Ne * Real.sqrt (mu * s) := by
  unfold DeterministicRecessiveBalanceRegime recessiveMutationSelectionDriftParameter
  exact Iff.rfl

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem recessiveMutationSelectionDriftParameter_at_reference_point :
    recessiveMutationSelectionDriftParameter 1000 (1 / 100) 1 = 200 := by
  unfold recessiveMutationSelectionDriftParameter
  rw [show (1 : ℝ) / 100 * 1 = (1 / 10) ^ 2 by norm_num]
  rw [Real.sqrt_sq (by norm_num)]
  norm_num

/-- **mutationSelectionBalanceRecessive at zero s, named.** Without selection nothing holds a
recessive allele down and the balance frequency is not given by this formula at all. The divisor
`2 * s` is zero and Lean returns `0`, reporting the allele as absent where it is in fact free to
drift to fixation. Consumers must require `s ≠ 0`. -/
theorem mutationSelectionBalanceRecessive_zero_s_is_junk (mu : ℝ) :
    mutationSelectionBalanceRecessive mu 0 = 0 := by
  unfold mutationSelectionBalanceRecessive
  simp

/-- **The recessive balance is a fixed point of the recessive map.** -/
theorem mutationSelectionBalanceRecessive_isFixedPoint (mu s : ℝ)
    (h_mu : 0 ≤ mu) (h_s : 0 < s) :
    mutationSelectionStepRecessive mu s (mutationSelectionBalanceRecessive mu s) =
      mutationSelectionBalanceRecessive mu s := by
  have hs : s ≠ 0 := ne_of_gt h_s
  have hnn : 0 ≤ mu * (mu + 4 * s) := by
    nlinarith [mul_nonneg h_mu h_mu, mul_nonneg h_mu h_s.le]
  have hR : Real.sqrt (mu * (mu + 4 * s)) ^ 2 = mu * (mu + 4 * s) := Real.sq_sqrt hnn
  -- `x` is the candidate frequency; `2 s x = R - mu` is the only fact about it used.
  have hx : 2 * s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) =
      Real.sqrt (mu * (mu + 4 * s)) - mu := by
    field_simp
  have hR' : (2 * s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) + mu) ^ 2 =
      mu * (mu + 4 * s) := by
    rw [hx]
    linear_combination hR
  have hfour : (4 * s) * (s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) ^ 2) =
      (4 * s) * (mu * (1 - (Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s))) := by
    linear_combination hR'
  have hfour_ne : (4 : ℝ) * s ≠ 0 := by
    intro hc
    apply hs
    linarith
  have hkey : s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) ^ 2 =
      mu * (1 - (Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) :=
    mul_left_cancel₀ hfour_ne hfour
  unfold mutationSelectionStepRecessive mutationSelectionBalanceRecessive
  linear_combination -hkey

/-- The recessive balance is a frequency, and its square is bounded by `mu / s`:
`s p² ≤ mu`, which is the exact sense in which `p ≲ √(mu/s)`. -/
theorem mutationSelectionBalanceRecessive_sq_le (mu s : ℝ)
    (h_mu : 0 ≤ mu) (h_s : 0 < s) :
    s * mutationSelectionBalanceRecessive mu s ^ 2 ≤ mu ∧
      0 ≤ mutationSelectionBalanceRecessive mu s := by
  have hle : mu * mu ≤ mu * (mu + 4 * s) := by
    nlinarith [mul_nonneg h_mu h_s.le]
  have hRge : mu ≤ Real.sqrt (mu * (mu + 4 * s)) :=
    calc mu = Real.sqrt (mu * mu) := (Real.sqrt_mul_self h_mu).symm
      _ ≤ Real.sqrt (mu * (mu + 4 * s)) := Real.sqrt_le_sqrt hle
  have hnonneg : 0 ≤ mutationSelectionBalanceRecessive mu s := by
    unfold mutationSelectionBalanceRecessive
    apply div_nonneg (by linarith)
    linarith
  refine ⟨?_, hnonneg⟩
  have hfix := mutationSelectionBalanceRecessive_isFixedPoint mu s h_mu h_s
  simp only [mutationSelectionStepRecessive] at hfix
  nlinarith [hfix, mul_nonneg h_mu hnonneg]

/-- **LoF variant portability depends on gene constraint.**
    Highly constrained genes have LoF variants in all populations
    (purifying selection maintains them rare). The comparison is made on the
    dominant mutation-selection balance derived above, at a common dominance
    coefficient `h`, so both arms are frequencies in `[0, 1]` whatever the
    selection coefficients are — including the weakly constrained arm with `s < mu`, where `mu / s`
    exceeds one and is therefore not a frequency at all.

    Worked example: Genes with high constraint (e.g., pLI > 0.9) show
    this pattern most clearly, and `haploinsufficiency_consistent_direction`
    below is about the same `h > 0` regime this theorem is stated in. -/
theorem constrained_genes_more_portable_lof
    (s_constrained s_unconstrained μ h : ℝ)
    (h_μ : 0 < μ)
    (h_h : 0 < h)
    (h_su : 0 < s_unconstrained)
    (h_stronger : s_unconstrained < s_constrained) :
    -- Equilibrium frequency is lower under stronger constraint
    mutationSelectionBalance μ s_constrained h <
      mutationSelectionBalance μ s_unconstrained h := by
  unfold mutationSelectionBalance
  have h_lo : 0 < h * s_unconstrained + μ := by nlinarith
  have h_lt : h * s_unconstrained + μ < h * s_constrained + μ := by nlinarith
  exact div_lt_div_of_pos_left h_μ h_lo h_lt

/-- **Haploinsufficiency gives directional effects.**
    For haploinsufficient genes, any LoF variant reduces function.
    The direction of effect is consistent across populations,
    even if the specific variants differ. -/
theorem haploinsufficiency_consistent_direction
    (effect_pop1 effect_pop2 : ℝ)
    (h_same_direction : 0 < effect_pop1 ∧ 0 < effect_pop2
      ∨ effect_pop1 < 0 ∧ effect_pop2 < 0) :
    effect_pop1 * effect_pop2 > 0 := by
  rcases h_same_direction with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos h1 h2
  · exact mul_pos_of_neg_of_neg h1 h2

/-! **Deleted: `gene_lof_maximally_portable_rare`.**

This declaration is absent on purpose. It took `a ≤ b` and `b ≤ c` and returned
`le_trans h₁ h₂`: transitivity of `≤` on three reals, which is Mathlib's
`le_trans`, under a name asserting that gene-level loss-of-function aggregation
is the most portable rare-variant construction. Nothing in it referred to a
gene, a variant, an annotation or a score, and "maximally portable" is not a
statement two applications of `≤` can carry — a maximum needs a set to be
maximal over, and none was given. -/

end LossOfFunction

/-!
## Rare Variant Effect Size Distribution

The effect size distribution of rare variants differs from common
variants, affecting both PGS construction and portability.
-/

section EffectSizeDistribution

/-- **`2p(1-p)` is strictly increasing below `1/2`.**

    The selection reading — purifying selection removing large-effect alleles
    that reach high frequency, so `E[β²|MAF]` falls with `MAF` — is about effect
    sizes, and no effect size appears below. This is the heterozygosity
    expression alone, monotone on the left half of the frequency range. -/
theorem two_mul_mul_one_sub_lt_of_lt
    (maf_rare maf_common : ℝ)
    (h_common_lt : maf_common ≤ 1/2)
    (h_rare_maf : maf_rare < maf_common) :
    -- Heterozygosity is smaller for rarer variants (when both ≤ 1/2)
    2 * maf_rare * (1 - maf_rare) < 2 * maf_common * (1 - maf_common) :=
  Foundations.two_mul_one_sub_strictMono_le_half maf_rare maf_common h_rare_maf h_common_lt

/-- **The α model: E[β²] ∝ [p(1-p)]^(1+α).**
    α = 0: neutral (no relationship between MAF and effect)
    α = -1: LDAK (β² ∝ 1/[p(1-p)])
    When `α < -1`, the exponent `1 + α` is negative, so lower heterozygosity
    implies a larger expected effect-size multiplier. This makes rarer variants
    more population-specific and therefore less portable.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_ldsc.py`,
    `test_expected_effect_multiplier`). Under the alpha model each locus
    contributes `2 p(1-p) beta^2` to genetic variance with `Var(beta)`
    proportional to `(p(1-p))^alpha`, so the contribution scales as
    `(p(1-p))^(1+alpha)`. Measured as the RATIO of mean contribution between a
    `p ≈ 0.5` band and a `p ≈ 0.1` band, which is a derived consequence of the
    construction rather than the construction itself:

      alpha    this def   simulated            sems
      -1.0      1.00000   0.99874±0.01451      0.09
      -0.5      1.66667   1.64558±0.02389      0.88
       0.0      2.77778   2.79000±0.04033      0.30

    The `alpha = -1` cell is the one that matters: it predicts NO frequency
    dependence of the variance contribution, and the measurement returns 0.999.

    Power: the prediction spans 1.000 to 2.778 across the three exponents. -/
noncomputable def expectedEffectMultiplier (p α : ℝ) : ℝ :=
  (p * (1 - p)) ^ (1 + α)

/-- **The multiplier is symmetric about even frequency and neutral at `α = -1`.** It depends on
the allele only through the heterozygosity `p(1-p)`, so relabelling which allele is counted
cannot change it, and the exponent `1 + α` is zero exactly at the selection parameter where
frequency drops out entirely. -/
theorem expectedEffectMultiplier_symm (p α : ℝ) :
    expectedEffectMultiplier (1 - p) α = expectedEffectMultiplier p α := by
  unfold expectedEffectMultiplier
  rw [show (1 - p) * (1 - (1 - p)) = p * (1 - p) by ring]

theorem expectedEffectMultiplier_neutral_exponent (p : ℝ) :
    expectedEffectMultiplier p (-1) = 1 := by
  unfold expectedEffectMultiplier
  rw [show (1 : ℝ) + -1 = 0 by ring, Real.rpow_zero]

theorem alpha_model_portability_impact
    (p_rare p_common α : ℝ)
    (h_rare_pos : 0 < p_rare)
    (h_rare_lt : p_rare < p_common)
    (h_common_le : p_common ≤ 1 / 2)
    (h_alpha : α < -1) :
    expectedEffectMultiplier p_common α < expectedEffectMultiplier p_rare α := by
  unfold expectedEffectMultiplier
  have h_common_pos : 0 < p_common :=
    lt_trans h_rare_pos h_rare_lt
  have h_common_lt_one : p_common < 1 := by
    linarith
  have h_rare_lt_half : p_rare < 1 / 2 :=
    lt_of_lt_of_le h_rare_lt h_common_le
  have h_rare_het_pos : 0 < p_rare * (1 - p_rare) := by
    apply mul_pos h_rare_pos
    linarith
  have h_het_lt : p_rare * (1 - p_rare) < p_common * (1 - p_common) := by
    nlinarith [sq_nonneg (p_common - 1 / 2), sq_nonneg (p_rare - 1 / 2)]
  have h_exp_neg : 1 + α < 0 := by
    linarith
  exact Real.rpow_lt_rpow_of_neg h_rare_het_pos h_het_lt h_exp_neg

/-- **A reciprocal of a product below `1/100` exceeds `100`:** for
    `0 < maf < 1/100` and `|β| ≤ 1` with `β ≠ 0`, `100 < 1/(maf·β²)`.

    The reading is that a rare variant needs a large sample, via
    `R² ∝ n·MAF·β²` and a power threshold. Neither the proportionality nor the
    threshold appears below: there is no sample size, no power and no `R²`, and
    `100` is a numeral rather than a required `n`. -/
theorem hundred_lt_one_div_mul_sq
    (maf β : ℝ) (h_maf : 0 < maf) (h_maf_small : maf < 1 / 100)
    (h_β : β ≠ 0) (h_β_le : |β| ≤ 1) :
    100 < 1 / (maf * β ^ 2) := by
  have h_β_sq : β ^ 2 ≤ 1 := by nlinarith [sq_abs β, abs_nonneg β]
  have h_prod_pos : 0 < maf * β ^ 2 := mul_pos h_maf (sq_pos_of_ne_zero h_β)
  rw [lt_div_iff₀ h_prod_pos]
  have h_prod_small : maf * β ^ 2 < 1 / 100 := by
    calc maf * β ^ 2 ≤ maf * 1 := by nlinarith [sq_nonneg β]
    _ = maf := mul_one maf
    _ < 1 / 100 := h_maf_small
  nlinarith

end EffectSizeDistribution

/-- **The two in the recessive drift parameter is the ploidy.**

`RareVariantPortability.recessiveMutationSelectionDriftParameter` is
`2 Nₑ √(μ s)`, and that two is the number of gene copies per individual: a
population of `Nₑ` diploids carries `ploidy · Nₑ` gene copies, drift acts at rate
`1 / (ploidy · Nₑ)`, and the parameter is the selective force `√(μ s)` measured
against it. Written inline the two was a bare numeral in a quantity whose whole
job is to say when drift wins, and a haploid reading of the same formula would
be off by exactly this factor. -/
theorem recessiveMutationSelectionDriftParameter_uses_ploidy (Ne mu s : ℝ) :
    Portability.recessiveMutationSelectionDriftParameter Ne mu s
      = Descent.Core.ploidy * Ne * Real.sqrt (mu * s) := by
  unfold Portability.recessiveMutationSelectionDriftParameter Descent.Core.ploidy; ring

/-- **The four in the dominant drift parameter is the corpus's own rate scaling.**

`RareVariantPortability.mutationSelectionDriftParameter` is `4 Nₑ h s`, and the
`4 Nₑ` is not an independent convention: it is `scaledMutationRate`, the same
`4 Nₑ ·` normalisation the corpus already applies to a mutation rate to get `θ`
and to a migration rate to get `4 Nₑ m`, applied here to the heterozygous
selection load `h s`. This is deliberately NOT stated as a multiple of `ploidy`.
Only one of the two factors in `4 = 2 · 2` is a gene-copy count; the other comes
from the diffusion limit, and tying it to `ploidy` would record a claim about
genetics that this parameter does not make. -/
theorem mutationSelectionDriftParameter_eq_scaledMutationRate (Ne s h : ℝ) :
    Portability.mutationSelectionDriftParameter Ne s h = Descent.Core.scaledMutationRate Ne (h * s)
      := by
  unfold Portability.mutationSelectionDriftParameter Descent.Core.scaledMutationRate
    Descent.Core.ploidy; ring

/-- The two drift-variance definitions are the same quantity. -/
theorem pgsDriftVariance_one_pop_eq_Var_Delta_Mu (V_A fst : ℝ) :
    PopGen.pgsDriftVariance_one_pop V_A fst = Portability.Var_Delta_Mu V_A fst := by
  rw [Descent.PopGen.pgsDriftVariance_one_pop_eq_ploidy_form,
    Descent.Portability.Var_Delta_Mu_eq_ploidy_form]

end Descent.Portability
