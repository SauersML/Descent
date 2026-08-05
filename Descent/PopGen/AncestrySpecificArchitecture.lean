/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations

namespace Descent.PopGen

open MeasureTheory

/-!
# Ancestry-Specific Genetic Architecture

This file formalizes how genetic architecture parameters
(effect sizes, allele frequencies, LD patterns) differ across
ancestries and how these differences create portability barriers.

Key results:
1. Allele frequency divergence via drift
2. Effect size heterogeneity from GxE
3. Ancestry-specific LD tagging
4. Allelic heterogeneity (different causal variants per locus)
5. Architecture convergence under shared environments

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat drift models of allele-frequency divergence, allelic heterogeneity
or LD tagging. Sources for individual results, where they exist, are cited at those
results.
-/


/-!
## Allele Frequency Divergence

Allele frequency differences between populations are the
most fundamental driver of PGS portability issues.
-/

section AlleleFrequencyDivergence

/-!
### Derivation of expectedFreqDiffSq = 2·F·p₀(1-p₀)

**Which `F` this section's `fst` argument is, stated -- it is NOT the pairwise
`F_ST` the rest of the corpus is written for.**

Every `fst` argument in this section is the PER-BRANCH drift coefficient: the
single-population Wright `F` measured against the ANCESTOR, i.e. the fraction of
ancestral heterozygosity a lineage has lost since the split. Three distinct
quantities share the letter across this development and they are not
interchangeable:

* **Per-branch drift `F`** (this section). `1 - (1 - 1/(2·Nₑ))^t`, which is
  `PopulationGeneticsFoundations.heterozygosityLossFromDrift`, approaching
  `1 - e^(-τ)` in coalescent time.
* **Pairwise Hudson `F_ST`** (`PortabilityDrift.fstFromTau`), `τ/(1 + τ)`.
  These two are NOT equal, and the corpus proves it: `fstFromTau_lt_coalescenceCdf`
  says `τ/(1+τ) < 1 - e^(-τ)` at every positive `τ`. At `τ = 1` they are `0.500`
  against `0.632`, a 26% gap -- so the substitution is a real error and not a
  rounding one. They agree only to first order in small divergence.
* **Nei's `G_ST`** (`Conventions.neiGst`), which is `(p₁-p₂)²/(4·p̄·(1-p̄))` and
  is HALF the per-branch `F` this section wants, since this section's identity
  reads `E[(p₁-p₂)²] = 2·F·p₀(1-p₀)` while Nei's reads
  `E[(p₁-p₂)²] = 4·G_ST·p̄·(1-p̄)`. Feeding `neiGst` to `expectedFreqDiffSq`
  halves the answer.

The sentence this note replaces -- "this **is** the definition of Fst" -- was
the defect: it named a WITHIN-population heterozygosity loss as a
BETWEEN-population variance ratio, which is exactly the conflation
`Descent.PopGen.DriftRegime` exists to prohibit and which `Conventions`'
`fstFromDrift_uses_coalescentTimeScale` docstring already names as the corpus's
recurring `F_ST` bug. Nothing outside this file consumes these three
definitions, so no downstream value is wrong today; the trap was live for the
next consumer.

Under the Wright-Fisher model, genetic drift causes allele frequencies
to fluctuate randomly across generations. For a single population
diverging from an ancestor with allele frequency p₀:

  Var(p_t - p₀) = p₀(1-p₀) × F(t)

with `F(t)` the per-branch drift coefficient just defined.

**Single-population drift variance:**
  driftVariance(p₀, F) = p₀·(1-p₀)·F

**Two-population divergence:**
Consider two populations (pop₁, pop₂) that diverged independently
from the same ancestral population with frequency p₀. Their allele
frequency deviations (p₁ - p₀) and (p₂ - p₀) are independent
because drift is driven by independent sampling in each lineage.

  E[(p₁ - p₂)²] = Var(p₁ - p₂)          (since E[p₁ - p₂] = 0)
                 = Var(p₁) + Var(p₂)      (independence of drift)
                 = p₀(1-p₀)·F + p₀(1-p₀)·F
                 = 2·p₀(1-p₀)·F

The factor of 2 arises because **both** lineages drift independently,
so the variance of their difference is the sum of their individual
drift variances.
-/

/-- **Drift variance for a single population.**
    `Var(p_t - p₀) = p₀(1-p₀) × F`, with `F` the PER-BRANCH drift coefficient --
    the fraction of ancestral heterozygosity this one lineage has lost since the
    split, Wright's `F` against the ancestor.

    Convention: `fst` is that per-branch `F`, not the pairwise Hudson `F_ST` of
    `PortabilityDrift.fstFromTau` and not Nei's `G_ST`. The section note above
    gives the three conversions and the size of each mistake; the short version
    is that Hudson agrees only to first order (`0.500` against `0.632` at
    `τ = 1`) and Nei's `G_ST` is exactly half of what this argument wants.

    Empirical status: **VALIDATED**, and the design is what earns that -- an earlier
    reading of this docstring headlined it VACUOUS, which was wrong and is corrected here.
    The vacuity is a property of a DESIGN, not of this definition. `battery_bulk21` scored a
    MATCH that carried no information, because it estimated `F_ST` on the same run as
    `Var(p) / (p₀(1-p₀))`, and substituting that relation into this body gives
    `p₀(1-p₀) · Var(p) / (p₀(1-p₀))`, which is `Var(p)` -- the estimator itself,
    residual exactly `0` under computer algebra, using no Wright-Fisher property
    beyond the martingale `E[p_t] = p₀`. That design could not have rejected any
    competitor, so it measured nothing.

    A design that takes `F` from the MODEL instead is not an identity, and it is
    the one that settles the convention question the paragraph above raises:
    **VALIDATED** (`simcov/battery_bulk41.py`, `group_b`). The design
    escapes the identity above by never feeding the sample's own heterozygosity loss back
    in. `F` is the MODEL's `1-(1-1/(2Nₑ))^t`, computed from the simulation's `Nₑ` and `t`
    alone; the observable is the realised `Var(p₁ - p₀)` over 2×10⁵ independent loci under
    Wright-Fisher binomial sampling in two demes from a common ancestor at `p₀ = 0.3`, with no
    mutation and no migration.

      Nₑ    t     F        this body   realised Var   sems
      200    50   0.1176    0.02470      0.02464      0.85
      200   150   0.3130    0.06574      0.06556      0.96
      500   100   0.0952    0.01999      0.01997      0.44
      100    40   0.1817    0.03815      0.03817      0.14

    The identity gate carries the two substitutions the paragraph above warns about, each
    MEASURED on the same replicates rather than converted. Nei's `G_ST` misses by up to 157
    sems, 47% low, which is the promised factor of two. The Hudson pairwise `F_ST` misses by
    7.8 sems, 2.3% -- the first-order agreement the note predicts, and small enough to
    explain why that substitution has gone unnoticed elsewhere in the corpus. The positive
    control, drift is unbiased so `E[p_t] = p₀`, passes at 0.95 sems. -/
noncomputable def driftVariance (p0 fst : ℝ) : ℝ :=
  p0 * (1 - p0) * fst

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem driftVariance_at_reference_point :
    driftVariance (1 / 2) (1 / 2) = 1 / 8 := by
  unfold driftVariance
  norm_num

/-- Drift variance is nonnegative on the biological parameter domain. -/
theorem driftVariance_nonneg (p0 fst : ℝ)
    (h_p0 : 0 ≤ p0) (h_p0_le : p0 ≤ 1) (h_fst : 0 ≤ fst) :
    0 ≤ driftVariance p0 fst := by
  unfold driftVariance
  apply mul_nonneg
  · exact mul_nonneg h_p0 (sub_nonneg.mpr h_p0_le)
  · exact h_fst

/-- Drift variance vanishes exactly at a monomorphic ancestor or at zero differentiation. -/
theorem driftVariance_eq_zero_iff (p0 fst : ℝ) :
    driftVariance p0 fst = 0 ↔ p0 = 0 ∨ p0 = 1 ∨ fst = 0 := by
  unfold driftVariance
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr h)
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- **Two-population drift variance from independent lineages.**
    For two populations diverging independently from the same
    ancestor, Var(p₁ - p₂) = Var(p₁) + Var(p₂) = 2·driftVariance.
    The factor of 2 comes from independence of drift.

    Empirical status: **VALIDATED**. As at `driftVariance`, an earlier reading of this
    docstring headlined it VACUOUS; that was wrong, because vacuity here is a property of a
    DESIGN and not of this definition, and it is corrected. `battery_bulk21`'s MATCH
    did carry no information: substituting the simulator's own
    `F_ST := Var(p)/(p₀(1-p₀))` collapses this onto
    `2·Var(p)`, which is what the simulator computes for `Var(p₁ - p₂)` once the two
    lineages are drawn independently — residual exactly `0`. The factor of `2` the docstring
    argues for is therefore assumed by the estimator, not tested by it. UNTESTED as a claim
    about the world.

    THE FACTOR OF TWO IS NOW TESTED: **VALIDATED** (`simcov/battery_bulk41.py`, `group_b`),
    by the design described at `driftVariance` -- `F` from the model's `Nₑ` and `t`, never
    from the sample -- with the observable being the realised `E[(p₁ - p₂)²]` over 2×10⁵
    independent loci in two independently drifting demes.

      Nₑ    t     F        this body   realised E[(p₁-p₂)²]   sems
      200    50   0.1176    0.04941         0.04932           0.61
      200   150   0.3130    0.13147         0.13129           0.46
      500   100   0.0952    0.03999         0.03991           0.61
      100    40   0.1817    0.07631         0.07636           0.23

    Dropping the factor of two on the SAME cells misses by up to 168 sems, 50% low, so the
    two is now carried by data rather than by the estimator's definition. Feeding the
    measured Hudson `F_ST` instead misses by 7.6 sems, 2.3%. -/
noncomputable def twoPopDriftVariance (p0 fst : ℝ) : ℝ :=
  2 * driftVariance p0 fst

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem twoPopDriftVariance_at_reference_point :
    twoPopDriftVariance (1 / 2) (1 / 2) = 1 / 4 := by
  norm_num [twoPopDriftVariance, driftVariance]


/-- Two-population drift variance equals the sum of individual drift variances. -/
theorem twoPopDriftVariance_eq_sum (p0 fst : ℝ) :
    twoPopDriftVariance p0 fst = driftVariance p0 fst + driftVariance p0 fst := by
  unfold twoPopDriftVariance; ring

/-- Independent two-lineage drift has the same null fiber as one-lineage drift. -/
theorem twoPopDriftVariance_eq_zero_iff (p0 fst : ℝ) :
    twoPopDriftVariance p0 fst = 0 ↔ p0 = 0 ∨ p0 = 1 ∨ fst = 0 := by
  rw [twoPopDriftVariance_eq_sum]
  constructor
  · intro h
    have h_zero : driftVariance p0 fst = 0 := by linarith
    exact (driftVariance_eq_zero_iff p0 fst).1 h_zero
  · intro h
    rw [(driftVariance_eq_zero_iff p0 fst).2 h]
    norm_num

/-- **Expected allele frequency difference from drift.**
    `E[(p₁ - p₂)²] = 2 × F × p₀(1-p₀)`, `p₀` the ancestral frequency and `F` the
    per-branch drift coefficient of `driftVariance`.

    Convention: the `2` is the count of independently drifting branches, and it
    is the constant that goes wrong when the argument is read as a pairwise
    differentiation instead. Against Nei's `G_ST` the same expectation is
    `4·G_ST·p̄·(1-p̄)`, so `fst := neiGst p₁ p₂` halves this body. See the
    section note.

    Empirical status: **VALIDATED**. An earlier reading of this docstring headlined it
    VACUOUS; that was wrong for the reason given at `driftVariance` -- vacuity is a property
    of a design, not of a definition -- and it is corrected here.
    `battery_bulk21`'s MATCH carried no information; this body is `twoPopDriftVariance`
    with its arguments in the other order, so it collapses onto the simulator's `2·Var(p)`
    for the same reason and with the same exactly-`0` residual. Note what that means for the
    convention paragraph above: the factor-of-2 question and the Nei/Hudson question are
    precisely what the simulation could NOT answer, because the estimator it compared
    against carried the corpus's own convention in its definition of `fst`. UNTESTED as a
    claim about the world; the convention is open and a simulation pinned to the convention
    cannot close it.

    A SIMULATION NOT PINNED TO THE CONVENTION CLOSES IT: **VALIDATED**
    (`simcov/battery_bulk41.py`, `group_b`). The escape is to take `F` from the model --
    `1-(1-1/(2Nₑ))^t`, a function of the simulation's parameters and nothing else -- and to
    MEASURE the Hudson `F_ST` and Nei `G_ST` separately on the same replicates as
    competitors, so all three conventions are numbers the run produced rather than one
    convention evaluated twice.

      Nₑ    t     F        this body   realised E[(p₁-p₂)²]   sems
      200    50   0.1176    0.04941         0.04932           0.61
      200   150   0.3130    0.13147         0.13129           0.46
      500   100   0.0952    0.03999         0.03991           0.61
      100    40   0.1817    0.07631         0.07636           0.23

    Both questions the paragraph above called unanswerable are answered on these cells: the
    factor of two is confirmed, since halving misses by 168 sems, and the Nei reading is
    refuted at 157 sems and 47% low -- the promised halving. The Hudson reading misses by
    only 2.3%, which is the first-order agreement and the reason it is a trap rather than an
    obvious error. -/
noncomputable def expectedFreqDiffSq (fst p0 : ℝ) : ℝ :=
  2 * fst * p0 * (1 - p0)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem expectedFreqDiffSq_at_reference_point :
    expectedFreqDiffSq (1 / 2) (1 / 2) = 1 / 4 := by
  unfold expectedFreqDiffSq
  norm_num

/-- **The two-population drift variance equals expectedFreqDiffSq.**
    This connects the derivation (summing independent drift variances)
    to the closed-form formula 2·Fst·p₀(1-p₀). -/
theorem twoPopDriftVariance_eq_expectedFreqDiffSq (p0 fst : ℝ) :
    twoPopDriftVariance p0 fst = expectedFreqDiffSq fst p0 := by
  unfold twoPopDriftVariance driftVariance expectedFreqDiffSq; ring

/-- Expected frequency difference is nonnegative on the biological parameter domain. -/
theorem expectedFreqDiffSq_nonneg (fst p0 : ℝ)
    (h_fst : 0 ≤ fst) (h_p0 : 0 ≤ p0) (h_p0_le : p0 ≤ 1) :
    0 ≤ expectedFreqDiffSq fst p0 := by
  unfold expectedFreqDiffSq
  nlinarith [mul_nonneg h_fst h_p0,
    mul_nonneg (mul_nonneg h_fst h_p0) (by linarith : 0 ≤ 1 - p0)]

/-- Expected squared frequency divergence vanishes exactly at zero differentiation or
when the ancestral allele is absent or fixed. -/
theorem expectedFreqDiffSq_eq_zero_iff (fst p0 : ℝ) :
    expectedFreqDiffSq fst p0 = 0 ↔ fst = 0 ∨ p0 = 0 ∨ p0 = 1 := by
  rw [← twoPopDriftVariance_eq_expectedFreqDiffSq]
  constructor
  · intro h
    rcases (twoPopDriftVariance_eq_zero_iff p0 fst).1 h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · rintro (h | h | h)
    · exact (twoPopDriftVariance_eq_zero_iff p0 fst).2 (Or.inr (Or.inr h))
    · exact (twoPopDriftVariance_eq_zero_iff p0 fst).2 (Or.inl h)
    · exact (twoPopDriftVariance_eq_zero_iff p0 fst).2 (Or.inr (Or.inl h))

/-- **Expected frequency difference increases with FST.**
    Derived from drift variance formula: E[(p₁-p₂)²] = 2·Fst·p₀(1-p₀).
    Since p₀(1-p₀) > 0 for 0 < p₀ < 1, the function is strictly
    increasing in Fst. This is direct algebraic monotonicity of
    the `expectedFreqDiffSq` definition. -/
theorem freq_diff_increases_with_fst (fst₁ fst₂ p0 : ℝ)
    (h_p0 : 0 < p0) (h_p0_lt : p0 < 1)
    (h_fst : fst₁ < fst₂) :
    expectedFreqDiffSq fst₁ p0 < expectedFreqDiffSq fst₂ p0 := by
  unfold expectedFreqDiffSq
  have h_het : 0 < p0 * (1 - p0) := mul_pos h_p0 (by linarith)
  -- 2 * fst₁ * p0 * (1 - p0) < 2 * fst₂ * p0 * (1 - p0)
  -- follows from fst₁ < fst₂ and 2 * p0 * (1-p0) > 0
  nlinarith

/- **Frequency-dependent effect on PGS variance.**
    PGS variance = Σ β²_j × 2p_j(1-p_j).
    When allele frequencies change, PGS variance changes even
    with identical effect sizes. -/
/-- **Exact ambiguity of weighted heterozygosity.** With a nonzero effect weight, two allele
frequencies have the same variance contribution exactly when they are equal or complementary.
The second branch is the minor/major-allele symmetry `p ↔ 1 - p`. -/
theorem weighted_heterozygosity_eq_iff
    (beta_sq p_source p_target : ℝ) (h_beta : beta_sq ≠ 0) :
    beta_sq * (2 * p_source * (1 - p_source)) =
        beta_sq * (2 * p_target * (1 - p_target)) ↔
      p_source = p_target ∨ p_source + p_target = 1 := by
  constructor
  · intro h
    have h_het : 2 * p_source * (1 - p_source) =
        2 * p_target * (1 - p_target) :=
      mul_left_cancel₀ h_beta h
    have h_factor : (p_source - p_target) * (1 - p_source - p_target) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp h_factor with h_same | h_complement
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | h_complement)
    · rfl
    · rw [show p_target = 1 - p_source by linarith]
      ring

theorem freq_change_alters_pgs_variance
    (beta_sq p_source p_target : ℝ)
    (h_beta : beta_sq ≠ 0)
    (h_diff : p_source ≠ p_target)
    (h_not_complement : p_source + p_target ≠ 1) :
    beta_sq * (2 * p_source * (1 - p_source)) ≠
      beta_sq * (2 * p_target * (1 - p_target)) := by
  intro h
  rcases (weighted_heterozygosity_eq_iff beta_sq p_source p_target h_beta).1 h with h_same | h_complement
  · exact h_diff h_same
  · exact h_not_complement h_complement

/-- **Lower-frequency alleles have larger proportional drift.**
    Variants with lower MAF have larger proportional frequency
    changes under drift than higher-MAF variants, because the
    coefficient of variation `(1-p)/p` is decreasing throughout the
    positive-frequency axis.

    Worked example: Rare variants (MAF < 1%) vs common variants (MAF > 5%). -/
theorem rare_variants_drift_more
    (p_rare p_common fst : ℝ)
    (h_rare : 0 < p_rare) (h_rare_lt : p_rare < p_common)
    (h_fst : 0 < fst) :
    -- Coefficient of variation of frequency is larger for rare
    expectedFreqDiffSq fst p_rare / p_rare^2 >
      expectedFreqDiffSq fst p_common / p_common^2 := by
  unfold expectedFreqDiffSq
  -- Need: 2*fst*p_rare*(1-p_rare)/p_rare² > 2*fst*p_common*(1-p_common)/p_common²
  -- = 2*fst*(1-p_rare)/p_rare > 2*fst*(1-p_common)/p_common
  -- = (1-p_rare)/p_rare > (1-p_common)/p_common
  -- = 1/p_rare - 1 > 1/p_common - 1
  -- = 1/p_rare > 1/p_common, true since p_rare < p_common
  have h_r2 : (0 : ℝ) < p_rare ^ 2 := sq_pos_of_pos h_rare
  have h_c2 : (0 : ℝ) < p_common ^ 2 := sq_pos_of_pos (by linarith)
  rw [gt_iff_lt, div_lt_div_iff₀ h_c2 h_r2]
  -- Difference factors as 2*fst*p_rare*p_common*(p_common - p_rare) > 0
  nlinarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) h_fst)
                              (mul_pos h_rare (show (0:ℝ) < p_common from by linarith)))
                     (show (0:ℝ) < p_common - p_rare from by linarith)]

end AlleleFrequencyDivergence


/-!
## Ancestry-Specific LD Tagging

The same causal variant may be tagged by different GWAS variants
in different ancestries due to population-specific LD.
-/

section LDTagging

/-- Apparent effect recovered through a tag at LD correlation `tagR` to the
causal variant.

    Regime: one causal variant, one tag, both standardized; the apparent effect
    is the tag's MARGINAL regression coefficient.

    Empirical status: **VALIDATED** (`simcov/battery_bulk22.py`, `group_b`).
    One causal variant and one tag at correlation `r`, both standardized, over
    2×10⁶ individuals; the observable is the tag's REALISED marginal OLS slope.
    `r` is swept from 0.3 to 0.9, over which `r` and `r²` separate threefold.

      β_c    r     this body   realised slope   sems
      0.3   0.9     0.270000      0.269586       0.61
      0.3   0.5     0.150000      0.150119       0.17
      0.5   0.7     0.350000      0.350293       0.44
      0.2   0.3     0.060000      0.060220       0.31

    The identity gate is carried: the squared form `β_c · r²` is run on the SAME
    cells and misses by 39 to 159 sems — at `r = 0.3` it predicts 0.018 against
    a measured 0.0602 — and the positive control, the causal variant's own
    slope, which must be `β_c`, passes at 0.02 sems. A match with no rejected
    competitor would have measured nothing.

    CORRECTED. This body previously took squared LD. Regressing the phenotype
    on the tag recovers
    `Cov(g_tag, y) = β_c · r`, and a standardized tag has unit variance, so no
    second factor of `r` divides it out. Both forms were carried on the same
    cells, so the exponent was chosen by the data and not by the parameter's
    name.

    `r²` remains the right argument for quantities QUADRATIC in the effect --
    the variance a tag explains is `β_c² · r²`, and there the square belongs.
    It is the linear effect that takes `r`. The sign matters too and `r²`
    discards it: two tags in equal-magnitude but opposite-sign LD carry
    apparent effects of opposite sign.

    LEDGER, read correctly. `simcov/ledger.json` carries a FALSIFIED record
    against the NAME `taggedEffect` at 158.98 sems (`bulk22`). It is not a
    falsification of the body below. Its `source` field reads
    `causalEffect * tagR2`, which is the squared form this definition was
    corrected AWAY from, and the same battery's other row -- `causalEffect * tagR`,
    logged with role `competitor` because it was the challenger at the time --
    is the MATCH at 0.61 sems and is what is written here now. The record is
    stale with respect to the body, and marked so: its freshness field is
    `UNVERIFIED (no recorded source hash)`, so nothing checked it against the
    Lean when the correction landed. Cited here because a reader who greps the
    ledger for this name and not for its `source` reaches the opposite
    conclusion, and the ledger cannot say this about itself. -/
noncomputable def taggedEffect (causalEffect tagR : ℝ) : ℝ :=
  Descent.Core.product causalEffect tagR

/-- The tagged-effect scale is pinned at an interior reference point. -/
theorem taggedEffect_at_reference_point : taggedEffect (1 / 2) (1 / 2) = 1 / 4 := by
  norm_num [taggedEffect,
      Descent.Core.product]

/-- **Tag SNP may differ across populations.**
    If tag_source is the best proxy for causal variant C in the source,
    and tag_target is the best proxy in the target,
    these may be different SNPs entirely. Their apparent effects agree exactly
    when the causal effect is null or the two tags have the same LD correlation.

    The discriminating parameter is the CORRELATION and not its square: two tags
    with equal `r²` but opposite sign carry apparent effects of opposite sign,
    which this statement now separates and the `r²` form could not. -/
theorem taggedEffect_eq_iff
    (causalEffect sourceTagR targetTagR : ℝ) :
    taggedEffect causalEffect sourceTagR = taggedEffect causalEffect targetTagR ↔
      causalEffect = 0 ∨ sourceTagR = targetTagR := by
  unfold taggedEffect Descent.Core.product
  constructor
  · intro h
    by_cases h_effect : causalEffect = 0
    · exact Or.inl h_effect
    · exact Or.inr (mul_left_cancel₀ h_effect h)
  · rintro (rfl | rfl) <;> ring

/-- **LD tagging efficiency.**
    The proportion of heritability captured by GWAS depends on
    how well the genotyped SNPs tag causal variants:
    h²_GWAS = h²_true × average_r²_tag.

    Regime: `h²_true` is the heritability the effects actually carry, not a
    nominal per-effect variance times a locus count. The distinction is not
    pedantic and it is what a measurement of this definition turns on -- see
    below.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_dis1.py`). 100000 individuals,
    300 causal variants each tagged by one variant at correlation `rho`,
    heritability captured by regressing the outcome on the TAGS, with the
    in-sample `R²` corrected for its `m/n` optimism:

      design              this def   captured
      h² = 0.5, rho = 0.9  0.40590   0.40681 ± 0.00257   (0.35 sems)
      h² = 0.5, rho = 0.6  0.18777   0.18793 ± 0.00119   (0.14 sems)
      h² = 0.8, rho = 0.8  0.51355   0.50972 ± 0.00322   (1.19 sems)

    **A retraction** (`battery_bulk5.py`). That battery reported this definition
    FALSIFIED at 42 sems and 23 percent low. The report is withdrawn: it drew 60
    effects from `N(0, h²/M)` and then compared against the NOMINAL `h²`. The
    realised heritability of 60 such draws scatters by `sqrt(2/60)`, about 18
    percent, which is the whole of the reported error -- the same runs agree to
    0.35 sems once `h²_true` is read as the heritability the drawn effects
    actually produce. The definition never claimed to know what a finite draw
    would realise.

    Power: the prediction spans 0.18777 to 0.51355 across the design.

    **The exponent is chosen by the data** (`simcov/battery_bulk29.py`,
    `group_b`), which the run above did not establish. An independent design --
    200 causal variants each with one tag, the phenotype built from the CAUSAL
    variants and the score fitted on the TAGS, 300000 individuals -- reproduces
    this body at worst 3.51 sems (1.2% relative) with `r` swept 0.3 to 0.9.
    Carried on the same cells, the UNSQUARED form `h²_true · r` is FALSIFIED at
    up to 652 sems (225% relative). So the square is not a convention: a tag
    recovers heritability, which is quadratic in the effect, through `r²`, while
    it recovers the EFFECT itself through `r` -- see `taggedEffect`, where the
    corpus had the exponents the other way round. -/
noncomputable def gwasHeritability (h2_true avg_r2_tag : ℝ) : ℝ :=
  Descent.Core.product h2_true avg_r2_tag

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem gwasHeritability_at_reference_point :
    gwasHeritability (1 / 2) (1 / 2) = 1 / 4 := by
  unfold gwasHeritability Descent.Core.product
  norm_num

/-- GWAS heritability vanishes exactly when there is no heritable signal or no tagging. -/
theorem gwasHeritability_eq_zero_iff (h2_true avg_r2_tag : ℝ) :
    gwasHeritability h2_true avg_r2_tag = 0 ↔ h2_true = 0 ∨ avg_r2_tag = 0 := by
  unfold gwasHeritability Descent.Core.product
  exact mul_eq_zero

/-- Perfect tagging recovers the true heritability; equality also holds vacuously when
the true heritability itself is zero. -/
theorem gwasHeritability_eq_true_iff (h2_true avg_r2_tag : ℝ) :
    gwasHeritability h2_true avg_r2_tag = h2_true ↔
      h2_true = 0 ∨ avg_r2_tag = 1 := by
  unfold gwasHeritability Descent.Core.product
  constructor
  · intro h
    have h_factor : h2_true * (avg_r2_tag - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h_factor with h_zero | h_tag
    · exact Or.inl h_zero
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

/-- GWAS heritability is at most true heritability under nonnegative signal and
tagging efficiency at most one. -/
theorem gwasHeritability_le_true (h2_true avg_r2_tag : ℝ)
    (h_h2 : 0 ≤ h2_true) (h_r2_le : avg_r2_tag ≤ 1) :
    gwasHeritability h2_true avg_r2_tag ≤ h2_true := by
  unfold gwasHeritability Descent.Core.product
  nlinarith


end LDTagging


/-!
## Allelic Heterogeneity

At the same locus, different populations may harbor different
causal variants due to independent mutation and selection.
-/

section AllelicHeterogeneity

/-- Signal retained after causal tagging and allelic sharing are applied. -/
noncomputable def allelicHeterogeneityRetainedSignal
    (r2_causal r2_tag sharedFraction : ℝ) : ℝ :=
  Descent.Core.product3 r2_causal r2_tag sharedFraction

/-- The retained-signal definition is pinned at an interior reference point. -/
theorem allelicHeterogeneityRetainedSignal_at_reference_point :
    allelicHeterogeneityRetainedSignal (1 / 2) (1 / 2) (1 / 2) = 1 / 8 := by
  norm_num [allelicHeterogeneityRetainedSignal,
      Descent.Core.product3]

/-- **Allelic heterogeneity reduces portability via variance decomposition.**
    Total locus variance in source = V_shared + V_source_specific.
    The tag SNP captures r²_tag of source total variance.
    In target, only the shared component transfers: target variance
    at the tag = r²_tag × V_shared = r²_tag × ρ × V_total,
    where ρ = V_shared / V_total < 1 due to population-specific variants.

    Derived: r2_causal * r2_tag * ρ < r2_causal * r2_tag because
    multiplying the positive quantity r2_causal * r2_tag by ρ < 1
    strictly reduces it. -/
theorem allelicHeterogeneityRetainedSignal_lt_full
    (r2_causal r2_tag ρ : ℝ)
    (h_causal : 0 < r2_causal) (h_tag : 0 < r2_tag)
    (h_ρ_lt : ρ < 1) :
    allelicHeterogeneityRetainedSignal r2_causal r2_tag ρ < r2_causal * r2_tag := by
  unfold allelicHeterogeneityRetainedSignal Descent.Core.product3
  have h_prod_pos : 0 < r2_causal * r2_tag := mul_pos h_causal h_tag
  calc r2_causal * r2_tag * ρ
      < r2_causal * r2_tag * 1 := by nlinarith
    _ = r2_causal * r2_tag := mul_one _

/-- Retained signal equals the fully shared signal exactly when one upstream signal
channel is already zero or the allelic component is completely shared. -/
theorem allelicHeterogeneityRetainedSignal_eq_full_iff
    (r2_causal r2_tag ρ : ℝ) :
    allelicHeterogeneityRetainedSignal r2_causal r2_tag ρ = r2_causal * r2_tag ↔
      r2_causal = 0 ∨ r2_tag = 0 ∨ ρ = 1 := by
  unfold allelicHeterogeneityRetainedSignal Descent.Core.product3
  constructor
  · intro h
    have h_factor : r2_causal * r2_tag * (ρ - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h_factor with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> ring

/-- Total gene-level variance is the sum of shared and population-specific components. -/
noncomputable def populationGeneVariance (shared specific : ℝ) : ℝ :=
  Descent.Core.sum shared specific

/-- Fraction of a target population's gene-level variance carried by shared variants. -/
noncomputable def crossPopulationGeneTransferFraction (shared targetSpecific : ℝ) : ℝ :=
  shared / populationGeneVariance shared targetSpecific

/-- **Population-specific rare variants at shared loci.**
    A gene may be important for a trait in all populations,
    but the specific damaging variants differ because rare
    mutations are recent and population-specific.

    Model: gene-level variance = v_shared + v_pop_specific.
    Both populations have positive gene-level variance (the gene
    matters in both), but the population-specific components may differ.

    Derived: both gene-level variances are strictly greater than
    the shared component alone, demonstrating that population-specific
    rare variants contribute genuine additional signal in each population.
    A PGS trained in EUR captures v_shared + v_eur_specific but only
    v_shared transfers to AFR, missing v_afr_specific entirely. -/
theorem populationGeneVariance_gt_shared
    (shared specific : ℝ) (h_specific : 0 < specific) :
    shared < populationGeneVariance shared specific := by
  unfold populationGeneVariance Descent.Core.sum
  linarith

/-- A positive target-specific component makes the shared transfer fraction strictly
smaller than one. -/
theorem crossPopulationGeneTransferFraction_lt_one
    (shared targetSpecific : ℝ)
    (h_shared : 0 < shared) (h_target : 0 < targetSpecific) :
    crossPopulationGeneTransferFraction shared targetSpecific < 1 := by
  unfold crossPopulationGeneTransferFraction populationGeneVariance Descent.Core.sum
  rw [div_lt_one (by linarith)]
  linarith

/-- With positive shared variance, full gene-level transfer occurs exactly when the target
has no population-specific variance component. -/
theorem crossPopulationGeneTransferFraction_eq_one_iff
    (shared targetSpecific : ℝ) (h_shared : 0 < shared) :
    crossPopulationGeneTransferFraction shared targetSpecific = 1 ↔ targetSpecific = 0 := by
  unfold crossPopulationGeneTransferFraction populationGeneVariance Descent.Core.sum
  constructor
  · intro h
    by_cases h_denom : shared + targetSpecific = 0
    · rw [h_denom, div_zero] at h
      norm_num at h
    · have h_eq : shared = shared + targetSpecific := (div_eq_one_iff_eq h_denom).1 h
      linarith
  · rintro rfl
    simp [ne_of_gt h_shared]

/-- Number of distinct causal signals across two populations after shared signals are
counted only once. -/
def distinctSignalCount (eur afr shared : ℕ) : ℕ :=
  eur + afr - shared

/-- **Inclusion-exclusion on signal counts.**
    Model: each population has `n_signals` independent signals at a locus, of
    which `n_shared` are shared, so the union of distinct signals is
    `n_eur + n_afr - n_shared`.

    What is proved is that the union is at least as large as either population's
    count. `≤`, not `<`: when one population's signals are all shared
    (`n_afr = n_shared`) the union equals `n_eur` exactly, so "exceeds" would be
    false. `omega` on three naturals.

    What is **not** proved: that conditional analysis in one population cannot
    discover all causal variants. No analysis, no discovery and no conditioning
    appears in the statement — only counts. Whether a population-specific
    signal count is evidence of allelic heterogeneity is a modelling claim this
    theorem does not reach. -/
theorem eurSignalCount_le_distinctSignalCount
    (n_signals_eur n_signals_afr n_shared : ℕ)
    (h_shared_le_afr : n_shared ≤ n_signals_afr) :
    n_signals_eur ≤ distinctSignalCount n_signals_eur n_signals_afr n_shared := by
  unfold distinctSignalCount
  omega

/-- The distinct cross-population signal count is at least the AFR signal count when
every shared signal is present in EUR. -/
theorem afrSignalCount_le_distinctSignalCount
    (n_signals_eur n_signals_afr n_shared : ℕ)
    (h_shared_le_eur : n_shared ≤ n_signals_eur) :
    n_signals_afr ≤ distinctSignalCount n_signals_eur n_signals_afr n_shared := by
  unfold distinctSignalCount
  omega

end AllelicHeterogeneity


/-!
## Architecture Convergence

Under shared environments and gene flow, genetic architectures
may converge, improving portability over time.
-/

section ArchitectureConvergence

/-!
### Derivation: fstMigrationDriftEquilibrium = 1/(1 + 4·Ne·m) from migration-drift balance

The island model equilibrium Fst is already derived in two places:

1. **PortabilityDrift.lean**: `fstMigrationDriftEquilibrium` is derived from the
   migration-drift fixed point equation. At equilibrium, the increase in Fst from
   drift (ΔFst_drift = (1 - Fst)/(2N)) balances the decrease from migration
   (ΔFst_migration = -m·Fst·(2 - m)), yielding Fst_eq = 1/(1 + 4Nm).

2. **PopulationGeneticsFoundations.lean**: `fstMigrationDriftEquilibrium` provides the same
   formula with additional properties (positivity, monotonicity in migration).

The definition below is identical to both. We prove this equality explicitly.
-/

/-- **One generation of gene flow against drift**, in the architecture file's
argument order.

This is `Descent.ibdFlowStep` with the homogenising force taken to be
migration: `F` is the probability that two gene copies from the same population
are identical by descent, drift adds `(1 - F)/(2 Nₑ)` and migration removes
`2 m F`.  It is written here, rather than only in `PortabilityDrift`, because
the obligation to derive `fstMigrationDriftEquilibrium` belongs to the file that states it;
`geneFlowFstStep_eq_ibdFlowStep` records that it is the same map.

Composition convention: drift and gene flow are added, not composed, which is
the weak-migration/large-`Nₑ` first-order model.  The unlinearised multiplicative
recursion `islandFstMultiplicativeStep` has a different fixed point.

    Empirical status: **VALIDATED**, including the argument
    forwarding (`validation/empirical/simcov/battery_bulk14.py`).
    Wright-Fisher forward simulation, 4000 loci, 300 replicate populations, one
    generation of drift plus gene flow from a fixed source pool, `F` read as
    `1 - H/H_ancestral`:

      Ne     rate     this def   simulated            sems
      200    0.002     0.07045   0.07050 ± 0.00028     0.15
      500    0.005     0.02602   0.02599 ± 0.00010     0.23
      200    0.010     0.05502   0.05497 ± 0.00022     0.22

    The forwarding is the point of the test. This definition's signature is
    `(m Ne F)` while the `ibdFlowStep` it delegates to is `(Ne rate F)`, so the
    first two arguments are exchanged in the call and a wrapper that failed to
    exchange them would be indistinguishable by eye. The battery calls this
    definition at its OWN order with the rate and `Ne` five orders apart: a
    transposed forwarding would return 205.61, 72.20 and 25.88 against a
    measurement near 0.05. The forwarding is correct, and it is now correct for
    a reason that a reader can check against numbers.

    Power: the prediction spans 0.026 to 0.070 across the design. -/
noncomputable def geneFlowFstStep (m Ne F : ℝ) : ℝ :=
  Portability.ibdFlowStep Ne m F

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem geneFlowFstStep_at_reference_point :
    geneFlowFstStep (1 / 4) 1 (1 / 2) = 1 / 2 := by
  norm_num [geneFlowFstStep, Portability.ibdFlowStep]


/-- One quantity, one map. -/
theorem geneFlowFstStep_eq_ibdFlowStep (m Ne F : ℝ) :
    geneFlowFstStep m Ne F = Portability.ibdFlowStep Ne m F := rfl

/-- **`fstMigrationDriftEquilibrium` is the fixed point of gene flow against drift.**
Migration homogenises at rate `2m` per pair and drift re-creates identity at
rate `1/(2 Nₑ)`; balancing them forces `F = 1/(1 + 4 Nₑ m)`.  The formula is
derived here, not stipulated: no other constant satisfies this. -/
theorem equilibriumFst_isFixedPoint (m Ne : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    geneFlowFstStep m Ne (Portability.fstMigrationDriftEquilibrium Ne m) = Portability.fstMigrationDriftEquilibrium Ne m :=
  Portability.ibdFlowStep_fixedPoint Ne m hNe hm

/-- Equilibrium FST strictly decreases as a nonnegative migration rate increases. -/
theorem fstMigrationDriftEquilibrium_lt_of_migration_lt (m₁ m₂ Ne : ℝ)
    (h_Ne : 0 < Ne) (h_m₁ : 0 ≤ m₁)
    (h_m : m₁ < m₂) :
    Portability.fstMigrationDriftEquilibrium Ne m₂ < Portability.fstMigrationDriftEquilibrium Ne m₁ := by
  unfold Portability.fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith


/-!
### Derivation: portabilityFromArchitecture = rg² × (1 - Fst) × tagging_ratio

The portability ratio R²_target / R²_source decomposes into three multiplicative
factors. This decomposition follows from the covariance model of PGS transfer:

**Step 1: Cross-population covariance decomposition.**
  R²_target = [Cov(PGS, Y_target)]² / [Var(PGS) × Var(Y_target)]

The cross-population covariance Cov(PGS, Y_target) factorizes because PGS weights
are fixed from the source GWAS while genotype-phenotype associations in the target
depend on allele frequencies and LD:

  Cov(PGS, Y_target) = rg × Cov_source × freq_correlation × ld_overlap

where:
- **rg** (genetic correlation): bounds the cross-population genetic covariance
  via Cauchy-Schwarz. If Cov_g(source, target) = rg × √(Vg_s × Vg_t), then
  the transferable signal is scaled by rg. (See GeneticArchitectureDiscovery.lean:
  `genetic_correlation_bounded` for the Cauchy-Schwarz bound.)

- **freq_correlation ≈ (1 - Fst)**: allele frequency divergence reduces the
  covariance between source PGS weights and target genotypes. The per-locus
  contribution is E[β × G_target] ∝ β × 2p_target, and the correlation between
  source and target allele frequencies is (1 - Fst). (See PortabilityDrift.lean:
  `covarianceRetentionFactorFromFst`.)

- **ld_overlap ≈ tagging_ratio**: the fraction of causal-variant LD captured
  by GWAS tag SNPs in the target population. Different LD patterns mean the
  tag SNP may not proxy the causal variant as well. (See PortabilityDrift.lean:
  `ldOverlapFromSharedLD`.)

**Step 2: Why the factors multiply.**
Frequency divergence and LD decay are independent processes:
- Frequency changes are driven by per-locus drift (a function of Fst).
- LD differences are driven by recombination and demographic history.

Because they act on orthogonal aspects of the covariance (per-locus variance
scaling vs. tag-causal correlation), their effects multiply. This is formalized
in PortabilityDrift.lean as `covarianceRetention`:
  covarianceRetention freq_corr ld_overlap = freq_corr × ld_overlap
                                           = (1 - Fst) × shared_LD

**Step 3: Squaring gives the R² ratio.**
Since R² ∝ Cov², the rg factor enters squared:
  R²_target / R²_source = rg² × (1 - Fst) × tagging_ratio

(The (1 - Fst) and tagging_ratio terms are already ratios of variance components,
so they enter linearly rather than squared in the R² ratio.)

This matches the already-derived `covarianceDivergenceFromRetention` in
PortabilityDrift.lean, which shows divergence = 1 - (1 - Fst) × shared_LD,
so retention = (1 - Fst) × shared_LD = (1 - Fst) × tagging_ratio.
-/

/-- **Portability prediction from architecture parameters.**
    Given M_eff, r_g, FST, and tagging efficiency,
    we can predict R²_target / R²_source. -/
noncomputable def portabilityFromArchitecture
    (rg fst tagging_ratio : ℝ) : ℝ :=
  rg^2 * (1 - fst) * tagging_ratio

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem portabilityFromArchitecture_at_reference_point :
    portabilityFromArchitecture (1 / 2) (1 / 2) (1 / 2) = 1 / 16 := by
  unfold portabilityFromArchitecture
  norm_num

/-- **portabilityFromArchitecture factors through covarianceRetention.**
    The (1 - Fst) × tagging_ratio component equals the covariance retention
    derived in PortabilityDrift.lean from the independence of allele frequency
    drift and LD decay. This connects the architecture-level formula to the
    derivation chain: covarianceRetention → covarianceDivergenceFromRetention. -/
theorem portabilityFromArchitecture_eq_rg_sq_mul_retention
    (rg fst tagging_ratio : ℝ) :
    portabilityFromArchitecture rg fst tagging_ratio =
      rg ^ 2 * Portability.covarianceRetention (Portability.covarianceRetentionFactorFromFst fst)
        (Portability.ldOverlapFromSharedLD tagging_ratio) := by
  unfold portabilityFromArchitecture Portability.covarianceRetention Portability.covarianceRetentionFactorFromFst
    Portability.ldOverlapFromSharedLD Descent.Core.product Descent.Core.complement Descent.Core.identifiedWith
  ring

/-- **Portability equals rg² × (1 - divergence), where divergence is derived.**
    covarianceDivergenceFromRetention fst tagging = 1 - (1-fst)×tagging,
    so retention = 1 - divergence = (1-fst)×tagging. This shows portability
    is rg² × (1 - covarianceDivergenceFromRetention). -/
theorem portabilityFromArchitecture_from_divergence
    (rg fst tagging_ratio : ℝ) :
    portabilityFromArchitecture rg fst tagging_ratio =
      rg^2 * (1 - Portability.covarianceDivergenceFromRetention fst tagging_ratio) := by
  unfold portabilityFromArchitecture Portability.covarianceDivergenceFromRetention
    Portability.covarianceRetention Portability.covarianceRetentionFactorFromFst Portability.ldOverlapFromSharedLD Descent.Core.product Descent.Core.complement Descent.Core.identifiedWith
  ring

/-- Architecture portability is zero exactly when cross-population effect correlation
vanishes, differentiation is complete, or the target tags none of the signal. -/
theorem portabilityFromArchitecture_eq_zero_iff (rg fst tagging_ratio : ℝ) :
    portabilityFromArchitecture rg fst tagging_ratio = 0 ↔
      rg = 0 ∨ fst = 1 ∨ tagging_ratio = 0 := by
  unfold portabilityFromArchitecture
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sq_eq_zero_iff.mp h)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr h)
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- With no differentiation and perfect tagging, portability is exactly the squared
cross-population genetic correlation. -/
@[simp] theorem portabilityFromArchitecture_perfect_tagging (rg : ℝ) :
    portabilityFromArchitecture rg 0 1 = rg ^ 2 := by
  unfold portabilityFromArchitecture
  ring

/-- Portability is bounded by rg². -/
theorem portability_bounded_by_rg_sq
    (rg fst tagging_ratio : ℝ)
    (h_fst : 0 ≤ fst)
    (h_tag : 0 ≤ tagging_ratio) (h_tag_le : tagging_ratio ≤ 1) :
    portabilityFromArchitecture rg fst tagging_ratio ≤ rg^2 := by
  unfold portabilityFromArchitecture
  have h1 : (1 - fst) * tagging_ratio ≤ 1 := by
    nlinarith [mul_nonneg h_fst h_tag]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left h1 (sq_nonneg rg)

end ArchitectureConvergence

theorem expectedFreqDiffSq_uses_hwe (fst p0 : ℝ) :
    PopGen.expectedFreqDiffSq fst p0 = fst * genotypeVarianceHWE p0 := by
  unfold PopGen.expectedFreqDiffSq genotypeVarianceHWE Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring

/-- **The `p (1 - p)` in the drift variance is half the diploid genotype variance.**
`AncestrySpecificArchitecture.driftVariance` is `p₀ (1 - p₀) · F_ST`, the ancestral
heterozygosity that has become between-population variance. Its heterozygosity factor is
`genotypeVarianceHWE` on the allele scale rather than the dosage scale, which is exactly
one `ploidy` apart, and writing it inline left that scale choice free. -/
theorem driftVariance_uses_genotypeVarianceHWE (p0 fst : ℝ) :
    PopGen.driftVariance p0 fst = genotypeVarianceHWE p0 * fst / Descent.Core.ploidy := by
  unfold PopGen.driftVariance genotypeVarianceHWE Descent.Core.ploidy Descent.Core.hweHeterozygosity Descent.Core.ploidy
  ring

end Descent.PopGen
