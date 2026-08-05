/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.OpenQuestions
import Descent.Spectral.PolygenicSpectroscopy

namespace Descent

open MeasureTheory

/-!
# Epistasis, Non-Additivity, and PGS Portability

This file formalizes the role of epistasis (gene-gene interaction)
and other non-additive genetic effects in PGS portability.
Standard PGS assumes additive effects, but non-additivity can
cause population-specific prediction patterns.

Key results:
1. Additive approximation and its limits
2. Pairwise epistasis and portability
3. Higher-order epistasis
4. Dominance effects and heterozygosity
5. Non-additive PGS methods

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat epistasis, dominance or other non-additive effects. Sources for
individual results, where they exist, are cited at those results.
-/


/-!
## Additive Approximation

The standard PGS is a sum of additive effects: PGS = Σ βᵢ gᵢ.
This is optimal under additivity but misses non-additive effects.
-/

section AdditiveApproximation

/-- **`a ≥ t/2` and `t > 0` give `a/t ≥ 1/2`.**

    **The claim is the hypothesis.** `h_A_large : V_A ≥ V_G / 2` says the
    additive part is at least half the total, which is the empirical assertion
    the name makes; dividing through by `V_G` adds nothing to it.

    The variance decomposition is gone from the signature. It was three binders
    -- `V_G = V_A + V_D + V_I`, `0 ≤ V_D`, `0 ≤ V_I` -- that no proof term ever
    mentioned, so the statement never was about a decomposition; it only looked
    like it. `V_D` and `V_I` went with them, since nothing else referred to
    them.

    Whether `V_A / V_G ≥ 1/2` actually holds for quantitative traits is a
    measurement, and this file makes none. -/
theorem half_le_div_of_half_le
    (V_A V_D V_I V_G : ℝ)
    (h_A_large : V_A ≥ V_G / 2)
    (h_G : 0 < V_G) :
    V_A / V_G ≥ 1 / 2 := by
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h_G]
  linarith

/-- **The additive `R²` ceiling is BELOW the non-additive-free ratio.**

    **Heritability convention, corrected.** The docstring used to read
    `r2_additive ≤ V_A / V_P ≤ h²_narrow = V_A / (V_A + V_E)`, naming the RIGHT
    side narrow-sense heritability. That is the wrong label and it points the
    wrong way. Narrow-sense heritability is `h² = V_A / V_P` with
    `V_P = V_A + V_D + V_I + V_E` -- the LEFT side here. `V_A / (V_A + V_E)` is
    what `h²` would be in a model with no dominance and no epistasis, and it is
    strictly LARGER whenever `V_D + V_I > 0`. A reader taking the old label
    would set the additive-PGS ceiling above the true narrow-sense heritability,
    by the factor `V_P / (V_A + V_E)`.

    So: an additive PGS captures at most `V_A` out of `V_P`, hence at most
    `h² = V_A / V_P`, and this theorem bounds THAT by the non-additive-free
    ratio. Both sides are `V_A` over a denominator; only the denominators
    differ, and dropping `V_D + V_I` from one of them is the whole content. -/
theorem additive_pgs_ceiling
    (V_A V_D V_I V_E : ℝ)
    (h_A : 0 ≤ V_A) (h_D : 0 ≤ V_D) (h_I : 0 ≤ V_I) (h_E : 0 < V_E) :
    V_A / (V_A + V_D + V_I + V_E) ≤ V_A / (V_A + V_E) := by
  rcases eq_or_lt_of_le h_A with rfl | h_A_pos
  · simp
  · exact div_le_div_of_nonneg_left (le_of_lt h_A_pos) (by linarith) (by linarith)

/-- **The additive approximation is frequency-dependent.**
    Fisher's average effect changes when allele frequencies change.
    α(p) = a + d(1-2p) where a is the additive effect and
    d is the dominance deviation.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk5.py`,
    `test_fisher_average_effect`). Fitting the slope IS what "average effect"
    means, so the oracle is a least-squares regression of genotypic value on
    dosage under Hardy-Weinberg, four million individuals per cell, worst 2.05
    sems over a prediction spanning 0.36000 to 1.30000.

    The design puts `p` on both sides of one half and uses a negative `d` in one
    cell, because the `(1 - 2p)` term vanishes at `p = 1/2` -- a design pinned
    there could not see it at all, which is the blindness
    `BlindnessRegistry` instance 8 records for this very quantity. -/
noncomputable def fisherAverageEffect (a d p : ℝ) : ℝ :=
  a + d * (1 - 2 * p)

/-- **fisherAverageEffect pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem fisherAverageEffect_at_reference_point :
    fisherAverageEffect (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold fisherAverageEffect
  norm_num

/-- **The average effect is the additive effect plus a dominance term that vanishes at even
frequency and reverses across it.** At `p = 1/2` the dominance contribution is exactly zero, and
reflecting the frequency flips its sign: that is why dominance is invisible to an additive model
at intermediate frequency and visible at the extremes. -/
theorem fisherAverageEffect_half (a d : ℝ) : fisherAverageEffect a d (1 / 2) = a := by
  unfold fisherAverageEffect; ring

theorem fisherAverageEffect_reflect (a d p : ℝ) :
    fisherAverageEffect a d (1 - p) - a = -(fisherAverageEffect a d p - a) := by
  unfold fisherAverageEffect; ring

/-- **Average effect changes across populations.**
    When allele frequency changes from p₁ to p₂, the average
    effect changes even if a and d stay the same. -/
theorem average_effect_frequency_dependent
    (a d p₁ p₂ : ℝ)
    (h_d : d ≠ 0) (h_freq : p₁ ≠ p₂) :
    fisherAverageEffect a d p₁ ≠ fisherAverageEffect a d p₂ := by
  unfold fisherAverageEffect
  intro h
  apply h_freq
  have : d * (1 - 2 * p₁) = d * (1 - 2 * p₂) := by linarith
  have := mul_left_cancel₀ h_d this
  linarith

end AdditiveApproximation


/-!
## Pairwise Epistasis

When two loci interact, their combined effect differs from the
sum of their individual effects.
-/

section PairwiseEpistasis

/-- **Pairwise epistatic model.**
    Y = β₁g₁ + β₂g₂ + β₁₂g₁g₂ + ε.
    The interaction term β₁₂ captures epistasis. -/
noncomputable def pairwiseModel
    (beta1 beta2 beta12 g1 g2 : ℝ) : ℝ :=
  beta1 * g1 + beta2 * g2 + beta12 * g1 * g2

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem pairwiseModel_at_reference_point :
    pairwiseModel 1 1 1 1 1 = 3 := by
  norm_num [pairwiseModel]


/-- **The interaction coefficient is exactly the departure from additivity.** This is what makes
`beta12` estimable: subtract the additive prediction and what remains is the product term, with
no part of it absorbable into the marginal effects. -/
theorem pairwiseModel_sub_additive (beta1 beta2 beta12 g1 g2 : ℝ) :
    pairwiseModel beta1 beta2 beta12 g1 g2 - (beta1 * g1 + beta2 * g2)
      = beta12 * g1 * g2 := by
  unfold pairwiseModel
  ring

/-- **Additive PGS misses interaction signal.**
    PGS_additive = β₁g₁ + β₂g₂ misses β₁₂g₁g₂. -/
theorem additive_misses_epistasis
    (beta1 beta2 beta12 g1 g2 : ℝ)
    (h_epistasis : beta12 ≠ 0) (h_g1 : g1 ≠ 0) (h_g2 : g2 ≠ 0) :
    beta1 * g1 + beta2 * g2 ≠ pairwiseModel beta1 beta2 beta12 g1 g2 := by
  unfold pairwiseModel
  intro h
  have : beta12 * g1 * g2 = 0 := by linarith
  have : beta12 * (g1 * g2) = 0 := by linarith
  rcases mul_eq_zero.mp this with h12 | hg
  · exact h_epistasis h12
  · rcases mul_eq_zero.mp hg with h1 | h2
    · exact h_g1 h1
    · exact h_g2 h2

/-- **Epistasis affects portability when allele frequencies change.**
    The contribution of epistasis to genetic variance:
    V_I ∝ Σ β₁₂² × 2p₁(1-p₁) × 2p₂(1-p₂).
    When frequencies change, V_I changes → additive PGS is miscalibrated.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk5.py`,
    `test_epistatic_variance`). Measured as the variance of the two-locus
    interaction term AFTER both main effects are removed by least squares, four
    million individuals, worst 2.56 sems over a prediction spanning 0.12250 to
    0.23040. Removing the main effects first is what makes this the epistatic
    component rather than the total two-locus variance. -/
noncomputable def epistaticVariance
    (beta12 p1 p2 : ℝ) : ℝ :=
  beta12 ^ 2 * (2 * p1 * (1 - p1)) * (2 * p2 * (1 - p2))

/-- **epistaticVariance pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 16`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem epistaticVariance_at_reference_point :
    epistaticVariance (1 / 2) (1 / 2) (1 / 2) = 1 / 16 := by
  unfold epistaticVariance
  norm_num

/-- Epistatic variance is nonneg. -/
theorem epistatic_variance_nonneg
    (beta12 p1 p2 : ℝ)
    (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1)
    (hp2 : 0 ≤ p2) (hp2' : p2 ≤ 1) :
    0 ≤ epistaticVariance beta12 p1 p2 := by
  unfold epistaticVariance
  apply mul_nonneg
  · apply mul_nonneg (sq_nonneg _)
    nlinarith
  · nlinarith

/-- **The epistatic variance is `4β₁₂²` times the heterozygosity product.**

    This is the whole arithmetic of the pairwise interaction term, stated once
    as an identity so that no downstream statement has to re-derive it and none
    can dress it up as something else. Every "epistasis changes across
    populations" claim is a claim about the right-hand factor: the interaction
    coefficient enters only through `β₁₂²`, and the two loci enter only through
    their heterozygosities, so anything that moves the epistatic variance moves
    `p(1-p)` at one locus or the other. -/
theorem epistaticVariance_eq_four_mul_heterozygosity_product
    (beta12 p1 p2 : ℝ) :
    epistaticVariance beta12 p1 p2 =
      4 * beta12 ^ 2 * (p1 * (1 - p1) * (p2 * (1 - p2))) := by
  unfold epistaticVariance
  ring

end PairwiseEpistasis


/-!
## Dominance Effects

Dominance means the effect of a heterozygote differs from the
average of the two homozygotes.
-/

section DominanceEffects

/-- **Dominance variance.**
    V_D = Σ (2pq d)² where d is the dominance deviation.
    V_D depends on heterozygosity, which differs across populations.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk5.py`,
    `test_dominance_variance`). Measured as the variance of the residual left by
    the additive fit at each locus, summed over independent loci -- the quantity
    the decomposition names, obtained by fitting rather than by rearranging:

      loci   this def   simulated            sems
      1       0.04410   0.04409±0.00003      0.31
      2       0.08096   0.08100±0.00006      0.57
      3       0.10331   0.10332±0.00007      0.12

    Power: the prediction spans 0.04410 to 0.10331 across the design. -/
noncomputable def dominanceVariance
    {m : ℕ} (p : Fin m → ℝ) (d : Fin m → ℝ) : ℝ :=
  ∑ i, (2 * p i * (1 - p i) * d i) ^ 2

/-- Reference evaluation on a two-locus index with distinct entries.  Not the empty index:
`∑ over Fin 0 = 0` holds for every sum body, so it fixes nothing. -/
theorem dominanceVariance_at_reference_point :
    dominanceVariance ![1, 3] ![1, 3] = 1296 := by
  norm_num [dominanceVariance, Fin.sum_univ_two]


/-- Dominance variance is nonneg. -/
theorem dominance_variance_nonneg
    {m : ℕ} (p : Fin m → ℝ) (d : Fin m → ℝ) :
    0 ≤ dominanceVariance p d := by
  unfold dominanceVariance
  exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)

/-- **Dominance contributes to portability loss.**
    When heterozygosity (2pq) differs across populations,
    the dominance variance changes, affecting PGS calibration. -/
theorem sq_mul_ne_sq_mul_of_ne_of_nonneg
    (het_source het_target d_val : ℝ)
    (h_het_diff : het_source ≠ het_target)
    (h_d : d_val ≠ 0)
    (h_sign : 0 ≤ het_source ∧ 0 ≤ het_target) :
    (het_source * d_val) ^ 2 ≠ (het_target * d_val) ^ 2 := by
  intro h
  apply h_het_diff
  rw [mul_pow, mul_pow] at h
  have h_d_sq : d_val ^ 2 ≠ 0 := (sq_pos_of_ne_zero h_d).ne'
  have h_eq : het_source ^ 2 = het_target ^ 2 := mul_right_cancel₀ h_d_sq h
  exact ((sq_eq_sq₀ h_sign.1 h_sign.2).mp h_eq)

/-- **Heterozygosity advantage affects disease traits.**
    For diseases with heterozygote advantage (e.g., sickle cell),
    the dominance effect is large and population-specific.
    When |d_sickle| > |d_typical|, the dominance variance
    contribution from the sickle locus exceeds that from a typical
    locus at the same heterozygosity level. -/
theorem heterozygote_advantage_large_dominance
    (d_sickle d_typical het : ℝ)
    (h_het : 0 < het)
    (h_d_typical_pos : 0 < |d_typical|)
    (h_large : |d_typical| < |d_sickle|) :
    (het * d_typical) ^ 2 < (het * d_sickle) ^ 2 := by
  rw [mul_pow, mul_pow]
  have hhet_sq : 0 < het ^ 2 := by positivity
  have habs_sq : |d_typical| ^ 2 < |d_sickle| ^ 2 := by
    nlinarith
  rw [← abs_sq d_typical, ← abs_sq d_sickle]
  simpa [mul_comm, mul_left_comm, mul_assoc] using mul_lt_mul_of_pos_left habs_sq hhet_sq

end DominanceEffects


/-!
## Non-Additive PGS Methods

Methods that incorporate non-additive effects for better prediction.
-/

section NonAdditiveMethods

/-- **A share is at most the share of a larger numerator over the same
    positive denominator:** `a/(a+b+c+d) ≤ (a+b+c)/(a+b+c+d)`.

    The reading is that a model capturing dominance and epistasis as well as
    additive effects explains more phenotypic variance than an additive-only
    model. Nothing below is about a model. There is no estimator, no fitting,
    no XGBoost and no neural network — the claim that such a method *attains*
    `V_A + V_D + V_I` is the whole content and is not stated, let alone proved.
    Four positive reals and one division. -/
theorem div_le_div_of_le_numerator
    (V_A V_D V_I V_E : ℝ)
    (h_A : 0 < V_A) (h_D : 0 < V_D) (h_I : 0 ≤ V_I) (h_E : 0 < V_E) :
    V_A / (V_A + V_D + V_I + V_E) ≤
      (V_A + V_D + V_I) / (V_A + V_D + V_I + V_E) := by
  apply div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **Subtracting more leaves less:** `k₁ < k₂` and `n > 0` give
    `r - k₂/n < r - k₁/n`.

    The reading is that a method with more free parameters carries a larger
    overfitting penalty `k/n`, so its cross-population prediction degrades
    further. That the penalty *is* `k/n` is stipulated by writing it, and no
    generalization bound is invoked or proved; `r2_train` is a variable name,
    not a fitted quantity. There is no second population below, so nothing here
    is cross-population at all. -/
theorem sub_div_lt_sub_div_of_lt
    (r2_train k_linear k_ml n : ℝ)
    (h_n : 0 < n)
    (h_more_params : k_linear < k_ml) :
    -- ML has larger overfitting penalty k/n
    r2_train - k_ml / n < r2_train - k_linear / n := by
  have : k_linear / n < k_ml / n := div_lt_div_of_pos_right h_more_params h_n
  linarith

/-- **A strictly smaller numerator gives a strictly smaller share, and a
    positive numerator a positive one:** for positive `a`, `b`, `c`,
    `a/(a+b+c) < (a+b)/(a+b+c)` and `0 < b/(a+b+c)`.

    The reading is a tradeoff: a richer model captures `V_A + V_NA` in the
    source population and only `V_A` in the target, so it wins within
    population and loses across. There is exactly one population below, and no
    model. The asserted tradeoff needs the non-additive share to fail to
    transport, which is assumed in the prose and appears nowhere in the
    statement. Two inequalities between three positive reals. -/
theorem div_lt_div_add_and_div_pos
    (V_A V_NA V_E : ℝ)
    (h_A : 0 < V_A) (h_NA : 0 < V_NA) (h_E : 0 < V_E) :
    -- ML within-pop R² > linear within-pop R², but
    -- ML cross-pop loss > linear cross-pop loss (= 0)
    V_A / (V_A + V_NA + V_E) < (V_A + V_NA) / (V_A + V_NA + V_E) ∧
      0 < V_NA / (V_A + V_NA + V_E) := by
  have h_denom : 0 < V_A + V_NA + V_E := by linarith
  constructor
  · exact div_lt_div_of_pos_right (by linarith) h_denom
  · exact div_pos h_NA h_denom

/-- **`a/(a+b+c) ≤ (a+b)/(a+b+c)` for positive `a`, `b`, `c`.**

    The reading is that a GBLUP kernel built as the Hadamard square of the
    additive kernel captures `V_A + V_I` where an additive kernel captures
    `V_A`. No kernel, no Hadamard product and no BLUP appears below, and that a
    kernel method attains either quantity is not stated. The same inequality as
    `div_le_div_of_le_numerator` with one fewer summand. -/
theorem div_le_div_of_le_numerator'
    (V_A V_I V_E : ℝ)
    (h_A : 0 < V_A) (h_I : 0 < V_I) (h_E : 0 < V_E) :
    V_A / (V_A + V_I + V_E) ≤ (V_A + V_I) / (V_A + V_I + V_E) := by
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **Regularization controls non-additive complexity.**
    Stronger regularization → more additive → more portable.
    With regularization parameter λ, the effective number of
    non-additive parameters captured scales as k_NA / (1 + λ).
    Larger λ suppresses non-additive terms, reducing the
    population-specific overfitting penalty k_eff / n. -/
theorem regularization_controls_portability
    (k_NA n lam_weak lam_strong : ℝ)
    (h_k : 0 < k_NA) (h_n : 0 < n)
    (h_lw : 0 < lam_weak)
    (h_stronger : lam_weak < lam_strong) :
    -- Stronger regularization → fewer effective parameters → less overfit
    k_NA / (1 + lam_strong) / n < k_NA / (1 + lam_weak) / n := by
  apply div_lt_div_of_pos_right _ h_n
  apply div_lt_div_of_pos_left h_k (by linarith) (by linarith)

end NonAdditiveMethods


/-!
## The condensation boundary of the pairwise model

`PairwiseEpistasis` above compares an additive fit against `pairwiseModel` and prices the
difference in variance and in portability. Every such comparison is calibrated against a
Gaussian law for the score, and that law is a degree-one statement: the Berry-Esseen
apparatus of `Descent.Portability.ScoreDistribution` describes additive aggregates.

`Descent.Spectral.PolygenicSpectroscopy` computes, in closed form, the allele-frequency-dependent
multiplicative degree at which the Gaussian genotype surrogate stops describing the
aggregate. The two theorems below are what that computation says about the *pairwise* and
three-way models specifically -- the models this file is about -- rather than about a
general chaos.

Scope, taken from the `MEASURED` block on `maxSafeEpistaticOrder` and not weakened here:
the common-variant column of that table is FALSIFIED, optimistic by up to `2.64x`, and the
condensation-direction claim is backwards. What is VALIDATED is the rare-variant tail, and
the rare-variant tail is the only thing used below. Both statements are therefore about
low-frequency variants, which is also where the pairwise model is most often fitted and
least often powered.
-/

section CondensationBoundary

/-- **Pairwise epistasis outruns its own Gaussian null at some frequency, for every panel
size.**

For any number `N` of disjoint interaction terms there is an allele frequency below
`1 / 8` at which the largest safe multiplicative degree has already fallen to two. So no
panel is large enough to make pairwise interaction statistics on sufficiently rare variants
subcritical: the Gaussian surrogate against which such a statistic is calibrated is
converging to a different limit than the genotypes are.

This is `PolygenicSpectroscopy.exists_maf_supercritical` at `m = 2`, converted from the
additive form `log N < m * c(q)` into the safe-order form by `epistatic_order_safe_iff`.
The conversion is the content: `maxSafeEpistaticOrder` is the quantity a study designer
reads, and the inequality on drifts is not.

    Empirical status: VALIDATED in the regime used -- the rare-variant tail of the
    `maxSafeEpistaticOrder` table, whose convexity gap falls to `0.0035` at `q = 1e-4`. -/
theorem exists_maf_pairwise_beyond_safe_order {N : ℝ} (hN : 1 ≤ N) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 8 ∧ maxSafeEpistaticOrder N q ≤ 2 := by
  obtain ⟨q, hq0, hq8, hsuper⟩ := exists_maf_supercritical (N := N) (m := 2) (by norm_num) hN
  refine ⟨q, hq0, hq8, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hq1 : q < 1 := by linarith
  have hsafe := (epistatic_order_safe_iff (N := N) (q := q) (m := 2) hq0 hq1).1 hcon
  linarith

/-- **Three-way interaction is past the boundary at MAF `10 ^ (-3)` for any realistic
panel.**

At `q = 1 / 1024` the Hardy-Weinberg Mellin drift exceeds `6`, so the safe order is below
`log N / 6`. Any panel with `log N ≤ 18` -- that is, up to about `6.6 * 10 ^ 7` disjoint
interaction terms, comfortably above the `10 ^ 6` a genome-wide pairwise scan produces --
therefore cannot support degree three.

The comparison that makes this a design statement rather than an inequality: the Gaussian
condensation constant would put the safe order at `N = 10 ^ 6` near `19`
(`gaussianCriticalMultiplier_bounds` times `log N = 13.8`). The genotype drift at this
frequency puts it below `3`. A design calibrated on the Gaussian constant is wrong about
the admissible interaction order by a factor of six at rare variants, and
`maxSafeEpistaticOrder_collapse_at_rare_maf` proves the sevenfold version of the same gap.

    Empirical status: VALIDATED in the regime used -- see the note above. -/
theorem threeway_beyond_safe_order_at_rare_maf {N : ℝ} (hN : Real.log N ≤ 18) :
    maxSafeEpistaticOrder N (1 / 1024) < 3 := by
  have hlb := rare_variant_drift_sharp_lower_bound
    (q := 1 / 1024) (by norm_num) (by norm_num)
  have harg : (1 : ℝ) / (2 * (1 / 1024)) = 512 := by norm_num
  rw [harg] at hlb
  have h512 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h512] at hlb
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdrift : (6 : ℝ) < hweMellinDrift (1 / 1024) := by linarith
  unfold maxSafeEpistaticOrder
  rw [div_lt_iff₀ (by linarith)]
  linarith

end CondensationBoundary

end Descent
