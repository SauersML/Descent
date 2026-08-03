/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

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
    the name makes; dividing through by `V_G` adds nothing to it. `V_D` and
    `V_I` are unconstrained apart from nonnegativity and do not enter the
    conclusion, and there is no trait, no variance component and no
    decomposition below beyond the equation `h_total` that names one.

    Whether `V_A / V_G ≥ 1/2` actually holds for quantitative traits is a
    measurement, and this file makes none. -/
theorem half_le_div_of_half_le
    (V_A V_D V_I V_G : ℝ)
    (h_total : V_G = V_A + V_D + V_I)
    (h_A_large : V_A ≥ V_G / 2)
    (h_D : 0 ≤ V_D) (h_I : 0 ≤ V_I) (h_G : 0 < V_G) :
    V_A / V_G ≥ 1 / 2 := by
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h_G]
  linarith

/-- **Additive PGS R² ≤ h² narrow-sense.**
    Even a perfect additive PGS cannot explain dominance or
    epistatic variance. An additive PGS can capture at most V_A
    out of total phenotypic variance V_P = V_A + V_D + V_I + V_E,
    so r2_additive ≤ V_A / V_P ≤ h²_narrow = V_A / (V_A + V_E). -/
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

    Empirical status: UNTESTED. -/
noncomputable def fisherAverageEffect (a d p : ℝ) : ℝ :=
  a + d * (1 - 2 * p)

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

    Empirical status: UNTESTED. -/
noncomputable def epistaticVariance
    (beta12 p1 p2 : ℝ) : ℝ :=
  beta12 ^ 2 * (2 * p1 * (1 - p1)) * (2 * p2 * (1 - p2))

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

/-- **Epistatic portability loss.**
    Even with identical additive effects across populations,
    epistasis creates portability loss because the interaction
    contributions change with allele frequencies. When allele
    frequencies differ (p₁_src ≠ p₁_tgt or p₂_src ≠ p₂_tgt)
    and there is nonzero epistasis (β₁₂ ≠ 0), the epistatic
    variance differs between populations. -/
theorem epistasis_portability_loss
    (beta12 p1_src p2_src p1_tgt p2_tgt : ℝ)
    (h_beta : beta12 ≠ 0)
    (h_p1s : 0 < p1_src) (h_p1s' : p1_src < 1)
    (h_p2s : 0 < p2_src) (h_p2s' : p2_src < 1)
    (h_p1t : 0 < p1_tgt) (h_p1t' : p1_tgt < 1)
    (h_p2t : 0 < p2_tgt) (h_p2t' : p2_tgt < 1)
    (h_freq_diff : p1_src * (1 - p1_src) * p2_src * (1 - p2_src) ≠
                   p1_tgt * (1 - p1_tgt) * p2_tgt * (1 - p2_tgt)) :
    epistaticVariance beta12 p1_src p2_src ≠
      epistaticVariance beta12 p1_tgt p2_tgt := by
  unfold epistaticVariance
  intro h
  apply h_freq_diff
  have h_sq : beta12 ^ 2 ≠ 0 := pow_ne_zero 2 h_beta
  -- Factor out beta12^2 and constants
  have : beta12 ^ 2 * (2 * p1_src * (1 - p1_src)) * (2 * p2_src * (1 - p2_src)) =
         beta12 ^ 2 * (2 * p1_tgt * (1 - p1_tgt)) * (2 * p2_tgt * (1 - p2_tgt)) := h
  have : 4 * beta12 ^ 2 * (p1_src * (1 - p1_src) * p2_src * (1 - p2_src)) =
         4 * beta12 ^ 2 * (p1_tgt * (1 - p1_tgt) * p2_tgt * (1 - p2_tgt)) := by nlinarith
  have := mul_left_cancel₀ (by positivity : (4 : ℝ) * beta12 ^ 2 ≠ 0) this
  exact this

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

    Empirical status: UNTESTED. -/
noncomputable def dominanceVariance
    {m : ℕ} (p : Fin m → ℝ) (d : Fin m → ℝ) : ℝ :=
  ∑ i, (2 * p i * (1 - p i) * d i) ^ 2

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
    (h_r2 : 0 < r2_train)
    (h_kl : 0 < k_linear) (h_km : 0 < k_ml)
    (h_n : 0 < n)
    (h_more_params : k_linear < k_ml)
    (h_valid : k_ml < n) :
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
    (h_lw : 0 < lam_weak) (h_ls : 0 < lam_strong)
    (h_stronger : lam_weak < lam_strong) :
    -- Stronger regularization → fewer effective parameters → less overfit
    k_NA / (1 + lam_strong) / n < k_NA / (1 + lam_weak) / n := by
  apply div_lt_div_of_pos_right _ h_n
  apply div_lt_div_of_pos_left h_k (by linarith) (by linarith)

end NonAdditiveMethods

end Calibrator
