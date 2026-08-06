/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Meta.Informal
import Descent.Portability.PortabilityDrift

namespace Descent.Program

open MeasureTheory
open scoped ProbabilityTheory
open PopGen.TransportedMetrics (r2FromSignalVariance)

/-!
# Formal Proofs for Open Questions in PGS Portability

Reference: Wang et al. (2026), "Three open questions in polygenic score portability",
Nature Communications 17:942.  DOI: 10.1038/s41467-026-68565-3

## The Three Open Questions

1. **Genetic distance poorly predicts individual-level accuracy.**
2. **Portability trends are trait-specific** (immune traits decay fastest).
3. **Portability depends on the prediction metric** (precision vs recall diverge).

We also formalize sub-questions:
4. Environmental variance heterogeneity confounds R² comparisons.
5. Winner's curse × allelic turnover amplification.
6. PGS variance non-monotonicity for immune traits.
7. Heterozygosity-driven predictor variance increase with distance.

## What this file proves, and the gaps that are now objects

THE FILE IS NAMED FOR QUESTIONS IT DOES NOT ANSWER.  Almost every docstring below already
says so, in the corpus's usual careful way: `omitted_variable_bias` proves "that adding a
nonzero product to a number changes it", `af_variance_fraction_lt_one` proves that one of
four positive fractions is under one, `sum_lt_sum_of_net_gain_on_subset` has "no loci and
no variance" in it.  Each of those sentences is a gap, and each was prose -- unqueryable,
uncountable, and impossible to fail on.

The `informal_lemma` and `informal_definition` commands from `Descent.Meta.Informal` turn
them into objects.  A gap records a stable tag, the prose, and the fully qualified names it
WAITS ON; it adds no constant to the environment, so no proof can cite it.
`#informal_report` then answers the question this file could not: which of these has
acquired all of its prerequisites while nobody was looking.

**A gap is filed under the fully qualified name its closing declaration will have.**  That
is the convention that makes deps compose: an `informal_lemma` may depend on an
`informal_definition`, and when someone writes the real declaration under that name the dep
closes by itself and the gap object is deleted.  A dep that names something absent is
indistinguishable from a typo -- `Descent.lean` says exactly this about failed searches --
so the names below are the names the corpus WOULD use, written once, in one place.

**Five withdrawn claims below now carry `@[withdrawn]`.**  Each is a docstring that already
began "Previously `X`, documented as ..." and then explained why the old heading was false.
That is the discipline `Descent.lean` asks for in capitals -- withdraw in place and quote
what it used to say -- and it was already being followed here.  What the attribute adds is
that the retraction can be listed.
-/

/-!
## Open Question 1: Law of Total Variance and Weak Predictability

Individual-level squared prediction error ε²ᵢ has high within-group variance.
The law of total variance implies R²(ε², genetic_distance) is small whenever
the conditional variance E[Var(ε²|D)] dominates Var(E[ε²|D]).
-/

section Question1

theorem scalar_summary_insufficient_for_accuracy
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (distance accuracy : V →ₗ[ℝ] ℝ)
    (hnot : ¬ ∃ c : ℝ, accuracy = c • distance) :
    ∀ θ : V, ∃ θ' : V, distance θ' = distance θ ∧ accuracy θ' ≠ accuracy θ :=
  Foundations.scalar_summary_insufficient_of_not_scalar_factorization distance accuracy hnot

/-! The conditional-noise-floor and Gaussian-floor bounds on the explainable fraction answer
this question, and they are `explainable_fraction_bound_of_conditional_noise_floor` and
`explainable_fraction_bound_of_conditional_gaussian_floor` in
`Descent.Foundations.TransportIdentities`.

They were also restated here, suffixed `_exact`, each copying its original's eight-line
measure-theoretic binder block and citing the original as its proof.  Both live in the
`Descent` namespace already, so the copies renamed nothing and reached no reader the
originals did not; what they added was a second block of hypotheses to keep in step. -/

/-- **The between-group fraction of an assumed variance decomposition is at most one.**

    Previously `law_of_total_variance_r2_bound`, documented as the law of total variance
    identity `Var(Z) = E[Var(Z|D)] + Var(E[Z|D])`. The law is not proved here: it is the
    hypothesis `h_decomp`, three unrelated reals related by an equation. What remains after
    it is assumed is that a nonnegative summand's share of a positive total is at most one,
    which is `div_le_one` plus `linarith`.

    The heading `law_of_total_variance_r2_bound` is withdrawn rather than deleted, and is
    recorded as such: see `@[withdrawn]` on this declaration.

    The real conditional-variance statements in this file are
    `explainable_fraction_bound_of_conditional_noise_floor_exact` and its Gaussian
    companion, which work against `conditionalVariance` and `conditionalMean` on an actual
    measure rather than against three scalars. Those are where the law of total variance
    is genuinely used. -/
@[withdrawn "OQ-1-law-of-total-variance-r2-bound"
  "the name said the law of total variance was proved here; the law is the \
   hypothesis h_decomp, three free reals related by an equation, and what is \
   proved is div_le_one"]
theorem between_group_variance_fraction_le_one
    (varZ eVarZgivenD varEZgivenD : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_eVar_nonneg : 0 ≤ eVarZgivenD)
    :
    varEZgivenD / varZ ≤ 1 := by
  rw [div_le_one h_varZ_pos, h_decomp]
  linarith

/-- **The complementary share of a two-part decomposition:** if
    `varZ = a + b` with `varZ > 0` and `a ≥ (1 - δ)·varZ`, then `b/varZ ≤ δ`.

    Read as the law of total variance, `a` is `E[Var(Z|D)]`, `b` is
    `Var(E[Z|D])`, and the conclusion is a bound on `R²(Z,D)`. That reading is
    supplied entirely by `h_decomp`, which stipulates the decomposition: there
    is no `Z`, no `D`, no conditional expectation and no `R²` below, and the
    law of total variance is not invoked, only assumed in the shape of an
    equation between three reals. A measured `δ` for a fitted model is not an
    instance of this, whose variables are free. -/
theorem div_le_of_ge_one_sub_mul
    (varZ eVarZgivenD varEZgivenD δ : ℝ)
    (h_decomp : varZ = eVarZgivenD + varEZgivenD)
    (h_varZ_pos : 0 < varZ)
    (h_within_dominates : eVarZgivenD ≥ (1 - δ) * varZ)
    :
    varEZgivenD / varZ ≤ δ := by
  have h1 : varEZgivenD = varZ - eVarZgivenD := by linarith
  rw [h1, sub_div, div_self (h_varZ_pos.ne')]
  linarith [le_div_iff₀ h_varZ_pos |>.mpr (by linarith : (1 - δ) * varZ ≤ eVarZgivenD)]


/-- **SES explains as much as genetic distance.**
    If both covariates explain comparable fractions and their total
    is bounded, each individual fraction must be small. -/
theorem comparable_covariates_both_small
    (r2_d r2_s B ε : ℝ)
    (h_comparable : r2_d ≤ r2_s + ε)
    (h_sum_bound : r2_d + r2_s ≤ B)
    :
    r2_d ≤ (B + ε) / 2 := by
  linarith

/-- **Question 1, stated about a measure instead of about three free reals.**

What this section has is `scalar_summary_insufficient_for_accuracy`, which says a scalar
summary cannot determine accuracy unless accuracy factors through it -- two linear
functionals on a vector space, with no distance, no individual and no population in it --
together with three lemmas that stipulate a variance decomposition as an equation between
three reals and read the conclusion off it.

The statement the section is named for is: let `D` be the σ-algebra generated by a
genetic-distance covariate and `L` the individual squared prediction error; then
`Var(E[L|D])/Var(L)` is small exactly when the conditional variance dominates.

WHAT MAKES THIS WORTH RECORDING AS AN OBJECT is that nothing is missing.
`total_variance_decomposition_subsigma` IS the law of total variance, proved against
`conditionalVariance` and `conditionalMean` on an actual measure, and the explainable
fraction already has its conditional-noise-floor bound.  So the scalar lemmas here are not
standing in for a theorem the corpus cannot reach.  They are standing in for one nobody has
written, and closing this means exhibiting the σ-algebra, not proving anything new about
variance. -/
informal_lemma "OQ-1-individual-accuracy-vs-distance"
  Descent.Program.explainable_fraction_of_individual_error_given_distance
  [Descent.Foundations.total_variance_decomposition_subsigma,
   Descent.Foundations.explainable_fraction_bound_of_conditional_noise_floor,
   Descent.Foundations.conditionalVariance,
   Descent.Foundations.scalar_summary_insufficient_of_not_scalar_factorization]

end Question1


/-!
## Open Question 2: Trait-Specific Portability

Trait-specific portability is the exact consequence of locuswise transport
heterogeneity together with trait-specific baseline weights.
-/

section Question2

variable {J L : Type*}
variable [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **Heterozygosity increases toward 0.5.**
    Under divergent selection, allele freq p moves from extreme to
    intermediate → H = 2p(1-p) increases.
    This drives PGS variance increase for immune traits. -/
theorem two_mul_one_sub_lt_of_lt_of_le_half
    (p₁ p₂ : ℝ)
    (hp₁_lt_p₂ : p₁ < p₂)
    (hp₂_le_half : p₂ ≤ 1 / 2) :
    2 * p₁ * (1 - p₁) < 2 * p₂ * (1 - p₂) := by
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]

/-- **PGS variance increases when the large-effect locus gains more heterozygosity than the
small-effect locus loses.** This is the mechanism proposed for WBC/lymphocyte count.

    A statement taking `h_net : v_large_t - v_large_s > v_small_s - v_small_t` and
    concluding `v_large_s + v_small_s < v_large_t + v_small_t` would be no mechanism at all:
    those two inequalities are the *same inequality rearranged*, so the hypothesis would be
    the conclusion and the proof the rearrangement.

    This one cannot be rearranged into its own hypotheses, because the hypotheses
    are about **effect sizes and heterozygosities separately** and the conclusion is about
    the variance sum they generate. A locus at frequency `p` with effect `β` contributes
    `2β²p(1-p)` to score variance, so the claim has content precisely when the weighting by
    `β²` is doing work: the large-effect locus must actually be the larger-effect one
    (`hβ`), and its heterozygosity gain must exceed the small locus's loss
    (`hlarge_gains_more`). Neither follows from the conclusion.

    Use `two_mul_one_sub_lt_of_lt_of_le_half` to discharge the gain hypothesis from allele
    frequencies moving toward `1/2` under divergent selection, which is the biological step
    the prose describes. -/
theorem two_term_weighted_sum_lt_of_larger_weight_gain
    (βL βS pL pL' pS pS' : ℝ)
    (hβ : βS ^ 2 ≤ βL ^ 2)
    (hβL : 0 < βL ^ 2)
    (hsmall_loses : pS' * (1 - pS') ≤ pS * (1 - pS))
    (hlarge_gains_more :
      pS * (1 - pS) - pS' * (1 - pS') < pL' * (1 - pL') - pL * (1 - pL)) :
    2 * βS ^ 2 * (pS * (1 - pS)) + 2 * βL ^ 2 * (pL * (1 - pL)) <
      2 * βS ^ 2 * (pS' * (1 - pS')) + 2 * βL ^ 2 * (pL' * (1 - pL')) := by
  have hloss_nonneg : 0 ≤ pS * (1 - pS) - pS' * (1 - pS') := by linarith
  -- The small locus's loss is weighted by the smaller squared effect ...
  have hweighted : βS ^ 2 * (pS * (1 - pS) - pS' * (1 - pS'))
      ≤ βL ^ 2 * (pS * (1 - pS) - pS' * (1 - pS')) :=
    mul_le_mul_of_nonneg_right hβ hloss_nonneg
  -- ... and that loss is strictly smaller than the large locus's gain.
  have hgain : βL ^ 2 * (pS * (1 - pS) - pS' * (1 - pS'))
      < βL ^ 2 * (pL' * (1 - pL') - pL * (1 - pL)) :=
    (mul_lt_mul_iff_right₀ hβL).mpr hlarge_gains_more
  nlinarith [hweighted, hgain]

/-- **PGS variance increase + effect decorrelation = compounded R² drop.**
    R² ∝ Cov²/(Var_PGS · Var_Y). If Var_PGS↑ and Cov↓, R² drops faster
    than either mechanism alone. -/
theorem compound_r2_drop
    (cov_s cov_t vpgs_s vpgs_t vy : ℝ)
    (h_cov_drop : cov_t ^ 2 < cov_s ^ 2)
    (h_vpgs_up : vpgs_s < vpgs_t)
    (h_vy_pos : 0 < vy)
    (h_vpgs_pos : 0 < vpgs_s) :
    cov_t ^ 2 / (vpgs_t * vy) < cov_s ^ 2 / (vpgs_s * vy) := by
  have h_denom_s : 0 < vpgs_s * vy := mul_pos h_vpgs_pos h_vy_pos
  have h_denom_t : 0 < vpgs_t * vy := mul_pos (by linarith) h_vy_pos
  have h_denom_up : vpgs_s * vy < vpgs_t * vy := mul_lt_mul_of_pos_right h_vpgs_up h_vy_pos
  have key : cov_t ^ 2 * (vpgs_s * vy) ≤ cov_t ^ 2 * (vpgs_t * vy) := by
    apply mul_le_mul_of_nonneg_left (le_of_lt h_denom_up) (sq_nonneg cov_t)
  calc cov_t ^ 2 / (vpgs_t * vy)
      ≤ cov_t ^ 2 / (vpgs_s * vy) := by
        rwa [div_le_div_iff₀ h_denom_t h_denom_s]
    _ < cov_s ^ 2 / (vpgs_s * vy) :=
        div_lt_div_of_pos_right h_cov_drop h_denom_s

/-- **Sign-flip probability.**
    Effect in target ~ N(ρ·β, σ²). Z-score for sign concordance = ρ·β/σ.
    Smaller ρ → smaller z-score → more sign flips.
    (31.7% for lymphocyte vs 9.6% for triglycerides in Wang et al.) -/
theorem sign_flip_z_decreases_with_turnover
    (β σ ρ₁ ρ₂ : ℝ)
    (hβ : 0 < β) (hσ : 0 < σ)
    (hρ : ρ₂ < ρ₁) :
    ρ₂ * β / σ < ρ₁ * β / σ :=
  div_lt_div_of_pos_right (by nlinarith) hσ

end Question2


/-!
## Open Question 3: Metric-Specific Portability

Different metrics are different functionals of the same transported law.
For continuous traits this is the exact MSE identity; for binary traits it is
the exact prevalence-recall-FPR formula for precision.
-/

section Question3

variable {Ω : Type*}

theorem binary_precision_formula_exact (c : Foundations.ConfusionMatrix) :
    Foundations.ConfusionMatrix.precision c =
      (Foundations.ConfusionMatrix.prevalence c * Foundations.ConfusionMatrix.recallRate c) /
        (Foundations.ConfusionMatrix.prevalence c * Foundations.ConfusionMatrix.recallRate c +
          (1 - Foundations.ConfusionMatrix.prevalence c) * Foundations.ConfusionMatrix.fpr c) :=
  Foundations.ConfusionMatrix.precision_eq_prevalence_recall_fpr c

/-- **Precision-recall divergence is consistent.**
    There exist parameter configurations with fixed prevalence and fixed target
    precision where recall changes and the induced false-positive rate changes
    exactly as required by the precision identity. -/
theorem precision_recall_divergence_exists :
    ∃ (π p r₁ r₂ f₁ f₂ : ℝ),
      0 < π ∧ π < 1 ∧
      0 < p ∧ p < 1 ∧
      0 < r₁ ∧ r₁ < r₂ ∧ r₂ ≤ 1 ∧
      f₁ = π * r₁ * (1 - p) / ((1 - π) * p) ∧
      f₂ = π * r₂ * (1 - p) / ((1 - π) * p) ∧
      (π * r₁) / (π * r₁ + (1 - π) * f₁) = p ∧
      (π * r₂) / (π * r₂ + (1 - π) * f₂) = p := by
  refine ⟨1 / 2, 1 / 2, 1 / 4, 1 / 3,
    (1 / 2) * (1 / 4) * (1 - 1 / 2) / ((1 - 1 / 2) * (1 / 2)),
    (1 / 2) * (1 / 3) * (1 - 1 / 2) / ((1 - 1 / 2) * (1 / 2)), ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa using
      (Foundations.ConfusionMatrix.constant_precision_of_fpr_choice
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 4) (by norm_num) (by norm_num) (by norm_num))
  · simpa using
      (Foundations.ConfusionMatrix.constant_precision_of_fpr_choice
        (π := 1 / 2) (p := 1 / 2) (r := 1 / 3) (by norm_num) (by norm_num) (by norm_num))

/-- **The confusion matrix a transported law produces at a threshold.**

`Foundations.ConfusionMatrix` is a record of four counts, and every theorem about it is an
algebraic identity between them.  Nothing in the corpus BUILDS one: there is no map from a
score distribution and a threshold to the four cells, so no confusion-matrix theorem is
currently a theorem about a population.

That map is the single missing construction between the metric identities and the
metric-specific portability claim below, and it is why that claim is blocked rather than
merely unwritten. -/
informal_definition "OQ-3-confusion-matrix-of-law"
  Descent.Foundations.ConfusionMatrix.confusionMatrixOfTransportedLaw
  [Descent.Foundations.ConfusionMatrix.precision_eq_prevalence_recall_fpr]

/-- **Question 3 proper: two metrics that ORDER two populations oppositely.**

What this section has is the exact precision identity, which is an algebraic fact about one
confusion matrix, and `precision_recall_divergence_exists`, which exhibits two operating
points on ONE population with equal precision and different recall.  Neither is the
paper's claim.

The claim is that portability is metric-dependent: there is a source law, a target law and
a single decision rule under which one metric ranks the target above the source and another
ranks it below.  That is a statement about two confusion matrices, and it needs the
transported law to produce them rather than four free reals to satisfy an identity.

The ingredients are present: the precision identity holds of any confusion matrix, and the
corpus transports a law between populations.  What is absent is a confusion matrix DERIVED
from a transported law at a threshold, which is the one construction between the two
halves. -/
informal_lemma "OQ-3-metric-order-reversal"
  Descent.Program.metrics_order_populations_oppositely
  [Descent.Foundations.ConfusionMatrix.precision_eq_prevalence_recall_fpr,
   Descent.Foundations.ConfusionMatrix.confusionMatrixOfTransportedLaw]

end Question3


/-!
## Open Question 4: Environmental Variance Heterogeneity
-/

section Question4

/-- **`Vg/(Vg + Ve)` decreases as `Ve` grows.**

    Read as `R²` under identical genetics, or as heritability, or as the attainable ceiling:
    they are one inequality. `Descent.GeneEnvironmentInterplay.env_variance_reduces_h2` is the
    same statement, kept there because that file's discussion needs it locally; this is not an
    independent result and should not be cited as one. -/
theorem env_variance_lowers_r2
    (Vg Ve₁ Ve₂ : ℝ)
    (hVg : 0 < Vg) (hVe₁ : 0 < Ve₁)
    (h_more_env : Ve₁ < Ve₂) :
    Vg / (Vg + Ve₂) < Vg / (Vg + Ve₁) := by
  apply div_lt_div_of_pos_left hVg (by linarith) (by linarith)

/-- **A nonzero product added to a coefficient changes it.**

    Kept under its old name because the arithmetic is what the surrounding discussion of
    omitted-variable bias appeals to, but read it as what it is: no regression, no
    estimator and no correlation appears in the statement. That the naive coefficient on
    genetic distance picks up exactly `β_ses · ρ` when SES is omitted is the standard
    omitted-variable formula, asserted in this docstring and derived nowhere in this
    corpus. What is proved is that adding a nonzero product to a number changes it. -/
@[withdrawn "OQ-4-omitted-variable-bias-name"
  "the name claims the omitted-variable formula; no regression, estimator or \
   correlation appears in the statement, and the formula is asserted in the \
   docstring and derived nowhere"]
theorem omitted_variable_bias
    (β_true β_ses ρ : ℝ)
    (h_ses : β_ses ≠ 0) (h_corr : ρ ≠ 0) :
    β_true + β_ses * ρ ≠ β_true := by
  intro h
  have : β_ses * ρ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact h_ses h
  · exact h_corr h

/-- **Portability drop decomposes into genetic + environmental parts.** -/
theorem both_le_of_add_eq_of_nonneg
    (r2s r2t Δg Δe : ℝ)
    (h_eq : r2s - r2t = Δg + Δe)
    (hΔg : 0 ≤ Δg) (hΔe : 0 ≤ Δe) :
    Δg ≤ r2s - r2t ∧ Δe ≤ r2s - r2t := by
  constructor <;> linarith

/-- **The least-squares coefficient of one covariate given a set of regressors.**

The corpus has covariance and variance on a measure, and it has several named quantities
that are described in prose as regression coefficients, but it has no definition of one:
no projection onto a span, no normal equations, no `argmin` over a coefficient vector.
Everything that reads as a regression statement in this file therefore reads it in the
docstring and proves arithmetic in the body.

This is the definition the corpus would need, and it is the reason the omitted-variable
gap below is BLOCKED rather than merely unwritten. -/
informal_definition "OQ-4-least-squares-coefficient"
  Descent.Foundations.leastSquaresCoefficient
  [Descent.Foundations.covariance_add_right, Descent.Foundations.variance_add_exp]

/-- **The omitted-variable formula, which this section asserts and the corpus derives
nowhere.**

`omitted_variable_bias` says its own docstring: that the naive coefficient on genetic
distance picks up exactly `β_ses · ρ` when SES is omitted "is the standard omitted-variable
formula, asserted in this docstring and derived nowhere in this corpus".  What is proved is
that adding a nonzero product to a number changes it.

The claim is `β_naive = β_true + β_ses · ρ`, where `ρ` is the coefficient of the omitted
regressor on the included one.  It cannot be stated at all until a least-squares
coefficient exists, which is why it depends on the informal definition above and not on
anything in this file.  Until then, `comparable_covariates_both_small` -- the section's
"SES explains as much as genetic distance" -- is `linarith` on two hypotheses, and the
paper's confounding argument is not in the corpus. -/
informal_lemma "OQ-4-omitted-variable-formula"
  Descent.Foundations.omitted_regressor_shifts_least_squares_coefficient
  [Descent.Foundations.leastSquaresCoefficient,
   Descent.Foundations.covariance_add_right]

end Question4


/-!
## Open Question 5: Winner's Curse × Allelic Turnover
-/

section Question5

/-- **Winner's curse prediction error model.**
    GWAS estimate β_hat = β_true + δ (inflation).
    Target effect β_t = ρ * β_true (turnover).
    Prediction error = β_hat - β_t = (1-ρ)*β + δ.
    Prediction error decomposes into turnover + inflation. -/
theorem prediction_error_decomp (β δ ρ : ℝ) :
    (β + δ) - ρ * β = (1 - ρ) * β + δ := by ring

/-- Prediction error is positive when both components are positive. -/
theorem prediction_error_positive
    (β δ ρ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hρ : ρ ≤ 1) :
    0 < (1 - ρ) * β + δ := by
  have : 0 ≤ (1 - ρ) * β := mul_nonneg (by linarith) (le_of_lt hβ)
  linarith

/-- **Winner's curse is worse with more turnover.**
    Relative error = ((1-ρ)β + δ) / (ρβ). As ρ↓, this increases. -/
theorem relative_error_increases_with_turnover
    (β δ ρ₁ ρ₂ : ℝ) (hβ : 0 < β) (hδ : 0 < δ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hρ : ρ₂ < ρ₁) :
    ((1 - ρ₁) * β + δ) / (ρ₁ * β) < ((1 - ρ₂) * β + δ) / (ρ₂ * β) := by
  rw [div_lt_div_iff₀ (mul_pos hρ₁ hβ) (mul_pos hρ₂ hβ)]
  nlinarith [sq_nonneg β, sq_nonneg δ, mul_pos hρ₁ hβ, mul_pos hρ₂ hβ,
             mul_pos hβ hδ, mul_pos hρ₁ hδ, mul_pos hρ₂ hδ]

/-- **Multiplying by a positive number preserves strict order:**
    `H_s < H_t` gives `β²·H_s < β²·H_t`.

    Read as genetics the two sides are one locus's contribution to score
    variance at two heterozygosities. That reading is the choice to call the
    factors `beta_sq` and `H`; no locus, no genotype and no score appears
    below. -/
theorem mul_lt_mul_left_of_pos'
    (beta_sq H_s H_t : ℝ) (hβ : 0 < beta_sq) (hH : H_s < H_t) :
    beta_sq * H_s < beta_sq * H_t :=
  mul_lt_mul_of_pos_left hH hβ

/-- **The winner's curse, as the conditional expectation it is.**

`prediction_error_decomp` is `ring`, `prediction_error_positive` is `linarith`, and
`relative_error_increases_with_turnover` is a division inequality.  All three treat the
inflation `δ` as a free positive real GIVEN, which is the whole content of the winner's
curse assumed rather than derived: the curse is that `E[β̂ | |β̂| > threshold] > β`, an
inequality about a conditional expectation under a selection event, and no threshold, no
selection event and no conditioning appears in this section.

`PopGen.winners_curse_overestimates` is the corpus's nearest statement and it is in the
population-genetics layer, where it belongs.  The gap here is the composition: the curse's
`δ` and the turnover's `ρ` acting on ONE effect, so that the amplification this section is
named for -- winner's curse TIMES allelic turnover -- is a theorem rather than the product
of two free parameters. -/
informal_lemma "OQ-5-winners-curse-times-turnover"
  Descent.Program.selection_inflation_amplified_by_turnover
  [Descent.PopGen.winners_curse_overestimates,
   Descent.PopGen.winners_curse_worse_near_threshold,
   Descent.Program.relative_error_increases_with_turnover]

end Question5


/-!
## Open Question 6: PGS Variance Non-Monotonicity
-/

section Question6

/-- **Variance decomposition into large and small effect groups.** -/
theorem variance_decomposition
    {m : ℕ} (w : Fin m → ℝ) (S : Finset (Fin m)) :
    ∑ i, w i = ∑ i ∈ S, w i + ∑ i ∈ Sᶜ, w i := by
  rw [← Finset.sum_union disjoint_compl_right]
  congr 1; exact (Finset.union_compl S).symm

/-- **A net gain on a subset raises the total:** if the increase over `S`
    exceeds the decrease over `Sᶜ`, then `∑ w_s < ∑ w_t`.

    The genetics reading partitions loci into a highlighted set and its
    complement and reads the sums as predictor variance. Below there are no
    loci and no variance — `w_s` and `w_t` are arbitrary functions into `ℝ`,
    not constrained to be nonnegative or to be per-locus contributions of
    anything. Splitting a sum over a finset and its complement, plus
    `linarith`. -/
theorem sum_lt_sum_of_net_gain_on_subset
    {m : ℕ} (w_s w_t : Fin m → ℝ) (S : Finset (Fin m))
    (h_net :
      (∑ i ∈ S, w_t i) - (∑ i ∈ S, w_s i) >
        (∑ i ∈ Sᶜ, w_s i) - (∑ i ∈ Sᶜ, w_t i)) :
    ∑ i, w_s i < ∑ i, w_t i := by
  rw [variance_decomposition w_s S, variance_decomposition w_t S]
  linarith

/-- **Score variance as a function of loci, so that the two sums above are about it.**

`variance_decomposition` splits a sum over a finset and its complement.
`sum_lt_sum_of_net_gain_on_subset` says its own docstring: "there are no loci and no
variance -- `w_s` and `w_t` are arbitrary functions into `ℝ`, not constrained to be
nonnegative or to be per-locus contributions of anything".

`Portability.pgsVarianceFromHet` is the per-locus contribution at ONE locus, and it exists.
What is absent is the sum of it over a locus index -- a score variance as a function of an
effect vector and a frequency vector -- which is the object both lemmas above are written
as though they were about.  With it,
`two_term_weighted_sum_lt_of_larger_weight_gain` becomes a statement about immune-trait
score variance; without it, it is arithmetic in a section named for a mechanism. -/
informal_definition "OQ-6-score-variance-over-loci"
  Descent.Portability.pgsVarianceOverLoci
  [Descent.Portability.pgsVarianceFromHet]

/-- **PGS variance non-monotonicity, as a statement about a score.**

The section claims that predictor variance rises with genetic distance for immune traits
while falling for others, which is a non-monotonicity IN THE DISTANCE.  Nothing below has a
distance in it: the two lemmas compare two frequency vectors with no ordering between them
and no map from a distance to either.

Two things are needed and one of them is not hard: the score variance above, and a
frequency path indexed by distance.  The corpus has the second in substance --
`presentDayPGSVariance` is already a function of `fstT` -- so this gap is the composition of
two things it has, at a locus index it does not. -/
informal_lemma "OQ-6-pgs-variance-nonmonotone-in-distance"
  Descent.Program.pgsVarianceOverLoci_nonmonotone_in_distance
  [Descent.Portability.pgsVarianceOverLoci,
   Descent.Portability.presentDayPGSVariance,
   Descent.Program.two_mul_one_sub_lt_of_lt_of_le_half,
   Descent.Program.two_term_weighted_sum_lt_of_larger_weight_gain]

end Question6


/-!
## Open Question 7: Brier Score Uncertainty Varies with Prevalence
-/

section Question7

/-- **Brier score irreducible noise = π(1-π).**
    This varies with prevalence, making R² comparisons across groups misleading. -/
theorem brier_uncertainty_formula (π : ℝ) :
    π * (1 - π) = -(π - 1/2) ^ 2 + 1/4 := by ring

/-- **Brier uncertainty is maximized at π = 1/2.** -/
theorem brier_uncertainty_max_at_half (π : ℝ) :
    π * (1 - π) ≤ 1/4 := by nlinarith [sq_nonneg (π - 1/2)]

/-- **Closer to 1/2 ↔ higher uncertainty.** -/
theorem closer_to_half_more_uncertainty
    (π₁ π₂ : ℝ)
    (h_closer : (π₂ - 1/2) ^ 2 < (π₁ - 1/2) ^ 2) :
    π₁ * (1 - π₁) < π₂ * (1 - π₂) := by
  nlinarith [brier_uncertainty_formula π₁, brier_uncertainty_formula π₂]

/-- **Prediction interval width increases as R² decreases.** -/
theorem interval_width_increases
    (r2₁ r2₂ : ℝ)
    (hr2₁ : r2₂ < r2₁) (hr2₁_lt : r2₁ < 1) :
    Real.sqrt (1 - r2₁) < Real.sqrt (1 - r2₂) :=
  Real.sqrt_lt_sqrt (by linarith) (by linarith)

end Question7


/-!
## Portability: the four-factor decomposition

Portability ratio = AF_factor × LD_factor × Effect_factor × Env_factor.
Genetic distance (Fst) captures only the AF factor, explaining why it
poorly predicts individual-level accuracy.
-/

section FourFactorDecomposition

/-- **The four-factor product is strictly below its AF factor alone.**

    Previously `single_factor_insufficient`, "No single factor captures the full ratio".
    Insufficiency of a single factor is a claim about approximation error, or about a
    factor failing to determine the product; neither is stated. What is proved is one
    strict inequality between the product and one of its factors, which is what you get
    from the other three being below one. It supports the surrounding argument — an Fst
    proxy that sees only the AF factor overstates portability — without being that
    argument. -/
@[withdrawn "OQ-four-factor-single-factor-insufficient"
  "the name claimed no single factor captures the full ratio, which is a claim \
   about approximation error; what is proved is one strict inequality between a \
   product and one of its factors"]
theorem four_factor_product_lt_af_factor
    (af ld eff env : ℝ)
    (h_af : 0 < af)
    (h_ld_lt : ld < 1)
    (h_eff : 0 < eff) (h_eff_lt : eff < 1)
    (h_env : 0 < env) (h_env_le : env ≤ 1) :
    af * ld * eff * env < af := by
  have h1 : ld * eff < 1 := by
    calc ld * eff < 1 * eff := mul_lt_mul_of_pos_right h_ld_lt h_eff
      _ = eff := one_mul eff
      _ < 1 := h_eff_lt
  have h2 : ld * eff * env < 1 := by
    calc ld * eff * env < 1 * env := mul_lt_mul_of_pos_right h1 h_env
      _ = env := one_mul env
      _ ≤ 1 := h_env_le
  calc af * ld * eff * env
      = af * (ld * eff * env) := by ring
    _ < af * 1 := mul_lt_mul_of_pos_left h2 h_af
    _ = af := mul_one af

/-- **One positive summand's share of a sum of four positive summands is below one.**

    Previously `genetic_distance_variance_bound`, "R² of genetic distance on portability is
    bounded by the AF variance fraction". No R², no genetic distance and no portability
    appears in the statement, and no bound *by* the AF fraction is proved — what is proved
    is a bound *on* it, namely that it is under one, which holds of any of the four
    fractions and is `div_lt_one`. The variance-decomposition reading, in which these four
    numbers are the variances of independent contributions to portability, is asserted in
    the section prose and formalised nowhere. -/
@[withdrawn "OQ-four-factor-genetic-distance-variance-bound"
  "the name claimed a bound BY the AF variance fraction; what is proved is a \
   bound ON it, namely that it is under one, which holds of any of the four \
   fractions and is div_lt_one"]
theorem af_variance_fraction_lt_one
    (var_af var_ld var_eff var_env : ℝ)
    (h_af : 0 < var_af) (h_ld : 0 < var_ld)
    (h_eff : 0 < var_eff) (h_env : 0 < var_env) :
    var_af / (var_af + var_ld + var_eff + var_env) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- **The four-factor decomposition itself.**

The section prose states that the portability ratio factorises as
`AF × LD × Effect × Env`, and that Fst sees only the first factor.  That product is what
makes the section's argument -- an Fst proxy overstates portability because it omits three
factors below one -- and it is asserted here and derived nowhere.  The two theorems above
take four free reals and prove, respectively, that a product is below one of its factors
and that one of four positive fractions is under one.  Both hold of any four numbers.

Closing this means DERIVING the factorisation from the corpus's own transported metrics:
`presentDayPGSVariance` carries the allele-frequency factor and `r2FromSignalVariance` the
environmental one, so two of the four factors already exist as functions rather than as
letters.  What is absent is the identity that the target-to-source ratio of
`r2FromSignalVariance` equals their product -- at which point the two arithmetic lemmas
above become steps in an argument instead of standing in for it. -/
informal_lemma "OQ-four-factor-decomposition"
  Descent.Program.portabilityRatio_eq_four_factor_product
  [Descent.Portability.presentDayPGSVariance,
   Descent.Portability.pgsVarianceFromHet,
   Descent.PopGen.TransportedMetrics.r2FromSignalVariance,
   Descent.Portability.expectedR2_strictMono_nonneg]

end FourFactorDecomposition


/-!
## Selection-Driven Allelic Turnover Model

Under fluctuating selection across populations, effect sizes at
immune-associated loci change faster than at neutral loci.
-/

section SelectionModel

/-- **Effect retention under selection.**
    ρ ≤ selection correlation. Low selection correlation → low ρ → low portability. -/
theorem mul_sq_le_mul_sq_of_le_of_nonneg
    (r2_src ρ_eff ρ_sel : ℝ)
    (hr2 : 0 ≤ r2_src)
    (h_bound : ρ_eff ≤ ρ_sel)
    (h_eff_nn : 0 ≤ ρ_eff) :
    r2_src * ρ_eff ^ 2 ≤ r2_src * ρ_sel ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ hr2
  exact sq_le_sq' (by linarith) h_bound

/-- **Neutral vs immune portability.**
    Neutral ρ = 1, immune ρ < 1. So neutral R² > immune R² at same distance. -/
theorem neutral_beats_immune
    (r2 ρ : ℝ) (hr2 : 0 < r2)
    (hρ_pos : 0 ≤ ρ) (hρ_lt : ρ < 1) :
    r2 * ρ ^ 2 < r2 * 1 ^ 2 := by
  rw [one_pow]
  apply mul_lt_mul_of_pos_left _ hr2
  nlinarith [sq_abs ρ, sq_nonneg ρ]

/-- **An effect-retention factor `ρ² < 1` strictly lowers target R² at a fixed target Fst.**

    Previously `drift_only_overestimates_immune_portability`, documented as "Under pure
    drift, portability ratio = (1-Fst_T)/(1-Fst_S). This is what Fst predicts." No ratio of
    source to target appears in the conclusion: **both sides are evaluated at `fstT`**, and
    the comparison is between including the turnover factor `ρ²` and omitting it. The
    source Fst enters no term.

    The linter caught it. The hypotheses `0 ≤ fstS` and `fstS < fstT` — the ones that made
    the statement look like a source-versus-target comparison — occurred in no proof term,
    and `fstS` itself occurred nowhere else, so all three are gone from the signature. What
    the theorem says is that a drift-only prediction, which omits `ρ²`, is higher than one
    that includes it; that supports the surrounding claim about immune traits without being
    a statement about genetic distance at all. -/
@[withdrawn "OQ-drift-only-overestimates-immune-portability"
  "the name claimed a source-to-target portability ratio under pure drift; both \
   sides are evaluated at fstT, the source Fst enters no term, and the three \
   hypotheses that made it look like a source-versus-target comparison occurred \
   in no proof term"]
theorem effect_retention_lowers_target_r2_at_fixed_fst
    (V_A V_E fstT ρ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstT : fstT < 1)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    PopGen.TransportedMetrics.r2FromSignalVariance (ρ ^ 2 * Portability.presentDayPGSVariance V_A fstT) V_E <
      PopGen.TransportedMetrics.r2FromSignalVariance (Portability.presentDayPGSVariance V_A fstT) V_E := by
  apply Portability.expectedR2_strictMono_nonneg V_E _ _ hVE
  · exact le_of_lt (mul_pos (sq_pos_of_pos hρ_pos)
      (by unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.product; exact mul_pos hVA (by linarith)))
  · have h_pdv_pos : 0 < Portability.presentDayPGSVariance V_A fstT := by
      unfold Portability.presentDayPGSVariance Portability.pgsVarianceFromHet Descent.Core.product; exact mul_pos hVA (by linarith)
    calc ρ ^ 2 * Portability.presentDayPGSVariance V_A fstT
        < 1 * Portability.presentDayPGSVariance V_A fstT := by
          apply mul_lt_mul_of_pos_right _ h_pdv_pos
          nlinarith [sq_abs ρ, sq_nonneg ρ]
      _ = Portability.presentDayPGSVariance V_A fstT := one_mul _

end SelectionModel


/-!
## LD Decay Interaction with Allelic Turnover

The paper shows that for immune traits, both LD patterns AND allelic effects
change simultaneously. The combined effect is worse than either alone.
We formalize this multiplicative interaction.
-/

section LDTurnoverInteraction

theorem faster_decay_lower_correlation
    (lam_slow lam_fast d : ℝ)
    (hlam_faster : lam_slow < lam_fast)
    (hd_pos : 0 < d) :
    Real.exp (-lam_fast * d) < Real.exp (-lam_slow * d) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- **LD tagging efficiency decays exponentially with genetic distance.**
    ρ²_LD(d) = exp(-λ_LD · d).

    **Attribution, corrected: this is NOT the Ohta-Kimura result**, which the
    docstring previously claimed. Ohta and Kimura (1971) give
    `σ_d² ≈ (10 + ρ)/((2 + ρ)(11 + ρ))` with `ρ = 4·Nₑ·c`, formalized at
    `LDDecayTheory.ohtaKimuraSigmaDSq`; that is HYPERBOLIC in the scaled
    recombination rate, not exponential in it, and so is Sved's
    `r² ≈ 1/(1 + 4·Nₑ·c)`. No published neutral two-locus theory in this
    corpus's reference set predicts an exponential in genetic distance. The
    exponential here is a phenomenological one-parameter chart, and it is only
    that.

    Regime: `d` is genetic distance, `λ_LD` a fitted rate with no derivation.
    Nothing identifies `λ_LD` with `Nₑ` or with a recombination rate, so this
    body cannot be inverted for a demographic parameter.

    Empirical status: **FALSIFIED as a shape**
    (`validation/empirical/popgensel/ldshapecell.py`, cell I). This
    supersedes the LEAD the sibling body `PortabilityDrift.ldCorrelationDecay`
    carried -- the same exponential chart, fitted against the same kind of
    simulated `r²` curve, missing at BOTH ends at 21.7 and 14.2 sems. That run
    was recorded as a lead rather than a verdict for one reason: it carried no
    valid positive control. Cell I supplies exactly that control and changes
    nothing else.

    Both shapes are fitted to the SAME binned msprime `r²` values with a free
    amplitude AND a free rate each, so neither is handicapped and any upward
    bias in the `r²` estimator is common to both. The discrimination is the
    shape, which no estimator convention moves.

    | design | exponential χ²/point | hyperbolic χ²/point | worst exp. residual | worst hyp. |
    |---|---|---|---|---|
    | `Nₑ = 2000`, 4 Mb | 28.49 | 4.16 | 8.87 sems | 3.91 sems |
    | `Nₑ = 5000`, 2 Mb | 79.66 | 1.95 | 12.56 sems | 3.46 sems |

    **The positive control, which is the whole point of this cell.** A fitter
    that prefers the hyperbolic on real data proves nothing unless it prefers the
    EXPONENTIAL on data that is genuinely exponential. Run on a true exponential
    with the same `x` grid and matched per-point noise, the same fitter prefers
    the exponential by a sum-of-squares ratio of 168 and 197. So the preference
    reported above is the data's and not the fitter's, and the lead becomes a
    verdict.

    This does not identify the hyperbolic's fitted rate with `4·Nₑ`: at
    `Nₑ = 5000` the fit returns `b = 6572` against Sved's `20000`. What is
    established is that the decay is hyperbolic in genetic distance and not
    exponential in it, which is what this body gets wrong -- and, as the
    paragraph above already says, no choice of `λ_LD` repairs a two-sided
    failure.

    **The successor is `PopGen.LDDecayTheory.ohtaKimuraSigmaDSq`**, and the
    withdrawal above named none, which leaves a consumer holding a falsified
    shape with nowhere to go. `simcov/battery_sved01.py` puts the same question
    to a forward two-locus Wright-Fisher engine rather than to msprime -- a
    different model class, a different estimator, no binning -- and over
    `ρ = 4·Nₑ·c` from 0.5 to 20 the Ohta-Kimura form MATCHES at worst 1.85 sems
    while this body's exponential shape is FALSIFIED at 6.29 sems and 36%
    relative. The exponential there is fitted to the very curve it is tested
    against, with a free amplitude AND a free rate, and the hyperbola is given
    no fitted constant at all; so the failure cannot be a badly chosen `λ_LD`,
    because it was chosen optimally.

    Sved's `1/(1 + 4·Nₑ·c)` is NOT the successor, and that battery was written
    to make it one. It is falsified at 17.6 sems in the same place, and `E[r²]`
    -- the expectation of the ratio, which is what an `r²` curve looks like a
    curve of -- has no mutation-free equilibrium to measure. -/
@[withdrawn "OQ-2-ld-decay-ohta-kimura-attribution"
  "this body was attributed to Ohta-Kimura; that result is hyperbolic in the \
   scaled recombination rate, and no published neutral two-locus theory in the \
   corpus's reference set predicts an exponential in genetic distance"]
noncomputable def ldTaggingDecay (lam_LD d : ℝ) : ℝ :=
  Real.exp (-lam_LD * d)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ldTaggingDecay_at_reference_point :
    ldTaggingDecay 0 0 = 1 := by
  norm_num [ldTaggingDecay]



/-- **Combined LD + effect turnover portability.**
    Total portability = R²_source · ρ²_LD(d) · ρ²_effect(d). -/
noncomputable def combinedPortability
    (r2_src lam_LD lam_eff d : ℝ) : ℝ :=
  r2_src * ldTaggingDecay lam_LD d * (Real.exp (-lam_eff * d)) ^ 2

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem combinedPortability_at_reference_point :
    combinedPortability 1 0 0 1 = 1 := by
  norm_num [combinedPortability, ldTaggingDecay]



/-- **At distance 0, combined portability equals source R².** -/
theorem combined_portability_at_zero (r2_src lam_LD lam_eff : ℝ) :
    combinedPortability r2_src lam_LD lam_eff 0 = r2_src := by
  unfold combinedPortability ldTaggingDecay
  simp [mul_zero, Real.exp_zero]

/-- **LD-only portability strictly exceeds combined portability at positive distance.**
    Adding effect turnover always makes portability worse. -/
theorem turnover_worsens_ld_only_portability
    (r2_src lam_LD lam_eff d : ℝ)
    (hr2 : 0 < r2_src)
    (hlam_eff : 0 < lam_eff) (hd : 0 < d) :
    combinedPortability r2_src lam_LD lam_eff d <
      r2_src * ldTaggingDecay lam_LD d := by
  unfold combinedPortability
  have h_exp_lt : (Real.exp (-lam_eff * d)) ^ 2 < 1 := by
    have h1 : Real.exp (-lam_eff * d) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith [mul_pos hlam_eff hd]
    have h2 : 0 ≤ Real.exp (-lam_eff * d) := Real.exp_nonneg _
    nlinarith [sq_abs (Real.exp (-lam_eff * d))]
  have h_base_pos : 0 < r2_src * ldTaggingDecay lam_LD d := by
    unfold ldTaggingDecay
    exact mul_pos hr2 (Real.exp_pos _)
  calc r2_src * ldTaggingDecay lam_LD d * (Real.exp (-lam_eff * d)) ^ 2
      < r2_src * ldTaggingDecay lam_LD d * 1 :=
        mul_lt_mul_of_pos_left h_exp_lt h_base_pos
    _ = r2_src * ldTaggingDecay lam_LD d := mul_one _

/-- **Immune portability drops multiplicatively faster.**
    For immune traits (large λ_eff), the combined decay is much faster
    than for neutral traits (small λ_eff). -/
theorem immune_combined_decay_faster
    (r2_src lam_LD lam_eff_neutral lam_eff_immune d : ℝ)
    (hr2 : 0 < r2_src)
    (hlami : lam_eff_neutral < lam_eff_immune)
    (hd : 0 < d) :
    combinedPortability r2_src lam_LD lam_eff_immune d <
      combinedPortability r2_src lam_LD lam_eff_neutral d := by
  unfold combinedPortability
  have h_ld_pos : 0 < r2_src * ldTaggingDecay lam_LD d := by
    unfold ldTaggingDecay; exact mul_pos hr2 (Real.exp_pos _)
  apply mul_lt_mul_of_pos_left _ h_ld_pos
  apply sq_lt_sq'
  · linarith [Real.exp_pos (-lam_eff_immune * d), Real.exp_pos (-lam_eff_neutral * d)]
  · exact faster_decay_lower_correlation lam_eff_neutral lam_eff_immune d hlami hd

/-- **Combined portability, rebuilt on the decay law that survived the test.**

`ldTaggingDecay` is FALSIFIED as a shape, by `ldshapecell.py` cell I, with a valid positive
control: the exponential loses to the hyperbolic at 28.49 against 4.16 and 79.66 against
1.95 χ² per point, while the same fitter prefers the exponential by sum-of-squares ratios
of 168 and 197 on data that is genuinely exponential.  The verdict is the data's and not
the fitter's.

`combinedPortability` is built on it, and so is every theorem in this section.  They are
all still true -- they are statements about `Real.exp` and nothing else -- and they are all
about a chart the corpus has measured and rejected.  The hyperbolic law it lost to is in
the corpus already, as `ohtaKimuraSigmaDSq`.

WHAT IS OPEN is not the falsification, which is settled, but the replacement: the same four
consequences -- value at distance zero, turnover strictly worsening portability, immune
decay faster, and the multiplicative interaction -- proved for a portability built on
`ohtaKimuraSigmaDSq` instead.  Three of the four are monotonicity arguments that a
hyperbolic satisfies as readily as an exponential, so this is a rewrite and not a research
problem, and its being open is the reason a falsified body still has consumers. -/
informal_lemma "OQ-2-portability-on-hyperbolic-decay"
  Descent.Program.hyperbolicCombinedPortability
  [Descent.PopGen.ohtaKimuraSigmaDSq,
   Descent.Program.combinedPortability,
   Descent.Program.turnover_worsens_ld_only_portability,
   Descent.Program.immune_combined_decay_faster]

end LDTurnoverInteraction


/-!
## R² Non-Comparability Across Groups

R² depends on the variance of both predictor and outcome within each group.
When comparing R² across genetic ancestry groups, heterogeneity in both
genetic and environmental variance makes direct comparison misleading.
-/

section R2NonComparability

/-- **R² is not comparable when phenotypic variances differ.**
    Two populations with the same signal but different noise have different R². -/
theorem r2_incomparable_across_groups
    (v_signal v_noise₁ v_noise₂ : ℝ)
    (h_sig : 0 < v_signal)
    (h_n₁ : 0 < v_noise₁) (h_n₂ : 0 < v_noise₂)
    (h_noise_diff : v_noise₁ ≠ v_noise₂) :
    v_signal / (v_signal + v_noise₁) ≠ v_signal / (v_signal + v_noise₂) := by
  intro h_eq
  apply h_noise_diff
  have h_d₁ : (0 : ℝ) < v_signal + v_noise₁ := by linarith
  have h_d₂ : (0 : ℝ) < v_signal + v_noise₂ := by linarith
  have h_cross := (div_eq_div_iff (h_d₁.ne') (h_d₂.ne')).mp h_eq
  nlinarith

/-- **Heteroscedasticity inflates apparent portability loss.**
    If Var(Y) is larger in the target (due to environmental factors),
    R²_target < R²_source even with identical signal. -/
theorem heteroscedasticity_inflates_loss
    (v_sig v_noise_s v_noise_t : ℝ)
    (h_sig : 0 < v_sig)
    (h_ns : 0 < v_noise_s)
    (h_more_noise : v_noise_s < v_noise_t) :
    v_sig / (v_sig + v_noise_t) < v_sig / (v_sig + v_noise_s) :=
  div_lt_div_of_pos_left h_sig (by linarith) (by linarith)

/-- **Corrected portability ratio accounts for noise differences.**
    The "true" portability ratio should compare signal-to-noise ratios,
    not R² values directly.
    SNR_s = v_sig_s / v_noise_s, SNR_t = v_sig_t / v_noise_t.
    Portability = SNR_t / SNR_s, which is invariant to noise scaling. -/
noncomputable def snrPortabilityRatio
    (v_sig_s v_noise_s v_sig_t v_noise_t : ℝ) : ℝ :=
  (v_sig_t / v_noise_t) / (v_sig_s / v_noise_s)

/-- **snrPortabilityRatio where its denominator vanishes, named.** The guard `v_sig_s / v_noise_s`
is zero at `v_sig_s = 0`, `v_noise_s = 1`. Lean returns `0` there rather than the value the
modelled quantity takes, and no type error marks the point. Consumers must require `v_sig_s /
v_noise_s ≠ 0`. -/
theorem snrPortabilityRatio_at_vsigs0vnoises1_is_junk (v_sig_t : ℝ) (v_noise_t : ℝ) :
    snrPortabilityRatio 0 1 v_sig_t v_noise_t = 0 := by
  unfold snrPortabilityRatio
  norm_num

/-- **SNR portability depends only on signal ratio when noise is constant.** -/
theorem snr_portability_signal_only
    (v_sig_s v_sig_t v_noise : ℝ)
    (h_ns : v_noise ≠ 0) :
    snrPortabilityRatio v_sig_s v_noise v_sig_t v_noise = v_sig_t / v_sig_s := by
  unfold snrPortabilityRatio
  field_simp

/-- **The `R²` ratio is the SNR ratio times the outcome-variance ratio**, which is this
section's claim written as an equation instead of an argument.

`Descent.Core.share v_sig v_noise` is `v_sig / (v_sig + v_noise)` -- the `R²` the corpus
computes everywhere -- and the section above says a portability quoted as a ratio of `R²`
values is not comparing signal transport, because `Var(Y)` differs between populations.
Here is the exact discrepancy: the two ratios agree only when `v_sig_t + v_noise` equals
`v_sig_s + v_noise`, that is only when the signal itself is unchanged, which is the case
where there is no portability loss to quote. Everywhere else the `R²` ratio is off by a
factor that depends on the outcome variances and not on transport at all.

This also ties these definitions to the corpus: `snrPortabilityRatio` lives in the register
of open questions, and until now nothing outside it constrained the quantity, so a wrong
body here would have been consistent with everything else. -/
theorem snrPortabilityRatio_eq_share_ratio_mul (v_sig_s v_sig_t v_noise : ℝ)
    (hn : 0 < v_noise) (hs : 0 < v_sig_s) (ht : 0 < v_sig_t) :
    snrPortabilityRatio v_sig_s v_noise v_sig_t v_noise
      = (Descent.Core.share v_sig_t v_noise / Descent.Core.share v_sig_s v_noise)
          * ((v_sig_t + v_noise) / (v_sig_s + v_noise)) := by
  have h1 : v_sig_s ≠ 0 := ne_of_gt hs
  have h2 : v_noise ≠ 0 := ne_of_gt hn
  have h3 : v_sig_t + v_noise ≠ 0 := ne_of_gt (by linarith)
  have h4 : v_sig_s + v_noise ≠ 0 := ne_of_gt (by linarith)
  unfold snrPortabilityRatio Descent.Core.share
  field_simp

end R2NonComparability


/-!
## Local Ancestry and Portability

The paper notes that measures of genetic distance based on global PCs are
"plausibly sub-optimal" and suggests local ancestry may better predict portability.
We formalize why local ancestry should be more informative.
-/

section LocalAncestry

/-- **Variance in local Fst across loci creates additional prediction error.**
    If local Fst varies (some loci have high Fst, others low), the prediction
    error has a "locus heterogeneity" component not captured by global Fst. -/
theorem mul_sum_lt_sum_mul_of_nonneg_of_exists_pos
    {m : ℕ} (β : Fin m → ℝ) (fst : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst i₀ - fst_global)) :
    fst_global * (∑ i, β i ^ 2) < ∑ i, β i ^ 2 * fst i := by
  have hsum_strict :
      0 < ∑ i, β i ^ 2 * (fst i - fst_global) := by
    have hsingle :
        β i₀ ^ 2 * (fst i₀ - fst_global)
          ≤ ∑ i, β i ^ 2 * (fst i - fst_global) := by
      simpa only using
        (Finset.single_le_sum
          (f := fun i ↦ β i ^ 2 * (fst i - fst_global))
          (fun i _ ↦ h_nonneg i)
          (Finset.mem_univ i₀))
    exact lt_of_lt_of_le h_strict hsingle
  have hrewrite :
      ∑ i, β i ^ 2 * (fst i - fst_global)
        = (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
    calc
      ∑ i, β i ^ 2 * (fst i - fst_global)
          = ∑ i, (β i ^ 2 * fst i - β i ^ 2 * fst_global) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i, β i ^ 2 * fst i) - ∑ i, β i ^ 2 * fst_global := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hgap :
      0 < (∑ i, β i ^ 2 * fst i) - fst_global * (∑ i, β i ^ 2) := by
    rw [← hrewrite]
    exact hsum_strict
  linarith

/-- **A weighted average exceeds a constant when the weighted deviations from
    it are positive:** `c < (∑ β² x) / (∑ β²)`.

    The genetics reading is that a genome-wide `F_ST` is a biased proxy for the
    effect-weighted average of local `F_ST`, so global and local carry
    different information. What is proved is that the weighted mean of `x`
    exceeds `c` when `∑ β²(x - c) > 0` — an arithmetic fact about weights, with no ancestry, no
    locus, no LD and no accuracy in it, and in particular no
    comparison of how informative two quantities are. -/
theorem lt_weighted_mean_of_weighted_deviation_pos
    {m : ℕ} (β : Fin m → ℝ) (fst_local : Fin m → ℝ) (fst_global : ℝ)
    (h_nonneg : ∀ i, 0 ≤ β i ^ 2 * (fst_local i - fst_global))
    (i₀ : Fin m)
    (h_strict : 0 < β i₀ ^ 2 * (fst_local i₀ - fst_global))
    (hweight_pos : 0 < ∑ i, β i ^ 2) :
    fst_global < (∑ i, β i ^ 2 * fst_local i) / (∑ i, β i ^ 2) :=
  (lt_div_iff₀ hweight_pos).2
    (mul_sum_lt_sum_mul_of_nonneg_of_exists_pos β fst_local fst_global h_nonneg i₀ h_strict)

end LocalAncestry


/-!
## Disease-Specific Portability

For binary traits (asthma, T2D), portability depends on additional factors:
- Prevalence differences across populations
- The specific metric used (precision, recall, F1, AUC)
- Threshold choice for classification
-/

section DiseasePortability

/-! **`f1Score` is not here any more.** It, `f1Score_at_precision0sensitivity0_is_junk`,
`f1_symmetric` and `f1_le_arithmetic_mean` moved to `Core/Decision.lean`, beside
`positivePredictiveValue`, `netBenefit` and `nriFromOperatingPoints`, which are the family
it belongs to. An F1 score is the harmonic mean of two reals and carries no programme
content; keeping it here meant `Portability/MetricSpecificPortability/PrecisionRecall.lean`
imported this module -- the audit layer, at the top of the graph -- to reach a formula in
two arguments, which is the `Portability -> Program` edge the layer order forbids. -/

/-
Two theorems were deleted from this section rather than renamed.

`prevalence_dominates_sensitivity_for_recall` assumed
`sens₁ / sens₂ < n_cases₂ / n_cases₁` and concluded `n_cases₁ * sens₁ < n_cases₂ * sens₂`.
Those are the same inequality: the proof was `rwa [div_lt_div_iff₀ ...] at h_sens_ratio`,
cross-multiplication and nothing else. The docstring said "The net effect on recall depends
on whether the prevalence increase dominates the sensitivity decrease. We prove the
sufficient condition" — but the sufficient condition *is* the conclusion, restated as a
ratio, so proving it from itself decides nothing about which effect dominates. Four of its
eight hypotheses, including the one saying the target has more cases, were unused.

`different_diseases_different_portability_patterns` took four inequalities as hypotheses
and returned their conjunction, `⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩`. Conjunction-introduction over
one's own premises is the case the corpus proof policy names explicitly. Nothing about
asthma, T2D, or a prevalence-distance relationship enters; the statement is true of any
four numbers with those orderings, which is what "qualitatively different patterns" was
being read off from.

The genuine metric-divergence result for this section is
`precision_recall_divergence_exists` above, which exhibits explicit witnesses satisfying
the precision identity rather than assuming the divergence.
-/

end DiseasePortability


/-!
## Calibrated PGS: When Portability is Recoverable

Not all portability loss is irrecoverable. Some can be addressed by:
1. Re-calibration (adjusting intercept and slope)
2. Ancestry-specific spline adjustments
3. Multi-ancestry training

We formalize which components of portability loss are recoverable.
-/

section RecoverablePortability


/-- **Rescaling by `1/r` inverts a slope change by `r`.**

    The nonvanishing hypothesis is real content: no rescaling recovers a slope that has
    been multiplied by zero. Read the name narrowly all the same. This is not
    recoverability by re-calibration, because recovering the slope requires knowing `r`,
    which this statement supplies to itself. -/
theorem slope_rescaling_inverts_slope_change
    (b r pgs : ℝ) (hr : r ≠ 0) :
    (b * r * pgs) * (1 / r) = b * pgs := by
  field_simp

/-- **LD mismatch is NOT recoverable by linear re-calibration.**
    If the LD structure changes, the normal equations have a different solution.
    No linear transformation of the source weights can recover the target optimum.
    (This reuses the existing source_erm_solves_source_not_target_normal_equations.) -/
theorem mulVec_smul_ne_of_not_aligned
    (w_source : Fin 2 → ℝ)
    (σ_target : Matrix (Fin 2) (Fin 2) ℝ)
    (cross_target : Fin 2 → ℝ)
    -- σ_target.mulVec is linear, so scaling w_source just scales the image
    -- The image of the source direction doesn't align with cross_target
    -- (cross_target is not a scalar multiple of σ_target.mulVec w_source)
    (h_not_aligned : ∀ α : ℝ, α • σ_target.mulVec w_source ≠ cross_target) :
    -- Then no linear re-calibration can recover target-optimal weights
    ∀ α : ℝ, σ_target.mulVec (α • w_source) ≠ cross_target := by
  intro α
  rw [Matrix.mulVec_smul]
  exact h_not_aligned α

/-- **Distinct effects give distinct predictions at every nonzero genotype.**

    Previously `effect_turnover_requires_target_data`, "the source GWAS provides no
    information about the new effects. Only target GWAS data helps." An information claim
    needs an information measure and a claim about what data determines what; neither
    appears. The statement is cancellation in a field: if `β_source ≠ β_target` then
    `β_source · y ≠ β_target · y` unless `y = 0`.

    This does say something the section wants — the discrepancy does not vanish, so no
    amount of rescaling the *genotype* hides it — and unlike
    `mulVec_smul_ne_of_not_aligned` above, which quantifies over all linear
    recalibrations `α` and shows none succeeds, it never quantifies over corrections at
    all. That is the difference between the two, and it is why only one of them keeps a
    non-recoverability name. -/
@[withdrawn "OQ-effect-turnover-requires-target-data"
  "the name made an information claim -- that the source GWAS carries no \
   information about the new effects -- with no information measure and no \
   statement about what data determines what; the statement is cancellation in \
   a field"]
theorem effect_mismatch_gives_prediction_mismatch_at_nonzero_genotype
    (β_source β_target : ℝ)
    (h_different : β_source ≠ β_target) :
    -- Any prediction using β_source has nonzero error for β_target
    ∀ y : ℝ, β_source * y ≠ β_target * y ∨ y = 0 := by
  intro y
  by_cases hy : y = 0
  · right; exact hy
  · left; intro h; exact h_different (mul_right_cancel₀ hy h)

end RecoverablePortability

/-!
## What this file costs the corpus, measured

Recorded as a `TODO` object rather than as a paragraph, because the last paragraph in this
corpus that told the next agent what to do was written from a name census, looked like a
decision already taken, and was wrong.  This one carries its numbers and says what would
overturn it.
-/

TODO "OQ-relocate-generic-arithmetic-helpers"
  "Four lemmas here are generic real arithmetic filed at layer 6 under a name \
   that says 'open question': div_le_of_ge_one_sub_mul, \
   both_le_of_add_eq_of_nonneg, mul_lt_mul_left_of_pos' and \
   mul_sq_le_mul_sq_of_le_of_nonneg. Each proves a fact about free reals, and \
   two of the four docstrings say outright that the genetics reading is \
   supplied by the names and appears nowhere in the statement.\n\n\
   MEASURED, two query shapes agreeing: ZERO consumers. Neither a \
   name-and-extension grep over Descent/ nor a case-insensitive content grep \
   over the whole repository finds a use of any of the four outside this file. \
   Two shapes because the corpus records that a single query answering zero is \
   a hypothesis and two queries of different shape agreeing on zero is a \
   result.\n\n\
   SO THIS IS NOT THE CHANGE IT LOOKS LIKE. Moving them down to Core would \
   relocate four lemmas nobody imports, which buys the layer order nothing: an \
   unused declaration casts no import shadow, so no importer is carrying this \
   file for their sake. What the measurement says instead is that they are \
   candidates for deletion under the corpus's own proof policy, and that the \
   decision is a read-the-bodies decision rather than a census decision.\n\n\
   WHAT WOULD OVERTURN THIS: a consumer in the validation Python, a consumer in \
   a file added after this was written, or a plan to cite one of them from a \
   lower layer. Each is checkable in one command."

end Descent.Program
