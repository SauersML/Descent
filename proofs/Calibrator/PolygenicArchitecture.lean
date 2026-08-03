/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Calibrator.HaplotypeTheory
import Calibrator.CertificateGrading
import Calibrator.TransportedMinimax
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Calibrator

open MeasureTheory

/-!
# Polygenic Architecture and PGS Portability

This file formalizes how the underlying genetic architecture of
complex traits — the distribution of effect sizes, the number of
causal variants, and their genomic distribution — affects PGS
portability across populations.

Key results:
1. Effect size distribution models (exponential, spike-and-slab)
2. Polygenicity and its relationship to portability
3. Genetic architecture parameters from GWAS
4. Architecture-dependent portability predictions
5. Heritability partitioning by functional category

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat effect-size distribution models or the minimax and
certificate-modulus material below. Sources for individual results, where they exist,
are cited at those results.
-/


/-!
## Effect Size Distribution

The distribution of per-variant effect sizes determines
how PGS portability scales with sample size and ancestry.
-/

section EffectSizeDistribution

/-- **Exponential distribution of squared effects.**
    Under the infinitesimal model: β² ~ Exponential(1/σ²)
    where σ² = h²/M (heritability divided by number of variants).

    Empirical status: UNTESTED. -/
noncomputable def expectedSquaredEffect (h2 M : ℝ) : ℝ := h2 / M

/-- Per-variant heritability decreases with polygenicity. -/
theorem per_variant_h2_decreases_with_M (h2 M₁ M₂ : ℝ)
    (h_h2 : 0 < h2) (h_M₁ : 0 < M₁) (h_M₂ : 0 < M₂)
    (h_M : M₁ < M₂) :
    expectedSquaredEffect h2 M₂ < expectedSquaredEffect h2 M₁ := by
  unfold expectedSquaredEffect
  exact div_lt_div_iff_of_pos_left h_h2 h_M₂ h_M₁ |>.mpr h_M

/-- **Spike-and-slab model.**
    π proportion of variants have effect ~ N(0, σ²_large),
    (1-π) proportion have effect = 0 (or ~ N(0, σ²_small)).
    π is the polygenicity parameter.

    Empirical status: UNTESTED.

    Denotes: a variance. Other definitions share this formula under names from a
    different concept family; the formula does not fix which is meant. -/
noncomputable def spikeAndSlabVariance (pi sigma_sq_large sigma_sq_small : ℝ) : ℝ :=
  pi * sigma_sq_large + (1 - pi) * sigma_sq_small

/-! ### The mixture map, shared with `HaplotypeTheory`

The spike-and-slab variance, the average phase interaction and the
ancestry-specific effect are three different quantities — a variance, an
interaction contribution and an effect size — that are all the same convex
combination of two values at a mixing weight. `Conventions.convexMix` names
that map; these two theorems record the coincidence in one of the two files
each pair lives in, so that a change to the mixture convention in either file
fails to compile rather than quietly disagreeing. -/

theorem spikeAndSlabVariance_eq_averagePhaseInteraction (pi a b : ℝ) :
    spikeAndSlabVariance pi a b = averagePhaseInteraction pi a b := by
  unfold spikeAndSlabVariance averagePhaseInteraction; ring

theorem spikeAndSlabVariance_eq_ancestrySpecificEffect (pi a b : ℝ) :
    spikeAndSlabVariance pi a b = ancestrySpecificEffect a b pi := by
  unfold spikeAndSlabVariance ancestrySpecificEffect; ring

/-- **The spike-and-slab formula is a variance only on `0 ≤ pi ≤ 1`.**

    Outside that interval `pi * σ²_large + (1 - pi) * σ²_small` is a signed
    extrapolation of a mixture, not a mixture, and it goes negative: at `pi = 2`
    with a zero slab variance it returns `-σ²_small`. Nothing in the definition
    prevents this, and `sas_variance_monotone_in_pi` below imposes no bounds at
    all, so the bound is recorded here as a theorem with the interval hypothesis
    visible.

    This is the mixture-interval statement: on `[0, 1]` the value is a convex
    combination and therefore lies between the two component variances, hence is
    nonnegative whenever they are. -/
theorem spikeAndSlabVariance_mem_interval
    (pi sigma_sq_large sigma_sq_small : ℝ)
    (h_pi_nonneg : 0 ≤ pi) (h_pi_le : pi ≤ 1)
    (h_order : sigma_sq_small ≤ sigma_sq_large) :
    sigma_sq_small ≤ spikeAndSlabVariance pi sigma_sq_large sigma_sq_small ∧
      spikeAndSlabVariance pi sigma_sq_large sigma_sq_small ≤ sigma_sq_large := by
  unfold spikeAndSlabVariance
  constructor <;> nlinarith

/-- On the mixture interval, and only there, the spike-and-slab variance is
nonnegative when its components are. -/
theorem spikeAndSlabVariance_nonneg
    (pi sigma_sq_large sigma_sq_small : ℝ)
    (h_pi_nonneg : 0 ≤ pi) (h_pi_le : pi ≤ 1)
    (h_large : 0 ≤ sigma_sq_large) (h_small : 0 ≤ sigma_sq_small) :
    0 ≤ spikeAndSlabVariance pi sigma_sq_large sigma_sq_small := by
  unfold spikeAndSlabVariance
  have h_one_minus : 0 ≤ 1 - pi := by linarith
  nlinarith

/-- **And it is negative off the interval**, which is what the missing bound
costs. At `pi = 2` with a zero slab variance the formula returns `-σ²_small`, a
negative variance. The witness is exhibited so that the failure is recorded
rather than assumed away. -/
theorem spikeAndSlabVariance_neg_off_interval
    (sigma_sq_small : ℝ) (h_small : 0 < sigma_sq_small) :
    spikeAndSlabVariance 2 0 sigma_sq_small < 0 := by
  unfold spikeAndSlabVariance
  linarith

/-- Spike-and-slab variance increases with polygenicity
    when the slab dominates. Note that this holds for every real `pi`, including
    values outside `[0, 1]` at which the quantity is not a variance; see
    `spikeAndSlabVariance_mem_interval` for the interval on which the conclusion
    is about a mixture. -/
theorem sas_variance_monotone_in_pi
    (pi₁ pi₂ sigma_sq_large sigma_sq_small : ℝ)
    (h_large : sigma_sq_small < sigma_sq_large)
    (h_pi : pi₁ < pi₂) :
    spikeAndSlabVariance pi₁ sigma_sq_large sigma_sq_small <
      spikeAndSlabVariance pi₂ sigma_sq_large sigma_sq_small := by
  unfold spikeAndSlabVariance; nlinarith

/-- **BayesR mixture components.**
    BayesR uses a 4-component mixture:
    β ~ π₀δ₀ + π₁N(0, 0.01σ²) + π₂N(0, 0.1σ²) + π₃N(0, σ²)
    where Σπ_i = 1 and σ² = h²/M. -/
theorem mixture_weights_sum_to_one
    (pi0 pi1 pi2 pi3 : ℝ)
    (h_sum : pi0 + pi1 + pi2 + pi3 = 1)
    (h_nn₀ : 0 ≤ pi0) (h_nn₁ : 0 ≤ pi1) (h_nn₂ : 0 ≤ pi2) (h_nn₃ : 0 ≤ pi3) :
    0 ≤ pi0 ∧ pi0 ≤ 1 := by
  constructor
  · exact h_nn₀
  · linarith

end EffectSizeDistribution


/-!
## Polygenicity and Portability

More polygenic traits tend to have better portability because
each variant contributes less, making the PGS less sensitive
to per-variant LD changes.
-/

section PolygenicityAndPortability

/-- **Polygenicity definition.**
    M_eff = effective number of causal variants
    = (Σ β²_j)² / Σ β⁴_j (inverse kurtosis measure).

    Empirical status: UNTESTED. -/
noncomputable def effectivePolygenicity (sum_beta_sq sum_beta_fourth : ℝ) : ℝ :=
  sum_beta_sq^2 / sum_beta_fourth

/-- Effective polygenicity ≥ 1.

    The hypothesis `h_cs` is not free: on a genuine effect vector it is a
    theorem, not an assumption. See `effectivePolygenicityOfEffects_mem_Icc`
    below, which removes it and adds the matching upper bound. This form is
    kept for callers holding only the two moment sums. -/
theorem effective_polygenicity_ge_one
    (sum_sq sum_fourth : ℝ)
    (h_fourth : 0 < sum_fourth)
    (h_cs : sum_fourth ≤ sum_sq^2) :
    1 ≤ effectivePolygenicity sum_sq sum_fourth := by
  unfold effectivePolygenicity
  rw [le_div_iff₀ h_fourth]
  linarith

/-- **Effective polygenicity of an explicit effect vector.**

    The same inverse-kurtosis measure, but fed the two moment sums of a named
    effect vector rather than two unrelated reals. Stating it this way is what
    lets the Cauchy–Schwarz hypothesis of `effective_polygenicity_ge_one` be
    discharged instead of assumed, and lets the matching upper bound be stated
    at all: `M_eff` cannot exceed the number of variants, which no formulation
    over two free reals can express.

    Empirical status: UNTESTED. -/
noncomputable def effectivePolygenicityOfEffects {q : ℕ} (beta : Fin q → ℝ) : ℝ :=
  effectivePolygenicity (∑ j, beta j ^ 2) (∑ j, beta j ^ 4)

/-- `∑ β⁴ ≤ (∑ β²)²`: the lower half of the polygenicity range, as a theorem
about an effect vector rather than a hypothesis about two reals. It is the
statement that a sum of nonnegative numbers dominates the sum of their
squares. -/
theorem sum_fourth_le_sq_sum_sq {q : ℕ} (beta : Fin q → ℝ) :
    ∑ j, beta j ^ 4 ≤ (∑ j, beta j ^ 2) ^ 2 := by
  have h : ∑ j : Fin q, (beta j ^ 2) ^ 2 ≤ (∑ j : Fin q, beta j ^ 2) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ ↦ sq_nonneg (beta j))
  have hrw : ∑ j : Fin q, (beta j ^ 2) ^ 2 = ∑ j, beta j ^ 4 :=
    Finset.sum_congr rfl (fun j _ ↦ by ring)
  rw [hrw] at h
  exact h

/-- `(∑ β²)² ≤ q · ∑ β⁴`: the upper half, by Cauchy–Schwarz against the
constant vector. This is the direction the two-free-reals formulation could not
state, because the variant count does not appear in its signature. -/
theorem sq_sum_sq_le_card_mul_sum_fourth {q : ℕ} (beta : Fin q → ℝ) :
    (∑ j, beta j ^ 2) ^ 2 ≤ (q : ℝ) * ∑ j, beta j ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
    (fun _ ↦ (1 : ℝ)) (fun j ↦ beta j ^ 2)
  have h3 : ∑ j : Fin q, (beta j ^ 2) ^ 2 = ∑ j, beta j ^ 4 :=
    Finset.sum_congr rfl (fun j _ ↦ by ring)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [h3] at h
  exact h

/-- **Effective polygenicity lies between one and the number of variants.**

    Two strengthenings of `effective_polygenicity_ge_one` at once. The
    Cauchy–Schwarz hypothesis is discharged rather than assumed, and the
    one-sided bound becomes two-sided: `1 ≤ M_eff ≤ q`, with the lower end
    approached by a single large effect and the upper end by `q` equal ones.
    Only the positivity of the fourth moment remains, and that is not a
    modelling assumption but the condition for the quotient to exist. -/
theorem effectivePolygenicityOfEffects_mem_Icc {q : ℕ} (beta : Fin q → ℝ)
    (h_pos : 0 < ∑ j, beta j ^ 4) :
    1 ≤ effectivePolygenicityOfEffects beta ∧
      effectivePolygenicityOfEffects beta ≤ (q : ℝ) := by
  unfold effectivePolygenicityOfEffects effectivePolygenicity
  constructor
  · rw [le_div_iff₀ h_pos, one_mul]
    exact sum_fourth_le_sq_sum_sq beta
  · rw [div_le_iff₀ h_pos]
    exact sq_sum_sq_le_card_mul_sum_fourth beta

/-- Explicit SNP-level portability model.

Each causal SNP contributes a source squared-effect mass
`sourceSquaredEffect j = β_source,j²`, and the target retains some portion of
that mass after LD mismatch, allele-frequency drift, effect-size drift, and
other transport losses. The retained mass is modeled directly at each SNP,
rather than through a single `√M` ansatz. -/
structure SNPArchitecturePortabilityModel (q : ℕ) where
  sourceSquaredEffect : Fin q → ℝ
  targetRetainedSquaredEffect : Fin q → ℝ
  sourceSquaredEffect_nonneg : ∀ j, 0 ≤ sourceSquaredEffect j
  targetRetained_nonneg : ∀ j, 0 ≤ targetRetainedSquaredEffect j
  targetRetained_le_source : ∀ j, targetRetainedSquaredEffect j ≤ sourceSquaredEffect j

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SNPArchitecturePortabilityModel.witness
    (q : ℕ) : SNPArchitecturePortabilityModel q where
  sourceSquaredEffect := fun _ ↦ 1
  targetRetainedSquaredEffect := fun _ ↦ 1 / 2
  sourceSquaredEffect_nonneg := fun _ ↦ by norm_num
  targetRetained_nonneg := fun _ ↦ by norm_num
  targetRetained_le_source := fun _ ↦ by norm_num

namespace SNPArchitecturePortabilityModel

/-- Total causal signal mass in the source architecture.

    Empirical status: UNTESTED. -/
noncomputable def sourceEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  ∑ j, model.sourceSquaredEffect j

/-- Total causal signal mass still retained in the target architecture.

    Empirical status: UNTESTED. -/
noncomputable def targetRetainedEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  ∑ j, model.targetRetainedSquaredEffect j

/-- Total signal mass lost across SNPs when transporting to the target.

    Empirical status: UNTESTED. -/
noncomputable def lostEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.sourceEffectMass - model.targetRetainedEffectMass

/-- Relative portability loss: lost causal signal mass as a fraction of the
source causal signal mass. -/
noncomputable def relativePortabilityLoss {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.lostEffectMass / model.sourceEffectMass

/-- Retained portability score: retained target causal signal mass as a
fraction of the source causal signal mass. -/
noncomputable def portabilityScore {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.targetRetainedEffectMass / model.sourceEffectMass

theorem sourceEffectMass_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    0 ≤ model.sourceEffectMass := by
  unfold sourceEffectMass
  exact Fintype.sum_nonneg fun j ↦ model.sourceSquaredEffect_nonneg j

theorem targetRetainedEffectMass_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    0 ≤ model.targetRetainedEffectMass := by
  unfold targetRetainedEffectMass
  exact Fintype.sum_nonneg fun j ↦ model.targetRetained_nonneg j

theorem targetRetainedEffectMass_le_sourceEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    model.targetRetainedEffectMass ≤ model.sourceEffectMass := by
  unfold targetRetainedEffectMass sourceEffectMass
  exact Finset.sum_le_sum fun j _ ↦ model.targetRetained_le_source j

/-- The relative portability loss is exactly the locuswise lost-effect mass
fraction. -/
theorem relativePortabilityLoss_eq_locuswise_loss_fraction {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    model.relativePortabilityLoss =
      (∑ j, (model.sourceSquaredEffect j - model.targetRetainedSquaredEffect j)) /
        model.sourceEffectMass := by
  unfold relativePortabilityLoss lostEffectMass sourceEffectMass targetRetainedEffectMass
  congr 1
  rw [← Finset.sum_sub_distrib]

@[simp] theorem portabilityScore_eq_one_sub_relativePortabilityLoss {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    model.portabilityScore = 1 - model.relativePortabilityLoss := by
  unfold portabilityScore relativePortabilityLoss lostEffectMass
  field_simp [ne_of_gt h_source]
  ring

theorem relativePortabilityLoss_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    0 ≤ model.relativePortabilityLoss := by
  rw [relativePortabilityLoss_eq_locuswise_loss_fraction model]
  apply div_nonneg
  · exact Fintype.sum_nonneg fun j ↦ sub_nonneg.mpr (model.targetRetained_le_source j)
  · exact le_of_lt h_source

theorem portabilityScore_le_one {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    model.portabilityScore ≤ 1 := by
  rw [portabilityScore_eq_one_sub_relativePortabilityLoss model h_source]
  have h_loss_nn := relativePortabilityLoss_nonneg model h_source
  linarith

end SNPArchitecturePortabilityModel

/-- Equal-effect portability score under a catastrophic-mismatch architecture:
all `M` causal SNPs have equal source squared effect, and SNPs in the explicit
set `mismatched` retain zero target signal. The retained fraction is therefore
the surviving SNP fraction. -/
noncomputable def uniformCatastrophicPortabilityScore
    (M : ℕ) (mismatched : Finset (Fin M)) : ℝ :=
  1 - (mismatched.card : ℝ) / (M : ℝ)

/-- **More polygenic architectures are more robust to the same number of badly
mismatched causal SNPs.**

This theorem is now stated on an explicit causal-SNP architecture: both traits
have equal per-SNP source effect mass, and both lose the same number of causal
SNPs in the target. The trait with more causal SNPs loses a smaller fraction of
its total causal signal mass. -/
theorem more_polygenic_more_portable
    {M₁ M₂ : ℕ}
    (mismatched₁ : Finset (Fin M₁))
    (mismatched₂ : Finset (Fin M₂))
    (h_M : M₁ < M₂)
    (h_same_card : mismatched₁.card = mismatched₂.card)
    (h_loss : 0 < mismatched₁.card) :
    uniformCatastrophicPortabilityScore M₁ mismatched₁ <
      uniformCatastrophicPortabilityScore M₂ mismatched₂ := by
  unfold uniformCatastrophicPortabilityScore
  have h_k_pos : 0 < (mismatched₁.card : ℝ) := Nat.cast_pos.mpr h_loss
  have h_M₁_pos_nat : 0 < M₁ := lt_of_lt_of_le h_loss (by
    simpa [Fintype.card_fin] using mismatched₁.card_le_univ)
  have h_M₂_pos_nat : 0 < M₂ := lt_trans h_M₁_pos_nat h_M
  have h_M₁_pos : 0 < (M₁ : ℝ) := Nat.cast_pos.mpr h_M₁_pos_nat
  have h_M₂_pos : 0 < (M₂ : ℝ) := Nat.cast_pos.mpr h_M₂_pos_nat
  have h_div :
      (mismatched₁.card : ℝ) / (M₂ : ℝ) <
        (mismatched₁.card : ℝ) / (M₁ : ℝ) :=
    (div_lt_div_iff_of_pos_left h_k_pos h_M₂_pos h_M₁_pos).2 (by exact_mod_cast h_M)
  have h_same_card_cast : (mismatched₂.card : ℝ) = (mismatched₁.card : ℝ) := by
    exact_mod_cast h_same_card.symm
  rw [h_same_card_cast]
  linarith

/-- Height-like traits can be more portable than BMI-like traits when the same
number of causal SNPs are catastrophically mismatched, because a larger set of
causal SNPs dilutes the lost fraction. -/
theorem height_polygenic_good_portability
    {M_height M_bmi : ℕ}
    (mismatchedHeight : Finset (Fin M_height))
    (mismatchedBMI : Finset (Fin M_bmi))
    (h_M : M_bmi < M_height)
    (h_same_card : mismatchedBMI.card = mismatchedHeight.card)
    (h_loss : 0 < mismatchedBMI.card) :
    uniformCatastrophicPortabilityScore M_bmi mismatchedBMI <
      uniformCatastrophicPortabilityScore M_height mismatchedHeight :=
  more_polygenic_more_portable mismatchedBMI mismatchedHeight h_M h_same_card h_loss

/-- **Selection can outweigh a polygenicity advantage.**

Even if the selected trait has more causal SNPs, it can still have worse
portability when the fraction of causal SNPs that lose target signal is larger. -/
theorem selection_overrides_polygenicity
    {M_neutral M_selected : ℕ}
    (neutralMismatch : Finset (Fin M_neutral))
    (selectedMismatch : Finset (Fin M_selected))
    (h_more_polygenic : M_neutral < M_selected)
    (h_selected_worse_fraction :
      (neutralMismatch.card : ℝ) / (M_neutral : ℝ) <
        (selectedMismatch.card : ℝ) / (M_selected : ℝ)) :
    M_neutral < M_selected ∧
      uniformCatastrophicPortabilityScore M_selected selectedMismatch <
        uniformCatastrophicPortabilityScore M_neutral neutralMismatch := by
  unfold uniformCatastrophicPortabilityScore
  constructor
  · exact h_more_polygenic
  · linarith

end PolygenicityAndPortability


/-!
## Nonsmooth Architecture Summaries and What They Cost to Estimate

The quantities this file uses to summarise an effect-size distribution are not
all of the same difficulty, and nothing in the corpus recorded the difference.

`expectedSquaredEffect`, `spikeAndSlabVariance` and `additiveVariance` are
smooth — quadratic — functionals of the effect vector, and are estimable at the
usual root-`n` rate. `effectivePolygenicity` and the mean absolute effect
`q⁻¹ ∑ |β_j|` are not. The mean absolute effect is the canonical nonsmooth
functional: in the Gaussian sequence model over a box, estimating
`n⁻¹ ∑ |θ_i|` has minimax risk of order `1 / log n`, logarithmic, not
polynomial. It is the natural measure of total additive signal and the closest
kin in this file to a polygenicity or sparsity summary, and it is far harder to
estimate than the variance-type summaries standing beside it.

The second half of the picture is about certificates rather than estimators.
The unconditional result is algebraic: completeness at grade `K` is equivalent
to grade-insensitivity of the modulus, and the deficit is the squared modulus
ratio. The first Gaussian-location-mixture audit found its grade-8 modulus
recovered 99.93% of the ungraded one, so the proposed polynomial fixed-grade
gap is not stated as a Lean theorem here. In particular it is not accepted as
a theorem-valued field of a biological model.

`Calibrator.PowerAnalysis` compares the logarithmic and polynomial benchmark
curves conditionally. Those comparisons are useful for falsifying a proposed
design calculation, but they are not sample-size guarantees for a GWAS until a
concrete observation model proves that its minimax risk and certificate modulus
are the stated curves.
-/

section NonsmoothSummaries

/-- **Mean absolute effect size across variants.**

    `q⁻¹ ∑_j |β_j|`, the natural summary of total additive signal on the effect
    scale rather than the squared-effect scale. Unlike `expectedSquaredEffect`
    it is not a smooth functional of the effect vector: it is Lipschitz but has
    no derivative at any coordinate through zero, and that is what governs how
    hard it is to estimate.

    Empirical status: UNTESTED. -/
noncomputable def meanAbsoluteEffect {q : ℕ} (beta : Fin q → ℝ) : ℝ :=
  (∑ j, |beta j|) / q

theorem meanAbsoluteEffect_nonneg {q : ℕ} (beta : Fin q → ℝ) :
    0 ≤ meanAbsoluteEffect beta := by
  unfold meanAbsoluteEffect
  exact div_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _) (Nat.cast_nonneg q)

/-- **The nonsmooth summary is dominated by the smooth one.**

    `(q⁻¹ ∑ |β_j|)² ≤ q⁻¹ ∑ β_j²` by Cauchy–Schwarz. The point of recording it
    is the contrast it sets up: the smaller quantity is the harder one to
    estimate, so the ordering of the two summaries by magnitude runs opposite to
    their ordering by statistical difficulty. -/
theorem meanAbsoluteEffect_sq_le_meanSquaredEffect {q : ℕ} (beta : Fin q → ℝ) :
    (meanAbsoluteEffect beta) ^ 2 ≤ (∑ j, beta j ^ 2) / q := by
  by_cases hq : q = 0
  · subst q
    simp [meanAbsoluteEffect]
  · have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
      (fun _ ↦ (1 : ℝ)) (fun j ↦ |beta j|)
    have h3 : ∑ j : Fin q, |beta j| ^ 2 = ∑ j, beta j ^ 2 :=
      Finset.sum_congr rfl (fun j _ ↦ sq_abs _)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    rw [h3] at h
    unfold meanAbsoluteEffect
    rw [div_pow, div_le_div_iff₀ (by positivity) hq']
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hq')
    nlinarith [hmul]

/-! ### A biological certificate problem with no theorem fields

The parameter is an additive-effect vector, the carrier is a closed ball, and
the target is `meanAbsoluteEffect`.  The structure below contains numerical
data only.  It cannot claim minimax duality, Donoho--Liu tightness, or a
fixed-grade gap by projection from an assumption field.
-/

/-- Bounded additive-effect architectures.  The absolute radius makes the set
nonempty and convex for every input, without a validity theorem parameter.

    Empirical status: UNTESTED. -/
noncomputable def boundedEffectCarrier (q : ℕ) (B : ℝ) : Set (Fin q → ℝ) :=
  Metric.closedBall 0 |B|

theorem boundedEffectCarrier_nonempty (q : ℕ) (B : ℝ) :
    (boundedEffectCarrier q B).Nonempty :=
  ⟨0, Metric.mem_closedBall_self (abs_nonneg B)⟩

theorem boundedEffectCarrier_convex (q : ℕ) (B : ℝ) :
    Convex ℝ (boundedEffectCarrier q B) :=
  convex_closedBall 0 |B|

open Calibrator.CertificateGrading in
/-- A finite catalogue of additive architectures and a numerical discrepancy
between mixture experiments.  No field has type `Prop`, and in particular the
graded modulus is not supplied by the caller: it is derived below as a
supremum over moment-matched prior pairs. -/
structure MeanAbsoluteEffectCertificateProblem (q n : ℕ) where
  effectRadius : ℝ
  architecture : Fin (n + 1) → Fin q → ℝ
  /-- Actual catalogue-indexed observation laws.  Prior discrepancies are
  derived as total variation between mixtures of these laws; they are not an
  arbitrary numerical input. -/
  observation : Fin (n + 1) → FinitePrior n
  logScale : ℝ

namespace MeanAbsoluteEffectCertificateProblem

open Calibrator.CertificateGrading

/-- The effect vectors this problem ranges over: the ball of radius
`effectRadius` in the per-variant effect coordinates.

    Empirical status: UNTESTED. Definitional within the problem declared above:
    it names the carrier the catalogue is quantified over rather than
    predicting an observable. -/
noncomputable def effects {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n) :
    Set (Fin q → ℝ) := boundedEffectCarrier q P.effectRadius

/-- Signed effect moment used by grade matching.  Grade two, for example,
matches the catalogue-average signed effect and squared-effect mass before it
tries to separate the nonsmooth mean-absolute-effect target. -/
noncomputable def architectureMoment {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (r : ℕ)
    (i : Fin (n + 1)) : ℝ :=
  ∑ j, (P.architecture i j) ^ (r + 1)

noncomputable def mixtureExperiment {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) :
    FiniteMixtureExperiment n n where
  target i := meanAbsoluteEffect (P.architecture i)
  moment := P.architectureMoment
  observation := P.observation

noncomputable def finiteProblem {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) :
    FiniteMomentCertificateProblem n :=
  P.mixtureExperiment.certificateProblem

noncomputable def calculus {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) : CertificateCalculus :=
  explicitCalculus P.finiteProblem.modulus P.logScale

@[simp] theorem finiteProblem_target {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.finiteProblem.target i = meanAbsoluteEffect (P.architecture i) := rfl

@[simp] theorem finiteProblem_moment {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (r : ℕ) (i : Fin (n + 1)) :
    P.finiteProblem.moment r i = P.architectureMoment r i := rfl

@[simp] theorem architectureMoment_zero {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.architectureMoment 0 i = ∑ j, P.architecture i j := by
  simp [architectureMoment]

@[simp] theorem architectureMoment_one {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.architectureMoment 1 i = ∑ j, (P.architecture i j) ^ 2 := by
  simp [architectureMoment]

/-- **What grade two means biologically.**  It is not a label or a theorem
parameter: the two mixture priors have equal expected signed-effect sum and
equal expected squared-effect mass across the architecture catalogue.  The
nonsmooth target they may still separate is mean absolute effect. -/
theorem momentMatched_two_iff {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n)
    (A B : FinitePrior n) :
    P.finiteProblem.MomentMatched 2 A B ↔
      FinitePrior.mean A (fun i ↦ ∑ j, P.architecture i j) =
          FinitePrior.mean B (fun i ↦ ∑ j, P.architecture i j) ∧
        FinitePrior.mean A (fun i ↦ ∑ j, (P.architecture i j) ^ 2) =
          FinitePrior.mean B (fun i ↦ ∑ j, (P.architecture i j) ^ 2) := by
  constructor
  · intro h
    constructor
    · simpa only [FinitePrior.mean, finiteProblem_moment, architectureMoment_zero] using
        h 0 (by omega)
    · simpa only [FinitePrior.mean, finiteProblem_moment, architectureMoment_one] using
        h 1 (by omega)
  · rintro ⟨h0, h1⟩ r hr
    interval_cases r
    · simpa only [FinitePrior.mean, finiteProblem_moment, architectureMoment_zero] using h0
    · simpa only [FinitePrior.mean, finiteProblem_moment, architectureMoment_one] using h1

theorem effects_nonempty {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n) :
    P.effects.Nonempty := boundedEffectCarrier_nonempty q P.effectRadius

theorem effects_convex {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n) :
    Convex ℝ P.effects := boundedEffectCarrier_convex q P.effectRadius

/-- Exact biological specialization of the completeness criterion. -/
theorem complete_iff_gradeInsensitive {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) :
    P.calculus.IsComplete K h ↔ P.calculus.GradeInsensitive K h :=
  isComplete_iff_gradeInsensitive P.calculus K h

/-- Exact Bernstein-type invariant for the mean-absolute-effect problem. -/
theorem deficit_eq_modulusRatio_sq {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) :
    P.calculus.deficit K h =
      (P.calculus.modulus.Δ 0 h / P.calculus.modulus.Δ K h) ^ 2 :=
  deficit_eq_modulus_ratio_sq P.calculus K h

/-- Modulus ratio for the biological mean-absolute-effect experiment. -/
noncomputable def certificationGap {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) : ℝ :=
  P.finiteProblem.modulus 0 h / P.finiteProblem.modulus K h

/-- **Fixed-grade incompleteness for polygenic architecture transport.**

For every fixed grade, sufficiently large architecture catalogues contain an
actual finite observation experiment on a convex bounded effect carrier whose
ungraded-to-graded modulus ratio is at least
`n^(b_K/2) / sqrt(log n)`, with `b_K = 1/(K+1)`.

The target is the mean absolute causal effect, grade two matches signed-effect
mass and squared-effect mass, and discrepancy is total variation between the
prior-predictive observation laws.  The proof is admitted openly: it must
construct the moment-matching architecture priors.  No benchmark curve,
crossing hypothesis, or external moment-comparison theorem substitutes for
that construction. -/
theorem fixedGrade_incompleteness_biology (K : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ P : MeanAbsoluteEffectCertificateProblem (n + 1) n,
        P.effects.Nonempty ∧ Convex ℝ P.effects ∧
          FiniteMixtureExperiment.fixedGradeGapScale K n ≤
            P.certificationGap (K + 1) 1 := by
  sorry

end MeanAbsoluteEffectCertificateProblem

/-! ### Positivity buys an exponent: the moment body of architecture spectra

An architecture summary is a functional of a **positive** measure — the allele-frequency
spectrum, or the distribution of effect sizes. The set of moment sequences of such measures
is a *moment body*, and a moment body is much smaller than the coordinatewise box that
contains it.

Quantitatively, for the class whose boundary tail is at most `M t^α` the log covering number
is `Θ((M/ε)^(1/α))`, against `ε^(-2/(2α-1))` for the enclosing hyperrectangle. The two
exponents are named inputs here — the lower bound needs shell atoms and a
Varshamov–Gilbert argument, the upper bound needs smoothed convex hulls and Carl's
inequality, and neither is in Mathlib. **The comparison is the theorem**, and it holds at
every admissible `α` with no exceptional interval.

**Why this matters for a study.** Covering numbers are what set sample sizes for estimating
a class: the number of architectures distinguishable at resolution `ε` is what a design must
separate. Treating the architecture class as a box — which is what a coordinatewise
effect-size or frequency-bin prior amounts to — overstates that count **by a power of the
resolution**, not by a constant. So a sample-size calculation built on a box-shaped class is
conservative by a polynomial factor, and the positivity of the underlying spectrum is what
pays for the difference.

The entropy comparison is independent of the conditional certificate-gap proposal above.
It should not be used as evidence for that proposal: the first audit found no polynomial
certificate deficit in the tested Gaussian-mixture instance.

Empirical status: UNTESTED. -/

section MomentBodyEntropy

/-- Log covering number at resolution ratio `t = M/ε` and exponent `e`.

    Both classes below are of this shape and differ only in the exponent, which is why the
    comparison reduces to a comparison of exponents. -/
noncomputable def logCoveringAtExponent (t e : ℝ) : ℝ := t ^ e

/-- **Strictly fewer distinguishable architectures, at every resolution finer than `M`.**

    Once the resolution ratio exceeds one — that is, once `ε < M`, the only regime in which
    a covering number is informative — the moment body's log covering number is strictly
    below the hyperrectangle's. The gap is a power of the resolution ratio, not a constant.

    This is the sample-size statement: a design that must separate the architecture class at
    resolution `ε` faces strictly fewer alternatives than a box-shaped class of the same
    tail order would present. -/
theorem momentBody_logCovering_lt (t α : ℝ) (ht : 1 < t) (hα : 1 / 2 < α) :
    logCoveringAtExponent t (momentBodyEntropyExponent α) <
      logCoveringAtExponent t (hyperrectangleEntropyExponent α) := by
  unfold logCoveringAtExponent
  exact Real.rpow_lt_rpow_left_iff ht |>.mpr
    (momentBody_entropy_exponent_lt α hα)

/-- The covering-number gap is a strict inequality of positive quantities, so the ratio of
    required alternative counts exceeds one. Recorded in the form a power calculation
    consumes. -/
theorem momentBody_logCovering_ratio_gt_one (t α : ℝ) (ht : 1 < t) (hα : 1 / 2 < α) :
    1 < logCoveringAtExponent t (hyperrectangleEntropyExponent α) /
      logCoveringAtExponent t (momentBodyEntropyExponent α) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hpos : 0 < logCoveringAtExponent t (momentBodyEntropyExponent α) :=
    Real.rpow_pos_of_pos ht0 _
  rw [lt_div_iff₀ hpos, one_mul]
  exact momentBody_logCovering_lt t α ht hα

end MomentBodyEntropy

end NonsmoothSummaries


/-!
## Heritability Partitioning

Partitioning heritability by functional category reveals
which genomic features drive PGS signal and portability.
-/

section HeritabilityPartitioning

/-- **Heritability enrichment.**
    Enrichment of category c = (h²_c / M_c) / (h²_total / M_total).
    High enrichment means the category harbors more causal signal
    per variant.

    Empirical status: UNTESTED. -/
noncomputable def heritabilityEnrichment (h2_cat M_cat h2_total M_total : ℝ) : ℝ :=
  (h2_cat / M_cat) / (h2_total / M_total)

/-- Enrichment > 1 means more heritability per variant. -/
theorem enrichment_interpretation (h2_c M_c h2_t M_t : ℝ)
    (h_ht : 0 < h2_t) (h_Mt : 0 < M_t)
    (h_enriched : h2_c / M_c > h2_t / M_t) :
    1 < heritabilityEnrichment h2_c M_c h2_t M_t := by
  unfold heritabilityEnrichment
  rw [one_lt_div₀ (div_pos h_ht h_Mt)]
  exact h_enriched

/-- **Genomic regions can be enriched for heritability.**
    When a region contains a fraction f_snp of variants but a fraction
    f_h2 of heritability, and f_h2 > f_snp, the enrichment f_h2/f_snp > 1.
    More precisely, if f_snp < α and f_h2 > β, enrichment > β/α.

    Worked example: Coding regions contain ~1.5% of variants (< 1/50)
    but ~10-20% of heritability (> 1/10), giving enrichment > 5×. -/
theorem region_heritability_enrichment
    (h2_region h2_total M_region M_total α β : ℝ)
    (h_prop_variants : M_region / M_total < α)
    (h_prop_h2 : β < h2_region / h2_total)
    (h_all_pos : 0 < h2_region ∧ 0 < h2_total ∧ 0 < M_region ∧ 0 < M_total)
    (h_α_pos : 0 < α) :
    β / α < heritabilityEnrichment h2_region M_region h2_total M_total := by
  obtain ⟨h_hc, h_ht, h_mc, h_mt⟩ := h_all_pos
  have hv : M_region < α * M_total := by rwa [div_lt_iff₀ h_mt] at h_prop_variants
  have hh : β * h2_total < h2_region := by rwa [lt_div_iff₀ h_ht] at h_prop_h2
  have hsimpl : heritabilityEnrichment h2_region M_region h2_total M_total =
    h2_region * M_total / (M_region * h2_total) := by
    unfold heritabilityEnrichment; field_simp
  rw [hsimpl, div_lt_div_iff₀ h_α_pos (mul_pos h_mc h_ht)]
  nlinarith

/-- **Squaring is strictly monotone on the nonnegatives:** `0 ≤ a`, `0 ≤ b`,
    `b < a` give `b² < a²`.

    **Both halves of the genetics are hypotheses.** The reading is that coding
    regions are under stronger purifying selection, hence effect sizes there are
    more correlated across populations (`rg_coding > rg_regulatory`), hence —
    since portability goes as `rg²` — coding variants port better. The first
    implication is assumed outright as `h_coding_higher`, and the second is
    assumed by choosing to square. No selection, no region annotation, and no
    portability measure appears below. What remains is `x ↦ x²` monotone on
    `[0, ∞)`. -/
theorem sq_lt_sq_of_nonneg_of_lt
    (rg_coding rg_regulatory : ℝ)
    (h_coding_nn : 0 ≤ rg_coding) (h_reg_nn : 0 ≤ rg_regulatory)
    (h_coding_higher : rg_regulatory < rg_coding) :
    rg_regulatory ^ 2 < rg_coding ^ 2 := by
  -- x² is strictly monotone on [0, ∞): if 0 ≤ a < b then a² < b²
  have h_sum_nonneg : 0 ≤ rg_coding + rg_regulatory := add_nonneg h_coding_nn h_reg_nn
  nlinarith

end HeritabilityPartitioning


/-!
## Architecture-Dependent Portability Predictions

Given estimated genetic architecture parameters, we can predict
expected portability for a trait across ancestries.
-/

section ArchitecturePredictions

open SNPArchitecturePortabilityModel

/-- **Portability prediction from explicit causal-SNP architecture.**

The predicted portability is the fraction of source causal squared-effect mass
that remains transportable in the target after aggregating over causal SNPs.
This keeps the prediction surface at the SNP architecture level rather than
collapsing it into a single trait-wide `r_g² × (1 - FST)` product. -/
noncomputable def predictedPortability {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.portabilityScore

/-- Predicted portability is at most the full source causal signal mass. -/
theorem predicted_le_source {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    predictedPortability model ≤ 1 := by
  simpa [predictedPortability] using portabilityScore_le_one model h_source

/-- Source-effect-weighted average of per-SNP retention upper envelopes.

Each `retentionUpper j` is an explicit SNP-level upper bound on the fraction of
source squared-effect mass that can survive in the target at causal SNP `j`. -/
noncomputable def weightedRetentionUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ) : ℝ :=
  (∑ j, retentionUpper j * model.sourceSquaredEffect j) /
    model.sourceEffectMass

/-- Any locuswise retention upper envelope induces a global portability upper
bound after weighting by source causal effect mass. -/
theorem predicted_le_weightedRetentionUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ)
    (h_source : 0 < model.sourceEffectMass)
    (h_bound : ∀ j,
      model.targetRetainedSquaredEffect j ≤
        retentionUpper j * model.sourceSquaredEffect j) :
    predictedPortability model ≤ weightedRetentionUpperBound model retentionUpper := by
  unfold predictedPortability weightedRetentionUpperBound portabilityScore
  have h_sum :
      model.targetRetainedEffectMass ≤
        ∑ j, retentionUpper j * model.sourceSquaredEffect j := by
    unfold targetRetainedEffectMass
    exact Finset.sum_le_sum fun j _ ↦ h_bound j
  exact (div_le_div_iff_of_pos_right h_source).2 h_sum

/-- **The slack in the retention envelope, as an identity rather than a
bound.**

The one-sided statement `predicted_le_weightedRetentionUpperBound` says only
that the envelope is above the truth. What is above it by is the
source-effect-weighted average of the locuswise slacks, and that is an equality
with no hypotheses on the envelope at all — not even that it is an upper bound.
The inequality and the attainment condition are both corollaries. -/
theorem weightedRetentionUpperBound_sub_predicted {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ) :
    weightedRetentionUpperBound model retentionUpper - predictedPortability model =
      (∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j)) / model.sourceEffectMass := by
  unfold weightedRetentionUpperBound predictedPortability portabilityScore
    targetRetainedEffectMass
  rw [div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib]

/-- **Threshold equals capacity when the locuswise constraint is active.**

If the envelope is attained at every causal SNP, the global portability equals
the global bound. No symmetry of the architecture is needed and no condition on
the effect distribution: activity of the constraint at each locus is the whole
hypothesis. -/
theorem predicted_eq_weightedRetentionUpperBound_of_active {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ)
    (h_active : ∀ j, model.targetRetainedSquaredEffect j =
      retentionUpper j * model.sourceSquaredEffect j) :
    predictedPortability model = weightedRetentionUpperBound model retentionUpper := by
  have h_sum : model.targetRetainedEffectMass =
      ∑ j, retentionUpper j * model.sourceSquaredEffect j := by
    unfold targetRetainedEffectMass
    exact Finset.sum_congr rfl (fun j _ ↦ h_active j)
  unfold predictedPortability weightedRetentionUpperBound portabilityScore
  rw [h_sum]

/-- **The bound is attained if and only if every locuswise constraint is
active.**

The two-sided form: under the locuswise envelope, global portability meets the
global bound exactly when no causal SNP has slack. One slack locus with positive
source mass is enough to make the bound strict, and no amount of activity
elsewhere compensates. -/
theorem weightedRetentionUpperBound_eq_predicted_iff_active {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ)
    (h_source : 0 < model.sourceEffectMass)
    (h_bound : ∀ j, model.targetRetainedSquaredEffect j ≤
      retentionUpper j * model.sourceSquaredEffect j) :
    weightedRetentionUpperBound model retentionUpper = predictedPortability model ↔
      ∀ j, model.targetRetainedSquaredEffect j =
        retentionUpper j * model.sourceSquaredEffect j := by
  have hid := weightedRetentionUpperBound_sub_predicted model retentionUpper
  constructor
  · intro h
    have hz : (∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j)) / model.sourceEffectMass = 0 := by
      rw [← hid, h, sub_self]
    have hz' : ∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j) = 0 := by
      rcases div_eq_zero_iff.mp hz with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt h_source)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sub_nonneg.mpr (h_bound j))).mp hz'
    intro j
    have hj := hall j (Finset.mem_univ j)
    linarith [hj]
  · intro h
    have hz : ∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [h j]
      ring
    rw [← sub_eq_zero, hid, hz, zero_div]

/-- **Architecture-based trait classification.**

Traits are ranked by their explicit causal-SNP loss fractions, not by a bare
scalar portability label. A trait with a smaller fraction of lost causal signal
has a larger retained portability score. -/
theorem architecture_classification
    {q_high q_moderate q_oligo : ℕ}
    (highPoly : SNPArchitecturePortabilityModel q_high)
    (moderate : SNPArchitecturePortabilityModel q_moderate)
    (oligo : SNPArchitecturePortabilityModel q_oligo)
    (h_high_source : 0 < highPoly.sourceEffectMass)
    (h_moderate_source : 0 < moderate.sourceEffectMass)
    (h_oligo_source : 0 < oligo.sourceEffectMass)
    (h_loss_order :
      highPoly.relativePortabilityLoss < moderate.relativePortabilityLoss ∧
        moderate.relativePortabilityLoss < oligo.relativePortabilityLoss) :
    predictedPortability oligo < predictedPortability moderate ∧
      predictedPortability moderate < predictedPortability highPoly := by
  rcases h_loss_order with ⟨h_high_moderate, h_moderate_oligo⟩
  constructor
  · rw [predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss oligo h_oligo_source,
      predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss moderate h_moderate_source]
    linarith
  · rw [predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss moderate h_moderate_source,
      predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss highPoly h_high_source]
    linarith

/-- Locuswise `r_g² × (1 - FST)` upper envelope for retained causal signal.

This is not a single trait-wide multiplicative law. Instead, each causal SNP
gets its own upper envelope from a locus-specific effect-correlation bound
`rgUpper j` and a locus-specific divergence lower bound `fstLower j`, and the
global portability bound is their source-effect-weighted average.

    Empirical status: UNTESTED. -/
noncomputable def rgFstWeightedUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (rgUpper fstLower : Fin q → ℝ) : ℝ :=
  weightedRetentionUpperBound model
    (fun j ↦ (rgUpper j) ^ 2 * (1 - fstLower j))

/-- **Explicit SNP-level portability upper bound from locuswise effect
correlation and causal divergence.**

If each causal SNP retains at most `rgUpper(j)^2 * (1 - fstLower(j))` of its
source squared-effect mass in the target, then total portability is bounded by
the source-effect-weighted average of those locuswise envelopes. -/
theorem portability_upper_bound_from_rg_fst
    {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (rgUpper fstLower : Fin q → ℝ)
    (h_source : 0 < model.sourceEffectMass)
    (h_locuswise_bound : ∀ j,
      model.targetRetainedSquaredEffect j ≤
        (rgUpper j) ^ 2 * (1 - fstLower j) * model.sourceSquaredEffect j) :
    predictedPortability model ≤ rgFstWeightedUpperBound model rgUpper fstLower := by
  unfold rgFstWeightedUpperBound
  exact predicted_le_weightedRetentionUpperBound model
    (fun j ↦ (rgUpper j) ^ 2 * (1 - fstLower j))
    h_source h_locuswise_bound

end ArchitecturePredictions

end Calibrator
