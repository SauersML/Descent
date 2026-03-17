import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

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

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Effect Size Distribution

The distribution of per-variant effect sizes determines
how PGS portability scales with sample size and ancestry.
-/

section EffectSizeDistribution

/-- **Exponential distribution of squared effects.**
    Under the infinitesimal model: β² ~ Exponential(1/σ²)
    where σ² = h²/M (heritability divided by number of variants). -/
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
    π is the polygenicity parameter. -/
noncomputable def spikeAndSlabVariance (pi sigma_sq_large sigma_sq_small : ℝ) : ℝ :=
  pi * sigma_sq_large + (1 - pi) * sigma_sq_small

/-- Spike-and-slab variance increases with polygenicity
    when the slab dominates. -/
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
    = (Σ β²_j)² / Σ β⁴_j (inverse kurtosis measure). -/
noncomputable def effectivePolygenicity (sum_beta_sq sum_beta_fourth : ℝ) : ℝ :=
  sum_beta_sq^2 / sum_beta_fourth

/-- Effective polygenicity ≥ 1. -/
theorem effective_polygenicity_ge_one
    (sum_sq sum_fourth : ℝ)
    (h_fourth : 0 < sum_fourth)
    (h_cs : sum_fourth ≤ sum_sq^2) :
    1 ≤ effectivePolygenicity sum_sq sum_fourth := by
  unfold effectivePolygenicity
  rw [le_div_iff₀ h_fourth]
  linarith

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

namespace SNPArchitecturePortabilityModel

/-- Total causal signal mass in the source architecture. -/
noncomputable def sourceEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  ∑ j, model.sourceSquaredEffect j

/-- Total causal signal mass still retained in the target architecture. -/
noncomputable def targetRetainedEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  ∑ j, model.targetRetainedSquaredEffect j

/-- Total signal mass lost across SNPs when transporting to the target. -/
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
  exact Fintype.sum_nonneg fun j => model.sourceSquaredEffect_nonneg j

theorem targetRetainedEffectMass_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    0 ≤ model.targetRetainedEffectMass := by
  unfold targetRetainedEffectMass
  exact Fintype.sum_nonneg fun j => model.targetRetained_nonneg j

theorem targetRetainedEffectMass_le_sourceEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    model.targetRetainedEffectMass ≤ model.sourceEffectMass := by
  unfold targetRetainedEffectMass sourceEffectMass
  exact Finset.sum_le_sum fun j _ => model.targetRetained_le_source j

/-- The relative portability loss is exactly the locuswise lost-effect mass
fraction. This is the explicit SNP-level replacement for the deleted CLT
`1 / √M` law. -/
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
  · exact Fintype.sum_nonneg fun j => sub_nonneg.mpr (model.targetRetained_le_source j)
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
        (mismatched₁.card : ℝ) / (M₁ : ℝ) := by
    exact (div_lt_div_iff_of_pos_left h_k_pos h_M₂_pos h_M₁_pos).2 (by exact_mod_cast h_M)
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
      uniformCatastrophicPortabilityScore M_height mismatchedHeight := by
  exact more_polygenic_more_portable mismatchedBMI mismatchedHeight h_M h_same_card h_loss

/-- **Selection can outweigh a polygenicity advantage.**

Even if the selected trait has more causal SNPs, it can still have worse
portability when the fraction of causal SNPs that lose target signal is larger.
This is the explicit-SNP replacement for the deleted `rg² × portabilityScore`
product theorem. -/
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
## Heritability Partitioning

Partitioning heritability by functional category reveals
which genomic features drive PGS signal and portability.
-/

section HeritabilityPartitioning

/-- **Heritability enrichment.**
    Enrichment of category c = (h²_c / M_c) / (h²_total / M_total).
    High enrichment means the category harbors more causal signal
    per variant. -/
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

/-- **Coding variants more portable than regulatory (from functional constraint).**
    Coding regions are under stronger purifying selection across all
    populations (protein sequences are conserved), so effect sizes at
    coding variants are more correlated cross-population: rg_coding > rg_reg.
    Since portability ∝ rg², and x ↦ x² is strictly monotone on [0,∞),
    higher rg implies higher portability.

    Derived: from rg_regulatory < rg_coding (both ≥ 0),
    the strict monotonicity of squaring on nonneg reals gives the result. -/
theorem coding_more_portable_than_regulatory
    (rg_coding rg_regulatory : ℝ)
    (h_coding_nn : 0 ≤ rg_coding) (h_reg_nn : 0 ≤ rg_regulatory)
    (h_coding_higher : rg_regulatory < rg_coding) :
    rg_regulatory ^ 2 < rg_coding ^ 2 := by
  -- x² is strictly monotone on [0, ∞): if 0 ≤ a < b then a² < b²
  have h_sum_nonneg : 0 ≤ rg_coding + rg_regulatory := add_nonneg h_coding_nn h_reg_nn
  nlinarith

/- **LDSC-SEG for partitioned heritability.**
    h²_c = M_c × (Σ_j∈c l_j × τ_c) / (N × Σ_j l_j)
    where τ_c is the per-SNP heritability coefficient for category c. -/

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
    exact Finset.sum_le_sum fun j _ => h_bound j
  exact (div_le_div_iff_of_pos_right h_source).2 h_sum

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
global portability bound is their source-effect-weighted average. -/
noncomputable def rgFstWeightedUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (rgUpper fstLower : Fin q → ℝ) : ℝ :=
  weightedRetentionUpperBound model
    (fun j => (rgUpper j) ^ 2 * (1 - fstLower j))

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
    (fun j => (rgUpper j) ^ 2 * (1 - fstLower j))
    h_source h_locuswise_bound

end ArchitecturePredictions

end Calibrator
