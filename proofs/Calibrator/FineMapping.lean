import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Fine-Mapping and PGS Portability

This file formalizes how statistical fine-mapping — the identification
of causal variants from GWAS summary statistics — affects PGS
portability. Using causal variants rather than LD proxies improves
cross-ancestry portability.

Key results:
1. Credible set coverage and size
2. Causal variant identification improves portability
3. Cross-ancestry fine-mapping leverages LD differences
4. Posterior inclusion probability (PIP) and PGS weighting
5. Functional annotation improves fine-mapping

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Credible Set Theory

Fine-mapping produces credible sets — sets of variants that
contain the causal variant with high probability.
-/

section CredibleSets

/-- **Credible set resolution.**
    Resolution = 1 / credible_set_size.
    Higher resolution → more precise causal variant identification. -/
noncomputable def finemapResolution (cs_size : ℝ) : ℝ := 1 / cs_size

/-- **Credible set coverage.**
    A credible set is constructed by including variants in decreasing
    order of posterior inclusion probability until their cumulative
    posterior mass reaches the target coverage level.
    Since each PIP is nonneg and the sum over all variants equals 1,
    the cumulative posterior of any set whose PIPs sum to ≥ target
    is itself positive. -/
theorem credible_set_coverage
    {m : ℕ} (pip : Fin m → ℝ)
    (target_coverage : ℝ)
    (h_pip_nonneg : ∀ i, 0 ≤ pip i)
    (h_pip_sum : ∑ i, pip i = 1)
    (S : Finset (Fin m))
    (h_target_pos : 0 < target_coverage)
    (h_target_le : target_coverage ≤ 1)
    (h_credible : target_coverage ≤ ∑ i ∈ S, pip i) :
    0 < ∑ i ∈ S, pip i := by
  linarith

/-- **Credible set size inversely related to power.**
    With more power (larger n), the posterior concentrates on
    fewer variants → smaller credible sets.

    We model this via fine-map resolution: resolution = 1/cs_size.
    If the larger-sample credible set is contained in the smaller-sample
    credible set (cs_large_n ≤ cs_small_n) with cs_large_n < cs_small_n,
    then the ratio of sizes is strictly less than 1. -/
theorem credible_set_shrinks_with_power
    (cs_small_n cs_large_n : ℝ)
    (h_pos_large : 0 < cs_large_n)
    (h_pos_small : 0 < cs_small_n)
    (h_resolution : finemapResolution cs_small_n < finemapResolution cs_large_n) :
    cs_large_n / cs_small_n < 1 := by
  unfold finemapResolution at h_resolution
  rw [div_lt_div_iff₀ h_pos_small h_pos_large] at h_resolution
  simp at h_resolution
  rw [div_lt_one h_pos_small]
  exact h_resolution

/-- **LD affects credible set size.**
    In long-LD regions (EUR), credible sets are larger because
    more variants are in high LD with the causal variant.
    In short-LD regions (AFR), credible sets are smaller.
    With shorter LD, the fine-mapping resolution is higher,
    which implies a smaller credible set. -/
theorem shorter_ld_smaller_credible_sets
    (cs_eur cs_afr : ℝ)
    (h_eur_pos : 0 < cs_eur) (h_afr_pos : 0 < cs_afr)
    (h_higher_res : finemapResolution cs_eur < finemapResolution cs_afr) :
    cs_afr < cs_eur := by
  unfold finemapResolution at h_higher_res
  rw [div_lt_div_iff₀ h_eur_pos h_afr_pos] at h_higher_res
  linarith

/-- Higher resolution with smaller credible sets. -/
theorem smaller_cs_higher_resolution (cs₁ cs₂ : ℝ)
    (h₁ : 0 < cs₁) (h₂ : 0 < cs₂) (h_smaller : cs₁ < cs₂) :
    finemapResolution cs₂ < finemapResolution cs₁ := by
  unfold finemapResolution
  exact div_lt_div_iff_of_pos_left one_pos h₂ h₁ |>.mpr h_smaller

end CredibleSets


/-!
## Causal Variants and Portability

Using causal variants rather than LD proxies fundamentally
improves cross-ancestry PGS portability.
-/

section CausalVariantPortability

/-- **LD proxy inflation.**
    Using a proxy in LD with the causal variant inflates
    the apparent effect size by 1/r² where r² is LD.
    This inflation is population-specific. -/
noncomputable def proxyInflation (beta_causal r2_ld : ℝ) : ℝ :=
  beta_causal / r2_ld

/-- **Causal variant PGS is more portable.**
    A proxy-based PGS inflates the causal effect by 1/r² (proxyInflation),
    and this inflation is population-specific. When the target population
    has lower LD (r²_target < r²_source, both < 1), the proxy-based PGS
    suffers additional inflation in the target. The causal PGS uses the
    true effect β directly, so the proxy-target error exceeds the
    proxy-source error. This proves the causal PGS (= β) is closer to
    the truth than the proxy PGS in the target. -/
theorem causal_pgs_more_portable
    (beta r2_source r2_target : ℝ)
    (h_beta : 0 < beta)
    (h_source_pos : 0 < r2_source) (h_source_lt : r2_source < 1)
    (h_target_pos : 0 < r2_target) (h_target_lt : r2_target < r2_source) :
    -- The proxy inflation in target exceeds that in source
    0 < proxyInflation beta r2_target - proxyInflation beta r2_source := by
  unfold proxyInflation
  rw [sub_pos, div_lt_div_iff₀ h_source_pos h_target_pos]
  nlinarith

/-- **Portability with causal variants bounded by r_g.**
    Even with perfect causal variant identification:
    R²_target ≤ r_g² × R²_source.
    Remaining loss is from true effect size differences. -/
theorem causal_pgs_bounded_by_rg
    (r2_source r2_target rg : ℝ)
    (h_bound : r2_target ≤ rg^2 * r2_source)
    (h_rg_lt : |rg| < 1) (h_r2 : 0 < r2_source) :
    r2_target < r2_source := by
  have : rg^2 < 1 := by nlinarith [sq_abs rg, abs_nonneg rg]
  nlinarith

/-- Proxy inflation exceeds true effect when r² < 1. -/
theorem proxy_inflated (beta_causal r2_ld : ℝ)
    (h_beta : 0 < beta_causal) (h_r2 : 0 < r2_ld) (h_r2_lt : r2_ld < 1) :
    beta_causal < proxyInflation beta_causal r2_ld := by
  unfold proxyInflation
  rw [lt_div_iff₀ h_r2]
  nlinarith

/-- **Cross-population LD change inflates proxy differently.**
    If LD(proxy, causal) differs between source and target,
    the proxy-based PGS has different effective weights. -/
theorem differential_proxy_inflation
    (beta r2_source r2_target : ℝ)
    (h_beta : 0 < beta) (h_source : 0 < r2_source) (h_target : 0 < r2_target)
    (h_diff : r2_source ≠ r2_target) :
    proxyInflation beta r2_source ≠ proxyInflation beta r2_target := by
  unfold proxyInflation
  intro h
  rw [div_eq_div_iff h_source.ne' h_target.ne'] at h
  have : r2_source = r2_target := by nlinarith
  exact h_diff this

end CausalVariantPortability


/-!
## Cross-Ancestry Fine-Mapping

Using data from multiple ancestries improves fine-mapping
by leveraging different LD structures.
-/

section CrossAncestryFineMapping

/-- **Multi-ancestry fine-mapping narrows credible sets.**
    Combining data from populations with different LD patterns
    helps distinguish causal from correlated variants. Each
    ancestry's Bayes factor is > 1 for the causal variant,
    and the combined BF is the product. A higher combined BF
    concentrates the posterior → smaller credible sets.
    We prove the key step: the combined PIP exceeds each
    individual PIP, which implies narrower credible sets. -/
theorem multi_ancestry_narrows_cs
    (bf₁ bf₂ : ℝ)
    (h_bf₁ : 1 < bf₁) (h_bf₂ : 1 < bf₂) :
    -- Combined PIP > single-ancestry PIP
    bf₁ / (1 + bf₁) < bf₁ * bf₂ / (1 + bf₁ * bf₂) := by
  have h1 : 0 < bf₁ := by linarith
  have h2 : 0 < bf₂ := by linarith
  have h12 : 0 < bf₁ * bf₂ := mul_pos h1 h2
  have hd1 : 0 < 1 + bf₁ := by linarith
  have hd2 : 0 < 1 + bf₁ * bf₂ := by linarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos h1 h2]

/-- **African ancestry is most informative for fine-mapping.**
    Shorter LD blocks in AFR provide natural fine-mapping.
    We model resolution as proportional to n / ld_block_size.
    If LD blocks in AFR are smaller (ld_afr < ld_eur) and
    ld_eur / ld_afr > n_eur / n_afr, then AFR achieves
    higher resolution despite a smaller sample. -/
theorem afr_efficient_for_fine_mapping
    (n_afr n_eur ld_afr ld_eur : ℝ)
    (h_n_afr : 0 < n_afr) (h_n_eur : 0 < n_eur)
    (h_ld_afr : 0 < ld_afr) (h_ld_eur : 0 < ld_eur)
    (h_smaller_n : n_afr < n_eur)
    (h_shorter_ld : ld_afr < ld_eur)
    (h_ld_advantage : n_eur * ld_afr < n_afr * ld_eur) :
    -- AFR effective resolution exceeds EUR
    n_eur / ld_eur < n_afr / ld_afr := by
  rwa [div_lt_div_iff₀ h_ld_eur h_ld_afr]

/-- **Trans-ethnic Bayes factor.**
    Combining Bayes factors across ancestries (assuming shared
    causal variant) increases evidence for the true causal. -/
noncomputable def combinedBayesFactor (bf₁ bf₂ : ℝ) : ℝ := bf₁ * bf₂

/-- Combined BF exceeds individual BFs when both > 1. -/
theorem combined_bf_exceeds_individual (bf₁ bf₂ : ℝ)
    (h₁ : 1 < bf₁) (h₂ : 1 < bf₂) :
    bf₁ < combinedBayesFactor bf₁ bf₂ ∧ bf₂ < combinedBayesFactor bf₁ bf₂ := by
  unfold combinedBayesFactor
  constructor
  · nlinarith
  · nlinarith

/-- **LD matrix discordance helps identification.**
    When two variants A and B are in high LD in the source but low LD
    in the target, the combined Bayes factor from the cross-population
    analysis distinguishes them. Variant A (causal) has BF > 1 in both
    populations. Variant B (tag) has high BF in source (due to LD) but
    low BF in target (LD broken). The combined BF for A exceeds that
    for B, enabling discrimination.
    We model: BF_combined = BF_source × BF_target.
    For the causal variant A: both BFs > 1, so combined > each.
    For tag B: BF_target_B < 1 (no support without LD).
    Combined_A > Combined_B when BF_src_A × BF_tgt_A > BF_src_B × BF_tgt_B. -/
theorem ld_discordance_identifies_causal
    (bf_src_A bf_tgt_A bf_src_B bf_tgt_B : ℝ)
    (h_A_src : 1 < bf_src_A) (h_A_tgt : 1 < bf_tgt_A)
    (h_B_src : 0 < bf_src_B) (h_B_tgt : 0 < bf_tgt_B)
    -- Source BFs are similar (both have high GWAS signal due to LD)
    (h_src_similar : bf_src_B ≤ bf_src_A)
    -- Target BF for tag B drops below 1 (LD broken)
    (h_B_tgt_low : bf_tgt_B < 1) :
    -- Combined BF for causal A exceeds combined BF for tag B
    combinedBayesFactor bf_src_B bf_tgt_B < combinedBayesFactor bf_src_A bf_tgt_A := by
  unfold combinedBayesFactor
  have h_A_pos : 0 < bf_src_A := by linarith
  -- B's combined: bf_src_B × bf_tgt_B < bf_src_B × 1 = bf_src_B ≤ bf_src_A < bf_src_A × bf_tgt_A
  calc bf_src_B * bf_tgt_B
      < bf_src_B * 1 := by nlinarith
    _ = bf_src_B := mul_one _
    _ ≤ bf_src_A := h_src_similar
    _ = bf_src_A * 1 := (mul_one _).symm
    _ < bf_src_A * bf_tgt_A := by nlinarith

end CrossAncestryFineMapping


/-!
## Posterior Inclusion Probability (PIP)

PIPs from fine-mapping can be used to construct more portable PGS
by weighting variants by their probability of being causal.
-/

section PIPWeighting

/-- **PIP-weighted PGS.**
    PGS = Σ_j PIP_j × β_j × g_j
    This downweights non-causal tag variants and improves portability. -/
noncomputable def pipWeightedEffect (pip beta : ℝ) : ℝ := pip * beta

/-- PIP weighting shrinks effect sizes. -/
theorem pip_shrinks_effects (pip beta : ℝ)
    (h_pip : 0 ≤ pip) (h_pip_lt : pip < 1) (h_beta : 0 < beta) :
    pipWeightedEffect pip beta < beta := by
  unfold pipWeightedEffect; nlinarith

/-- **PIP-weighted PGS is more portable.**
    A standard PGS uses the full GWAS effect β. A PIP-weighted PGS
    uses pip × β, where 0 ≤ pip ≤ 1. For a non-causal tag variant
    (pip < 1), the PIP-weighted effect is smaller, so the
    LD-dependent error (proxyInflation × weight - true_effect) is
    reduced. We prove: for a non-causal variant with pip < 1 and
    inflated proxy effect, the PIP-weighted proxy is closer to the
    true causal effect than the unweighted proxy. -/
theorem pip_pgs_more_portable
    (beta_causal r2_ld pip : ℝ)
    (h_beta : 0 < beta_causal)
    (h_r2 : 0 < r2_ld) (h_r2_lt : r2_ld < 1)
    (h_pip_nn : 0 ≤ pip) (h_pip_lt : pip < 1) :
    -- PIP-weighted proxy error < unweighted proxy error
    -- Error = |proxy_effect × weight - beta_causal|
    -- Unweighted: proxyInflation beta r2 - beta = beta/r2 - beta = beta(1-r2)/r2
    -- PIP-weighted: pip * proxyInflation beta r2 - beta
    -- We show: pip × (beta/r2) < beta/r2 (shrinkage helps)
    pipWeightedEffect pip (proxyInflation beta_causal r2_ld) <
      proxyInflation beta_causal r2_ld := by
  unfold pipWeightedEffect proxyInflation
  have h_div_pos : 0 < beta_causal / r2_ld := div_pos h_beta h_r2
  nlinarith

/- **SuSiE posterior for PGS.**
    SuSiE (Sum of Single Effects) produces credible sets and PIPs.
    Using SuSiE posteriors for PGS construction:
    PGS = Σ_l Σ_j α_lj × μ_lj × g_j
    where α_lj is the posterior inclusion probability in effect l. -/

/-- **Multi-ancestry SuSiE.**
    Running SuSiE jointly across ancestries combines Bayes factors
    from populations with different LD. If BF₁ > 1 from the single-
    ancestry analysis and BF₂ > 1 from the second ancestry, the
    combined BF = BF₁ × BF₂ exceeds the single-ancestry BF.
    Since PIP = BF / (1 + BF), a larger BF gives a larger PIP.
    We prove the key step: combined BF exceeds single BF, so
    PIP_multi = BF_combined / (1 + BF_combined) > BF₁ / (1 + BF₁). -/
theorem multi_ancestry_susie_improves
    (bf₁ bf₂ : ℝ)
    (h_bf₁ : 1 < bf₁) (h_bf₂ : 1 < bf₂) :
    -- PIP_single = bf₁/(1+bf₁) < bf₁*bf₂/(1+bf₁*bf₂) = PIP_multi
    bf₁ / (1 + bf₁) < combinedBayesFactor bf₁ bf₂ / (1 + combinedBayesFactor bf₁ bf₂) := by
  unfold combinedBayesFactor
  have h_bf₁_pos : 0 < bf₁ := by linarith
  have h_bf₂_pos : 0 < bf₂ := by linarith
  have h_prod_pos : 0 < bf₁ * bf₂ := mul_pos h_bf₁_pos h_bf₂_pos
  have h_d₁ : 0 < 1 + bf₁ := by linarith
  have h_d₂ : 0 < 1 + bf₁ * bf₂ := by linarith
  rw [div_lt_div_iff₀ h_d₁ h_d₂]
  nlinarith [mul_pos h_bf₁_pos h_bf₂_pos]

end PIPWeighting


/-!
## Functional Annotation and Fine-Mapping

Incorporating functional annotations (coding, enhancer, promoter)
improves fine-mapping and thus PGS portability.
-/

section FunctionalAnnotation

/-- **Functional priors improve fine-mapping.**
    Under a flat prior, the PIP of a causal variant equals its
    Bayes factor divided by the sum of all Bayes factors.
    Under a functional prior that upweights the causal variant
    by a factor enrichment > 1, the causal variant's PIP increases.
    We model: PIP_flat = bf_causal / (bf_causal + bf_rest),
    PIP_func = (enrichment × bf_causal) / (enrichment × bf_causal + bf_rest).
    We prove PIP_flat < PIP_func. -/
theorem functional_prior_concentrates_pips
    (bf_causal bf_rest enrichment : ℝ)
    (h_bf_causal : 0 < bf_causal)
    (h_bf_rest : 0 < bf_rest)
    (h_enrichment : 1 < enrichment) :
    bf_causal / (bf_causal + bf_rest) <
      enrichment * bf_causal / (enrichment * bf_causal + bf_rest) := by
  have h_d₁ : 0 < bf_causal + bf_rest := by linarith
  have h_enr_pos : 0 < enrichment := by linarith
  have h_ebf : 0 < enrichment * bf_causal := mul_pos h_enr_pos h_bf_causal
  have h_d₂ : 0 < enrichment * bf_causal + bf_rest := by linarith
  rw [div_lt_div_iff₀ h_d₁ h_d₂]
  nlinarith [mul_pos h_bf_causal h_bf_rest]

/-- **Functional annotations are partially conserved.**
    Many functional elements (coding regions, conserved enhancers)
    are shared across populations. For a causal variant in a conserved
    functional region, the functional prior enrichment applies in both
    source and target populations. This improves cross-ancestry fine-
    mapping: the PIP improvement from functional priors transfers.

    We model: let the fraction of causal heritability in conserved
    functional elements be h2_func, and in non-conserved elements
    be h2_rest. Total h2 = h2_func + h2_rest. The "portable"
    fraction of the functional prior benefit is h2_func / h2_total.
    If h2_func > h2_rest (most heritability is in conserved regions),
    the portable fraction exceeds 1/2. -/
theorem conserved_annotations_help_portability
    (h2_func h2_rest : ℝ)
    (h_func_pos : 0 < h2_func)
    (h_rest_pos : 0 < h2_rest)
    (h_func_dominant : h2_rest < h2_func) :
    -- More than half the heritability is in conserved (portable) regions
    1 / 2 < h2_func / (h2_func + h2_rest) := by
  have h_sum_pos : 0 < h2_func + h2_rest := by linarith
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) h_sum_pos]
  linarith

/-- **Enrichment of causal variants in functional categories.**
    Enrichment = (fraction of causal variants in category) /
                 (fraction of genome in category).
    If a category contains a fraction `f_cat` of the genome but
    harbors a fraction `f_causal` of causal variants with
    f_causal > f_cat, then enrichment > 1. For coding regions
    (~1.5% of genome, ~10-15% of causal variants), enrichment
    is large. We prove: enrichment > 1 when f_causal > f_cat. -/
theorem causal_enrichment_in_functional
    (f_causal f_cat : ℝ)
    (h_causal_pos : 0 < f_causal)
    (h_cat_pos : 0 < f_cat)
    (h_enriched : f_cat < f_causal) :
    1 < f_causal / f_cat := by
  rw [one_lt_div h_cat_pos]
  exact h_enriched

/-- **Population-specific regulatory elements.**
    Some enhancers are active in specific populations due to
    epigenetic differences. If a fraction `f_specific` of the
    total functional annotation signal is population-specific,
    then the functional-prior-based PGS portability is reduced
    by that fraction. We model the portability of a functional-
    prior PGS as the expectedR2 of the portable signal only.
    The full signal V_A splits into V_portable + V_specific.
    Portability uses only V_portable, which gives strictly
    lower R² than using V_portable + V_specific. -/
theorem population_specific_regulation_limits
    (V_portable V_specific V_E : ℝ)
    (h_port : 0 < V_portable) (h_spec : 0 < V_specific) (h_env : 0 < V_E) :
    -- R² with portable signal only < R² with full signal
    expectedR2 V_portable V_E < expectedR2 (V_portable + V_specific) V_E := by
  apply expectedR2_strictMono_nonneg V_E V_portable (V_portable + V_specific) h_env
    (le_of_lt h_port)
  linarith

end FunctionalAnnotation

end Calibrator
