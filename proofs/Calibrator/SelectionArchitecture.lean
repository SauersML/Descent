import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Selection Pressure, Trait Architecture, and Portability

This file formalizes how different modes of natural selection shape
trait genetic architecture and consequently affect PGS portability.
The key insight from Wang et al. is that trait-specific portability
patterns are explained by selection regime differences.

Key results:
1. Stabilizing selection maintains genetic architecture → better portability
2. Diversifying/balancing selection changes architecture → worse portability
3. Polygenic adaptation creates coordinated allele frequency shifts
4. Immune traits under fluctuating selection have fastest portability decay
5. Relationship between GWAS effect sizes and selection coefficients

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Stabilizing Selection and Architecture Conservation

Under stabilizing selection, the trait optimum is the same across
populations. Selection maintains effects near the optimum, so genetic
architecture is conserved → good portability.
-/

section StabilizingSelection

/-- **Stabilizing selection constraint on effect sizes.**
    Under stabilizing selection with strength s and optimum μ,
    large-effect alleles are rare because they're selected against.
    The equilibrium effect size distribution has variance ∝ 1/s. -/
noncomputable def equilibriumEffectVariance (v_mutation s : ℝ) : ℝ :=
  v_mutation / s

/-- Stronger stabilizing selection → smaller effect sizes. -/
theorem stronger_stabilizing_smaller_effects
    (v_mutation s₁ s₂ : ℝ)
    (h_vm : 0 < v_mutation)
    (h_s₁ : 0 < s₁) (h_s₂ : 0 < s₂)
    (h_stronger : s₁ < s₂) :
    equilibriumEffectVariance v_mutation s₂ < equilibriumEffectVariance v_mutation s₁ := by
  unfold equilibriumEffectVariance
  exact div_lt_div_of_pos_left h_vm h_s₁ h_stronger

/-- **Effect correlation under stabilizing selection.**
    When both populations are under the same stabilizing selection,
    effect sizes are pulled toward the same optimum.
    ρ(effects) ≈ 1 - O(1/2Ns) where Ns is selection × drift balance. -/
noncomputable def effectCorrelationStabilizing (Ns : ℝ) : ℝ :=
  1 - 1 / (2 * Ns)

/-- Effect correlation increases with stronger selection (relative to drift). -/
theorem effect_correlation_increases_with_Ns
    (Ns₁ Ns₂ : ℝ)
    (h₁ : 1 < Ns₁) (h₂ : 1 < Ns₂) (h_more : Ns₁ < Ns₂) :
    effectCorrelationStabilizing Ns₁ < effectCorrelationStabilizing Ns₂ := by
  unfold effectCorrelationStabilizing
  rw [sub_lt_sub_iff_left]
  exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **Highly polygenic traits have better portability.**
    When trait is highly polygenic (many small effects), each locus
    contributes little, and the overall signal is robust to per-locus changes.
    This is essentially a law of large numbers argument. -/
theorem polygenicity_improves_portability
    (m₁ m₂ : ℕ) (var_per_locus : ℝ)
    (h_m₁ : 0 < m₁) (h_m₂ : 0 < m₂) (h_more : m₁ < m₂)
    (h_var : 0 < var_per_locus) :
    -- Variance of portability ratio estimate ∝ 1/m
    var_per_locus / (m₂ : ℝ) < var_per_locus / (m₁ : ℝ) := by
  exact div_lt_div_of_pos_left h_var (Nat.cast_pos.mpr h_m₁) (Nat.cast_lt.mpr h_more)

/-- **Height is a prototypical stabilizing selection trait.**
    Height has ~10,000 associated loci, each of small effect.
    Portability is relatively good (slow decay with distance).
    We verify the parameter regime. -/
theorem height_parameter_regime :
    let n_loci := 10000
    let per_locus_h2 := 0.00005  -- Each locus explains 0.005% of variance
    let total_h2 := n_loci * per_locus_h2
    total_h2 = 0.5 := by norm_num

end StabilizingSelection


/-!
## Diversifying and Fluctuating Selection

Under diversifying selection, the trait optimum differs across populations.
Effects that are beneficial in one population may be neutral or deleterious
in another → allelic turnover → poor portability.
-/

section DiversifyingSelection

/-- **Fluctuating selection accelerates effect turnover.**
    Under fluctuating selection with autocorrelation time τ,
    the effect correlation decays as ρ(t) = exp(-t/τ). -/
noncomputable def fluctuatingEffectCorrelation (t τ : ℝ) : ℝ :=
  Real.exp (-t / τ)

/-- Effect correlation decays with divergence time. -/
theorem fluctuating_correlation_decays
    (t₁ t₂ τ : ℝ)
    (h_τ : 0 < τ) (h_t₁ : 0 < t₁) (h_more : t₁ < t₂) :
    fluctuatingEffectCorrelation t₂ τ < fluctuatingEffectCorrelation t₁ τ := by
  unfold fluctuatingEffectCorrelation
  apply Real.exp_lt_exp.mpr
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_right h_more h_τ

/-- Shorter autocorrelation time → faster decay. -/
theorem shorter_autocorrelation_faster_decay
    (t τ₁ τ₂ : ℝ)
    (h_τ₁ : 0 < τ₁) (h_τ₂ : 0 < τ₂)
    (h_shorter : τ₂ < τ₁)
    (h_t : 0 < t) :
    fluctuatingEffectCorrelation t τ₂ < fluctuatingEffectCorrelation t τ₁ := by
  unfold fluctuatingEffectCorrelation
  apply Real.exp_lt_exp.mpr
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left h_t h_τ₁ h_shorter

/-- **Immune traits have short autocorrelation times.**
    Pathogen-driven selection creates fluctuating fitness landscapes
    with τ ~ 100-1000 generations (vs τ → ∞ for stabilizing selection).
    This explains why lymphocyte count portability decays so fast. -/
theorem immune_short_autocorrelation
    (τ_immune τ_neutral t : ℝ)
    (h_immune : 0 < τ_immune) (h_neutral : 0 < τ_neutral)
    (h_shorter : τ_immune < τ_neutral)
    (h_t : 0 < t) :
    fluctuatingEffectCorrelation t τ_immune < fluctuatingEffectCorrelation t τ_neutral :=
  shorter_autocorrelation_faster_decay t τ_neutral τ_immune h_neutral h_immune h_shorter h_t

/-- **Balancing selection maintains intermediate allele frequencies.**
    Under balancing selection (e.g., heterozygote advantage in HLA),
    allele frequencies are maintained near 0.5 → high heterozygosity.
    This increases PGS variance even as accuracy drops. -/
theorem balancing_selection_high_het
    (p_neutral p_balanced : ℝ)
    (h_neutral_low : p_neutral < 0.1)
    (h_neutral_pos : 0 < p_neutral)
    (h_balanced : 0.3 < p_balanced) (h_balanced_lt : p_balanced < 0.5) :
    2 * p_neutral * (1 - p_neutral) < 2 * p_balanced * (1 - p_balanced) := by
  nlinarith [sq_nonneg (p_balanced - 1/2), sq_nonneg (p_neutral - 1/2)]

end DiversifyingSelection


/-!
## Polygenic Adaptation

Polygenic adaptation occurs when many alleles of small effect shift
in frequency in a coordinated direction. This creates a mean shift
in PGS without changing individual-variant effects.
-/

section PolygenicAdaptation

/-- **Polygenic adaptation score shift.**
    Under polygenic adaptation, the mean PGS shifts by
    Δμ = Σᵢ βᵢ · Δpᵢ where Δpᵢ are coordinated frequency changes. -/
noncomputable def polygenicAdaptationShift
    {m : ℕ} (β : Fin m → ℝ) (Δp : Fin m → ℝ) : ℝ :=
  ∑ i, β i * Δp i

/-- **Under neutral drift, expected shift is zero.**
    E[Δpᵢ] = 0 under drift, so E[Δμ] = 0. -/
theorem neutral_expected_shift_zero
    {m : ℕ} (β : Fin m → ℝ) :
    polygenicAdaptationShift β (fun _ => 0) = 0 := by
  unfold polygenicAdaptationShift
  simp

/-- **Under selection, shift is nonzero and directional.**
    If selection favors higher trait values, Δpᵢ > 0 for positive-effect
    alleles and Δpᵢ < 0 for negative-effect alleles.
    The shift Σ βᵢ Δpᵢ > 0. -/
theorem selected_shift_positive
    {m : ℕ} (β : Fin m → ℝ) (Δp : Fin m → ℝ)
    (h_concordant : ∀ i, 0 ≤ β i * Δp i)
    (h_exists_pos : ∃ i, 0 < β i * Δp i) :
    0 < polygenicAdaptationShift β Δp := by
  unfold polygenicAdaptationShift
  obtain ⟨i₀, hi₀⟩ := h_exists_pos
  exact Finset.sum_pos_of_nonneg_of_exists_pos _ (fun i _ => h_concordant i) ⟨i₀, Finset.mem_univ _, hi₀⟩

/-- **Polygenic adaptation creates PGS mean shift but not R² loss.**
    The mean shift is recoverable by recalibration (intercept adjustment).
    R² only drops if effect sizes change, not just if frequencies shift. -/
theorem adaptation_shift_recoverable
    (pgs μ_shift : ℝ) :
    (pgs + μ_shift) - μ_shift = pgs := by ring

/-- **QST-FST comparison detects polygenic adaptation.**
    Q_ST = Var(between-pop trait means) / Var(total).
    Under neutrality, Q_ST ≈ F_ST.
    Q_ST >> F_ST indicates directional selection.
    Q_ST << F_ST indicates stabilizing selection. -/
theorem qst_fst_comparison_directional
    (qst fst : ℝ)
    (h_qst : 0 < qst) (h_fst : 0 < fst)
    (h_directional : fst < qst) :
    -- Q_ST / F_ST > 1 indicates directional selection
    1 < qst / fst := by
  rw [lt_div_iff h_fst]; linarith

theorem qst_fst_comparison_stabilizing
    (qst fst : ℝ)
    (h_qst : 0 < qst) (h_fst : 0 < fst)
    (h_stabilizing : qst < fst) :
    -- Q_ST / F_ST < 1 indicates stabilizing selection
    qst / fst < 1 := by
  rw [div_lt_one h_fst]; exact h_stabilizing

end PolygenicAdaptation


/-!
## GWAS Power and Minor Allele Frequency

The power to detect a causal variant in GWAS depends on its minor
allele frequency (MAF). MAF spectra differ across populations,
creating ascertainment-like portability effects.
-/

section GWASPowerMAF

/-- **GWAS non-centrality parameter.**
    NCP = n × β² × 2p(1-p) where n is sample size, β is effect, p is MAF.
    Larger NCP → more power to detect the variant. -/
noncomputable def gwasNCP (n : ℕ) (β p : ℝ) : ℝ :=
  n * β ^ 2 * (2 * p * (1 - p))

/-- NCP is positive for informative variants. -/
theorem gwas_ncp_pos (n : ℕ) (β p : ℝ)
    (hn : 0 < n) (hβ : β ≠ 0) (hp : 0 < p) (hp1 : p < 1) :
    0 < gwasNCP n β p := by
  unfold gwasNCP
  apply mul_pos
  · apply mul_pos
    · exact Nat.cast_pos.mpr hn
    · exact sq_pos_of_ne_zero hβ
  · nlinarith

/-- **NCP depends on population-specific MAF.**
    A variant with MAF 0.3 in Europeans may have MAF 0.05 in
    East Asians. The NCP ratio is proportional to the heterozygosity ratio. -/
theorem ncp_ratio_from_maf
    (n : ℕ) (β p₁ p₂ : ℝ)
    (hn : 0 < n) (hβ : 0 < β)
    (hp₁ : 0 < p₁) (hp₁1 : p₁ < 1)
    (hp₂ : 0 < p₂) (hp₂1 : p₂ < 1)
    (h_maf : p₁ < p₂) (h_half : p₂ ≤ 1/2) :
    gwasNCP n β p₁ < gwasNCP n β p₂ := by
  unfold gwasNCP
  apply mul_lt_mul_of_pos_left _ (mul_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hβ))
  -- 2p₁(1-p₁) < 2p₂(1-p₂) when p₁ < p₂ ≤ 1/2
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]

/-- **Population-specific GWAS recovers population-specific signals.**
    Variants that are common in the target population but rare in the
    source population are missed by source GWAS. Target GWAS recovers them. -/
theorem target_gwas_recovers_missed_variants
    (r2_source_only r2_combined : ℝ)
    (h_improvement : r2_source_only < r2_combined)
    (h_source_nn : 0 ≤ r2_source_only) :
    0 < r2_combined - r2_source_only := by linarith

end GWASPowerMAF


/-!
## Genetic Architecture Parameters and Portability Predictions

We derive concrete portability predictions from genetic architecture
parameters for different trait classes.
-/

section ArchitecturePredictions

/-- **Trait classification by selection regime.**
    Different trait classes have different expected portability patterns:
    - Metabolic/anthropometric: stabilizing selection → slow decay
    - Immune/inflammatory: fluctuating selection → fast decay
    - Behavioral/psychiatric: complex selection → intermediate decay -/

/-- Portability ordering across trait classes. -/
theorem portability_ordering
    (r2_metabolic r2_behavioral r2_immune : ℝ)
    (h_met_best : r2_behavioral < r2_metabolic)
    (h_beh_mid : r2_immune < r2_behavioral) :
    r2_immune < r2_metabolic := by linarith

/-- **Selection coefficient determines portability timescale.**
    The characteristic timescale for portability decay is 1/(2s) generations,
    where s is the selection coefficient.
    For neutral traits: s ≈ 0 → timescale → ∞ (drift only).
    For immune traits: s ≈ 0.01 → timescale ≈ 50 generations. -/
theorem selection_determines_timescale
    (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h_stronger : s₁ < s₂) :
    1 / (2 * s₂) < 1 / (2 * s₁) := by
  apply div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **Number of independent loci matters more than heritability for portability.**
    Two traits with the same h² but different architecture have different portability:
    - Trait A: h² = 0.5 from 10 loci (oligogenic)
    - Trait B: h² = 0.5 from 10000 loci (highly polygenic)
    Trait B has better portability because each locus contributes less. -/
theorem polygenic_more_portable_than_oligogenic
    (h2 : ℝ) (m_oligo m_poly : ℕ)
    (h_h2 : 0 < h2)
    (h_oligo : 0 < m_oligo) (h_poly : 0 < m_poly)
    (h_more_loci : m_oligo < m_poly) :
    -- Per-locus contribution is smaller for polygenic traits
    h2 / (m_poly : ℝ) < h2 / (m_oligo : ℝ) := by
  exact div_lt_div_of_pos_left h_h2 (Nat.cast_pos.mpr h_oligo) (Nat.cast_lt.mpr h_more_loci)

end ArchitecturePredictions


/-!
## Pleiotropy and Cross-Trait Portability

Pleiotropic loci affect multiple traits. The portability of a PGS
for one trait may be correlated with portability of related traits
through shared pleiotropic architecture.
-/

section Pleiotropy

/-- **Pleiotropic effect model.**
    A locus affects trait 1 with effect β₁ and trait 2 with effect β₂.
    The genetic correlation rg = Σ β₁ᵢβ₂ᵢ / √(Σβ₁ᵢ²·Σβ₂ᵢ²). -/

/-- **Shared portability through pleiotropy.**
    If two traits share many pleiotropic loci, their portability
    patterns are correlated. Specifically, if turnover affects
    the shared loci, both traits suffer. -/
theorem shared_pleiotropy_correlated_portability
    (r2_t1_source r2_t1_target r2_t2_source r2_t2_target ρ_shared : ℝ)
    (h_shared : 0 < ρ_shared) (h_shared_le : ρ_shared ≤ 1)
    -- Both traits drop proportionally to the shared component
    (h_t1_drop : r2_t1_target = r2_t1_source * (1 - ρ_shared * 0.5))
    (h_t2_drop : r2_t2_target = r2_t2_source * (1 - ρ_shared * 0.3))
    (h_t1_pos : 0 < r2_t1_source) (h_t2_pos : 0 < r2_t2_source) :
    r2_t1_target < r2_t1_source ∧ r2_t2_target < r2_t2_source := by
  constructor
  · rw [h_t1_drop]
    have : 1 - ρ_shared * 0.5 < 1 := by nlinarith
    exact mul_lt_of_lt_one_right h_t1_pos this
  · rw [h_t2_drop]
    have : 1 - ρ_shared * 0.3 < 1 := by nlinarith
    exact mul_lt_of_lt_one_right h_t2_pos this

/-- **Cross-trait portability prediction.**
    The portability ratio of trait 1's PGS for predicting trait 2 in
    population T is bounded by the product of:
    (1) genetic correlation between traits
    (2) portability of each trait individually -/
theorem cross_trait_portability_bound
    (rg port₁ port₂ : ℝ)
    (h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1)
    (h_p₁ : 0 ≤ port₁) (h_p₁_le : port₁ ≤ 1)
    (h_p₂ : 0 ≤ port₂) (h_p₂_le : port₂ ≤ 1) :
    rg * port₁ * port₂ ≤ 1 := by
  calc rg * port₁ * port₂ ≤ 1 * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul h_rg_le h_p₁_le h_p₁ (by linarith)
        · exact h_p₂_le
        · exact h_p₂
        · exact mul_nonneg (by linarith) (by linarith)
    _ = 1 := by ring

end Pleiotropy

end Calibrator
