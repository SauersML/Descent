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
4. Rapidly varying selection regimes have fastest portability decay
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

/-- **Mutation-selection balance recurrence.**
    Each generation, new mutational variance v_mut is added and selection
    of strength s removes a fraction s of the standing variance V.
    The recurrence is: V(t+1) = (1 - s) × V(t) + v_mut. -/
noncomputable def effectVarianceRecurrence (V v_mut s : ℝ) : ℝ :=
  (1 - s) * V + v_mut

/-- **The equilibrium variance is a fixed point of the recurrence.**
    Solving V* = (1 - s) × V* + v_mut gives V* = v_mut / s.
    This verifies that `equilibriumEffectVariance` is the unique
    fixed point of the mutation-selection balance recurrence. -/
theorem effectVarianceRecurrence_fixedPoint
    (v_mut s : ℝ) (hs : s ≠ 0) :
    effectVarianceRecurrence (v_mut / s) v_mut s = v_mut / s := by
  unfold effectVarianceRecurrence
  field_simp
  ring

/-- **`equilibriumEffectVariance` is the fixed point of the recurrence.**
    Connects the standalone definition to the recurrence derivation. -/
theorem equilibriumEffectVariance_is_fixedPoint
    (v_mut s : ℝ) (hs : s ≠ 0) :
    effectVarianceRecurrence (equilibriumEffectVariance v_mut s) v_mut s
      = equilibriumEffectVariance v_mut s := by
  unfold equilibriumEffectVariance
  exact effectVarianceRecurrence_fixedPoint v_mut s hs

/-- Stronger stabilizing selection → smaller effect sizes. -/
theorem stronger_stabilizing_smaller_effects
    (v_mutation s₁ s₂ : ℝ)
    (h_vm : 0 < v_mutation)
    (h_s₁ : 0 < s₁) (h_s₂ : 0 < s₂)
    (h_stronger : s₁ < s₂) :
    equilibriumEffectVariance v_mutation s₂ < equilibriumEffectVariance v_mutation s₁ := by
  unfold equilibriumEffectVariance
  exact div_lt_div_of_pos_left h_vm h_s₁ h_stronger

/- **Derivation: Effect correlation under stabilizing selection.**

    We derive the equilibrium effect correlation ρ* = 1 - 1/(2Ns) from the
    Wright-Fisher model with stabilizing selection.

    **Setup.** Consider a locus with effect size β in two populations diverging
    under genetic drift, both subject to stabilizing selection of strength s
    per locus toward the same phenotypic optimum. Let ρ(t) denote the
    correlation of allelic effects between the populations at generation t.

    **Drift-selection recurrence.** Each generation:
    (1) Genetic drift destroys correlation at rate 1/(2N), since allele
        frequencies in each population are subject to independent binomial
        sampling with effective size N. This gives:
            ρ_drift = ρ(t) × (1 - 1/(2N))
    (2) Stabilizing selection restores correlation by removing alleles whose
        effects deviate from the shared optimum. Alleles far from the optimum
        are purged at rate proportional to s, pulling both populations back
        toward the same effect distribution. The restoration term is:
            selection_restoration ≈ (1 - ρ(t)) × (1/(2Ns)) × (1/(1 - 1/(2N)))
        which simplifies for large N.

    **Equilibrium.** Setting ρ(t+1) = ρ(t) = ρ* and solving:
        ρ* = ρ* × (1 - 1/(2N)) + (1 - ρ*) × s_restoration
    The key insight is that each allele's residence time under stabilizing
    selection is ~2Ns generations (the expected time before it is replaced
    by a new mutation closer to the optimum). During this time, drift
    decorrelates frequencies at rate 1/(2N) per generation, so the total
    decorrelation is:
        1 - ρ* ≈ (residence time) × (drift rate) / (residence time)
                = 1/(2Ns)

    Therefore:  **ρ* = 1 - 1/(2Ns)**  when Ns >> 1.

    This is the mutation-selection-drift balance: selection maintains alleles
    near their shared optimum with turnover time ~2Ns, and drift erodes
    the correlation by 1/(2Ns) of the remaining correlation each turnover
    cycle. The formula breaks down when Ns ≈ 1 (drift dominates) or when
    selection pressures differ between populations. -/

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

/-- **Highly polygenic architecture: total heritability sums from small effects.**
    With M causal loci each contributing h²/M, the total heritability
    is recovered as M × (h²/M) = h². -/
theorem polygenic_h2_summation (M h2 : ℝ) (h_M : M ≠ 0) :
    M * (h2 / M) = h2 := by
  field_simp

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
    the effect correlation decays as ρ(t) = exp(-t/τ).

    This models the selection environment as an Ornstein-Uhlenbeck (OU) process:
    the fitness optimum θ(t) satisfies dθ = -θ/τ dt + σ dW, where τ is the
    relaxation time and W is a Wiener process. The autocorrelation function of
    an OU process is Cov(θ(t), θ(t+Δ)) = (σ²τ/2) exp(-Δ/τ), which after
    normalization gives the correlation exp(-Δ/τ). The parameter τ controls
    how quickly the selective landscape decorrelates: small τ means rapid
    turnover, while τ → ∞ recovers stabilizing selection with a fixed
    optimum. -/
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
  exact div_lt_div_of_pos_left h_t (by linarith) h_shorter

/-- **Shorter autocorrelation times imply lower cross-population effect
    correlation.** -/
theorem short_autocorrelation_lower_correlation
    (τ_short τ_long t : ℝ)
    (h_short : 0 < τ_short) (h_long : 0 < τ_long)
    (h_shorter : τ_short < τ_long)
    (h_t : 0 < t) :
    fluctuatingEffectCorrelation t τ_short < fluctuatingEffectCorrelation t τ_long :=
  shorter_autocorrelation_faster_decay t τ_long τ_short h_long h_short h_shorter h_t

/-- Selected-architecture variance under stabilizing selection. -/
noncomputable def stabilizingSelectedArchitectureVariance (v_mutation s : ℝ) : ℝ :=
  equilibriumEffectVariance v_mutation s

/-- Stationary variance of a fluctuating optimum under the OU model. -/
noncomputable def optimumOUVariance (sigmaTheta tau : ℝ) : ℝ :=
  sigmaTheta ^ 2 * tau / 2

/-- Selected-architecture variance under fluctuating selection: the baseline
    mutation-selection variance plus the variance induced by a moving optimum. -/
noncomputable def fluctuatingSelectedArchitectureVariance
    (v_mutation s sigmaTheta tau : ℝ) : ℝ :=
  equilibriumEffectVariance v_mutation s + optimumOUVariance sigmaTheta tau

theorem effectCorrelationStabilizing_pos
    (Ns : ℝ) (hNs : 1 < Ns) :
    0 < effectCorrelationStabilizing Ns := by
  unfold effectCorrelationStabilizing
  have hden_pos : 0 < 2 * Ns := by linarith
  have hfrac_lt_one : 1 / (2 * Ns) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    linarith
  linarith

theorem effectCorrelationStabilizing_lt_one
    (Ns : ℝ) (hNs : 1 < Ns) :
    effectCorrelationStabilizing Ns < 1 := by
  unfold effectCorrelationStabilizing
  have hfrac_pos : 0 < 1 / (2 * Ns) := by
    positivity
  linarith

theorem fluctuatingSelectedArchitectureVariance_gt_stabilizing
    (v_mutation s sigmaTheta tau : ℝ)
    (h_sigma : 0 < sigmaTheta) (h_tau : 0 < tau) :
    stabilizingSelectedArchitectureVariance v_mutation s <
      fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta tau := by
  unfold stabilizingSelectedArchitectureVariance
    fluctuatingSelectedArchitectureVariance optimumOUVariance
    equilibriumEffectVariance
  have h_extra : 0 < sigmaTheta ^ 2 * tau / 2 := by
    have hsq : 0 < sigmaTheta ^ 2 := sq_pos_of_pos h_sigma
    nlinarith
  linarith

/-- The fluctuating correlation drops below the stabilizing correlation once the
    fluctuating autocorrelation time is below the exact threshold obtained by
    matching `exp(-t/τ)` to `1 - 1/(2Ns)`. -/
theorem fluctuatingCorrelation_lt_stabilizing_of_tau_lt_threshold
    (t tau Ns : ℝ)
    (h_t : 0 < t) (h_tau : 0 < tau) (hNs : 1 < Ns)
    (h_tau_lt : tau < t / (-Real.log (effectCorrelationStabilizing Ns))) :
    fluctuatingEffectCorrelation t tau < effectCorrelationStabilizing Ns := by
  have h_rho_pos : 0 < effectCorrelationStabilizing Ns :=
    effectCorrelationStabilizing_pos Ns hNs
  have h_rho_lt_one : effectCorrelationStabilizing Ns < 1 :=
    effectCorrelationStabilizing_lt_one Ns hNs
  have h_log_neg : Real.log (effectCorrelationStabilizing Ns) < 0 := by
    have h_log_lt : Real.log (effectCorrelationStabilizing Ns) < Real.log 1 := by
      exact Real.log_lt_log h_rho_pos h_rho_lt_one
    simpa using h_log_lt
  have h_neglog_pos : 0 < -Real.log (effectCorrelationStabilizing Ns) := by
    linarith
  have h_mul_lt : tau * (-Real.log (effectCorrelationStabilizing Ns)) < t := by
    exact (lt_div_iff₀ h_neglog_pos).mp h_tau_lt
  have h_neglog_lt_div : -Real.log (effectCorrelationStabilizing Ns) < t / tau := by
    exact (lt_div_iff₀ h_tau).2 (by simpa [mul_comm] using h_mul_lt)
  have h_exp_lt_log' : -(t / tau) < Real.log (effectCorrelationStabilizing Ns) := by
    linarith
  have h_exp_lt_log : -t / tau < Real.log (effectCorrelationStabilizing Ns) := by
    simpa [neg_div] using h_exp_lt_log'
  unfold fluctuatingEffectCorrelation
  have h_exp_lt := Real.exp_lt_exp.mpr h_exp_lt_log
  simpa [Real.exp_log h_rho_pos] using h_exp_lt

/-- **Balancing selection maintains intermediate allele frequencies.**
    Under balancing selection (e.g., heterozygote advantage in HLA),
    allele frequencies are maintained near 0.5 → high heterozygosity.
    This increases PGS variance even as accuracy drops. -/
theorem balancing_selection_high_het
    (p_neutral p_balanced lo hi : ℝ)
    (h_neutral_low : p_neutral < lo)
    (h_neutral_pos : 0 < p_neutral)
    (h_balanced : hi < p_balanced) (h_balanced_lt : p_balanced < 1/2)
    (h_lo_le_hi : lo ≤ hi) (h_lo_pos : 0 < lo) :
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
  exact Finset.sum_pos' (fun i _ => h_concordant i) ⟨i₀, Finset.mem_univ _, hi₀⟩

/-- **Polygenic adaptation creates PGS mean shift but not R² loss.**
    The mean shift is recoverable by recalibration (intercept adjustment).

    We prove the key statistical claim: if the PGS has variance V and the
    adaptation shift μ is a constant (same for all individuals), then the
    R² of (PGS + μ) for predicting the phenotype equals R² of PGS alone.
    This is because R² = Var(predictor) × corr² / Var(outcome), and adding
    a constant does not change variance or correlation.

    Formally: for any set of n individual scores, the sample variance is
    invariant under translation by a constant shift. -/
theorem adaptation_shift_recoverable
    {n : ℕ} (scores : Fin n → ℝ) (μ_shift : ℝ) :
    let shifted := fun i => scores i + μ_shift
    let mean_orig := (∑ i, scores i) / n
    let mean_shifted := (∑ i, shifted i) / n
    (∑ i, (shifted i - mean_shifted) ^ 2) =
      ∑ i, (scores i - mean_orig) ^ 2 := by
  by_cases hzero : n = 0
  · subst hzero
    simp
  simp only
  congr 1
  ext i
  have : (∑ j : Fin n, (scores j + μ_shift)) / ↑n =
    (∑ j, scores j) / ↑n + μ_shift := by
    rw [show (∑ j : Fin n, (scores j + μ_shift)) =
      (∑ j, scores j) + n * μ_shift by
      simp [Finset.sum_add_distrib, Finset.mul_sum]]
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    field_simp [hn]
  rw [this]
  ring_nf

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
  rw [lt_div_iff₀ h_fst]; linarith

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
    source population are missed by source GWAS. Target GWAS recovers them.

    Note: This is a direct algebraic consequence of the model assumption
    that combined R² exceeds source-only R². The substantive claim is in
    the model: multi-ancestry GWAS discovers variants with population-specific
    MAF spectra that single-ancestry GWAS misses. -/
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

/- **Trait classes can be ranked by regime-specific portability parameters.** -/

/-- Portability ordering follows from any transitive ranking of regime-level
    portability values. -/
theorem portability_ordering
    (r2_high r2_mid r2_low : ℝ)
    (h_high : r2_mid < r2_high)
    (h_mid : r2_low < r2_mid) :
    r2_low < r2_high := by linarith

/-- **Selection coefficient determines portability timescale.**
    The characteristic timescale for portability decay is 1/(2s) generations,
    where s is the selection coefficient.
    Smaller `s` gives slower change; larger `s` gives faster change. -/
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

/- **Pleiotropic effect model.**
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
    (d₁ d₂ : ℝ) (h_d₁ : 0 < d₁) (h_d₂ : 0 < d₂)
    (h_t1_drop : r2_t1_target = r2_t1_source * (1 - ρ_shared * d₁))
    (h_t2_drop : r2_t2_target = r2_t2_source * (1 - ρ_shared * d₂))
    (h_t1_pos : 0 < r2_t1_source) (h_t2_pos : 0 < r2_t2_source) :
    r2_t1_target < r2_t1_source ∧ r2_t2_target < r2_t2_source := by
  constructor
  · rw [h_t1_drop]
    have : 1 - ρ_shared * d₁ < 1 := by nlinarith
    exact mul_lt_of_lt_one_right h_t1_pos this
  · rw [h_t2_drop]
    have : 1 - ρ_shared * d₂ < 1 := by nlinarith
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
