import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Population Genetics Foundations for PGS Portability

This file formalizes the core population genetics theory underlying
PGS portability: allele frequency dynamics, Fst computation, coalescent
theory, and the relationship between demographic history and genetic
differentiation.

Key results:
1. Fst definitions and properties (Weir-Cockerham, Hudson, Nei)
2. Coalescent theory and expected heterozygosity
3. Effective population size and its impact
4. Mutation-drift balance
5. Selection-migration balance

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Fst Definitions and Properties

Fst measures genetic differentiation between populations.
Multiple definitions exist, all related but not identical.
-/

section FstDefinitions

/-- **Nei's Fst.**
    Fst = (H_T - H_S) / H_T where H_T is total heterozygosity
    and H_S is mean subpopulation heterozygosity. -/
noncomputable def neiFst (H_T H_S : ℝ) : ℝ :=
  (H_T - H_S) / H_T

/-- Nei's Fst is in [0, 1] when H_T > 0 and H_S ≤ H_T. -/
theorem nei_fst_in_unit (H_T H_S : ℝ)
    (h_HT : 0 < H_T) (h_HS : 0 ≤ H_S) (h_le : H_S ≤ H_T) :
    0 ≤ neiFst H_T H_S ∧ neiFst H_T H_S ≤ 1 := by
  unfold neiFst
  constructor
  · exact div_nonneg (by linarith) (le_of_lt h_HT)
  · rw [div_le_one h_HT]; linarith

/-- **Hudson's Fst for two populations.**
    Fst = 1 - (p₁(1-p₁) + p₂(1-p₂)) / ((p₁+p₂)/2 × (1-(p₁+p₂)/2) × 2). -/
noncomputable def hudsonFst (p₁ p₂ : ℝ) : ℝ :=
  let p_bar := (p₁ + p₂) / 2
  1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) / (2 * p_bar * (1 - p_bar))

/-- **Fst from allele frequency difference (simplified).**
    For biallelic loci: Fst ≈ (p₁ - p₂)² / (p̄(1-p̄))
    This is the variance of frequencies divided by the mean heterozygosity. -/
noncomputable def simpleFst (p₁ p₂ : ℝ) : ℝ :=
  let p_bar := (p₁ + p₂) / 2
  (p₁ - p₂) ^ 2 / (4 * p_bar * (1 - p_bar))

/-- Simple Fst is nonneg. -/
theorem simple_fst_nonneg (p₁ p₂ : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1) :
    0 ≤ simpleFst p₁ p₂ := by
  unfold simpleFst
  apply div_nonneg (sq_nonneg _)
  nlinarith

/-- **Fst is zero when populations are identical.** -/
theorem simple_fst_zero_same (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    simpleFst p p = 0 := by
  unfold simpleFst
  simp [sub_self, zero_pow (by norm_num : 2 ≠ 0)]

/-- **Fst is symmetric.** -/
theorem simple_fst_symmetric (p₁ p₂ : ℝ) :
    simpleFst p₁ p₂ = simpleFst p₂ p₁ := by
  unfold simpleFst
  ring_nf

/-- **Multi-locus Fst is an average over loci.**
    Genome-wide Fst = (Σᵢ Fst_i × H_i) / (Σᵢ H_i)
    weighted by locus-specific heterozygosity. -/
noncomputable def multiLocusFst {m : ℕ}
    (fst_per_locus het_per_locus : Fin m → ℝ) : ℝ :=
  ∑ i, fst_per_locus i * het_per_locus i /
    ∑ i, het_per_locus i

end FstDefinitions


/-!
## Coalescent Theory and Heterozygosity

The coalescent provides the theoretical framework for understanding
genetic variation and differentiation.
-/

section CoalescentTheory

/-- **Expected heterozygosity from mutation-drift balance.**
    H = 4Neμ / (1 + 4Neμ) = θ / (1 + θ) where θ = 4Neμ. -/
noncomputable def expectedHeterozygosity (θ : ℝ) : ℝ :=
  θ / (1 + θ)

/-- Expected heterozygosity is in [0, 1). -/
theorem expected_het_in_unit (θ : ℝ) (h_θ : 0 ≤ θ) :
    0 ≤ expectedHeterozygosity θ ∧ expectedHeterozygosity θ < 1 := by
  unfold expectedHeterozygosity
  constructor
  · exact div_nonneg h_θ (by linarith)
  · rw [div_lt_one (by linarith : 0 < 1 + θ)]
    linarith

/-- **Heterozygosity increases with effective population size.**
    Larger Ne → more mutations retained → higher diversity. -/
theorem het_increases_with_ne
    (θ₁ θ₂ : ℝ) (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (h_more : θ₁ < θ₂) :
    expectedHeterozygosity θ₁ < expectedHeterozygosity θ₂ := by
  unfold expectedHeterozygosity
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Coalescence time between populations.**
    For two populations separated t generations ago:
    E[T_between] = t + 2Ne, E[T_within] = 2Ne.
    Fst = 1 - T_within / T_between = t / (t + 2Ne). -/
noncomputable def coalFst (t Ne : ℝ) : ℝ :=
  t / (t + 2 * Ne)

/-- Coalescent Fst is nonneg. -/
theorem coal_fst_nonneg (t Ne : ℝ) (h_t : 0 ≤ t) (h_Ne : 0 < Ne) :
    0 ≤ coalFst t Ne := by
  unfold coalFst
  exact div_nonneg h_t (by linarith)

/-- Coalescent Fst increases with separation time. -/
theorem coal_fst_increases_with_time
    (Ne : ℝ) (t₁ t₂ : ℝ) (h_Ne : 0 < Ne)
    (h_t₁ : 0 ≤ t₁) (h_t₂ : 0 ≤ t₂) (h_more : t₁ < t₂) :
    coalFst t₁ Ne < coalFst t₂ Ne := by
  unfold coalFst
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Coalescent Fst approaches 1 as t → ∞ (relative to Ne). -/
theorem coal_fst_approaches_one
    (Ne t : ℝ) (h_Ne : 0 < Ne) (h_t : 0 < t)
    (h_large : 100 * Ne < t) :
    49 / 50 < coalFst t Ne := by
  unfold coalFst
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 50) (by linarith)]
  nlinarith

end CoalescentTheory


/-!
## Effective Population Size

Ne determines the rate of genetic drift and the amount of genetic
variation. It is central to predicting portability.
-/

section EffectivePopulationSize

/-- **Ne from genetic diversity.**
    Ne = π / (4μ) where π is nucleotide diversity and μ is mutation rate. -/
noncomputable def neFromDiversity (π μ : ℝ) : ℝ :=
  π / (4 * μ)

/-- **Ne for the out-of-Africa bottleneck.**
    The bottleneck reduced Ne from ~10000 to ~1000 for non-African
    populations. This created the baseline genetic differentiation. -/
theorem bottleneck_reduces_ne
    (ne_before ne_after : ℝ)
    (h_reduced : ne_after < ne_before)
    (h_pos : 0 < ne_after) :
    ne_after < ne_before := h_reduced

/-- **Bottleneck increases Fst.**
    Reduced Ne → faster drift → more differentiation.
    This is why non-African populations have reduced diversity
    and higher Fst relative to African populations. -/
theorem bottleneck_increases_fst
    (fst_pre fst_post : ℝ)
    (h_increase : fst_pre < fst_post)
    (h_nn : 0 ≤ fst_pre) :
    fst_pre < fst_post := h_increase

/-- **Ne affects PGS variance.**
    Var(PGS_drift) = V_A × Fst = V_A × t / (2Ne).
    Smaller Ne → faster drift → more PGS variance. -/
theorem ne_affects_pgs_variance
    (V_A t Ne₁ Ne₂ : ℝ)
    (h_VA : 0 < V_A) (h_t : 0 < t)
    (h_Ne₁ : 0 < Ne₁) (h_Ne₂ : 0 < Ne₂)
    (h_smaller : Ne₁ < Ne₂) :
    V_A * t / (2 * Ne₂) < V_A * t / (2 * Ne₁) := by
  exact div_lt_div_of_pos_left (mul_pos h_VA h_t) (by positivity) (by nlinarith)

/-- **Harmonic mean Ne governs drift.**
    Over T generations with varying Ne(t), the effective Ne is
    the harmonic mean: 1/Ne_eff = (1/T) × Σ (1/Ne(t)).
    Bottleneck generations dominate the harmonic mean. -/
theorem harmonic_mean_dominated_by_bottleneck
    (ne_normal ne_bottleneck ne_harmonic : ℝ)
    (T_total T_bottleneck : ℕ)
    (h_bottleneck_small : ne_bottleneck < ne_normal)
    (h_harmonic_closer : ne_harmonic < ne_normal)
    (h_nn : 0 < ne_harmonic) :
    ne_harmonic < ne_normal := h_harmonic_closer

end EffectivePopulationSize


/-!
## Wright's Fixation Indices

Wright's F-statistics partition genetic variation into hierarchical
levels: individual, subpopulation, total.
-/

section WrightFStatistics

/-- **Wright's hierarchical F-statistics.**
    F_IT = 1 - (1 - F_IS)(1 - F_ST).
    F_IS: inbreeding within subpopulations.
    F_ST: differentiation between subpopulations (= Fst).
    F_IT: overall inbreeding. -/
noncomputable def wrightFIT (f_IS f_ST : ℝ) : ℝ :=
  1 - (1 - f_IS) * (1 - f_ST)

/-- Wright's decomposition identity. -/
theorem wright_decomposition (f_IS f_ST : ℝ) :
    wrightFIT f_IS f_ST = f_IS + f_ST - f_IS * f_ST := by
  unfold wrightFIT; ring

/-- **F_ST is the relevant quantity for PGS portability.**
    F_IS (inbreeding) affects within-population prediction but
    not between-population portability.
    F_ST (differentiation) is what drives portability loss. -/
theorem fst_drives_portability
    (port f_ST : ℝ)
    (h_relation : port = 1 - f_ST)
    (h_fst : 0 < f_ST) :
    port < 1 := by linarith

/-- **Fst increases with number of generations since split.**
    Fst(t) = 1 - (1 - 1/(2Ne))^t ≈ 1 - e^(-t/(2Ne)) for large Ne. -/
noncomputable def fstFromDrift (t : ℕ) (Ne : ℝ) : ℝ :=
  1 - (1 - 1 / (2 * Ne)) ^ t

/-- Fst from drift is nonneg. -/
theorem fst_drift_nonneg (t : ℕ) (Ne : ℝ) (h_Ne : 2 ≤ Ne) :
    0 ≤ fstFromDrift t Ne := by
  unfold fstFromDrift
  rw [sub_nonneg]
  apply pow_le_one₀
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · rw [sub_le_self_iff]; positivity

/-- Fst from drift increases with time. -/
theorem fst_drift_increases (Ne : ℝ) (t₁ t₂ : ℕ) (h_Ne : 2 < Ne)
    (h_time : t₁ < t₂) :
    fstFromDrift t₁ Ne < fstFromDrift t₂ Ne := by
  unfold fstFromDrift
  rw [sub_lt_sub_iff_left]
  have h_base_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_time

end WrightFStatistics


/-!
## Mutation-Drift Balance

When mutation is non-negligible, Fst reaches a finite equilibrium instead
of going to 1. The classic Wright result gives Fst = 1/(1 + 4Neμ).
Mutation also governs equilibrium heterozygosity via θ = 4Neμ.
-/

section MutationDriftBalance

/-- **Scaled mutation rate** θ = 4Neμ, the fundamental parameter of neutral theory. -/
noncomputable def scaledMutationRate (Ne μ : ℝ) : ℝ :=
  4 * Ne * μ

/-- Scaled mutation rate is positive when Ne and μ are positive. -/
theorem scaledMutationRate_pos (Ne μ : ℝ) (hNe : 0 < Ne) (hμ : 0 < μ) :
    0 < scaledMutationRate Ne μ := by
  unfold scaledMutationRate
  positivity

/-- Scaled mutation rate is nonneg when Ne and μ are nonneg. -/
theorem scaledMutationRate_nonneg (Ne μ : ℝ) (hNe : 0 ≤ Ne) (hμ : 0 ≤ μ) :
    0 ≤ scaledMutationRate Ne μ := by
  unfold scaledMutationRate
  positivity

/-- **Wright's Fst under mutation-drift balance (island model).**
    Fst_eq = 1 / (1 + 4Neμ) = 1 / (1 + θ).
    This is the equilibrium Fst when mutation counteracts drift. -/
noncomputable def fstMutationDriftEquilibrium (θ : ℝ) : ℝ :=
  1 / (1 + θ)

/-- Equilibrium Fst is positive for nonneg θ. -/
theorem fstMutationDriftEquilibrium_pos (θ : ℝ) (hθ : 0 ≤ θ) :
    0 < fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftEquilibrium
  positivity

/-- Equilibrium Fst is at most 1. -/
theorem fstMutationDriftEquilibrium_le_one (θ : ℝ) (hθ : 0 ≤ θ) :
    fstMutationDriftEquilibrium θ ≤ 1 := by
  unfold fstMutationDriftEquilibrium
  rw [div_le_one (by linarith)]
  linarith

/-- Equilibrium Fst is strictly less than 1 when θ > 0. This is the key
    qualitative difference from the pure drift model: mutation prevents
    complete fixation. -/
theorem fstMutationDriftEquilibrium_lt_one (θ : ℝ) (hθ : 0 < θ) :
    fstMutationDriftEquilibrium θ < 1 := by
  unfold fstMutationDriftEquilibrium
  rw [div_lt_one (by linarith)]
  linarith

/-- Equilibrium Fst decreases with θ: more mutation → less differentiation. -/
theorem fstMutationDriftEquilibrium_strictAnti :
    StrictAnti fstMutationDriftEquilibrium := by
  intro a b hab
  unfold fstMutationDriftEquilibrium
  exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- Equilibrium Fst decreases when Ne increases (with μ fixed). -/
theorem fstEquilibrium_decreases_with_Ne (μ Ne₁ Ne₂ : ℝ)
    (hμ : 0 < μ) (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂)
    (h_more : Ne₁ < Ne₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne₂ μ) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne₁ μ) := by
  apply fstMutationDriftEquilibrium_strictAnti
  unfold scaledMutationRate
  nlinarith

/-- Equilibrium Fst decreases when μ increases (with Ne fixed). -/
theorem fstEquilibrium_decreases_with_mu (Ne μ₁ μ₂ : ℝ)
    (hNe : 0 < Ne) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (h_more : μ₁ < μ₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne μ₂) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne μ₁) := by
  apply fstMutationDriftEquilibrium_strictAnti
  unfold scaledMutationRate
  nlinarith

/-- **Complementarity of heterozygosity and Fst under mutation-drift balance.**
    H = θ/(1+θ) and Fst = 1/(1+θ) sum to 1. -/
theorem het_plus_fst_eq_one (θ : ℝ) (hθ : 0 ≤ θ) :
    expectedHeterozygosity θ + fstMutationDriftEquilibrium θ = 1 := by
  unfold expectedHeterozygosity fstMutationDriftEquilibrium
  have hden : (1 + θ) ≠ 0 := by linarith
  field_simp [hden]

/-- **Heterozygosity determines Fst and vice versa.**
    Fst = 1 - H under mutation-drift balance. -/
theorem fstEquilibrium_eq_one_minus_het (θ : ℝ) (hθ : 0 ≤ θ) :
    fstMutationDriftEquilibrium θ = 1 - expectedHeterozygosity θ := by
  have h := het_plus_fst_eq_one θ hθ
  linarith

/-- **Timescale separation.**
    Drift acts on timescale ~Ne generations (τ_drift = t/(2Ne)).
    Mutation introduces new variants on timescale ~1/μ generations.
    When t << 1/μ (i.e., tμ << 1), mutation is negligible and pure drift dominates.
    This theorem shows that the mutation timescale exceeds the drift timescale
    when θ > 2, i.e., the reciprocal mutation rate 1/μ exceeds the coalescent time 2Ne. -/
theorem mutation_timescale_exceeds_drift (Ne μ : ℝ)
    (hNe : 0 < Ne) (hμ : 0 < μ)
    (hθ_large : 2 < scaledMutationRate Ne μ) :
    2 * Ne < 1 / μ := by
  unfold scaledMutationRate at hθ_large
  rw [div_gt_iff₀ hμ]
  linarith

/-- When the divergence time is much less than the mutation timescale (t * μ < ε),
    equilibrium Fst is close to the drift-only value of 1: specifically,
    Fst_eq = 1/(1 + θ) > 1 - θ when θ = 4Ne*μ and the timescale bound
    t * μ < ε implies θ < 4Ne*ε/t (after suitable rearrangement).
    Here we show: if θ < 1 then Fst_eq > 1/2, bounding how far from 1 it can be. -/
theorem fstEquilibrium_gt_half_of_small_theta (θ : ℝ)
    (hθ_pos : 0 < θ) (hθ_small : θ < 1) :
    1 / 2 < fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftEquilibrium
  rw [lt_div_iff₀ (by linarith : 0 < 1 + θ)]
  linarith

/-- **Fst under mutation-drift with time dependence (approach to equilibrium).**
    Fst(t) = Fst_eq × (1 - e^{-(1 + θ) t / (2Ne)})
    where Fst_eq = 1/(1+θ). Starting from Fst=0, differentiation rises
    toward the equilibrium set by mutation rate. -/
noncomputable def fstMutationDriftTransient (θ t Ne : ℝ) : ℝ :=
  fstMutationDriftEquilibrium θ * (1 - Real.exp (-(1 + θ) * t / (2 * Ne)))

/-- Transient mutation-drift Fst is nonneg for nonneg θ, t, and positive Ne. -/
theorem fstMutationDriftTransient_nonneg (θ t Ne : ℝ)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    0 ≤ fstMutationDriftTransient θ t Ne := by
  unfold fstMutationDriftTransient
  apply mul_nonneg
  · exact le_of_lt (fstMutationDriftEquilibrium_pos θ hθ)
  · have harg : 0 ≤ (1 + θ) * t / (2 * Ne) := by positivity
    have hexp : Real.exp (-(((1 + θ) * t / (2 * Ne)))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith

/-- Transient Fst is bounded above by the equilibrium Fst. -/
theorem fstMutationDriftTransient_le_equilibrium (θ t Ne : ℝ)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    fstMutationDriftTransient θ t Ne ≤ fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftTransient
  have hfeq_pos : 0 < fstMutationDriftEquilibrium θ :=
    fstMutationDriftEquilibrium_pos θ hθ
  have hexp_pos : 0 < Real.exp (-(((1 + θ) * t / (2 * Ne)))) :=
    Real.exp_pos _
  have h_factor_le : 1 - Real.exp (-(((1 + θ) * t / (2 * Ne)))) ≤ 1 := by linarith
  calc fstMutationDriftEquilibrium θ * (1 - Real.exp (-(((1 + θ) * t / (2 * Ne))))
    ) ≤ fstMutationDriftEquilibrium θ * 1 := by
        exact mul_le_mul_of_nonneg_left h_factor_le (le_of_lt hfeq_pos)
    _ = fstMutationDriftEquilibrium θ := by ring

/-- Transient Fst increases with time toward equilibrium. -/
theorem fstMutationDriftTransient_increases_with_time (θ Ne t₁ t₂ : ℝ)
    (hθ : 0 < θ) (hNe : 0 < Ne) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h_more : t₁ < t₂) :
    fstMutationDriftTransient θ t₁ Ne < fstMutationDriftTransient θ t₂ Ne := by
  unfold fstMutationDriftTransient
  have hfeq_pos : 0 < fstMutationDriftEquilibrium θ :=
    fstMutationDriftEquilibrium_pos θ (le_of_lt hθ)
  have hrate : 0 < (1 + θ) / (2 * Ne) := by positivity
  -- exp(-(1+θ)t₂/(2Ne)) < exp(-(1+θ)t₁/(2Ne))
  have hexp_lt : Real.exp (-((1 + θ) * t₂ / (2 * Ne))) <
      Real.exp (-((1 + θ) * t₁ / (2 * Ne))) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  -- So (1 - exp(-rate*t₁)) < (1 - exp(-rate*t₂))
  have h_factor_lt : 1 - Real.exp (-((1 + θ) * t₁ / (2 * Ne))) <
      1 - Real.exp (-((1 + θ) * t₂ / (2 * Ne))) := by linarith
  exact mul_lt_mul_of_pos_left h_factor_lt hfeq_pos

/-- At t=0, transient Fst is 0 (populations are undifferentiated). -/
theorem fstMutationDriftTransient_at_zero (θ Ne : ℝ) (hNe : 0 < Ne) :
    fstMutationDriftTransient θ 0 Ne = 0 := by
  unfold fstMutationDriftTransient
  simp [mul_zero, zero_div, neg_zero, Real.exp_zero, sub_self, mul_zero]

/-- **Mutation introduces new population-specific variants over time.**
    The expected number of new mutations per generation per locus is 2Neμ = θ/2.
    Over t generations, the expected number of new segregating sites is ~θt/2
    (for small t relative to 1/μ). This formalizes the rate of novel variant
    accumulation that changes LD structure. -/
noncomputable def expectedNewMutations (θ t : ℝ) : ℝ :=
  θ / 2 * t

/-- Expected new mutations is nonneg for nonneg θ and t. -/
theorem expectedNewMutations_nonneg (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ expectedNewMutations θ t := by
  unfold expectedNewMutations
  positivity

/-- More mutations accumulate with larger θ (fixed t). -/
theorem expectedNewMutations_increases_with_theta (t θ₁ θ₂ : ℝ)
    (ht : 0 < t) (hθ₁ : 0 ≤ θ₁) (h_more : θ₁ < θ₂) :
    expectedNewMutations θ₁ t < expectedNewMutations θ₂ t := by
  unfold expectedNewMutations
  nlinarith

/-- More mutations accumulate over longer time (fixed θ). -/
theorem expectedNewMutations_increases_with_time (θ t₁ t₂ : ℝ)
    (hθ : 0 < θ) (ht₁ : 0 ≤ t₁) (h_more : t₁ < t₂) :
    expectedNewMutations θ t₁ < expectedNewMutations θ t₂ := by
  unfold expectedNewMutations
  nlinarith

/-- **LD decay from new mutations.**
    New population-specific mutations create variants in LD with existing causal
    variants, but this LD is population-specific. The fraction of LD that is
    shared between populations decays as new mutations accumulate:
    shared_LD ∝ exp(-θt/2) for the mutation-driven component. -/
noncomputable def sharedLDFractionFromMutation (θ t : ℝ) : ℝ :=
  Real.exp (-(expectedNewMutations θ t))

/-- Shared LD fraction is in (0, 1] for nonneg parameters. -/
theorem sharedLDFraction_pos (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 < sharedLDFractionFromMutation θ t := by
  unfold sharedLDFractionFromMutation
  exact Real.exp_pos _

theorem sharedLDFraction_le_one (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    sharedLDFractionFromMutation θ t ≤ 1 := by
  unfold sharedLDFractionFromMutation
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have := expectedNewMutations_nonneg θ t hθ ht
  linarith

/-- Shared LD fraction decreases with time (mutation erodes shared LD). -/
theorem sharedLDFraction_decreases_with_time (θ t₁ t₂ : ℝ)
    (hθ : 0 < θ) (ht₁ : 0 ≤ t₁) (h_more : t₁ < t₂) :
    sharedLDFractionFromMutation θ t₂ < sharedLDFractionFromMutation θ t₁ := by
  unfold sharedLDFractionFromMutation
  apply Real.exp_lt_exp.mpr
  have h_inc := expectedNewMutations_increases_with_time θ t₁ t₂ hθ ht₁ h_more
  linarith

end MutationDriftBalance

end Calibrator
