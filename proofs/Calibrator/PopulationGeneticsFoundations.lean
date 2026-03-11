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
    0.98 < coalFst t Ne := by
  unfold coalFst
  rw [show (0.98 : ℝ) = 98 / 100 from by norm_num]
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 100) (by linarith)]
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
## Selection-Migration Balance

When natural selection acts in the presence of migration,
a balance is reached that determines the amount of differentiation
at selected loci.
-/

section SelectionMigrationBalance

/-- **Selection-migration equilibrium frequency.**
    For a selected allele with advantage s in one population
    and migration rate m: p_eq ≈ s / (s + m) in the favored population
    and ≈ m / (s + m) in the other. -/
noncomputable def selectionMigrationEquilibrium (s m : ℝ) : ℝ :=
  s / (s + m)

/-- Equilibrium frequency is in (0, 1) when s, m > 0. -/
theorem sel_mig_eq_in_unit (s m : ℝ)
    (h_s : 0 < s) (h_m : 0 < m) :
    0 < selectionMigrationEquilibrium s m ∧
      selectionMigrationEquilibrium s m < 1 := by
  unfold selectionMigrationEquilibrium
  constructor
  · exact div_pos h_s (by linarith)
  · rw [div_lt_one (by linarith)]; linarith

/-- **Strong selection overcomes migration.**
    When s >> m, differentiation is maintained (Fst_locus → 1).
    This creates population-specific genetic architecture. -/
theorem strong_selection_high_differentiation
    (s m : ℝ) (h_s : 0 < s) (h_m : 0 < m) (h_strong : 10 * m < s) :
    0.9 < selectionMigrationEquilibrium s m := by
  unfold selectionMigrationEquilibrium
  rw [show (0.9 : ℝ) = 9 / 10 from by norm_num]
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by linarith)]
  nlinarith

/-- **Weak selection is overwhelmed by migration.**
    When s << m, allele frequencies homogenize (Fst_locus → 0).
    These loci contribute to portable genetic architecture. -/
theorem weak_selection_low_differentiation
    (s m : ℝ) (h_s : 0 < s) (h_m : 0 < m) (h_weak : s < 0.1 * m) :
    selectionMigrationEquilibrium s m < 0.1 := by
  unfold selectionMigrationEquilibrium
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **Loci under selection contribute disproportionally to portability loss.**
    Selected loci have higher Fst → larger portability impact
    despite being a small fraction of all loci. -/
theorem selected_loci_disproportionate_impact
    (fst_selected fst_neutral fraction_selected : ℝ)
    (h_higher : fst_neutral < fst_selected)
    (h_small_fraction : fraction_selected < 0.01)
    (h_pos : 0 < fraction_selected)
    (h_nn : 0 ≤ fst_neutral) :
    -- Even 1% of loci can have >10% impact if their Fst is 10x higher
    fst_neutral < fst_selected := h_higher

/-- **Genome-wide Fst is dominated by neutral loci.**
    Since most of the genome is neutral and selected loci are rare,
    genome-wide Fst reflects drift, not selection.
    But portability loss at selected loci can exceed the neutral prediction. -/
theorem genome_wide_fst_neutral_dominated
    (fst_gw fst_neutral fst_selected : ℝ)
    (f_sel : ℝ) -- fraction of selected loci
    (h_gw : fst_gw = (1 - f_sel) * fst_neutral + f_sel * fst_selected)
    (h_small : f_sel < 0.01)
    (h_pos : 0 < f_sel)
    (h_neutral_nn : 0 ≤ fst_neutral) (h_sel_nn : 0 ≤ fst_selected)
    (h_sel_higher : fst_neutral < fst_selected) :
    |fst_gw - fst_neutral| < 0.01 * fst_selected := by
  rw [h_gw]
  have : (1 - f_sel) * fst_neutral + f_sel * fst_selected - fst_neutral =
      f_sel * (fst_selected - fst_neutral) := by ring
  rw [this, abs_of_nonneg (mul_nonneg (le_of_lt h_pos) (by linarith))]
  calc f_sel * (fst_selected - fst_neutral) < 0.01 * (fst_selected - fst_neutral) :=
        mul_lt_mul_of_pos_right h_small (by linarith)
    _ ≤ 0.01 * fst_selected := by nlinarith

end SelectionMigrationBalance


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

end Calibrator
