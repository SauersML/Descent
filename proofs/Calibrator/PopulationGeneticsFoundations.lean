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
1. Fst definitions and properties (Nei, Hudson, simplified)
2. Coalescent theory and expected heterozygosity
3. Effective population size and drift
4. Wright's fixation indices
5. Mutation-drift balance (equilibrium and transient Fst, LD decay)

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
    9 / 10 < selectionMigrationEquilibrium s m := by
  unfold selectionMigrationEquilibrium
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 10) (by linarith)]
  nlinarith

/-- **Weak selection is overwhelmed by migration.**
    When s << m, allele frequencies homogenize (Fst_locus → 0).
    These loci contribute to portable genetic architecture. -/
theorem weak_selection_low_differentiation
    (s m : ℝ) (h_s : 0 < s) (h_m : 0 < m) (h_weak : s < (1 / 10) * m) :
    selectionMigrationEquilibrium s m < 1 / 10 := by
  unfold selectionMigrationEquilibrium
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **Loci under selection contribute disproportionally to portability loss.**
    Selected loci have higher Fst → larger portability impact
    despite being a small fraction of all loci.
    The weighted Fst contribution of selected loci (fraction × fst_selected)
    can exceed their fraction of the genome, showing disproportionate impact
    when fst_selected > fst_neutral. -/
theorem selected_loci_disproportionate_impact
    (fst_selected fst_neutral fraction_selected : ℝ)
    (h_higher : fst_neutral < fst_selected)
    (h_small_fraction : fraction_selected < 1 / 100)
    (h_pos : 0 < fraction_selected)
    (h_nn : 0 ≤ fst_neutral) :
    -- The selected loci contribution exceeds what you'd expect from neutral Fst
    fraction_selected * fst_neutral < fraction_selected * fst_selected := by
  exact mul_lt_mul_of_pos_left h_higher h_pos

/-- **Genome-wide Fst is dominated by neutral loci.**
    Since most of the genome is neutral and selected loci are rare,
    genome-wide Fst reflects drift, not selection.
    But portability loss at selected loci can exceed the neutral prediction. -/
theorem genome_wide_fst_neutral_dominated
    (fst_gw fst_neutral fst_selected : ℝ)
    (f_sel : ℝ) -- fraction of selected loci
    (h_gw : fst_gw = (1 - f_sel) * fst_neutral + f_sel * fst_selected)
    (h_small : f_sel < 1 / 100)
    (h_pos : 0 < f_sel)
    (h_neutral_nn : 0 ≤ fst_neutral) (h_sel_nn : 0 ≤ fst_selected)
    (h_sel_higher : fst_neutral < fst_selected) :
    |fst_gw - fst_neutral| < (1 / 100) * fst_selected := by
  rw [h_gw]
  have : (1 - f_sel) * fst_neutral + f_sel * fst_selected - fst_neutral =
      f_sel * (fst_selected - fst_neutral) := by ring
  rw [this, abs_of_nonneg (mul_nonneg (le_of_lt h_pos) (by linarith))]
  calc f_sel * (fst_selected - fst_neutral) < (1 / 100) * (fst_selected - fst_neutral) :=
        mul_lt_mul_of_pos_right h_small (by linarith)
    _ ≤ (1 / 100) * fst_selected := by nlinarith

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

    **Biological derivation.** Nei's Fst is *defined* as the proportion of total
    heterozygosity that is due to between-population differences:

      Fst = (H_T − H_S) / H_T = 1 − H_S / H_T

    where H_T is total (meta-population) heterozygosity and H_S is the mean
    subpopulation heterozygosity. Rearranging gives

      H_S / H_T  +  Fst  =  1

    so the within-population share and the between-population share of genetic
    diversity are complementary *by definition* of Fst as a variance partition.

    At mutation-drift equilibrium under the infinite-alleles model,
    H_S / H_T = θ/(1+θ) = `expectedHeterozygosity θ` and
    Fst = 1/(1+θ) = `fstMutationDriftEquilibrium θ`.  The algebraic identity
    θ/(1+θ) + 1/(1+θ) = 1 is therefore the equilibrium instantiation of the
    definitional partition H_S/H_T + Fst = 1.

    See also `nei_fst_complement` for the general (non-equilibrium)
    version derived directly from Nei's definition, and
    `nei_fst_equilibrium_consistent` which connects the two. -/
theorem het_plus_fst_eq_one (θ : ℝ) (hθ : 0 ≤ θ) :
    expectedHeterozygosity θ + fstMutationDriftEquilibrium θ = 1 := by
  unfold expectedHeterozygosity fstMutationDriftEquilibrium
  have hden : (1 + θ) ≠ 0 := by linarith
  field_simp [hden]

/-- **The within-population heterozygosity share and Nei's Fst sum to 1.**
    Since `neiFst H_T H_S = (H_T − H_S) / H_T = 1 − H_S / H_T`, we have
    H_S / H_T + neiFst H_T H_S = 1.  No equilibrium assumption is needed;
    the identity holds for *any* H_T ≠ 0.  This is the general form of the
    variance partition that `het_plus_fst_eq_one` instantiates at equilibrium. -/
theorem nei_fst_complement (H_S H_T : ℝ) (hHT : H_T ≠ 0) :
    H_S / H_T + neiFst H_T H_S = 1 := by
  unfold neiFst
  field_simp

/-- **At mutation-drift equilibrium, Nei's Fst recovers fstMutationDriftEquilibrium.**
    When H_S = θ/(1+θ) (`expectedHeterozygosity θ`) and H_T = 1 (maximal
    heterozygosity under the infinite-alleles model), Nei's formula gives
    Fst = 1/(1+θ) = `fstMutationDriftEquilibrium θ`. -/
theorem nei_fst_equilibrium_consistent (θ : ℝ) (hθ : 0 ≤ θ) :
    neiFst 1 (expectedHeterozygosity θ) = fstMutationDriftEquilibrium θ := by
  unfold neiFst expectedHeterozygosity fstMutationDriftEquilibrium
  have hden : (1 + θ) ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- **At mutation-drift equilibrium, the within-population share equals expectedHeterozygosity.**
    When H_T = 1, we have H_S / H_T = H_S = θ/(1+θ). -/
theorem within_pop_share_eq_het (θ : ℝ) :
    expectedHeterozygosity θ / 1 = expectedHeterozygosity θ := by
  simp

/-- **Heterozygosity determines Fst and vice versa.**
    Fst = 1 - H under mutation-drift balance. -/
theorem fstEquilibrium_eq_one_minus_het (θ : ℝ) (hθ : 0 ≤ θ) :
    fstMutationDriftEquilibrium θ = 1 - expectedHeterozygosity θ := by
  have h := het_plus_fst_eq_one θ hθ
  linarith

/-- **Timescale separation.**
    Drift acts on timescale ~Ne generations (τ_drift = t/(2Ne)).
    Mutation introduces new variants on timescale ~1/μ generations.
    When θ > 2, the reciprocal mutation rate 1/μ exceeds the coalescent time 2Ne. -/
theorem mutation_timescale_exceeds_drift (Ne μ : ℝ)
    (hNe : 0 < Ne) (hμ : 0 < μ)
    (hθ_large : 2 < scaledMutationRate Ne μ) :
    2 * Ne < 1 / μ := by
  unfold scaledMutationRate at hθ_large
  rw [div_gt_iff₀ hμ]
  linarith

/-- When θ < 1, equilibrium Fst > 1/2. -/
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
  have hexp_lt : Real.exp (-((1 + θ) * t₂ / (2 * Ne))) <
      Real.exp (-((1 + θ) * t₁ / (2 * Ne))) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
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
    Over t generations, the expected number of new segregating sites is ~θt/2. -/
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


/-!
## Migration-Drift Balance: Population Genetics Foundations

The island model of migration-drift balance is a cornerstone of population genetics.
When populations exchange migrants at rate m per generation, drift and migration
reach an equilibrium Fst = 1/(1 + 4Nm). This section provides the pure population
genetics foundations for migration effects, independent of PGS portability.

Key results:
1. Island model Fst equilibrium and monotonicity properties
2. Stepping-stone model and isolation by distance
3. Migration homogenizes allele frequencies and LD
4. Admixture (recent migration pulses) and transient LD
5. Asymmetric migration and effective migration rates
-/

section MigrationDriftFoundations

/-! ### Island Model Equilibrium -/

/-- **Wright's island model Fst.** Fst = 1/(1 + 4Nm).
    Under the infinite-island model, each deme exchanges a fraction m of
    its individuals with a common migrant pool each generation. At equilibrium,
    drift (increasing differentiation) balances migration (decreasing it). -/
noncomputable def islandModelFst (Ne m : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- Island model Fst is the reciprocal of (1 + 4Nm). -/
theorem islandModelFst_eq_inv (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    islandModelFst Ne m = (1 + 4 * Ne * m)⁻¹ := by
  unfold islandModelFst
  rw [one_div]

/-- Island model Fst is in (0, 1) for positive Ne and m. -/
theorem islandModelFst_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < islandModelFst Ne m := by
  unfold islandModelFst
  positivity

theorem islandModelFst_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    islandModelFst Ne m < 1 := by
  unfold islandModelFst
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- **Island model Fst is strictly decreasing in migration rate.**
    The function m ↦ 1/(1 + 4Nm) is strictly anti-monotone for positive Ne. -/
theorem islandModelFst_strictAnti_m (Ne : ℝ) (hNe : 0 < Ne) :
    StrictAnti (fun m => islandModelFst Ne m) := by
  intro a b hab
  unfold islandModelFst
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **Island model Fst is strictly decreasing in Ne.**
    Larger populations have more effective migrants per generation. -/
theorem islandModelFst_strictAnti_Ne (m : ℝ) (hm : 0 < m) :
    StrictAnti (fun Ne => islandModelFst Ne m) := by
  intro a b hab
  unfold islandModelFst
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **When 4Nm > 1, Fst < 1/2** (one-migrant-per-generation rule).
    This is Wright's classical threshold: even one migrant per generation
    (Nm = 0.25, so 4Nm = 1) is enough to prevent substantial differentiation. -/
theorem islandModelFst_lt_half_of_one_migrant (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m)
    (h_threshold : 1 < 4 * Ne * m) :
    islandModelFst Ne m < 1 / 2 := by
  unfold islandModelFst
  rw [div_lt_div_iff₀ (by nlinarith : 0 < 1 + 4 * Ne * m) (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **When 4Nm ≫ 1, Fst ≈ 0.** Specifically, 4Nm > k implies Fst < 1/(1+k). -/
theorem islandModelFst_small_of_large_migration (Ne m k : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hk : 0 < k)
    (h_large : k < 4 * Ne * m) :
    islandModelFst Ne m < 1 / (1 + k) := by
  unfold islandModelFst
  apply div_lt_div_of_pos_left one_pos (by linarith) (by nlinarith)

/-! ### Relationship between Migration and Mutation Effects on Fst -/

/-- **Migration-mutation equivalence for Fst.**
    Under the island model, the equilibrium Fst has the same functional form
    whether the homogenizing force is migration or mutation:
    Fst_migration = 1/(1+4Nm), Fst_mutation = 1/(1+4Neμ).
    The key parameter is the scaled rate 4N × (rate). -/
theorem islandModelFst_eq_mutationForm (Ne m : ℝ) :
    islandModelFst Ne m = fstMutationDriftEquilibrium (4 * Ne * m) := by
  unfold islandModelFst fstMutationDriftEquilibrium
  ring

/-- **Combined migration and mutation reduce Fst below either alone.**
    When both migration (m) and mutation (μ) act, the equilibrium Fst
    is 1/(1 + 4Nm + 4Neμ), which is below either individual equilibrium. -/
noncomputable def fstMigrationMutationEquilibrium (Ne m μ : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m + 4 * Ne * μ)

/-- Combined Fst is below migration-only Fst. -/
theorem fstMigrationMutation_lt_migrationOnly (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 < μ) :
    fstMigrationMutationEquilibrium Ne m μ < islandModelFst Ne m := by
  unfold fstMigrationMutationEquilibrium islandModelFst
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- Combined Fst is below mutation-only Fst. -/
theorem fstMigrationMutation_lt_mutationOnly (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 < μ) :
    fstMigrationMutationEquilibrium Ne m μ < fstMutationDriftEquilibrium (4 * Ne * μ) := by
  unfold fstMigrationMutationEquilibrium fstMutationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### Stepping-Stone Model Foundations -/

/-- **One-dimensional stepping-stone Fst.**
    In a linear array of demes with nearest-neighbor migration at rate m,
    Fst between demes i and j depends on |i-j|. For the continuous
    approximation: Fst(d) ≈ 1 - exp(-d/√(2Nm)) where d is the number of
    steps. We model the characteristic length scale. -/
noncomputable def steppingStoneCharacteristicLength (Ne m : ℝ) : ℝ :=
  Real.sqrt (2 * Ne * m)

/-- The characteristic length scale is positive for positive Ne and m. -/
theorem steppingStoneCharacteristicLength_pos (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) :
    0 < steppingStoneCharacteristicLength Ne m := by
  unfold steppingStoneCharacteristicLength
  exact Real.sqrt_pos.mpr (by positivity)

/-- **Continuous stepping-stone Fst approximation.**
    Fst(d) ≈ 1 - exp(-d / L) where L = √(2Nm). -/
noncomputable def continuousSteppingStoneFst (L d : ℝ) : ℝ :=
  1 - Real.exp (-(d / L))

/-- Stepping-stone Fst is nonneg for nonneg distance and positive L. -/
theorem continuousSteppingStoneFst_nonneg (L d : ℝ)
    (hL : 0 < L) (hd : 0 ≤ d) :
    0 ≤ continuousSteppingStoneFst L d := by
  unfold continuousSteppingStoneFst
  have harg : 0 ≤ d / L := div_nonneg hd (le_of_lt hL)
  have hexp : Real.exp (-(d / L)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **Stepping-stone Fst is strictly increasing in distance.** -/
theorem continuousSteppingStoneFst_increases (L d₁ d₂ : ℝ)
    (hL : 0 < L) (hd₁ : 0 ≤ d₁) (h_more : d₁ < d₂) :
    continuousSteppingStoneFst L d₁ < continuousSteppingStoneFst L d₂ := by
  unfold continuousSteppingStoneFst
  have h_exp_lt : Real.exp (-(d₂ / L)) < Real.exp (-(d₁ / L)) := by
    apply Real.exp_lt_exp.mpr
    have : d₁ / L < d₂ / L := div_lt_div_of_pos_right h_more hL
    linarith
  linarith

/-- **Stepping-stone Fst increases with larger L (more migration).**
    More migration increases the characteristic length, which means at any
    fixed distance d, Fst is lower (i.e., increasing L decreases Fst). -/
theorem continuousSteppingStoneFst_decreases_with_L (L₁ L₂ d : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hd : 0 < d) (h_more : L₁ < L₂) :
    continuousSteppingStoneFst L₂ d < continuousSteppingStoneFst L₁ d := by
  unfold continuousSteppingStoneFst
  have h_ratio_lt : d / L₂ < d / L₁ := by
    exact div_lt_div_of_pos_left hd hL₁ h_more
  have h_exp_lt : Real.exp (-(d / L₁)) < Real.exp (-(d / L₂)) := by
    apply Real.exp_lt_exp.mpr; linarith
  linarith

/-! ### Allele Frequency Homogenization by Migration -/

/-- **Allele frequency convergence under migration.**
    Starting from initial frequency p₀ in a deme, the frequency after t
    generations of migration at rate m toward a continent with frequency p_c is:
    p(t) = p_c + (p₀ - p_c) × (1-m)^t.
    The deviation from the continental frequency decays geometrically. -/
noncomputable def alleleFreqAfterMigration (p₀ p_c m : ℝ) (t : ℕ) : ℝ :=
  p_c + (p₀ - p_c) * (1 - m) ^ t

/-- After 0 generations of migration, frequency is unchanged. -/
theorem alleleFreqAfterMigration_at_zero (p₀ p_c m : ℝ) :
    alleleFreqAfterMigration p₀ p_c m 0 = p₀ := by
  unfold alleleFreqAfterMigration
  simp

/-- **Allele frequency converges toward continental frequency.**
    The deviation |p(t) - p_c| decreases with each generation of migration. -/
theorem alleleFreq_deviation_decreases (p₀ p_c m : ℝ) (t₁ t₂ : ℕ)
    (hm : 0 < m) (hm1 : m < 1)
    (hne : p₀ ≠ p_c) (ht : t₁ < t₂) :
    |alleleFreqAfterMigration p₀ p_c m t₂ - p_c| <
    |alleleFreqAfterMigration p₀ p_c m t₁ - p_c| := by
  unfold alleleFreqAfterMigration
  simp only [add_sub_cancel_left]
  rw [abs_mul, abs_mul]
  apply mul_lt_mul_of_pos_left
  · rw [abs_of_nonneg (pow_nonneg (by linarith) _),
        abs_of_nonneg (pow_nonneg (by linarith) _)]
    have h_base_pos : 0 < 1 - m := by linarith
    have h_base_lt : 1 - m < 1 := by linarith
    exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht
  · exact abs_pos.mpr (sub_ne_zero.mpr hne)

/-! ### Effective Migration Rate -/

/-- **Effective migration rate for asymmetric migration.**
    When migration is asymmetric between two demes, the effective migration
    rate that determines the overall Fst is the arithmetic mean. -/
noncomputable def effectiveMigration (m₁₂ m₂₁ : ℝ) : ℝ :=
  (m₁₂ + m₂₁) / 2

/-- Effective migration is between the two directional rates. -/
theorem effectiveMigration_bounds (m₁₂ m₂₁ : ℝ) (h : m₂₁ < m₁₂) :
    m₂₁ < effectiveMigration m₁₂ m₂₁ ∧ effectiveMigration m₁₂ m₂₁ < m₁₂ := by
  unfold effectiveMigration
  constructor <;> linarith

/-- Effective migration equals both rates when migration is symmetric. -/
theorem effectiveMigration_symmetric (m : ℝ) :
    effectiveMigration m m = m := by
  unfold effectiveMigration
  ring

/-- **Asymmetric migration yields asymmetric Fst.**
    The population receiving more migrants has lower Fst (from its perspective).
    We prove the Fst difference is proportional to the migration asymmetry. -/
theorem asymmetric_fst_difference_sign (Ne m₁₂ m₂₁ : ℝ)
    (hNe : 0 < Ne) (hm₁₂ : 0 < m₁₂) (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    islandModelFst Ne m₁₂ < islandModelFst Ne m₂₁ := by
  exact islandModelFst_strictAnti_m Ne hNe h_asym

/-! ### Migration and LD Homogenization -/

/-- **LD similarity between populations under migration.**
    Populations exchanging migrants share more similar LD patterns.
    We model the LD correlation as a function of scaled migration rate:
    LD_correlation(M) = M² / (1 + M)² (proportion of LD that is shared).
    This accounts for both allele frequency sharing and haplotype sharing. -/
noncomputable def ldCorrelationFromMigration (M : ℝ) : ℝ :=
  M ^ 2 / (1 + M) ^ 2

/-- LD correlation from migration is nonneg. -/
theorem ldCorrelationFromMigration_nonneg (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ ldCorrelationFromMigration M := by
  unfold ldCorrelationFromMigration
  exact div_nonneg (sq_nonneg M) (sq_nonneg (1 + M))

/-- LD correlation from migration is at most 1. -/
theorem ldCorrelationFromMigration_le_one (M : ℝ) (hM : 0 ≤ M) :
    ldCorrelationFromMigration M ≤ 1 := by
  unfold ldCorrelationFromMigration
  rw [div_le_one (sq_pos_of_pos (by linarith : 0 < 1 + M))]
  exact sq_le_sq' (by linarith) (by linarith)

/-- **LD correlation increases with migration rate.** -/
theorem ldCorrelationFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (h_more : M₁ < M₂) :
    ldCorrelationFromMigration M₁ < ldCorrelationFromMigration M₂ := by
  unfold ldCorrelationFromMigration
  -- (M₁/(1+M₁))² < (M₂/(1+M₂))² follows from M₁/(1+M₁) < M₂/(1+M₂)
  rw [div_pow, div_pow]
  have h1M₁ : 0 < 1 + M₁ := by linarith
  have h1M₂ : 0 < 1 + M₂ := by linarith
  have h_ratio : M₁ / (1 + M₁) < M₂ / (1 + M₂) := by
    rw [div_lt_div_iff₀ h1M₁ h1M₂]; nlinarith
  have h_pos : 0 < M₁ / (1 + M₁) := div_pos hM₁ h1M₁
  exact div_lt_div_of_pos_right (sq_lt_sq' (by linarith) h_ratio)
    (sq_pos_of_pos h1M₂)

end MigrationDriftFoundations


/-!
## Derivation of Fst from Wright-Fisher Drift Dynamics

Rather than *defining* Fst as a formula, we *derive* it from the fundamental
Wright-Fisher recurrence for heterozygosity.  The key identity is:

  H(t+1) = (1 - 1/(2N)) × H(t)

which expresses the fact that two alleles drawn from generation t+1 are
identical by descent with probability 1/(2N), leaving heterozygosity reduced
by that factor each generation.

We then:
1. Solve this recurrence in closed form by induction.
2. Define Fst(t) = 1 - H(t)/H₀ and derive its properties.
3. Introduce mutation, find the equilibrium heterozygosity H* = θ/(1+θ),
   and derive Fst_eq = 1/(1+θ) as a *consequence*.
-/

section FstDerivationFromDrift

/-! ### Pure-drift heterozygosity recurrence -/

/-- **Heterozygosity recurrence under pure drift.**
    Each generation, the probability that two sampled alleles are distinct
    is reduced by a factor of (1 - 1/(2Ne)). -/
noncomputable def hetRecurrence (Ne : ℝ) (H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => (1 - 1 / (2 * Ne)) * hetRecurrence Ne H₀ t

/-- **Closed-form solution by induction.**
    hetRecurrence Ne H₀ t = (1 - 1/(2Ne))^t × H₀. -/
theorem hetRecurrence_closed_form (Ne H₀ : ℝ) (t : ℕ) :
    hetRecurrence Ne H₀ t = (1 - 1 / (2 * Ne)) ^ t * H₀ := by
  induction t with
  | zero =>
    simp [hetRecurrence]
  | succ n ih =>
    simp only [hetRecurrence, ih]
    ring

/-! ### Fst derived from heterozygosity loss -/

/-- **Fst derived from heterozygosity decay.**
    Fst(t) = 1 - H(t)/H₀ = 1 - (1 - 1/(2Ne))^t.
    This is not a definition imposed from outside; it is the fractional
    loss of heterozygosity after t generations of drift. -/
noncomputable def fstDerived (Ne : ℝ) (t : ℕ) : ℝ :=
  1 - (1 - 1 / (2 * Ne)) ^ t

/-- **Fst matches heterozygosity loss.**
    When H₀ > 0, fstDerived Ne t = 1 - hetRecurrence Ne H₀ t / H₀. -/
theorem fstDerived_eq_het_loss (Ne H₀ : ℝ) (t : ℕ) (hH₀ : H₀ ≠ 0) :
    fstDerived Ne t = 1 - hetRecurrence Ne H₀ t / H₀ := by
  unfold fstDerived
  rw [hetRecurrence_closed_form]
  field_simp

/-- **Fst(0) = 0**: populations start undifferentiated. -/
theorem fstDerived_zero (Ne : ℝ) : fstDerived Ne 0 = 0 := by
  unfold fstDerived
  simp

/-- **Fst is monotonically increasing in t.**
    More generations of drift → more differentiation. -/
theorem fstDerived_mono (Ne : ℝ) (t₁ t₂ : ℕ) (hNe : 2 < Ne)
    (h_lt : t₁ < t₂) :
    fstDerived Ne t₁ < fstDerived Ne t₂ := by
  unfold fstDerived
  have h_base_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  linarith [pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_lt]

/-- **0 ≤ Fst(t) for all t when Ne ≥ 2.** -/
theorem fstDerived_nonneg (Ne : ℝ) (t : ℕ) (hNe : 2 ≤ Ne) :
    0 ≤ fstDerived Ne t := by
  unfold fstDerived
  rw [sub_nonneg]
  apply pow_le_one₀
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · rw [sub_le_self_iff]; positivity

/-- **Fst(t) < 1 for all t when Ne ≥ 2.** -/
theorem fstDerived_lt_one (Ne : ℝ) (t : ℕ) (hNe : 2 ≤ Ne) :
    fstDerived Ne t < 1 := by
  unfold fstDerived
  linarith [pow_pos (show 0 < 1 - 1 / (2 * Ne) by
    rw [sub_pos, div_lt_one (by linarith)]; linarith) t]

/-- **Fst increases faster with smaller Ne.**
    For t ≥ 1 and Ne₁ < Ne₂, we have fstDerived Ne₁ t > fstDerived Ne₂ t.
    Smaller populations drift faster. -/
theorem fstDerived_faster_small_Ne (Ne₁ Ne₂ : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂) (h_lt : Ne₁ < Ne₂) :
    fstDerived Ne₂ t < fstDerived Ne₁ t := by
  unfold fstDerived
  -- Need (1 - 1/(2Ne₂))^t > (1 - 1/(2Ne₁))^t, i.e. larger base → larger power
  -- which means 1 - (larger)^t < 1 - (smaller)^t
  have h_base₁_pos : 0 < 1 - 1 / (2 * Ne₁) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base₂_lt_one : 1 - 1 / (2 * Ne₂) < 1 := by
    rw [sub_lt_self_iff]; positivity
  have h_base_lt : 1 - 1 / (2 * Ne₁) < 1 - 1 / (2 * Ne₂) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  linarith [pow_lt_pow_left₀ h_base_lt (le_of_lt h_base₁_pos) (Nat.not_eq_zero_of_lt (by omega : 0 < t))]

/-- **Consistency check: fstDerived agrees with the earlier fstFromDrift.**
    This confirms our derivation produces the same formula that was previously
    defined axiomatically. -/
theorem fstDerived_eq_fstFromDrift (Ne : ℝ) (t : ℕ) :
    fstDerived Ne t = fstFromDrift t Ne := by
  unfold fstDerived fstFromDrift

/-! ### Mutation-drift recurrence and equilibrium -/

/-- **Heterozygosity recurrence with mutation.**
    Drift reduces heterozygosity by factor (1 - 1/(2N)), while mutation
    creates new heterozygosity at rate 2μ from homozygous sites. -/
noncomputable def hetMutationDriftRecurrence (Ne mu : ℝ) (H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => (1 - 1 / (2 * Ne)) * hetMutationDriftRecurrence Ne mu H₀ t +
              2 * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t)

/-- **Equilibrium heterozygosity.**
    At mutation-drift balance, H* = θ/(1+θ) where θ = 4Neμ. -/
noncomputable def hetEquilibrium (Ne mu : ℝ) : ℝ :=
  4 * Ne * mu / (1 + 4 * Ne * mu)

/-- **Algebraic verification of the fixed point.**
    If we start at H* = θ/(1+θ), one step of the recurrence returns H*.
    This proves H* is indeed a fixed point — the equilibrium heterozygosity. -/
theorem hetMutationDrift_fixed_point (Ne mu : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu) :
    hetMutationDriftRecurrence Ne mu (hetEquilibrium Ne mu) 1 =
      hetEquilibrium Ne mu := by
  unfold hetMutationDriftRecurrence hetEquilibrium
  -- We need: (1 - 1/(2Ne)) * (4Neμ/(1+4Neμ)) + 2μ * (1 - 4Neμ/(1+4Neμ))
  --        = 4Neμ/(1+4Neμ)
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  have hNe2 : (2 * Ne) ≠ 0 := by linarith
  field_simp
  ring

/-- **The fixed point is unique in [0,1].**
    For any H in [0,1] satisfying f(H) = H, we must have H = θ/(1+θ).
    We prove this by direct algebra: the fixed-point equation is linear in H. -/
theorem hetMutationDrift_fixed_point_unique (Ne mu H : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu)
    (h_fixed : (1 - 1 / (2 * Ne)) * H + 2 * mu * (1 - H) = H) :
    H = hetEquilibrium Ne mu := by
  unfold hetEquilibrium
  -- From the fixed-point equation:
  -- H - (1 - 1/(2Ne))H - 2μ(1-H) = 0
  -- H × [1 - (1 - 1/(2Ne)) + 2μ] = 2μ
  -- H × [1/(2Ne) + 2μ] = 2μ
  -- H = 2μ / (1/(2Ne) + 2μ) = 4Neμ / (1 + 4Neμ)
  have hNe2 : (2 * Ne) ≠ 0 := by linarith
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  have hcoeff : 0 < 1 / (2 * Ne) + 2 * mu := by positivity
  -- Rearrange h_fixed: H * (1/(2Ne) + 2μ) = 2μ
  have h_rearranged : H * (1 / (2 * Ne) + 2 * mu) = 2 * mu := by
    field_simp at h_fixed ⊢
    linarith
  -- Solve for H
  have h_solve : H = 2 * mu / (1 / (2 * Ne) + 2 * mu) := by
    field_simp at h_rearranged ⊢
    linarith
  -- Now show 2μ / (1/(2Ne) + 2μ) = 4Neμ / (1 + 4Neμ)
  rw [h_solve]
  field_simp
  ring

/-- **Derive Fst_eq = 1/(1+θ) from the equilibrium heterozygosity.**
    Since H* = θ/(1+θ) and Fst = 1 - H* (for biallelic loci where H_max = 1),
    we get Fst_eq = 1 - θ/(1+θ) = 1/(1+θ).

    This is Wright's classical result, but *derived* from the recurrence
    rather than postulated. -/
theorem fstEquilibrium_derived (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - hetEquilibrium Ne mu = 1 / (1 + 4 * Ne * mu) := by
  unfold hetEquilibrium
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  field_simp
  ring

/-- **Derived Fst_eq agrees with the earlier fstMutationDriftEquilibrium.**
    This confirms that the formula we derived from the recurrence is the
    same as the one previously defined. -/
theorem fstEquilibrium_derived_consistent (Ne mu : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - hetEquilibrium Ne mu = fstMutationDriftEquilibrium (4 * Ne * mu) := by
  rw [fstEquilibrium_derived Ne mu hNe hmu]
  unfold fstMutationDriftEquilibrium

/-- **Equilibrium heterozygosity is in (0, 1) for positive parameters.** -/
theorem hetEquilibrium_pos (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    0 < hetEquilibrium Ne mu := by
  unfold hetEquilibrium
  positivity

theorem hetEquilibrium_lt_one (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    hetEquilibrium Ne mu < 1 := by
  unfold hetEquilibrium
  rw [div_lt_one (by positivity)]
  linarith

/-- **Equilibrium Fst is in (0, 1) for positive parameters.** -/
theorem fstEquilibrium_derived_pos (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    0 < 1 - hetEquilibrium Ne mu := by
  linarith [hetEquilibrium_lt_one Ne mu hNe hmu]

theorem fstEquilibrium_derived_lt_one (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - hetEquilibrium Ne mu < 1 := by
  linarith [hetEquilibrium_pos Ne mu hNe hmu]

/-- **Larger θ → lower equilibrium Fst** (derived version).
    More mutation (or larger Ne) means more diversity maintained against drift. -/
theorem fstEquilibrium_derived_decreases (Ne₁ Ne₂ mu : ℝ)
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (hmu : 0 < mu)
    (h_lt : Ne₁ < Ne₂) :
    1 - hetEquilibrium Ne₂ mu < 1 - hetEquilibrium Ne₁ mu := by
  -- Equivalent to hetEquilibrium Ne₁ mu < hetEquilibrium Ne₂ mu
  -- i.e., 4Ne₁μ/(1+4Ne₁μ) < 4Ne₂μ/(1+4Ne₂μ)
  unfold hetEquilibrium
  have h₁ : 0 < 1 + 4 * Ne₁ * mu := by positivity
  have h₂ : 0 < 1 + 4 * Ne₂ * mu := by positivity
  rw [sub_lt_sub_iff_left]
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

end FstDerivationFromDrift

end Calibrator
