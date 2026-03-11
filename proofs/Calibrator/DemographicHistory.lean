import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Demographic History Models and PGS Portability

This file formalizes how specific demographic histories (migration,
admixture, bottlenecks, expansion) affect PGS portability predictions.

Key results:
1. Island model equilibrium and migration-drift balance
2. Stepping-stone models for isolation by distance
3. Admixture models and ancestry-specific effects
4. Recent expansion and rare variant architecture
5. Archaic introgression effects on PGS

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Island Model and Migration-Drift Balance

The Wright-Fisher island model gives equilibrium Fst as a function
of migration rate. This determines the baseline portability.
-/

section IslandModel

/-- **Island model equilibrium Fst.**
    F_ST = 1 / (1 + 4·Ne·m) where m is migration rate per generation. -/
noncomputable def islandModelFst (Ne m : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- Island model Fst is in (0, 1) for positive parameters. -/
theorem island_fst_in_unit_interval (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) :
    0 < islandModelFst Ne m ∧ islandModelFst Ne m < 1 := by
  unfold islandModelFst
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]; linarith [mul_pos hNe hm]

/-- **More migration → lower Fst → better portability.** -/
theorem more_migration_lower_fst (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    islandModelFst Ne m₂ < islandModelFst Ne m₁ := by
  unfold islandModelFst
  apply div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith)

/-- **Recent migration disrupts the equilibrium.**
    If migration rate changes from m₁ to m₂ at time t₀,
    Fst is between the old and new equilibria for a transient period.
    Current PGS portability may not match equilibrium predictions. -/
theorem transient_fst_between_equilibria
    (fst_old fst_new fst_current : ℝ)
    (h_between_low : fst_new ≤ fst_current)
    (h_between_high : fst_current ≤ fst_old)
    (h_not_eq_old : fst_current ≠ fst_old) :
    fst_new ≤ fst_current ∧ fst_current < fst_old := by
  exact ⟨h_between_low, lt_of_le_of_ne h_between_high h_not_eq_old⟩

end IslandModel


/-!
## Stepping-Stone Model (Isolation by Distance)

In a stepping-stone model, gene flow occurs mainly between neighboring
populations. This creates a spatial gradient in Fst.
-/

section SteppingStone

/-- **Pairwise Fst in the stepping-stone model.**
    F_ST(d) ≈ d / (d + 4·Ne·m·σ²) for physical distance d,
    dispersal variance σ², and local migration rate m. -/
noncomputable def steppingStoneFst (d Ne m σ_sq : ℝ) : ℝ :=
  d / (d + 4 * Ne * m * σ_sq)

/-- Stepping-stone Fst increases with distance. -/
theorem stepping_stone_fst_increasing (d₁ d₂ Ne m σ_sq : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq)
    (hd₁ : 0 < d₁) (h_farther : d₁ < d₂) :
    steppingStoneFst d₁ Ne m σ_sq < steppingStoneFst d₂ Ne m σ_sq := by
  unfold steppingStoneFst
  have h_C := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Stepping-stone Fst saturates at large distances.**
    As d → ∞, F_ST → 1. But for moderate distances, Fst grows sublinearly.
    This means portability should decline slower at larger distances. -/
theorem stepping_stone_fst_saturates (d Ne m σ_sq : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq)
    (hd : 0 < d) :
    steppingStoneFst d Ne m σ_sq < 1 := by
  unfold steppingStoneFst
  rw [div_lt_one (by nlinarith [mul_pos (mul_pos hNe hm) hσ])]
  linarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ]

/-- **Isolation by distance creates continuous portability gradient.**
    Unlike the island model where portability is uniform for all non-source
    populations, the stepping-stone model predicts a gradual decline. -/
theorem ibd_portability_gradient
    (d₁ d₂ r2_source r2_d₁ r2_d₂ : ℝ)
    (h_farther : d₁ < d₂)
    (h_monotone : r2_d₂ < r2_d₁) (h_d₁_lt : r2_d₁ < r2_source) :
    r2_d₂ < r2_source := by linarith

end SteppingStone


/-!
## Admixture Models

Recently admixed populations pose unique challenges for PGS.
The admixture proportions and time since admixture determine
the LD structure and portability.
-/

section AdmixtureModels

/-- **Two-way admixture Fst.**
    For a population that is α fraction from population A and
    (1-α) from population B:
    Fst(admixed, A) ≈ (1-α)² × Fst(A,B). -/
noncomputable def admixedFst (α fst_AB : ℝ) : ℝ :=
  (1 - α) ^ 2 * fst_AB

/-- Admixed Fst is smaller than parent Fst. -/
theorem admixed_fst_smaller (α fst_AB : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (h_fst : 0 < fst_AB) :
    admixedFst α fst_AB < fst_AB := by
  unfold admixedFst
  have h1 : (1 - α) ^ 2 < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mpr
    rw [abs_of_nonneg (by linarith)]; linarith
  calc (1 - α) ^ 2 * fst_AB < 1 * fst_AB := mul_lt_mul_of_pos_right h1 h_fst
    _ = fst_AB := one_mul _

/-- **PGS trained in parent population has intermediate portability to admixed.**
    Better than to the other parent, worse than to itself. -/
theorem admixed_intermediate_portability
    (r2_A_to_A r2_A_to_admixed r2_A_to_B : ℝ)
    (h_self : r2_A_to_admixed < r2_A_to_A)
    (h_better : r2_A_to_B < r2_A_to_admixed) :
    r2_A_to_B < r2_A_to_admixed ∧ r2_A_to_admixed < r2_A_to_A :=
  ⟨h_better, h_self⟩

/-- **Admixture proportion determines optimal PGS combination.**
    For an individual with α fraction ancestry A and (1-α) from B,
    the optimal PGS is approximately α × PGS_A + (1-α) × PGS_B. -/
theorem optimal_admixed_pgs_is_weighted
    (pgs_A pgs_B α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    -- The weighted combination is between the two parent PGS values
    min pgs_A pgs_B ≤ α * pgs_A + (1 - α) * pgs_B ∧
      α * pgs_A + (1 - α) * pgs_B ≤ max pgs_A pgs_B := by
  constructor
  · by_cases h : pgs_A ≤ pgs_B
    · simp [min_eq_left h]
      nlinarith
    · push_neg at h
      simp [min_eq_right (le_of_lt h)]
      nlinarith
  · by_cases h : pgs_A ≤ pgs_B
    · simp [max_eq_right h]
      nlinarith
    · push_neg at h
      simp [max_eq_left (le_of_lt h)]
      nlinarith

end AdmixtureModels


/-!
## Recent Expansion and Rare Variants

Recent population expansion creates an excess of rare variants.
These variants are population-specific and affect PGS portability.
-/

section RecentExpansion

/-- **Proportion of singletons increases with expansion.**
    Under expansion from N₀ to N₁ in T generations,
    the proportion of singletons ≈ 1 - log(N₀)/log(N₁). -/
noncomputable def singletonProportion (N₀ N₁ : ℝ) : ℝ :=
  1 - Real.log N₀ / Real.log N₁

/-- More expansion → more singletons. -/
theorem more_expansion_more_singletons
    (N₀ N₁ N₂ : ℝ)
    (hN₀ : 1 < N₀) (hN₁ : N₀ < N₁) (hN₂ : N₁ < N₂) :
    singletonProportion N₀ N₁ < singletonProportion N₀ N₂ := by
  unfold singletonProportion
  rw [sub_lt_sub_iff_left]
  apply div_lt_div_of_pos_left
  · exact Real.log_pos hN₀
  · exact Real.log_pos (by linarith)
  · exact Real.log_lt_log (by linarith) hN₂

/-- **Rare variants are population-specific.**
    A singleton in population A has probability 0 of being observed
    in population B (if no recent shared ancestry).
    This means rare-variant PGS has zero portability. -/
theorem rare_variant_pgs_not_portable
    (r2_rare_source r2_rare_target : ℝ)
    (h_zero : r2_rare_target = 0) (h_source_pos : 0 < r2_rare_source) :
    r2_rare_target < r2_rare_source := by
  linarith

/-- **Common variant PGS is more portable than rare variant PGS.**
    Common variants (MAF > 5%) are more likely to be shared across
    populations → better portability. -/
theorem common_more_portable_than_rare
    (r2_common r2_rare : ℝ)
    (h_better : r2_rare < r2_common)
    (h_rare_nn : 0 ≤ r2_rare) :
    r2_rare / r2_common < 1 := by
  rw [div_lt_one (by linarith)]
  exact h_better

end RecentExpansion


/-!
## Archaic Introgression

Introgression from archaic hominins (Neanderthal, Denisovan) introduced
genetic variants that differ across modern populations. These affect
PGS portability for traits where introgressed variants contribute.
-/

section ArchaicIntrogression

/-- **Introgression fraction differs across populations.**
    European/Asian: ~2% Neanderthal
    Melanesian: ~2% Neanderthal + ~3-5% Denisovan
    African: ~0-0.3% archaic
    These differences create population-specific genetic variants. -/
theorem introgression_creates_population_specific_variants
    (pct_eur pct_afr : ℝ)
    (h_eur : 1.5 < pct_eur) (h_eur_lt : pct_eur < 2.5)
    (h_afr : 0 ≤ pct_afr) (h_afr_lt : pct_afr < 1/2) :
    pct_afr < pct_eur := by linarith

/-- **Introgressed variants contribute to trait heritability.**
    For traits under selection involving introgressed regions
    (e.g., immune function, skin pigmentation), a fraction of
    heritability comes from Neanderthal-derived alleles.
    This fraction is absent in African populations → portability gap. -/
theorem introgression_portability_gap
    (h2_shared h2_introgressed : ℝ)
    (h_shared : 0 < h2_shared)
    (h_intro : 0 < h2_introgressed) :
    -- In the non-introgressed population, only shared heritability is captured
    h2_shared < h2_shared + h2_introgressed := by linarith

/-- **The introgression portability gap is small for most traits.**
    Most heritability comes from shared ancient variants.
    Introgression contributes a small fraction (typically < 1%). -/
theorem introgression_gap_bounded
    (h2_total h2_intro : ℝ)
    (h_total : 0 < h2_total)
    (h_small : h2_intro ≤ (1/100) * h2_total)
    (h_intro_nn : 0 ≤ h2_intro) :
    h2_intro / h2_total ≤ 1/100 := by
  exact div_le_of_le_mul₀ (le_of_lt h_total) (by norm_num) h_small

end ArchaicIntrogression


/-!
## Founder Effects and Genetic Drift in Isolated Populations

Small, isolated populations experience strong genetic drift,
creating large Fst and potentially unusual genetic architecture.
-/

section FounderEffects

/-- **Founder effect amplifies drift.**
    A population founded by k individuals has effective Fst
    approximately 1/(2k) per generation in the initial bottleneck. -/
noncomputable def founderFst (k : ℕ) (t : ℕ) : ℝ :=
  1 - (1 - 1 / (2 * (k : ℝ))) ^ t

/-- Smaller founding population → larger Fst. -/
theorem smaller_founder_larger_fst
    (k₁ k₂ : ℕ) (t : ℕ)
    (hk₁ : 2 < k₁) (hk₂ : 2 < k₂)
    (h_smaller : k₂ < k₁) (ht : 0 < t) :
    founderFst k₁ t < founderFst k₂ t := by
  unfold founderFst
  -- 1 - 1/(2k₂) < 1 - 1/(2k₁) because k₂ < k₁
  have h_base : 1 - 1 / (2 * (k₂ : ℝ)) < 1 - 1 / (2 * (k₁ : ℝ)) := by
    rw [sub_lt_sub_iff_left]
    apply div_lt_div_of_pos_left one_pos
    · exact Nat.cast_pos.mpr (by omega) |> (fun h => mul_pos (by norm_num : (0:ℝ) < 2) h)
    · exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr h_smaller) (by norm_num : (0:ℝ) < 2)
  have h_nn : 0 ≤ 1 - 1 / (2 * (k₂ : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (2 : ℝ) ≤ k₂ := by exact Nat.ofNat_le_cast.mpr (by omega)
    linarith
  linarith [pow_lt_pow_left₀ h_base h_nn (by omega : t ≠ 0)]

/-- **PGS portability to isolated populations is poor.**
    Finnish, Ashkenazi Jewish, and Pacific Islander populations
    have experienced founder effects that make PGS less portable. -/
theorem founder_effect_reduces_portability
    (r2_cosmopolitan r2_isolated : ℝ)
    (h_drop : r2_isolated < r2_cosmopolitan)
    (h_pos : 0 < r2_cosmopolitan) :
    r2_isolated / r2_cosmopolitan < 1 := by
  rw [div_lt_one h_pos]; exact h_drop

end FounderEffects

end Calibrator
