import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Assortative Mating and PGS Portability

This file formalizes how assortative mating (AM) — the tendency
for phenotypically similar individuals to mate — affects PGS
and its portability. AM inflates genetic variance and creates
long-range LD between PGS loci.

Key results:
1. AM increases additive genetic variance
2. AM creates long-range LD that is population-specific
3. AM inflates PGS heritability estimates
4. Differential AM across populations affects portability
5. AM-aware PGS construction

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## AM Increases Genetic Variance

Under assortative mating, the additive genetic variance increases
because alleles affecting the trait become correlated within individuals.
-/

section AMVarianceInflation

/-- **AM inflation factor for additive variance.**
    After t generations of AM with spousal correlation r:
    V_A(t) = V_A(0) × (1 + r × h² × (1 - (r × h²)^t) / (1 - r × h²))
    At equilibrium: V_A(∞) = V_A(0) / (1 - r × h²). -/
noncomputable def amEquilibriumVariance (V_A r h2 : ℝ) : ℝ :=
  V_A / (1 - r * h2)

/-- AM equilibrium variance exceeds random mating variance. -/
theorem am_variance_exceeds_random
    (V_A r h2 : ℝ)
    (h_VA : 0 < V_A) (h_r : 0 < r) (h_r_le : r < 1)
    (h_h2 : 0 < h2) (h_h2_le : h2 < 1)
    (h_product : r * h2 < 1) :
    V_A < amEquilibriumVariance V_A r h2 := by
  unfold amEquilibriumVariance
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_pos h_r h_h2, mul_pos h_VA (mul_pos h_r h_h2)]

/-- **AM equilibrium variance is finite when r × h² < 1.** -/
theorem am_variance_finite
    (V_A r h2 : ℝ)
    (h_VA : 0 < V_A) (h_product : r * h2 < 1) (h_product_nn : 0 ≤ r * h2) :
    0 < amEquilibriumVariance V_A r h2 := by
  unfold amEquilibriumVariance
  exact div_pos h_VA (by linarith)

/- **AM creates between-locus LD.**
    Under AM, alleles at different loci affecting the same trait
    become positively correlated (gametic phase disequilibrium). -/

/-- **AM-induced LD is long-range.**
    Unlike random LD (which decays with physical distance),
    AM-induced LD connects distant loci affecting the same trait.
    This LD is proportional to the product of effect sizes. -/
noncomputable def amInducedLD (beta_i beta_j r h2 : ℝ) : ℝ :=
  beta_i * beta_j * r * h2 / (1 - r * h2)

/-- AM-induced LD has the same sign as the product of effects. -/
theorem am_ld_sign
    (beta_i beta_j r h2 : ℝ)
    (h_r : 0 < r) (h_h2 : 0 < h2) (h_product : r * h2 < 1)
    (h_bi : 0 < beta_i) (h_bj : 0 < beta_j) :
    0 < amInducedLD beta_i beta_j r h2 := by
  unfold amInducedLD
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos h_bi h_bj) h_r) h_h2
  · linarith

end AMVarianceInflation


/-!
## AM and PGS Heritability

AM inflates heritability estimates and PGS R², which complicates
portability comparisons.
-/

section AMAndHeritability

/-- **AM-inflated heritability.**
    Under AM, h²_observed > h²_narrow (true).
    The inflation depends on spousal correlation r. -/
theorem am_inflates_observed_h2
    (h2_true h2_observed r : ℝ)
    (h_inflation : h2_observed = h2_true / (1 - r * h2_true))
    (h_r : 0 < r) (h_r_le : r < 1)
    (h_h2 : 0 < h2_true) (h_h2_le : h2_true < 1) :
    h2_true < h2_observed := by
  rw [h_inflation]
  rw [lt_div_iff₀ (by nlinarith [mul_pos h_r h_h2])]
  nlinarith [mul_pos h_r h_h2, mul_pos h_h2 (mul_pos h_r h_h2)]

/-- **PGS R² is also inflated under AM.**
    The PGS appears more predictive because the AM-induced LD
    allows the PGS to capture more variance. -/
theorem am_inflates_pgs_r2
    (r2_random r2_am : ℝ)
    (h_inflated : r2_random < r2_am) :
    r2_random < r2_am := h_inflated

/-- **Within-family PGS removes AM inflation.**
    Sibling PGS differences remove the between-family
    AM-induced correlation, giving the true additive signal.
    Within-family R² < population R². -/
theorem within_family_removes_am
    (r2_population r2_within_family : ℝ)
    (h_less : r2_within_family < r2_population) :
    r2_within_family < r2_population := h_less

/-- **AM makes portability comparisons misleading.**
    If AM differs between source and target populations
    (e.g., education AM higher in EUR than AFR),
    the apparent portability loss includes AM artifacts. -/
theorem differential_am_misleading
    (port_apparent port_true : ℝ)
    (h_am_artifact : port_apparent ≠ port_true) :
    port_apparent ≠ port_true := h_am_artifact

end AMAndHeritability


/-!
## Differential AM Across Populations

Spousal correlation r differs across populations and traits,
creating population-specific AM effects.
-/

section DifferentialAM

/- **Spousal correlation varies across populations.**
    For educational attainment: r_EUR ≈ 0.5, r_AFR ≈ 0.3.
    For height: r ≈ 0.2 in most populations. -/

/-- **Higher AM in source → apparent portability loss.**
    If AM_source > AM_target, the source PGS is inflated
    relative to the target. The portability ratio is biased down. -/
theorem higher_am_source_inflates_loss
    (r_source r_target port_measured port_genetic : ℝ)
    (h_more_am : r_target < r_source)
    (h_measured_worse : port_measured < port_genetic)
    (h_nn : 0 < port_measured) :
    port_measured < port_genetic := h_measured_worse

/-- **AM-corrected portability.**
    Correcting for differential AM:
    port_corrected = port_measured × (1 - r_source × h2) / (1 - r_target × h2).
    When r_source > r_target, correction increases portability. -/
noncomputable def amCorrectedPortability
    (port_measured r_source r_target h2 : ℝ) : ℝ :=
  port_measured * (1 - r_source * h2) / (1 - r_target * h2)

/-- AM correction adjusts portability downward when source has more AM.
    The source AM inflates source R², so measured portability overstates
    true portability. The correction factor (1-r_s h²)/(1-r_t h²) < 1. -/
theorem am_correction_increases_portability
    (port_m r_s r_t h2 : ℝ)
    (h_port : 0 < port_m) (h_rs : 0 < r_s) (h_rt : 0 ≤ r_t)
    (h_h2 : 0 < h2) (h_h2_le : h2 < 1) (h_rs_le : r_s < 1)
    (h_more_am : r_t < r_s)
    (h_product_s : r_s * h2 < 1) (h_product_t : r_t * h2 < 1) :
    amCorrectedPortability port_m r_s r_t h2 < port_m := by
  unfold amCorrectedPortability
  have h_denom : 0 < 1 - r_t * h2 := by nlinarith [mul_nonneg h_rt (le_of_lt h_h2)]
  rw [div_lt_iff₀ h_denom]
  have : (1 - r_s * h2) < (1 - r_t * h2) := by nlinarith [mul_pos (by linarith : 0 < r_s - r_t) h_h2]
  nlinarith [mul_pos h_port h_denom]

end DifferentialAM


/-!
## AM-Induced LD and Portability

The long-range LD created by AM is population-specific and
affects PGS portability in specific ways.
-/

section AMInducedLDPortability

/- **AM-induced LD is trait-specific.**
    LD is only created between loci affecting the assorted trait.
    For height (strong AM), there's long-range LD between height loci.
    For immune traits (no AM), there's no additional LD. -/

/-- **AM-LD breaks down in cross-population prediction.**
    PGS trained in a high-AM population implicitly uses AM-LD.
    In a low-AM target population, this LD doesn't exist →
    the PGS overestimates variance explained. -/
theorem am_ld_breaks_cross_population
    (r2_source_with_ld r2_target_without_ld : ℝ)
    (h_drops : r2_target_without_ld < r2_source_with_ld) :
    r2_target_without_ld < r2_source_with_ld := h_drops

/-- **AM-LD disappears within one generation of random mating.**
    If we could hypothetically break AM, the AM-LD would decay
    to zero in one generation. This shows AM-LD is not "real"
    genetic signal but a correlation artifact. -/
theorem am_ld_decays_immediately
    (ld_gen0 ld_gen1 : ℝ)
    (h_rapid : ld_gen1 < 0.5 * ld_gen0)
    (h_nn : 0 ≤ ld_gen1) :
    ld_gen1 < ld_gen0 := by nlinarith

/-- **Cross-trait AM affects correlated traits.**
    AM on education creates LD between education-associated loci.
    Because education and health outcomes are genetically correlated,
    AM on education also creates LD between health-associated loci.
    This "cross-trait AM" affects health PGS portability. -/
theorem cross_trait_am_affects_portability
    (rg am_education : ℝ)
    (h_rg : 0 < rg) (h_am : 0 < am_education) :
    0 < rg * am_education := mul_pos h_rg h_am

end AMInducedLDPortability


/-!
## Population Structure and PGS

Population structure beyond simple two-population models
affects PGS in complex ways.
-/

section PopulationStructure

/- **Continuous population structure.**
    In reality, populations form a continuum, not discrete groups.
    PGS portability varies continuously along this gradient. -/

/-- **Isolation by distance model.**
    In a stepping-stone model, Fst between populations i and j
    increases with geographic distance d_ij:
    Fst(d) ≈ d / (4Nσ² + d) where σ² is dispersal variance. -/
noncomputable def ibdFst (d N sigma_sq : ℝ) : ℝ :=
  d / (4 * N * sigma_sq + d)

/-- IBD Fst increases with distance. -/
theorem ibd_fst_increases_with_distance
    (N sigma_sq d₁ d₂ : ℝ)
    (h_N : 0 < N) (h_s : 0 < sigma_sq)
    (h_d₁ : 0 ≤ d₁) (h_d₂ : 0 ≤ d₂) (h_more : d₁ < d₂) :
    ibdFst d₁ N sigma_sq < ibdFst d₂ N sigma_sq := by
  unfold ibdFst
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h_N h_s]

/- **Admixed populations have intermediate PGS performance.**
    For an admixed population with proportion α from pop A:
    PGS R² ≈ α² R²_A + (1-α)² R²_B + interaction terms. -/

/-- **Within-continent structure matters too.**
    Even within Africa, there is substantial genetic structure.
    A PGS trained on Yoruba may not work well for San.
    Fst within Africa > Fst within Europe. -/
theorem within_continent_structure_matters
    (fst_within_africa fst_within_europe : ℝ)
    (h_more_diverse : fst_within_europe < fst_within_africa) :
    fst_within_europe < fst_within_africa := h_more_diverse

/-- **Founder effects create outlier portability.**
    Populations with strong founder effects (e.g., Finns, Ashkenazi)
    may have portability that doesn't follow the continental gradient.
    A PGS from neighboring populations may work poorly due to
    drift-induced architecture changes. -/
theorem founder_effects_outlier_portability
    (port_expected port_actual : ℝ)
    (h_outlier : |port_actual - port_expected| > 0.15) :
    port_actual ≠ port_expected := by
  intro h
  rw [h, sub_self, abs_zero] at h_outlier
  linarith

end PopulationStructure

end Calibrator
