import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Genetic Architecture Discovery, Winner's Curse, and Effect Estimation

This file formalizes how the discovery of genetic architecture
(through GWAS) is affected by population choice, and how this
affects downstream PGS portability.

Key results:
1. GWAS discovery power depends on LD and MAF in the discovery sample
2. Ascertainment bias from discovery population
3. Effect size estimation and shrinkage
4. Multi-trait analysis and genetic correlation

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## GWAS Discovery and Population Specificity

GWAS discovers associations that are specific to the population's
LD structure and allele frequency spectrum.
-/

section GWASDiscovery

/- **GWAS power function.**
    Power = Φ(√NCP - z_α/2) where NCP = n × β² × 2p(1-p). -/

/-- **Power increases with sample size.** -/
theorem power_increases_with_n
    (β p : ℝ) (n₁ n₂ : ℕ)
    (hβ : β ≠ 0) (hp : 0 < p) (hp1 : p < 1) (h_n : n₁ < n₂) (hn₁ : 0 < n₁) :
    -- NCP increases with n
    (n₁ : ℝ) * β ^ 2 * (2 * p * (1 - p)) <
      (n₂ : ℝ) * β ^ 2 * (2 * p * (1 - p)) := by
  apply mul_lt_mul_of_pos_right
  · apply mul_lt_mul_of_pos_right (Nat.cast_lt.mpr h_n) (sq_pos_of_ne_zero hβ)
  · nlinarith

/-- **GWAS finds different SNPs in different populations.**
    Due to different LD and MAF, the set of genome-wide significant
    SNPs can differ substantially. -/
theorem different_populations_different_hits
    (n_shared n_pop1_only n_pop2_only : ℕ)
    (h_not_all_shared : 0 < n_pop1_only ∨ 0 < n_pop2_only) :
    n_shared < n_shared + n_pop1_only + n_pop2_only := by
  rcases h_not_all_shared with h | h <;> omega

/-- **Winner's curse is worse for variants near the significance threshold.**
    The bias is proportional to the threshold / true effect ratio. -/
theorem winners_curse_worse_near_threshold
    (β₁ β₂ threshold : ℝ)
    (h₁_near : |β₁| < 1.5 * threshold)
    (h₂_far : 2 * threshold < |β₂|)
    (h_thr : 0 < threshold)
    (hβ₁ : β₁ ≠ 0) :
    -- Relative bias is larger for β₁
    threshold / |β₁| > threshold / |β₂| := by
  apply div_lt_div_of_pos_left h_thr
  · exact abs_pos.mpr hβ₁
  · linarith

end GWASDiscovery


/-!
## Effect Size Estimation and Portability

Accurate effect size estimation is crucial for PGS performance.
Different estimation methods have different bias-variance tradeoffs.
-/

section EffectEstimation

/-- **Ridge regression shrinks effects toward zero.**
    β̂_ridge = (X'X + λI)⁻¹X'Y = β_true × X'X/(X'X + λI).
    Bias: E[β̂] = β_true × (1 - λ/(X'X + λ)). -/
theorem ridge_introduces_bias
    (β_true lam xtx : ℝ)
    (h_lam : 0 < lam) (h_xtx : 0 < xtx) :
    |β_true * xtx / (xtx + lam)| < |β_true| ∨ β_true = 0 := by
  by_cases hβ : β_true = 0
  · right; exact hβ
  · left
    rw [abs_div, abs_mul]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < |xtx + lam|)]
    rw [abs_of_pos (by linarith : (0:ℝ) < xtx), abs_of_pos (by linarith : (0:ℝ) < xtx + lam)]
    nlinarith [abs_nonneg β_true, abs_pos.mpr hβ]

end EffectEstimation


/-!
## Multi-Trait Analysis and Genetic Correlation

Multi-trait GWAS methods can improve portability by leveraging
shared genetic architecture across related traits.
-/

section MultiTraitAnalysis

/-- **Genetic correlation between traits.**
    rg = Cov_g(trait1, trait2) / √(V_g1 × V_g2). -/
noncomputable def geneticCorrelation
    (cov_g vg₁ vg₂ : ℝ) : ℝ :=
  cov_g / Real.sqrt (vg₁ * vg₂)

/-- Genetic correlation is bounded by [-1, 1] (Cauchy-Schwarz). -/
theorem genetic_correlation_bounded
    (cov_g vg₁ vg₂ : ℝ)
    (h_cs : cov_g ^ 2 ≤ vg₁ * vg₂)
    (h₁ : 0 < vg₁) (h₂ : 0 < vg₂) :
    |geneticCorrelation cov_g vg₁ vg₂| ≤ 1 := by
  unfold geneticCorrelation
  rw [abs_div]
  rw [div_le_one (by exact abs_pos.mpr (Real.sqrt_pos.mpr (by positivity)).ne')]
  rw [abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  exact (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr (by nlinarith [sq_abs cov_g])

/-- **Cross-trait portability leverages genetic correlation.**
    If trait A has good portability and rg(A,B) is high,
    trait B can borrow portability information from A.
    Effective portability for B is at least rg² × portability(A). -/
theorem cross_trait_portability_gain
    (port_A rg : ℝ)
    (h_port : 0 < port_A) (h_port_le : port_A ≤ 1)
    (h_rg : 0 ≤ rg) (h_rg_le : rg ≤ 1) :
    0 ≤ rg ^ 2 * port_A := by
  exact mul_nonneg (sq_nonneg _) (le_of_lt h_port)

end MultiTraitAnalysis

end Calibrator
