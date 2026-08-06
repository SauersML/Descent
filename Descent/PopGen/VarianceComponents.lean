/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.TransportIdentities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Data.Matrix.Basic

assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.PopGen

open MeasureTheory

/-!
# Variance Components, Heritability, and PGS Performance

This file formalizes the relationship between variance components,
heritability estimation, and PGS performance across populations.

Key results:
1. GREML heritability estimation and its assumptions
2. h² SNP vs h² twin and the missing heritability problem
3. Variance component changes across populations
4. Heritability is population-specific
5. PGS R² ceiling from heritability

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat GREML estimation, missing heritability or the
population-specificity of h2. Sources for individual results, where they exist, are cited
at those results.
-/


/-!
## Heritability Definitions and Relationships

Different definitions of heritability lead to different ceilings
for PGS performance.
-/

section HeritabilityDefinitions

/-- **Narrow-sense heritability.**
    h² = V_A / V_P where V_A is additive genetic variance
    and V_P = V_A + V_D + V_I + V_E is total phenotypic variance. -/
noncomputable def narrowSenseH2 (V_A V_D V_I V_E : ℝ) : ℝ :=
  V_A / (V_A + V_D + V_I + V_E)

/-- **narrowSenseH2 where its denominator vanishes, named.** The guard `V_A + V_D + V_I + V_E` is
zero at `V_A = 0`, `V_D = 0`, `V_I = 0`, `V_E = 0`. A phenotype with no variance of any kind has
no heritability to report; the value returned reads as a trait with no genetic basis. Lean
returns `0` there rather than the value the modelled quantity takes, and no type error marks the
point. Consumers must require `V_A + V_D + V_I + V_E ≠ 0`. -/
theorem narrowSenseH2_at_va0vd0vi0ve0_is_junk :
    narrowSenseH2 0 0 0 0 = 0 := by
  unfold narrowSenseH2
  norm_num

/-- Narrow-sense h² is in [0, 1] for nonneg components. -/
theorem narrow_h2_in_unit (V_A V_D V_I V_E : ℝ)
    (hA : 0 ≤ V_A) (hD : 0 ≤ V_D) (hI : 0 ≤ V_I) (hE : 0 ≤ V_E)
    (h_total : 0 < V_A + V_D + V_I + V_E) :
    0 ≤ narrowSenseH2 V_A V_D V_I V_E ∧
      narrowSenseH2 V_A V_D V_I V_E ≤ 1 := by
  unfold narrowSenseH2
  constructor
  · exact div_nonneg hA (le_of_lt h_total)
  · rw [div_le_one h_total]; linarith

/-- **SNP heritability.**
    h²_SNP = V_A_tagged / V_P ≤ h²_narrow.
    Only the variance tagged by genotyped SNPs is captured. -/
noncomputable def snpH2 (V_A_tagged V_P : ℝ) : ℝ :=
  Descent.Core.ratio V_A_tagged V_P

/-- **snpH2 at zero V_P, named.** A trait with no phenotypic variance has no heritability to
estimate. Lean returns `0`, reporting a trait with no genetic basis rather than a trait with no
variance at all. Consumers must require `V_P ≠ 0`. -/
theorem snpH2_zero_vp_is_junk (V_A_tagged : ℝ) :
    snpH2 V_A_tagged 0 = 0 := by
  unfold snpH2 Descent.Core.ratio
  simp

/-- SNP heritability ≤ narrow-sense heritability. -/
theorem snp_h2_le_narrow_h2
    (V_A_tagged V_A_total V_D V_I V_E : ℝ)
    (h_tagged : V_A_tagged ≤ V_A_total)
    (h_total : 0 < V_A_total + V_D + V_I + V_E) :
    snpH2 V_A_tagged (V_A_total + V_D + V_I + V_E) ≤
      narrowSenseH2 V_A_total V_D V_I V_E := by
  unfold snpH2 narrowSenseH2 Descent.Core.ratio
  exact div_le_div_of_nonneg_right h_tagged (le_of_lt h_total)

/-- **The tagging gap, as an identity rather than an inequality.**

    `snp_h2_le_narrow_h2` says only that the SNP heritability is the smaller of
    the two. How much smaller is not an estimate: the difference is the untagged
    additive variance over the phenotypic variance, on the nose. The one-sided
    statement is the corollary obtained by discarding the sign information in
    the numerator, and with it goes the ability to say when the two coincide,
    which is now visible — never, unless the tagging is complete. -/
theorem narrow_h2_sub_snp_h2_eq
    (V_A_tagged V_A_total V_D V_I V_E : ℝ) :
    narrowSenseH2 V_A_total V_D V_I V_E -
        snpH2 V_A_tagged (V_A_total + V_D + V_I + V_E) =
      (V_A_total - V_A_tagged) / (V_A_total + V_D + V_I + V_E) := by
  unfold snpH2 narrowSenseH2 Descent.Core.ratio
  rw [div_sub_div_same]

/-- **The missing heritability gap.**
    h²_twin - h²_SNP > 0 for most traits. This is the "missing heritability".
    It sets an upper bound on what PGS can achieve with current genotyping.

    We derive the gap from the variance component model: h²_twin captures
    V_A_total / V_P while h²_SNP captures only V_A_tagged / V_P. The gap
    arises whenever some additive variance is not tagged by genotyped SNPs
    (V_A_untagged > 0). We prove that h²_twin - h²_SNP = V_A_untagged / V_P > 0,
    connecting the gap to the concrete untagged variance component.

    **Strengthened to the equality the docstring already claimed.** The
    conclusion was `0 < h2_twin - h2_snp`, one-sided, while the text above it
    asserted the identity. The identity is now in the statement and the
    positivity is its corollary, so a reader of the signature no longer has to
    take the numerator on trust. -/
theorem missing_heritability_gap
    (V_A_tagged V_A_untagged V_D V_I V_E : ℝ)
    (h_untagged_pos : 0 < V_A_untagged)
    (h_total : 0 < V_A_tagged + V_A_untagged + V_D + V_I + V_E) :
    let V_P := V_A_tagged + V_A_untagged + V_D + V_I + V_E
    let h2_twin := (V_A_tagged + V_A_untagged) / V_P
    let h2_snp := V_A_tagged / V_P
    h2_twin - h2_snp = V_A_untagged / V_P ∧ 0 < h2_twin - h2_snp := by
  simp only
  have h_gap :
      (V_A_tagged + V_A_untagged) / (V_A_tagged + V_A_untagged + V_D + V_I + V_E) -
        V_A_tagged / (V_A_tagged + V_A_untagged + V_D + V_I + V_E) =
      V_A_untagged / (V_A_tagged + V_A_untagged + V_D + V_I + V_E) := by
    rw [div_sub_div_same]
    congr 1
    ring
  refine ⟨h_gap, ?_⟩
  rw [h_gap]
  exact div_pos h_untagged_pos h_total

end HeritabilityDefinitions


/-!
## Population-Specific Heritability

Heritability is NOT a fixed property of a trait — it depends on
allele frequencies, LD structure, and environmental variance
in the specific population.
-/

section PopulationSpecificH2

/-- **Additive variance under LINKAGE EQUILIBRIUM** — the qualifier is load-bearing and was
    missing.

    `V_A = Σᵢ 2pᵢ(1-pᵢ)αᵢ²` drops the LD cross term `Σᵢ≠ⱼ 4·αᵢ·αⱼ·D_ij`, so it is correct only
    at `D = 0` and is stated unconditionally. **The sign of the error flips with the sign of
    the effect product**, which is why no constant repairs it: at `p = 1/2`, `D = 1/8`, exact
    rationals, `α = (1,1)` gives `1` against a true `3/2` (ratio `2/3`), while `α = (1,-1)`
    gives `1` against a true `1/2` (ratio `2`).

    Simulation at `n = 400k` reproduces both: `1.4975` against the LD-inclusive `1.5`, with a
    `D = 0` control at `0.9974` against `1.0`.

    Empirical status: **VALIDATED at linkage equilibrium**; the unconditional reading is
    **FALSIFIED** (`validation/empirical/ldsc_diff/`). -/
noncomputable def additiveVariance
    {m : ℕ} (p : Fin m → ℝ) (α : Fin m → ℝ) : ℝ :=
  ∑ i, 2 * p i * (1 - p i) * (α i) ^ 2

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem additiveVariance_at_reference_point :
    additiveVariance (![1, 3] : Fin 2 → ℝ) (![2, 5] : Fin 2 → ℝ) = -300 := by
  norm_num [additiveVariance, Fin.sum_univ_two]


/-- Additive variance is nonneg. -/
theorem additive_variance_nonneg
    {m : ℕ} (p : Fin m → ℝ) (α : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ additiveVariance p α := by
  unfold additiveVariance
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hp i)
    · linarith [hp1 i]
  · exact sq_nonneg _

/-! ### Why the variance components are the easy summaries

`additiveVariance` is a quadratic — hence smooth — functional of the effect
vector, and so are `narrowSenseH2`, `snpH2` and every component appearing in
the ceiling results below. Smooth functionals of this kind are estimable at
polynomial rates, and the sample-size laws in `Descent.Decision.PowerAnalysis` are
the right shape for them.

That is a property of these particular summaries and does not extend to the
whole file's subject matter. A summary of the same effect vector that is not
smooth — the mean absolute effect, or an inverse-kurtosis polygenicity measure
— may carry a logarithmic benchmark rather than a power of `q` in a specified
Gaussian-sequence model; see
`Descent.PopGen.PolygenicArchitecture`, section `NonsmoothSummaries`. The
distinction is invisible in the formulas, which look equally elementary, and it
is worth stating here because the two kinds of quantity are routinely reported
side by side in the same table with the same standard errors. -/

/-- **Frequency change affects additive variance.**
    When MAF changes from p to p' at a single locus,
    the contribution to V_A changes.

    The two premises that carry this are `h_freq : p₁ ≠ p₂` and
    `h_sum : p₁ + p₂ ≠ 1`, and the second is not optional: `2p(1-p)` is
    symmetric about `1/2`, so a reflected pair `p₂ = 1 - p₁` gives *equal*
    additive variance at different frequencies. Four `0 < p < 1` premises used
    to sit alongside them; a scan of the kernel-accepted proof term found that
    none of the four occurs in the proof — the factorization
    `(p₁ - p₂)(1 - (p₁ + p₂)) = 0` needs no range at all — and they have been
    removed rather than left to suggest the range is what makes this work. -/
theorem frequency_change_affects_va
    (p₁ p₂ α : ℝ)
    (h_freq : p₁ ≠ p₂) (h_α : α ≠ 0)
    (h_sum : p₁ + p₂ ≠ 1) :
    2 * p₁ * (1 - p₁) * α ^ 2 ≠ 2 * p₂ * (1 - p₂) * α ^ 2 := by
  intro h
  have h_sq : 0 < α ^ 2 := sq_pos_of_ne_zero h_α
  have h_eq : 2 * p₁ * (1 - p₁) = 2 * p₂ * (1 - p₂) :=
    mul_right_cancel₀ h_sq.ne' h
  -- From 2p₁(1-p₁) = 2p₂(1-p₂), get (p₁-p₂)(1-(p₁+p₂)) = 0
  have : (p₁ - p₂) * (1 - (p₁ + p₂)) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact h_freq (sub_eq_zero.mp h)
  · exact h_sum (by linarith)

/-- **Environmental variance heterogeneity across populations.**
    If Ve differs, h² differs even with identical genetic architecture. -/
theorem env_variance_changes_h2
    (V_A Ve₁ Ve₂ : ℝ)
    (hVA : 0 < V_A) (hVe₁ : 0 < Ve₁)
    (h_diff : Ve₁ < Ve₂) :
    V_A / (V_A + Ve₂) < V_A / (V_A + Ve₁) := by
  exact div_lt_div_of_pos_left hVA (by linarith) (by linarith)

/-- **GxE creates population-specific heritability.**
    Gene-environment interaction means the genetic effect depends
    on the environment. In different environments, V_A changes. -/
theorem gxe_changes_heritability
    (V_A_env1 V_A_env2 V_E : ℝ)
    (h_diff : V_A_env1 ≠ V_A_env2) (h_E : 0 < V_E)
    (h1 : 0 < V_A_env1) (h2 : 0 < V_A_env2) :
    V_A_env1 / (V_A_env1 + V_E) ≠ V_A_env2 / (V_A_env2 + V_E) := by
  intro h
  have h_d1 : V_A_env1 + V_E ≠ 0 := by linarith
  have h_d2 : V_A_env2 + V_E ≠ 0 := by linarith
  have h_eq : V_A_env1 * (V_A_env2 + V_E) = V_A_env2 * (V_A_env1 + V_E) := by
    field_simp at h
    linarith
  have : V_A_env1 = V_A_env2 := by nlinarith
  exact h_diff this

end PopulationSpecificH2


/-!
## PGS R² Ceiling

The maximum achievable PGS R² is bounded by the heritability
and the GWAS sample size.
-/

section PGSCeiling

/-- **PGS R² ceiling from heritability.**
    R²_PGS ≤ h²_SNP. No PGS can explain more variance than what's
    genetically tagged. The PGS explains a fraction f of tagged
    additive variance, so R²_PGS = f × h²_SNP ≤ h²_SNP. -/
theorem mul_le_self_of_factor_le_one
    (h2_snp f : ℝ)
    (h_h2 : 0 < h2_snp)
    (h_f_le : f ≤ 1) :
    h2_snp * f ≤ h2_snp := by
  exact mul_le_of_le_one_right (le_of_lt h_h2) h_f_le

/-- **The ceiling is attained only by a complete PGS.**

    The two-sided companion to `mul_le_self_of_factor_le_one`: the ceiling `h²_SNP`
    is reached exactly when the fraction of tagged additive variance the score
    captures is one. A bound with no attainment condition cannot distinguish a
    ceiling that is approached from one that is unreachable; this says which
    this is. -/
theorem mul_eq_self_iff_eq_one
    (h2_snp f : ℝ) (h_h2 : 0 < h2_snp) :
    h2_snp * f = h2_snp ↔ f = 1 := by
  constructor
  · intro h
    have h' : h2_snp * f = h2_snp * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel₀ (ne_of_gt h_h2) h'
  · intro h
    rw [h, mul_one]

/-- **PGS R² ceiling from GWAS power.**
    R²_PGS ≤ h²_SNP × (1 - (1-power)^m)
    where power is per-SNP GWAS power and m is number of causal SNPs.
    With finite sample size, not all SNPs are discovered. -/
theorem mul_le_self_of_fraction_le_one
    (h2_snp power_fraction : ℝ)
    (h_h2 : 0 < h2_snp)
    (h_power_le : power_fraction ≤ 1) :
    h2_snp * power_fraction ≤ h2_snp := by
  exact mul_le_of_le_one_right (le_of_lt h_h2) h_power_le

/-- **Portability further reduces the ceiling.**
    R²_PGS_target ≤ h²_SNP × power_fraction × portability_ratio. -/
theorem mul_mul_le_self_of_le_one_of_le_one
    (h2_snp power_frac port_ratio : ℝ)
    (h_h2 : 0 < h2_snp) (h_port : 0 < port_ratio)
    (h_power_le : power_frac ≤ 1) (h_port_le : port_ratio ≤ 1) :
    h2_snp * power_frac * port_ratio ≤ h2_snp := by
  calc h2_snp * power_frac * port_ratio
      ≤ h2_snp * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h_power_le (le_of_lt h_h2)
        · exact h_port_le
        · exact le_of_lt h_port
        · exact mul_nonneg (le_of_lt h_h2) (by linarith)
    _ = h2_snp := by ring

/-- **The three-way ceiling decomposition.**
    R²_target ≤ h² × (GWAS power) × (portability ratio).
    Each factor is ≤ 1, and the product can be very small. -/
theorem three_way_ceiling
    (h2 gwas_power port_ratio target_r2 : ℝ)
    (h_h2_le : h2 ≤ 1) (h_power_le : gwas_power ≤ 1)
    (h_port_le : port_ratio ≤ 1)
    (h_h2_nn : 0 ≤ h2) (h_power_nn : 0 ≤ gwas_power)
    (h_bound : target_r2 ≤ h2 * gwas_power * port_ratio) :
    target_r2 ≤ 1 := by
  have : h2 * gwas_power * port_ratio ≤ 1 := by
    calc h2 * gwas_power * port_ratio
        ≤ 1 * 1 * 1 := by nlinarith [mul_nonneg h_h2_nn h_power_nn]
      _ = 1 := by ring
  linarith

end PGSCeiling


/-!
## GREML Estimation and Bias

GREML (Genomic REML) estimates h² from GRM. Its accuracy depends
on LD and population structure assumptions.
-/

section GREML

/-- **A quantity plus a nonzero offset differs from the quantity.**

    The name says what is proved. The GREML reading — that using linkage-disequilibrium
    structure from one population to estimate heritability in another leaves a nonzero bias —
    is the reason someone would supply `h_ld_nonzero`, and it is not derived here: no genomic
    relationship matrix, no phenotypic covariance and no estimator appears below. That the bias
    is nonzero is the hypothesis, so this cannot be cited as evidence that GREML is
    LD-sensitive. -/
theorem add_ne_self_of_ne_zero
    (h2_estimated h2_true ld_bias : ℝ)
    (h_bias : h2_estimated = h2_true + ld_bias)
    (h_ld_nonzero : ld_bias ≠ 0) :
    h2_estimated ≠ h2_true := by
  rw [h_bias]; intro h; apply h_ld_nonzero; linarith

/-- **GREML underestimates h² when causal variants are poorly tagged.**
    The true SNP heritability is `V_A / V_P`, while GREML only captures
    the tagged additive variance `(mean_tag_r2 * V_A) / V_P`. If tagging is
    imperfect, the underestimation gap is exactly
    `((1 - mean_tag_r2) * V_A) / V_P > 0`. -/
theorem greml_underestimates_with_poor_tagging
    (V_A V_P mean_tag_r2 : ℝ)
    (h_imperfect : mean_tag_r2 < 1)
    (h_VA_pos : 0 < V_A) (h_VP_pos : 0 < V_P) :
    let h2_true := V_A / V_P
    let h2_greml := (mean_tag_r2 * V_A) / V_P
    h2_true - h2_greml = ((1 - mean_tag_r2) * V_A) / V_P ∧
      0 < h2_true - h2_greml := by
  simp only
  rw [← sub_div]
  have h_gap :
      V_A - mean_tag_r2 * V_A = (1 - mean_tag_r2) * V_A := by
    ring
  rw [h_gap]
  constructor
  · rfl
  · apply div_pos
    · nlinarith
    · exact h_VP_pos

/-- **Population structure inflates GREML h² estimate.**
    Cryptic stratification in the GWAS sample creates a positive bias
    in the GRM-based h² estimate.

    **Model:** GREML estimates h² = V_A / V_P by fitting a linear mixed
    model with a GRM kernel. When there is population structure, the GRM
    captures both true genetic relatedness and stratification-induced
    correlations. The GREML estimate becomes:
      h²_GREML = (V_A + V_strat) / (V_A + V_strat + V_E)
    while the true h² is:
      h²_true = V_A / (V_A + V_strat + V_E)

    We derive: h²_GREML > h²_true whenever V_strat > 0, because
    (V_A + V_strat)/V_P > V_A/V_P when V_P > 0.

    **Strengthened from a direction to a magnitude.** The inflation is not
    merely positive; it equals the stratification variance as a fraction of the
    phenotypic variance, `V_strat / V_P`, with no residual term. That is what
    makes the bias correctable in principle from an estimate of `V_strat`
    alone, which the one-sided form could not support. -/
theorem stratification_inflates_greml
    (V_A V_strat V_E : ℝ)
    (h_strat_pos : 0 < V_strat)
    (h_total : 0 < V_A + V_strat + V_E) :
    let V_P := V_A + V_strat + V_E
    let h2_true := V_A / V_P
    let h2_greml := (V_A + V_strat) / V_P
    h2_greml - h2_true = V_strat / V_P ∧ h2_true < h2_greml := by
  simp only
  have h_gap : (V_A + V_strat) / (V_A + V_strat + V_E) -
      V_A / (V_A + V_strat + V_E) = V_strat / (V_A + V_strat + V_E) := by
    rw [div_sub_div_same]
    congr 1
    ring
  refine ⟨h_gap, ?_⟩
  exact div_lt_div_of_pos_right (by linarith) h_total

end GREML


/-!
## Liability Scale Conversion

For binary traits, h² on the observed scale differs from h² on
the liability scale. Conversion depends on prevalence.
-/

section LiabilityScale

/-- **Observed-to-liability scale conversion (Dempster-Lee-Risch).**

    **Derivation of the Dempster-Lee-Risch conversion:**

    On the liability scale, assume Y ~ N(0, 1). Disease occurs when Y > T,
    where T = Φ⁻¹(1-K) and K = prevalence. This is the "liability threshold
    model."

    The key question: how does a unit change in liability translate to a
    change in disease risk on the observed (binary 0/1) scale?

    1. The observed (binary) heritability h²_obs measures variance explained
       on the 0/1 disease scale.

    2. The liability heritability h²_liab measures variance explained on the
       continuous latent liability scale.

    3. The relationship between the two involves the "ascertainment correction"
       factor. At the threshold T, the standard normal density is z = φ(T).
       A small shift δ in mean liability changes disease risk by:
         ΔP(disease) ≈ z × δ

    4. Variance on observed scale vs liability scale:
       - A genetic variant explaining variance σ² on the liability scale
         explains variance ≈ z² × σ² / (K(1-K)) on the observed scale
         (after accounting for the Bernoulli variance K(1-K) of the binary outcome).

    5. Therefore: h²_obs = h²_liab × z² / (K(1-K))

    6. Rearranging: **h²_liab = h²_obs × K(1-K) / z²**

    The factor K(1-K)/z² is the inverse of the "ascertainment correction,"
    which accounts for the nonlinear mapping between the continuous liability
    and binary disease status. For rare diseases (small K), the threshold T
    is far in the tail, z = φ(T) is small, and z² << K(1-K), so
    h²_liab >> h²_obs.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk8.py`,
    `test_liability_scale_h2`). The test is whether the transform RECOVERS the
    liability heritability the simulation was built with. Three million
    individuals per cell: a liability with known `h2` is dichotomised at
    prevalence `K`, the observed-scale heritability is fitted by regression on
    the 0/1 outcome, and the transform is applied to it.

      h2_liab   K       recovered   built with sems
      0.5       0.05      0.50157     0.50000     1.92
      0.5       0.20      0.49912     0.50000     1.07
      0.3       0.10      0.29998     0.30000     0.04

    The control is that the same regression recovers `h2` when the outcome is
    the liability itself rather than its dichotomy; it passes, so the
    observed-scale fit is sound before the transform is asked to correct it.

    Power: `K` moves by a factor of four across the design, and `z^2` with it,
    so a transform missing the prevalence factor would separate. -/
noncomputable def liabilityScaleH2
    (h2_observed prevalence z_height : ℝ) : ℝ :=
  h2_observed * prevalence * (1 - prevalence) / z_height ^ 2

/-- **liabilityScaleH2 at zero z_height, named.** A zero threshold height makes the
observed-to-liability conversion undefined. Lean returns `0`, reporting no heritability on the
liability scale for any observed-scale estimate whatsoever. Consumers must require
`z_height ≠ 0`. -/
theorem liabilityScaleH2_zero_zheight_is_junk (h2_observed prevalence : ℝ) :
    liabilityScaleH2 h2_observed prevalence 0 = 0 := by
  unfold liabilityScaleH2
  simp

/-- **Liability h² is larger than observed h² for rare diseases.**
    When prevalence K is small, K(1-K)/z² > 1 because z is large
    (the threshold is far in the tail). -/
theorem liability_h2_larger_for_rare
    (h2_observed prevalence z_height : ℝ)
    (h_obs_pos : 0 < h2_observed)
    (h_conversion_gt_one : prevalence * (1 - prevalence) / z_height ^ 2 > 1) :
    h2_observed < liabilityScaleH2 h2_observed prevalence z_height := by
  unfold liabilityScaleH2
  rw [show h2_observed * prevalence * (1 - prevalence) / z_height ^ 2 =
    h2_observed * (prevalence * (1 - prevalence) / z_height ^ 2) by ring]
  exact lt_mul_of_one_lt_right h_obs_pos h_conversion_gt_one

/-- **Prevalence-dependent h² creates portability confusion.**
    Two populations with the same genetic architecture but different
    prevalence have different observed h², which can be mistaken
    for a portability effect. -/
theorem prevalence_confounds_h2_portability
    (K₁ K₂ z₁ z₂ : ℝ)
    (h_diff_ratio : K₁ * (1 - K₁) / z₁ ^ 2 ≠ K₂ * (1 - K₂) / z₂ ^ 2) :
    -- Different observed h² even with same genetic architecture
    liabilityScaleH2 1 K₁ z₁ ≠ liabilityScaleH2 1 K₂ z₂ := by
  unfold liabilityScaleH2
  simp
  exact h_diff_ratio

end LiabilityScale

/-- **`additiveVariance` is a sum over loci and therefore assumes linkage equilibrium**;
this theorem pins its `2 p (1 - p)` to `ploidy` and says nothing about that assumption.

The qualifier is load-bearing. The per-locus sum drops the cross term
`Σ_{i≠j} 4 α_i α_j D_ij`, and the sign of the resulting error flips with the sign of the
effect product, so no constant repairs it: at `p = 1/2`, `D = 1/8`, `α = (1,1)` gives `1`
against a true `3/2`, while `α = (1,-1)` gives `1` against a true `1/2`. The
unconditional reading is FALSIFIED (`VarianceComponents.additiveVariance`). -/
theorem additiveVariance_uses_hwe {m : ℕ} (p α : Fin m → ℝ) :
    PopGen.additiveVariance p α = ∑ i, Descent.Core.hweHeterozygosity (p i) * (α i) ^ 2 := by
  unfold PopGen.additiveVariance Descent.Core.hweHeterozygosity Descent.Core.ploidy; ring_nf

end Descent.PopGen
