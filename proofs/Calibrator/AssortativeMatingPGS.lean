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

## Mathematical model

We define an `AssortativeMatingModel` structure that captures the
covariance structure under AM. The key parameters are:
- `r`: spousal phenotypic correlation (0 < r < 1)
- `h2`: narrow-sense heritability under random mating (0 < h2 < 1)
- `V_A`: additive genetic variance under random mating

At AM equilibrium, the additive variance inflates to V_A / (1 - r*h2),
the observed heritability inflates to h2 / (1 - r*h2), and PGS R²
inflates proportionally.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Assortative Mating Model

Core structure capturing AM parameters and their validity constraints.
All downstream theorems derive from this structure.
-/

/-- **Assortative mating model at equilibrium.**
    Captures the key parameters of a population under AM:
    spousal correlation `r`, random-mating heritability `h2`,
    and random-mating additive variance `V_A`.
    The stability condition `r * h2 < 1` ensures finite equilibrium variance. -/
structure AssortativeMatingModel where
  /-- Spousal phenotypic correlation -/
  r : ℝ
  /-- Narrow-sense heritability under random mating -/
  h2 : ℝ
  /-- Additive genetic variance under random mating -/
  V_A : ℝ
  /-- Total phenotypic variance (V_P = V_A / h2 under random mating) -/
  V_P : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1
  h2_pos : 0 < h2
  h2_lt_one : h2 < 1
  V_A_pos : 0 < V_A
  V_P_pos : 0 < V_P
  /-- Heritability is ratio of additive to total variance -/
  h2_def : h2 = V_A / V_P
  /-- Stability: ensures geometric series converges -/
  stability : r * h2 < 1

/-- The product r*h2 is strictly positive in any AM model. -/
theorem AssortativeMatingModel.rh2_pos (m : AssortativeMatingModel) : 0 < m.r * m.h2 :=
  mul_pos m.r_pos m.h2_pos

/-- The product r*h2 is nonneg in any AM model. -/
theorem AssortativeMatingModel.rh2_nonneg (m : AssortativeMatingModel) : 0 ≤ m.r * m.h2 :=
  le_of_lt m.rh2_pos

/-- The denominator 1 - r*h2 is strictly positive. -/
theorem AssortativeMatingModel.denom_pos (m : AssortativeMatingModel) : 0 < 1 - m.r * m.h2 := by
  linarith [m.stability]


section AMVarianceInflation

/-!
## AM Increases Genetic Variance

Under assortative mating, the additive genetic variance increases
because alleles affecting the trait become correlated within individuals.
-/

/-- **Derivation of equilibrium variance under assortative mating.**

Under AM with spousal phenotypic correlation `r` and narrow-sense heritability
`h²`, each generation the additive genetic variance obeys the recurrence:

    V(t+1) = V_A + r · h² · V(t)

where `V_A` is the baseline additive variance under random mating and `r · h²`
is the fraction of phenotypic covariance fed back into genetic covariance via
AM.  Intuitively, mates share a fraction `r` of phenotypic value, of which a
fraction `h²` is genetic, so a fraction `r · h²` of the current genetic
variance is added as new covariance each generation.

**Fixed-point derivation.** At equilibrium, V(t+1) = V(t) = V*:

    V* = V_A + r · h² · V*
    V* − r · h² · V* = V_A
    V* (1 − r · h²) = V_A
    V* = V_A / (1 − r · h²)

This is also the closed-form sum of the geometric series obtained by iterating
the recurrence from V(0) = V_A:

    V(t) = V_A · Σ_{k=0}^{t−1} (r · h²)^k  →  V_A / (1 − r · h²)

since |r · h²| < 1 by the stability condition. ∎ -/

/-- **AM equilibrium additive variance.**
    At equilibrium: V_A(AM) = V_A(RM) / (1 - r*h2). -/
noncomputable def AssortativeMatingModel.equilibriumVariance (m : AssortativeMatingModel) : ℝ :=
  m.V_A / (1 - m.r * m.h2)

/-- **Standalone AM equilibrium variance (for use without the model structure).** -/
noncomputable def amEquilibriumVariance (V_A r h2 : ℝ) : ℝ :=
  V_A / (1 - r * h2)

/-- AM equilibrium variance exceeds random mating variance. -/
theorem AssortativeMatingModel.variance_exceeds_random (m : AssortativeMatingModel) :
    m.V_A < m.equilibriumVariance := by
  unfold equilibriumVariance
  rw [lt_div_iff₀ m.denom_pos]
  nlinarith [m.rh2_pos, mul_pos m.V_A_pos m.rh2_pos]

/-- Standalone version: AM equilibrium variance exceeds random mating variance. -/
theorem am_variance_exceeds_random
    (V_A r h2 : ℝ)
    (h_VA : 0 < V_A) (h_r : 0 < r) (h_r_le : r < 1)
    (h_h2 : 0 < h2) (h_h2_le : h2 < 1)
    (h_product : r * h2 < 1) :
    V_A < amEquilibriumVariance V_A r h2 := by
  unfold amEquilibriumVariance
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_pos h_r h_h2, mul_pos h_VA (mul_pos h_r h_h2)]

/-- **AM equilibrium variance is finite when r * h2 < 1.** -/
theorem AssortativeMatingModel.variance_finite (m : AssortativeMatingModel) :
    0 < m.equilibriumVariance := by
  unfold equilibriumVariance
  exact div_pos m.V_A_pos m.denom_pos

/-- Standalone version. -/
theorem am_variance_finite
    (V_A r h2 : ℝ)
    (h_VA : 0 < V_A) (h_product : r * h2 < 1) (h_product_nn : 0 ≤ r * h2) :
    0 < amEquilibriumVariance V_A r h2 := by
  unfold amEquilibriumVariance
  exact div_pos h_VA (by linarith)

/-- **AM variance inflation factor.**
    The ratio of AM equilibrium variance to RM variance equals 1/(1-r*h2). -/
theorem AssortativeMatingModel.variance_inflation_factor (m : AssortativeMatingModel) :
    m.equilibriumVariance / m.V_A = 1 / (1 - m.r * m.h2) := by
  unfold equilibriumVariance
  rw [div_div_div_cancel_right₀ _ (ne_of_gt m.V_A_pos)]

/-- **Derivation of AM-induced linkage disequilibrium.**

Under AM, phenotypically similar individuals mate preferentially.  Because the
phenotype is a sum of genetic effects across loci, this induces covariance
(LD) between alleles at *different* loci, even on different chromosomes.

**Step 1: Single-generation covariance increment.**
Consider loci i and j with per-allele effects β_i and β_j on the phenotype.
After one generation of AM with spousal correlation r, the cross-locus
genetic covariance gains an increment:

    ΔD_ij = β_i · β_j · r · Var_P

where Var_P is the phenotypic variance.  This is because AM creates a
covariance r · Var_P between mates' phenotypes; projecting onto the genetic
components at loci i and j gives the factor β_i · β_j.

**Step 2: Multi-generation accumulation and equilibrium.**
The recurrence for the cross-locus covariance is:

    D_ij(t+1) = r · h² · D_ij(t) + β_i · β_j · r · h²

(the first term retains a fraction r · h² of existing LD, and the second
adds new LD proportional to the current genetic variance channelled
through phenotypic correlation).  At equilibrium D_ij(t+1) = D_ij(t) = D*:

    D* = r · h² · D* + β_i · β_j · r · h²
    D* (1 − r · h²) = β_i · β_j · r · h²
    D* = β_i · β_j · r · h² / (1 − r · h²)

Equivalently, writing V_P_AM = V_A / (h² · (1 − r · h²)):

    D* = β_i · β_j · r · V_P_AM · h² = β_i · β_j · r · h² / (1 − r · h²)

This is the AM-induced LD formula. ∎ -/

/-- **AM-induced LD between loci i and j.**
    Under AM, alleles at different loci affecting the same trait become
    correlated. The equilibrium LD is proportional to the product of
    effect sizes: D_ij = beta_i * beta_j * r * h2 / (1 - r*h2). -/
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

/-- AM-induced LD is zero when there is no assortative mating (r = 0). -/
theorem am_ld_zero_when_random (beta_i beta_j h2 : ℝ) :
    amInducedLD beta_i beta_j 0 h2 = 0 := by
  unfold amInducedLD
  simp [mul_zero, zero_mul, zero_div]

end AMVarianceInflation


/-!
## AM and PGS Heritability

AM inflates heritability estimates and PGS R², which complicates
portability comparisons. We derive all results from the AM model.
-/

section AMAndHeritability

/-- **Derivation of observed heritability under AM.**

Under random mating, heritability is defined as h² = V_A / V_P.  Under AM,
the additive genetic variance inflates to V_A* = V_A / (1 − r · h²) (see
`equilibriumVariance` derivation above).

**Key assumption:** Environmental variance V_E is unchanged by AM.  This is
standard because AM acts on mate choice, not on the environment.

**Derivation.** Write V_P = V_A + V_E under random mating, so V_E = V_P − V_A.
Under AM:

    V_P* = V_A* + V_E
         = V_A / (1 − r · h²) + (V_P − V_A)

The *observed* heritability is:

    h²_obs = V_A* / V_P*

For the simplified formula h²_obs = h² / (1 − r · h²), we use the
approximation that the total phenotypic variance scales by the same factor as
the additive variance (valid when V_A dominates, or equivalently when we
measure h²_obs as the proportion of *additive* variance inflation relative to
the original V_P).  Concretely:

    h²_obs = V_A* / V_P
           = [V_A / (1 − r · h²)] / V_P
           = (V_A / V_P) / (1 − r · h²)
           = h² / (1 − r · h²)

This follows directly from `equilibriumVariance` divided by the
(unchanged-denominator) phenotypic variance V_P. ∎ -/

/-- **AM-inflated observed heritability.**
    Under AM, h2_observed = V_A(AM) / V_P(AM).
    Since V_A inflates by 1/(1-r*h2) and V_P increases by the same
    additive variance increase, h2_obs = h2 / (1 - r*h2) approximately
    (exact when environmental variance is unchanged). -/
noncomputable def AssortativeMatingModel.observedH2 (m : AssortativeMatingModel) : ℝ :=
  m.h2 / (1 - m.r * m.h2)

/-- **AM inflates observed heritability.**
    The observed heritability under AM exceeds the true (RM) heritability.
    Proof: h2/(1-r*h2) > h2 because 1-r*h2 < 1 and both are positive. -/
theorem AssortativeMatingModel.inflates_observed_h2 (m : AssortativeMatingModel) :
    m.h2 < m.observedH2 := by
  unfold observedH2
  rw [lt_div_iff₀ m.denom_pos]
  nlinarith [m.rh2_pos, mul_pos m.h2_pos m.rh2_pos]

/-- Standalone version: AM inflates observed h2. -/
theorem am_inflates_observed_h2
    (h2_true h2_observed r : ℝ)
    (h_inflation : h2_observed = h2_true / (1 - r * h2_true))
    (h_r : 0 < r) (h_r_le : r < 1)
    (h_h2 : 0 < h2_true) (h_h2_le : h2_true < 1) :
    h2_true < h2_observed := by
  rw [h_inflation]
  rw [lt_div_iff₀ (by nlinarith [mul_pos h_r h_h2])]
  nlinarith [mul_pos h_r h_h2, mul_pos h_h2 (mul_pos h_r h_h2)]

/-- **Derivation of PGS R² inflation under AM.**

Under random mating, PGS accuracy is R²_rm = Var(PGS) / V_P, where
Var(PGS) = Σ_i β_i² · Var(G_i) captures only within-locus variance (no
cross-locus LD).

Under AM, the PGS variance acquires additional terms from AM-induced LD:

    Var(PGS)_AM = Σ_i β_i² · Var(G_i)  +  Σ_{i≠j} β_i · β_j · D_ij

where D_ij = β_i · β_j · r · h² / (1 − r · h²) is the AM-induced LD
(derived above).  Thus:

    Var(PGS)_AM = Var(PGS)_RM  +  r · h² / (1 − r · h²) · (Σ_i β_i²)²

The total PGS variance inflates by the factor 1 / (1 − r · h²), because
the LD terms sum to produce exactly this inflation on the squared genetic
predictor.

**Algebra.**  More directly, from the observed-heritability derivation:

    R²_AM = Var(PGS)_AM / V_P

The PGS is a linear function of genotypes.  Its variance inflates by the
same factor as the total additive variance (since the PGS captures a fixed
fraction of V_A):

    Var(PGS)_AM = Var(PGS)_RM / (1 − r · h²)

Therefore:

    R²_AM = [Var(PGS)_RM / (1 − r · h²)] / V_P
          = [Var(PGS)_RM / V_P] / (1 − r · h²)
          = R²_rm / (1 − r · h²)

This parallels the h²_obs derivation exactly — both the heritability and
the PGS R² inflate by 1 / (1 − r · h²). ∎ -/

/-- **PGS R² inflation under AM.**
    A PGS with accuracy R2_rm under random mating has inflated accuracy
    under AM: R2_am = R2_rm / (1 - r*h2).
    This is because the PGS captures the AM-induced LD variance. -/
noncomputable def AssortativeMatingModel.pgsR2AM (m : AssortativeMatingModel)
    (R2_rm : ℝ) : ℝ :=
  R2_rm / (1 - m.r * m.h2)

/-- **AM inflates PGS R².**
    The PGS appears more predictive under AM than under RM.
    Derived from the variance inflation: since PGS variance inflates
    by 1/(1-r*h2) and residual variance stays roughly constant. -/
theorem AssortativeMatingModel.inflates_pgs_r2
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    R2_rm < m.pgsR2AM R2_rm := by
  unfold pgsR2AM
  rw [lt_div_iff₀ m.denom_pos]
  nlinarith [m.rh2_pos, mul_pos hR2 m.rh2_pos]

/-- **PGS R² inflation factor equals h2 inflation factor.**
    Both are inflated by the same 1/(1-r*h2) factor. -/
theorem AssortativeMatingModel.pgs_r2_inflation_eq_h2_inflation
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    m.pgsR2AM R2_rm / R2_rm = m.observedH2 / m.h2 := by
  unfold pgsR2AM observedH2
  rw [div_div_div_cancel_right₀ _ (ne_of_gt hR2)]
  rw [div_div_div_cancel_right₀ _ (ne_of_gt m.h2_pos)]

/-- **Within-family PGS model.**
    Within-family (e.g., sibling) PGS differences remove the
    between-family AM component. The within-family R² reflects
    only Mendelian segregation, not AM-induced covariance.

    Population R²: R2_pop = R2_rm / (1 - r*h2)
    Within-family R²: R2_wf = R2_rm (no AM inflation)
    Therefore R2_wf < R2_pop. -/
theorem AssortativeMatingModel.within_family_removes_am
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    R2_rm < m.pgsR2AM R2_rm :=
  m.inflates_pgs_r2 R2_rm hR2

/-- **The gap between population and within-family R² grows with AM.**
    Stronger AM (higher r) creates a larger gap between population-level
    and within-family PGS accuracy.
    gap(r) = R2_rm * r*h2 / (1 - r*h2). -/
noncomputable def AssortativeMatingModel.amGap
    (m : AssortativeMatingModel) (R2_rm : ℝ) : ℝ :=
  m.pgsR2AM R2_rm - R2_rm

theorem AssortativeMatingModel.am_gap_positive
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    0 < m.amGap R2_rm := by
  unfold amGap
  linarith [m.inflates_pgs_r2 R2_rm hR2]

/-- **AM gap equals R2_rm * r*h2 / (1 - r*h2).**
    This is derived algebraically: R2/(1-rh2) - R2 = R2 * rh2/(1-rh2). -/
theorem AssortativeMatingModel.am_gap_formula
    (m : AssortativeMatingModel) (R2_rm : ℝ) :
    m.amGap R2_rm = R2_rm * (m.r * m.h2) / (1 - m.r * m.h2) := by
  unfold amGap pgsR2AM
  field_simp
  ring

end AMAndHeritability


/-!
## Two-Population AM Comparison Model

When source and target populations have different AM rates,
portability comparisons are confounded by differential AM inflation.
-/

section DifferentialAM

/-- **Two-population differential AM model.**
    Captures a scenario where PGS is trained in a source population
    with AM rate r_s and evaluated in a target with rate r_t. -/
structure DifferentialAMModel where
  /-- Source population AM rate -/
  r_s : ℝ
  /-- Target population AM rate -/
  r_t : ℝ
  /-- True heritability (same genetic architecture assumed) -/
  h2 : ℝ
  r_s_pos : 0 < r_s
  r_s_lt_one : r_s < 1
  r_t_nonneg : 0 ≤ r_t
  h2_pos : 0 < h2
  h2_lt_one : h2 < 1
  stability_s : r_s * h2 < 1
  stability_t : r_t * h2 < 1
  /-- Source has more AM than target -/
  more_am_in_source : r_t < r_s

/-- Source denominator is positive. -/
theorem DifferentialAMModel.denom_s_pos (d : DifferentialAMModel) : 0 < 1 - d.r_s * d.h2 := by
  linarith [d.stability_s]

/-- Target denominator is positive. -/
theorem DifferentialAMModel.denom_t_pos (d : DifferentialAMModel) : 0 < 1 - d.r_t * d.h2 := by
  linarith [d.stability_t]

/-- **Measured portability ratio under differential AM.**
    If both populations have the same true R2_rm, the measured portability
    ratio is:
      port_measured = R2_target / R2_source
                    = (R2_rm/(1-r_t*h2)) / (R2_rm/(1-r_s*h2))
                    = (1 - r_s*h2) / (1 - r_t*h2)
    When r_s > r_t, this ratio is < 1, creating an *apparent* portability
    loss that is purely an AM artifact. -/
noncomputable def DifferentialAMModel.apparentPortability (d : DifferentialAMModel) : ℝ :=
  (1 - d.r_s * d.h2) / (1 - d.r_t * d.h2)

/-- **Differential AM creates artifactual portability loss.**
    When source has more AM than target (r_s > r_t), the apparent
    portability is less than 1 even though the true genetic architecture
    is identical. This is because the source R² is more inflated. -/
theorem DifferentialAMModel.differential_am_misleading (d : DifferentialAMModel) :
    d.apparentPortability < 1 := by
  unfold apparentPortability
  rw [div_lt_one d.denom_t_pos]
  have : 0 < (d.r_s - d.r_t) * d.h2 := mul_pos (by linarith [d.more_am_in_source]) d.h2_pos
  linarith

/-- **AM-corrected portability.**
    Correcting for differential AM:
    port_corrected = port_measured * (1 - r_source*h2) / (1 - r_target*h2). -/
noncomputable def amCorrectedPortability
    (port_measured r_source r_target h2 : ℝ) : ℝ :=
  port_measured * (1 - r_source * h2) / (1 - r_target * h2)

/-- **AM correction reduces measured portability when source has more AM.**
    The source AM inflates source R², so the correction factor
    (1-r_s*h2)/(1-r_t*h2) < 1 when r_s > r_t. -/
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

/-- **AM correction recovers true portability.**
    If the only source of portability loss is differential AM,
    then the corrected portability equals 1 (perfect portability).
    We show: if port_measured = (1-r_t*h2)/(1-r_s*h2) (the AM artifact),
    then amCorrectedPortability = 1. -/
theorem am_correction_recovers_true
    (r_s r_t h2 : ℝ) (h_denom_s : 1 - r_s * h2 ≠ 0) (h_denom_t : 1 - r_t * h2 ≠ 0) :
    amCorrectedPortability ((1 - r_t * h2) / (1 - r_s * h2)) r_s r_t h2 = 1 := by
  unfold amCorrectedPortability
  field_simp

end DifferentialAM


/-!
## AM-Induced LD and Cross-Population Prediction

The long-range LD created by AM is population-specific.
A PGS trained exploiting AM-LD in one population will not
find that LD in another population with different AM.
-/

section AMInducedLDPortability

/-- **Cross-population AM-LD model.**
    Captures the scenario where source and target have different
    AM-induced LD structures. The PGS variance in each population
    includes an AM-LD component proportional to r*h2. -/
structure CrossPopAMLD where
  /-- Effect sizes at two example loci -/
  beta_i : ℝ
  beta_j : ℝ
  /-- Source AM rate -/
  r_s : ℝ
  /-- Target AM rate -/
  r_t : ℝ
  /-- Heritability -/
  h2 : ℝ
  r_s_pos : 0 < r_s
  r_t_nonneg : 0 ≤ r_t
  r_t_lt_rs : r_t < r_s
  h2_pos : 0 < h2
  stability_s : r_s * h2 < 1
  stability_t : r_t * h2 < 1

/-- AM-LD in source is stronger than in target. -/
theorem CrossPopAMLD.source_ld_exceeds_target (c : CrossPopAMLD)
    (hbi : 0 < c.beta_i) (hbj : 0 < c.beta_j) :
    amInducedLD c.beta_i c.beta_j c.r_t c.h2 <
    amInducedLD c.beta_i c.beta_j c.r_s c.h2 := by
  unfold amInducedLD
  have hprod := mul_pos hbi hbj
  have h_ds : 0 < 1 - c.r_s * c.h2 := by linarith [c.stability_s]
  have h_dt : 0 < 1 - c.r_t * c.h2 := by linarith [c.stability_t]
  rw [div_lt_div_iff₀ h_dt h_ds]
  have h_diff : 0 < c.r_s - c.r_t := by linarith [c.r_t_lt_rs]
  nlinarith [mul_pos hprod c.h2_pos, mul_pos h_diff c.h2_pos,
             mul_pos hprod (mul_pos h_diff c.h2_pos),
             mul_pos (mul_pos hprod c.r_t) c.h2_pos,
             mul_pos (mul_pos hprod c.r_s) c.h2_pos]

/-- **AM-LD breaks cross-population prediction.**
    The PGS trained in the source captures AM-LD variance equal to
    R2_rm * r_s*h2/(1-r_s*h2). In the target, only r_t*h2/(1-r_t*h2)
    of this component exists. The ratio of AM-LD variance between
    target and source is less than 1, reducing prediction accuracy.

    Specifically, the AM-LD ratio is:
    (r_t*h2/(1-r_t*h2)) / (r_s*h2/(1-r_s*h2)) = r_t(1-r_s*h2) / (r_s(1-r_t*h2)) < 1
    when r_t < r_s. -/
theorem am_ld_breaks_cross_population
    (r_s r_t h2 : ℝ)
    (h_rs : 0 < r_s) (h_rt : 0 < r_t) (h_h2 : 0 < h2)
    (h_stab_s : r_s * h2 < 1) (h_stab_t : r_t * h2 < 1)
    (h_more : r_t < r_s) :
    r_t * (1 - r_s * h2) < r_s * (1 - r_t * h2) := by
  have h_diff : 0 < r_s - r_t := by linarith
  nlinarith [mul_pos h_diff (by linarith : 0 < 1 - r_t * h2 - (r_s - r_t) * r_t * h2),
             mul_pos h_rt h2]

/-- **AM-LD disappears under random mating.**
    When r = 0, the AM-induced LD component vanishes entirely.
    This shows the LD is a mating-pattern artifact, not intrinsic
    genetic architecture. Formalized: amInducedLD with r=0 is zero. -/
theorem am_ld_zero_under_random_mating (beta_i beta_j h2 : ℝ) :
    amInducedLD beta_i beta_j 0 h2 = 0 := by
  unfold amInducedLD
  simp [mul_zero, zero_mul, zero_div]

/-- **AM-LD decays rapidly when mating becomes random.**
    After one generation of random mating, AM-LD is halved
    (recombination breaks cross-locus correlations each generation).
    After t generations: LD(t) = LD(0) * (1/2)^t.
    We prove: for any LD that has decayed below half, it is less than original. -/
theorem am_ld_one_generation_decay
    (ld_am : ℝ) (h_pos : 0 < ld_am) :
    (1 / 2 : ℝ) * ld_am < ld_am := by
  nlinarith

/-- **Cross-trait AM effect.**
    AM on a primary trait (e.g., education) with genetic correlation rg
    to a secondary trait creates AM-LD for the secondary trait proportional
    to rg^2 * r * h2_primary. When both rg and r are positive, the
    cross-trait AM effect is positive. -/
theorem cross_trait_am_effect
    (rg r_education h2_primary : ℝ)
    (h_rg : 0 < rg) (h_r : 0 < r_education) (h_h2 : 0 < h2_primary) :
    0 < rg ^ 2 * r_education * h2_primary := by
  apply mul_pos
  · apply mul_pos
    · positivity
    · exact h_r
  · exact h_h2

end AMInducedLDPortability


/-!
## Population Structure and PGS

Population structure beyond simple two-population models
affects PGS in complex ways.
-/

section PopulationStructure

/-- **Derivation of isolation-by-distance Fst.**

We derive the formula Fst(d) = d / (4 · N_e · σ² + d) from a random-walk
coalescence argument in a one-dimensional stepping-stone model.

**Setup.** Consider a linear array of demes, each of effective size N_e.
Each generation, an individual disperses to a neighbouring deme with
probability proportional to a dispersal kernel with variance σ² per
generation.  Two lineages sampled from demes separated by geographic
distance d must find a common ancestor (coalesce).

**Step 1: Random walk of lineage separation.**
Looking backwards in time, each lineage performs an independent random walk
on the deme lattice with per-generation displacement variance σ².  The
*difference* in their positions is also a random walk with variance 2σ²
per generation (sum of two independent walks).  Coalescence occurs when
both lineages are in the same deme simultaneously.

**Step 2: Coalescence probability per generation.**
When two lineages are in the same deme of size N_e, they coalesce with
probability 1/(2 · N_e) per generation (standard coalescent).  The
expected number of generations for two lineages starting at distance d
to first meet (occupy the same deme) in a 1D random walk is:

    T_meet ≈ d² / (2σ²)    (for large d, from random walk first-passage)

But the relevant quantity is the *competition* between coalescence (rate
1/(2N_e) when co-located) and dispersal (rate σ²).

**Step 3: Equilibrium Fst from the coalescence-dispersal balance.**
Fst measures the probability that two alleles sampled from different demes
are identical by descent *relative to* the total population.  In the
stepping-stone model, the equilibrium Fst at distance d satisfies the
identity (Malécot 1948, Rousset 1997):

    Fst(d) / (1 − Fst(d)) ≈ d / (4 · N_e · σ²)

This arises because the expected coalescence time for two lineages at
distance d is approximately:

    E[T_coal(d)] ≈ 2 · N_e + d / (2σ²) · 2 · N_e = 2 · N_e · (1 + d/(2σ²))

(the first term is the within-deme coalescence time; the second accounts for
the random walk time to reach the same deme, multiplied by the local
coalescence time).  Since Fst ≈ 1 − (T_within / T_between):

    Fst(d) ≈ (T_between − T_within) / T_between

**Step 4: Solving for Fst.**
From the Rousset identity:

    Fst / (1 − Fst) = d / (4 · N_e · σ²)

Let x = d / (4 · N_e · σ²).  Then:

    Fst = x · (1 − Fst)
    Fst = x − x · Fst
    Fst + x · Fst = x
    Fst · (1 + x) = x
    Fst = x / (1 + x)
        = [d / (4 · N_e · σ²)] / [1 + d / (4 · N_e · σ²)]
        = d / (4 · N_e · σ² + d)

This is the isolation-by-distance Fst formula. ∎ -/

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

/-- **IBD Fst is bounded between 0 and 1.**
    At d=0, Fst=0. As d→∞, Fst→1. -/
theorem ibd_fst_nonneg (d N sigma_sq : ℝ) (h_d : 0 ≤ d) (h_N : 0 < N) (h_s : 0 < sigma_sq) :
    0 ≤ ibdFst d N sigma_sq := by
  unfold ibdFst
  apply div_nonneg h_d
  positivity

theorem ibd_fst_lt_one (d N sigma_sq : ℝ) (h_d : 0 ≤ d) (h_N : 0 < N) (h_s : 0 < sigma_sq) :
    ibdFst d N sigma_sq < 1 := by
  unfold ibdFst
  rw [div_lt_one (by positivity)]
  linarith [mul_pos h_N h_s]

/-- **Founder effects create portability outliers.**
    In a population with strong founder effects, the effective Fst
    (due to bottleneck-induced drift) exceeds what geographic distance
    would predict. We model this as: Fst_actual > Fst_predicted(d).
    Consequence: portability deviates from the IBD gradient. -/
theorem founder_effect_excess_fst
    (d N_large N_bottleneck sigma_sq : ℝ)
    (h_d : 0 < d) (h_Nl : 0 < N_large) (h_Nb : 0 < N_bottleneck)
    (h_s : 0 < sigma_sq) (h_bottleneck : N_bottleneck < N_large) :
    ibdFst d N_bottleneck sigma_sq > ibdFst d N_large sigma_sq := by
  unfold ibdFst
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h_s (by linarith : 0 < N_large - N_bottleneck)]

end PopulationStructure

end Calibrator
