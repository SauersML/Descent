import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory Finset

/-!
# Derivation of the PGS Portability Bound from First Principles

We formalize the portability derivation first in a general shared-LD kernel
model, where the transported PGS uses source effect sizes as weights and both
the score variance and target genetic variance are evaluated under a common
genotype covariance operator `K`. The standardized diagonal-LD
(independent-variant) model then appears as a specialization.

In the shared-LD model we prove the exact identity

  R²_target = rg_K² × h²_target

where `rg_K` is the effect correlation induced by the shared LD kernel. We then
derive the practical portability bound

  R²_target ≤ rg_K² × R²_source

under an explicit target-vs-source heritability comparison. In the
standardized diagonal-LD model, `rg_K` reduces to the ordinary Euclidean
effect-size correlation.

## Setup

A PGS is PGS = Σᵢ βᵢ × Gᵢ where βᵢ are GWAS effect sizes.
In the source population, R²_source = Cov(PGS, Y)² / (Var(PGS) × Var(Y)).
In the target population, effect sizes change: β_target = rg × β_source + ε,
where rg is the cross-population genetic correlation.

The Cauchy-Schwarz inequality bounds the cross-population covariance:
  Cov(PGS_source, Y_target)² ≤ Var(PGS_source) × Var(Y_target_genetic)
Combined with the effect correlation rg, this yields:
  R²_target ≤ rg² × R²_source
-/


/-!
## PGS Model: Effect Sizes and LD Structure
-/

section PGSPortabilityDerivation

/-- Covariance between PGS (using source weights) and the genetic component
    of the phenotype in a given population:
    Cov(PGS, Y_genetic) = Σᵢ Σⱼ β_source_i × Σᵢⱼ × β_causal_j
    where β_causal are the true causal effects in that population. -/
noncomputable def pgsPhenoCov {m : ℕ} (β_weights β_causal : Fin m → ℝ)
    (ld : Fin m → Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin m, β_weights i * ld i j * β_causal j

/-- Genetic variance induced by a shared LD kernel. -/
noncomputable def sharedLDGeneticVariance {m : ℕ}
    (β : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) : ℝ :=
  pgsPhenoCov β β ld

/-- Heritability induced by a shared LD kernel. -/
noncomputable def sharedLDHeritability {m : ℕ}
    (β : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sharedLDGeneticVariance β ld / var_y

/-- R² of a PGS: the squared correlation between PGS and phenotype.
    R² = Cov(PGS, Y)² / (Var(PGS) × Var(Y)). -/
noncomputable def pgsR2 (cov_pgs_y : ℝ) (var_pgs var_y : ℝ) : ℝ :=
  cov_pgs_y ^ 2 / (var_pgs * var_y)

/-- Source-population `R²` of the score that uses the true source effects as
    weights under a shared LD kernel. -/
noncomputable def sourceTruthR2SharedLD {m : ℕ}
    (β_source : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  pgsR2 (sharedLDGeneticVariance β_source ld)
    (sharedLDGeneticVariance β_source ld) var_y

/-- Target-population transported `R²` of the source-weighted score under a
    shared LD kernel. -/
noncomputable def transportedTargetR2SharedLD {m : ℕ}
    (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  pgsR2 (pgsPhenoCov β_source β_target ld)
    (sharedLDGeneticVariance β_source ld) var_y

/-- Effect correlation induced by a shared LD kernel. -/
noncomputable def ldEffectGeneticCorrelation {m : ℕ}
    (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) : ℝ :=
  pgsPhenoCov β_source β_target ld /
    Real.sqrt (sharedLDGeneticVariance β_source ld * sharedLDGeneticVariance β_target ld)

/-- Euclidean / independent-variant genetic correlation between source and
    target effect-size vectors. This is the diagonal-LD specialization of the
    shared-LD correlation above. -/
noncomputable def effectGeneticCorrelation {m : ℕ} (β_source β_target : Fin m → ℝ) : ℝ :=
  (∑ i : Fin m, β_source i * β_target i) /
    Real.sqrt ((∑ i : Fin m, β_source i ^ 2) * (∑ i : Fin m, β_target i ^ 2))

/-- Standardized diagonal LD operator: independent variants with unit variance. -/
def standardizedDiagonalLD {m : ℕ} : Fin m → Fin m → ℝ :=
  fun i j => if i = j then 1 else 0

/-- Additive genetic variance in the standardized diagonal-LD model. -/
noncomputable def additiveGeneticVariance {m : ℕ} (β : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, β i ^ 2

/-- Additive heritability `h² = V_A / V_Y` in the standardized diagonal-LD model. -/
noncomputable def additiveHeritability {m : ℕ} (β : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  additiveGeneticVariance β / var_y

/-- Source-population `R²` of the score that uses source effect sizes as weights in the
    standardized diagonal-LD model. -/
noncomputable def sourceSelfR2DiagonalLD {m : ℕ} (β_source : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sourceTruthR2SharedLD β_source standardizedDiagonalLD var_y

/-- Target-population transported `R²` of the source-weighted score in the
    standardized diagonal-LD model. -/
noncomputable def transportedTargetR2DiagonalLD {m : ℕ}
    (β_source β_target : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  transportedTargetR2SharedLD β_source β_target standardizedDiagonalLD var_y

/-- **Cauchy-Schwarz for effect-size inner product.**
    |Σᵢ β_source_i × β_target_i|² ≤ (Σᵢ β_source_i²) × (Σᵢ β_target_i²).
    This is the discrete Cauchy-Schwarz inequality applied to the vectors
    of effect sizes, and is the core mathematical ingredient for the
    portability bound.

    We prove this using Mathlib's `inner_mul_le_norm_mul_sq` on `EuclideanSpace`.
    The key insight: interpreting β_source and β_target as elements of ℝ^m
    (a Hilbert space), the Cauchy-Schwarz inequality gives
    ⟨β_source, β_target⟩² ≤ ‖β_source‖² × ‖β_target‖².
    The inner product ⟨u, v⟩ = Σᵢ uᵢ vᵢ and ‖u‖² = Σᵢ uᵢ² in EuclideanSpace. -/
theorem effect_size_cauchy_schwarz {m : ℕ}
    (β_s β_t : Fin m → ℝ)
    (sum_s_sq sum_t_sq cross : ℝ)
    (h_ss : sum_s_sq = ∑ i : Fin m, β_s i ^ 2)
    (h_tt : sum_t_sq = ∑ i : Fin m, β_t i ^ 2)
    (h_cross : cross = ∑ i : Fin m, β_s i * β_t i) :
    cross ^ 2 ≤ sum_s_sq * sum_t_sq := by
  subst h_ss; subst h_tt; subst h_cross
  simpa using sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) β_s β_t

/-- **Genetic correlation is bounded by [-1, 1].**
    |rg| ≤ 1 follows directly from Cauchy-Schwarz on effect sizes. -/
theorem effect_genetic_correlation_bounded {m : ℕ}
    (β_s β_t : Fin m → ℝ)
    (h_s_nonzero : 0 < ∑ i : Fin m, β_s i ^ 2)
    (h_t_nonzero : 0 < ∑ i : Fin m, β_t i ^ 2) :
    (effectGeneticCorrelation β_s β_t) ^ 2 ≤ 1 := by
  unfold effectGeneticCorrelation
  rw [div_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (∑ i, β_s i ^ 2) * (∑ i, β_t i ^ 2))]
  rw [div_le_one (by positivity)]
  exact effect_size_cauchy_schwarz β_s β_t _ _ _
    rfl rfl rfl

/-- A source-truth score achieves the shared-LD heritability exactly. -/
theorem sourceTruthR2_eq_sharedLDHeritability {m : ℕ}
    (β : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < sharedLDGeneticVariance β ld) :
    sourceTruthR2SharedLD β ld var_y = sharedLDHeritability β ld var_y := by
  unfold sourceTruthR2SharedLD pgsR2 sharedLDHeritability
  field_simp [ne_of_gt h_var_y, ne_of_gt h_beta_nonzero]

/-- **Exact transported `R²` identity under a shared LD kernel.**

    If the transported score uses the source effect vector as weights and both
    the score variance and target genetic variance are evaluated under a common
    LD kernel `K`, then

    `R²_target = rg_K² × h²_target`.

    This is the actual first-principles identity behind the portability
    derivation. The diagonal-LD theorem below is a specialization, not the
    flagship statement. -/
theorem transportedTargetR2_eq_ldRgSq_mul_targetH2_sharedLD
    {m : ℕ}
    (β_s β_t : Fin m → ℝ)
    (ld : Fin m → Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_s_nonzero : 0 < sharedLDGeneticVariance β_s ld)
    (h_t_nonzero : 0 < sharedLDGeneticVariance β_t ld) :
    transportedTargetR2SharedLD β_s β_t ld var_y =
      (ldEffectGeneticCorrelation β_s β_t ld) ^ 2 * sharedLDHeritability β_t ld var_y := by
  unfold transportedTargetR2SharedLD ldEffectGeneticCorrelation sharedLDHeritability
    sharedLDGeneticVariance pgsR2
  rw [div_pow]
  have hsqrt :
      Real.sqrt (pgsPhenoCov β_s β_s ld * pgsPhenoCov β_t β_t ld) ^ 2 =
        pgsPhenoCov β_s β_s ld * pgsPhenoCov β_t β_t ld := by
    apply Real.sq_sqrt
    exact mul_nonneg (le_of_lt h_s_nonzero) (le_of_lt h_t_nonzero)
  rw [hsqrt]
  field_simp [ne_of_gt h_var_y, ne_of_gt h_s_nonzero, ne_of_gt h_t_nonzero]
  have h_t_cov_nonzero : pgsPhenoCov β_t β_t ld ≠ 0 := by
    simpa [sharedLDGeneticVariance] using ne_of_gt h_t_nonzero
  have h_t_self : pgsPhenoCov β_t β_t ld * (pgsPhenoCov β_t β_t ld)⁻¹ = 1 := by
    rw [mul_inv_cancel₀ h_t_cov_nonzero]
  calc
    pgsPhenoCov β_s β_t ld ^ 2 * (pgsPhenoCov β_s β_s ld)⁻¹ =
        pgsPhenoCov β_s β_t ld ^ 2 * (pgsPhenoCov β_s β_s ld)⁻¹ * 1 := by ring
    _ =
        pgsPhenoCov β_s β_t ld ^ 2 * (pgsPhenoCov β_s β_s ld)⁻¹ *
          (pgsPhenoCov β_t β_t ld * (pgsPhenoCov β_t β_t ld)⁻¹) := by
        rw [h_t_self]
    _ =
        pgsPhenoCov β_s β_t ld ^ 2 * (pgsPhenoCov β_s β_s ld)⁻¹ *
          pgsPhenoCov β_t β_t ld * (pgsPhenoCov β_t β_t ld)⁻¹ := by ring
    _ =
        pgsPhenoCov β_s β_t ld ^ 2 * pgsPhenoCov β_t β_t ld /
          (pgsPhenoCov β_s β_s ld * pgsPhenoCov β_t β_t ld) := by
        ring_nf

/-- **Practical portability bound under a shared LD kernel.**

    In the shared-LD model, the exact identity above gives
    `R²_target = rg_K² × h²_target`. If the target heritability under the same
    kernel does not exceed the source heritability, then

    `R²_target ≤ rg_K² × R²_source`.

    No extra source-optimality surrogate is assumed here: the source `R²`
    term is the actual source-truth score under the same kernel. -/
theorem portability_bound_sharedLD {m : ℕ}
    (β_s β_t : Fin m → ℝ)
    (ld : Fin m → Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_s_nonzero : 0 < sharedLDGeneticVariance β_s ld)
    (h_t_nonzero : 0 < sharedLDGeneticVariance β_t ld)
    (h_target_h2_le_source_h2 :
      sharedLDHeritability β_t ld var_y ≤ sharedLDHeritability β_s ld var_y) :
    transportedTargetR2SharedLD β_s β_t ld var_y ≤
      (ldEffectGeneticCorrelation β_s β_t ld) ^ 2 * sourceTruthR2SharedLD β_s ld var_y := by
  rw [transportedTargetR2_eq_ldRgSq_mul_targetH2_sharedLD β_s β_t ld var_y
    h_var_y h_s_nonzero h_t_nonzero]
  rw [sourceTruthR2_eq_sharedLDHeritability β_s ld var_y h_var_y h_s_nonzero]
  exact mul_le_mul_of_nonneg_left h_target_h2_le_source_h2 (sq_nonneg _)

/-- Under standardized diagonal LD, `pgsPhenoCov` reduces to the effect-size inner product. -/
theorem pgsPhenoCov_standardizedDiagonalLD {m : ℕ}
    (β_weights β_causal : Fin m → ℝ) :
    pgsPhenoCov β_weights β_causal standardizedDiagonalLD =
      ∑ i : Fin m, β_weights i * β_causal i := by
  unfold pgsPhenoCov standardizedDiagonalLD
  simp

/-- Under standardized diagonal LD, the source PGS variance is the additive genetic variance. -/
theorem pgsPhenoCov_self_standardizedDiagonalLD {m : ℕ}
    (β : Fin m → ℝ) :
    pgsPhenoCov β β standardizedDiagonalLD = additiveGeneticVariance β := by
  rw [pgsPhenoCov_standardizedDiagonalLD]
  unfold additiveGeneticVariance
  congr with i
  ring

/-- Under standardized diagonal LD, the shared-LD genetic variance is additive genetic variance. -/
theorem sharedLDGeneticVariance_standardizedDiagonalLD_eq_additiveGeneticVariance {m : ℕ}
    (β : Fin m → ℝ) :
    sharedLDGeneticVariance β standardizedDiagonalLD = additiveGeneticVariance β := by
  unfold sharedLDGeneticVariance
  exact pgsPhenoCov_self_standardizedDiagonalLD β

/-- Under standardized diagonal LD, shared-LD heritability is additive heritability. -/
theorem sharedLDHeritability_standardizedDiagonalLD_eq_additiveHeritability {m : ℕ}
    (β : Fin m → ℝ) (var_y : ℝ) :
    sharedLDHeritability β standardizedDiagonalLD var_y = additiveHeritability β var_y := by
  unfold sharedLDHeritability additiveHeritability sharedLDGeneticVariance
  rw [pgsPhenoCov_self_standardizedDiagonalLD]

/-- Under standardized diagonal LD, the shared-LD effect correlation is the Euclidean
    effect-size correlation. -/
theorem ldEffectGeneticCorrelation_standardizedDiagonalLD_eq_effectGeneticCorrelation {m : ℕ}
    (β_s β_t : Fin m → ℝ) :
    ldEffectGeneticCorrelation β_s β_t standardizedDiagonalLD =
      effectGeneticCorrelation β_s β_t := by
  unfold ldEffectGeneticCorrelation effectGeneticCorrelation sharedLDGeneticVariance
  rw [pgsPhenoCov_standardizedDiagonalLD, pgsPhenoCov_self_standardizedDiagonalLD,
    pgsPhenoCov_self_standardizedDiagonalLD]
  unfold additiveGeneticVariance
  rfl

/-- In the standardized diagonal-LD model, a source-optimal score has
    `R²_source = h²_source`. -/
theorem sourceOptimalR2_eq_additiveHeritability {m : ℕ}
    (β : Fin m → ℝ) (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β) :
    sourceSelfR2DiagonalLD β var_y = additiveHeritability β var_y := by
  unfold sourceSelfR2DiagonalLD
  rw [sourceTruthR2_eq_sharedLDHeritability β standardizedDiagonalLD var_y h_var_y]
  · exact sharedLDHeritability_standardizedDiagonalLD_eq_additiveHeritability β var_y
  · simpa [sharedLDGeneticVariance_standardizedDiagonalLD_eq_additiveGeneticVariance] using
      h_beta_nonzero

/-- **Exact transported `R²` identity in the standardized diagonal-LD model.**

    In the independent-variant standardized model, with source weights equal
    to the source effect sizes, the transported target `R²` admits the exact
    factorization

    `R²_target = rg² × h²_target`.

    This is the precise algebraic bridge between the transported covariance
    formula and the genetic-correlation normalization. The Cauchy-Schwarz step
    enters through the fact that `rg² ≤ 1`; the factorization itself is exact. -/
theorem transportedTargetR2_eq_rgSq_mul_targetH2_diagonalLD
    {m : ℕ}
    (β_s β_t : Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_s_nonzero : 0 < additiveGeneticVariance β_s)
    (h_t_nonzero : 0 < additiveGeneticVariance β_t) :
    transportedTargetR2DiagonalLD β_s β_t var_y =
      (effectGeneticCorrelation β_s β_t) ^ 2 * additiveHeritability β_t var_y := by
  unfold transportedTargetR2DiagonalLD
  rw [transportedTargetR2_eq_ldRgSq_mul_targetH2_sharedLD β_s β_t standardizedDiagonalLD
    var_y h_var_y]
  · rw [ldEffectGeneticCorrelation_standardizedDiagonalLD_eq_effectGeneticCorrelation]
    rw [sharedLDHeritability_standardizedDiagonalLD_eq_additiveHeritability]
  · simpa [sharedLDGeneticVariance_standardizedDiagonalLD_eq_additiveGeneticVariance] using
      h_s_nonzero
  · simpa [sharedLDGeneticVariance_standardizedDiagonalLD_eq_additiveGeneticVariance] using
      h_t_nonzero

/-- **Practical diagonal-LD portability bound specialized to the source-truth score.**

    This is the standardized diagonal-LD specialization of the shared-LD
    portability bound. The exact identity above gives

    `R²_target = rg² × h²_target`.

    If the target additive heritability does not exceed the source additive
    heritability, then we recover the practical portability bound

    `R²_target ≤ rg² × R²_source`.

    This is a corollary of the shared-LD theorem, not a separately assumed
    source-optimality statement. -/
theorem portability_bound_diagonal_ld {m : ℕ}
    (β_s β_t : Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_s_nonzero : 0 < additiveGeneticVariance β_s)
    (h_t_nonzero : 0 < additiveGeneticVariance β_t)
    (h_target_h2_le_source_h2 :
      additiveHeritability β_t var_y ≤ additiveHeritability β_s var_y) :
    transportedTargetR2DiagonalLD β_s β_t var_y ≤
      (effectGeneticCorrelation β_s β_t) ^ 2 * sourceSelfR2DiagonalLD β_s var_y := by
  unfold transportedTargetR2DiagonalLD sourceSelfR2DiagonalLD
  have h_shared :
      sharedLDHeritability β_t standardizedDiagonalLD var_y ≤
        sharedLDHeritability β_s standardizedDiagonalLD var_y := by
    simpa [sharedLDHeritability_standardizedDiagonalLD_eq_additiveHeritability] using
      h_target_h2_le_source_h2
  have h_s_nonzero' : 0 < sharedLDGeneticVariance β_s standardizedDiagonalLD := by
    simpa [sharedLDGeneticVariance_standardizedDiagonalLD_eq_additiveGeneticVariance] using
      h_s_nonzero
  have h_t_nonzero' : 0 < sharedLDGeneticVariance β_t standardizedDiagonalLD := by
    simpa [sharedLDGeneticVariance_standardizedDiagonalLD_eq_additiveGeneticVariance] using
      h_t_nonzero
  have h_bound :=
    portability_bound_sharedLD β_s β_t standardizedDiagonalLD var_y
      h_var_y h_s_nonzero' h_t_nonzero' h_shared
  simpa [ldEffectGeneticCorrelation_standardizedDiagonalLD_eq_effectGeneticCorrelation] using
    h_bound

/-- Proportional effect vectors scale additive genetic variance by the squared
    proportionality constant. -/
theorem additiveGeneticVariance_proportional {m : ℕ}
    (β : Fin m → ℝ) (c : ℝ) :
    additiveGeneticVariance (fun i => c * β i) = c ^ 2 * additiveGeneticVariance β := by
  unfold additiveGeneticVariance
  calc
    ∑ i : Fin m, (c * β i) ^ 2 = ∑ i : Fin m, c ^ 2 * (β i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = c ^ 2 * ∑ i : Fin m, β i ^ 2 := by
      rw [← Finset.mul_sum]
    _ = c ^ 2 * additiveGeneticVariance β := by
      rfl

/-- Proportional effect vectors scale additive heritability by the squared
    proportionality constant. -/
theorem additiveHeritability_proportional {m : ℕ}
    (β : Fin m → ℝ) (c var_y : ℝ) :
    additiveHeritability (fun i => c * β i) var_y =
      c ^ 2 * additiveHeritability β var_y := by
  unfold additiveHeritability
  rw [additiveGeneticVariance_proportional]
  ring

/-- If target effects are a nonzero scalar multiple of source effects, their
    squared effect correlation is exactly one. -/
theorem effectGeneticCorrelation_sq_one_of_proportional {m : ℕ}
    (β : Fin m → ℝ) (c : ℝ)
    (h_beta_nonzero : 0 < additiveGeneticVariance β)
    (h_c : c ≠ 0) :
    (effectGeneticCorrelation β (fun i => c * β i)) ^ 2 = 1 := by
  have h_cross :
      (∑ i : Fin m, β i * (c * β i)) = c * additiveGeneticVariance β := by
    unfold additiveGeneticVariance
    calc
      ∑ i : Fin m, β i * (c * β i) = ∑ i : Fin m, c * (β i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = c * ∑ i : Fin m, β i ^ 2 := by
        rw [← Finset.mul_sum]
      _ = c * additiveGeneticVariance β := by
        rfl
  have h_t_nonzero :
      0 < additiveGeneticVariance (fun i => c * β i) := by
    rw [additiveGeneticVariance_proportional]
    have h_c_sq_pos : 0 < c ^ 2 := by
      nlinarith [sq_pos_iff.mpr h_c]
    exact mul_pos h_c_sq_pos h_beta_nonzero
  have h_beta_ne : additiveGeneticVariance β ≠ 0 := ne_of_gt h_beta_nonzero
  have h_c_sq_ne : c ^ 2 ≠ 0 := by
    nlinarith [sq_pos_iff.mpr h_c]
  unfold effectGeneticCorrelation
  rw [h_cross]
  change
    (c * additiveGeneticVariance β /
        Real.sqrt
          (additiveGeneticVariance β *
            ∑ i : Fin m, (fun i => c * β i) i ^ 2)) ^ 2 = 1
  change
    (c * additiveGeneticVariance β /
        Real.sqrt
          (additiveGeneticVariance β *
            additiveGeneticVariance (fun i => c * β i))) ^ 2 = 1
  rw [additiveGeneticVariance_proportional, div_pow]
  rw [Real.sq_sqrt]
  · field_simp [h_beta_ne, h_c_sq_ne]
  · positivity

/-- **The diagonal-LD portability bound is tight for proportional effects.**
    If the target effect vector is exactly `rg × β_source`, then the transported
    target score achieves

    `R²_target = rg² × R²_source`

    exactly in the standardized diagonal-LD model for the source-truth score.
    This is the equality case of Cauchy-Schwarz expressed on the actual `R²`
    objects, not only on the underlying inner-product identity. -/
theorem portability_bound_tight_when_proportional {m : ℕ}
    (β_s : Fin m → ℝ) (rg var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_s_nonzero : 0 < additiveGeneticVariance β_s)
    (h_rg : rg ≠ 0) :
    transportedTargetR2DiagonalLD β_s (fun i => rg * β_s i) var_y =
      rg ^ 2 * sourceSelfR2DiagonalLD β_s var_y := by
  have h_t_nonzero :
      0 < additiveGeneticVariance (fun i => rg * β_s i) := by
    rw [additiveGeneticVariance_proportional]
    have h_rg_sq_pos : 0 < rg ^ 2 := by
      nlinarith [sq_pos_iff.mpr h_rg]
    exact mul_pos h_rg_sq_pos h_s_nonzero
  rw [transportedTargetR2_eq_rgSq_mul_targetH2_diagonalLD
    β_s (fun i => rg * β_s i) var_y h_var_y h_s_nonzero h_t_nonzero]
  rw [effectGeneticCorrelation_sq_one_of_proportional β_s rg h_s_nonzero h_rg]
  rw [one_mul]
  rw [additiveHeritability_proportional]
  rw [sourceOptimalR2_eq_additiveHeritability β_s var_y h_var_y h_s_nonzero]

/-- Source-truth diagonal-LD `R²` is positive for a nonzero additive signal and
    positive phenotype variance. -/
theorem sourceSelfR2DiagonalLD_pos {m : ℕ}
    (β : Fin m → ℝ) (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β) :
    0 < sourceSelfR2DiagonalLD β var_y := by
  rw [sourceOptimalR2_eq_additiveHeritability β var_y h_var_y h_beta_nonzero]
  unfold additiveHeritability
  exact div_pos h_beta_nonzero h_var_y

/-- **Exact portability-ratio equality for proportional effects.**
    In the standardized diagonal-LD source-truth setting, if
    `β_target = rg × β_source`, then the transported/source `R²` ratio is
    exactly `rg²`. This is the direct portability-ratio statement most useful
    for interpretation or comparison with observed target/source `R²` ratios. -/
theorem portability_ratio_tight_when_proportional {m : ℕ}
    (β_s : Fin m → ℝ) (rg var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_s_nonzero : 0 < additiveGeneticVariance β_s)
    (h_rg : rg ≠ 0) :
    transportedTargetR2DiagonalLD β_s (fun i => rg * β_s i) var_y /
      sourceSelfR2DiagonalLD β_s var_y = rg ^ 2 := by
  have h_source_pos : 0 < sourceSelfR2DiagonalLD β_s var_y :=
    sourceSelfR2DiagonalLD_pos β_s var_y h_var_y h_s_nonzero
  rw [portability_bound_tight_when_proportional β_s rg var_y h_var_y h_s_nonzero h_rg]
  rw [mul_div_assoc, div_self (ne_of_gt h_source_pos), mul_one]

end PGSPortabilityDerivation


/-!
# Transfer Learning and Domain Adaptation for PGS

This file formalizes the connection between PGS portability and
transfer learning theory from machine learning. The cross-population
PGS problem is precisely a domain adaptation problem where the
source domain (discovery population) differs from the target domain.

Key results:
1. Ben-David domain adaptation bounds for PGS
2. H-divergence between genetic ancestry domains
3. Importance weighting for PGS recalibration
4. Feature representation learning across ancestries
5. Sample complexity for target-domain fine-tuning

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Domain Adaptation Framework for PGS

The PGS portability problem maps to domain adaptation:
- Source domain: discovery population (EUR)
- Target domain: application population (AFR, EAS, etc.)
- Feature space: genotypes
- Label: phenotype
- Hypothesis class: linear predictors (PGS)
-/

section DomainAdaptation

/-- Hypothesis-specific Ben-David certificate for a transferred PGS.

    This is an explicit assumption boundary: proving the certificate requires
    external domain-adaptation arguments, but once it is available we can
    derive concrete target-error bounds from separate caps on its components. -/
structure PGSBenDavidCertificate where
  err_source : ℝ
  err_target : ℝ
  divergence : ℝ
  lambda_star : ℝ
  target_le_source_plus_divergence_plus_lambda :
    err_target ≤ err_source + divergence + lambda_star

/-- Ben-David upper-bound functional `ε_S(h) + d_H(S,T) + λ*`. -/
def benDavidUpperBound (err_source divergence lambda_star : ℝ) : ℝ :=
  err_source + divergence + lambda_star

/-- **Ben-David bound for PGS portability.**
    For a fixed transferred PGS hypothesis `h`, suppose a Ben-David certificate
    establishes `ε_T(h) ≤ ε_S(h) + d_H(S,T) + λ*`. If the source error,
    divergence term, and irreducible gap are separately upper-bounded by
    `source_err_ub`, `div_ub`, and `lambda_ub`, then the target error is at
    most the sum of those component caps. -/
theorem ben_david_pgs_bound
    (cert : PGSBenDavidCertificate)
    (source_err_ub div_ub lambda_ub : ℝ)
    (h_source : cert.err_source ≤ source_err_ub)
    (h_div : cert.divergence ≤ div_ub)
    (h_lambda : cert.lambda_star ≤ lambda_ub) :
    cert.err_target ≤ benDavidUpperBound source_err_ub div_ub lambda_ub := by
  unfold benDavidUpperBound
  linarith [cert.target_le_source_plus_divergence_plus_lambda, h_source, h_div, h_lambda]

/-- **The divergence term relates to Fst.**
    The H-divergence between two genetic ancestry populations
    is monotonically related to Fst. Modeled as divergence = c * Fst
    for a positive proportionality constant c. -/
theorem divergence_increases_with_fst
    (fst₁ fst₂ c : ℝ)
    (h_c : 0 < c)
    (h_fst : fst₁ < fst₂) :
    c * fst₁ < c * fst₂ := by
  exact mul_lt_mul_of_pos_left h_fst h_c

/-- **Larger `λ*` worsens the Ben-David upper bound.**
    `λ*` is the irreducible source-target approximation gap appearing in the
    domain-adaptation certificate. For fixed source error and divergence, a
    larger `λ*` strictly increases the certified target-error upper bound.

    This is the honest formal statement available in this file. Biological
    claims that specific traits have different `λ*` values require a separate
    trait-level model or certificate and are not asserted here. -/
theorem larger_lambda_star_worsens_ben_david_bound
    (err_source divergence lambda₁ lambda₂ : ℝ)
    (h_lambda : lambda₁ < lambda₂) :
    benDavidUpperBound err_source divergence lambda₁ <
      benDavidUpperBound err_source divergence lambda₂ := by
  unfold benDavidUpperBound
  linarith

/-- **A relative tightness certificate gives a two-sided envelope around a bound.**
    This theorem does not derive tightness of the Ben-David bound from a model
    class. It records the exact quantitative consequence of a supplied
    certificate `|actual_gap - bound| < ε * bound`: the realized target-source
    gap lies within a multiplicative `(1 ± ε)` envelope around the reference
    bound. -/
theorem relative_gap_certificate_yields_two_sided_envelope
    (bound actual_gap ε : ℝ)
    (h_tight : |actual_gap - bound| < ε * bound) :
    (1 - ε) * bound < actual_gap ∧ actual_gap < (1 + ε) * bound := by
  have h := abs_lt.mp h_tight
  constructor <;> linarith [h.1, h.2]

end DomainAdaptation


/-!
## Importance Weighting for PGS

Importance weighting (IW) adjusts for the distribution shift
between source and target populations by reweighting individuals.
-/

section ImportanceWeighting

/- **Importance weights for genetic ancestry.**
    w(x) = P_target(x) / P_source(x) for genotype x.
    In practice, estimated from allele frequency ratios. -/

/- **IW-corrected PGS.**
    β̂_IW = argmin Σᵢ wᵢ (yᵢ - x'ᵢ β)²
    This gives unbiased estimates for the target population. -/

/-- **IW effective sample size.**
    n_eff = (Σ wᵢ)² / (Σ wᵢ²) ≤ n.
    The effective sample size decreases with the divergence
    between source and target (larger weights). -/
noncomputable def importanceWeightESS (sum_w sum_w_sq : ℝ) : ℝ :=
  sum_w ^ 2 / sum_w_sq

/-- IW ESS ≤ n (unweighted). -/
theorem iw_ess_le_n
    (n sum_w sum_w_sq : ℝ)
    (h_cauchy_schwarz : sum_w ^ 2 ≤ n * sum_w_sq)
    (h_sw_pos : 0 < sum_w_sq) :
    importanceWeightESS sum_w sum_w_sq ≤ n := by
  unfold importanceWeightESS
  rw [div_le_iff₀ h_sw_pos]
  exact h_cauchy_schwarz

/-- **IW ESS decreases with population divergence.**
    As Fst increases, the importance weights become more variable,
    reducing the effective sample size. Modeled: weight variance
    grows with Fst, and ESS = n / (1 + Var(w)). -/
theorem iw_ess_decreases_with_divergence
    (n var_w₁ var_w₂ : ℝ)
    (h_n : 0 < n) (h_v1 : 0 ≤ var_w₁)
    (h_more_divergent : var_w₁ < var_w₂) :
    n / (1 + var_w₂) < n / (1 + var_w₁) := by
  apply div_lt_div_of_pos_left h_n (by linarith) (by linarith)

/-- **Any positive weight variance strictly reduces the IW effective sample size.**
    In the explicit model `ESS = n / (1 + Var(w))`, positive weight variance
    forces the effective sample size below the unweighted sample size. -/
theorem iw_positive_weight_variance_reduces_ess
    (n var_w : ℝ)
    (h_n : 0 < n)
    (h_var : 0 < var_w) :
    n / (1 + var_w) < n := by
  have h_denom : 1 < 1 + var_w := by linarith
  have h_denom_pos : 0 < 1 + var_w := by linarith
  have h_mul : n < n * (1 + var_w) := by nlinarith
  exact (div_lt_iff₀ h_denom_pos).2 h_mul

/-- **Doubly robust estimation combines IW with model adaptation.**
    DR estimator: if either the weighting model or the outcome model is
    asymptotically correct, and the other nuisance component remains
    uniformly bounded, the target-population estimator is consistent. -/
def AsymptoticallyZero (err : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |err n| < ε

/-- An estimator sequence converges to the target parameter in absolute error. -/
def AsymptoticallyConsistent (est : ℕ → ℝ) (truth : ℝ) : Prop :=
  AsymptoticallyZero (fun n => est n - truth)

/-- If an error term is bounded by a product and one factor converges to zero
    while the other is uniformly bounded, then the error also converges to zero. -/
theorem asymptoticallyZero_of_abs_le_mul
    (h f g : ℕ → ℝ)
    (h_bound : ∀ n, |h n| ≤ |f n| * |g n|)
    (hg_bounded : ∃ C ≥ 0, ∀ n, |g n| ≤ C)
    (hf_zero : AsymptoticallyZero f) :
    AsymptoticallyZero h := by
  intro ε hε
  rcases hg_bounded with ⟨C, hC_nn, hgC⟩
  have hC1_pos : 0 < C + 1 := by linarith
  have h_scaled_pos : 0 < ε / (C + 1) := by positivity
  rcases hf_zero (ε / (C + 1)) h_scaled_pos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hf_small : |f n| < ε / (C + 1) := hN n hn
  have hg_le : |g n| ≤ C := hgC n
  have h_mul_le : |f n| * |g n| ≤ |f n| * C := by
    exact mul_le_mul_of_nonneg_left hg_le (abs_nonneg _)
  have h_mul_le' : |f n| * C ≤ (ε / (C + 1)) * C := by
    exact mul_le_mul_of_nonneg_right hf_small.le hC_nn
  have hC_lt : C < C + 1 := by linarith
  have h_scaled_lt : (ε / (C + 1)) * C < (ε / (C + 1)) * (C + 1) := by
    exact mul_lt_mul_of_pos_left hC_lt h_scaled_pos
  have h_cancel : (ε / (C + 1)) * (C + 1) = ε := by
    field_simp [ne_of_gt hC1_pos]
  calc
    |h n| ≤ |f n| * |g n| := h_bound n
    _ ≤ |f n| * C := h_mul_le
    _ ≤ (ε / (C + 1)) * C := h_mul_le'
    _ < (ε / (C + 1)) * (C + 1) := h_scaled_lt
    _ = ε := h_cancel

/-- **Doubly robust consistency.**
    Let `est_dr n` estimate a target parameter `θ`. If the DR estimation error is
    bounded by the product of the residual weighting bias and residual outcome-model
    bias, then consistency follows whenever either nuisance component converges to
    zero and the other stays uniformly bounded. -/
theorem doubly_robust_consistency
    (θ : ℝ)
    (est_dr bias_iw_only bias_model_only : ℕ → ℝ)
    (h_dr_error_bound :
      ∀ n, |est_dr n - θ| ≤ |bias_iw_only n| * |bias_model_only n|)
    (h_iw_bounded : ∃ C ≥ 0, ∀ n, |bias_iw_only n| ≤ C)
    (h_model_bounded : ∃ C ≥ 0, ∀ n, |bias_model_only n| ≤ C)
    (h_either :
      AsymptoticallyZero bias_iw_only ∨ AsymptoticallyZero bias_model_only) :
    AsymptoticallyConsistent est_dr θ := by
  unfold AsymptoticallyConsistent
  rcases h_either with h_iw_zero | h_model_zero
  · exact asymptoticallyZero_of_abs_le_mul
      (fun n => est_dr n - θ) bias_iw_only bias_model_only
      h_dr_error_bound h_model_bounded h_iw_zero
  · exact asymptoticallyZero_of_abs_le_mul
      (fun n => est_dr n - θ) bias_model_only bias_iw_only
      (by
        intro n
        have h := h_dr_error_bound n
        simpa [mul_comm] using h)
      h_iw_bounded h_model_zero

end ImportanceWeighting


/-!
## Feature Representation Learning

Learning genotype representations that are invariant to ancestry
while preserving trait-relevant information.
-/

section FeatureRepresentation

/- **Ancestry-invariant representations.**
    Find a mapping φ(x) such that P_S(φ(x)) ≈ P_T(φ(x))
    while preserving Y = f(φ(x)) + ε. -/

/-- **PCA projection as a simple representation.**
    Projecting genotypes onto top PCs separates ancestry from
    trait-relevant variation. Removing top PCs reduces ancestry
    signal but may also remove trait signal.
    Net target error is modeled as ancestry-induced bias plus a weighted
    penalty for discarded trait signal. -/
def pcaSignalLossPenalty
    (signalBaseline signalRetained lossWeight : ℝ) : ℝ :=
  lossWeight * (signalBaseline - signalRetained)

/-- Reduction in ancestry-induced target bias achieved by removing ancestry PCs. -/
def pcaBiasReduction
    (ancestryBiasWith ancestryBiasWithout : ℝ) : ℝ :=
  ancestryBiasWith - ancestryBiasWithout

/-- Linearized target error after PCA adjustment: ancestry bias plus a
    weighted trait-signal loss penalty. -/
def pcaNetTargetError
    (ancestryBias signalBaseline signalRetained lossWeight : ℝ) : ℝ :=
  ancestryBias + pcaSignalLossPenalty signalBaseline signalRetained lossWeight

/-- Exact error difference induced by removing ancestry PCs. -/
theorem pca_target_error_difference
    (ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight : ℝ) :
    pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight -
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight =
      pcaSignalLossPenalty signal_with signal_without lossWeight -
        pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
  unfold pcaNetTargetError pcaSignalLossPenalty pcaBiasReduction
  ring

/-- **PCA removal improves target error iff bias reduction exceeds weighted signal loss.**
    This is the exact total-error criterion: PC removal helps iff the
    ancestry-bias reduction is larger than the weighted trait-signal loss,
    is neutral iff they are equal, and hurts iff the loss term is larger. -/
theorem pca_tradeoff
    (ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight : ℝ) :
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight <
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      pcaSignalLossPenalty signal_with signal_without lossWeight <
        pcaBiasReduction ancestry_bias_with ancestry_bias_without) ∧
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight ≤
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      pcaSignalLossPenalty signal_with signal_without lossWeight ≤
        pcaBiasReduction ancestry_bias_with ancestry_bias_without) ∧
    (pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight <
        pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight ↔
      pcaBiasReduction ancestry_bias_with ancestry_bias_without <
        pcaSignalLossPenalty signal_with signal_without lossWeight) ∧
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight =
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      pcaSignalLossPenalty signal_with signal_without lossWeight =
        pcaBiasReduction ancestry_bias_with ancestry_bias_without) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hdiff := pca_target_error_difference
      ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight
    constructor <;> intro h
    · have hsub :
          pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight -
              pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight < 0 := by
        linarith
      rw [hdiff] at hsub
      nlinarith
    · have hsub :
          pcaSignalLossPenalty signal_with signal_without lossWeight -
              pcaBiasReduction ancestry_bias_with ancestry_bias_without < 0 := by
        nlinarith
      rw [← hdiff] at hsub
      linarith
  · have hdiff := pca_target_error_difference
      ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight
    constructor <;> intro h
    · have hsub :
          pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight -
              pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ≤ 0 := by
        linarith
      rw [hdiff] at hsub
      linarith
    · have hsub :
          pcaSignalLossPenalty signal_with signal_without lossWeight -
              pcaBiasReduction ancestry_bias_with ancestry_bias_without ≤ 0 := by
        linarith
      rw [← hdiff] at hsub
      linarith
  · have hdiff := pca_target_error_difference
      ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight
    constructor <;> intro h
    · have hsub :
          0 <
            pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight -
              pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight := by
        linarith
      rw [hdiff] at hsub
      linarith
    · have hsub :
          0 < pcaSignalLossPenalty signal_with signal_without lossWeight -
              pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
        linarith
      rw [← hdiff] at hsub
      linarith
  · have hdiff := pca_target_error_difference
      ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight
    constructor <;> intro h
    · have hsub :
          pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight -
              pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight = 0 := by
        linarith
      rw [hdiff] at hsub
      nlinarith
    · have hsub :
          pcaSignalLossPenalty signal_with signal_without lossWeight -
              pcaBiasReduction ancestry_bias_with ancestry_bias_without = 0 := by
        linarith
      rw [← hdiff] at hsub
      linarith

/-- When the ancestry-bias reduction and signal loss are both positive,
    the total-error tradeoff is controlled by a single loss-weight threshold. -/
theorem pca_tradeoff_threshold_on_lossWeight
    (ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight : ℝ)
    (h_signal_gap : signal_without < signal_with) :
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight <
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      lossWeight <
        pcaBiasReduction ancestry_bias_with ancestry_bias_without /
          (signal_with - signal_without)) ∧
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight =
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      lossWeight =
        pcaBiasReduction ancestry_bias_with ancestry_bias_without /
          (signal_with - signal_without)) := by
  have hgap_pos : 0 < signal_with - signal_without := sub_pos.mpr h_signal_gap
  have hgap_ne : signal_with - signal_without ≠ 0 := ne_of_gt hgap_pos
  rcases pca_tradeoff ancestry_bias_with ancestry_bias_without
      signal_with signal_without lossWeight with
      ⟨hImprove, _, _, hNeutral⟩
  refine ⟨?_, ?_⟩
  · constructor <;> intro h
    · have hpenalty := hImprove.mp h
      unfold pcaSignalLossPenalty at hpenalty
      by_contra hnot
      have hge :
          pcaBiasReduction ancestry_bias_with ancestry_bias_without /
              (signal_with - signal_without) ≤ lossWeight := by
        linarith
      have hmul :
          (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
              (signal_with - signal_without)) * (signal_with - signal_without) ≤
            lossWeight * (signal_with - signal_without) := by
        exact mul_le_mul_of_nonneg_right hge hgap_pos.le
      have hdiv :
          (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
              (signal_with - signal_without)) * (signal_with - signal_without) =
            pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
        field_simp [hgap_ne]
      rw [hdiv] at hmul
      linarith
    · have hpenalty :
          lossWeight * (signal_with - signal_without) <
            pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
        have hmul :
            lossWeight * (signal_with - signal_without) <
              (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
                  (signal_with - signal_without)) * (signal_with - signal_without) := by
          exact mul_lt_mul_of_pos_right h hgap_pos
        have hdiv :
            (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
                (signal_with - signal_without)) * (signal_with - signal_without) =
              pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
          field_simp [hgap_ne]
        rw [hdiv] at hmul
        exact hmul
      exact hImprove.mpr (by
        unfold pcaSignalLossPenalty
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpenalty)
  · constructor <;> intro h
    · have hpenalty := hNeutral.mp h
      unfold pcaSignalLossPenalty at hpenalty
      exact (eq_div_iff hgap_ne).2 (by
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpenalty)
    · have hpenalty :
          lossWeight * (signal_with - signal_without) =
            pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
        exact (eq_div_iff hgap_ne).1 h
      exact hNeutral.mpr (by
        unfold pcaSignalLossPenalty
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpenalty)

/-- **A local PC-removal minimum beats the adjacent choices.**
    This theorem does not prove existence of a globally optimal number of
    removed PCs. It records the exact local-optimality consequence available
    from two neighboring error comparisons. -/
theorem local_pc_removal_minimum_beats_adjacent_choices
    (err_k err_k_plus_1 err_k_minus_1 : ℝ)
    (h_local_min_right : err_k ≤ err_k_plus_1)
    (h_local_min_left : err_k ≤ err_k_minus_1) :
    err_k ≤ min err_k_plus_1 err_k_minus_1 := by
  exact le_min h_local_min_right h_local_min_left

/-- **A certified lower-divergence representation tightens the transfer bound.**
    Compare two representation-learning strategies through the actual
    domain-adaptation bound components they induce. If the new representation
    has no larger source error, strictly smaller divergence, and no larger
    `λ*`, then its Ben-David upper bound is strictly smaller.

    This theorem does not formalize adversarial optimization itself. It gives
    the rigorous consequence available once any method, adversarial or
    otherwise, is certified to improve the bound components. -/
theorem lower_divergence_representation_tightens_ben_david_bound
    (err_source_standard err_source_new : ℝ)
    (divergence_standard divergence_new : ℝ)
    (lambda_standard lambda_new : ℝ)
    (h_source : err_source_new ≤ err_source_standard)
    (h_div : divergence_new < divergence_standard)
    (h_lambda : lambda_new ≤ lambda_standard) :
    benDavidUpperBound err_source_new divergence_new lambda_new <
      benDavidUpperBound err_source_standard divergence_standard lambda_standard := by
  unfold benDavidUpperBound
  linarith

/-- **Positive information-bottleneck objective means signal exceeds the ancestry penalty.**
    The theorem states only the exact inequality encoded by the objective
    `I(φ(X); Y) - λ I(φ(X); A)`: if that scalar objective is positive, then the
    retained trait information exceeds the penalized ancestry information. -/
theorem positive_info_bottleneck_objective_means_signal_exceeds_penalty
    (I_phi_A I_phi_Y lam : ℝ)
    (h_objective : I_phi_Y - lam * I_phi_A > 0)
    (_h_lam : 0 < lam) (_h_I_A_nn : 0 ≤ I_phi_A) :
    I_phi_Y > lam * I_phi_A := by linarith

end FeatureRepresentation


/-!
## Fine-Tuning and Few-Shot Adaptation

Adapting a source-population PGS to a target population with
limited target-population data.
-/

section FineTuning

/- **Sample complexity for PGS fine-tuning.**
    The number of target-population samples needed to improve
    upon the source PGS depends on:
    1. The divergence (Fst) between source and target
    2. The genetic architecture complexity
    3. The source PGS quality -/

/-- Fine-tuned target `R²` in a simple additive penalty model. -/
def fineTunedTargetR2 (r2_source divergence_penalty adaptation_gain : ℝ) : ℝ :=
  r2_source - divergence_penalty + adaptation_gain

/-- Target-trained `R²` in a simple additive estimation-penalty model. -/
def scratchTargetR2 (oracle_target_r2 estimation_penalty : ℝ) : ℝ :=
  oracle_target_r2 - estimation_penalty

/-- **Fine-tuning wins in the explicit additive penalty model.**
    This theorem does not claim a universal fine-tuning advantage. It works in
    the two formal score models above:

    - `fineTunedTargetR2` starts from source `R²`, pays a portability penalty,
      and gains target-specific adaptation;
    - `scratchTargetR2` starts from an oracle target ceiling and pays a
      finite-sample estimation penalty.

    If the fine-tuned baseline `r2_source + adaptation_gain` weakly exceeds the
    scratch oracle ceiling, and the scratch estimator pays a larger penalty than
    the fine-tuning portability cost, then the modeled fine-tuned target `R²`
    exceeds the modeled scratch target `R²`. -/
theorem fine_tuned_target_r2_exceeds_scratch_of_penalty_gap
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 estimation_penalty : ℝ)
    (h_baseline : oracle_target_r2 ≤ r2_source + adaptation_gain)
    (h_penalty : divergence_penalty < estimation_penalty) :
    scratchTargetR2 oracle_target_r2 estimation_penalty <
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
  unfold scratchTargetR2 fineTunedTargetR2
  linarith

/-- **Crossover extracted from assumed learning-curve inequalities.**
    This theorem does not derive a critical sample size from optimization or
    statistics. It simply records the two boundary inequalities that follow once
    the user supplies a candidate `n_crit` together with below-threshold and
    above-threshold dominance assumptions for the two learning curves. -/
theorem crossover_from_assumed_critical_sample_size
    (n_crit : ℕ) (r2_source_unadjusted r2_target_trained : ℝ → ℝ)
    (h_below : ∀ n : ℕ, n < n_crit → r2_target_trained n < r2_source_unadjusted n)
    (h_above : ∀ n : ℕ, n_crit ≤ n → r2_source_unadjusted n ≤ r2_target_trained n)
    (h_crit_pos : 0 < n_crit) :
    -- Just below n_crit, source wins; at n_crit, target wins (crossover)
    r2_target_trained ((n_crit - 1 : ℕ) : ℝ) < r2_source_unadjusted ((n_crit - 1 : ℕ) : ℝ) ∧
      r2_source_unadjusted n_crit ≤ r2_target_trained n_crit := by
  constructor
  · exact h_below (n_crit - 1) (Nat.sub_lt h_crit_pos (Nat.succ_pos 0))
  · exact h_above _ (le_refl _)

/- **Regularized fine-tuning shrinks toward source PGS.**
    β̂_target = argmin Σ wᵢ(yᵢ - x'ᵢβ)² + λ‖β - β̂_source‖²
    The regularization λ controls how much to trust the source PGS. -/

/-- **Optimal regularization decreases with n_target.**
    With more target data, we should trust the target data more
    and the source PGS less. Modeled: optimal λ ∝ 1/n. -/
theorem optimal_lambda_decreases_with_n
    (c : ℝ) (n₁ n₂ : ℕ)
    (h_c : 0 < c)
    (h_n₁ : 0 < n₁)
    (h_more_data : n₁ < n₂) :
    c / (n₂ : ℝ) < c / (n₁ : ℝ) := by
  apply div_lt_div_of_pos_left h_c
  · exact Nat.cast_pos.mpr h_n₁
  · exact Nat.cast_lt.mpr h_more_data

/-- **Amortized per-population adaptation cost falls with the number of source tasks.**
    In the simple amortization model where a one-off adaptation cost
    `n_adapt_single` is spread evenly across `k` source populations, the
    per-population cost `n_adapt_single / k` is strictly below the single-task
    cost whenever `k > 1`. -/
theorem amortized_per_population_adaptation_cost_falls_with_task_count
    (n_adapt_single : ℝ) (k : ℕ)
    (h_n : 0 < n_adapt_single) (h_k : 1 < k) :
    n_adapt_single / (k : ℝ) < n_adapt_single := by
  have hk_pos : 0 < (k : ℝ) := by
    exact Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one h_k)
  have hk_gt_one : (1 : ℝ) < k := by
    exact_mod_cast h_k
  have h_mul : n_adapt_single < n_adapt_single * (k : ℝ) := by
    nlinarith
  exact (div_lt_iff₀ hk_pos).2 h_mul

end FineTuning


/-!
## Theoretical Limits of Transfer

Even with optimal transfer learning, there are fundamental limits
on cross-population PGS performance.
-/

section TransferLimits

/-- **Subunit cross-pop effect correlation prevents attaining target heritability.**
    If a transported score is certified to satisfy the ceiling
    `R²_target ≤ rg_sq × h²_target` and the cross-pop effect-correlation factor
    satisfies `rg_sq < 1`, then the score falls strictly below the target
    heritability ceiling. This is the actual transfer-limit consequence used in
    this file. -/
theorem subunit_effect_correlation_prevents_attaining_target_heritability
    (r2_target rg_sq h2_target : ℝ)
    (h_bound : r2_target ≤ rg_sq * h2_target)
    (h_rg_lt : rg_sq < 1)
    (h_h2_pos : 0 < h2_target) :
    r2_target < h2_target := by
  have h_ceiling_lt : rg_sq * h2_target < h2_target := by
    nlinarith
  exact lt_of_le_of_lt h_bound h_ceiling_lt

/-- **A positive private causal fraction lowers the transferable `R²` ceiling.**
    In the simple overlap model where only the shared fraction `f_shared`
    contributes cross-population signal, the transferable ceiling is
    `r2_source * f_shared = r2_source * (1 - f_private)`. Any strictly positive
    private fraction therefore lowers that ceiling below the source `R²`. -/
theorem private_causal_fraction_lowers_transfer_ceiling
    (r2_source f_shared f_private : ℝ)
    (h_total : f_shared + f_private = 1)
    (h_private : 0 < f_private)
    (h_r2 : 0 < r2_source) :
    r2_source * f_shared = r2_source * (1 - f_private) ∧
      r2_source * f_shared < r2_source := by
  have h_shared_eq : f_shared = 1 - f_private := by linarith
  constructor
  · rw [h_shared_eq]
  · have h_shared_lt_one : f_shared < 1 := by linarith
    exact mul_lt_of_lt_one_right h_r2 h_shared_lt_one

/-- **Transporting a source-optimized PGS to a more diverged target lowers `R²`.**
    This is the honest transfer-limit statement available from the core drift
    transport model: once the target population is strictly farther in `F_ST`
    than the source, the transported target `R²` is strictly below the source
    `R²`. This rules out a universally optimal score within that model, without
    overclaiming a general no-free-lunch theorem over all predictors. -/
theorem transported_source_pgs_loses_r2_with_positive_drift
    (r2Source fstSource fstTarget : ℝ)
    (h_r2 : 0 < r2Source ∧ r2Source < 1)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromObservables r2Source fstSource fstTarget < r2Source := by
  exact targetR2_lt_source_from_observables r2Source fstSource fstTarget
    h_r2 h_fst h_fst_bounds

end TransferLimits

end Calibrator
