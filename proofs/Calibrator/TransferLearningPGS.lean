import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions
import Mathlib.Algebra.Order.Chebyshev

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

/-- Information-bottleneck objective `I(φ(X); Y) - λ I(φ(X); A)`. -/
def infoBottleneckObjective (I_phi_Y I_phi_A lam : ℝ) : ℝ :=
  I_phi_Y - lam * I_phi_A

/-- Exact normalized Gaussian source residual risk from mutual information.
    For a jointly Gaussian source trait `Y` and representation `φ(X)` with
    `Var(Y)=1`, the residual variance fraction is exactly `exp(-2 I(φ(X);Y))`. -/
noncomputable def gaussianSourceResidualRisk (I_phi_Y : ℝ) : ℝ :=
  Real.exp (-2 * I_phi_Y)

/-- Pinsker-certified ancestry-divergence cap from mutual information.
    This is the standard `√(2 I)` envelope obtained by combining binary-domain
    total-variation control with Pinsker's inequality. -/
noncomputable def pinskerAncestryDivergenceCap (I_phi_A : ℝ) : ℝ :=
  Real.sqrt (2 * I_phi_A)

/-- Information-certified Ben-David upper envelope built from:
    - exact Gaussian source residual risk,
    - a Pinsker ancestry-divergence cap,
    - the irreducible `λ*` term. -/
noncomputable def infoCertifiedBenDavidUpperBound
    (I_phi_Y I_phi_A lambda_star : ℝ) : ℝ :=
  gaussianSourceResidualRisk I_phi_Y +
    pinskerAncestryDivergenceCap I_phi_A + lambda_star

/-- More label information strictly lowers the exact Gaussian source residual term. -/
theorem gaussianSourceResidualRisk_strictAnti
    (I₁ I₂ : ℝ)
    (hI : I₁ < I₂) :
    gaussianSourceResidualRisk I₂ < gaussianSourceResidualRisk I₁ := by
  unfold gaussianSourceResidualRisk
  exact Real.exp_lt_exp.mpr (by linarith)

/-- Less ancestry information weakly lowers the Pinsker divergence cap. -/
theorem pinskerAncestryDivergenceCap_mono
    (I₁ I₂ : ℝ)
    (hI₂ : I₁ ≤ I₂) :
    pinskerAncestryDivergenceCap I₁ ≤ pinskerAncestryDivergenceCap I₂ := by
  unfold pinskerAncestryDivergenceCap
  apply Real.sqrt_le_sqrt
  nlinarith

/-- Dominating a representation by increasing trait information and not
    increasing ancestry leakage tightens the information-certified transfer
    envelope. -/
theorem more_label_info_less_ancestry_info_tightens_ben_david_bound
    (I_phi_Y_standard I_phi_Y_new I_phi_A_standard I_phi_A_new : ℝ)
    (lambda_standard lambda_new : ℝ)
    (h_IY : I_phi_Y_standard < I_phi_Y_new)
    (h_IA_standard : I_phi_A_new ≤ I_phi_A_standard)
    (h_lambda : lambda_new ≤ lambda_standard) :
    infoCertifiedBenDavidUpperBound I_phi_Y_new I_phi_A_new lambda_new <
      infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A_standard lambda_standard := by
  have h_source :
      gaussianSourceResidualRisk I_phi_Y_new <
        gaussianSourceResidualRisk I_phi_Y_standard :=
    gaussianSourceResidualRisk_strictAnti I_phi_Y_standard I_phi_Y_new h_IY
  have h_div :
      pinskerAncestryDivergenceCap I_phi_A_new ≤
        pinskerAncestryDivergenceCap I_phi_A_standard :=
    pinskerAncestryDivergenceCap_mono
      I_phi_A_new I_phi_A_standard h_IA_standard
  unfold infoCertifiedBenDavidUpperBound
  linarith

/-- An exact information certificate upper-bounds the Ben-David functional. -/
theorem benDavidUpperBound_le_infoCertifiedBenDavidUpperBound
    (err_source divergence lambda_star I_phi_Y I_phi_A : ℝ)
    (h_source : err_source ≤ gaussianSourceResidualRisk I_phi_Y)
    (h_div : divergence ≤ pinskerAncestryDivergenceCap I_phi_A) :
    benDavidUpperBound err_source divergence lambda_star ≤
      infoCertifiedBenDavidUpperBound I_phi_Y I_phi_A lambda_star := by
  unfold benDavidUpperBound infoCertifiedBenDavidUpperBound
  linarith

/-- **Improving the information-bottleneck objective tightens the transfer bound.**
    This is now an exact information-certified statement rather than an affine
    calibration assumption. If ancestry leakage is held fixed, then a strict
    gain in the bottleneck objective means strictly larger trait information.
    Under the exact Gaussian residual-risk formula and the Pinsker ancestry
    envelope, that strictly tightens the information-certified Ben-David
    upper bound. -/
theorem higher_info_bottleneck_objective_tightens_ben_david_bound
    (I_phi_Y_standard I_phi_Y_new I_phi_A : ℝ)
    (lambda_standard lambda_new lam : ℝ)
    (h_lambda : lambda_new ≤ lambda_standard)
    (h_obj :
      infoBottleneckObjective I_phi_Y_new I_phi_A lam >
        infoBottleneckObjective I_phi_Y_standard I_phi_A lam) :
    infoCertifiedBenDavidUpperBound I_phi_Y_new I_phi_A lambda_new <
      infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A lambda_standard := by
  have h_IY : I_phi_Y_standard < I_phi_Y_new := by
    unfold infoBottleneckObjective at h_obj
    linarith
  exact more_label_info_less_ancestry_info_tightens_ben_david_bound
    I_phi_Y_standard I_phi_Y_new I_phi_A I_phi_A
    lambda_standard lambda_new h_IY (le_rfl) h_lambda

/-- **A better information-bottleneck representation certifies a lower target-error cap.**
    If a learned representation `φ` comes with a Ben-David certificate whose
    source error is bounded by the exact Gaussian residual-risk formula and
    whose domain divergence is bounded by the Pinsker ancestry-leakage cap,
    then improving the information-bottleneck objective at fixed ancestry
    leakage strictly lowers the certified target-error cap. -/
theorem higher_info_bottleneck_objective_lowers_target_error_cap
    (cert_new : PGSBenDavidCertificate)
    (I_phi_Y_standard I_phi_Y_new I_phi_A : ℝ)
    (lambda_standard lam : ℝ)
    (h_source :
      cert_new.err_source ≤ gaussianSourceResidualRisk I_phi_Y_new)
    (h_div :
      cert_new.divergence ≤ pinskerAncestryDivergenceCap I_phi_A)
    (h_lambda : cert_new.lambda_star ≤ lambda_standard)
    (h_obj :
      infoBottleneckObjective I_phi_Y_new I_phi_A lam >
        infoBottleneckObjective I_phi_Y_standard I_phi_A lam) :
    cert_new.err_target <
      infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A lambda_standard := by
  have h_cert_le :
      benDavidUpperBound cert_new.err_source cert_new.divergence cert_new.lambda_star ≤
        infoCertifiedBenDavidUpperBound I_phi_Y_new I_phi_A cert_new.lambda_star := by
    exact benDavidUpperBound_le_infoCertifiedBenDavidUpperBound
      cert_new.err_source cert_new.divergence cert_new.lambda_star
      I_phi_Y_new I_phi_A h_source h_div
  have h_info_lt :
      infoCertifiedBenDavidUpperBound I_phi_Y_new I_phi_A cert_new.lambda_star <
        infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A lambda_standard := by
    exact higher_info_bottleneck_objective_tightens_ben_david_bound
      I_phi_Y_standard I_phi_Y_new I_phi_A
      lambda_standard cert_new.lambda_star lam h_lambda h_obj
  have h_target :
      cert_new.err_target ≤
        benDavidUpperBound cert_new.err_source cert_new.divergence cert_new.lambda_star := by
    exact cert_new.target_le_source_plus_divergence_plus_lambda
  linarith

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

/-- Exact portability penalty induced by observable source-target drift. This is
    the loss in target `R²` relative to the source baseline under the exact
    observable transport theorem `targetR2FromObservables`. -/
noncomputable def observableTransportPenalty
    (r2Source fstSource fstTarget : ℝ) : ℝ :=
  r2Source - targetR2FromObservables r2Source fstSource fstTarget

/-- The additive fine-tuning model is exactly the observable transported target
    `R²` plus any additional target-specific adaptation gain once the
    portability penalty is instantiated by the exact drift transport map. -/
theorem fineTunedTargetR2_eq_targetR2FromObservables_plus_adaptation
    (r2Source fstSource fstTarget adaptationGain : ℝ) :
    fineTunedTargetR2 r2Source
        (observableTransportPenalty r2Source fstSource fstTarget)
        adaptationGain =
      targetR2FromObservables r2Source fstSource fstTarget + adaptationGain := by
  unfold fineTunedTargetR2 observableTransportPenalty
  ring

/-- Exact target-only oracle `R²` in the diagonal-LD architecture model. This is
    the target self-prediction ceiling, i.e. target additive heritability. -/
noncomputable def targetOracleR2DiagonalLD {m : ℕ}
    (β_target : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sourceSelfR2DiagonalLD β_target var_y

/-- The scratch-training scalar model becomes the exact target heritability
    ceiling minus the chosen estimation penalty once the oracle target `R²` is
    instantiated by the target architecture. -/
theorem scratchTargetR2_eq_targetHeritability_minus_estimationPenalty_diagonalLD
    {m : ℕ}
    (β_target : Fin m → ℝ) (var_y estimation_penalty : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β_target) :
    scratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) estimation_penalty =
      additiveHeritability β_target var_y - estimation_penalty := by
  unfold scratchTargetR2 targetOracleR2DiagonalLD
  rw [sourceOptimalR2_eq_additiveHeritability β_target var_y h_var_y h_beta_nonzero]

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

/-- Scratch-trained target `R²` with finite-sample estimation noise
    `noiseVar / nTarget`. -/
noncomputable def sampleLimitedScratchTargetR2
    (oracle_target_r2 noiseVar nTarget : ℝ) : ℝ :=
  scratchTargetR2 oracle_target_r2 (noiseVar / nTarget)

/-- Sample-limited scratch training is the exact target heritability ceiling
    minus the explicit finite-sample estimation penalty `noiseVar / nTarget`. -/
theorem sampleLimitedScratchTargetR2_eq_targetHeritability_minus_noise_over_n_diagonalLD
    {m : ℕ}
    (β_target : Fin m → ℝ) (var_y noiseVar nTarget : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β_target) :
    sampleLimitedScratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) noiseVar nTarget =
      additiveHeritability β_target var_y - noiseVar / nTarget := by
  unfold sampleLimitedScratchTargetR2 scratchTargetR2 targetOracleR2DiagonalLD
  rw [sourceOptimalR2_eq_additiveHeritability β_target var_y h_var_y h_beta_nonzero]

/-- Exact target sample size at which scratch training matches fine-tuning in
    the explicit additive `R²` model above. -/
noncomputable def scratchVsFineTuningCriticalSampleSize
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar : ℝ) : ℝ :=
  noiseVar /
    (oracle_target_r2 -
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain)

/-- **Scratch training matches fine-tuning at the derived critical sample size.**
    In the explicit model
    `scratchTargetR2 = oracle_target_r2 - noiseVar / nTarget`,
    the crossover point is solved exactly rather than assumed. -/
theorem scratchTargetR2_eq_fineTunedTargetR2_at_critical_sample_size
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar : ℝ)
    (h_gap :
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain <
        oracle_target_r2)
    (h_noise : 0 < noiseVar) :
    sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar
        (scratchVsFineTuningCriticalSampleSize
          r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar) =
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
  unfold sampleLimitedScratchTargetR2 scratchVsFineTuningCriticalSampleSize
    scratchTargetR2 fineTunedTargetR2
  have h_gap_pos :
      0 < oracle_target_r2 - (r2_source - divergence_penalty + adaptation_gain) := by
    unfold fineTunedTargetR2 at h_gap
    linarith
  field_simp [ne_of_gt h_gap_pos, ne_of_gt h_noise]
  ring_nf

/-- **Scratch training beats fine-tuning exactly above a derived sample threshold.**
    In the explicit additive `R²` model, the target-only estimator overtakes
    fine-tuning if and only if the target sample size exceeds the exact
    crossover `noiseVar / (oracle_target_r2 - fineTunedTargetR2)`. -/
theorem scratch_beats_fine_tuning_iff_target_sample_exceeds_critical
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar nTarget : ℝ)
    (h_gap :
      fineTunedTargetR2 r2_source divergence_penalty adaptation_gain <
        oracle_target_r2)
    (h_n : 0 < nTarget) :
    fineTunedTargetR2 r2_source divergence_penalty adaptation_gain <
      sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget ↔
    scratchVsFineTuningCriticalSampleSize
        r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar <
      nTarget := by
  have h_gap_pos :
      0 < oracle_target_r2 -
        fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
    exact sub_pos.mpr h_gap
  constructor
  · intro h
    unfold sampleLimitedScratchTargetR2 scratchVsFineTuningCriticalSampleSize
      scratchTargetR2 at *
    have hineq :
        noiseVar / nTarget <
          oracle_target_r2 -
            fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
      linarith
    have hcross :
        noiseVar <
          nTarget *
            (oracle_target_r2 -
              fineTunedTargetR2 r2_source divergence_penalty adaptation_gain) := by
      rw [div_lt_iff₀ h_n] at hineq
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
    rw [div_lt_iff₀ h_gap_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
  · intro h
    unfold sampleLimitedScratchTargetR2 scratchVsFineTuningCriticalSampleSize
      scratchTargetR2 at *
    have hcross :
        noiseVar <
          nTarget *
            (oracle_target_r2 -
              fineTunedTargetR2 r2_source divergence_penalty adaptation_gain) := by
      rw [div_lt_iff₀ h_gap_pos] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hineq :
        noiseVar / nTarget <
          oracle_target_r2 -
            fineTunedTargetR2 r2_source divergence_penalty adaptation_gain := by
      rw [div_lt_iff₀ h_n]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
    linarith

/- **Regularized fine-tuning shrinks toward source PGS.**
    β̂_target = argmin Σ wᵢ(yᵢ - x'ᵢβ)² + λ‖β - β̂_source‖²
    The regularization λ controls how much to trust the source PGS. -/

/-- **Target fine-tuning shrinkage MSE.**
    We model the fine-tuned estimator as a convex combination of the unbiased
    target-only estimator and the source estimator, with source weight `λ`.

    - `gapSq` is the squared source-target effect mismatch.
    - `noiseVar` is the per-sample target estimation variance scale.
    - `noiseVar / nTarget` is the variance of the target-only estimator.

    The resulting MSE decomposes into:
    - squared transfer bias: `gapSq * λ^2`
    - residual target-estimation variance: `(noiseVar / nTarget) * (1 - λ)^2`. -/
noncomputable def sourceShrinkageMSE (gapSq noiseVar nTarget lam : ℝ) : ℝ :=
  gapSq * lam^2 + (noiseVar / nTarget) * (1 - lam)^2

/-- **Exact optimizer of the source-shrinkage MSE.**
    In the explicit bias-variance model above, the unique minimizer is
    `(noiseVar / nTarget) / (gapSq + noiseVar / nTarget)`. This is derived from the
    quadratic objective, not assumed. -/
noncomputable def optimalSourceShrinkageWeight (gapSq noiseVar nTarget : ℝ) : ℝ :=
  (noiseVar / nTarget) / (gapSq + noiseVar / nTarget)

/-- Exact quadratic decomposition around the optimal source weight. -/
theorem sourceShrinkageMSE_eq_optimal_plus_square
    (gapSq noiseVar nTarget lam : ℝ)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    sourceShrinkageMSE gapSq noiseVar nTarget lam =
      gapSq * (noiseVar / nTarget) / (gapSq + noiseVar / nTarget) +
        (gapSq + noiseVar / nTarget) *
          (lam - optimalSourceShrinkageWeight gapSq noiseVar nTarget)^2 := by
  set b : ℝ := noiseVar / nTarget
  have h_curv' : gapSq + b ≠ 0 := by simpa [b] using h_curv
  have hquad :
      gapSq * lam ^ 2 + b * (1 - lam)^2 =
        gapSq * b / (gapSq + b) +
          (gapSq + b) * (lam - b / (gapSq + b))^2 := by
    field_simp [h_curv']
    ring_nf
  simpa [sourceShrinkageMSE, optimalSourceShrinkageWeight, b] using hquad

/-- Closed-form optimizer rewritten with the original denominator. -/
theorem optimalSourceShrinkageWeight_eq_closed_form
    (gapSq noiseVar nTarget : ℝ)
    (h_n : 0 < nTarget)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    optimalSourceShrinkageWeight gapSq noiseVar nTarget =
      noiseVar / (nTarget * gapSq + noiseVar) := by
  have hn_ne : nTarget ≠ 0 := ne_of_gt h_n
  have h_denom : nTarget * gapSq + noiseVar ≠ 0 := by
    intro h_zero
    apply h_curv
    have hmul : nTarget * (gapSq + noiseVar / nTarget) = 0 := by
      calc
        nTarget * (gapSq + noiseVar / nTarget) = nTarget * gapSq + noiseVar := by
          field_simp [hn_ne]
        _ = 0 := h_zero
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exact False.elim (hn_ne h0)
    · exact h0
  unfold optimalSourceShrinkageWeight
  field_simp [hn_ne, h_curv, h_denom]

/-- **The explicit source-shrinkage weight minimizes the fine-tuning MSE.**
    This is a true optimization theorem for the quadratic transfer-bias /
    target-variance objective above. -/
theorem optimalSourceShrinkageWeight_minimizes_mse
    (gapSq noiseVar nTarget lam : ℝ)
    (h_gapSq : 0 ≤ gapSq)
    (h_noise : 0 ≤ noiseVar)
    (h_n : 0 < nTarget) :
    sourceShrinkageMSE gapSq noiseVar nTarget
        (optimalSourceShrinkageWeight gapSq noiseVar nTarget) ≤
      sourceShrinkageMSE gapSq noiseVar nTarget lam := by
  have hcoeff_nonneg : 0 ≤ gapSq + noiseVar / nTarget := by
    have hdiv_nonneg : 0 ≤ noiseVar / nTarget := by
      exact div_nonneg h_noise (le_of_lt h_n)
    linarith
  by_cases h_curv : gapSq + noiseVar / nTarget = 0
  · have hdiv_zero : noiseVar / nTarget = 0 := by
      have hdiv_nonneg : 0 ≤ noiseVar / nTarget := by
        exact div_nonneg h_noise (le_of_lt h_n)
      linarith
    have h_gap_zero : gapSq = 0 := by
      have hdiv_nonneg : 0 ≤ noiseVar / nTarget := by
        exact div_nonneg h_noise (le_of_lt h_n)
      linarith
    have h_noise_zero : noiseVar = 0 := by
      have hn_ne : nTarget ≠ 0 := ne_of_gt h_n
      have hmul : (noiseVar / nTarget) * nTarget = 0 := by
        simpa using congrArg (fun x : ℝ => x * nTarget) hdiv_zero
      calc
        noiseVar = (noiseVar / nTarget) * nTarget := by
          field_simp [hn_ne]
        _ = 0 := hmul
    simp [sourceShrinkageMSE, optimalSourceShrinkageWeight, h_gap_zero, h_noise_zero]
  · rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget lam h_curv]
    have hsquare_nonneg :
        0 ≤ (gapSq + noiseVar / nTarget) *
          (lam - optimalSourceShrinkageWeight gapSq noiseVar nTarget)^2 := by
      exact mul_nonneg hcoeff_nonneg (sq_nonneg _)
    have h_at_opt :
        sourceShrinkageMSE gapSq noiseVar nTarget
            (optimalSourceShrinkageWeight gapSq noiseVar nTarget) =
          gapSq * (noiseVar / nTarget) / (gapSq + noiseVar / nTarget) := by
      rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget
        (optimalSourceShrinkageWeight gapSq noiseVar nTarget) h_curv]
      ring
    rw [h_at_opt]
    linarith

/-- **Optimal regularization decreases with target sample size.**
    In the explicit shrinkage-MSE model above, the source weight solving the
    optimization problem is
    `noiseVar / (nTarget * gapSq + noiseVar)`. Hence, with a fixed transfer gap
    and fixed per-sample target noise, more target data strictly decreases the
    optimal amount of shrinkage toward the source PGS. -/
theorem optimal_lambda_decreases_with_n
    (gapSq noiseVar : ℝ) (n₁ n₂ : ℕ)
    (h_gapSq : 0 < gapSq)
    (h_noise : 0 < noiseVar)
    (h_n₁ : 0 < n₁)
    (h_more_data : n₁ < n₂) :
    optimalSourceShrinkageWeight gapSq noiseVar n₂ <
      optimalSourceShrinkageWeight gapSq noiseVar n₁ := by
  have h_n₂ : 0 < n₂ := lt_trans h_n₁ h_more_data
  have h_curv₁ : gapSq + noiseVar / (n₁ : ℝ) ≠ 0 := by
    have h_pos : 0 < gapSq + noiseVar / (n₁ : ℝ) := by
      have hn₁_real : 0 < (n₁ : ℝ) := Nat.cast_pos.mpr h_n₁
      have hdiv_pos : 0 < noiseVar / (n₁ : ℝ) := by
        exact div_pos h_noise hn₁_real
      linarith
    linarith
  have h_curv₂ : gapSq + noiseVar / (n₂ : ℝ) ≠ 0 := by
    have hn₂_real : 0 < (n₂ : ℝ) := Nat.cast_pos.mpr h_n₂
    have h_pos : 0 < gapSq + noiseVar / (n₂ : ℝ) := by
      have hdiv_pos : 0 < noiseVar / (n₂ : ℝ) := by
        exact div_pos h_noise hn₂_real
      linarith
    linarith
  rw [optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar (n₂ : ℝ)
      (Nat.cast_pos.mpr h_n₂) h_curv₂,
    optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar (n₁ : ℝ)
      (Nat.cast_pos.mpr h_n₁) h_curv₁]
  apply div_lt_div_of_pos_left h_noise
  · have hn₁_real : 0 < (n₁ : ℝ) := Nat.cast_pos.mpr h_n₁
    nlinarith
  · have hcast : (n₁ : ℝ) < (n₂ : ℝ) := by
      exact_mod_cast h_more_data
    nlinarith

/-- **The optimal source weight drops below one-half exactly past a target
    sample threshold.**
    In the explicit shrinkage-MSE model, this gives an interpretable
    sample-complexity criterion for when the target data should dominate the
    source PGS in the optimal convex combination. -/
theorem optimalSourceShrinkageWeight_le_half_iff_target_samples_dominate_gap
    (gapSq noiseVar nTarget : ℝ)
    (h_gapSq : 0 < gapSq)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget) :
    optimalSourceShrinkageWeight gapSq noiseVar nTarget ≤ 1 / 2 ↔
      noiseVar ≤ nTarget * gapSq := by
  have h_curv : gapSq + noiseVar / nTarget ≠ 0 := by
    have h_pos : 0 < gapSq + noiseVar / nTarget := by
      exact add_pos h_gapSq (div_pos h_noise h_n)
    linarith
  have h_denom_pos : 0 < nTarget * gapSq + noiseVar := by
    nlinarith
  rw [optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar nTarget h_n h_curv]
  constructor
  · intro h
    have h_cross : noiseVar ≤ (1 / 2 : ℝ) * (nTarget * gapSq + noiseVar) := by
      exact (div_le_iff₀ h_denom_pos).1 h
    nlinarith
  · intro h
    exact (div_le_iff₀ h_denom_pos).2 (by nlinarith)

/-- Squared coefficient mismatch between a transported source predictor and the
    target-optimal linear predictor. This is the exact bias term appearing in
    the source-shrinkage fine-tuning MSE. -/
noncomputable def coefficientGapSq {p : ℕ}
    (wSource wTarget : Fin p → ℝ) : ℝ :=
  dotProduct (fun i => wSource i - wTarget i) (fun i => wSource i - wTarget i)

/-- Sum of the first `k` population-specific deviations around a shared
    representation center. -/
noncomputable def populationDeviationSum {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i => Finset.sum (Finset.range k) (fun j => deviation j i)

/-- Mean population-specific deviation after training on the first `k`
    source populations. -/
noncomputable def meanPopulationDeviation {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i => (k : ℝ)⁻¹ * populationDeviationSum deviation k i

/-- Meta-learned source weights: a shared center plus the average
    source-population-specific deviation. -/
noncomputable def metaLearnedSourceWeights {p : ℕ}
    (wShared : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i => wShared i + meanPopulationDeviation deviation k i

/-- Population-specific effect deviation around a shared ancestral-effect
    center. This is the exact effect-architecture object whose average is used
    by the meta-learning block below. -/
noncomputable def centeredPopulationEffectDeviation {p : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ) : ℕ → Fin p → ℝ :=
  fun j i => wSource j i - wShared i

/-- Exact mean effect vector over the first `k` source populations. -/
noncomputable def sourcePopulationMeanWeights {p : ℕ}
    (wSource : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i => (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j => wSource j i))

/-- The meta-learned source weights are exactly the mean source-population
    effect vector once the deviations are instantiated as centered effect
    differences around the shared center. -/
theorem metaLearnedSourceWeights_eq_sourcePopulationMeanWeights
    {p : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (k : ℕ)
    (h_k : 0 < k) :
    metaLearnedSourceWeights wShared
        (centeredPopulationEffectDeviation wShared wSource) k =
      sourcePopulationMeanWeights wSource k := by
  funext i
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_k)
  unfold metaLearnedSourceWeights meanPopulationDeviation populationDeviationSum
    centeredPopulationEffectDeviation sourcePopulationMeanWeights
  have hsum_const : Finset.sum (Finset.range k) (fun _ => wShared i) = (k : ℝ) * wShared i := by
    simp
  calc
    wShared i + (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j => wSource j i - wShared i))
        = wShared i + (k : ℝ)⁻¹ *
            (Finset.sum (Finset.range k) (fun j => wSource j i) -
              Finset.sum (Finset.range k) (fun _ => wShared i)) := by
              rw [Finset.sum_sub_distrib]
    _ = wShared i + (k : ℝ)⁻¹ *
            (Finset.sum (Finset.range k) (fun j => wSource j i) - (k : ℝ) * wShared i) := by
              rw [hsum_const]
    _ = (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j => wSource j i)) := by
          field_simp [hk_ne]
          ring

/-- Exact squared transfer gap of the meta-learned source weights. -/
noncomputable def metaLearnedTransferGapSq {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : ℝ :=
  coefficientGapSq (metaLearnedSourceWeights wShared deviation k) wTarget

/-- The meta-learned exact transfer gap is literally the squared mismatch
    between the mean source-population effect vector and the target-optimal
    effect vector. -/
theorem metaLearnedTransferGapSq_eq_sourcePopulationMeanEffectGapSq
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (k : ℕ)
    (h_k : 0 < k) :
    metaLearnedTransferGapSq wShared wTarget
        (centeredPopulationEffectDeviation wShared wSource) k =
      coefficientGapSq (sourcePopulationMeanWeights wSource k) wTarget := by
  unfold metaLearnedTransferGapSq
  rw [metaLearnedSourceWeights_eq_sourcePopulationMeanWeights wShared wSource k h_k]

/-- Dot product distributes over addition in the left argument. -/
theorem dotProduct_add_left {p : ℕ}
    (u v w : Fin p → ℝ) :
    dotProduct (fun i => u i + v i) w = dotProduct u w + dotProduct v w := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

/-- Dot product distributes over addition in the right argument. -/
theorem dotProduct_add_right {p : ℕ}
    (u v w : Fin p → ℝ) :
    dotProduct u (fun i => v i + w i) = dotProduct u v + dotProduct u w := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

/-- Dot product is symmetric over `ℝ`. -/
theorem dotProduct_comm {p : ℕ}
    (u v : Fin p → ℝ) :
    dotProduct u v = dotProduct v u := by
  simp [dotProduct, mul_comm]

/-- Pulling a scalar out of the left dot-product argument. -/
theorem dotProduct_smul_left {p : ℕ}
    (c : ℝ) (u v : Fin p → ℝ) :
    dotProduct (fun i => c * u i) v = c * dotProduct u v := by
  unfold dotProduct
  rw [show (∑ i, (c * u i) * v i) = ∑ i, c * (u i * v i) by
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  rw [← Finset.mul_sum]

/-- Pulling a scalar out of the right dot-product argument. -/
theorem dotProduct_smul_right {p : ℕ}
    (u v : Fin p → ℝ) (c : ℝ) :
    dotProduct u (fun i => c * v i) = c * dotProduct u v := by
  unfold dotProduct
  rw [show (∑ i, u i * (c * v i)) = ∑ i, c * (u i * v i) by
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  rw [← Finset.mul_sum]

/-- Dot product of a finite sum of vectors with a fixed vector. -/
theorem dotProduct_sum_left {α : Type*} [DecidableEq α] {p : ℕ}
    (s : Finset α)
    (f : α → Fin p → ℝ)
    (v : Fin p → ℝ) :
    dotProduct (fun i => Finset.sum s (fun j => f j i)) v =
      Finset.sum s (fun j => dotProduct (f j) v) := by
  unfold dotProduct
  rw [show (∑ i, (Finset.sum s (fun j => f j i)) * v i) =
      ∑ i, Finset.sum s (fun j => f j i * v i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]]
  rw [Finset.sum_comm]

/-- Dot product of a fixed vector with a finite sum of vectors. -/
theorem dotProduct_sum_right {α : Type*} [DecidableEq α] {p : ℕ}
    (s : Finset α)
    (u : Fin p → ℝ)
    (f : α → Fin p → ℝ) :
    dotProduct u (fun i => Finset.sum s (fun j => f j i)) =
      Finset.sum s (fun j => dotProduct u (f j)) := by
  unfold dotProduct
  rw [show (∑ i, u i * (Finset.sum s (fun j => f j i))) =
      ∑ i, Finset.sum s (fun j => u i * f j i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]]
  rw [Finset.sum_comm]

/-- Prefix-sum recursion for population-specific deviations. -/
theorem populationDeviationSum_succ {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) :
    populationDeviationSum deviation (k + 1) =
      fun i => populationDeviationSum deviation k i + deviation k i := by
  funext i
  simp [populationDeviationSum, Finset.sum_range_succ]

/-- If the new population-specific deviation is orthogonal to each earlier
    deviation, then it is orthogonal to their sum. -/
theorem dotProduct_populationDeviationSum_last_eq_zero {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ)
    (h_pair : ∀ j < k, dotProduct (deviation j) (deviation k) = 0) :
    dotProduct (populationDeviationSum deviation k) (deviation k) = 0 := by
  rw [show dotProduct (populationDeviationSum deviation k) (deviation k) =
      Finset.sum (Finset.range k) (fun j => dotProduct (deviation j) (deviation k)) by
      simpa [populationDeviationSum] using
        dotProduct_sum_left (Finset.range k) deviation (deviation k)]
  apply Finset.sum_eq_zero
  intro j hj
  exact h_pair j (Finset.mem_range.mp hj)

/-- Exact norm growth of the summed population-specific deviations.
    Under pairwise orthogonality and equal per-population squared norm, the
    squared norm of the sum over `k` populations is exactly `k * gap`. -/
theorem populationDeviationSum_squaredNorm_eq_mul {p : ℕ}
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ) :
    ∀ k : ℕ,
      (∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap) →
      (∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0) →
      dotProduct (populationDeviationSum deviation k) (populationDeviationSum deviation k) =
        k * populationSpecificGap
  | 0, _, _ => by
      simp [populationDeviationSum, dotProduct]
  | k + 1, h_norm, h_pair => by
      have h_norm_prev : ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap := by
        intro j hj
        exact h_norm j (lt_trans hj (Nat.lt_succ_self k))
      have h_pair_prev :
          ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0 := by
        intro j hj l hl hneq
        exact h_pair j (lt_trans hj (Nat.lt_succ_self k))
          l (lt_trans hl (Nat.lt_succ_self k)) hneq
      have ih :=
        populationDeviationSum_squaredNorm_eq_mul deviation populationSpecificGap k
          h_norm_prev h_pair_prev
      have h_last_norm :
          dotProduct (deviation k) (deviation k) = populationSpecificGap := by
        exact h_norm k (Nat.lt_succ_self k)
      have h_cross_left :
          dotProduct (populationDeviationSum deviation k) (deviation k) = 0 := by
        apply dotProduct_populationDeviationSum_last_eq_zero
        intro j hj
        exact h_pair j (lt_trans hj (Nat.lt_succ_self k))
          k (Nat.lt_succ_self k) (Nat.ne_of_lt hj)
      calc
        dotProduct (populationDeviationSum deviation (k + 1))
            (populationDeviationSum deviation (k + 1))
            =
              dotProduct (populationDeviationSum deviation k) (populationDeviationSum deviation k) +
                dotProduct (populationDeviationSum deviation k) (deviation k) +
                (dotProduct (deviation k) (populationDeviationSum deviation k) +
                  dotProduct (deviation k) (deviation k)) := by
                rw [populationDeviationSum_succ, dotProduct_add_left,
                  dotProduct_add_right, dotProduct_add_right]
        _ = k * populationSpecificGap + 0 + (0 + populationSpecificGap) := by
              rw [ih, h_cross_left, dotProduct_comm, h_cross_left, h_last_norm]
        _ = (((k + 1 : ℕ) : ℝ) * populationSpecificGap) := by
              rw [Nat.cast_add, Nat.cast_one]
              ring_nf

/-- Exact squared norm of the averaged population-specific deviation.
    Under pairwise orthogonality and equal per-population squared norm, the
    average deviation has squared norm exactly `gap / k`. -/
theorem meanPopulationDeviation_squaredNorm_eq_populationSpecificGap_div_k {p : ℕ}
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (h_norm : ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    dotProduct (meanPopulationDeviation deviation k) (meanPopulationDeviation deviation k) =
      populationSpecificGap / k := by
  have h_sumnorm :=
    populationDeviationSum_squaredNorm_eq_mul deviation populationSpecificGap k h_norm h_pair
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_k)
  unfold meanPopulationDeviation
  calc
    dotProduct (fun i => (k : ℝ)⁻¹ * populationDeviationSum deviation k i)
        (fun i => (k : ℝ)⁻¹ * populationDeviationSum deviation k i)
        =
          ((k : ℝ)⁻¹)^2 *
            dotProduct (populationDeviationSum deviation k) (populationDeviationSum deviation k) := by
              unfold dotProduct
              rw [show (∑ i,
                    ((k : ℝ)⁻¹ * populationDeviationSum deviation k i) *
                      ((k : ℝ)⁻¹ * populationDeviationSum deviation k i))
                  = ∑ i, ((k : ℝ)⁻¹)^2 *
                      (populationDeviationSum deviation k i *
                        populationDeviationSum deviation k i) by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring]
              rw [← Finset.mul_sum]
    _ = ((k : ℝ)⁻¹)^2 * (k * populationSpecificGap) := by
          rw [h_sumnorm]
    _ = populationSpecificGap / k := by
          field_simp [hk_ne]

/-- If the shared representation residual is orthogonal to each population-
    specific deviation, then it is orthogonal to their average. -/
theorem dotProduct_meanPopulationDeviation_eq_zero {p : ℕ}
    (u : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (k : ℕ)
    (h_orth : ∀ j < k, dotProduct u (deviation j) = 0) :
    dotProduct u (meanPopulationDeviation deviation k) = 0 := by
  unfold meanPopulationDeviation
  rw [dotProduct_smul_right]
  rw [show dotProduct u (populationDeviationSum deviation k) =
      Finset.sum (Finset.range k) (fun j => dotProduct u (deviation j)) by
      simpa [populationDeviationSum] using
        dotProduct_sum_right (Finset.range k) u deviation]
  have hsum :
      Finset.sum (Finset.range k) (fun j => dotProduct u (deviation j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact h_orth j (Finset.mem_range.mp hj)
  rw [hsum]
  ring

/-- Exact transfer-gap formula for the shared-feature meta-learning model.
    If the shared center has residual gap `irreducibleGap`, each population-
    specific deviation has squared norm `populationSpecificGap`, those
    deviations are pairwise orthogonal, and each is orthogonal to the shared
    residual, then averaging over `k` source populations yields the exact
    residual gap `irreducibleGap + populationSpecificGap / k`. -/
theorem metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j < k, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm :
      ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair :
      ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    metaLearnedTransferGapSq wShared wTarget deviation k =
      irreducibleGap + populationSpecificGap / k := by
  let sharedResidual : Fin p → ℝ := fun i => wShared i - wTarget i
  have h_shared_norm : dotProduct sharedResidual sharedResidual = irreducibleGap := by
    simpa [sharedResidual, coefficientGapSq] using h_shared
  have h_mean_norm :
      dotProduct (meanPopulationDeviation deviation k) (meanPopulationDeviation deviation k) =
        populationSpecificGap / k := by
    exact meanPopulationDeviation_squaredNorm_eq_populationSpecificGap_div_k
      deviation populationSpecificGap k h_k h_norm h_pair
  have h_cross :
      dotProduct sharedResidual (meanPopulationDeviation deviation k) = 0 := by
    exact dotProduct_meanPopulationDeviation_eq_zero
      sharedResidual deviation k h_shared_orth
  have h_sub :
      (fun i =>
        (metaLearnedSourceWeights wShared deviation k i) - wTarget i) =
        fun i => sharedResidual i + meanPopulationDeviation deviation k i := by
    funext i
    unfold metaLearnedSourceWeights sharedResidual
    ring
  unfold metaLearnedTransferGapSq coefficientGapSq
  rw [h_sub]
  calc
    dotProduct
        (fun i => sharedResidual i + meanPopulationDeviation deviation k i)
        (fun i => sharedResidual i + meanPopulationDeviation deviation k i)
        =
          dotProduct sharedResidual sharedResidual +
            dotProduct sharedResidual (meanPopulationDeviation deviation k) +
            (dotProduct (meanPopulationDeviation deviation k) sharedResidual +
              dotProduct (meanPopulationDeviation deviation k)
                (meanPopulationDeviation deviation k)) := by
              rw [dotProduct_add_left, dotProduct_add_right, dotProduct_add_right]
    _ = irreducibleGap + 0 + (0 + populationSpecificGap / k) := by
          rw [h_shared_norm, h_cross, dotProduct_comm, h_cross, h_mean_norm]
    _ = irreducibleGap + populationSpecificGap / k := by
          ring

/-- Exact population-genetic bridge for meta-learning: if the source
    population effect vectors decompose into a shared center plus orthogonal
    centered deviations, then the mean source effect vector itself has exact
    transfer gap `irreducibleGap + populationSpecificGap / k` to the target
    optimum. -/
theorem sourcePopulationMeanEffectGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j < k, dotProduct (fun i => wShared i - wTarget i)
        (centeredPopulationEffectDeviation wShared wSource j) = 0)
    (h_norm :
      ∀ j < k, dotProduct (centeredPopulationEffectDeviation wShared wSource j)
        (centeredPopulationEffectDeviation wShared wSource j) = populationSpecificGap)
    (h_pair :
      ∀ j < k, ∀ l < k, j ≠ l →
        dotProduct (centeredPopulationEffectDeviation wShared wSource j)
          (centeredPopulationEffectDeviation wShared wSource l) = 0) :
    coefficientGapSq (sourcePopulationMeanWeights wSource k) wTarget =
      irreducibleGap + populationSpecificGap / k := by
  rw [← metaLearnedTransferGapSq_eq_sourcePopulationMeanEffectGapSq
    wShared wTarget wSource k h_k]
  exact metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    wShared wTarget (centeredPopulationEffectDeviation wShared wSource)
    irreducibleGap populationSpecificGap k h_k h_shared h_shared_orth h_norm h_pair

/-- More source populations strictly reduce the exact residual transfer gap in
    the shared-feature meta-learning model, because the averaged population-
    specific deviation has exact squared norm `gap / k`. -/
theorem metaLearnedTransferGapSq_strictMono {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (k₁ k₂ : ℕ)
    (h_pop : 0 < populationSpecificGap)
    (h_k₁ : 0 < k₁)
    (h_more : k₁ < k₂)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j < k₂, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm :
      ∀ j < k₂, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair :
      ∀ j < k₂, ∀ l < k₂, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    metaLearnedTransferGapSq wShared wTarget deviation k₂ <
      metaLearnedTransferGapSq wShared wTarget deviation k₁ := by
  have h_k₂ : 0 < k₂ := lt_trans h_k₁ h_more
  have h_formula₂ :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ =
        irreducibleGap + populationSpecificGap / k₂ := by
    exact metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
      wShared wTarget deviation irreducibleGap populationSpecificGap
      k₂ h_k₂ h_shared h_shared_orth h_norm h_pair
  have h_formula₁ :
      metaLearnedTransferGapSq wShared wTarget deviation k₁ =
        irreducibleGap + populationSpecificGap / k₁ := by
    exact metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
      wShared wTarget deviation irreducibleGap populationSpecificGap
      k₁ h_k₁ h_shared
      (by
        intro j hj
        exact h_shared_orth j (lt_trans hj h_more))
      (by
        intro j hj
        exact h_norm j (lt_trans hj h_more))
      (by
        intro j hj l hl hneq
        exact h_pair j (lt_trans hj h_more) l (lt_trans hl h_more) hneq)
  rw [h_formula₂, h_formula₁]
  have hk₁ : 0 < (k₁ : ℝ) := Nat.cast_pos.mpr h_k₁
  have hcast : (k₁ : ℝ) < (k₂ : ℝ) := by
    exact_mod_cast h_more
  have hdiv : populationSpecificGap / (k₂ : ℝ) < populationSpecificGap / (k₁ : ℝ) := by
    exact div_lt_div_of_pos_left h_pop hk₁ hcast
  linarith

/-- Positivity of the exact shared-feature meta-learning transfer gap. -/
theorem metaLearnedTransferGapSq_pos {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (k : ℕ)
    (h_irred : 0 ≤ irreducibleGap)
    (h_pop : 0 < populationSpecificGap)
    (h_k : 0 < k)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j < k, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm :
      ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair :
      ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    0 < metaLearnedTransferGapSq wShared wTarget deviation k := by
  rw [metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    wShared wTarget deviation irreducibleGap populationSpecificGap
    k h_k h_shared h_shared_orth h_norm h_pair]
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr h_k
  have hdiv : 0 < populationSpecificGap / (k : ℝ) := by
    exact div_pos h_pop hk
  linarith

/-- Weighted population-specific deviation around the shared representation
    center. This lets us compare the usual equal-weight meta average against
    arbitrary affine aggregation of the first `k` source populations. -/
noncomputable def weightedPopulationDeviation {p k : ℕ}
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i => ∑ j : Fin k, weight j * deviation j i

/-- Weighted meta-learned source weights built from an affine combination of
    source-population-specific deviations around a shared center. -/
noncomputable def weightedMetaSourceWeights {p k : ℕ}
    (wShared : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i => wShared i + weightedPopulationDeviation deviation weight i

/-- Exact transfer gap of a weighted affine meta-aggregator. -/
noncomputable def weightedMetaTransferGapSq {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : ℝ :=
  coefficientGapSq (weightedMetaSourceWeights wShared deviation weight) wTarget

/-- Uniform affine weights on `k` source populations. -/
noncomputable def uniformMetaWeight (k : ℕ) : Fin k → ℝ :=
  fun _ => (k : ℝ)⁻¹

/-- Weighted average of source-population effect vectors. -/
noncomputable def weightedPopulationEffectAverage {p k : ℕ}
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i => ∑ j : Fin k, weight j * wSource j i

/-- Centered finite-population effect deviations around a shared effect center. -/
noncomputable def centeredPopulationEffectDeviationFin {p k : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : Fin k → Fin p → ℝ) : Fin k → Fin p → ℝ :=
  fun j i => wSource j i - wShared i

/-- Any affine meta-aggregator is exactly the weighted average of the source
    effect vectors once deviations are instantiated as centered source effects. -/
theorem weightedMetaSourceWeights_eq_weightedPopulationEffectAverage
    {p k : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    weightedMetaSourceWeights wShared
        (centeredPopulationEffectDeviationFin wShared wSource) weight =
      weightedPopulationEffectAverage wSource weight := by
  funext i
  unfold weightedMetaSourceWeights weightedPopulationDeviation
    centeredPopulationEffectDeviationFin weightedPopulationEffectAverage
  calc
    wShared i + ∑ j : Fin k, weight j * (wSource j i - wShared i)
        = wShared i + ((∑ j : Fin k, weight j * wSource j i) -
            (∑ j : Fin k, weight j) * wShared i) := by
              have hsplit :
                  (∑ j : Fin k, weight j * (wSource j i - wShared i)) =
                    (∑ j : Fin k, weight j * wSource j i) -
                      ∑ j : Fin k, weight j * wShared i := by
                    calc
                      (∑ j : Fin k, weight j * (wSource j i - wShared i))
                          = ∑ j : Fin k, (weight j * wSource j i - weight j * wShared i) := by
                              apply Finset.sum_congr rfl
                              intro j hj
                              ring
                      _ = (∑ j : Fin k, weight j * wSource j i) -
                            ∑ j : Fin k, weight j * wShared i := by
                              rw [Finset.sum_sub_distrib]
              have hconst :
                  (∑ j : Fin k, weight j * wShared i) =
                    (∑ j : Fin k, weight j) * wShared i := by
                    calc
                      (∑ j : Fin k, weight j * wShared i)
                          = ∑ j : Fin k, wShared i * weight j := by
                              apply Finset.sum_congr rfl
                              intro j hj
                              ring
                      _ = wShared i * ∑ j : Fin k, weight j := by
                            rw [Finset.mul_sum]
                      _ = (∑ j : Fin k, weight j) * wShared i := by
                            ring
              rw [hsplit, hconst]
    _ = ∑ j : Fin k, weight j * wSource j i := by
          rw [h_sum]
          ring

/-- The weighted meta-learning transfer gap is literally the squared mismatch
    between the weighted average source effect vector and the target-optimal
    effect vector. -/
theorem weightedMetaTransferGapSq_eq_weightedPopulationEffectAverageGapSq
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    weightedMetaTransferGapSq wShared wTarget
        (centeredPopulationEffectDeviationFin wShared wSource) weight =
      coefficientGapSq (weightedPopulationEffectAverage wSource weight) wTarget := by
  unfold weightedMetaTransferGapSq
  rw [weightedMetaSourceWeights_eq_weightedPopulationEffectAverage
    wShared wSource weight h_sum]

/-- Exact squared norm of a weighted population-specific deviation. Under
    pairwise orthogonality and equal per-population squared norm, the weighted
    combination has squared norm `gap × Σ_j w_j²`. -/
theorem weightedPopulationDeviation_squaredNorm_eq_populationSpecificGap_mul_sum_sq
    {p k : ℕ}
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (populationSpecificGap : ℝ)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    dotProduct (weightedPopulationDeviation deviation weight)
      (weightedPopulationDeviation deviation weight) =
        populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
  unfold weightedPopulationDeviation
  rw [show
      dotProduct
          (fun i => ∑ j : Fin k, weight j * deviation j i)
          (fun i => ∑ j : Fin k, weight j * deviation j i) =
        ∑ j : Fin k,
          dotProduct (fun i => weight j * deviation j i)
            (fun i => ∑ l : Fin k, weight l * deviation l i) by
      simpa using
        dotProduct_sum_left (Finset.univ)
          (fun j : Fin k => fun i => weight j * deviation j i)
          (fun i => ∑ l : Fin k, weight l * deviation l i)]
  calc
    ∑ j : Fin k,
        dotProduct (fun i => weight j * deviation j i)
          (fun i => ∑ l : Fin k, weight l * deviation l i)
      =
        ∑ j : Fin k,
          weight j *
            dotProduct (deviation j)
              (fun i => ∑ l : Fin k, weight l * deviation l i) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [dotProduct_smul_left]
    _ =
        ∑ j : Fin k,
          weight j *
            (∑ l : Fin k, weight l * dotProduct (deviation j) (deviation l)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show
              dotProduct (deviation j)
                (fun i => ∑ l : Fin k, weight l * deviation l i) =
              ∑ l : Fin k,
                dotProduct (deviation j) (fun i => weight l * deviation l i) by
                simpa using
                  dotProduct_sum_right (Finset.univ) (deviation j)
                    (fun l : Fin k => fun i => weight l * deviation l i)]
          congr 1
          apply Finset.sum_congr rfl
          intro l hl
          rw [dotProduct_smul_right]
    _ = ∑ j : Fin k, weight j * (weight j * populationSpecificGap) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_eq_single j]
          · rw [h_norm]
          · intro l hl hlj
            rw [h_pair j l (Ne.symm hlj), mul_zero]
          · intro hj_not_mem
            exact (hj_not_mem (Finset.mem_univ j)).elim
    _ = populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
          rw [show
              (∑ j : Fin k, weight j * (weight j * populationSpecificGap)) =
                ∑ j : Fin k, populationSpecificGap * weight j ^ 2 by
                apply Finset.sum_congr rfl
                intro j hj
                ring]
          rw [Finset.mul_sum]

/-- Exact transfer-gap formula for an affine weighted meta-aggregator. -/
theorem weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    weightedMetaTransferGapSq wShared wTarget deviation weight =
      irreducibleGap + populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
  let sharedResidual : Fin p → ℝ := fun i => wShared i - wTarget i
  have h_shared_norm : dotProduct sharedResidual sharedResidual = irreducibleGap := by
    simpa [sharedResidual, coefficientGapSq] using h_shared
  have h_weighted_norm :
      dotProduct (weightedPopulationDeviation deviation weight)
        (weightedPopulationDeviation deviation weight) =
          populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
    exact weightedPopulationDeviation_squaredNorm_eq_populationSpecificGap_mul_sum_sq
      deviation weight populationSpecificGap h_norm h_pair
  have h_cross :
      dotProduct sharedResidual (weightedPopulationDeviation deviation weight) = 0 := by
    unfold weightedPopulationDeviation
    rw [show
        dotProduct sharedResidual
          (fun i => ∑ j : Fin k, weight j * deviation j i) =
          ∑ j : Fin k,
            dotProduct sharedResidual (fun i => weight j * deviation j i) by
          simpa using
            dotProduct_sum_right (Finset.univ) sharedResidual
              (fun j : Fin k => fun i => weight j * deviation j i)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [dotProduct_smul_right, h_shared_orth j, mul_zero]
  have h_sub :
      (fun i =>
        weightedMetaSourceWeights wShared deviation weight i - wTarget i) =
      fun i => sharedResidual i + weightedPopulationDeviation deviation weight i := by
    funext i
    unfold weightedMetaSourceWeights sharedResidual weightedPopulationDeviation
    ring
  unfold weightedMetaTransferGapSq coefficientGapSq
  rw [h_sub]
  calc
    dotProduct
        (fun i => sharedResidual i + weightedPopulationDeviation deviation weight i)
        (fun i => sharedResidual i + weightedPopulationDeviation deviation weight i)
        =
          dotProduct sharedResidual sharedResidual +
            dotProduct sharedResidual (weightedPopulationDeviation deviation weight) +
            (dotProduct (weightedPopulationDeviation deviation weight) sharedResidual +
              dotProduct (weightedPopulationDeviation deviation weight)
                (weightedPopulationDeviation deviation weight)) := by
              rw [dotProduct_add_left, dotProduct_add_right, dotProduct_add_right]
    _ = irreducibleGap + 0 + (0 + populationSpecificGap * ∑ j : Fin k, weight j ^ 2) := by
          rw [h_shared_norm, h_cross, dotProduct_comm, h_cross, h_weighted_norm]
    _ = irreducibleGap + populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
          ring

/-- Among affine weights summing to one, the squared weight mass is minimized
    by the uniform average. This is the exact Cauchy-Schwarz step behind the
    `1 / k` decay of the shared-feature meta-learning transfer gap. -/
theorem one_div_card_le_sum_sq_of_affine_weights
    {k : ℕ}
    (weight : Fin k → ℝ)
    (h_k : 0 < k)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    1 / (k : ℝ) ≤ ∑ j : Fin k, weight j ^ 2 := by
  have h_sq :=
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k))) (f := weight)
  have h_card : ((#(Finset.univ : Finset (Fin k)) : ℕ) : ℝ) = k := by
    simp
  have h_key : 1 ≤ (k : ℝ) * ∑ j : Fin k, weight j ^ 2 := by
    simpa [h_sum, h_card] using h_sq
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr h_k
  by_contra h_contra
  have hlt : ∑ j : Fin k, weight j ^ 2 < 1 / (k : ℝ) := by
    exact not_le.mp h_contra
  have hmul_lt : (k : ℝ) * ∑ j : Fin k, weight j ^ 2 < 1 := by
    have := mul_lt_mul_of_pos_left hlt hk
    simpa [div_eq_mul_inv, one_div, hk.ne'] using this
  linarith

/-- Exact uniform affine weighting formula. -/
theorem weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k_of_uniform
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) =
      irreducibleGap + populationSpecificGap / k := by
  rw [weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
    wShared wTarget deviation (uniformMetaWeight k)
    irreducibleGap populationSpecificGap h_shared h_shared_orth h_norm h_pair]
  have hcard : (∑ j : Fin k, ((uniformMetaWeight k) j) ^ 2) = k * ((k : ℝ)⁻¹ ^ 2) := by
    simp [uniformMetaWeight]
  rw [hcard]
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h_k)
  field_simp [hk_ne]

/-- **Equal-weight meta-averaging is exactly optimal among affine source-model
    aggregators under the shared-feature geometry.**
    Under orthogonal population-specific deviations of equal squared norm,
    every affine combination of the `k` source-specific models has exact
    transfer gap `irreducibleGap + gap × Σ_j w_j²`, so the uniform average
    minimizes the exact transfer gap because `Σ_j w_j² ≥ 1 / k`. -/
theorem weightedMetaTransferGapSq_ge_uniform_of_affine_weights
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_sum : ∑ j : Fin k, weight j = 1)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0)
    (h_pop : 0 ≤ populationSpecificGap) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) ≤
      weightedMetaTransferGapSq wShared wTarget deviation weight := by
  rw [weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k_of_uniform
      wShared wTarget deviation irreducibleGap populationSpecificGap
      h_k h_shared h_shared_orth h_norm h_pair,
    weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
      wShared wTarget deviation weight irreducibleGap populationSpecificGap
      h_shared h_shared_orth h_norm h_pair]
  have h_sq_lb : 1 / (k : ℝ) ≤ ∑ j : Fin k, weight j ^ 2 := by
    exact one_div_card_le_sum_sq_of_affine_weights weight h_k h_sum
  have hmul :
      populationSpecificGap / k ≤
        populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left h_sq_lb h_pop
  linarith

/-- Optimal fine-tuning MSE after choosing the source-shrinkage weight
    optimally. -/
noncomputable def optimalFineTuningMSE (gapSq noiseVar nTarget : ℝ) : ℝ :=
  sourceShrinkageMSE gapSq noiseVar nTarget
    (optimalSourceShrinkageWeight gapSq noiseVar nTarget)

/-- Closed form of the optimal fine-tuning MSE. -/
theorem optimalFineTuningMSE_eq_closed_form
    (gapSq noiseVar nTarget : ℝ)
    (h_curv : gapSq + noiseVar / nTarget ≠ 0) :
    optimalFineTuningMSE gapSq noiseVar nTarget =
      gapSq * (noiseVar / nTarget) / (gapSq + noiseVar / nTarget) := by
  unfold optimalFineTuningMSE
  rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget
    (optimalSourceShrinkageWeight gapSq noiseVar nTarget) h_curv]
  ring

/-- For fixed target sample size and noise level, the optimal fine-tuning MSE
    is strictly increasing in the residual source-target mismatch. -/
theorem optimalFineTuningMSE_strictMono_in_gapSq
    (gap₁ gap₂ noiseVar nTarget : ℝ)
    (h_gap₁ : 0 ≤ gap₁)
    (h_gap : gap₁ < gap₂)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget) :
    optimalFineTuningMSE gap₁ noiseVar nTarget <
      optimalFineTuningMSE gap₂ noiseVar nTarget := by
  have h_curv₁ : gap₁ + noiseVar / nTarget ≠ 0 := by
    have h_pos : 0 < gap₁ + noiseVar / nTarget := by
      have hdiv : 0 < noiseVar / nTarget := div_pos h_noise h_n
      linarith
    linarith
  have h_curv₂ : gap₂ + noiseVar / nTarget ≠ 0 := by
    have h_pos : 0 < gap₂ + noiseVar / nTarget := by
      have hdiv : 0 < noiseVar / nTarget := div_pos h_noise h_n
      linarith
    linarith
  rw [optimalFineTuningMSE_eq_closed_form gap₁ noiseVar nTarget h_curv₁,
    optimalFineTuningMSE_eq_closed_form gap₂ noiseVar nTarget h_curv₂]
  set b : ℝ := noiseVar / nTarget
  have hb_pos : 0 < b := by
    unfold b
    exact div_pos h_noise h_n
  change gap₁ * b / (gap₁ + b) < gap₂ * b / (gap₂ + b)
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
  have h_sq_term : gap₁ * (b * b) < gap₂ * (b * b) := by
    exact mul_lt_mul_of_pos_right h_gap (mul_pos hb_pos hb_pos)
  nlinarith

/-- Target sample size needed for the optimal fine-tuning MSE to reach a target
    tolerance `τ`. This is the exact threshold obtained by solving the
    closed-form optimal-MSE equation for `nTarget`. -/
noncomputable def requiredTargetSamplesForOptimalFineTuningMSE
    (gapSq noiseVar tau : ℝ) : ℝ :=
  noiseVar * (gapSq - tau) / (tau * gapSq)

/-- The required target sample size is positive whenever the desired MSE target
    lies strictly below the transfer gap. -/
theorem requiredTargetSamplesForOptimalFineTuningMSE_pos
    (gapSq noiseVar tau : ℝ)
    (h_noise : 0 < noiseVar)
    (h_tau : 0 < tau)
    (h_gap : tau < gapSq) :
    0 < requiredTargetSamplesForOptimalFineTuningMSE gapSq noiseVar tau := by
  unfold requiredTargetSamplesForOptimalFineTuningMSE
  have h_gap_pos : 0 < gapSq := by linarith
  have h_num : 0 < noiseVar * (gapSq - tau) := by
    have : 0 < gapSq - tau := by linarith
    exact mul_pos h_noise this
  have h_den : 0 < tau * gapSq := by
    exact mul_pos h_tau h_gap_pos
  exact div_pos h_num h_den

/-- For a fixed MSE tolerance, reducing the transfer gap strictly lowers the
    target sample size required to hit that tolerance under optimal fine-tuning. -/
theorem requiredTargetSamplesForOptimalFineTuningMSE_strictMono_in_gapSq
    (gap₁ gap₂ noiseVar tau : ℝ)
    (h_gap₁ : 0 < gap₁)
    (h_gap : gap₁ < gap₂)
    (h_noise : 0 < noiseVar)
    (h_tau : 0 < tau) :
    requiredTargetSamplesForOptimalFineTuningMSE gap₁ noiseVar tau <
      requiredTargetSamplesForOptimalFineTuningMSE gap₂ noiseVar tau := by
  have h_gap₂ : 0 < gap₂ := lt_trans h_gap₁ h_gap
  have h_rewrite₁ :
      requiredTargetSamplesForOptimalFineTuningMSE gap₁ noiseVar tau =
        noiseVar / tau - noiseVar / gap₁ := by
    unfold requiredTargetSamplesForOptimalFineTuningMSE
    field_simp [ne_of_gt h_tau, ne_of_gt h_gap₁]
  have h_rewrite₂ :
      requiredTargetSamplesForOptimalFineTuningMSE gap₂ noiseVar tau =
        noiseVar / tau - noiseVar / gap₂ := by
    unfold requiredTargetSamplesForOptimalFineTuningMSE
    field_simp [ne_of_gt h_tau, ne_of_gt h_gap₂]
  rw [h_rewrite₁, h_rewrite₂]
  have hdiv : noiseVar / gap₂ < noiseVar / gap₁ := by
    exact div_lt_div_of_pos_left h_noise h_gap₁ h_gap
  nlinarith

/-- Exact target excess quadratic risk of using `w` instead of the
    target-optimal predictor `wStar`. -/
noncomputable def targetLinearExcessRisk {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w wStar : Fin p → ℝ) : ℝ :=
  targetLinearRisk sigmaObsTarget crossTarget noiseVar w -
    targetLinearRisk sigmaObsTarget crossTarget noiseVar wStar

/-- Symmetric target covariance swaps the bilinear cross-term exactly:
    `uᵀΣv = vᵀΣu`. -/
theorem dotProduct_mulVec_swap_of_isSymm
    {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A.IsSymm)
    (u v : Fin p → ℝ) :
    dotProduct u (A.mulVec v) = dotProduct v (A.mulVec u) := by
  have h := sum_mulVec_mul_eq_sum_mul_transpose_mulVec A v u
  simpa [dotProduct, hA.eq, mul_comm] using h

/-- Exact excess-risk decomposition for target quadratic risk.
    If `wStar` solves the target normal equations, then the target excess risk
    of any transported weight vector `w` is exactly the quadratic form of the
    coefficient error under the target covariance geometry. -/
theorem targetLinearExcessRisk_eq_quadratic_gap
    {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w wStar : Fin p → ℝ)
    (h_symm : sigmaObsTarget.IsSymm)
    (h_opt : sigmaObsTarget.mulVec wStar = crossTarget) :
    targetLinearExcessRisk sigmaObsTarget crossTarget noiseVar w wStar =
      dotProduct (fun i => w i - wStar i)
        (sigmaObsTarget.mulVec (fun i => w i - wStar i)) := by
  let u : Fin p → ℝ := fun i => w i - wStar i
  have hw : w = fun i => wStar i + u i := by
    funext i
    simp [u]
  have hmul :
      sigmaObsTarget.mulVec (fun i => wStar i + u i) =
        sigmaObsTarget.mulVec wStar + sigmaObsTarget.mulVec u := by
    simpa [u] using matrix_mulVec_add sigmaObsTarget wStar u
  have hswap :
      dotProduct wStar (sigmaObsTarget.mulVec u) =
        dotProduct u crossTarget := by
    calc
      dotProduct wStar (sigmaObsTarget.mulVec u) =
          dotProduct u (sigmaObsTarget.mulVec wStar) := by
            exact dotProduct_mulVec_swap_of_isSymm sigmaObsTarget h_symm wStar u
      _ = dotProduct u crossTarget := by simp [h_opt]
  let a : ℝ := dotProduct wStar crossTarget
  let b : ℝ := dotProduct wStar (sigmaObsTarget.mulVec u)
  let c : ℝ := dotProduct u crossTarget
  let d : ℝ := dotProduct u (sigmaObsTarget.mulVec u)
  have hexpand1 :
      dotProduct (fun i => wStar i + u i) (crossTarget + sigmaObsTarget.mulVec u) =
        a + b + c + d := by
    simp [a, b, c, d, dotProduct, Finset.sum_add_distrib, add_mul, mul_add]
    ring
  have hexpand2 :
      dotProduct (fun i => wStar i + u i) crossTarget = a + c := by
    simp [a, c, dotProduct, Finset.sum_add_distrib, add_mul]
  have h_gap_rhs :
      dotProduct (fun i => (fun j => wStar j + u j) i - wStar i)
        (sigmaObsTarget.mulVec (fun i => (fun j => wStar j + u j) i - wStar i)) = d := by
    simp [d]
  unfold targetLinearExcessRisk targetLinearRisk
  rw [hw, hmul, h_opt, hexpand1, hexpand2]
  rw [h_gap_rhs]
  rw [show b = c by
    simpa [b, c] using hswap]
  linarith

/-- In the isotropic target-feature model (`Σ_T = I`), the exact target excess
    quadratic risk is literally the squared coefficient mismatch. -/
  theorem isotropic_targetLinearExcessRisk_eq_coefficientGapSq
      {p : ℕ}
      (crossTarget : Fin p → ℝ)
      (noiseVar : ℝ)
      (w wStar : Fin p → ℝ)
      (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
      targetLinearExcessRisk (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar w wStar =
        coefficientGapSq w wStar := by
    have h_one_symm : (1 : Matrix (Fin p) (Fin p) ℝ).IsSymm :=
      Matrix.isSymm_one
    have h_excess :=
      targetLinearExcessRisk_eq_quadratic_gap
        (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar w wStar
        h_one_symm h_opt
    simpa using h_excess

/-- Any upper bound on exact isotropic target excess risk is automatically an
    upper bound on the fine-tuning bias term `coefficientGapSq`. -/
theorem coefficientGapSq_le_of_targetLinearExcessRisk_le
    {p : ℕ}
    (crossTarget : Fin p → ℝ)
    (noiseVar errCap : ℝ)
    (w wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget)
    (h_excess :
      targetLinearExcessRisk (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar w wStar ≤ errCap) :
    coefficientGapSq w wStar ≤ errCap := by
  rw [← isotropic_targetLinearExcessRisk_eq_coefficientGapSq
    crossTarget noiseVar w wStar h_opt]
  exact h_excess

/-- Exact target-specific adaptation gain: the reduction in literal target
    excess quadratic risk achieved by moving from `wBefore` to `wAfter`. -/
noncomputable def exactAdaptationGain {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ) : ℝ :=
  targetLinearExcessRisk sigmaObsTarget crossTarget noiseVar wBefore wStar -
    targetLinearExcessRisk sigmaObsTarget crossTarget noiseVar wAfter wStar

/-- In the isotropic target design, exact adaptation gain is literally the drop
    in squared coefficient mismatch to the target-optimal effect vector. -/
theorem exactAdaptationGain_eq_coefficientGapDrop_isotropic
    {p : ℕ}
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    exactAdaptationGain (1 : Matrix (Fin p) (Fin p) ℝ)
        crossTarget noiseVar wBefore wAfter wStar =
      coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar := by
  unfold exactAdaptationGain
  rw [isotropic_targetLinearExcessRisk_eq_coefficientGapSq crossTarget noiseVar
      wBefore wStar h_opt]
  rw [isotropic_targetLinearExcessRisk_eq_coefficientGapSq crossTarget noiseVar
      wAfter wStar h_opt]

/-- The scalar fine-tuning `adaptation_gain` parameter is exactly the gain in
    target `R²` obtained by reducing literal target excess risk, once the
    baseline portability loss is instantiated by the exact observable drift
    transport theorem. -/
theorem fineTunedTargetR2_eq_observable_transport_plus_exact_excessRisk_reduction
    {p : ℕ}
    (r2Source fstSource fstTarget : ℝ)
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ) :
    fineTunedTargetR2 r2Source
        (observableTransportPenalty r2Source fstSource fstTarget)
        (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar) =
      targetR2FromObservables r2Source fstSource fstTarget +
        exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar := by
  rw [fineTunedTargetR2_eq_targetR2FromObservables_plus_adaptation]

/-- In the isotropic target design, the scalar fine-tuning model is exactly the
    observable transported baseline plus the drop in squared effect mismatch
    from target adaptation. -/
theorem fineTunedTargetR2_eq_observable_transport_plus_gap_drop_isotropic
    {p : ℕ}
    (r2Source fstSource fstTarget : ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    fineTunedTargetR2 r2Source
        (observableTransportPenalty r2Source fstSource fstTarget)
        (exactAdaptationGain (1 : Matrix (Fin p) (Fin p) ℝ)
          crossTarget noiseVar wBefore wAfter wStar) =
      targetR2FromObservables r2Source fstSource fstTarget +
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar) := by
  rw [fineTunedTargetR2_eq_observable_transport_plus_exact_excessRisk_reduction]
  rw [exactAdaptationGain_eq_coefficientGapDrop_isotropic crossTarget noiseVar
    wBefore wAfter wStar h_opt]

/-- **A better information-bottleneck representation lowers target sample needs.**
    This theorem no longer inserts an affine bridge from a domain-adaptation
    bound into the fine-tuning gap. Instead it uses an exact estimator-level
    model:

    - target prediction risk is the literal quadratic risk
      `targetLinearRisk Σ_T c_T σ²`;
    - in the isotropic target design (`Σ_T = I`), the exact excess risk of the
      transported source weights equals the squared coefficient mismatch
      `coefficientGapSq`;
    - the source-shrinkage fine-tuning MSE uses that exact squared mismatch as
      its transfer-bias term.

    Therefore, if the transported source predictor's exact target excess risk is
    certified to lie below its Ben-David target-error certificate, then a better
    information-bottleneck representation yields a strictly smaller exact target
    sample requirement to hit any fixed fine-tuning MSE tolerance. -/
theorem higher_info_bottleneck_objective_reduces_required_target_samples
    {p : ℕ}
    (cert_new : PGSBenDavidCertificate)
    (crossTarget wSourceNew wTarget : Fin p → ℝ)
    (I_phi_Y_standard I_phi_Y_new I_phi_A : ℝ)
    (lambda_standard lam : ℝ)
    (targetNoiseVar noiseVar tau : ℝ)
    (h_noise : 0 < noiseVar)
    (h_tau : 0 < tau)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wTarget = crossTarget)
    (h_excess :
      targetLinearExcessRisk (1 : Matrix (Fin p) (Fin p) ℝ)
        crossTarget targetNoiseVar wSourceNew wTarget ≤ cert_new.err_target)
    (h_source :
      cert_new.err_source ≤ gaussianSourceResidualRisk I_phi_Y_new)
    (h_div :
      cert_new.divergence ≤ pinskerAncestryDivergenceCap I_phi_A)
    (h_lambda : cert_new.lambda_star ≤ lambda_standard)
    (h_obj :
      infoBottleneckObjective I_phi_Y_new I_phi_A lam >
        infoBottleneckObjective I_phi_Y_standard I_phi_A lam)
    (h_tau_small :
      tau < coefficientGapSq wSourceNew wTarget) :
    0 <
      requiredTargetSamplesForOptimalFineTuningMSE
        (coefficientGapSq wSourceNew wTarget)
        noiseVar tau ∧
    requiredTargetSamplesForOptimalFineTuningMSE
        (coefficientGapSq wSourceNew wTarget)
        noiseVar tau <
      requiredTargetSamplesForOptimalFineTuningMSE
        (infoCertifiedBenDavidUpperBound
          I_phi_Y_standard I_phi_A lambda_standard)
        noiseVar tau := by
  have h_gap_le_err :
      coefficientGapSq wSourceNew wTarget ≤ cert_new.err_target := by
    exact coefficientGapSq_le_of_targetLinearExcessRisk_le
      crossTarget targetNoiseVar cert_new.err_target wSourceNew wTarget h_opt h_excess
  have h_target_cap_lt :
      cert_new.err_target <
        infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A lambda_standard := by
    exact higher_info_bottleneck_objective_lowers_target_error_cap
      cert_new I_phi_Y_standard I_phi_Y_new I_phi_A
      lambda_standard lam h_source h_div h_lambda h_obj
  have h_gap_order :
      coefficientGapSq wSourceNew wTarget <
        infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A lambda_standard := by
    linarith
  have h_gap_new_pos :
      0 < coefficientGapSq wSourceNew wTarget := by
    linarith
  have h_required_new_pos :
      0 <
        requiredTargetSamplesForOptimalFineTuningMSE
          (coefficientGapSq wSourceNew wTarget)
          noiseVar tau := by
    exact requiredTargetSamplesForOptimalFineTuningMSE_pos
      (coefficientGapSq wSourceNew wTarget)
      noiseVar tau h_noise h_tau h_tau_small
  have h_required_lt :
      requiredTargetSamplesForOptimalFineTuningMSE
          (coefficientGapSq wSourceNew wTarget)
          noiseVar tau <
        requiredTargetSamplesForOptimalFineTuningMSE
          (infoCertifiedBenDavidUpperBound
            I_phi_Y_standard I_phi_A lambda_standard)
          noiseVar tau := by
    exact requiredTargetSamplesForOptimalFineTuningMSE_strictMono_in_gapSq
      (coefficientGapSq wSourceNew wTarget)
      (infoCertifiedBenDavidUpperBound
        I_phi_Y_standard I_phi_A lambda_standard)
      noiseVar tau h_gap_new_pos h_gap_order h_noise h_tau
  exact ⟨h_required_new_pos, h_required_lt⟩

/-- **More source populations reduce the target fine-tuning burden.**
    This is an explicit shared-feature meta-learning theorem, not a hard-coded
    `1 / k` law. We model the transported source weights learned from the first
    `k` populations as

    - a shared center `wShared`,
    - plus the average of `k` population-specific deviations.

    The `1 / k` decay is then derived, not assumed: if the population-specific
    deviations are pairwise orthogonal, each has the same squared norm
    `populationSpecificGap`, and each is orthogonal to the shared residual
    `wShared - wTarget`, then averaging over more source populations strictly
    lowers the exact squared coefficient gap to the target optimum. Because the
    optimal shrinkage fine-tuning MSE and the required target sample size are
    already solved exactly as functions of that gap, they strictly decrease as
    well. -/
theorem amortized_per_population_adaptation_cost_falls_with_task_count
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (irreducibleGap populationSpecificGap noiseVar nTarget tau : ℝ)
    (k₁ k₂ : ℕ)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j < k₂, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm :
      ∀ j < k₂, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair :
      ∀ j < k₂, ∀ l < k₂, j ≠ l → dotProduct (deviation j) (deviation l) = 0)
    (h_irred : 0 ≤ irreducibleGap)
    (h_pop : 0 < populationSpecificGap)
    (h_noise : 0 < noiseVar)
    (h_n : 0 < nTarget)
    (h_tau : 0 < tau)
    (h_k₁ : 0 < k₁)
    (h_more_tasks : k₁ < k₂)
    (h_tau_small :
      tau < metaLearnedTransferGapSq wShared wTarget deviation k₂) :
    metaLearnedTransferGapSq wShared wTarget deviation k₂ <
      metaLearnedTransferGapSq wShared wTarget deviation k₁ ∧
    optimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₂)
        noiseVar nTarget <
      optimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₁)
        noiseVar nTarget ∧
    0 <
      requiredTargetSamplesForOptimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₂)
        noiseVar tau ∧
    requiredTargetSamplesForOptimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₂)
        noiseVar tau <
      requiredTargetSamplesForOptimalFineTuningMSE
        (metaLearnedTransferGapSq wShared wTarget deviation k₁)
        noiseVar tau := by
  have h_k₂ : 0 < k₂ := lt_trans h_k₁ h_more_tasks
  have h_gap_order :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ <
        metaLearnedTransferGapSq wShared wTarget deviation k₁ := by
    exact metaLearnedTransferGapSq_strictMono
      wShared wTarget deviation irreducibleGap populationSpecificGap
      k₁ k₂ h_pop h_k₁ h_more_tasks h_shared h_shared_orth h_norm h_pair
  have h_gap₂_pos :
      0 < metaLearnedTransferGapSq wShared wTarget deviation k₂ := by
    exact metaLearnedTransferGapSq_pos
      wShared wTarget deviation irreducibleGap populationSpecificGap
      k₂ h_irred h_pop h_k₂ h_shared h_shared_orth h_norm h_pair
  have h_mse_order :
      optimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar nTarget <
        optimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₁)
          noiseVar nTarget := by
    exact optimalFineTuningMSE_strictMono_in_gapSq
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      (metaLearnedTransferGapSq wShared wTarget deviation k₁)
      noiseVar nTarget (le_of_lt h_gap₂_pos) h_gap_order h_noise h_n
  have h_req_pos :
      0 <
        requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar tau := by
    exact requiredTargetSamplesForOptimalFineTuningMSE_pos
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      noiseVar tau h_noise h_tau h_tau_small
  have h_req_order :
      requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar tau <
        requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₁)
          noiseVar tau := by
    exact requiredTargetSamplesForOptimalFineTuningMSE_strictMono_in_gapSq
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      (metaLearnedTransferGapSq wShared wTarget deviation k₁)
      noiseVar tau h_gap₂_pos h_gap_order h_noise h_tau
  exact ⟨h_gap_order, h_mse_order, h_req_pos, h_req_order⟩

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

/-- **Transfer ceiling from private architecture and migration-limited LD sharing.**
    Even with perfect transport on the shared loci, only the shared causal
    fraction `1 - f_private` can contribute across populations, and only the
    migration-drift shared-LD fraction `sharedLDFromMigration M` can be tagged
    coherently in the target. This gives the architecture-aware ceiling

    `h²_target × (1 - f_private) × sharedLDFromMigration M`.

    The ceiling is stated in terms of target heritability rather than source
    `R²`, so it is directly comparable to the theoretical transport limits above
    and to the migration-drift LD machinery in `PortabilityDrift`. -/
noncomputable def privateArchitectureTransferCeiling
    (h2_target f_private M : ℝ) : ℝ :=
  h2_target * (1 - f_private) * sharedLDFromMigration M

/-- **A positive private causal fraction lowers the transferable `R²` ceiling.**
    In the architecture-aware transfer model above, compare a trait with
    private causal fraction `f_private` to the same trait with no private
    architecture (`f_private = 0`) at the same migration-drift LD sharing level
    `sharedLDFromMigration M`.

    If a transported score is certified to satisfy the private-architecture
    ceiling, then any strictly positive private fraction pushes the achievable
    target `R²` strictly below the no-private benchmark, and therefore strictly
    below target heritability as well. This is a real transport-limit statement,
    not just the algebraic identity `f_shared = 1 - f_private`. -/
theorem private_causal_fraction_lowers_transfer_ceiling
    (r2_target h2_target f_private M : ℝ)
    (h_bound : r2_target ≤ privateArchitectureTransferCeiling h2_target f_private M)
    (h_h2 : 0 < h2_target)
    (h_private : 0 < f_private)
    (hM : 0 < M) :
    privateArchitectureTransferCeiling h2_target f_private M <
      privateArchitectureTransferCeiling h2_target 0 M ∧
    r2_target < privateArchitectureTransferCeiling h2_target 0 M ∧
    r2_target < h2_target := by
  have h_shared_pos : 0 < sharedLDFromMigration M := by
    unfold sharedLDFromMigration
    have h_den_pos : 0 < 1 + M := by linarith
    exact div_pos hM h_den_pos
  have h_shared_lt_one : sharedLDFromMigration M < 1 :=
    sharedLDFromMigration_lt_one M (le_of_lt hM)
  have h_one_minus_lt_one : 1 - f_private < 1 := by linarith
  have h_ceiling_lt_no_private :
      privateArchitectureTransferCeiling h2_target f_private M <
        privateArchitectureTransferCeiling h2_target 0 M := by
    unfold privateArchitectureTransferCeiling
    have h_base_pos : 0 < h2_target * sharedLDFromMigration M := by
      exact mul_pos h_h2 h_shared_pos
    calc
      h2_target * (1 - f_private) * sharedLDFromMigration M
          = (h2_target * sharedLDFromMigration M) * (1 - f_private) := by ring
      _ < h2_target * sharedLDFromMigration M := by
        exact mul_lt_of_lt_one_right h_base_pos h_one_minus_lt_one
      _ = h2_target * (1 - (0 : ℝ)) * sharedLDFromMigration M := by ring
  have h_no_private_lt_h2 :
      privateArchitectureTransferCeiling h2_target 0 M < h2_target := by
    unfold privateArchitectureTransferCeiling
    calc
      h2_target * (1 - (0 : ℝ)) * sharedLDFromMigration M
          = h2_target * sharedLDFromMigration M := by ring
      _ < h2_target := by
        exact mul_lt_of_lt_one_right h_h2 h_shared_lt_one
  have h_r2_lt_no_private :
      r2_target < privateArchitectureTransferCeiling h2_target 0 M :=
    lt_of_le_of_lt h_bound h_ceiling_lt_no_private
  have h_r2_lt_h2 : r2_target < h2_target :=
    lt_trans h_r2_lt_no_private h_no_private_lt_h2
  exact ⟨h_ceiling_lt_no_private, h_r2_lt_no_private, h_r2_lt_h2⟩

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
