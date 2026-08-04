/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Calibrator.OpenQuestions
import Calibrator.TransplantationStability

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
    where β_causal are the modelled causal effects in that population.

    Empirical status: UNTESTED. -/
noncomputable def pgsPhenoCov {m : ℕ} (β_weights β_causal : Fin m → ℝ)
    (ld : Fin m → Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin m, β_weights i * ld i j * β_causal j

/-- Genetic variance induced by a shared LD kernel.

    Empirical status: UNTESTED. -/
noncomputable def sharedLDGeneticVariance {m : ℕ}
    (β : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) : ℝ :=
  pgsPhenoCov β β ld

/-- Heritability induced by a shared LD kernel.

    Empirical status: UNTESTED. -/
noncomputable def sharedLDHeritability {m : ℕ}
    (β : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sharedLDGeneticVariance β ld / var_y

/-- **sharedLDHeritability at zero var_y, named.** A trait with no phenotypic variance has no
heritability. Lean returns `0`, reporting a trait with no genetic basis rather than a trait with no
variance at all -- and the two have opposite implications for whether a score can ever work.
Consumers must require `var_y ≠ 0`. -/
theorem sharedLDHeritability_zero_vary_is_junk {m : ℕ} (β : Fin m → ℝ)
    (ld : Fin m → Fin m → ℝ) :
    sharedLDHeritability β ld 0 = 0 := by
  unfold sharedLDHeritability
  simp

/-- R² of a PGS: the squared correlation between PGS and phenotype.
    R² = Cov(PGS, Y)² / (Var(PGS) × Var(Y)).

    Empirical status: UNTESTED. -/
noncomputable def pgsR2 (cov_pgs_y : ℝ) (var_pgs var_y : ℝ) : ℝ :=
  cov_pgs_y ^ 2 / (var_pgs * var_y)

/-- **pgsR2 at zero var_pgs, named.** A score with no variance has no `R²`. Lean returns `0`,
which reads as a score that varies and fails, rather than a score that is constant. Consumers
must require `var_pgs ≠ 0`. -/
theorem pgsR2_zero_varpgs_is_junk (cov_pgs_y : ℝ) (var_y : ℝ) :
    pgsR2 cov_pgs_y 0 var_y = 0 := by
  unfold pgsR2
  simp

/-- **`R²` is invariant under rescaling the score.** Multiplying the polygenic score by `c`
multiplies its covariance with the outcome by `c` and its variance by `c²`, and the ratio is
unchanged. This is the defining property of a squared correlation: it is why `R²` is comparable
across scores on different scales, and a body that failed it would depend on the arbitrary units
the score happens to be reported in. -/
theorem pgsR2_scale_invariant (cov_pgs_y var_pgs var_y c : ℝ) (hc : c ≠ 0) :
    pgsR2 (c * cov_pgs_y) (c ^ 2 * var_pgs) var_y = pgsR2 cov_pgs_y var_pgs var_y := by
  unfold pgsR2
  rw [mul_pow, show c ^ 2 * var_pgs * var_y = c ^ 2 * (var_pgs * var_y) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **One body, two names, tied.** `DGP.explainedR2FromTransportMoments` is the
same squared-correlation coordinate. -/
theorem pgsR2_eq_explainedR2FromTransportMoments (cov_pgs_y var_pgs var_y : ℝ) :
    pgsR2 cov_pgs_y var_pgs var_y =
      explainedR2FromTransportMoments cov_pgs_y var_pgs var_y := rfl

/-- Source-population `R²` of the score that uses the source's own effects as
    weights under a shared LD kernel.

    Empirical status: UNTESTED. -/
noncomputable def sourceTruthR2SharedLD {m : ℕ}
    (β_source : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  pgsR2 (sharedLDGeneticVariance β_source ld)
    (sharedLDGeneticVariance β_source ld) var_y

/-- Target-population transported `R²` of the source-weighted score under a
    shared LD kernel.

    Empirical status: UNTESTED. -/
noncomputable def transportedTargetR2SharedLD {m : ℕ}
    (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  pgsR2 (pgsPhenoCov β_source β_target ld)
    (sharedLDGeneticVariance β_source ld) var_y

/-- Effect correlation induced by a shared LD kernel.

    Empirical status: UNTESTED. -/
noncomputable def ldEffectGeneticCorrelation {m : ℕ}
    (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) : ℝ :=
  pgsPhenoCov β_source β_target ld /
    Real.sqrt (sharedLDGeneticVariance β_source ld * sharedLDGeneticVariance β_target ld)

/-- Euclidean / independent-variant genetic correlation between source and
    target effect-size vectors. This is the diagonal-LD specialization of the
    shared-LD correlation above.

    Empirical status: UNTESTED. -/
noncomputable def effectGeneticCorrelation {m : ℕ} (β_source β_target : Fin m → ℝ) : ℝ :=
  (∑ i : Fin m, β_source i * β_target i) /
    Real.sqrt ((∑ i : Fin m, β_source i ^ 2) * (∑ i : Fin m, β_target i ^ 2))

/-- **effectGeneticCorrelation at an empty variant panel, named.** Both effect sums are empty, so
the numerator and the radicand vanish together and the square root divides by zero. Lean returns
`0`: no genetic correlation between two traits measured on no variants, which is what two
genuinely unrelated traits also give. Consumers must exclude it by hypothesis. -/
theorem effectGeneticCorrelation_empty_panel_is_junk (β_source β_target : Fin 0 → ℝ) :
    effectGeneticCorrelation β_source β_target = 0 := by
  unfold effectGeneticCorrelation
  norm_num

/-- Standardized diagonal LD operator: independent variants with unit variance.

    Empirical status: UNTESTED. -/
def standardizedDiagonalLD {m : ℕ} : Fin m → Fin m → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Additive genetic variance in the standardized diagonal-LD model. -/
noncomputable def additiveGeneticVariance {m : ℕ} (β : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, β i ^ 2

/-- Additive heritability `h² = V_A / V_Y` in the standardized diagonal-LD model.

    Empirical status: UNTESTED. -/
noncomputable def additiveHeritability {m : ℕ} (β : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  additiveGeneticVariance β / var_y

/-- **additiveHeritability at zero var_y, named.** The same zero-phenotypic-variance branch as
`sharedLDHeritability`, reached through a different genetic-variance definition, and reported
identically. Consumers must require `var_y ≠ 0`. -/
theorem additiveHeritability_zero_vary_is_junk {m : ℕ} (β : Fin m → ℝ) :
    additiveHeritability β 0 = 0 := by
  unfold additiveHeritability
  simp

/-- Source-population `R²` of the score that uses source effect sizes as weights in the
    standardized diagonal-LD model.

    Empirical status: UNTESTED. -/
noncomputable def sourceSelfR2DiagonalLD {m : ℕ}
    (β_source : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sourceTruthR2SharedLD β_source standardizedDiagonalLD var_y

/-- Target-population transported `R²` of the source-weighted score in the
    standardized diagonal-LD model.

    Empirical status: UNTESTED. -/
noncomputable def transportedTargetR2DiagonalLD {m : ℕ}
    (β_source β_target : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  transportedTargetR2SharedLD β_source β_target standardizedDiagonalLD var_y

/-- **Cauchy-Schwarz for effect-size inner product.**
    |Σᵢ β_source_i × β_target_i|² ≤ (Σᵢ β_source_i²) × (Σᵢ β_target_i²).
    This is the discrete Cauchy-Schwarz inequality applied to the vectors
    of effect sizes, and is the core mathematical ingredient for the
    portability bound.

    Proved from Mathlib's `sum_mul_sq_le_sq_mul_sq` over `Finset.univ`, which
    is the finite-sum form of Cauchy-Schwarz and needs no Hilbert-space
    structure on `Fin m → ℝ`. -/
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
theorem portability_bound_sharedLD_of_target_h2_le_source_h2 {m : ℕ}
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
theorem portability_bound_diagonal_ld_of_target_h2_le_source_h2 {m : ℕ}
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
    portability_bound_sharedLD_of_target_h2_le_source_h2 β_s β_t standardizedDiagonalLD var_y
      h_var_y h_s_nonzero' h_t_nonzero' h_shared
  simpa [ldEffectGeneticCorrelation_standardizedDiagonalLD_eq_effectGeneticCorrelation] using
    h_bound

/-- Proportional effect vectors scale additive genetic variance by the squared
    proportionality constant. -/
theorem additiveGeneticVariance_proportional {m : ℕ}
    (β : Fin m → ℝ) (c : ℝ) :
    additiveGeneticVariance (fun i ↦ c * β i) = c ^ 2 * additiveGeneticVariance β := by
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
    additiveHeritability (fun i ↦ c * β i) var_y =
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
    (effectGeneticCorrelation β (fun i ↦ c * β i)) ^ 2 = 1 := by
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
      0 < additiveGeneticVariance (fun i ↦ c * β i) := by
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
            ∑ i : Fin m, (fun i ↦ c * β i) i ^ 2)) ^ 2 = 1
  change
    (c * additiveGeneticVariance β /
        Real.sqrt
          (additiveGeneticVariance β *
            additiveGeneticVariance (fun i ↦ c * β i))) ^ 2 = 1
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
    transportedTargetR2DiagonalLD β_s (fun i ↦ rg * β_s i) var_y =
      rg ^ 2 * sourceSelfR2DiagonalLD β_s var_y := by
  have h_t_nonzero :
      0 < additiveGeneticVariance (fun i ↦ rg * β_s i) := by
    rw [additiveGeneticVariance_proportional]
    have h_rg_sq_pos : 0 < rg ^ 2 := by
      nlinarith [sq_pos_iff.mpr h_rg]
    exact mul_pos h_rg_sq_pos h_s_nonzero
  rw [transportedTargetR2_eq_rgSq_mul_targetH2_diagonalLD
    β_s (fun i ↦ rg * β_s i) var_y h_var_y h_s_nonzero h_t_nonzero]
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
    transportedTargetR2DiagonalLD β_s (fun i ↦ rg * β_s i) var_y /
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

Reference: Ben-David, Blitzer, Crammer, Kulesza, Pereira and Vaughan (2010),
"A theory of learning from different domains", Machine Learning 79:151-175 -- the
source of the eps_S(h) + d_H(S,T) + lambda* bound formalized below. The mapping of
that bound onto ancestry domains, and the relation between H-divergence and Fst,
are derived here, not imported from it.
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

/-- Ben-David upper-bound functional `ε_S(h) + d_H(S,T) + λ*`. -/
def benDavidUpperBound (err_source divergence lambda_star : ℝ) : ℝ :=
  err_source + divergence + lambda_star

/-! **Deleted: `divergence_increases_with_fst`.**

The name's claim — that H-divergence between ancestry populations is monotone in `F_ST` —
lives entirely in prose, together with the linear model `divergence = c * F_ST` that would
make it precise. Neither is derived anywhere in this corpus, and asserting the *shape* of
that relation is not a small assumption: it is what would let a measured `F_ST` be
converted into a term of the Ben-David bound at all. Multiplying an inequality by a
positive constant is the only result such a theorem holds. -/

/-- **The Ben-David bound is a sum, pinned.** The comparison with the information-certified
bound below is one-sided and holds for any body dominated by it. The three terms enter additively
and with equal weight: source error, domain divergence and the joint-optimal residual. -/
theorem benDavidUpperBound_reference :
    benDavidUpperBound 1 2 3 = 6 := by
  unfold benDavidUpperBound
  norm_num

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

/-- **IW effective sample size.**
    n_eff = (Σ wᵢ)² / (Σ wᵢ²) ≤ n.
    The effective sample size decreases with the divergence
    between source and target (larger weights). -/
noncomputable def importanceWeightESS (sum_w sum_w_sq : ℝ) : ℝ :=
  sum_w ^ 2 / sum_w_sq

/-- **importanceWeightESS at zero sum_w_sq, named.** With zero total squared weight there are no
samples and the effective sample size is undefined. Lean returns `0`, which is the correct-looking
answer for the wrong reason and hides the empty-sample case inside the degenerate-weights case.
Consumers must require `sum_w_sq ≠ 0`. -/
theorem importanceWeightESS_zero_sumwsq_is_junk (sum_w : ℝ) :
    importanceWeightESS sum_w 0 = 0 := by
  unfold importanceWeightESS
  simp

/-- **The effective size recovers the squared total weight.** -/
theorem importanceWeightESS_mul_sumSq (sum_w sum_w_sq : ℝ) (h : sum_w_sq ≠ 0) :
    importanceWeightESS sum_w sum_w_sq * sum_w_sq = sum_w ^ 2 := by
  unfold importanceWeightESS
  field_simp

/-- **IW ESS ≤ n, from an actual weight vector, with Cauchy-Schwarz proved.**

    `iw_ess_le_n` used to state this for free scalars `sum_w` and `sum_w_sq` and take
    `sum_w ^ 2 ≤ n * sum_w_sq` as a hypothesis. That hypothesis is Cauchy-Schwarz, which
    is the only mathematical content the bound has; assuming it left the theorem as
    `div_le_iff₀`, and left `n`, `sum_w` and `sum_w_sq` as three unrelated reals with no
    stated connection to any set of weights. In particular nothing forced `sum_w` to be
    the sum of the same weights whose squares make `sum_w_sq`, so the scalar form was
    satisfied by triples that correspond to no weight vector at all.

    Stated over `w : Fin n → ℝ` the hypothesis is discharged from Mathlib
    (`sq_sum_le_card_mul_sum_sq`, the `f = g` case of Chebyshev's sum inequality) and `n`
    is the actual sample size rather than a free variable. -/
theorem importanceWeightESS_le_card {n : ℕ} (w : Fin n → ℝ)
    (h_sq_pos : 0 < ∑ i, w i ^ 2) :
    importanceWeightESS (∑ i, w i) (∑ i, w i ^ 2) ≤ (n : ℝ) := by
  unfold importanceWeightESS
  rw [div_le_iff₀ h_sq_pos]
  simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := w))

/-- **The ESS is nonnegative**, since it is a square over a positive sum. -/
theorem importanceWeightESS_nonneg {n : ℕ} (w : Fin n → ℝ)
    (h_sq_pos : 0 < ∑ i, w i ^ 2) :
    0 ≤ importanceWeightESS (∑ i, w i) (∑ i, w i ^ 2) := by
  unfold importanceWeightESS
  positivity

/-- **Equal weights attain the bound**: the ESS of a constant weight vector is exactly
    `n`, so the inequality above is sharp and not merely an envelope. Requires `c ≠ 0`,
    since all-zero weights leave the ESS a `0/0`. -/
theorem importanceWeightESS_of_const {n : ℕ} (c : ℝ) (hc : c ≠ 0) (hn : 0 < n) :
    importanceWeightESS (∑ _i : Fin n, c) (∑ _i : Fin n, c ^ 2) = (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold importanceWeightESS
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_pow]
  field_simp

/-! **Deleted: `iw_ess_decreases_with_divergence` and
`iw_positive_weight_variance_reduces_ess`.**

These theorems are absent on purpose. They attach to a second formula for one quantity,
and it is the formula that does not exist. `importanceWeightESS` — the definition this
section is built around, and the one `validation/popgen_defs/transfer_battery.py`
exercises — is `(Σw)²/Σw²`. Both named theorems are about `n / (1 + v)`. That expression is
defined nowhere in this corpus and is proved equal to nothing that is. The identification
`(Σw)²/Σw² = n/(1 + Var(w))` needs the weights normalized to mean one, and no such
normalization is stated or assumed, so a result named for the effective sample size
establishes nothing about it.

Stripped of the naming, `iw_ess_decreases_with_divergence` is `div_lt_div_of_pos_left` and
`iw_positive_weight_variance_reduces_ess` is `div_lt_iff₀` — Mathlib in domain costume,
neither used anywhere. Divergence and `F_ST` appear in neither statement, and the chain
from ancestry divergence to weight variance lives only in prose ("as Fst increases, the
importance weights become more variable"), formalized nowhere.

`importanceWeightESS_le_card` above stands in their place, about the definition that
exists and that the validation battery tests. A genuine monotonicity result — that more
variable weights give a smaller ESS — is a real and provable statement over `w`, and is
the thing to add here if it is wanted. Until then it stays unasserted. -/

/-- **Doubly robust estimation combines IW with model adaptation.**
    DR estimator: if either the weighting model or the outcome model is
    asymptotically correct, and the other nuisance component remains
    uniformly bounded, the target-population estimator is consistent. -/
def AsymptoticallyZero (err : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |err n| < ε

/-- An estimator sequence converges to the target parameter in absolute error. -/
def AsymptoticallyConsistent (est : ℕ → ℝ) (truth : ℝ) : Prop :=
  AsymptoticallyZero (fun n ↦ est n - truth)

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
  have h_mul_le : |f n| * |g n| ≤ |f n| * C :=
    mul_le_mul_of_nonneg_left hg_le (abs_nonneg _)
  have h_mul_le' : |f n| * C ≤ (ε / (C + 1)) * C :=
    mul_le_mul_of_nonneg_right hf_small.le hC_nn
  have hC_lt : C < C + 1 := by linarith
  have h_scaled_lt : (ε / (C + 1)) * C < (ε / (C + 1)) * (C + 1) :=
    mul_lt_mul_of_pos_left hC_lt h_scaled_pos
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
      (fun n ↦ est_dr n - θ) bias_iw_only bias_model_only
      h_dr_error_bound h_model_bounded h_iw_zero
  · exact asymptoticallyZero_of_abs_le_mul
      (fun n ↦ est_dr n - θ) bias_model_only bias_iw_only
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

/-- **PCA projection as a simple representation.**
    Projecting genotypes onto top PCs separates ancestry from
    trait-relevant variation. Removing top PCs reduces ancestry
    signal but may also remove trait signal.
    Net target error is modeled as ancestry-induced bias plus a weighted
    penalty for discarded trait signal. -/
def pcaSignalLossPenalty
    (signalBaseline signalRetained lossWeight : ℝ) : ℝ :=
  lossWeight * (signalBaseline - signalRetained)

/-- **The signal-loss penalty's orientation and scale, pinned.** This definition carries no
result of its own. Two units of weight on two units of lost signal is a penalty of four: the
weight multiplies the loss rather than the retained signal, and the difference runs baseline
minus retained so that losing signal costs rather than pays. -/
theorem pcaSignalLossPenalty_reference :
    pcaSignalLossPenalty 3 1 2 = 4 := by
  unfold pcaSignalLossPenalty
  norm_num

/-- Reduction in ancestry-induced target bias achieved by removing ancestry PCs. -/
def pcaBiasReduction
    (ancestryBiasWith ancestryBiasWithout : ℝ) : ℝ :=
  ancestryBiasWith - ancestryBiasWithout

/-- **The bias-reduction sign convention, pinned.** This definition carries no result of its own,
and the whole content of the definition is which way the subtraction runs. A reduction is
positive when correcting for principal components leaves LESS ancestry bias than not correcting;
the reversed body reports successful correction as damage. -/
theorem pcaBiasReduction_positive_when_correction_helps :
    pcaBiasReduction 3 1 = 2 := by
  unfold pcaBiasReduction
  norm_num

/-- Linearized target error after PCA adjustment: ancestry bias plus a
    weighted trait-signal loss penalty. -/
def pcaNetTargetError
    (ancestryBias signalBaseline signalRetained lossWeight : ℝ) : ℝ :=
  ancestryBias + pcaSignalLossPenalty signalBaseline signalRetained lossWeight

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem pcaNetTargetError_at_reference_point :
    pcaNetTargetError 1 1 1 1 = 1 := by
  norm_num [pcaNetTargetError, pcaSignalLossPenalty]



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
  -- All four comparisons are the one difference identity read four ways.  Written out,
  -- each carried its own copy of the same two-step rearrangement.
  have hdiff := pca_target_error_difference
    ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight
  refine ⟨?_, ?_, ?_, ?_⟩ <;> constructor <;> intro h <;> linarith

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
            lossWeight * (signal_with - signal_without) :=
        mul_le_mul_of_nonneg_right hge hgap_pos.le
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
                  (signal_with - signal_without)) * (signal_with - signal_without) :=
          mul_lt_mul_of_pos_right h hgap_pos
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
            pcaBiasReduction ancestry_bias_with ancestry_bias_without :=
        (eq_div_iff hgap_ne).1 h
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
    err_k ≤ min err_k_plus_1 err_k_minus_1 :=
  le_min h_local_min_right h_local_min_left

/-- Information-bottleneck objective `I(φ(X); Y) - λ I(φ(X); A)`. -/
def infoBottleneckObjective (I_phi_Y I_phi_A lam : ℝ) : ℝ :=
  I_phi_Y - lam * I_phi_A

/-- **The information-bottleneck trade-off, pinned.** This definition carries no result of its
own. The ancestry term is subtracted and weighted, so a Lagrange multiplier of two on equal
outcome and ancestry information gives an objective of minus one: past `lam = 1` the objective
prefers discarding predictive information to buying ancestry invariance. -/
theorem infoBottleneckObjective_reference :
    infoBottleneckObjective 1 1 2 = -1 := by
  unfold infoBottleneckObjective
  norm_num

/-- Closed-form normalized Gaussian source residual risk from mutual information.
    For a jointly Gaussian source trait `Y` and representation `φ(X)` with
    `Var(Y)=1`, the residual variance fraction is under this model `exp(-2 I(φ(X);Y))`.

    Empirical status: UNTESTED. -/
noncomputable def gaussianSourceResidualRisk (I_phi_Y : ℝ) : ℝ :=
  Real.exp (-2 * I_phi_Y)

/-- **The Gaussian residual risk's rate, pinned.** `gaussianSourceResidualRisk_strictAnti` says
the risk decreases in the retained information, which is true of EVERY decreasing function and
so fixes no exponent. Half a nat of information about the outcome cuts the residual risk by
exactly one e-fold, which is what fixes the factor two in the exponent. -/
theorem gaussianSourceResidualRisk_half_nat :
    gaussianSourceResidualRisk (1 / 2) = Real.exp (-1) := by
  unfold gaussianSourceResidualRisk
  norm_num

/-- Pinsker-certified ancestry-divergence cap from mutual information.
    This is the standard `√(2 I)` envelope obtained by combining binary-domain
    total-variation control with Pinsker's inequality.

    Empirical status: UNTESTED. -/
noncomputable def pinskerAncestryDivergenceCap (I_phi_A : ℝ) : ℝ :=
  Real.sqrt (2 * I_phi_A)

/-- **pinskerAncestryDivergenceCap at a negative mutual information, named.** Mutual information
cannot be negative, but a plug-in estimate of it can be. `Real.sqrt` is junk-zero on the negative
radicand, so the cap is reported as zero: the tightest possible bound, certifying that no
ancestry information leaks, produced by an estimate that was invalid. Consumers must exclude it
by hypothesis. -/
theorem pinskerAncestryDivergenceCap_negative_information_is_junk :
    pinskerAncestryDivergenceCap (-1) = 0 := by
  unfold pinskerAncestryDivergenceCap
  rw [show (2 : ℝ) * (-1) = -2 by ring]
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-- **The Pinsker cap's constant, pinned.** `pinskerAncestryDivergenceCap_mono` fixes the
direction and holds for `sqrt (c * I)` at every positive `c`. Half a nat of ancestry information
caps the total-variation divergence at one, which is what fixes `c = 2` -- and, incidentally,
marks where the cap stops saying anything, since total variation never exceeds one. -/
theorem pinskerAncestryDivergenceCap_half_nat :
    pinskerAncestryDivergenceCap (1 / 2) = 1 := by
  unfold pinskerAncestryDivergenceCap
  norm_num

/-- Information-certified Ben-David upper envelope built from:
    - exact Gaussian source residual risk,
    - a Pinsker ancestry-divergence cap,
    - the irreducible `λ*` term. -/
noncomputable def infoCertifiedBenDavidUpperBound
    (I_phi_Y I_phi_A lambda_star : ℝ) : ℝ :=
  gaussianSourceResidualRisk I_phi_Y +
    pinskerAncestryDivergenceCap I_phi_A + lambda_star

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem infoCertifiedBenDavidUpperBound_at_reference_point :
    infoCertifiedBenDavidUpperBound 0 0 0 = 1 := by
  norm_num [infoCertifiedBenDavidUpperBound, gaussianSourceResidualRisk,
    pinskerAncestryDivergenceCap]



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

/-- An exact information certificate upper-bounds the Ben-David functional —
    but only for the source error and divergence the certificate actually
    dominates, which is why the name carries the condition. -/
theorem benDavidUpperBound_le_infoCertifiedBenDavidUpperBound_of_dominated_components
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

end FeatureRepresentation


/-!
## Fine-Tuning and Few-Shot Adaptation

Adapting a source-population PGS to a target population with
limited target-population data.
-/

section FineTuning

/-- Fine-tuned target `R²` in a simple additive penalty model. -/
def fineTunedTargetR2 (r2_source divergence_penalty adaptation_gain : ℝ) : ℝ :=
  r2_source - divergence_penalty + adaptation_gain

/-- **Divergence and adaptation enter with opposite signs and equal weight.**

The three-term budget is additive, so a divergence penalty is cancelled exactly by an equal
adaptation gain and the fine-tuned accuracy returns to the source's. That symmetry is the content
of the model -- it says the two effects are commensurable and trade one for one -- and a body
weighting them differently would still be monotone in each argument, which is all the surrounding
comparisons require. -/
theorem fineTunedTargetR2_cancels (r2_source d : ℝ) :
    fineTunedTargetR2 r2_source d d = r2_source := by
  unfold fineTunedTargetR2
  ring

/-- Target-trained `R²` in a simple additive estimation-penalty model. -/
def scratchTargetR2 (oracle_target_r2 estimation_penalty : ℝ) : ℝ :=
  oracle_target_r2 - estimation_penalty

/-- Canonical deployed target `R²` for transfer/adaptation methods: start from
    an explicit transported target baseline, add any target-specific adaptation
    gain, and subtract any finite-sample estimation penalty. This is the shared
    target-metric surface that both fine-tuning and scratch training reduce to. -/
def deployedTransferTargetR2
    (transported_r2 adaptation_gain estimation_penalty : ℝ) : ℝ :=
  transported_r2 + adaptation_gain - estimation_penalty

/-- **deployedTransferTargetR2 pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the coefficients a
one-sided bound or an invariance leaves free. -/
theorem deployedTransferTargetR2_at_reference_point :
    deployedTransferTargetR2 (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold deployedTransferTargetR2
  norm_num

/-- The target-only oracle gap above an explicit transported target baseline. This
    is the amount of target-specific gain available beyond that transported
    `R²` before any estimation penalty is paid. -/
def oracleTransportAdaptationGain
    (transported_r2 oracle_target_r2 : ℝ) : ℝ :=
  oracle_target_r2 - transported_r2

/-- **The adaptation gain's orientation, pinned.** This definition carries no result of its own,
and its entire content is the direction of the subtraction. The gain is what refitting in the
target would buy over transporting the source score, so it is positive when the oracle beats the
transported score. -/
theorem oracleTransportAdaptationGain_positive_when_oracle_wins :
    oracleTransportAdaptationGain 1 3 = 2 := by
  unfold oracleTransportAdaptationGain
  norm_num

/-- Portability penalty as the literal gap between a source baseline and an
    explicitly supplied transported target baseline. -/
noncomputable def transportPenalty
    (source_r2 transported_r2 : ℝ) : ℝ :=
  source_r2 - transported_r2

/-- **The transport penalty's orientation, pinned.** This definition carries no result of its
own. The penalty is what transporting COSTS relative to performance in the source population, so
it is positive when the score does worse after transport. -/
theorem transportPenalty_positive_when_transport_costs :
    transportPenalty 3 1 = 2 := by
  unfold transportPenalty
  norm_num

/-- The additive fine-tuning model is exactly the transported target baseline
    plus any additional target-specific adaptation gain once the portability
    penalty is instantiated by the literal source-minus-transported gap. -/
theorem fineTunedTargetR2_eq_transportedR2_plus_adaptation
    (source_r2 transported_r2 adaptationGain : ℝ) :
    fineTunedTargetR2 source_r2
        (transportPenalty source_r2 transported_r2)
        adaptationGain =
      transported_r2 + adaptationGain := by
  unfold fineTunedTargetR2 transportPenalty
  ring

/-- Fine-tuning is exactly the canonical deployed-transfer target `R²` with an
    explicit transported baseline, target-specific adaptation gain, and zero
    estimation penalty. -/
theorem fineTunedTargetR2_eq_deployedTransferTargetR2
    (source_r2 transported_r2 adaptationGain : ℝ) :
    fineTunedTargetR2 source_r2
        (transportPenalty source_r2 transported_r2)
        adaptationGain =
      deployedTransferTargetR2 transported_r2 adaptationGain 0 := by
  rw [fineTunedTargetR2_eq_transportedR2_plus_adaptation]
  unfold deployedTransferTargetR2
  ring

/-- Target-only oracle `R²` in the diagonal-LD architecture model. This is the
    target self-prediction ceiling, i.e. target additive heritability.

    Empirical status: UNTESTED. -/
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

/-- Scratch training is also exactly the canonical deployed-transfer target
    `R²`: the baseline is the chosen transported target `R²`, the adaptation
    gain is the oracle gap above that transported baseline, and the estimator
    pays the explicit estimation penalty. -/
theorem scratchTargetR2_eq_deployedTransferTargetR2
    (transported_r2 oracle_target_r2 estimation_penalty : ℝ) :
    scratchTargetR2 oracle_target_r2 estimation_penalty =
      deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2)
        estimation_penalty := by
  unfold scratchTargetR2 deployedTransferTargetR2 oracleTransportAdaptationGain
  ring

/-- The canonical deployed-transfer target `R²` can always be rewritten as the
    target oracle ceiling minus any residual post-transfer gap and minus any
    explicit estimation penalty. This is the common algebraic form behind the
    scratch, fine-tuning, and meta-learning specializations below. -/
theorem deployedTransferTargetR2_eq_oracle_minus_residualGap_minus_estimationPenalty
    (transported_r2 oracle_target_r2 residual_gap estimation_penalty : ℝ) :
    deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2 - residual_gap)
        estimation_penalty =
      oracle_target_r2 - residual_gap - estimation_penalty := by
  unfold deployedTransferTargetR2 oracleTransportAdaptationGain
  ring

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
    `noiseVar / nTarget`.

    Regime: `noiseVar / nTarget ≤ oracle_target_r2`. The subtraction is a
    first-order estimation penalty and is only a model of `R²` while it stays
    below the ceiling it is subtracted from. Outside that regime it returns
    values no `R²` can take: at `oracle_target_r2 = 1e-4`, `noiseVar = 1000`,
    `nTarget = 1` it is `-1000`.
    `sampleLimitedScratchTargetR2_negative_of_small_sample` exhibits the escape
    and `sampleLimitedScratchTargetR2_nonneg` states the condition that
    excludes it. `usableScratchTargetR2` is the clamped variant for callers who
    cannot discharge the regime; it is offered rather than substituted here
    because clamping would assert that the estimator still attains `0` at
    sample sizes where this model has simply left its domain, and that is a
    modelling claim the development has no evidence for.

    Empirical status: UNTESTED inside the regime; FALSIFIED outside it, where
    the value is not an `R²`. -/
noncomputable def sampleLimitedScratchTargetR2
    (oracle_target_r2 noiseVar nTarget : ℝ) : ℝ :=
  scratchTargetR2 oracle_target_r2 (noiseVar / nTarget)

/-- **The range escape, exhibited.**  Once the estimation penalty exceeds the
oracle ceiling the modelled `R²` goes negative, without bound. -/
theorem sampleLimitedScratchTargetR2_negative_of_small_sample
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : oracle_target_r2 < noiseVar / nTarget) :
    sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget < 0 := by
  unfold sampleLimitedScratchTargetR2 scratchTargetR2
  linarith

/-- **The condition that keeps it an `R²`.**  This is the regime declared on the
definition, stated as a hypothesis a caller can discharge. -/
theorem sampleLimitedScratchTargetR2_nonneg
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : noiseVar / nTarget ≤ oracle_target_r2) :
    0 ≤ sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget := by
  unfold sampleLimitedScratchTargetR2 scratchTargetR2
  linarith

/-- **Clamped scratch-trained target `R²`.**

The same model, floored at `0`: a predictor is never worse than the population
mean in the `R²` a deployment would report, because the mean is always
available. Use this where the sample size is not known to satisfy the regime on
`sampleLimitedScratchTargetR2`; the two agree inside it
(`usableScratchTargetR2_eq_of_nonneg`), and `0` is attained rather than
approached, which is the correct behaviour at sample sizes carrying no usable
signal.

    Empirical status: UNTESTED. -/
noncomputable def usableScratchTargetR2
    (oracle_target_r2 noiseVar nTarget : ℝ) : ℝ :=
  max 0 (sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget)

/-- Inside the regime the clamp does nothing, so no downstream result changes
meaning. -/
theorem usableScratchTargetR2_eq_of_nonneg
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : noiseVar / nTarget ≤ oracle_target_r2) :
    usableScratchTargetR2 oracle_target_r2 noiseVar nTarget =
      sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar nTarget :=
  max_eq_right (sampleLimitedScratchTargetR2_nonneg oracle_target_r2 noiseVar nTarget h)

/-- The clamped variant never leaves `[0, ∞)`, which is the range property the
unclamped model lacks. -/
theorem usableScratchTargetR2_nonneg
    (oracle_target_r2 noiseVar nTarget : ℝ) :
    0 ≤ usableScratchTargetR2 oracle_target_r2 noiseVar nTarget :=
  le_max_left _ _

/-- **The zero floor is attained**, at any sample size where the estimation
penalty reaches the oracle ceiling: no usable signal, and the model says so
rather than reporting a negative number. -/
theorem usableScratchTargetR2_eq_zero_of_exhausted
    (oracle_target_r2 noiseVar nTarget : ℝ)
    (h : oracle_target_r2 ≤ noiseVar / nTarget) :
    usableScratchTargetR2 oracle_target_r2 noiseVar nTarget = 0 := by
  unfold usableScratchTargetR2
  apply max_eq_left
  unfold sampleLimitedScratchTargetR2 scratchTargetR2
  linarith

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

/-- Sample-limited scratch training is the canonical deployed-transfer target
    `R²` with an explicit transported baseline, the oracle target gap above
    that baseline, and the explicit finite-sample penalty `noiseVar / nTarget`. -/
theorem sampleLimitedScratchTargetR2_eq_deployedTransferTargetR2
    {m : ℕ}
    (β_target : Fin m → ℝ)
    (var_y transported_r2 noiseVar nTarget : ℝ) :
    sampleLimitedScratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) noiseVar nTarget =
      deployedTransferTargetR2
        transported_r2
        (oracleTransportAdaptationGain
          transported_r2
          (targetOracleR2DiagonalLD β_target var_y))
        (noiseVar / nTarget) := by
  unfold sampleLimitedScratchTargetR2
  simpa using scratchTargetR2_eq_deployedTransferTargetR2
    transported_r2
    (targetOracleR2DiagonalLD β_target var_y)
    (noiseVar / nTarget)

/-- In the diagonal-LD target architecture model, sample-limited scratch
    training is exactly an explicit transported target baseline plus the target
    heritability gap above that transported baseline, minus the finite-sample
    estimation penalty. -/
theorem sampleLimitedScratchTargetR2_eq_coreTransport_plus_targetHeritabilityGap_minus_noise
    {m : ℕ}
    (β_target : Fin m → ℝ)
    (var_y transported_r2 noiseVar nTarget : ℝ)
    (h_var_y : 0 < var_y)
    (h_beta_nonzero : 0 < additiveGeneticVariance β_target) :
    sampleLimitedScratchTargetR2 (targetOracleR2DiagonalLD β_target var_y) noiseVar nTarget =
      deployedTransferTargetR2
        transported_r2
        (additiveHeritability β_target var_y -
          transported_r2)
        (noiseVar / nTarget) := by
  rw [sampleLimitedScratchTargetR2_eq_targetHeritability_minus_noise_over_n_diagonalLD
    β_target var_y noiseVar nTarget h_var_y h_beta_nonzero]
  unfold deployedTransferTargetR2
  ring

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
        fineTunedTargetR2 r2_source divergence_penalty adaptation_gain :=
    sub_pos.mpr h_gap
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

/-- **sourceShrinkageMSE at its junk point, named.** With no target samples the estimation term
`noiseVar / nTarget` is unbounded and no shrinkage weight is safe. The divisor is zero, that
term vanishes, and the mean squared error reduces to the bias term alone -- so the optimiser is
free to take `lam` toward one and is told it costs nothing. Consumers must exclude the argument
that makes the guard vanish. -/
theorem sourceShrinkageMSE_zero_target_samples_is_junk (gapSq noiseVar lam : ℝ) :
    sourceShrinkageMSE gapSq noiseVar 0 lam = gapSq * lam ^ 2 := by
  unfold sourceShrinkageMSE
  simp

/-- **Exact optimizer of the source-shrinkage MSE.**
    In the explicit bias-variance model above, the unique minimizer is
    `(noiseVar / nTarget) / (gapSq + noiseVar / nTarget)`. This is derived from the
    quadratic objective, not assumed. -/
noncomputable def optimalSourceShrinkageWeight (gapSq noiseVar nTarget : ℝ) : ℝ :=
  (noiseVar / nTarget) / (gapSq + noiseVar / nTarget)

/-- **optimalSourceShrinkageWeight where its denominator vanishes, named.** The guard `gapSq +
noiseVar / nTarget` is zero at `gapSq = 0`, `noiseVar = 0`, `nTarget = 1`. Lean returns `0`
there rather than the value the modelled quantity takes, and no type error marks the point.
Consumers must require `gapSq + noiseVar / nTarget ≠ 0`. -/
theorem optimalSourceShrinkageWeight_at_gapsq0noisevar0ntarget1_is_junk :
    optimalSourceShrinkageWeight 0 0 1 = 0 := by
  unfold optimalSourceShrinkageWeight
  norm_num

/-- **With no transfer gap the optimal weight is one: keep the source entirely.** The quadratic
decomposition below holds around whatever the optimum is and does not say where it sits; this
does, and it is the endpoint that distinguishes a shrinkage rule from its complement. -/
theorem optimalSourceShrinkageWeight_no_gap (noiseVar nTarget : ℝ)
    (h : noiseVar / nTarget ≠ 0) :
    optimalSourceShrinkageWeight 0 noiseVar nTarget = 1 := by
  unfold optimalSourceShrinkageWeight
  rw [zero_add, div_self h]

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
    have hdiv_nonneg : 0 ≤ noiseVar / nTarget :=
      div_nonneg h_noise (le_of_lt h_n)
    linarith
  by_cases h_curv : gapSq + noiseVar / nTarget = 0
  · have hdiv_zero : noiseVar / nTarget = 0 := by
      have hdiv_nonneg : 0 ≤ noiseVar / nTarget :=
        div_nonneg h_noise (le_of_lt h_n)
      linarith
    have h_gap_zero : gapSq = 0 := by
      have hdiv_nonneg : 0 ≤ noiseVar / nTarget :=
        div_nonneg h_noise (le_of_lt h_n)
      linarith
    have h_noise_zero : noiseVar = 0 := by
      have hn_ne : nTarget ≠ 0 := ne_of_gt h_n
      have hmul : (noiseVar / nTarget) * nTarget = 0 := by
        simpa using congrArg (fun x : ℝ ↦ x * nTarget) hdiv_zero
      calc
        noiseVar = (noiseVar / nTarget) * nTarget := by
          field_simp [hn_ne]
        _ = 0 := hmul
    simp [sourceShrinkageMSE, optimalSourceShrinkageWeight, h_gap_zero, h_noise_zero]
  · rw [sourceShrinkageMSE_eq_optimal_plus_square gapSq noiseVar nTarget lam h_curv]
    have hsquare_nonneg :
        0 ≤ (gapSq + noiseVar / nTarget) *
          (lam - optimalSourceShrinkageWeight gapSq noiseVar nTarget)^2 :=
      mul_nonneg hcoeff_nonneg (sq_nonneg _)
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
      have hdiv_pos : 0 < noiseVar / (n₁ : ℝ) :=
        div_pos h_noise hn₁_real
      linarith
    linarith
  have h_curv₂ : gapSq + noiseVar / (n₂ : ℝ) ≠ 0 := by
    have hn₂_real : 0 < (n₂ : ℝ) := Nat.cast_pos.mpr h_n₂
    have h_pos : 0 < gapSq + noiseVar / (n₂ : ℝ) := by
      have hdiv_pos : 0 < noiseVar / (n₂ : ℝ) :=
        div_pos h_noise hn₂_real
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
    have h_pos : 0 < gapSq + noiseVar / nTarget :=
      add_pos h_gapSq (div_pos h_noise h_n)
    linarith
  have h_denom_pos : 0 < nTarget * gapSq + noiseVar := by
    nlinarith
  rw [optimalSourceShrinkageWeight_eq_closed_form gapSq noiseVar nTarget h_n h_curv]
  constructor
  · intro h
    have h_cross : noiseVar ≤ (1 / 2 : ℝ) * (nTarget * gapSq + noiseVar) :=
      (div_le_iff₀ h_denom_pos).1 h
    nlinarith
  · intro h
    exact (div_le_iff₀ h_denom_pos).2 (by nlinarith)

/-- Squared coefficient mismatch between a transported source predictor and the
    target-optimal linear predictor. This is the exact bias term appearing in
    the source-shrinkage fine-tuning MSE. -/
noncomputable def coefficientGapSq {p : ℕ}
    (wSource wTarget : Fin p → ℝ) : ℝ :=
  dotProduct (fun i ↦ wSource i - wTarget i) (fun i ↦ wSource i - wTarget i)

/-- The squared coefficient gap is a sum of squares, so it is never negative.
    Proved here rather than assumed, so no downstream theorem has to receive
    `0 ≤ irreducibleGap` as a gift. -/
theorem coefficientGapSq_nonneg {p : ℕ} (wSource wTarget : Fin p → ℝ) :
    0 ≤ coefficientGapSq wSource wTarget := by
  have h :
      coefficientGapSq wSource wTarget =
        ∑ i : Fin p, (wSource i - wTarget i) * (wSource i - wTarget i) := rfl
  rw [h]
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

/-- Sum of the first `k` population-specific deviations around a shared
    representation center. -/
noncomputable def populationDeviationSum {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ Finset.sum (Finset.range k) (fun j ↦ deviation j i)

/-- Mean population-specific deviation after training on the first `k`
    source populations. -/
noncomputable def meanPopulationDeviation {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ (k : ℝ)⁻¹ * populationDeviationSum deviation k i

/-- Meta-learned source weights: a shared center plus the average
    source-population-specific deviation. -/
noncomputable def metaLearnedSourceWeights {p : ℕ}
    (wShared : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ wShared i + meanPopulationDeviation deviation k i

/-- Population-specific effect deviation around a shared ancestral-effect
    center. This is the closed-form effect-architecture object whose average is used
    by the meta-learning block below.

    The population index is left general. This was two definitions with identical
    bodies, one indexed by `ℕ` and one by `Fin k`; nothing in the deviation depends on
    which, so the index is a parameter rather than a reason for a second definition.

    Empirical status: UNTESTED. -/
noncomputable def centeredPopulationEffectDeviation {p : ℕ} {ι : Type*}
    (wShared : Fin p → ℝ)
    (wSource : ι → Fin p → ℝ) : ι → Fin p → ℝ :=
  fun j i ↦ wSource j i - wShared i

/-- Exact mean effect vector over the first `k` source populations. -/
noncomputable def sourcePopulationMeanWeights {p : ℕ}
    (wSource : ℕ → Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  fun i ↦ (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j ↦ wSource j i))

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
  have hsum_const : Finset.sum (Finset.range k) (fun _ ↦ wShared i) = (k : ℝ) * wShared i := by
    simp
  calc
    wShared i + (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j ↦ wSource j i - wShared i))
        = wShared i + (k : ℝ)⁻¹ *
            (Finset.sum (Finset.range k) (fun j ↦ wSource j i) -
              Finset.sum (Finset.range k) (fun _ ↦ wShared i)) := by
              rw [Finset.sum_sub_distrib]
    _ = wShared i + (k : ℝ)⁻¹ *
            (Finset.sum (Finset.range k) (fun j ↦ wSource j i) - (k : ℝ) * wShared i) := by
              rw [hsum_const]
    _ = (k : ℝ)⁻¹ * (Finset.sum (Finset.range k) (fun j ↦ wSource j i)) := by
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
    dotProduct (fun i ↦ u i + v i) w = dotProduct u w + dotProduct v w := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

/-- Dot product distributes over addition in the right argument. -/
theorem dotProduct_add_right {p : ℕ}
    (u v w : Fin p → ℝ) :
    dotProduct u (fun i ↦ v i + w i) = dotProduct u v + dotProduct u w := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

/-- Dot product is symmetric over `ℝ`. -/
theorem dotProduct_comm {p : ℕ}
    (u v : Fin p → ℝ) :
    dotProduct u v = dotProduct v u := by
  simp [dotProduct, mul_comm]

/-- Pulling a scalar out of the left dot-product argument. -/
theorem dotProduct_smul_left {p : ℕ}
    (c : ℝ) (u v : Fin p → ℝ) :
    dotProduct (fun i ↦ c * u i) v = c * dotProduct u v := by
  unfold dotProduct
  rw [show (∑ i, (c * u i) * v i) = ∑ i, c * (u i * v i) by
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  rw [← Finset.mul_sum]

/-- Pulling a scalar out of the right dot-product argument. -/
theorem dotProduct_smul_right {p : ℕ}
    (u v : Fin p → ℝ) (c : ℝ) :
    dotProduct u (fun i ↦ c * v i) = c * dotProduct u v := by
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
    dotProduct (fun i ↦ Finset.sum s (fun j ↦ f j i)) v =
      Finset.sum s (fun j ↦ dotProduct (f j) v) := by
  unfold dotProduct
  rw [show (∑ i, (Finset.sum s (fun j ↦ f j i)) * v i) =
      ∑ i, Finset.sum s (fun j ↦ f j i * v i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]]
  rw [Finset.sum_comm]

/-- Dot product of a fixed vector with a finite sum of vectors. -/
theorem dotProduct_sum_right {α : Type*} [DecidableEq α] {p : ℕ}
    (s : Finset α)
    (u : Fin p → ℝ)
    (f : α → Fin p → ℝ) :
    dotProduct u (fun i ↦ Finset.sum s (fun j ↦ f j i)) =
      Finset.sum s (fun j ↦ dotProduct u (f j)) := by
  unfold dotProduct
  rw [show (∑ i, u i * (Finset.sum s (fun j ↦ f j i))) =
      ∑ i, Finset.sum s (fun j ↦ u i * f j i) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]]
  rw [Finset.sum_comm]

/-- Prefix-sum recursion for population-specific deviations. -/
theorem populationDeviationSum_succ {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ) :
    populationDeviationSum deviation (k + 1) =
      fun i ↦ populationDeviationSum deviation k i + deviation k i := by
  funext i
  simp [populationDeviationSum, Finset.sum_range_succ]

/-- If the new population-specific deviation is orthogonal to each earlier
    deviation, then it is orthogonal to their sum. -/
theorem dotProduct_populationDeviationSum_last_eq_zero {p : ℕ}
    (deviation : ℕ → Fin p → ℝ) (k : ℕ)
    (h_pair : ∀ j < k, dotProduct (deviation j) (deviation k) = 0) :
    dotProduct (populationDeviationSum deviation k) (deviation k) = 0 := by
  rw [show dotProduct (populationDeviationSum deviation k) (deviation k) =
      Finset.sum (Finset.range k) (fun j ↦ dotProduct (deviation j) (deviation k)) by
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
      have h_norm_prev :
          ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap := by
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
          dotProduct (deviation k) (deviation k) = populationSpecificGap :=
        h_norm k (Nat.lt_succ_self k)
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
    dotProduct (fun i ↦ (k : ℝ)⁻¹ * populationDeviationSum deviation k i)
        (fun i ↦ (k : ℝ)⁻¹ * populationDeviationSum deviation k i)
        =
          ((k : ℝ)⁻¹)^2 *
            dotProduct (populationDeviationSum deviation k)
              (populationDeviationSum deviation k) := by
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
      Finset.sum (Finset.range k) (fun j ↦ dotProduct u (deviation j)) by
      simpa [populationDeviationSum] using
        dotProduct_sum_right (Finset.range k) u deviation]
  have hsum :
      Finset.sum (Finset.range k) (fun j ↦ dotProduct u (deviation j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact h_orth j (Finset.mem_range.mp hj)
  rw [hsum]
  ring

/-- **The meta-learning deviation geometry, named once.**

Five statements below are conditioned on the same three facts about the population-specific
deviations: each is orthogonal to the shared residual, each has the same squared norm, and
distinct ones are orthogonal.  Written out at each theorem that block was five identical
lines repeated five times, and restricting it to a smaller task count was another nine.
It is one geometry, so it is one structure, with its own restriction lemma. -/
structure MetaLearningDeviations {p : ℕ} (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ) (populationSpecificGap : ℝ) (k : ℕ) : Prop where
  /-- Every deviation is orthogonal to the shared residual. -/
  shared_orth : ∀ j < k, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0
  /-- Every deviation has the same squared norm. -/
  norm_eq : ∀ j < k, dotProduct (deviation j) (deviation j) = populationSpecificGap
  /-- Distinct deviations are orthogonal. -/
  pairwise : ∀ j < k, ∀ l < k, j ≠ l → dotProduct (deviation j) (deviation l) = 0

/-- **The geometry is inhabited.**  A theorem conditioned on a bundle nothing satisfies is
true and empty.  One source population with zero deviation from the shared centre satisfies
all three conditions, so the statements below are statements about something. -/
theorem metaLearningDeviations_witness {p : ℕ} (wShared wTarget : Fin p → ℝ) :
    MetaLearningDeviations wShared wTarget (fun _ _ ↦ 0) 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j _
    simp [dotProduct]
  · intro j _
    simp [dotProduct]
  · intro j hj l hl hne
    exact absurd (show j = l by omega) hne

/-- The geometry at `k₂` populations restricts to any smaller task count. -/
theorem MetaLearningDeviations.mono {p : ℕ} {wShared wTarget : Fin p → ℝ}
    {deviation : ℕ → Fin p → ℝ} {populationSpecificGap : ℝ} {k₁ k₂ : ℕ}
    (h : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂)
    (hle : k₁ ≤ k₂) :
    MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₁ :=
  ⟨fun j hj ↦ h.shared_orth j (lt_of_lt_of_le hj hle),
    fun j hj ↦ h.norm_eq j (lt_of_lt_of_le hj hle),
    fun j hj l hl hne ↦
      h.pairwise j (lt_of_lt_of_le hj hle) l (lt_of_lt_of_le hl hle) hne⟩

/-- Exact transfer-gap formula for the shared-feature meta-learning model.
    The shared center's own residual gap is `coefficientGapSq wShared wTarget`
    — computed, not assumed. If in addition each population-specific deviation
    has squared norm `populationSpecificGap`, those deviations are pairwise
    orthogonal, and each is orthogonal to the shared residual, then averaging
    over `k` source populations yields the exact residual gap
    `coefficientGapSq wShared wTarget + populationSpecificGap / k`. -/
theorem metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k) :
    metaLearnedTransferGapSq wShared wTarget deviation k =
      coefficientGapSq wShared wTarget + populationSpecificGap / k := by
  obtain ⟨h_shared_orth, h_norm, h_pair⟩ := hdev
  obtain ⟨irreducibleGap, h_shared⟩ :
      ∃ g : ℝ, coefficientGapSq wShared wTarget = g := ⟨_, rfl⟩
  rw [h_shared]
  let sharedResidual : Fin p → ℝ := fun i ↦ wShared i - wTarget i
  have h_shared_norm : dotProduct sharedResidual sharedResidual = irreducibleGap := by
    simpa [sharedResidual, coefficientGapSq] using h_shared
  have h_mean_norm :
      dotProduct (meanPopulationDeviation deviation k) (meanPopulationDeviation deviation k) =
        populationSpecificGap / k :=
    meanPopulationDeviation_squaredNorm_eq_populationSpecificGap_div_k
      deviation populationSpecificGap k h_k h_norm h_pair
  have h_cross :
      dotProduct sharedResidual (meanPopulationDeviation deviation k) = 0 :=
    dotProduct_meanPopulationDeviation_eq_zero
      sharedResidual deviation k h_shared_orth
  have h_sub :
      (fun i ↦
        (metaLearnedSourceWeights wShared deviation k i) - wTarget i) =
        fun i ↦ sharedResidual i + meanPopulationDeviation deviation k i := by
    funext i
    unfold metaLearnedSourceWeights sharedResidual
    ring
  unfold metaLearnedTransferGapSq coefficientGapSq
  rw [h_sub]
  calc
    dotProduct
        (fun i ↦ sharedResidual i + meanPopulationDeviation deviation k i)
        (fun i ↦ sharedResidual i + meanPopulationDeviation deviation k i)
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
    transfer gap `coefficientGapSq wShared wTarget + populationSpecificGap / k`
    to the target optimum. -/
theorem sourcePopulationMeanEffectGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (wSource : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_k : 0 < k)
    (hdev : MetaLearningDeviations wShared wTarget
      (centeredPopulationEffectDeviation wShared wSource) populationSpecificGap k) :
    coefficientGapSq (sourcePopulationMeanWeights wSource k) wTarget =
      coefficientGapSq wShared wTarget + populationSpecificGap / k := by
  rw [← metaLearnedTransferGapSq_eq_sourcePopulationMeanEffectGapSq
    wShared wTarget wSource k h_k]
  exact metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    wShared wTarget (centeredPopulationEffectDeviation wShared wSource)
    populationSpecificGap k h_k hdev

/-- More source populations strictly reduce the exact residual transfer gap in
    the shared-feature meta-learning model, because the averaged population-
    specific deviation has exact squared norm `gap / k`. -/
theorem metaLearnedTransferGapSq_strictMono {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k₁ k₂ : ℕ)
    (h_pop : 0 < populationSpecificGap)
    (h_k₁ : 0 < k₁)
    (h_more : k₁ < k₂)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂) :
    metaLearnedTransferGapSq wShared wTarget deviation k₂ <
      metaLearnedTransferGapSq wShared wTarget deviation k₁ := by
  have h_k₂ : 0 < k₂ := lt_trans h_k₁ h_more
  have h_formula₂ :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ =
        coefficientGapSq wShared wTarget + populationSpecificGap / k₂ :=
    metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
      wShared wTarget deviation populationSpecificGap
      k₂ h_k₂ hdev
  have h_formula₁ :
      metaLearnedTransferGapSq wShared wTarget deviation k₁ =
        coefficientGapSq wShared wTarget + populationSpecificGap / k₁ :=
    metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
      wShared wTarget deviation populationSpecificGap
      k₁ h_k₁ (hdev.mono (le_of_lt h_more))
  rw [h_formula₂, h_formula₁]
  have hk₁ : 0 < (k₁ : ℝ) := Nat.cast_pos.mpr h_k₁
  have hcast : (k₁ : ℝ) < (k₂ : ℝ) := by
    exact_mod_cast h_more
  have hdiv : populationSpecificGap / (k₂ : ℝ) < populationSpecificGap / (k₁ : ℝ) :=
    div_lt_div_of_pos_left h_pop hk₁ hcast
  linarith

/-- Positivity of the exact shared-feature meta-learning transfer gap. -/
theorem metaLearnedTransferGapSq_pos {p : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k : ℕ)
    (h_pop : 0 < populationSpecificGap)
    (h_k : 0 < k)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k) :
    0 < metaLearnedTransferGapSq wShared wTarget deviation k := by
  rw [metaLearnedTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k
    wShared wTarget deviation populationSpecificGap
    k h_k hdev]
  have h_irred : 0 ≤ coefficientGapSq wShared wTarget :=
    coefficientGapSq_nonneg wShared wTarget
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr h_k
  have hdiv : 0 < populationSpecificGap / (k : ℝ) :=
    div_pos h_pop hk
  linarith

/-- Weighted population-specific deviation around the shared representation
    center. This lets us compare the usual equal-weight meta average against
    arbitrary affine aggregation of the first `k` source populations. -/
noncomputable def weightedPopulationDeviation {p k : ℕ}
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i ↦ ∑ j : Fin k, weight j * deviation j i

/-- Weighted meta-learned source weights built from an affine combination of
    source-population-specific deviations around a shared center. -/
noncomputable def weightedMetaSourceWeights {p k : ℕ}
    (wShared : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  fun i ↦ wShared i + weightedPopulationDeviation deviation weight i

/-- Exact transfer gap of a weighted affine meta-aggregator. -/
noncomputable def weightedMetaTransferGapSq {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : ℝ :=
  coefficientGapSq (weightedMetaSourceWeights wShared deviation weight) wTarget

/-- Uniform affine weights on `k` source populations. -/
noncomputable def uniformMetaWeight (k : ℕ) : Fin k → ℝ :=
  fun _ ↦ (k : ℝ)⁻¹

/-- Weighted average of source-population effect vectors: the same weighted combination
    as `weightedPopulationDeviation`, applied to the source effect vectors themselves
    rather than to their deviations around a shared center.

    Empirical status: UNTESTED. -/
noncomputable def weightedPopulationEffectAverage {p k : ℕ}
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ) : Fin p → ℝ :=
  weightedPopulationDeviation wSource weight

/-- Any affine meta-aggregator is exactly the weighted average of the source
    effect vectors once deviations are instantiated as centered source effects. -/
theorem weightedMetaSourceWeights_eq_weightedPopulationEffectAverage
    {p k : ℕ}
    (wShared : Fin p → ℝ)
    (wSource : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (h_sum : ∑ j : Fin k, weight j = 1) :
    weightedMetaSourceWeights wShared
        (centeredPopulationEffectDeviation wShared wSource) weight =
      weightedPopulationEffectAverage wSource weight := by
  funext i
  unfold weightedMetaSourceWeights weightedPopulationEffectAverage
    centeredPopulationEffectDeviation weightedPopulationDeviation
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
        (centeredPopulationEffectDeviation wShared wSource) weight =
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
          (fun i ↦ ∑ j : Fin k, weight j * deviation j i)
          (fun i ↦ ∑ j : Fin k, weight j * deviation j i) =
        ∑ j : Fin k,
          dotProduct (fun i ↦ weight j * deviation j i)
            (fun i ↦ ∑ l : Fin k, weight l * deviation l i) by
      simpa using
        dotProduct_sum_left (Finset.univ)
          (fun j : Fin k ↦ fun i ↦ weight j * deviation j i)
          (fun i ↦ ∑ l : Fin k, weight l * deviation l i)]
  calc
    ∑ j : Fin k,
        dotProduct (fun i ↦ weight j * deviation j i)
          (fun i ↦ ∑ l : Fin k, weight l * deviation l i)
      =
        ∑ j : Fin k,
          weight j *
            dotProduct (deviation j)
              (fun i ↦ ∑ l : Fin k, weight l * deviation l i) := by
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
                (fun i ↦ ∑ l : Fin k, weight l * deviation l i) =
              ∑ l : Fin k,
                dotProduct (deviation j) (fun i ↦ weight l * deviation l i) by
                simpa using
                  dotProduct_sum_right (Finset.univ) (deviation j)
                    (fun l : Fin k ↦ fun i ↦ weight l * deviation l i)]
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
    (populationSpecificGap : ℝ)
    (h_shared_orth :
      ∀ j, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    weightedMetaTransferGapSq wShared wTarget deviation weight =
      coefficientGapSq wShared wTarget +
        populationSpecificGap * ∑ j : Fin k, weight j ^ 2 := by
  obtain ⟨irreducibleGap, h_shared⟩ :
      ∃ g : ℝ, coefficientGapSq wShared wTarget = g := ⟨_, rfl⟩
  rw [h_shared]
  let sharedResidual : Fin p → ℝ := fun i ↦ wShared i - wTarget i
  have h_shared_norm : dotProduct sharedResidual sharedResidual = irreducibleGap := by
    simpa [sharedResidual, coefficientGapSq] using h_shared
  have h_weighted_norm :
      dotProduct (weightedPopulationDeviation deviation weight)
        (weightedPopulationDeviation deviation weight) =
          populationSpecificGap * ∑ j : Fin k, weight j ^ 2 :=
    weightedPopulationDeviation_squaredNorm_eq_populationSpecificGap_mul_sum_sq
      deviation weight populationSpecificGap h_norm h_pair
  have h_cross :
      dotProduct sharedResidual (weightedPopulationDeviation deviation weight) = 0 := by
    unfold weightedPopulationDeviation
    rw [show
        dotProduct sharedResidual
          (fun i ↦ ∑ j : Fin k, weight j * deviation j i) =
          ∑ j : Fin k,
            dotProduct sharedResidual (fun i ↦ weight j * deviation j i) by
          simpa using
            dotProduct_sum_right (Finset.univ) sharedResidual
              (fun j : Fin k ↦ fun i ↦ weight j * deviation j i)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [dotProduct_smul_right, h_shared_orth j, mul_zero]
  have h_sub :
      (fun i ↦
        weightedMetaSourceWeights wShared deviation weight i - wTarget i) =
      fun i ↦ sharedResidual i + weightedPopulationDeviation deviation weight i := by
    funext i
    unfold weightedMetaSourceWeights sharedResidual weightedPopulationDeviation
    ring
  unfold weightedMetaTransferGapSq coefficientGapSq
  rw [h_sub]
  calc
    dotProduct
        (fun i ↦ sharedResidual i + weightedPopulationDeviation deviation weight i)
        (fun i ↦ sharedResidual i + weightedPopulationDeviation deviation weight i)
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
  have hlt : ∑ j : Fin k, weight j ^ 2 < 1 / (k : ℝ) :=
    not_le.mp h_contra
  have hmul_lt : (k : ℝ) * ∑ j : Fin k, weight j ^ 2 < 1 := by
    have := mul_lt_mul_of_pos_left hlt hk
    simpa [div_eq_mul_inv, one_div, hk.ne'] using this
  linarith

/-- Exact uniform affine weighting formula. -/
theorem weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k_of_uniform
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_shared_orth :
      ∀ j, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) =
      coefficientGapSq wShared wTarget + populationSpecificGap / k := by
  rw [weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
    wShared wTarget deviation (uniformMetaWeight k)
    populationSpecificGap h_shared_orth h_norm h_pair]
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
    transfer gap `coefficientGapSq wShared wTarget + gap × Σ_j w_j²`, so the
    uniform average minimizes the exact transfer gap because `Σ_j w_j² ≥ 1 / k`. -/
theorem weightedMetaTransferGapSq_ge_uniform_of_affine_weights
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_sum : ∑ j : Fin k, weight j = 1)
    (h_shared_orth :
      ∀ j, dotProduct (fun i ↦ wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0)
    (h_pop : 0 ≤ populationSpecificGap) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) ≤
      weightedMetaTransferGapSq wShared wTarget deviation weight := by
  rw [weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_div_k_of_uniform
      wShared wTarget deviation populationSpecificGap
      h_k h_shared_orth h_norm h_pair,
    weightedMetaTransferGapSq_eq_irreducible_plus_populationSpecificGap_mul_sum_sq
      wShared wTarget deviation weight populationSpecificGap
      h_shared_orth h_norm h_pair]
  have h_sq_lb : 1 / (k : ℝ) ≤ ∑ j : Fin k, weight j ^ 2 :=
    one_div_card_le_sum_sq_of_affine_weights weight h_k h_sum
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
  have h_sq_term : gap₁ * (b * b) < gap₂ * (b * b) :=
    mul_lt_mul_of_pos_right h_gap (mul_pos hb_pos hb_pos)
  nlinarith

/-- Target sample size needed for the optimal fine-tuning MSE to reach a target
    tolerance `τ`. This is the exact threshold obtained by solving the
    closed-form optimal-MSE equation for `nTarget`. -/
noncomputable def requiredTargetSamplesForOptimalFineTuningMSE
    (gapSq noiseVar tau : ℝ) : ℝ :=
  noiseVar * (gapSq - tau) / (tau * gapSq)

/-- **requiredTargetSamplesForOptimalFineTuningMSE at zero gapSq, named.** A zero squared gap means
source and target coincide and no target samples are needed -- but the formula reaches that answer
through a division by zero rather than through the model, so it returns `0` for the wrong reason
and returns it just as readily when `tau` is zero and the requirement diverges. Consumers must
require `gapSq ≠ 0`. -/
theorem requiredTargetSamplesForOptimalFineTuningMSE_zero_gapsq_is_junk (noiseVar : ℝ) (tau : ℝ) :
    requiredTargetSamplesForOptimalFineTuningMSE 0 noiseVar tau = 0 := by
  unfold requiredTargetSamplesForOptimalFineTuningMSE
  simp

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
  have h_den : 0 < tau * gapSq :=
    mul_pos h_tau h_gap_pos
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
  have hdiv : noiseVar / gap₂ < noiseVar / gap₁ :=
    div_lt_div_of_pos_left h_noise h_gap₁ h_gap
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
      dotProduct (fun i ↦ w i - wStar i)
        (sigmaObsTarget.mulVec (fun i ↦ w i - wStar i)) := by
  let u : Fin p → ℝ := fun i ↦ w i - wStar i
  have hw : w = fun i ↦ wStar i + u i := by
    funext i
    simp [u]
  have hmul :
      sigmaObsTarget.mulVec (fun i ↦ wStar i + u i) =
        sigmaObsTarget.mulVec wStar + sigmaObsTarget.mulVec u := by
    simpa [u] using matrix_mulVec_add sigmaObsTarget wStar u
  have hswap :
      dotProduct wStar (sigmaObsTarget.mulVec u) =
        dotProduct u crossTarget := by
    calc
      dotProduct wStar (sigmaObsTarget.mulVec u) =
          dotProduct u (sigmaObsTarget.mulVec wStar) :=
            dotProduct_mulVec_swap_of_isSymm sigmaObsTarget h_symm wStar u
      _ = dotProduct u crossTarget := by simp [h_opt]
  let a : ℝ := dotProduct wStar crossTarget
  let b : ℝ := dotProduct wStar (sigmaObsTarget.mulVec u)
  let c : ℝ := dotProduct u crossTarget
  let d : ℝ := dotProduct u (sigmaObsTarget.mulVec u)
  have hexpand1 :
      dotProduct (fun i ↦ wStar i + u i) (crossTarget + sigmaObsTarget.mulVec u) =
        a + b + c + d := by
    simp [a, b, c, d, dotProduct, Finset.sum_add_distrib, add_mul, mul_add]
    ring
  have hexpand2 :
      dotProduct (fun i ↦ wStar i + u i) crossTarget = a + c := by
    simp [a, c, dotProduct, Finset.sum_add_distrib, add_mul]
  have h_gap_rhs :
      dotProduct (fun i ↦ (fun j ↦ wStar j + u j) i - wStar i)
        (sigmaObsTarget.mulVec (fun i ↦ (fun j ↦ wStar j + u j) i - wStar i)) = d := by
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
      targetLinearExcessRisk (1 : Matrix (Fin p) (Fin p) ℝ)
        crossTarget noiseVar w wStar ≤ errCap) :
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

section ExactGainFineTuning

/-! Every declaration in this section is about one score at one design, and each of them
repeated the same seven-line binder block to say so.  The block is a `variable` line now,
which is what Lean has for this; only the hypothesis `h_opt`, which the isotropic
statements need and the general ones do not, stays where it is used. -/

variable {p : ℕ}
  (source_r2 transported_r2 : ℝ)
  (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
  (crossTarget : Fin p → ℝ)
  (noiseVar : ℝ)
  (wBefore wAfter wStar : Fin p → ℝ)

/-- The fine-tuned target `R²` credited with the EXACT adaptation gain: the transported
baseline, penalised by the portability loss, and credited with the literal drop in target
excess risk rather than a scalar parameter.

Every theorem about this score wrote it out in full -- four lines of it, on top of the
binder block they share -- so the score and its readings could drift apart in a proof that
still typechecks.  The isotropic score below is this one at `Σ = 1`. -/
noncomputable def fineTunedTargetR2OfExactGain : ℝ :=
  fineTunedTargetR2 source_r2
    (transportPenalty source_r2 transported_r2)
    (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar)

/-- The scalar fine-tuning `adaptation_gain` parameter is exactly the gain in
    target `R²` obtained by reducing literal target excess risk, once the
    baseline portability loss is instantiated by an explicit transported
    baseline. -/
theorem fineTunedTargetR2_eq_transportedBaseline_plus_exact_excessRisk_reduction :
    fineTunedTargetR2OfExactGain source_r2 transported_r2 sigmaObsTarget
        crossTarget noiseVar wBefore wAfter wStar =
      transported_r2 +
        exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar := by
  unfold fineTunedTargetR2OfExactGain
  rw [fineTunedTargetR2_eq_transportedR2_plus_adaptation]

/-- The exact excess-risk fine-tuning theorem is an instance of the canonical
    deployed-transfer target `R²` surface with an explicit transported baseline,
    exact target-specific adaptation gain, and zero estimation penalty. -/
theorem fineTunedTargetR2_eq_deployedTransferTargetR2_exactAdaptationGain :
    fineTunedTargetR2OfExactGain source_r2 transported_r2 sigmaObsTarget
        crossTarget noiseVar wBefore wAfter wStar =
      deployedTransferTargetR2 transported_r2
        (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar) 0 := by
  unfold fineTunedTargetR2OfExactGain
  simpa using fineTunedTargetR2_eq_deployedTransferTargetR2
    source_r2 transported_r2
    (exactAdaptationGain sigmaObsTarget crossTarget noiseVar wBefore wAfter wStar)

/-- The fine-tuned target `R²` of the isotropic design: the transported baseline penalised
by the portability loss and credited with the exact adaptation gain at `Σ = 1`.

The two theorems below evaluate this same score against two different right-hand sides, and
each wrote the score out in full -- four lines of it, on top of the seven binder lines they
share.  Named once, the pair reads as two readings of one quantity, which is what it is. -/
noncomputable def isotropicFineTunedTargetR2 : ℝ :=
  fineTunedTargetR2OfExactGain source_r2 transported_r2
    (1 : Matrix (Fin p) (Fin p) ℝ) crossTarget noiseVar wBefore wAfter wStar

/-- In the isotropic target design, the scalar fine-tuning model is exactly the
    transported baseline plus the drop in squared effect mismatch
    from target adaptation. -/
theorem fineTunedTargetR2_eq_transportedBaseline_plus_gap_drop_isotropic
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    isotropicFineTunedTargetR2 source_r2 transported_r2 crossTarget noiseVar
        wBefore wAfter wStar =
      transported_r2 +
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar) := by
  unfold isotropicFineTunedTargetR2
  rw [fineTunedTargetR2_eq_transportedBaseline_plus_exact_excessRisk_reduction]
  rw [exactAdaptationGain_eq_coefficientGapDrop_isotropic crossTarget noiseVar
    wBefore wAfter wStar h_opt]

/-- In the isotropic target design, the deployed fine-tuning target `R²`
    reduces to the canonical transported baseline plus the exact drop in
    squared coefficient mismatch, with zero estimation penalty. -/
theorem fineTunedTargetR2_eq_deployedTransferTargetR2_gapDrop_isotropic
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    isotropicFineTunedTargetR2 source_r2 transported_r2 crossTarget noiseVar
        wBefore wAfter wStar =
      deployedTransferTargetR2 transported_r2
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar) 0 := by
  rw [fineTunedTargetR2_eq_transportedBaseline_plus_gap_drop_isotropic
    source_r2 transported_r2 crossTarget noiseVar wBefore wAfter wStar h_opt]
  unfold deployedTransferTargetR2
  ring

end ExactGainFineTuning

/-- Taking the transported baseline to be the target oracle ceiling minus the
    pre-adaptation coefficient gap — written out in the statement rather than
    assumed of a free variable — isotropic fine-tuning reduces the deployed
    target `R²` exactly to the oracle ceiling minus the residual
    post-adaptation gap. This is the clean residual-gap form of the canonical
    deployed-transfer theorem. -/
theorem fineTunedTargetR2_eq_oracle_minus_postGap_isotropic
    {p : ℕ}
    (source_r2 oracle_target_r2 : ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (wBefore wAfter wStar : Fin p → ℝ)
    (h_opt : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec wStar = crossTarget) :
    fineTunedTargetR2 source_r2
        (transportPenalty source_r2
          (oracle_target_r2 - coefficientGapSq wBefore wStar))
        (exactAdaptationGain (1 : Matrix (Fin p) (Fin p) ℝ)
          crossTarget noiseVar wBefore wAfter wStar) =
      oracle_target_r2 - coefficientGapSq wAfter wStar := by
  -- The goal is `isotropicFineTunedTargetR2` unfolded. `rw` matches syntactically,
  -- so fold it back before rewriting with the lemma stated about that name.
  show isotropicFineTunedTargetR2 source_r2
      (oracle_target_r2 - coefficientGapSq wBefore wStar)
      crossTarget noiseVar wBefore wAfter wStar =
    oracle_target_r2 - coefficientGapSq wAfter wStar
  rw [fineTunedTargetR2_eq_deployedTransferTargetR2_gapDrop_isotropic
    source_r2 (oracle_target_r2 - coefficientGapSq wBefore wStar)
    crossTarget noiseVar wBefore wAfter wStar h_opt]
  have h_oracle_gap :
      oracleTransportAdaptationGain
          (oracle_target_r2 - coefficientGapSq wBefore wStar)
          oracle_target_r2 =
        coefficientGapSq wBefore wStar := by
    unfold oracleTransportAdaptationGain
    ring
  calc
    deployedTransferTargetR2
        (oracle_target_r2 - coefficientGapSq wBefore wStar)
        (coefficientGapSq wBefore wStar - coefficientGapSq wAfter wStar)
        0
      =
        deployedTransferTargetR2
          (oracle_target_r2 - coefficientGapSq wBefore wStar)
          (oracleTransportAdaptationGain
              (oracle_target_r2 - coefficientGapSq wBefore wStar)
              oracle_target_r2 -
            coefficientGapSq wAfter wStar)
          0 := by rw [h_oracle_gap]
    _ = oracle_target_r2 - coefficientGapSq wAfter wStar - 0 :=
      deployedTransferTargetR2_eq_oracle_minus_residualGap_minus_estimationPenalty
        (oracle_target_r2 - coefficientGapSq wBefore wStar)
        oracle_target_r2
        (coefficientGapSq wAfter wStar)
        0
    _ = oracle_target_r2 - coefficientGapSq wAfter wStar := by ring

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
    (populationSpecificGap noiseVar nTarget tau : ℝ)
    (k₁ k₂ : ℕ)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂)
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
        metaLearnedTransferGapSq wShared wTarget deviation k₁ :=
    metaLearnedTransferGapSq_strictMono
      wShared wTarget deviation populationSpecificGap
      k₁ k₂ h_pop h_k₁ h_more_tasks hdev
  have h_gap₂_pos :
      0 < metaLearnedTransferGapSq wShared wTarget deviation k₂ :=
    metaLearnedTransferGapSq_pos
      wShared wTarget deviation populationSpecificGap
      k₂ h_pop h_k₂ hdev
  have h_mse_order :
      optimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar nTarget <
        optimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₁)
          noiseVar nTarget :=
    optimalFineTuningMSE_strictMono_in_gapSq
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      (metaLearnedTransferGapSq wShared wTarget deviation k₁)
      noiseVar nTarget (le_of_lt h_gap₂_pos) h_gap_order h_noise h_n
  have h_req_pos :
      0 <
        requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar tau :=
    requiredTargetSamplesForOptimalFineTuningMSE_pos
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      noiseVar tau h_noise h_tau h_tau_small
  have h_req_order :
      requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₂)
          noiseVar tau <
        requiredTargetSamplesForOptimalFineTuningMSE
          (metaLearnedTransferGapSq wShared wTarget deviation k₁)
          noiseVar tau :=
    requiredTargetSamplesForOptimalFineTuningMSE_strictMono_in_gapSq
      (metaLearnedTransferGapSq wShared wTarget deviation k₂)
      (metaLearnedTransferGapSq wShared wTarget deviation k₁)
      noiseVar tau h_gap₂_pos h_gap_order h_noise h_tau
  exact ⟨h_gap_order, h_mse_order, h_req_pos, h_req_order⟩

/-- More source populations strictly improve the canonical deployed-transfer
    target `R²` when the only remaining adaptation burden is the exact
    meta-learned residual coefficient gap. This expresses the meta-learning
    block directly on the shared deployed metric surface rather than only on
    gap or MSE surrogates. -/
theorem metaLearned_deployedTransferTargetR2_strictMono
    {p : ℕ}
    (transported_r2 oracle_target_r2 estimation_penalty : ℝ)
    (wShared wTarget : Fin p → ℝ)
    (deviation : ℕ → Fin p → ℝ)
    (populationSpecificGap : ℝ)
    (k₁ k₂ : ℕ)
    (hdev : MetaLearningDeviations wShared wTarget deviation populationSpecificGap k₂)
    (h_pop : 0 < populationSpecificGap)
    (h_k₁ : 0 < k₁)
    (h_more_tasks : k₁ < k₂) :
    deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2 -
          metaLearnedTransferGapSq wShared wTarget deviation k₁)
        estimation_penalty <
      deployedTransferTargetR2 transported_r2
        (oracleTransportAdaptationGain transported_r2 oracle_target_r2 -
          metaLearnedTransferGapSq wShared wTarget deviation k₂)
        estimation_penalty := by
  have h_gap_order :
      metaLearnedTransferGapSq wShared wTarget deviation k₂ <
        metaLearnedTransferGapSq wShared wTarget deviation k₁ :=
    metaLearnedTransferGapSq_strictMono
      wShared wTarget deviation populationSpecificGap
      k₁ k₂ h_pop h_k₁ h_more_tasks hdev
  unfold deployedTransferTargetR2 oracleTransportAdaptationGain
  linarith

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

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem privateArchitectureTransferCeiling_at_reference_point :
    privateArchitectureTransferCeiling 1 1 1 = 0 := by
  norm_num [privateArchitectureTransferCeiling, sharedLDFromMigration]



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
    have h_base_pos : 0 < h2_target * sharedLDFromMigration M :=
      mul_pos h_h2 h_shared_pos
    calc
      h2_target * (1 - f_private) * sharedLDFromMigration M
          = (h2_target * sharedLDFromMigration M) * (1 - f_private) := by ring
      _ < h2_target * sharedLDFromMigration M :=
        mul_lt_of_lt_one_right h_base_pos h_one_minus_lt_one
      _ = h2_target * (1 - (0 : ℝ)) * sharedLDFromMigration M := by ring
  have h_no_private_lt_h2 :
      privateArchitectureTransferCeiling h2_target 0 M < h2_target := by
    unfold privateArchitectureTransferCeiling
    calc
      h2_target * (1 - (0 : ℝ)) * sharedLDFromMigration M
          = h2_target * sharedLDFromMigration M := by ring
      _ < h2_target :=
        mul_lt_of_lt_one_right h_h2 h_shared_lt_one
  have h_r2_lt_no_private :
      r2_target < privateArchitectureTransferCeiling h2_target 0 M :=
    lt_of_le_of_lt h_bound h_ceiling_lt_no_private
  have h_r2_lt_h2 : r2_target < h2_target :=
    lt_trans h_r2_lt_no_private h_no_private_lt_h2
  exact ⟨h_ceiling_lt_no_private, h_r2_lt_no_private, h_r2_lt_h2⟩

end TransferLimits

/-! ## What it costs to have fitted against the wrong linkage-disequilibrium operator

Every bound above takes the operator as given. In practice the panel is optimised against an
estimated reference linkage structure and deployed against the target's true one, and what decides
whether that is tolerable is not the error in the estimated objective — which moves at first order
and always will — but the loss from transplanting the optimizer.

`Calibrator.TransplantationStability` answers with one number the fit already contains: `γ`, the
margin by which the selected panel beats the runner-up in the fitted objective. With `δ` an error
budget for the operator, the deployment loss is `min(2δ, 8δ²/γ)`, and the quadratic branch binds
exactly when `4δ < γ`.

The degenerate branch is not hypothetical. Near-ties between candidate panels, shrinkage levels
and ancestry-weighting schemes are the normal case, and there the standard argument — the
objective is stationary at the optimum, so small model error costs second order — fails: the
transplanted choice lands on the wrong branch and pays the full `δ`.

So a transferred score should be reported with its margin. Without `γ` there is no route from an
operator error budget to a deployment-loss bound, and optimality under one estimated operator is a
different claim from robustness to having estimated it. -/

section OperatorError

open Matrix

/-- From linkage-disequilibrium model error to deployment loss. Instance of
    `transplant_excess_le`, in the eigenbasis of the true operator: `spectrum` carries its
    eigenvalues with the deployed design at the ground direction, `weights` the fitted panel's
    coefficients, `E` the operator error with quadratic form bounded by `modelError`, and
    `margin` the gap between the selected panel and the runner-up. The excess loss is quadratic
    in the model error with constant `8/margin`.

    The spectral gap bound and the perturbation estimate used by `transplant_excess_le` are both
    proved in `Calibrator.TransplantationStability`.

    Empirical status: DERIVED; `margin` is a quantity a fit already produces and this result asks
    to be reported. -/
theorem ldModelError_to_deploymentLoss {n : ℕ}
    (spectrum weights : Fin (n + 1) → ℝ)
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (margin modelError : ℝ)
    (hmargin : 0 < margin) (herr : 0 ≤ modelError) (hEsymm : E.IsSymm)
    (hEbound : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      |v ⬝ᵥ (E *ᵥ v)| ≤ modelError)
    (hunit : ∑ i, weights i ^ 2 = 1)
    (hgap : ∀ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
      spectrum 0 + margin ≤ spectrum i)
    (hmin : ∀ v : Fin (n + 1) → ℝ, (∑ i, v i ^ 2) = 1 →
      perturbedEnergy spectrum E weights ≤ perturbedEnergy spectrum E v) :
    spectralEnergy spectrum weights - spectrum 0 ≤ 8 * modelError ^ 2 / margin :=
  transplant_excess_le spectrum weights E margin modelError hmargin herr hEsymm hEbound
    hunit hgap hmin

/-- The quadratic branch applies only while the model error is small against the margin.

    Empirical status: DERIVED. -/
theorem quadraticLoss_binds_iff_error_small (margin modelError : ℝ)
    (hmargin : 0 < margin) (herr : 0 < modelError) :
    8 * modelError ^ 2 / margin < 2 * modelError ↔ 4 * modelError < margin :=
  quadratic_beats_linear_iff margin modelError hmargin herr

/-- At a tie between candidate panels the loss is the full model error.

    Empirical status: DERIVED. -/
theorem tiedPanels_lose_the_whole_error (modelError : ℝ) (herr : 0 < modelError) :
    trueDesignValue modelError 0 - trueDesignValue modelError 1 = modelError :=
  (crossing_loss_linear modelError herr).2.2

/-! ### Junk-value boundaries

Four bodies here divide, and one takes a square root that Mathlib sends to `0` on negative
arguments.  Each branch is named so a consumer cannot read the returned `0` as a measurement. -/

/-- A nonpositive product of shared-LD genetic variances sends the square root to Mathlib's
junk `0`, and the correlation with it.  Zero correlation is a meaningful value, so this branch
has to be named rather than detected. -/
theorem ldEffectGeneticCorrelation_at_nonpositive_variance_is_junk
    {m : ℕ} (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ)
    (hnonpos : sharedLDGeneticVariance β_source ld * sharedLDGeneticVariance β_target ld ≤ 0) :
    ldEffectGeneticCorrelation β_source β_target ld = 0 := by
  unfold ldEffectGeneticCorrelation
  rw [Real.sqrt_eq_zero_of_nonpos hnonpos, div_zero]

/-- With no target sample the noise-per-sample term is Mathlib's junk `0`, so the body reports
the noiseless oracle rather than the correct limit of no information. -/
theorem sampleLimitedScratchTargetR2_at_zero_sample_is_junk
    (oracle_target_r2 noiseVar : ℝ) :
    sampleLimitedScratchTargetR2 oracle_target_r2 noiseVar 0
      = scratchTargetR2 oracle_target_r2 0 := by
  unfold sampleLimitedScratchTargetR2
  rw [div_zero]

/-- When fine-tuning already matches the oracle there is no crossing sample size, and the
quotient reports `0` -- the value that would mean "no samples needed", the opposite reading. -/
theorem scratchVsFineTuningCriticalSampleSize_at_no_gap_is_junk
    (r2_source divergence_penalty adaptation_gain oracle_target_r2 noiseVar : ℝ)
    (hgap : oracle_target_r2
      = fineTunedTargetR2 r2_source divergence_penalty adaptation_gain) :
    scratchVsFineTuningCriticalSampleSize r2_source divergence_penalty adaptation_gain
        oracle_target_r2 noiseVar = 0 := by
  unfold scratchVsFineTuningCriticalSampleSize
  rw [hgap, sub_self, div_zero]

/-- Averaging over no populations divides by zero, and the mean deviation reports `0` rather
than being undefined. -/
theorem meanPopulationDeviation_at_zero_count_is_junk
    {p : ℕ} (deviation : ℕ → Fin p → ℝ) (i : Fin p) :
    meanPopulationDeviation deviation 0 i = 0 := by
  unfold meanPopulationDeviation
  simp

/-- The same boundary for the averaged source weights. -/
theorem sourcePopulationMeanWeights_at_zero_count_is_junk
    {p : ℕ} (wSource : ℕ → Fin p → ℝ) (i : Fin p) :
    sourcePopulationMeanWeights wSource 0 i = 0 := by
  unfold sourcePopulationMeanWeights
  simp

end OperatorError

end Calibrator
