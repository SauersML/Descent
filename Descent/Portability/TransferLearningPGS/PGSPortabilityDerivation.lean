/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Chebyshev
import Descent.PopGen.DGP
import Descent.Portability.TransplantationStability
import Descent.Core.Ratios

namespace Descent.Portability

open MeasureTheory Finset

/-!
# `TransferLearningPGS.PGSPortabilityDerivation`

Part of the split of `Descent/Portability/TransferLearningPGS.lean`, which was 3,558 lines.

This part is the HEAD of the fan. The split first made the parts a CHAIN -- each importing
the one before, in the order the original text ran -- which preserved every resolution the
single file had and charged every part a dependency on everything written above it, used or
not. This part is what the others were resolved against: it declares the definitions they
name and carries the imports they share, and it names no sibling itself.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

section PGSPortabilityDerivation

/-- Covariance between PGS (using source weights) and the genetic component
    of the phenotype in a given population:
    Cov(PGS, Y_genetic) = Σᵢ Σⱼ β_source_i × Σᵢⱼ × β_causal_j
    where β_causal are the modelled causal effects in that population.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transfer.py`,
    `test_transfer_chain`). Standardised dosages on a recombining coalescent
    panel, LD as the correlation matrix: against the empirical `Cov(PGS, y)` at
    0.63 sems and against the realised `Var(PGS)` at 0.00. -/
noncomputable def pgsPhenoCov {m : ℕ} (β_weights β_causal : Fin m → ℝ)
    (ld : Fin m → Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin m, β_weights i * ld i j * β_causal j

/-- Genetic variance induced by a shared LD kernel.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transfer.py`,
    `test_transfer_chain`). Against the realised variance of the score on a
    recombining coalescent panel: 0.00 sems. -/
noncomputable def sharedLDGeneticVariance {m : ℕ}
    (β : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) : ℝ :=
  pgsPhenoCov β β ld

/-- Heritability induced by a shared LD kernel.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transfer.py`,
    `test_transfer_chain`). Against the realised fraction of phenotypic variance
    carried by the additive score: 0.00 sems. -/
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

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transfer.py`,
    `test_transfer_chain`). Against the squared correlation of score with phenotype, source and
    transported: 0.02 and 1.35 sems over a prediction
    spanning 0.11581 to 0.23227, a factor of two. -/
noncomputable def pgsR2 (cov_pgs_y : ℝ) (var_pgs var_y : ℝ) : ℝ :=
  Descent.Core.squaredShare cov_pgs_y var_pgs var_y

/-- **pgsR2 at zero var_pgs, named.** A score with no variance has no `R²`. Lean returns `0`,
which reads as a score that varies and fails, rather than a score that is constant. Consumers
must require `var_pgs ≠ 0`. -/
theorem pgsR2_zero_varpgs_is_junk (cov_pgs_y : ℝ) (var_y : ℝ) :
    pgsR2 cov_pgs_y 0 var_y = 0 := by
  unfold pgsR2 Descent.Core.squaredShare
  simp

/-- **`R²` is invariant under rescaling the score.** Multiplying the polygenic score by `c`
multiplies its covariance with the outcome by `c` and its variance by `c²`, and the ratio is
unchanged. This is the defining property of a squared correlation: it is why `R²` is comparable
across scores on different scales, and a body that failed it would depend on the arbitrary units
the score happens to be reported in. -/
theorem pgsR2_scale_invariant (cov_pgs_y var_pgs var_y c : ℝ) (hc : c ≠ 0) :
    pgsR2 (c * cov_pgs_y) (c ^ 2 * var_pgs) var_y = pgsR2 cov_pgs_y var_pgs var_y := by
  unfold pgsR2 Descent.Core.squaredShare
  rw [mul_pow, show c ^ 2 * var_pgs * var_y = c ^ 2 * (var_pgs * var_y) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **One body, two names, tied.** `DGP.explainedR2FromTransportMoments` is the
same squared-correlation coordinate. -/
theorem pgsR2_eq_explainedR2FromTransportMoments (cov_pgs_y var_pgs var_y : ℝ) :
    pgsR2 cov_pgs_y var_pgs var_y =
      PopGen.explainedR2FromTransportMoments cov_pgs_y var_pgs var_y := rfl

/-- Source-population `R²` of the score that uses the source's own effects as
    weights under a shared LD kernel.

    Empirical status: **VALIDATED** through `pgsR2`, measured on the
    same runs (`battery_transfer.py`, `test_transfer_chain`) at 0.02 sems. -/
noncomputable def sourceTruthR2SharedLD {m : ℕ}
    (β_source : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  pgsR2 (sharedLDGeneticVariance β_source ld)
    (sharedLDGeneticVariance β_source ld) var_y

/-- Target-population transported `R²` of the source-weighted score under a
    shared LD kernel.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_transfer.py`,
    `test_transfer_chain`). The transported case is the one that matters, since
    the source weights were not fitted there: 1.35 sems, predicted 0.11581
    against a measured 0.12099. -/
noncomputable def transportedTargetR2SharedLD {m : ℕ}
    (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) (var_y : ℝ) : ℝ :=
  pgsR2 (pgsPhenoCov β_source β_target ld)
    (sharedLDGeneticVariance β_source ld) var_y

/-- Effect correlation induced by a shared LD kernel.

    Empirical status: **VALIDATED**, and it separates from its
    LD-free sibling (`validation/empirical/simcov/battery_transfer.py`,
    `test_transfer_chain`). The oracle is the realised correlation between the
    two genetic values in the same individuals:

      definition                       predicted   measured             sems
      ldEffectGeneticCorrelation         0.67104   0.67104±0.00869      0.00
      effectGeneticCorrelation (LD-free) 0.69792   0.67104±0.00869      3.09

    Under LD only the LD-weighted contraction is the genetic correlation. The
    plain cosine between effect vectors is a different quantity and differs by
    3.1 sems on a panel with realistic coalescent LD. -/
noncomputable def ldEffectGeneticCorrelation {m : ℕ}
    (β_source β_target : Fin m → ℝ) (ld : Fin m → Fin m → ℝ) : ℝ :=
  pgsPhenoCov β_source β_target ld /
    Real.sqrt (sharedLDGeneticVariance β_source ld * sharedLDGeneticVariance β_target ld)

/-- Euclidean / independent-variant genetic correlation between source and
    target effect-size vectors. This is the diagonal-LD specialization of the
    shared-LD correlation above.

    Empirical status: **VALIDATED IN THE DECLARED REGIME**
    (`validation/empirical/simcov/battery_pgscal01.py`). The regime is
    `standardizedDiagonalLD` made real: 200000 individuals with INDEPENDENT
    standardized genotypes, 400 variants. The oracle is the realised Pearson
    correlation between the two genetic values in those individuals, and the
    prediction is evaluated at the REALISED effect vectors, never at the nominal
    `ρ` used to draw them — at `m = 400` those differ by about 5%, which is the
    size of a spurious falsification.

      design            this body   realised corr(G_s,G_t)   sems
      ρ=0.9  μ=0          0.90778     0.90783±0.00068        0.07
      ρ=0.5  μ=0          0.48140     0.48066±0.00178        0.42
      ρ=0.2  μ=0          0.18449     0.18522±0.00160        0.45
      ρ=0.7  μ=0.6        0.75741     0.75779±0.00091        0.42
      ρ=0.3  μ=0.9        0.62049     0.62109±0.00158        0.38

    The identity gate: the CENTRED Pearson correlation between the same two
    effect vectors — the natural rival, and equal to this body whenever the
    effects have mean zero — is rejected at 72.8 and 225.2 sems on the two cells
    where the effect distribution has a nonzero mean. The uncentred cosine is
    the genetic correlation; the centred one is not. The positive control, two
    orthogonalised effect vectors whose realised genetic correlation must be
    zero, passes at 0.31 sems.

    THE REGIME IS A CONDITION. Under real LD the sibling
    `ldEffectGeneticCorrelation` is the genetic correlation and this body is
    3.1 sems away from it; that separation is measured at that definition. -/
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

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is the DEFINITION of the
    regime, not a statement within it. The identity matrix is what "diagonal LD"
    means, and no measurement of any population could agree or disagree with it:
    a population whose LD matrix is not the identity is not a counterexample to
    this body, it is simply outside the regime this body names.

    What carries empirical content is every result stated over it, and those are
    measured at their own definitions: `sourceSelfR2DiagonalLD`,
    `transportedTargetR2DiagonalLD` and `targetOracleR2DiagonalLD` are all
    VALIDATED against simulated individuals drawn with independent standardized
    genotypes -- which is this operator made real -- and the two wrong forms of
    the `pgsR2` shape are rejected there at 1364 and 212 sems.

    An UNTESTED marker here would read as an unpaid debt and is not one. It
    inflates the count of things owed a measurement with an item that can never
    receive one, which is the same reasoning `DGP.ldWitnessBeta` and the
    `MechanisticPortabilityWitnesses` fixtures already carry. -/
def standardizedDiagonalLD {m : ℕ} : Fin m → Fin m → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Additive genetic variance in the standardized diagonal-LD model.

    Empirical status: **VALIDATED IN THE DECLARED REGIME** (`simcov/battery_bulk41.py`,
    `group_c`). `m` standardized causal variants in LINKAGE EQUILIBRIUM over 4×10⁵
    individuals; the observable is the realised sample variance of the genetic value `Gβ`.

      m     this body   realised Var(Gβ)   sems
       50    0.53004        0.52709        2.50
      200    0.47943        0.47806        1.28
      100    0.61262        0.61106        1.14

    The identity gate: `∑|βᵢ|` misses by 7040 sems and the per-variant mean `(∑βᵢ²)/m` by
    445 sems on the same cells. The positive control -- a SINGLE standardized variant, whose
    genetic value has variance exactly `β²` -- passes at 0.45 sems.

    THE REGIME IS A CONDITION, and the same run shows it. Putting the identical variants in
    exchangeable LD at pairwise correlation 0.5 leaves this body 9.2% off the realised
    variance, because outside linkage equilibrium the variance is `βᵀΣβ` and the cross terms
    do not vanish. `standardizedDiagonalLD` is what makes `Σ = I` here; a caller who
    substitutes a real LD matrix and keeps this body has changed the claim. -/
noncomputable def additiveGeneticVariance {m : ℕ} (β : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, β i ^ 2


/-- Additive heritability `h² = V_A / V_Y` in the standardized diagonal-LD model.

    Regime: STANDARDIZED genotypes. That is the condition under which
    `additiveGeneticVariance` is `∑ βᵢ²` at all; on a dosage scale the sum is
    off by the allele-frequency factor and this ratio inherits the error.

    Empirical status: **VALIDATED** (`simcov/battery_bulk18.py`,
    `test_architecture_scalars`). Measured as a REALISED variance ratio and not
    as the parameter it was simulated at: 40000 individuals are drawn with standardized genotypes
    and effects at three architectures, and the body's
    `∑ βᵢ² / var_y` is compared against `Var(g) / Var(y)` computed from the
    realised phenotypes through an independent path. The body predicts 0.19968,
    0.48808 and 0.76970 against measured 0.20023 ± 0.00142, 0.48524 ± 0.00343
    and 0.76912 ± 0.00544, worst cell 0.83 sems at 0.59% relative, over a
    prediction spanning 74%. The companion `additiveGeneticVariance` is measured
    on the same runs at worst 0.83 sems. -/
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

    Regime: independent standardized variants -- that is what `diagonal LD`
    means, and it is the condition under which `∑ βᵢ²` is the score variance at
    all.

    Empirical status: **VALIDATED** (`simcov/battery_bulk27.py`). 300 variants,
    300000 individuals; the oracle is the REALISED squared correlation between
    a simulated score and a simulated phenotype, and no body is evaluated to
    build it. Worst cell 3.36 sems at 0.92% relative -- above the three-sem
    gate but below the two-percent floor, which is the finite-sample bias of a
    realised `R²` rather than a defect in the body.

    Power: see `transportedTargetR2DiagonalLD`, where two wrong forms of the
    shared `pgsR2` shape are rejected at 1364 and 212 sems on the same runs. -/
noncomputable def sourceSelfR2DiagonalLD {m : ℕ}
    (β_source : Fin m → ℝ) (var_y : ℝ) : ℝ :=
  sourceTruthR2SharedLD β_source standardizedDiagonalLD var_y

/-- Target-population transported `R²` of the source-weighted score in the
    standardized diagonal-LD model.

    Regime: independent standardized variants; source weights carried into the
    target population unchanged, so the only thing degrading the `R²` is effect
    turnover.

    Empirical status: **VALIDATED** (`simcov/battery_bulk27.py`). Effects drawn
    per population at genetic correlation `rg` = 0.4, 0.6, 0.9, 1.0 with `h²`
    from 0.3 to 0.7; 300 variants, 300000 individuals. The comparison target is
    the realised squared correlation between the source-weighted score and the
    target phenotype. Worst cell 4.06 sems at 1.38% relative -- the
    finite-sample bias of a realised `R²`, below the two-percent floor.

    Power, and why this is a measurement and not a restatement: two wrong forms
    of the `pgsR2` shape ride on the SAME cells and are rejected decisively --
    the covariance left unsquared, `cov / (var_pgs · var_y)`, misses by up to
    1364 sems (468% relative), and the score variance omitted,
    `cov² / var_y`, by up to 212 sems (73%). An oracle algebraically pinned to
    the body could not reject either, since the measurement would move with whatever prediction was
    fed in. Both the square and the divisor are
    therefore chosen by the data.

    The `rg = 1` cell was carried as a control and is DEGENERATE: there the
    transported score IS the oracle score, so both sides are the same number and
    it cannot fail. The harness detected that and voided it, which is why the
    competing forms are recorded as leads rather than falsifications. The three
    validated bodies do not rest on it. -/
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
  unfold sourceTruthR2SharedLD pgsR2 sharedLDHeritability Descent.Core.squaredShare
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
    sharedLDGeneticVariance pgsR2 Descent.Core.squaredShare
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
source of the eps_S(h) + (1/2) d_{H delta H}(S,T) + lambda* bound formalized
below -- see `benDavidUpperBound` for why the one-half is not optional. The mapping of
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

/-- Ben-David upper-bound functional `ε_S(h) + divergence + λ*`.

    **Convention on the divergence argument, stated because the published bound
    carries a factor this body does not.** Ben-David, Blitzer, Crammer, Kulesza,
    Pereira and Vaughan (2010), Theorem 2, is

      `ε_T(h) ≤ ε_S(h) + ½·d_{HΔH}(D_S, D_T) + λ`,

    and the `½` is there because their `d_H(D, D') = 2·sup_{h∈H} |Pr_D[I(h)] -
    Pr_{D'}[I(h)]|` carries a factor two in its own definition. So `divergence`
    here must be supplied as the HALF-divergence `½·d_{HΔH}`, equivalently the
    bare supremum `sup_h |Pr_{D_S}[I(h)] - Pr_{D_T}[I(h)]|`. Feeding a raw
    `d_{HΔH}` doubles the middle term and the bound is loose by that factor.

    This is a naming convention and not a claim: nothing in the corpus computes
    `d_{HΔH}` from an ancestry pair, and `divergence_increases_with_fst` was
    deleted (note below) precisely because the map from `F_ST` to this argument
    is not derived anywhere. The convention still has to be written down --
    an argument named `divergence` against a cited theorem whose divergence is
    twice it is exactly the unstated-convention defect this corpus has already
    paid for over `F_ST`. -/
noncomputable def benDavidUpperBound (err_source divergence lambda_star : ℝ) : ℝ :=
  Descent.Core.sum3 err_source divergence lambda_star

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
  unfold benDavidUpperBound Descent.Core.sum3
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
  unfold benDavidUpperBound Descent.Core.sum3
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

end Descent.Portability
