/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PCCorrectability.Phase

namespace Descent.Portability

/-!
# Application-level correctability diagnostic
-/

/-!
### Test-specific ancestry axis

Blanc and Berg identify, for a pre-specified PGS association test, one GWAS-panel
axis `F̃_Gr` that carries every confounding contribution relevant to that test.
The next equivalence is the finite-dimensional necessity-and-sufficiency result:
zeroing that residual axis protects the test against every confounder, and no
nonzero residual axis can provide such a uniform guarantee.
-/

/-- Bias in a PGS association statistic along a residual cross-panel ancestry
axis.  `scale` collects the positive locus- and panel-count factors.

    Regime: the residual axis CENTRED, which is what PC correction leaves
    behind. That is load-bearing and is the whole content of the comparison
    below.

    Empirical status: **VALIDATED** (`simcov/battery_bulk41.py`, `group_b`).
    200000 individuals; the expected phenotype carries a gradient along the
    residual axis plus an offset, and the observable is the realised
    association of the DRAWN phenotype with that axis. Worst cell 1.78 sems at
    1.31% relative, over designs where the offset runs 0 to 1 and the axis
    spread 0.5 to 2.

    Power, and the practical warning: the same inner product with the axis left
    UNCENTRED misses by up to 894 sems (1333% relative). The two agree exactly
    when the offset is zero and diverge without bound as it grows -- at
    `shift = 1.0` the uncentred form reads 1.075 where the truth is 0.075, a
    fourteenfold overstatement. This is the error that makes a PC-corrected
    test look catastrophically biased when it is nearly clean, and it is
    invisible in any design that only ever centres its phenotype. The competing
    form is recorded as a LEAD rather than a falsification because this run's
    control was DEGENERATE: the axis is centred by construction, so "the axis
    has mean zero" compares a number against itself and cannot fail. The
    harness detected that and voided it; the MATCH above does not rest on it. -/
noncomputable def pgsTestAxisBias {d : ℕ} (scale : ℝ)
    (expectedPhenotype residualTargetAxis : Fin d → ℝ) : ℝ :=
  scale * ∑ i, expectedPhenotype i * residualTargetAxis i


/-- Controlling the single test-specific ancestry axis is necessary and
sufficient for unbiasedness uniformly over all possible ancestry-correlated
expected phenotypes. -/
theorem target_axis_control_iff_uniformly_unbiased {d : ℕ}
    (scale : ℝ) (hscale : scale ≠ 0) (residualTargetAxis : Fin d → ℝ) :
    (∀ expectedPhenotype : Fin d → ℝ,
        pgsTestAxisBias scale expectedPhenotype residualTargetAxis = 0) ↔
      residualTargetAxis = 0 := by
  constructor
  · intro hunbiased
    have hproduct := hunbiased residualTargetAxis
    unfold pgsTestAxisBias at hproduct
    have hsum_mul : (∑ i, residualTargetAxis i * residualTargetAxis i) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hscale
    have hsum_sq : (∑ i, residualTargetAxis i ^ 2) = 0 := by
      simpa [pow_two] using hsum_mul
    have hcoordinate_zero : ∀ i, residualTargetAxis i ^ 2 = 0 := by
      have hfunction : (fun i ↦ residualTargetAxis i ^ 2) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg
          (fun i ↦ sq_nonneg (residualTargetAxis i))).mp hsum_sq
      intro i
      simpa using congrFun hfunction i
    funext i
    exact sq_eq_zero_iff.mp (hcoordinate_zero i)
  · intro hzero expectedPhenotype
    subst residualTargetAxis
    simp [pgsTestAxisBias]

/-!
### Residual susceptibility and application-level risk

Blanc, Mawass, and Berg refine the target-axis geometry into an empirical
diagnostic.  If `σf²` is variance along the GWAS-panel target axis and `σr²`
is marker variance along the corresponding prediction-panel contrast, then
`H = σf² σr²`.  After correction, the same definition with residual ancestry
variance gives `H'`.  This section makes explicit how an upstream overlap
lower bound becomes a lower bound on `H'`, and how `H'` combines with ascertainment to determine the
critical confounding magnitude.
-/

/-- Genetic variance in the GWAS panel explained by a specified external
ancestry gradient.  This is `H` before correction and `H'` when
`ancestryVariance` is the residual variance after correction.

    Regime: the marker's loading on the axis and the ancestry coordinate
    independent and centred. Independence is what makes the variance of their
    product the product of their variances; correlated loadings would add a
    covariance term this body has no room for.

    Empirical status: **VALIDATED** (`simcov/battery_bulk41.py`, `group_a`).
    400000 individuals with an ancestry coordinate and a marker loading drawn
    independently; the observable is the realised variance of their product,
    which is the confounding component an ancestry gradient induces. Worst cell
    1.02 sems at 0.69% relative.

    Power: the two variances are swept in OPPOSITE directions -- (1, 1),
    (4, 0.25), (0.5, 2), (2, 3) -- so a body that is merely monotone in each
    argument cannot survive. The SUM is FALSIFIED at 483 sems (324% relative)
    and the GEOMETRIC MEAN at 88 sems (59%), which is what fixes the
    combination as multiplicative rather than either of the obvious
    alternatives.

    The error bar is inflated threefold over the normal formula for a variance,
    because the product of two centred normals is heavy-tailed and the normal
    sem understates its own scatter -- the same correction that turned a
    spurious falsification of `spikeAndSlabVariance` into the noise it was. -/
noncomputable def ancestryGradientSusceptibility
    (markerAxisVariance ancestryVariance : ℝ) : ℝ :=
  Descent.Core.product markerAxisVariance ancestryVariance

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ancestryGradientSusceptibility_at_reference_point :
    ancestryGradientSusceptibility (1 / 2) (1 / 2) = 1 / 4 := by
  unfold ancestryGradientSusceptibility Descent.Core.product
  norm_num

/-- A lower bound on residual ancestry energy immediately induces a lower
bound on residual susceptibility `H'`. -/
theorem residual_susceptibility_lower_bound
    (markerAxisVariance residualFloor residualAncestryVariance : ℝ)
    (hmarker : 0 ≤ markerAxisVariance)
    (hfloor : residualFloor ≤ residualAncestryVariance) :
    markerAxisVariance * residualFloor ≤
      ancestryGradientSusceptibility markerAxisVariance residualAncestryVariance := by
  unfold ancestryGradientSusceptibility Descent.Core.product
  exact mul_le_mul_of_nonneg_left hfloor hmarker

/-- The sub-threshold overlap envelope therefore gives a directly reportable
floor on `H'`: marker-axis variance times the confounding energy not captured
by the fitted sample PCs. -/
theorem subthreshold_overlap_implies_susceptibility_floor
    (m : EmpiricalPCOverlapModel) (ε markerAxisVariance : ℝ)
    (hmarker : 0 ≤ markerAxisVariance)
    (hoverlap : ∀ i, m.overlapSq i ≤ ε ^ 2) :
    markerAxisVariance *
        (m.confoundingEnergy - (m.k : ℝ) * ε ^ 2) ≤
      ancestryGradientSusceptibility markerAxisVariance m.residualBiasEnergy := by
  exact residual_susceptibility_lower_bound
    markerAxisVariance
    (m.confoundingEnergy - (m.k : ℝ) * ε ^ 2)
    m.residualBiasEnergy hmarker
    (residual_bias_floor_of_subthreshold_overlap m ε hoverlap)

/-- Fraction of a target ancestry axis captured by correction, written in the
form `V_K = 1 - H'/H`. -/
noncomputable def pcTargetAxisEfficacy
    (uncorrectedSusceptibility residualSusceptibility : ℝ) : ℝ :=
  Descent.Core.proportionalReduction residualSusceptibility uncorrectedSusceptibility

/-- **Principal-component correction efficacy against a null susceptibility, named.** If the
uncorrected susceptibility is zero there was nothing to correct and the efficacy is undefined.
Lean returns `1`: PERFECT correction, the best possible score, awarded for correcting a
susceptibility that was not there. A diagnostic that scores its own inapplicability as success is
the wrong way round. Consumers must require `uncorrectedSusceptibility ≠ 0`. -/
theorem pcTargetAxisEfficacy_null_susceptibility_is_junk (residualSusceptibility : ℝ) :
    pcTargetAxisEfficacy 0 residualSusceptibility = 1 := by
  unfold pcTargetAxisEfficacy Descent.Core.proportionalReduction
  simp

/-- Rearranging the efficacy definition recovers the residual susceptibility
exactly. -/
theorem residual_susceptibility_eq_one_sub_efficacy_mul
    (H Hres : ℝ) (hH : H ≠ 0) :
    Hres = (1 - pcTargetAxisEfficacy H Hres) * H := by
  unfold pcTargetAxisEfficacy Descent.Core.proportionalReduction
  field_simp
  ring

/-- Multiplicative effect of directional ascertainment (`Φ`) and global
SNP-count inflation (`Λ`) on standardized PGS bias. -/
noncomputable def ascertainmentAmplification (Φ Λ : ℝ) : ℝ :=
  (1 + Φ + Λ) / Real.sqrt (1 + Λ)

/-- **ascertainmentAmplification at its junk point, named.** At `Λ = -1` the normalising square
root vanishes and the amplification diverges. `Real.sqrt 0` is zero, the divisor is zero, and
Lean returns `0`: no amplification at all where it is unbounded. Consumers must exclude the
argument that makes the guard vanish. -/
theorem ascertainmentAmplification_unit_negative_lambda_is_junk (Φ : ℝ) :
    ascertainmentAmplification Φ (-1) = 0 := by
  unfold ascertainmentAmplification
  simp

/-- Coefficient multiplying the magnitude of environmental confounding in the
standardized PGS bias formula.  `expectedSNPCount` corresponds to `L Sbar`,
`Hres` to residual susceptibility `H'`, and `effectSD` to `σβ`.

    Empirical status: UNTESTED. -/
noncomputable def pgsStratificationRiskCoefficient
    (expectedSNPCount Hres effectSD Φ Λ : ℝ) : ℝ :=
  Real.sqrt expectedSNPCount * Real.sqrt Hres / effectSD *
    ascertainmentAmplification Φ Λ

/-- A zero effect scale divides by zero and Mathlib returns `0`, so the study is reported as
carrying no stratification risk exactly when its effect units are degenerate. -/
theorem pgsStratificationRiskCoefficient_at_zero_effect_scale_is_junk
    (expectedSNPCount Hres Φ Λ : ℝ) :
    pgsStratificationRiskCoefficient expectedSNPCount Hres 0 Φ Λ = 0 := by
  unfold pgsStratificationRiskCoefficient
  simp


/-- Standardized residual stratification bias is linear in the confounding
magnitude once the study design and residual target-axis geometry are fixed.

**"Fixed study design" has to mean the ascertained VARIANT SET, not the
ascertainment threshold.** Those are different conditions and the
proportionality holds under only one of them.

    Empirical status: **FALSIFIED** when the ascertainment threshold is what is
    held fixed, and it holds to 1.1 sems when the variant set is
    (`validation/empirical/simcov/battery_strat01.py`). A confounded
    null: 1500 candidate variants carrying an ancestry-frequency gradient, 8000
    GWAS and 8000 target individuals, no variant causal, phenotype `c·a + noise`
    on a standardized ancestry axis. The observable is the regression slope of
    the score on the TARGET panel's ancestry axis over `σβ`. The coefficient is
    read as `bias(c₀)/c₀` on four replicates at `c₀ = 0.4` and the prediction is
    compared on eight DISJOINT replicates across an eightfold range of `c`, so
    no input comes from the replicates the oracle measures.

      c      variants   this body   measured             sems
      0.15      282      246.33      163.10±8.49         9.80
      0.30      716      492.67      479.37±11.08        1.20
      0.40      858      656.89      679.60±13.48        1.68
      0.80     1097     1313.78     1400.35±16.98        5.10
      1.20     1169     1970.67     2108.78±25.63        5.39

    The relation is convex, not proportional: 51% high at the bottom of the
    range and 6% low at the top. The mechanism is in the second column — more
    confounding puts more variants over the threshold, 282 to 1169 across the
    sweep, so the summary the coefficient is a function of moves with the very
    quantity it multiplies. Holding the SELECTED SET fixed instead removes it
    entirely: the same code path then tracks `K·c` at worst 1.1 sems over the
    same eightfold range, which is also the check that the design can reproduce
    proportionality when proportionality is what is there.

    The identity gate: the quadratic `K·c₀·(c/c₀)²`, which agrees with this body
    exactly at the anchor and diverges either side of it, is rejected at up to
    148 sems and 180%. So the truth lies between the two shapes and the design
    discriminates shape rather than merely calibration. The positive control —
    the same pipeline with the confounder off and real additive effects of known
    size, whose mean marginal estimate must recover them — passes at 0.87 sems.

    WHAT THIS DOES NOT SETTLE: the functional form of
    `pgsStratificationRiskCoefficient` itself, which is a separate question and
    is not on trial here. Whatever that coefficient is, this battery calibrates
    it from data and tests only the proportionality it is asserted to enter by.

    Consumers are affected in one direction. `criticalConfoundingMagnitude`
    inverts the proportionality to report how much confounding would be needed
    to produce an observed signal; under threshold ascertainment it therefore
    OVERSTATES the confounding required at small signals — 246 where 163 was
    measured — which is the reassuring direction and the wrong one. -/
noncomputable def standardizedResidualPGSBias
    (expectedSNPCount Hres effectSD Φ Λ confounding : ℝ) : ℝ :=
  pgsStratificationRiskCoefficient expectedSNPCount Hres effectSD Φ Λ * confounding

/-- Reference evaluation: no confounding, no standardized residual bias. -/
theorem standardizedResidualPGSBias_at_no_confounding
    (expectedSNPCount Hres effectSD Φ Λ : ℝ) :
    standardizedResidualPGSBias expectedSNPCount Hres effectSD Φ Λ 0 = 0 := by
  unfold standardizedResidualPGSBias
  ring


/-- Environmental confounding magnitude required to reach a specified
standardized signal under the residual-susceptibility model. -/
noncomputable def criticalConfoundingMagnitude
    (criticalSignal expectedSNPCount Hres effectSD Φ Λ : ℝ) : ℝ :=
  criticalSignal /
    pgsStratificationRiskCoefficient expectedSNPCount Hres effectSD Φ Λ

/-- **criticalConfoundingMagnitude at a null effect standard deviation, named.** The
stratification coefficient divides by the effect standard deviation, so at zero it is junk-zero,
and this quantity then divides by that zero and is junk-zero in turn. Two branches in sequence:
no confounding magnitude is critical, reported for a design where any confounding is. Consumers
must exclude it by hypothesis. -/
theorem criticalConfoundingMagnitude_null_effect_sd_is_junk
    (criticalSignal expectedSNPCount Hres : ℝ) :
    criticalConfoundingMagnitude criticalSignal expectedSNPCount Hres 0 = 0 := by
  funext Φ Λ
  norm_num [criticalConfoundingMagnitude, pgsStratificationRiskCoefficient]

/-- The critical-confounding diagnostic is exact whenever its risk coefficient
is nonzero.  This is the formal version of bracketing whether an observed PGS
gradient could plausibly be generated by residual stratification. -/
theorem standardized_bias_at_critical_confounding
    (criticalSignal expectedSNPCount Hres effectSD Φ Λ : ℝ)
    (hcoefficient :
      pgsStratificationRiskCoefficient expectedSNPCount Hres effectSD Φ Λ ≠ 0) :
    standardizedResidualPGSBias expectedSNPCount Hres effectSD Φ Λ
        (criticalConfoundingMagnitude criticalSignal expectedSNPCount Hres effectSD Φ Λ) =
      criticalSignal := by
  unfold standardizedResidualPGSBias criticalConfoundingMagnitude
  exact mul_div_cancel₀ criticalSignal hcoefficient

/-- For a positive risk coefficient, confounding reaches a positive signal
threshold exactly when it exceeds the reported critical magnitude. -/
theorem signal_exceeds_threshold_iff_confounding_exceeds_critical
    (criticalSignal expectedSNPCount Hres effectSD Φ Λ confounding : ℝ)
    (hcoefficient :
      0 < pgsStratificationRiskCoefficient expectedSNPCount Hres effectSD Φ Λ) :
    criticalSignal ≤
        standardizedResidualPGSBias expectedSNPCount Hres effectSD Φ Λ confounding ↔
      criticalConfoundingMagnitude criticalSignal expectedSNPCount Hres effectSD Φ Λ ≤
        confounding := by
  unfold standardizedResidualPGSBias criticalConfoundingMagnitude
  rw [mul_comm]
  exact (div_le_iff₀ hcoefficient).symm

/-- Exact two-point non-identifiability: if a confounded-null state and a
causal-differentiation state produce the same observation but have different
causal targets, no estimator can recover the target on both.  Mutual
contiguity supplies the asymptotic, quantitative analogue of this collision. -/
theorem no_exact_estimator_of_two_point_collision
    {Parameter Observation : Type}
    (observe : Parameter → Observation) (causalTarget : Parameter → ℝ)
    (confoundedNull causalAlternative : Parameter)
    (h_observation : observe confoundedNull = observe causalAlternative)
    (h_target : causalTarget confoundedNull ≠ causalTarget causalAlternative) :
    ¬ ∃ estimator : Observation → ℝ,
        ∀ parameter, estimator (observe parameter) = causalTarget parameter := by
  rintro ⟨estimator, hcorrect⟩
  apply h_target
  calc
    causalTarget confoundedNull = estimator (observe confoundedNull) :=
      (hcorrect confoundedNull).symm
    _ = estimator (observe causalAlternative) := congrArg estimator h_observation
    _ = causalTarget causalAlternative := hcorrect causalAlternative

/-- In the idealized population-eigenvector model, adding one *true* ancestry
PC removes its positive eigenvalue contribution.  This lemma does not apply to
sub-threshold sample PCs, whose overlap with the demographic direction may be
negligible and whose estimation cost can dominate the removed bias. -/
theorem more_exact_population_pcs_reduce_modeled_residual
    (p : ℕ) (eigenvals : Fin p → ℝ) (c : ℝ) (k : ℕ)
    (h_c : 0 < c)
    (h_eig_pos : ∀ i, 0 < eigenvals i)
    (h_k_bound : k + 2 < p) :
    c * (∑ i : Fin p, if k + 1 < i.val then eigenvals i else 0) <
      c * (∑ i : Fin p, if k < i.val then eigenvals i else 0) := by
  apply mul_lt_mul_of_pos_left _ h_c
  apply Finset.sum_lt_sum
  · intro i _
    split_ifs with h1 h2
    · exact le_refl _
    · exfalso
      exact h2 (lt_trans (Nat.lt_succ_self k) h1)
    · exact le_of_lt (h_eig_pos i)
    · exact le_refl _
  · have hk1_bound : k + 1 < p := by
      exact lt_trans (Nat.lt_succ_self (k + 1)) h_k_bound
    refine ⟨⟨k + 1, hk1_bound⟩, Finset.mem_univ _, ?_⟩
    simp only [show ¬(k + 1 < k + 1) from lt_irrefl _, ite_false,
               show k < k + 1 from Nat.lt_succ_iff.mpr (le_refl _), ite_true]
    exact h_eig_pos _

end Descent.Portability
