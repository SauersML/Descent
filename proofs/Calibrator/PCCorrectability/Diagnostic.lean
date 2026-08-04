/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PCCorrectability.Phase
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Calibrator

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

    Empirical status: UNTESTED. -/
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
lower bound becomes a lower bound on `H'`, and how `H'` combines with
ascertainment to determine the critical confounding magnitude.
-/

/-- Genetic variance in the GWAS panel explained by a specified external
ancestry gradient.  This is `H` before correction and `H'` when
`ancestryVariance` is the residual variance after correction.

    Empirical status: UNTESTED. -/
noncomputable def ancestryGradientSusceptibility
    (markerAxisVariance ancestryVariance : ℝ) : ℝ :=
  markerAxisVariance * ancestryVariance

/-- A lower bound on residual ancestry energy immediately induces a lower
bound on residual susceptibility `H'`. -/
theorem residual_susceptibility_lower_bound
    (markerAxisVariance residualFloor residualAncestryVariance : ℝ)
    (hmarker : 0 ≤ markerAxisVariance)
    (hfloor : residualFloor ≤ residualAncestryVariance) :
    markerAxisVariance * residualFloor ≤
      ancestryGradientSusceptibility markerAxisVariance residualAncestryVariance := by
  unfold ancestryGradientSusceptibility
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
  1 - residualSusceptibility / uncorrectedSusceptibility

/-- **Principal-component correction efficacy against a null susceptibility, named.** If the
uncorrected susceptibility is zero there was nothing to correct and the efficacy is undefined.
Lean returns `1`: PERFECT correction, the best possible score, awarded for correcting a
susceptibility that was not there. A diagnostic that scores its own inapplicability as success is
the wrong way round. Consumers must require `uncorrectedSusceptibility ≠ 0`. -/
theorem pcTargetAxisEfficacy_null_susceptibility_is_junk (residualSusceptibility : ℝ) :
    pcTargetAxisEfficacy 0 residualSusceptibility = 1 := by
  unfold pcTargetAxisEfficacy
  simp

/-- Rearranging the efficacy definition recovers the residual susceptibility
exactly. -/
theorem residual_susceptibility_eq_one_sub_efficacy_mul
    (H Hres : ℝ) (hH : H ≠ 0) :
    Hres = (1 - pcTargetAxisEfficacy H Hres) * H := by
  unfold pcTargetAxisEfficacy
  field_simp
  ring

/-- Multiplicative effect of directional ascertainment (`Φ`) and global
SNP-count inflation (`Λ`) on standardized PGS bias. -/
noncomputable def ascertainmentAmplification (Φ Λ : ℝ) : ℝ :=
  (1 + Φ + Λ) / Real.sqrt (1 + Λ)

/-- Coefficient multiplying the magnitude of environmental confounding in the
standardized PGS bias formula.  `expectedSNPCount` corresponds to `L Sbar`,
`Hres` to residual susceptibility `H'`, and `effectSD` to `σβ`.

    Empirical status: UNTESTED. -/
noncomputable def pgsStratificationRiskCoefficient
    (expectedSNPCount Hres effectSD Φ Λ : ℝ) : ℝ :=
  Real.sqrt expectedSNPCount * Real.sqrt Hres / effectSD *
    ascertainmentAmplification Φ Λ

/-- Standardized residual stratification bias is linear in the confounding
magnitude once the study design and residual target-axis geometry are fixed.

    Empirical status: UNTESTED. -/
noncomputable def standardizedResidualPGSBias
    (expectedSNPCount Hres effectSD Φ Λ confounding : ℝ) : ℝ :=
  pgsStratificationRiskCoefficient expectedSNPCount Hres effectSD Φ Λ * confounding

/-- Environmental confounding magnitude required to reach a specified
standardized signal under the residual-susceptibility model. -/
noncomputable def criticalConfoundingMagnitude
    (criticalSignal expectedSNPCount Hres effectSD Φ Λ : ℝ) : ℝ :=
  criticalSignal /
    pgsStratificationRiskCoefficient expectedSNPCount Hres effectSD Φ Λ

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

end Calibrator
