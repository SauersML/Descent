import Calibrator.PCCorrectability.Core

namespace Calibrator

/-!
# Spectral phase and residual-overlap bounds
-/

/-!
### Detectability phase boundary

The following definitions isolate the finite-dimensional algebra from the
random-matrix input.  `bbpProxyThreshold` is the usual rank-one proxy
`(1/2)√(n/M)`, while the demographic spike is `F · m`.  A theorem connecting a
particular genotype ensemble to this proxy must supply an eigenvector-overlap
bound; that probabilistic theorem is deliberately not assumed here.
-/

/-- Rank-one signal contributed by a subgroup of effective size `m` and
differentiation `F`. -/
noncomputable def demographicSpike (F m : ℝ) : ℝ := F * m

/-- BBP-style proxy threshold for `n` samples and `M` effectively independent
markers. -/
noncomputable def bbpProxyThreshold (n M : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (n / M)

/-- Signed distance from the spike to the spectral proxy threshold.  A positive
value is the detectable side of the phase diagram. -/
noncomputable def pcCorrectabilityMargin (n M F m : ℝ) : ℝ :=
  demographicSpike F m - bbpProxyThreshold n M

/-- `F_ST` alone cannot determine PC correctability: at fixed positive `F`,
sample size, and marker count, two subgroup sizes lie on opposite sides of the
spectral threshold. -/
theorem fst_does_not_determine_pc_correctability
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    ∃ mBelow mAbove : ℝ,
      0 < mBelow ∧ 0 < mAbove ∧
      demographicSpike F mBelow < bbpProxyThreshold n M ∧
      bbpProxyThreshold n M < demographicSpike F mAbove := by
  let t := bbpProxyThreshold n M
  have ht : 0 < t := by
    unfold t bbpProxyThreshold
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 (div_pos hn hM))
  refine ⟨t / (2 * F), 2 * t / F, ?_, ?_, ?_, ?_⟩
  · exact div_pos ht (mul_pos (by norm_num) hF)
  · exact div_pos (mul_pos (by norm_num) ht) hF
  · have hidentity : demographicSpike F (t / (2 * F)) = t / 2 := by
      unfold demographicSpike
      field_simp [hF.ne']
    rw [hidentity]
    exact half_lt_self ht
  · have hidentity : demographicSpike F (2 * t / F) = 2 * t := by
      unfold demographicSpike
      field_simp [hF.ne']
    rw [hidentity]
    linarith

/-- Empirical-PC overlap summary.  `overlapSq i` is the squared overlap between
the `i`th fitted PC and the true confounding direction. -/
structure EmpiricalPCOverlapModel where
  k : ℕ
  confoundingEnergy : ℝ
  overlapSq : Fin k → ℝ
  overlapSq_nonneg : ∀ i, 0 ≤ overlapSq i
  overlapSq_sum_le : (∑ i, overlapSq i) ≤ confoundingEnergy

/-- Confounding energy left after removing the fitted PCs. -/
noncomputable def EmpiricalPCOverlapModel.residualBiasEnergy
    (m : EmpiricalPCOverlapModel) : ℝ :=
  m.confoundingEnergy - ∑ i, m.overlapSq i

/-- A uniform eigenvector-overlap envelope gives a residual-bias floor uniform
over the fitted PCs: `K` overlaps of at most `ε²` can remove at most `K ε²`
confounding energy.  This is the deterministic bridge needed from a
sub-threshold sparse-spike overlap theorem. -/
theorem residual_bias_floor_of_subthreshold_overlap
    (m : EmpiricalPCOverlapModel) (ε : ℝ)
    (hoverlap : ∀ i, m.overlapSq i ≤ ε ^ 2) :
    m.confoundingEnergy - (m.k : ℝ) * ε ^ 2 ≤ m.residualBiasEnergy := by
  have hsum : (∑ i, m.overlapSq i) ≤ ∑ _i : Fin m.k, ε ^ 2 := by
    exact Finset.sum_le_sum (fun i _ => hoverlap i)
  have hsum' : (∑ i, m.overlapSq i) ≤ (m.k : ℝ) * ε ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  unfold EmpiricalPCOverlapModel.residualBiasEnergy
  linarith

/-- A certificate packages the external random-matrix conclusion with the
finite-sample correction model.  The threshold inequality and overlap envelope
are kept separate because threshold-to-overlap is the genuinely hard theorem
for sparse, LD-dependent genotype matrices. -/
structure SubthresholdPCCertificate extends EmpiricalPCOverlapModel where
  n : ℝ
  markers : ℝ
  differentiation : ℝ
  subgroupSize : ℝ
  n_pos : 0 < n
  markers_pos : 0 < markers
  differentiation_pos : 0 < differentiation
  subgroupSize_pos : 0 < subgroupSize
  belowThreshold :
    demographicSpike differentiation subgroupSize ≤ bbpProxyThreshold n markers
  overlapEnvelope : ℝ
  overlap_bound : ∀ i, overlapSq i ≤ overlapEnvelope ^ 2

/-- Certified sub-threshold structure has both a nonpositive correctability
margin and the quantitative residual-bias floor implied by its overlap bound. -/
theorem subthreshold_pc_residual_bias_floor (m : SubthresholdPCCertificate) :
    pcCorrectabilityMargin m.n m.markers m.differentiation m.subgroupSize ≤ 0 ∧
      m.confoundingEnergy - (m.k : ℝ) * m.overlapEnvelope ^ 2 ≤
        m.residualBiasEnergy := by
  constructor
  · unfold pcCorrectabilityMargin
    exact sub_nonpos.mpr m.belowThreshold
  · exact residual_bias_floor_of_subthreshold_overlap
      m.toEmpiricalPCOverlapModel m.overlapEnvelope m.overlap_bound

/-- Exact one-step bias--variance accounting for adding an empirical PC. -/
theorem pc_step_total_error_change
    (residualBias estimationVariance biasRemoved varianceAdded : ℝ) :
    ((residualBias - biasRemoved) + (estimationVariance + varianceAdded)) -
        (residualBias + estimationVariance) = varianceAdded - biasRemoved := by
  ring

/-- Adding a PC increases total error whenever its estimation-variance cost
exceeds the confounding bias it removes.  Thus empirical correction is not
monotone in `K` without a signal-overlap assumption. -/
theorem adding_subthreshold_pc_can_increase_total_error
    (residualBias estimationVariance biasRemoved varianceAdded : ℝ)
    (hcost : biasRemoved < varianceAdded) :
    residualBias + estimationVariance <
      (residualBias - biasRemoved) + (estimationVariance + varianceAdded) := by
  linarith

/-- Dimensionless danger index from the different marker scalings of aggregate
PGS bias and spectral detectability. -/
noncomputable def markerDangerIndex (confounding n markers : ℝ) : ℝ :=
  confounding * Real.sqrt (markers / n)

/-- At fixed sample size and positive confounding, increasing the number of
effectively independent markers strictly increases the danger index. -/
theorem more_markers_increase_uncorrectable_bias_danger
    (confounding n markers₁ markers₂ : ℝ)
    (hconfounding : 0 < confounding) (hn : 0 < n)
    (hmarkers₁ : 0 < markers₁) (hmore : markers₁ < markers₂) :
    markerDangerIndex confounding n markers₁ <
      markerDangerIndex confounding n markers₂ := by
  unfold markerDangerIndex
  apply mul_lt_mul_of_pos_left _ hconfounding
  apply Real.sqrt_lt_sqrt (div_nonneg (le_of_lt hmarkers₁) (le_of_lt hn))
  exact (div_lt_div_iff_of_pos_right hn).2 hmore

end Calibrator
