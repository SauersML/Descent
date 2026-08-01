import Calibrator.PCCorrectability.Core
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Spectral phase and residual-overlap bounds
-/

/-!
### Detectability phase boundary

The following definitions isolate the finite-dimensional algebra from the
random-matrix input.  `bbpProxyThreshold` is the usual rank-one proxy
`√(n/M)`, while the rank-one demographic spike is `2 F m_eff`, with
`m_eff = m(n-m)/n`.  This is the same parameterization used by the executable
calculator.  A theorem connecting a non-i.i.d. genotype ensemble to this model
must still justify its effective marker count. The exact spiked-covariance
overlap algebra is isolated in `PCCorrectability.Overlap`.
-/

/-- Effective size of a subgroup contrast with subgroup size `m` in a panel of
size `n`. -/
noncomputable def effectiveSubgroupSize (n m : ℝ) : ℝ := m * (n - m) / n

/-- Rank-one signal contributed by a subgroup contrast with differentiation
`F`. -/
noncomputable def demographicSpike (n F m : ℝ) : ℝ :=
  2 * F * effectiveSubgroupSize n m

/-- BBP-style proxy threshold for `n` samples and `M` effectively independent
markers. -/
noncomputable def bbpProxyThreshold (n M : ℝ) : ℝ :=
  Real.sqrt (n / M)

/-- Signed distance from the spike to the spectral proxy threshold.  A positive
value is the detectable side of the phase diagram. -/
noncomputable def pcCorrectabilityMargin (n M F m : ℝ) : ℝ :=
  demographicSpike n F m - bbpProxyThreshold n M

/-- `F_ST` alone cannot determine PC correctability: at fixed positive `F`,
sample size, and marker count, two valid subgroup sizes lie on opposite sides
of the spectral threshold whenever the balanced contrast is detectable. -/
theorem fst_does_not_determine_pc_correctability
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    bbpProxyThreshold n M < F * n / 2 →
      ∃ mBelow mAbove : ℝ,
        0 < mBelow ∧ mBelow < n ∧
        0 < mAbove ∧ mAbove < n ∧
        demographicSpike n F mBelow < bbpProxyThreshold n M ∧
        bbpProxyThreshold n M < demographicSpike n F mAbove := by
  intro hdetectable
  let t := bbpProxyThreshold n M
  have ht : 0 < t := by
    unfold t bbpProxyThreshold
    exact Real.sqrt_pos.2 (div_pos hn hM)
  let mBelow := t / (4 * F)
  let mAbove := n / 2
  have hmBelow_pos : 0 < mBelow := by
    exact div_pos ht (mul_pos (by norm_num) hF)
  have hmBelow_lt : mBelow < n := by
    unfold mBelow
    rw [div_lt_iff₀ (mul_pos (by norm_num) hF)]
    nlinarith [hdetectable]
  have hmAbove_pos : 0 < mAbove := by
    unfold mAbove
    linarith
  have hmAbove_lt : mAbove < n := by
    unfold mAbove
    linarith
  have heffective_below_lt : effectiveSubgroupSize n mBelow < mBelow := by
    unfold effectiveSubgroupSize
    rw [div_lt_iff₀ hn]
    nlinarith
  have htwice_below : 2 * F * mBelow = t / 2 := by
    unfold mBelow
    field_simp [hF.ne']
    norm_num
  have hspike_below : demographicSpike n F mBelow < t := by
    unfold demographicSpike
    calc
      2 * F * effectiveSubgroupSize n mBelow < 2 * F * mBelow :=
        mul_lt_mul_of_pos_left heffective_below_lt (mul_pos (by norm_num) hF)
      _ = t / 2 := htwice_below
      _ < t := half_lt_self ht
  have hspike_above : t < demographicSpike n F mAbove := by
    have hidentity : demographicSpike n F mAbove = F * n / 2 := by
      unfold demographicSpike effectiveSubgroupSize mAbove
      field_simp [hn.ne']
      ring
    rw [hidentity]
    exact hdetectable
  exact ⟨mBelow, mAbove, hmBelow_pos, hmBelow_lt, hmAbove_pos, hmAbove_lt,
    hspike_below, hspike_above⟩

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
  subgroupSize_lt_n : subgroupSize < n
  belowThreshold :
    demographicSpike n differentiation subgroupSize ≤ bbpProxyThreshold n markers
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
