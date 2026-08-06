/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PCCorrectability.Core
import Descent.Portability.PCCorrectability.Threshold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

/-!
# Spectral phase and residual-overlap bounds
-/

/-- Empirical-PC overlap summary.  `overlapSq i` is the squared overlap between
the `i`th fitted PC and the true confounding direction. -/
structure EmpiricalPCOverlapModel where
  k : ℕ
  confoundingEnergy : ℝ
  overlapSq : Fin k → ℝ
  overlapSq_nonneg : ∀ i, 0 ≤ overlapSq i
  overlapSq_sum_le : (∑ i, overlapSq i) ≤ confoundingEnergy

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def EmpiricalPCOverlapModel.witness : EmpiricalPCOverlapModel where
  k := 1
  confoundingEnergy := 1
  overlapSq := fun _ ↦ 0
  overlapSq_nonneg := fun _ ↦ le_refl 0
  overlapSq_sum_le := by simp

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
    exact Finset.sum_le_sum (fun i _ ↦ hoverlap i)
  have hsum' : (∑ i, m.overlapSq i) ≤ (m.k : ℝ) * ε ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  unfold EmpiricalPCOverlapModel.residualBiasEnergy
  linarith

/-! No sub-threshold random-matrix conclusion is accepted as a certificate field.  The
algebraic overlap bound above remains reusable; connecting it to an LD-dependent genotype
matrix requires a proved random-matrix theorem in this repository. -/

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

/-- **markerDangerIndex at its junk point, named.** With no samples the confounding danger per
marker is unbounded. The ratio `markers / n` is junk-zero, its square root is zero, and the
index reports NO danger from a study with no data. Consumers must guard the argument that makes
the divisor vanish. -/
theorem markerDangerIndex_zero_samples_is_junk (confounding markers : ℝ) :
    markerDangerIndex confounding 0 markers = 0 := by
  unfold markerDangerIndex
  simp

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

/-- **The danger index is the confounding energy measured in units of the BBP
threshold.** The two aspect-ratio factors are exact reciprocals --
`markerDangerIndex` carries `√(M/n)` and `bbpProxyThreshold` carries `√(n/M)` --
so their product is the confounding energy alone, with the design dropping out
entirely.

This is why the two quantities belong in one phase diagram rather than two.
`more_markers_increase_uncorrectable_bias_danger` says the danger grows with the
panel and `bbpProxyThreshold_aspect_invariant` says detectability depends only
on `n/M`; stated separately those are two monotonicities in the same variable
with no stated relation, and a reader has no way to tell whether the danger
index is a second, independent scaling or the same one read from the other side.
It is the same one. Until this identity existed the module imported
`Descent.PCCorrectability.Threshold` and used nothing from it, so the
dependency was declared and never honoured. -/
theorem markerDangerIndex_mul_bbpProxyThreshold
    (confounding n markers : ℝ) (hn : 0 < n) (hmarkers : 0 < markers) :
    markerDangerIndex confounding n markers * bbpProxyThreshold n markers =
      confounding := by
  unfold markerDangerIndex bbpProxyThreshold
  have hproduct : markers / n * (n / markers) = 1 := by
    field_simp
  rw [mul_assoc, ← Real.sqrt_mul (div_nonneg hmarkers.le hn.le), hproduct,
    Real.sqrt_one, mul_one]

/-- **The detectable side of the phase diagram is exactly `danger index < 1`.**
A design corrects the confounder when the spike clears the BBP proxy threshold;
the identity above turns that comparison into a single dimensionless number, so
the phase boundary is at one rather than at a design-dependent value.

Note which direction is which: a LARGER danger index is the undetectable side.
The index rises with the panel, so adding effectively independent markers at
fixed sample size moves a design across the boundary in the wrong direction --
the content of `more_markers_increase_uncorrectable_bias_danger`, now located on
the phase diagram instead of standing alone. -/
theorem markerDangerIndex_lt_one_iff_confounding_lt_bbpProxyThreshold
    (confounding n markers : ℝ) (hn : 0 < n) (hmarkers : 0 < markers) :
    markerDangerIndex confounding n markers < 1 ↔
      confounding < bbpProxyThreshold n markers := by
  have hthreshold : 0 < bbpProxyThreshold n markers := by
    unfold bbpProxyThreshold
    exact Real.sqrt_pos.mpr (div_pos hn hmarkers)
  have hmul := markerDangerIndex_mul_bbpProxyThreshold confounding n markers hn hmarkers
  constructor
  · intro hdanger
    have hgap : 0 < (1 - markerDangerIndex confounding n markers) *
        bbpProxyThreshold n markers :=
      mul_pos (by linarith) hthreshold
    nlinarith [hmul, hgap]
  · intro hconfounding
    by_contra hdanger
    push_neg at hdanger
    have hgap : 0 ≤ (markerDangerIndex confounding n markers - 1) *
        bbpProxyThreshold n markers :=
      mul_nonneg (by linarith) hthreshold.le
    nlinarith [hmul, hgap]

end Descent.Portability
