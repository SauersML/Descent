/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.PCCorrectability.Core
import Calibrator.PCCorrectability.Threshold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Calibrator

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
