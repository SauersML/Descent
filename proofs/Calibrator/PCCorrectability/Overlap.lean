/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.PCCorrectability.Threshold

namespace Calibrator

/-!
# Johnstone--Paul overlap curve

Writing `c = n/M` and `s = λ - 1` for the population spike above the noise
eigenvalue, the asymptotic squared overlap is
`(1 - c/s²) / (1 + c/s)` above `s = √c`, and zero below it.
-/

/-- Squared sample/population eigenvector overlap in the rank-one
spiked-covariance model. -/
noncomputable def samplePCOverlapSq (n M spike : ℝ) : ℝ :=
  if bbpProxyThreshold n M < spike then
    (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike)
  else 0

/-- Below the BBP edge, the modeled eigenvector overlap is exactly zero. -/
theorem samplePCOverlapSq_eq_zero_of_subthreshold
    (n M spike : ℝ) (h : spike ≤ bbpProxyThreshold n M) :
    samplePCOverlapSq n M spike = 0 := by
  simp [samplePCOverlapSq, not_lt.mpr h]

/-- Above the BBP edge, the implementation uses the Johnstone--Paul overlap
formula exactly. -/
theorem samplePCOverlapSq_eq_of_superthreshold
    (n M spike : ℝ) (h : bbpProxyThreshold n M < spike) :
    samplePCOverlapSq n M spike =
      (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike) := by
  simp [samplePCOverlapSq, h]

/-- Above the edge, the Johnstone--Paul squared overlap is strictly between
zero and one for positive sample and marker counts. -/
theorem samplePCOverlapSq_pos_and_lt_one
    (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h : bbpProxyThreshold n M < spike) :
    0 < samplePCOverlapSq n M spike ∧ samplePCOverlapSq n M spike < 1 := by
  rw [samplePCOverlapSq_eq_of_superthreshold n M spike h]
  have hc : 0 < n / M := div_pos hn hM
  have ht : 0 < bbpProxyThreshold n M := Real.sqrt_pos.2 hc
  have hspike : 0 < spike := ht.trans h
  have ht_sq : bbpProxyThreshold n M ^ 2 = n / M := by
    unfold bbpProxyThreshold
    exact Real.sq_sqrt (le_of_lt hc)
  have hc_lt_spike_sq : n / M < spike ^ 2 := by
    rw [← ht_sq]
    exact (sq_lt_sq₀ (le_of_lt ht) (le_of_lt hspike)).2 h
  have hspike_sq : 0 < spike ^ 2 := sq_pos_of_pos hspike
  have hratio_pos : 0 < (n / M) / spike ^ 2 := div_pos hc hspike_sq
  have hratio_lt_one : (n / M) / spike ^ 2 < 1 :=
    (div_lt_one hspike_sq).2 hc_lt_spike_sq
  have hnum : 0 < 1 - (n / M) / spike ^ 2 := sub_pos.mpr hratio_lt_one
  have hlinear_ratio : 0 < (n / M) / spike := div_pos hc hspike
  have hdenom : 0 < 1 + (n / M) / spike := by linarith
  constructor
  · exact div_pos hnum hdenom
  · rw [div_lt_one hdenom]
    linarith

/-- Fraction of the target ancestry axis left after projection onto the modeled
sample PC. -/
noncomputable def samplePCResidualAxisFraction (n M spike : ℝ) : ℝ :=
  1 - samplePCOverlapSq n M spike

/-- A sub-threshold sample PC leaves the entire target axis unresolved.  Thus,
in the rank-one model, increasing the requested PC count cannot recover an axis
whose empirical eigenvector has zero overlap with its population direction. -/
theorem subthreshold_sample_pc_leaves_full_axis
    (n M spike : ℝ) (h : spike ≤ bbpProxyThreshold n M) :
    samplePCResidualAxisFraction n M spike = 1 := by
  rw [samplePCResidualAxisFraction, samplePCOverlapSq_eq_zero_of_subthreshold n M spike h]
  ring

/-- Above the edge, the residual fraction is exactly one minus the
Johnstone--Paul overlap used by the executable calculator. -/
theorem superthreshold_sample_pc_residual_fraction
    (n M spike : ℝ) (h : bbpProxyThreshold n M < spike) :
    samplePCResidualAxisFraction n M spike =
      1 - (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike) := by
  rw [samplePCResidualAxisFraction, samplePCOverlapSq_eq_of_superthreshold n M spike h]

/-- A detectable finite spike is only partially recovered: its modeled residual
axis fraction is also strictly between zero and one. -/
theorem samplePCResidualAxisFraction_pos_and_lt_one
    (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h : bbpProxyThreshold n M < spike) :
    0 < samplePCResidualAxisFraction n M spike ∧
      samplePCResidualAxisFraction n M spike < 1 := by
  have hoverlap := samplePCOverlapSq_pos_and_lt_one n M spike hn hM h
  unfold samplePCResidualAxisFraction
  constructor <;> linarith

/-- Above the phase transition, the residual fraction has a closed rational
form.  This is algebraically equivalent to one minus the Johnstone--Paul
overlap but is better suited to design calculations and monotonicity proofs. -/
theorem samplePCResidualAxisFraction_eq_rational
    (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h : bbpProxyThreshold n M < spike) :
    samplePCResidualAxisFraction n M spike =
      (n / M) * (spike + 1) / (spike * (spike + n / M)) := by
  rw [superthreshold_sample_pc_residual_fraction n M spike h]
  have hratio : 0 < n / M := div_pos hn hM
  have hedge : 0 < bbpProxyThreshold n M := Real.sqrt_pos.2 hratio
  have hspike : 0 < spike := hedge.trans h
  field_simp [ne_of_gt hspike]
  ring

/-- Once the spike is detectable, increasing its strength strictly decreases
the fraction of the target axis left after projecting out the sample PC. -/
theorem samplePCResidualAxisFraction_strictAntiOn_superthreshold
    (n M spike₁ spike₂ : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h₁ : bbpProxyThreshold n M < spike₁) (h₂ : spike₁ < spike₂) :
    samplePCResidualAxisFraction n M spike₂ <
      samplePCResidualAxisFraction n M spike₁ := by
  have hratio : 0 < n / M := div_pos hn hM
  have hedge : 0 < bbpProxyThreshold n M := Real.sqrt_pos.2 hratio
  have hspike₁ : 0 < spike₁ := hedge.trans h₁
  have hspike₂ : 0 < spike₂ := hspike₁.trans h₂
  have h₂super : bbpProxyThreshold n M < spike₂ := h₁.trans h₂
  rw [samplePCResidualAxisFraction_eq_rational n M spike₁ hn hM h₁,
    samplePCResidualAxisFraction_eq_rational n M spike₂ hn hM h₂super]
  have hdenominator₁ : 0 < spike₁ * (spike₁ + n / M) :=
    mul_pos hspike₁ (add_pos hspike₁ hratio)
  have hdenominator₂ : 0 < spike₂ * (spike₂ + n / M) :=
    mul_pos hspike₂ (add_pos hspike₂ hratio)
  rw [div_lt_div_iff₀ hdenominator₂ hdenominator₁]
  have hfactor :
      0 < (spike₂ - spike₁) *
        (spike₁ * spike₂ + spike₁ + spike₂ + n / M) := by
    apply mul_pos (sub_pos.mpr h₂)
    positivity
  have hcore :
      (spike₂ + 1) * (spike₁ * (spike₁ + n / M)) <
        (spike₁ + 1) * (spike₂ * (spike₂ + n / M)) := by
    nlinarith
  simpa only [mul_assoc] using mul_lt_mul_of_pos_left hcore hratio

end Calibrator
