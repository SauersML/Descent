/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMetricIdentification

assert_below Descent.Decision Descent.Program

/-!
An exact linear-fractional transformation for finite conditional report means.
Normalization is retained explicitly as a row of the transformed constraints.
A positive success guard makes the inverse transformation well-defined.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GuardedMetricOptimization

open FiniteMetricIdentification

variable {S O : Type*} [Fintype S]

structure Linearized (observe : O → S → ℝ) (observed : O → ℝ)
    (acceptance : S → ℝ) (guard : ℝ) where
  weights : S → ℝ
  scale : ℝ
  nonneg : ∀ state, 0 ≤ weights state
  normalization : ∑ state, weights state = scale
  observations : ∀ observation, pairing (observe observation) weights = observed observation * scale
  accepted : pairing acceptance weights = 1
  scale_nonneg : 0 ≤ scale
  scale_upper : scale ≤ 1 / guard

variable (observe : O → S → ℝ) (observed : O → ℝ) (acceptance : S → ℝ) (guard : ℝ)

noncomputable def linearize (hguard : 0 < guard) (p : S → ℝ)
    (hp : p ∈ feasible observe observed) (haccept : guard ≤ pairing acceptance p) :
    Linearized observe observed acceptance guard where
  weights := (1 / pairing acceptance p) • p
  scale := 1 / pairing acceptance p
  nonneg := fun state ↦ mul_nonneg (one_div_nonneg.mpr (hguard.le.trans haccept)) (hp.1.1 state)
  normalization := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hp.1.2, mul_one]
  observations := by
    intro observation
    rw [pairing_smul, hp.2 observation, mul_comm]
  accepted := by
    rw [pairing_smul, one_div_mul_cancel (ne_of_gt (hguard.trans_le haccept))]
  scale_nonneg := one_div_nonneg.mpr (hguard.le.trans haccept)
  scale_upper := one_div_le_one_div_of_le hguard haccept

variable {observe observed acceptance guard}

theorem scale_pos (problem : Linearized observe observed acceptance guard) : 0 < problem.scale := by
  by_contra h
  have hz : problem.scale = 0 := le_antisymm (le_of_not_gt h) problem.scale_nonneg
  have hzero (state : S) : problem.weights state = 0 := by
    apply le_antisymm _ (problem.nonneg state)
    calc
      problem.weights state ≤ ∑ other, problem.weights other :=
        Finset.single_le_sum (fun other _ ↦ problem.nonneg other) (Finset.mem_univ state)
      _ = 0 := problem.normalization.trans hz
  have haccepted := problem.accepted
  simp only [pairing, hzero, mul_zero, Finset.sum_const_zero] at haccepted
  norm_num at haccepted

noncomputable def recover (problem : Linearized observe observed acceptance guard) : S → ℝ :=
  (1 / problem.scale) • problem.weights

theorem recover_feasible (problem : Linearized observe observed acceptance guard) :
    recover problem ∈ feasible observe observed := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro state
    exact mul_nonneg (one_div_nonneg.mpr problem.scale_nonneg) (problem.nonneg state)
  · simp only [recover, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, problem.normalization]
    exact one_div_mul_cancel (ne_of_gt (scale_pos problem))
  · intro observation
    rw [recover, pairing_smul, problem.observations]
    field_simp [ne_of_gt (scale_pos problem)]

theorem recover_acceptance (problem : Linearized observe observed acceptance guard) :
    pairing acceptance (recover problem) = 1 / problem.scale := by
  rw [recover, pairing_smul, problem.accepted, mul_one]

theorem recover_guard (hguard : 0 < guard)
    (problem : Linearized observe observed acceptance guard) :
    guard ≤ pairing acceptance (recover problem) := by
  rw [recover_acceptance]
  have hh := (le_div_iff₀ hguard).mp problem.scale_upper
  apply (le_div_iff₀ (scale_pos problem)).mpr
  nlinarith

theorem recover_linearize (hguard : 0 < guard) (p : S → ℝ)
    (hp : p ∈ feasible observe observed) (haccept : guard ≤ pairing acceptance p) :
    recover (linearize observe observed acceptance guard hguard p hp haccept) = p := by
  have hd : pairing acceptance p ≠ 0 := ne_of_gt (hguard.trans_le haccept)
  simp only [recover, linearize, one_div, inv_inv, smul_smul, mul_inv_cancel₀ hd, one_smul]

/-- The transformed objective equals the original guarded conditional mean. -/
theorem linearize_objective (hguard : 0 < guard) (p : S → ℝ)
    (hp : p ∈ feasible observe observed) (haccept : guard ≤ pairing acceptance p)
    (numerator : S → ℝ) :
    pairing numerator (linearize observe observed acceptance guard hguard p hp haccept).weights =
      pairing numerator p / pairing acceptance p := by
  rw [linearize, pairing_smul]
  ring

theorem recover_objective (problem : Linearized observe observed acceptance guard)
    (numerator : S → ℝ) :
    pairing numerator (recover problem) / pairing acceptance (recover problem) =
      pairing numerator problem.weights := by
  rw [recover_acceptance, recover, pairing_smul]
  field_simp [ne_of_gt (scale_pos problem)]

/-- Both optimization problems have exactly the same attainable objective values. -/
theorem attainable_objectives (hguard : 0 < guard) (numerator : S → ℝ) :
    {value | ∃ p ∈ feasible observe observed, guard ≤ pairing acceptance p ∧
      value = pairing numerator p / pairing acceptance p} =
      {value | ∃ problem : Linearized observe observed acceptance guard,
        value = pairing numerator problem.weights} := by
  ext value
  constructor
  · rintro ⟨p, hp, haccept, rfl⟩
    exact ⟨linearize observe observed acceptance guard hguard p hp haccept,
      (linearize_objective hguard p hp haccept numerator).symm⟩
  · rintro ⟨problem, rfl⟩
    exact ⟨recover problem, recover_feasible problem, recover_guard hguard problem,
      (recover_objective problem numerator).symm⟩

/-- Recovering a transformed point and transforming it again preserves both variables. -/
theorem linearize_recover (hguard : 0 < guard)
    (problem : Linearized observe observed acceptance guard) :
    (linearize observe observed acceptance guard hguard (recover problem)
      (recover_feasible problem) (recover_guard hguard problem)).weights = problem.weights ∧
    (linearize observe observed acceptance guard hguard (recover problem)
      (recover_feasible problem) (recover_guard hguard problem)).scale = problem.scale := by
  constructor
  · change (1 / pairing acceptance (recover problem)) • recover problem = problem.weights
    rw [recover_acceptance, recover]
    simp [one_div, smul_smul, ne_of_gt (scale_pos problem)]
  · change 1 / pairing acceptance (recover problem) = problem.scale
    rw [recover_acceptance, one_div_one_div]

end Descent.Portability.GuardedMetricOptimization
