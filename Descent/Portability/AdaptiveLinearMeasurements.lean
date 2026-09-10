/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TargetUncertainty
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

assert_below Descent.Decision Descent.Program

/-!
Deterministic adaptive noiseless linear measurements. The zero-response path
is part of the actual recursive procedure, not an assumed fixed-query surrogate.
Dimension forces an invisible unit direction on every subspace larger than the
query budget, giving a target-weighted minimax lower bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AdaptiveLinearMeasurements

open TargetUncertainty

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A deterministic query procedure may choose every later linear functional
and its final prediction as an arbitrary function of earlier exact responses. -/
inductive Procedure : ℕ → Type _
  | done (prediction : F) : Procedure 0
  | ask {q : ℕ} (question : E →L[ℝ] ℝ) (continuation : ℝ → Procedure q) : Procedure (q + 1)

variable {E F}

namespace Procedure

def run : {q : ℕ} → Procedure E F q → E → F
  | 0, .done prediction, _ => prediction
  | _ + 1, .ask question continuation, v => (continuation (question v)).run v

def zeroPrediction : {q : ℕ} → Procedure E F q → F
  | 0, .done prediction => prediction
  | _ + 1, .ask _ continuation => (continuation 0).zeroPrediction

def zeroQuestions : {q : ℕ} → Procedure E F q → Fin q → E →L[ℝ] ℝ
  | 0, .done _, j => Fin.elim0 j
  | _ + 1, .ask question continuation, j =>
      Fin.cases question (fun i ↦ (continuation 0).zeroQuestions i) j

/-- An input annihilating the questions actually selected on the zero path
follows that same path, including every adaptive branch choice. -/
theorem run_eq_zeroPrediction {q : ℕ} (procedure : Procedure E F q) (v : E)
    (hzero : ∀ j, procedure.zeroQuestions j v = 0) :
    procedure.run v = procedure.zeroPrediction := by
  induction q with
  | zero => cases procedure; rfl
  | succ q ih =>
    cases procedure with
    | ask question continuation =>
      have hfirst : question v = 0 := by simpa only [zeroQuestions, Fin.cases_zero] using hzero 0
      simp only [run, hfirst, zeroPrediction]
      apply ih (continuation 0)
      intro j
      simpa only [zeroQuestions, Fin.cases_succ] using hzero j.succ

/-- A fixed batch of scalar questions is a special case of an adaptive procedure. -/
def fixed : {q : ℕ} → (Fin q → E →L[ℝ] ℝ) → ((Fin q → ℝ) → F) → Procedure E F q
  | 0, _, decode => .done (decode Fin.elim0)
  | _ + 1, questions, decode => .ask (questions 0) (fun response ↦
      fixed (fun j ↦ questions j.succ) (fun responses ↦ decode (Fin.cases response responses)))

/-- The concrete fixed procedure returns its decoder applied to the measured coordinates. -/
theorem fixed_run {q : ℕ} (questions : Fin q → E →L[ℝ] ℝ)
    (decode : (Fin q → ℝ) → F) (v : E) :
    (fixed questions decode).run v = decode (fun j ↦ questions j v) := by
  induction q with
  | zero =>
    simp only [fixed, run]
    congr 1
    funext j
    exact Fin.elim0 j
  | succ q ih =>
    simp only [fixed, run, ih]
    congr 1
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl

end Procedure

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Uniform target loss of the complete adaptive procedure. -/
def UniformRisk {q : ℕ} (procedure : Procedure E F q) (L : E →L[ℝ] F)
    (radius risk : ℝ) : Prop :=
  ∀ v : E, ‖v‖ ≤ radius → ‖L v - procedure.run v‖ ^ 2 ≤ risk

/-- Dimension alone yields a unit vector annihilated by all scalar queries.
The existence of this direction is proved, not supplied as a query lower bound. -/
theorem common_kernel_unit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {q : ℕ} (questions : Fin q → V →L[ℝ] ℝ)
    (hdim : q < Module.finrank ℝ V) :
    ∃ v : V, ‖v‖ = 1 ∧ ∀ j, questions j v = 0 := by
  let queryMap : V →ₗ[ℝ] (Fin q → ℝ) := LinearMap.pi (fun j ↦ (questions j).toLinearMap)
  have hker : LinearMap.ker queryMap ≠ ⊥ := by
    intro hbot
    have hinjective := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinjective
    have hdim' : Module.finrank ℝ V ≤ q := by simpa using hle
    omega
  obtain ⟨v, hv, hvne⟩ := (LinearMap.ker queryMap).ne_bot_iff.mp hker
  have hquestions : ∀ j, questions j v = 0 := by
    have heq := LinearMap.mem_ker.mp hv
    intro j
    exact congrFun heq j
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]
  intro j
  simp only [map_smul, hquestions j, smul_zero]

/-- Any target-sensitive subspace of dimension greater than the query budget
forces the stated error against every deterministic adaptive procedure. -/
theorem adaptive_lower_of_subspace {q : ℕ} (procedure : Procedure E F q)
    (L : E →L[ℝ] F) (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (hdim : q < Module.finrank ℝ V) (s radius risk : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ radius)
    (hvisible : ∀ v : V, s * ‖v‖ ≤ ‖L v‖)
    (h : UniformRisk procedure L radius risk) : radius ^ 2 * s ^ 2 ≤ risk := by
  obtain ⟨v, hvnorm, hvzero⟩ := common_kernel_unit (V := V) (q := q)
    (fun j : Fin q ↦ (procedure.zeroQuestions j).comp (V.subtypeL : V →L[ℝ] E)) hdim
  have hzero : ∀ j, procedure.zeroQuestions j (radius • (v : E)) = 0 := by
    intro j
    have hz : procedure.zeroQuestions j (v : E) = 0 := hvzero j
    simp only [map_smul, hz, smul_zero]
  have hnegzero : ∀ j, procedure.zeroQuestions j (-(radius • (v : E))) = 0 := by
    intro j
    simp only [map_neg, hzero j, neg_zero]
  have hnorm : ‖radius • (v : E)‖ ≤ radius := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    change radius * ‖v‖ ≤ radius
    rw [hvnorm, mul_one]
  have hplus := h (radius • (v : E)) hnorm
  have hminus := h (-(radius • (v : E))) (by simpa only [norm_neg] using hnorm)
  rw [procedure.run_eq_zeroPrediction _ hzero] at hplus
  rw [procedure.run_eq_zeroPrediction _ hnegzero, map_neg] at hminus
  have hlower := two_point_lower (L (radius • (v : E))) procedure.zeroPrediction risk hplus hminus
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hlower
  have hvis : s ≤ ‖L (v : E)‖ := by simpa only [hvnorm, mul_one] using hvisible v
  have hsq := mul_self_le_mul_self hs hvis
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg radius)
  nlinarith

end Descent.Portability.AdaptiveLinearMeasurements
