/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.ToLin

assert_below Descent.Decision Descent.Program

/-!
# The exact response of a finite report to a specified mechanism

Hold the initial law and the reporting kernel fixed and let each transition depend on a
parameter. Differentiating the finite matrix product that produces the report expectation
places the derivative in each transition position in turn, and the result is the exact sum
over stages of the forward law at that stage, the transition derivative there, and the
backward value afterwards. When a transition row is a support-preserving exponential tilt,
its derivative is the tilt weight centred at its own row mean, and the stagewise term becomes
the row covariance between the tilt weight and the downstream report value.

This is TQ Theorem 6.3 (6.4)-(6.5). The derivative is obtained from a hypothesis that says
only what the manuscript says, that each transition entry is differentiable at the base
parameter with the stated derivative matrix; nothing about the report, the initial law or the
reporting kernel is assumed to move. The covariance form is proved against
`Foundations.covariance` evaluated at the row law built by
`PortabilityMasterTheorem.weightedExp`, so the covariance is the one this corpus already
uses, not a private redefinition.

The manuscript's remark that a parameter-dependent initial law, report kernel or phenotype
rule contributes further product-rule terms is respected here by holding exactly those
fixed: they are not silently differentiated away.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MechanismReportDerivative

open scoped Matrix

noncomputable section

variable {S : Type*} [Fintype S]

/-- The backward value after `remaining` further transitions starting at stage `stage`. -/
def backValue (kernel : ℕ → ℝ → Matrix S S ℝ) (terminal : S → ℝ) :
    ℕ → ℕ → ℝ → (S → ℝ)
  | _, 0, _ => terminal
  | stage, remaining + 1, θ =>
      kernel stage θ *ᵥ backValue kernel terminal (stage + 1) remaining θ

/-- The derivative of the backward value at the base parameter, obtained by placing the
transition derivative in each position in turn. -/
def backDeriv (kernel : ℕ → ℝ → Matrix S S ℝ) (rate : ℕ → Matrix S S ℝ)
    (terminal : S → ℝ) : ℕ → ℕ → (S → ℝ)
  | _, 0 => 0
  | stage, remaining + 1 =>
      rate stage *ᵥ backValue kernel terminal (stage + 1) remaining 0 +
        kernel stage 0 *ᵥ backDeriv kernel rate terminal (stage + 1) remaining

/-- The forward law after `steps` transitions from `stage` at the base parameter. -/
def forwardLaw (kernel : ℕ → ℝ → Matrix S S ℝ) (initial : S → ℝ) (stage : ℕ) :
    ℕ → (S → ℝ)
  | 0 => initial
  | steps + 1 => forwardLaw kernel initial stage steps ᵥ* kernel (stage + steps) 0

/-- Advancing the initial law by one transition shifts the forward chain by one stage. -/
theorem forwardLaw_shift (kernel : ℕ → ℝ → Matrix S S ℝ) (initial : S → ℝ) (stage : ℕ) :
    ∀ steps : ℕ,
      forwardLaw kernel (initial ᵥ* kernel stage 0) (stage + 1) steps =
        forwardLaw kernel initial stage (steps + 1) := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
    show forwardLaw kernel (initial ᵥ* kernel stage 0) (stage + 1) steps ᵥ*
        kernel (stage + 1 + steps) 0 = _
    rw [ih]
    show _ = forwardLaw kernel initial stage (steps + 1) ᵥ* kernel (stage + (steps + 1)) 0
    rw [show stage + 1 + steps = stage + (steps + 1) by omega]

/-- Each entry of the backward value is differentiable at the base parameter, with the
derivative computed by the product rule stage by stage. -/
theorem hasDerivAt_backValue (kernel : ℕ → ℝ → Matrix S S ℝ) (rate : ℕ → Matrix S S ℝ)
    (terminal : S → ℝ)
    (hkernel : ∀ stage i j, HasDerivAt (fun θ ↦ kernel stage θ i j) (rate stage i j) 0) :
    ∀ (remaining stage : ℕ) (s : S),
      HasDerivAt (fun θ ↦ backValue kernel terminal stage remaining θ s)
        (backDeriv kernel rate terminal stage remaining s) 0 := by
  intro remaining
  induction remaining with
  | zero =>
    intro stage s
    simpa [backValue, backDeriv] using hasDerivAt_const (0 : ℝ) (terminal s)
  | succ remaining ih =>
    intro stage s
    have hterm : ∀ t : S,
        HasDerivAt (fun θ ↦ kernel stage θ s t *
            backValue kernel terminal (stage + 1) remaining θ t)
          (rate stage s t * backValue kernel terminal (stage + 1) remaining 0 t +
            kernel stage 0 s t * backDeriv kernel rate terminal (stage + 1) remaining t) 0 :=
      fun t ↦ (hkernel stage s t).mul (ih (stage + 1) t)
    have hfun : (fun θ ↦ backValue kernel terminal stage (remaining + 1) θ s) =
        ∑ t : S, fun θ ↦ kernel stage θ s t *
          backValue kernel terminal (stage + 1) remaining θ t := by
      funext θ
      simp [backValue, Matrix.mulVec, dotProduct, Finset.sum_apply]
    have hval : backDeriv kernel rate terminal stage (remaining + 1) s =
        ∑ t, (rate stage s t * backValue kernel terminal (stage + 1) remaining 0 t +
          kernel stage 0 s t * backDeriv kernel rate terminal (stage + 1) remaining t) := by
      simp [backDeriv, Matrix.mulVec, dotProduct, Finset.sum_add_distrib]
    rw [hfun, hval]
    exact HasDerivAt.sum fun t _ ↦ hterm t

/-- The report expectation is differentiable at the base parameter, with derivative the
pairing of the initial law with the backward derivative. -/
theorem hasDerivAt_report (kernel : ℕ → ℝ → Matrix S S ℝ) (rate : ℕ → Matrix S S ℝ)
    (terminal initial : S → ℝ)
    (hkernel : ∀ stage i j, HasDerivAt (fun θ ↦ kernel stage θ i j) (rate stage i j) 0)
    (horizon : ℕ) :
    HasDerivAt (fun θ ↦ initial ⬝ᵥ backValue kernel terminal 0 horizon θ)
      (initial ⬝ᵥ backDeriv kernel rate terminal 0 horizon) 0 := by
  have hterm : ∀ s : S,
      HasDerivAt (fun θ ↦ initial s * backValue kernel terminal 0 horizon θ s)
        (initial s * backDeriv kernel rate terminal 0 horizon s) 0 := fun s ↦
    (hasDerivAt_backValue kernel rate terminal hkernel horizon 0 s).const_mul (initial s)
  have hfun : (fun θ ↦ initial ⬝ᵥ backValue kernel terminal 0 horizon θ) =
      ∑ s : S, fun θ ↦ initial s * backValue kernel terminal 0 horizon θ s := by
    funext θ
    simp [dotProduct, Finset.sum_apply]
  have hval : initial ⬝ᵥ backDeriv kernel rate terminal 0 horizon =
      ∑ s : S, initial s * backDeriv kernel rate terminal 0 horizon s := rfl
  rw [hfun, hval]
  exact HasDerivAt.sum fun s _ ↦ hterm s

/-- TQ (6.4): the derivative of the report expectation is the exact sum over stages of the
forward law there, the transition derivative there, and the backward value afterwards. -/
theorem dotProduct_backDeriv_eq_sum (kernel : ℕ → ℝ → Matrix S S ℝ)
    (rate : ℕ → Matrix S S ℝ) (terminal : S → ℝ) :
    ∀ (remaining stage : ℕ) (initial : S → ℝ),
      initial ⬝ᵥ backDeriv kernel rate terminal stage remaining =
        ∑ step ∈ Finset.range remaining,
          (forwardLaw kernel initial stage step ᵥ* rate (stage + step)) ⬝ᵥ
            backValue kernel terminal (stage + step + 1) (remaining - (step + 1)) 0 := by
  intro remaining
  induction remaining with
  | zero =>
    intro stage initial
    simp [backDeriv, dotProduct]
  | succ remaining ih =>
    intro stage initial
    have hsplit : initial ⬝ᵥ backDeriv kernel rate terminal stage (remaining + 1) =
        (initial ᵥ* rate stage) ⬝ᵥ backValue kernel terminal (stage + 1) remaining 0 +
          (initial ᵥ* kernel stage 0) ⬝ᵥ
            backDeriv kernel rate terminal (stage + 1) remaining := by
      simp only [backDeriv, dotProduct_add, Matrix.dotProduct_mulVec]
    rw [hsplit, ih (stage + 1) (initial ᵥ* kernel stage 0), Finset.sum_range_succ']
    have hhead : (forwardLaw kernel initial stage 0 ᵥ* rate (stage + 0)) ⬝ᵥ
        backValue kernel terminal (stage + 0 + 1) (remaining + 1 - (0 + 1)) 0 =
          (initial ᵥ* rate stage) ⬝ᵥ backValue kernel terminal (stage + 1) remaining 0 := by
      simp [forwardLaw]
    rw [hhead, add_comm]
    refine congrArg (fun x ↦ x + _) (Finset.sum_congr rfl fun step _ ↦ ?_)
    rw [forwardLaw_shift kernel initial stage step,
      show stage + 1 + step = stage + (step + 1) by omega,
      show remaining + 1 - (step + 1 + 1) = remaining - (step + 1) by omega]

/-- TQ Theorem 6.3 (6.4): the exact mechanism-to-report derivative at the base parameter. -/
theorem mechanism_to_report_derivative (kernel : ℕ → ℝ → Matrix S S ℝ)
    (rate : ℕ → Matrix S S ℝ) (terminal initial : S → ℝ)
    (hkernel : ∀ stage i j, HasDerivAt (fun θ ↦ kernel stage θ i j) (rate stage i j) 0)
    (horizon : ℕ) :
    HasDerivAt (fun θ ↦ initial ⬝ᵥ backValue kernel terminal 0 horizon θ)
      (∑ step ∈ Finset.range horizon,
        (forwardLaw kernel initial 0 step ᵥ* rate (0 + step)) ⬝ᵥ
          backValue kernel terminal (0 + step + 1) (horizon - (step + 1)) 0) 0 := by
  rw [← dotProduct_backDeriv_eq_sum kernel rate terminal horizon 0 initial]
  exact hasDerivAt_report kernel rate terminal initial hkernel horizon

/-- A support-preserving exponential tilt of a probability row has derivative the row mass
times the tilt weight centred at its own row mean. -/
theorem hasDerivAt_tiltedRow (row weight : S → ℝ) (hrow : ∑ l, row l = 1) (j : S) :
    HasDerivAt (fun θ ↦ row j * Real.exp (θ * weight j) /
        ∑ l, row l * Real.exp (θ * weight l))
      (row j * (weight j - ∑ l, row l * weight l)) 0 := by
  have hexp : ∀ t : S, HasDerivAt (fun θ : ℝ ↦ Real.exp (θ * weight t)) (weight t) 0 := by
    intro t
    have hlin : HasDerivAt (fun θ : ℝ ↦ θ * weight t) (weight t) 0 := by
      simpa using (hasDerivAt_id' (x := (0 : ℝ))).mul_const (weight t)
    simpa using hlin.exp
  have hnum : HasDerivAt (fun θ : ℝ ↦ row j * Real.exp (θ * weight j))
      (row j * weight j) 0 := (hexp j).const_mul (row j)
  have hden : HasDerivAt (fun θ : ℝ ↦ ∑ l, row l * Real.exp (θ * weight l))
      (∑ l, row l * weight l) 0 := by
    have hfun : (fun θ : ℝ ↦ ∑ l, row l * Real.exp (θ * weight l)) =
        ∑ l : S, fun θ : ℝ ↦ row l * Real.exp (θ * weight l) := by
      funext θ
      simp [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum fun l _ ↦ (hexp l).const_mul (row l)
  have hdenval : (∑ l, row l * Real.exp ((0 : ℝ) * weight l)) = 1 := by
    simpa using hrow
  have hne : (∑ l, row l * Real.exp ((0 : ℝ) * weight l)) ≠ 0 := by
    rw [hdenval]
    exact one_ne_zero
  have hquot := hnum.div hden hne
  have hsimp : (row j * weight j * (∑ l, row l * Real.exp ((0 : ℝ) * weight l)) -
      row j * Real.exp ((0 : ℝ) * weight j) * (∑ l, row l * weight l)) /
      (∑ l, row l * Real.exp ((0 : ℝ) * weight l)) ^ 2 =
      row j * (weight j - ∑ l, row l * weight l) := by
    rw [hdenval]
    simp only [zero_mul, Real.exp_zero, mul_one, one_pow, div_one]
    ring
  rw [← hsimp]
  exact hquot

/-- Expanding a row-weighted pairing of a transition derivative with a report value. -/
theorem vecMul_dotProduct_expand (transition : Matrix S S ℝ) (law value : S → ℝ) :
    (law ᵥ* transition) ⬝ᵥ value = ∑ i, law i * ∑ j, transition i j * value j := by
  simp only [dotProduct, Matrix.vecMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The centred tilt term at one row, written as a difference of row expectations. -/
theorem centred_tilt_row (transition : Matrix S S ℝ) (weight value : S → ℝ) (i : S) :
    ∑ j, transition i j * (weight j - ∑ l, transition i l * weight l) * value j =
      (∑ j, transition i j * (weight j * value j)) -
        (∑ l, transition i l * weight l) * ∑ j, transition i j * value j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- TQ (6.5): for an exponential tilt the stagewise term is the row covariance between the
tilt weight and the downstream report value, taken against the row law itself. -/
theorem tilt_term_eq_row_covariance (transition : Matrix S S ℝ) (weight : S → S → ℝ)
    (hnonneg : ∀ i j, 0 ≤ transition i j) (hrow : ∀ i, ∑ j, transition i j = 1)
    (law value : S → ℝ) :
    ∑ i, law i * ∑ j, transition i j * (weight i j - ∑ l, transition i l * weight i l) *
        value j =
      ∑ i, law i * Foundations.covariance
        (weightedExp (transition i) (hnonneg i) (hrow i)) (weight i) value := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine congrArg (fun x ↦ law i * x) ?_
  rw [centred_tilt_row transition (weight i) value i,
    Foundations.covariance_eq_expect_mul_sub_means]
  simp only [weightedExp_apply]

end

end Descent.Portability.MechanismReportDerivative
