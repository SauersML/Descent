/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PThresholdTrainingLaw
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

assert_below Descent.Decision Descent.Program

/-!
Real-arithmetic Firth iteration from PLINK2's 10 January 2026 source, commit
`a686ce404cbc7f273988752112022e3e1f4bd1ed`, `FirthRegressionD`.
Probabilities, information, leverage, adjusted scores and clipped updates are
constructed explicitly. The only supplied checks describe additional rejection
by the two matrix-inversion routines. Positive determinants are required before
using the real inverse and log determinant. Their floating-point implementation
and the binary build's equivalence to these real operations remain separate.

The iteration permits 26 updates, each clipped to coordinate magnitude 5.
The resulting coefficient bound is not a bound on a portability ratio.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FirthFiniteIterationLaw

variable {R J : Type*} [Fintype R] [Fintype J] [DecidableEq J] [Nonempty J]

/-- Maximum coordinate magnitude, including the intercept coordinate. -/
noncomputable def maxAbs (values : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j ↦ |values j|)

omit [DecidableEq J] in
theorem abs_le_maxAbs (values : J → ℝ) (j : J) : |values j| ≤ maxAbs values := by
  unfold maxAbs
  exact Finset.le_sup' (fun j ↦ |values j|) (Finset.mem_univ j)

omit [DecidableEq J] in
theorem maxAbs_nonneg (values : J → ℝ) : 0 ≤ maxAbs values :=
  (abs_nonneg (values (Classical.arbitrary J))).trans (abs_le_maxAbs values _)

/-- PLINK scales the entire step by 5/maxAbs when any coordinate exceeds 5. -/
noncomputable def clippedStep (delta : J → ℝ) : J → ℝ :=
  if 5 < maxAbs delta then fun j ↦ (5 / maxAbs delta) * delta j else delta

noncomputable def clippedMagnitude (delta : J → ℝ) : ℝ := min (maxAbs delta) 5

omit [DecidableEq J] in
theorem clippedStep_coordinate_bound (delta : J → ℝ) (j : J) :
    |clippedStep delta j| ≤ 5 := by
  unfold clippedStep
  split_ifs with h
  · have hm : 0 < maxAbs delta := lt_trans (by norm_num) h
    have hf : 0 ≤ 5 / maxAbs delta := by positivity
    rw [abs_mul, abs_of_nonneg hf]
    calc
      5 / maxAbs delta * |delta j| ≤ 5 / maxAbs delta * maxAbs delta :=
        mul_le_mul_of_nonneg_left (abs_le_maxAbs delta j) hf
      _ = 5 := div_mul_cancel₀ _ (ne_of_gt hm)
  · exact (abs_le_maxAbs delta j).trans (le_of_not_gt h)

omit [DecidableEq J] in
theorem clippedMagnitude_bounds (delta : J → ℝ) :
    0 ≤ clippedMagnitude delta ∧ clippedMagnitude delta ≤ 5 := by
  exact ⟨le_min (maxAbs_nonneg delta) (by norm_num), min_le_right _ _⟩

omit [DecidableEq J] in
theorem maxAbs_clippedStep (delta : J → ℝ) :
    maxAbs (clippedStep delta) = clippedMagnitude delta := by
  unfold clippedStep clippedMagnitude
  split_ifs with h
  · have hm : 0 < maxAbs delta := lt_trans (by norm_num) h
    have hf : 0 ≤ 5 / maxAbs delta := by positivity
    rw [min_eq_right h.le]
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      change |(5 / maxAbs delta) * delta j| ≤ 5
      rw [abs_mul, abs_of_nonneg hf]
      calc
        _ ≤ (5 / maxAbs delta) * maxAbs delta :=
          mul_le_mul_of_nonneg_left (abs_le_maxAbs delta j) hf
        _ = 5 := div_mul_cancel₀ _ (ne_of_gt hm)
    · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j ↦ |delta j|)
      change maxAbs delta = |delta j| at hj
      have hle := abs_le_maxAbs (fun j ↦ (5 / maxAbs delta) * delta j) j
      rw [abs_mul, abs_of_nonneg hf, ← hj, div_mul_cancel₀ _ (ne_of_gt hm)] at hle
      exact hle
  · exact (min_eq_left (le_of_not_gt h)).symm

noncomputable def probability (x : R → J → ℝ) (beta : J → ℝ) (row : R) : ℝ :=
  1 / (1 + Real.exp (-(∑ j, x row j * beta j)))

omit [Fintype R] [DecidableEq J] [Nonempty J] in
theorem probability_mem_openUnit (x : R → J → ℝ) (beta : J → ℝ) (row : R) :
    0 < probability x beta row ∧ probability x beta row < 1 := by
  have he := Real.exp_pos (-(∑ j, x row j * beta j))
  unfold probability
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 1 + Real.exp (-(∑ j, x row j * beta j)))).mpr
    linarith

noncomputable def varianceWeight (x : R → J → ℝ) (beta : J → ℝ) (row : R) : ℝ :=
  probability x beta row * (1 - probability x beta row)

omit [Fintype R] [DecidableEq J] [Nonempty J] in
theorem varianceWeight_pos (x : R → J → ℝ) (beta : J → ℝ) (row : R) :
    0 < varianceWeight x beta row :=
  mul_pos (probability_mem_openUnit x beta row).1
    (sub_pos.mpr (probability_mem_openUnit x beta row).2)

noncomputable def weightedInformation (x : R → J → ℝ) (weight : R → ℝ) : Matrix J J ℝ :=
  fun j k ↦ ∑ row, x row j * weight row * x row k

noncomputable def logLikelihood (x : R → J → ℝ) (labels : R → Bool) (beta : J → ℝ) : ℝ :=
  ∑ row, if labels row then Real.log (probability x beta row)
    else Real.log (1 - probability x beta row)

noncomputable def leverage (x : R → J → ℝ) (weight : R → ℝ) (inverse : Matrix J J ℝ)
    (row : R) : ℝ := weight row * ∑ j, ∑ k, x row j * inverse j k * x row k

noncomputable def adjustedScore (x : R → J → ℝ) (labels : R → Bool)
    (p h : R → ℝ) (j : J) : ℝ :=
  ∑ row, x row j * ((if labels row then 1 else 0) - p row + h row * (1 / 2 - p row))

/-- These are failure checks, not supplied optimizer iterates or bounded steps. -/
structure MatrixChecks (J : Type*) where
  informationAccepted : Matrix J J ℝ → Bool
  updateAccepted : Matrix J J ℝ → Bool

def exactMatrixChecks : MatrixChecks J := ⟨fun _ ↦ true, fun _ ↦ true⟩

inductive Failure where
  | boundaryProbability
  | informationInverse
  | updateInverse
  deriving DecidableEq

structure Snapshot (R J : Type*) where
  variance : R → ℝ
  leverage : R → ℝ
  score : J → ℝ
  penalizedLogLikelihood : ℝ

/-- A successful first inversion supplies the ordinary inverse information;
its determinant contributes the Jeffreys penalty to the objective. -/
noncomputable def snapshot (checks : MatrixChecks J) (x : R → J → ℝ)
    (labels : R → Bool) (beta : J → ℝ) : Except Failure (Snapshot R J) := by
  classical
  let p := probability x beta
  let v := varianceWeight x beta
  let information := weightedInformation x v
  exact if (∀ row, p row ≠ 0 ∧ p row ≠ 1) then
    if checks.informationAccepted information ∧ 0 < information.det then
      let h := leverage x v information⁻¹
      .ok ⟨v, h, adjustedScore x labels p h,
        logLikelihood x labels beta + (1 / 2) * Real.log information.det⟩
    else .error .informationInverse
  else .error .boundaryProbability

omit [Nonempty J] in
/-- Finite real predictors cannot hit an exact probability of zero or one.
Floating-point saturation remains an additional implementation phenomenon. -/
theorem snapshot_no_boundary_failure (checks : MatrixChecks J) (x : R → J → ℝ)
    (labels : R → Bool) (beta : J → ℝ) :
    snapshot checks x labels beta ≠ .error .boundaryProbability := by
  classical
  have hp : ∀ row, probability x beta row ≠ 0 ∧ probability x beta row ≠ 1 := by
    intro row
    exact ⟨ne_of_gt (probability_mem_openUnit x beta row).1,
      ne_of_lt (probability_mem_openUnit x beta row).2⟩
  unfold snapshot
  dsimp only
  rw [if_pos hp]
  split_ifs <;> simp

/-- The second matrix uses (1+h_i)*p_i*(1-p_i), as in FirthRegressionD. -/
noncomputable def updateInformation (x : R → J → ℝ) (current : Snapshot R J) : Matrix J J ℝ :=
  weightedInformation x (fun row ↦ (1 + current.leverage row) * current.variance row)

noncomputable def rawUpdate (x : R → J → ℝ) (current : Snapshot R J) : J → ℝ :=
  fun j ↦ ∑ k, (updateInformation x current)⁻¹ j k * current.score k

structure Iterate (J : Type*) where
  beta : J → ℝ
  previousMagnitude : ℝ
  previousLogLikelihood : ℝ
  previousInverse : Option (Matrix J J ℝ)

structure Returned (J : Type*) where
  beta : J → ℝ
  unfinished : Bool
  iteration : ℕ
  inverse : Option (Matrix J J ℝ)

/-- Source semantics: the objective-change check is one-sided, not absolute.
Convergence is never declared at iteration zero. -/
noncomputable def Converged (iteration : ℕ) (state : Iterate J) (current : Snapshot R J) : Prop :=
  iteration ≠ 0 ∧ state.previousMagnitude ≤ 1 / 100000 ∧
    maxAbs current.score < 1 / 100000 ∧
    current.penalizedLogLikelihood - state.previousLogLikelihood < 1 / 100000

noncomputable def updated (state : Iterate J) (x : R → J → ℝ)
    (current : Snapshot R J) : Iterate J :=
  let delta := rawUpdate x current
  ⟨fun j ↦ state.beta j + clippedStep delta j, clippedMagnitude delta,
    current.penalizedLogLikelihood, some (updateInformation x current)⁻¹⟩

/-- `remaining=26` starts at source iteration 0. At remaining=0, iteration26
still computes its snapshot and checks convergence before returning unfinished. -/
noncomputable def loop (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool) :
    ℕ → Iterate J → Except Failure (Returned J)
  | remaining, state => by
    classical
    exact match snapshot checks x labels state.beta with
    | .error failure => .error failure
    | .ok current =>
      if Converged (26 - remaining) state current then
        .ok ⟨state.beta, false, 26 - remaining, state.previousInverse⟩
      else match remaining with
      | 0 => .ok ⟨state.beta, true, 26, state.previousInverse⟩
      | remaining + 1 =>
        if checks.updateAccepted (updateInformation x current) ∧
            0 < (updateInformation x current).det then
          loop checks x labels remaining (updated state x current)
        else .error .updateInverse

noncomputable def run (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool) :
    Except Failure (Returned J) := loop checks x labels 26 ⟨fun _ ↦ 0, 0, 0, none⟩

/-- Complete real-matrix specialization, with no additional numerical
rejections beyond the explicit positive-determinant checks. -/
noncomputable def exactRun (x : R → J → ℝ) (labels : R → Bool) : Except Failure (Returned J) :=
  run exactMatrixChecks x labels

theorem iteration_limit_iff (remaining : ℕ) (h : remaining ≤ 26) :
    remaining = 0 ↔ 25 < 26 - remaining := by omega

theorem loop_coefficient_bound (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool)
    (remaining : ℕ) (state : Iterate J) (result : Returned J)
    (hr : loop checks x labels remaining state = .ok result) (j : J) :
    |result.beta j| ≤ |state.beta j| + 5 * remaining := by
  induction remaining generalizing state with
  | zero =>
    unfold loop at hr
    cases hs : snapshot checks x labels state.beta with
    | error failure => simp [hs] at hr
    | ok current =>
      simp only [hs] at hr
      split_ifs at hr <;> cases hr <;> simp
  | succ remaining ih =>
    unfold loop at hr
    cases hs : snapshot checks x labels state.beta with
    | error failure => simp [hs] at hr
    | ok current =>
      simp only [hs] at hr
      split_ifs at hr with hc hu
      · cases hr
        have hn : (0 : ℝ) ≤ 5 * (remaining + 1 : ℕ) := by positivity
        exact le_add_of_nonneg_right hn
      · have hbound := ih (updated state x current) hr
        have hstep := clippedStep_coordinate_bound (rawUpdate x current) j
        have habs := abs_add_le (state.beta j) (clippedStep (rawUpdate x current) j)
        change |result.beta j| ≤ |state.beta j + clippedStep (rawUpdate x current) j| +
          5 * remaining at hbound
        push_cast
        linarith

/-- Every coefficient returned from the zero-initialized real Firth path is
bounded by 130, including an UNFINISHED result at its iteration limit. -/
theorem run_coefficient_bound (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool)
    (result : Returned J) (hr : run checks x labels = .ok result) (j : J) :
    |result.beta j| ≤ 130 := by
  have h := loop_coefficient_bound checks x labels 26 ⟨fun _ ↦ 0, 0, 0, none⟩ result hr j
  norm_num at h
  exact h

theorem exactRun_coefficient_bound (x : R → J → ℝ) (labels : R → Bool)
    (result : Returned J) (hr : exactRun x labels = .ok result) (j : J) :
    |result.beta j| ≤ 130 := run_coefficient_bound exactMatrixChecks x labels result hr j

/-- At iteration26 the convergence check still takes priority over unfinished.
No new update matrix is computed on this return path. -/
theorem loop_zero_converged (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool)
    (state : Iterate J) (current : Snapshot R J)
    (hs : snapshot checks x labels state.beta = .ok current) (hc : Converged 26 state current) :
    loop checks x labels 0 state = .ok ⟨state.beta, false, 26, state.previousInverse⟩ := by
  classical
  rw [loop, hs]
  exact if_pos hc

theorem loop_zero_unfinished (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool)
    (state : Iterate J) (current : Snapshot R J)
    (hs : snapshot checks x labels state.beta = .ok current) (hc : ¬ Converged 26 state current) :
    loop checks x labels 0 state = .ok ⟨state.beta, true, 26, state.previousInverse⟩ := by
  classical
  rw [loop, hs]
  exact if_neg hc

theorem loop_preserves_inverse (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool)
    (remaining : ℕ) (state : Iterate J) (result : Returned J)
    (hi : state.previousInverse.isSome) (hr : loop checks x labels remaining state = .ok result) :
    result.inverse.isSome := by
  induction remaining generalizing state with
  | zero =>
    unfold loop at hr
    cases hs : snapshot checks x labels state.beta with
    | error failure => simp [hs] at hr
    | ok current =>
      simp only [hs] at hr
      split_ifs at hr <;> cases hr <;> exact hi
  | succ remaining ih =>
    unfold loop at hr
    cases hs : snapshot checks x labels state.beta with
    | error failure => simp [hs] at hr
    | ok current =>
      simp only [hs] at hr
      split_ifs at hr with hc hu
      · cases hr
        exact hi
      · exact ih (updated state x current) (by simp [updated]) hr

/-- The caller's zero initialization cannot return before computing an update,
so every successful output carries the actual preceding inverse matrix. -/
theorem run_inverse_defined (checks : MatrixChecks J) (x : R → J → ℝ) (labels : R → Bool)
    (result : Returned J) (hr : run checks x labels = .ok result) : result.inverse.isSome := by
  unfold run at hr
  rw [loop] at hr
  cases hs : snapshot checks x labels (fun _ ↦ 0) with
  | error failure => simp [hs] at hr
  | ok current =>
    simp only [hs, Nat.sub_self, Converged, ne_eq, not_true_eq_false, false_and, if_false] at hr
    split_ifs at hr with hu
    exact loop_preserves_inverse checks x labels 25
      (updated ⟨fun _ ↦ 0, 0, 0, none⟩ x current) result (by simp [updated]) hr

theorem loop_unfinished_iteration (checks : MatrixChecks J) (x : R → J → ℝ)
    (labels : R → Bool) (remaining : ℕ) (state : Iterate J) (result : Returned J)
    (hr : loop checks x labels remaining state = .ok result) (hu : result.unfinished = true) :
    result.iteration = 26 := by
  induction remaining generalizing state with
  | zero =>
    unfold loop at hr
    cases hs : snapshot checks x labels state.beta with
    | error failure => simp [hs] at hr
    | ok current =>
      simp only [hs] at hr
      split_ifs at hr <;> cases hr <;> rfl
  | succ remaining ih =>
    unfold loop at hr
    cases hs : snapshot checks x labels state.beta with
    | error failure => simp [hs] at hr
    | ok current =>
      simp only [hs] at hr
      split_ifs at hr with hc hupdate
      · cases hr
        cases hu
      · exact ih (updated state x current) hr

omit [Nonempty J] in
theorem rawUpdate_solves_information (x : R → J → ℝ) (current : Snapshot R J)
    (hd : 0 < (updateInformation x current).det) :
    (updateInformation x current).mulVec (rawUpdate x current) = current.score := by
  have hi : IsUnit (updateInformation x current).det := isUnit_iff_ne_zero.mpr (ne_of_gt hd)
  change (updateInformation x current).mulVec
    ((updateInformation x current)⁻¹.mulVec current.score) = current.score
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hi, Matrix.one_mulVec]

end Descent.Portability.FirthFiniteIterationLaw
