/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransportCoordinates

assert_below Descent.Decision Descent.Program

/-!
# Residual genetic repair: the exact value of the information a score discarded

A deployed predictor `f₀` reads a retained representation `Z` of the genome and
context -- a published polygenic score, ancestry coordinates, clinical baseline.
Richer genetic features `φ` may carry outcome information `Z` erased.  Centre them on
`Z`, `r = φ − E[φ ∣ Z]`; then `E[r_i f₀] = 0` for every coordinate, because `f₀` is a
function of `Z`.  That single orthogonality is the only hypothesis this module takes,
and it takes it on the expectation functional rather than deriving it from a
conditional expectation; `NestedInformationGain.residual_feature_orthogonal` is the
measure-theoretic statement that conditional centring delivers it.

Under that hypothesis the module proves, for the repaired predictor `f₀ + vᵀr`:

* `repair_expansion`: `E[(Y − f₀ − vᵀr)²] = E[(Y − f₀)²] − 2 vᵀc_r + vᵀ Σ_r v`,
  with `c_r = E[rY]` and `Σ_r = E[rrᵀ]`, for every coefficient `v`.
* `residual_repair_law`: for any normal-equation solution `Σ_r v* = c_r`, the repaired
  risk is `E[(Y − f₀)²] − c_rᵀ v*` and every other `v` pays exactly
  `(v − v*)ᵀ Σ_r (v − v*)` more.  No invertibility of `Σ_r` is assumed anywhere;
  `exists_repair_solution` supplies a solution whatever its rank, and
  `repair_value_unique` shows the value `c_rᵀ v*` does not depend on which solution is
  taken, which is what entitles the design to write it as `c_rᵀ Σ_r⁺ c_r`.
* `repair_value_eq_secondMoment` and `repair_value_nonneg`: the value removed is the
  second moment of the oracle correction, `c_rᵀ v* = E[(v*ᵀ r)²] ≥ 0`.

This is the population oracle: what a linear read of the residual features can remove
from squared risk when the moments are known.  It says nothing about a fitted
estimator, whose realised gain is this value less its own estimation error.

Builds on `TransportCoordinates.excess_risk_law`, `crossMoment_mem_range`,
`oracle_value_unique`, `expMse_expand`, `crossMoment_dot` and
`Foundations.secondMoment_quadratic_form`.

## Empirical status

None. The bodies here are algebra: a least-squares decomposition of a residual outcome
is an identity between moments, not a measurement of any.  What carries an empirical
status is a named quantity in a subsystem module asserting that this algebra computes
something measurable, and such names keep their own docstrings, regimes and ledger rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ResidualGeneticRepair

open Foundations TransportCoordinates

noncomputable section

variable {Ω : Type*}
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The residual outcome `Y − f₀`: what the base predictor leaves unexplained. -/
def residualOutcome (f₀ Y : Ω → ℝ) : Ω → ℝ := fun ω ↦ Y ω - f₀ ω

/-- The repaired predictor `f₀ + vᵀr`: the base predictor plus a linear read of the
residual features. -/
def repairedPredictor (f₀ : Ω → ℝ) (r : Ω → J → ℝ) (v : J → ℝ) : Ω → ℝ :=
  fun ω ↦ f₀ ω + dot v (r ω)

omit [DecidableEq J] in
/-- The risk of the repaired predictor against `Y` is the risk of the linear read
against the residual outcome. -/
theorem expMse_repaired (E : ExpFunctional Ω) (f₀ Y : Ω → ℝ) (r : Ω → J → ℝ)
    (v : J → ℝ) :
    expMse E Y (repairedPredictor f₀ r v)
      = expMse E (residualOutcome f₀ Y) (linScore v r) := by
  unfold expMse repairedPredictor residualOutcome linScore
  congr 1
  funext ω
  ring

omit [Fintype J] [DecidableEq J] in
/-- **Orthogonality moves the cross moment onto the outcome.**  When every residual
feature is orthogonal to the base predictor, `E[r(Y − f₀)] = E[rY]`. -/
theorem crossMoment_residualOutcome (E : ExpFunctional Ω) (f₀ Y : Ω → ℝ)
    (r : Ω → J → ℝ) (horth : ∀ i, E (fun ω ↦ r ω i * f₀ ω) = 0) :
    crossMomentVector E r (residualOutcome f₀ Y) = crossMomentVector E r Y := by
  funext i
  unfold crossMomentVector residualOutcome
  have hsplit : (fun ω ↦ r ω i * (Y ω - f₀ ω))
      = (fun ω ↦ r ω i * Y ω) - (fun ω ↦ r ω i * f₀ ω) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  rw [hsplit, E.eval_sub, horth i, sub_zero]

/-- **The exact repair expansion.**  For every coefficient `v`,
`E[(Y − f₀ − vᵀr)²] = E[(Y − f₀)²] − 2 vᵀc_r + vᵀ Σ_r v`. -/
theorem repair_expansion (E : ExpFunctional Ω) (f₀ Y : Ω → ℝ) (r : Ω → J → ℝ)
    (v : J → ℝ) (horth : ∀ i, E (fun ω ↦ r ω i * f₀ ω) = 0) :
    expMse E Y (repairedPredictor f₀ r v)
      = expMse E Y f₀ - 2 * dot v (crossMomentVector E r Y)
        + dot v ((secondMomentMatrix E r).mulVec v) := by
  rw [expMse_repaired, expMse_expand, crossMoment_dot,
    crossMoment_residualOutcome E f₀ Y r horth, secondMoment_quadratic_form]
  rfl

/-- A least-squares coefficient for the repair exists whatever the rank of `Σ_r`. -/
theorem exists_repair_solution (E : ExpFunctional Ω) (Y : Ω → ℝ) (r : Ω → J → ℝ) :
    ∃ vStar : J → ℝ, (secondMomentMatrix E r).mulVec vStar = crossMomentVector E r Y :=
  crossMoment_mem_range E r Y

/-- **The residual repair law.**  For any normal-equation solution `v*` and every `v`,
`E[(Y − f₀ − vᵀr)²] = E[(Y − f₀)²] − c_rᵀ v* + (v − v*)ᵀ Σ_r (v − v*)`. -/
theorem residual_repair_law (E : ExpFunctional Ω) (f₀ Y : Ω → ℝ) (r : Ω → J → ℝ)
    (vStar v : J → ℝ)
    (horth : ∀ i, E (fun ω ↦ r ω i * f₀ ω) = 0)
    (hstar : (secondMomentMatrix E r).mulVec vStar = crossMomentVector E r Y) :
    expMse E Y (repairedPredictor f₀ r v)
      = expMse E Y f₀ - dot vStar (crossMomentVector E r Y)
        + dot (fun i ↦ v i - vStar i)
            ((secondMomentMatrix E r).mulVec (fun i ↦ v i - vStar i)) := by
  have hstar' : (secondMomentMatrix E r).mulVec vStar
      = crossMomentVector E r (residualOutcome f₀ Y) := by
    rw [crossMoment_residualOutcome E f₀ Y r horth]
    exact hstar
  rw [expMse_repaired, excess_risk_law E r (residualOutcome f₀ Y) vStar v hstar',
    crossMoment_residualOutcome E f₀ Y r horth]
  rfl

/-- The repair value `c_rᵀ v*` is exactly the risk the oracle correction removes. -/
theorem repair_value_eq (E : ExpFunctional Ω) (f₀ Y : Ω → ℝ) (r : Ω → J → ℝ)
    (vStar : J → ℝ) (horth : ∀ i, E (fun ω ↦ r ω i * f₀ ω) = 0)
    (hstar : (secondMomentMatrix E r).mulVec vStar = crossMomentVector E r Y) :
    expMse E Y f₀ - expMse E Y (repairedPredictor f₀ r vStar)
      = dot vStar (crossMomentVector E r Y) := by
  rw [residual_repair_law E f₀ Y r vStar vStar horth hstar]
  have hzero : (fun i ↦ vStar i - vStar i) = (0 : J → ℝ) := by
    funext i
    simp
  rw [hzero, Matrix.mulVec_zero, dot_zero_right]
  ring

/-- The repair value does not depend on which least-squares solution is taken. -/
theorem repair_value_unique (E : ExpFunctional Ω) (Y : Ω → ℝ) (r : Ω → J → ℝ)
    (v₁ v₂ : J → ℝ)
    (h₁ : (secondMomentMatrix E r).mulVec v₁ = crossMomentVector E r Y)
    (h₂ : (secondMomentMatrix E r).mulVec v₂ = crossMomentVector E r Y) :
    dot v₁ (crossMomentVector E r Y) = dot v₂ (crossMomentVector E r Y) :=
  oracle_value_unique E r Y v₁ v₂ h₁ h₂

/-- The repair value is the second moment of the oracle correction. -/
theorem repair_value_eq_secondMoment (E : ExpFunctional Ω) (Y : Ω → ℝ) (r : Ω → J → ℝ)
    (vStar : J → ℝ)
    (hstar : (secondMomentMatrix E r).mulVec vStar = crossMomentVector E r Y) :
    dot vStar (crossMomentVector E r Y) = E (fun ω ↦ dot vStar (r ω) ^ 2) := by
  rw [secondMoment_quadratic_form, hstar]

/-- The repair value is nonnegative: a linear read of the residual features never
raises the oracle squared risk. -/
theorem repair_value_nonneg (E : ExpFunctional Ω) (Y : Ω → ℝ) (r : Ω → J → ℝ)
    (vStar : J → ℝ)
    (hstar : (secondMomentMatrix E r).mulVec vStar = crossMomentVector E r Y) :
    0 ≤ dot vStar (crossMomentVector E r Y) := by
  rw [repair_value_eq_secondMoment E Y r vStar hstar]
  exact E.nonneg_eval _ fun ω ↦ sq_nonneg _

/-- No coefficient beats a normal-equation solution: the excess is a nonnegative
quadratic form in `v − v*`. -/
theorem repaired_risk_ge_oracle (E : ExpFunctional Ω) (f₀ Y : Ω → ℝ) (r : Ω → J → ℝ)
    (vStar v : J → ℝ)
    (horth : ∀ i, E (fun ω ↦ r ω i * f₀ ω) = 0)
    (hstar : (secondMomentMatrix E r).mulVec vStar = crossMomentVector E r Y) :
    expMse E Y (repairedPredictor f₀ r vStar) ≤ expMse E Y (repairedPredictor f₀ r v) := by
  rw [residual_repair_law E f₀ Y r vStar v horth hstar,
    residual_repair_law E f₀ Y r vStar vStar horth hstar]
  have hzero : (fun i ↦ vStar i - vStar i) = (0 : J → ℝ) := by
    funext i
    simp
  rw [hzero, Matrix.mulVec_zero, dot_zero_right, ← secondMoment_quadratic_form]
  have hnn : 0 ≤ E (fun ω ↦ dot (fun i ↦ v i - vStar i) (r ω) ^ 2) :=
    E.nonneg_eval _ fun ω ↦ sq_nonneg _
  linarith

end

end Descent.Portability.ResidualGeneticRepair
