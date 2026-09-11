/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem
import Descent.Portability.TraitPortabilityRange

assert_below Descent.Decision Descent.Program

/-!
# The sharp unrestricted counterfactual region and reports versus causes

A completely specified observational law for a finite-valued exposure and a bounded outcome
leaves the mean of an intervened outcome free in an explicit interval, and every point of
that interval is attained by an acyclic structural model with exactly the same observational
law. The filling constant is a function of the exposure value, so every exposure value is
completed simultaneously by one model. Separately, two structural models can agree on the
entire observational law, hence on every observational report, and still disagree about an
intervention.

This is UPT Theorem 10.1 (10.1)-(10.2) and PL Theorem 11.1. The observational law enters
through `Foundations.ExpFunctional`, so the outcome is an arbitrary integrable bounded
variable rather than a finitely supported one; the counterfactual outcome is an explicit
`def` and its expectation is computed exactly. The lower endpoint is the restricted
expectation on the event that the exposure already takes the intervened value, and the width
is exactly the probability that it does not.

The hypotheses are the manuscript's domain conditions: the outcome lies in the unit
interval, the filling constants lie in the unit interval, and the observational law is
given. Nothing here assumes latent confounding is absent; the construction allows it.

## Empirical status

None. The bodies here are algebra: a structural equation and an expectation functional are
claims about a model class, and what carries an empirical status is a named quantity in a
subsystem module asserting that this algebra computes something measurable. Those names keep
their own docstrings, their own regimes, and their own ledger rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CounterfactualRegion

open Foundations

noncomputable section

variable {Ω X : Type*} [DecidableEq X]

/-- The observed outcome restricted to the event that the exposure already equals `x`. -/
def restrictedOutcome (xval : Ω → X) (yval : Ω → ℝ) (x : X) : Ω → ℝ :=
  fun ω ↦ if xval ω = x then yval ω else 0

/-- The indicator of the event that the exposure does not equal `x`. -/
def offIndicator (xval : Ω → X) (x : X) : Ω → ℝ :=
  fun ω ↦ if xval ω = x then 0 else 1

/-- The structural outcome of UPT (10.2) under the intervention setting the exposure to `x`:
consistency on the event the exposure already equals `x`, an arbitrary admissible constant
off that event. One `fill` completes every exposure value at once. -/
def counterfactualOutcome (xval : Ω → X) (yval : Ω → ℝ) (fill : X → ℝ) (x : X) : Ω → ℝ :=
  fun ω ↦ if xval ω = x then yval ω else fill x

/-- Consistency: the intervened outcome at the exposure's own value is the observed
outcome, so the structural model reproduces the observational law exactly. -/
theorem counterfactualOutcome_consistent (xval : Ω → X) (yval : Ω → ℝ) (fill : X → ℝ)
    (ω : Ω) : counterfactualOutcome xval yval fill (xval ω) ω = yval ω := by
  simp [counterfactualOutcome]

/-- The intervened outcome splits into its consistent part and the filled part. -/
theorem counterfactualOutcome_split (xval : Ω → X) (yval : Ω → ℝ) (fill : X → ℝ) (x : X) :
    counterfactualOutcome xval yval fill x =
      restrictedOutcome xval yval x + fill x • offIndicator xval x := by
  funext ω
  by_cases hx : xval ω = x
  · simp [counterfactualOutcome, restrictedOutcome, offIndicator, hx]
  · simp [counterfactualOutcome, restrictedOutcome, offIndicator, hx]

/-- UPT (10.1) computed exactly: the intervened mean is the restricted expectation plus the
filling constant times the probability that the exposure is not already `x`. -/
theorem expectation_counterfactualOutcome (E : ExpFunctional Ω) (xval : Ω → X)
    (yval : Ω → ℝ) (fill : X → ℝ) (x : X) :
    E (counterfactualOutcome xval yval fill x) =
      E (restrictedOutcome xval yval x) + fill x * E (offIndicator xval x) := by
  rw [counterfactualOutcome_split, E.add_eval, E.smul_eval]

/-- The probability of the complementary event is nonnegative. -/
theorem expectation_offIndicator_nonneg (E : ExpFunctional Ω) (xval : Ω → X) (x : X) :
    0 ≤ E (offIndicator xval x) := by
  refine E.nonneg_eval _ fun ω ↦ ?_
  by_cases hx : xval ω = x <;> simp [offIndicator, hx]

/-- UPT Theorem 10.1: with admissible filling constants the intervened mean lies in the
stated interval, whose lower endpoint is the restricted expectation and whose width is the
probability that the exposure is not already `x`. -/
theorem counterfactual_mean_mem_interval (E : ExpFunctional Ω) (xval : Ω → X)
    (yval : Ω → ℝ) (fill : X → ℝ) (x : X) (hlow : 0 ≤ fill x) (hhigh : fill x ≤ 1) :
    E (restrictedOutcome xval yval x) ≤ E (counterfactualOutcome xval yval fill x) ∧
      E (counterfactualOutcome xval yval fill x) ≤
        E (restrictedOutcome xval yval x) + E (offIndicator xval x) := by
  have hoff := expectation_offIndicator_nonneg E xval x
  rw [expectation_counterfactualOutcome]
  constructor
  · nlinarith
  · nlinarith

/-- UPT Theorem 10.1, attainment: every point of the interval is realised by an acyclic
structural model whose observational law is unchanged. The witness is an explicit filling
constant, and the same `fill` completes every other exposure value simultaneously. -/
theorem counterfactual_mean_attains (E : ExpFunctional Ω) (xval : Ω → X) (yval : Ω → ℝ)
    (x : X) (target : ℝ)
    (hlow : E (restrictedOutcome xval yval x) ≤ target)
    (hhigh : target ≤ E (restrictedOutcome xval yval x) + E (offIndicator xval x)) :
    ∃ fill : X → ℝ, 0 ≤ fill x ∧ fill x ≤ 1 ∧
      E (counterfactualOutcome xval yval fill x) = target := by
  have hoff := expectation_offIndicator_nonneg E xval x
  rcases eq_or_lt_of_le hoff with hzero | hpos
  · refine ⟨fun _ ↦ 0, le_refl 0, zero_le_one, ?_⟩
    rw [expectation_counterfactualOutcome, ← hzero]
    simp only [zero_mul, add_zero]
    linarith
  · refine ⟨fun _ ↦ (target - E (restrictedOutcome xval yval x)) / E (offIndicator xval x),
      div_nonneg (by linarith) hoff, ?_, ?_⟩
    · rw [div_le_one hpos]
      linarith
    · rw [expectation_counterfactualOutcome, div_mul_cancel₀ _ (ne_of_gt hpos)]
      ring

/-- The sign attached to a fair exogenous draw in the two-model construction. -/
def signOf (draw : Bool) : ℝ := if draw then 1 else -1

/-- The sign map here is the corpus sign map, not a second convention. -/
theorem signOf_eq_sign : signOf = TraitPortabilityRange.sign := rfl

/-- The first structural model's outcome equation, read on the pair of exposure and exogenous
draw: the outcome copies the exposure. -/
def outcomeFromExposure (input : ℝ × ℝ) : ℝ := input.1

/-- The second structural model's outcome equation on the same pair: the outcome copies the
exogenous variable directly, bypassing the exposure. -/
def outcomeFromExogenous (input : ℝ × ℝ) : ℝ := input.2

/-- PL Theorem 11.1: the two models agree pointwise on the observed exposure-outcome pair,
so every observational report of either model, deterministic or randomised, has the same
law. Nothing is left to a distributional argument here: the observed pairs are equal. -/
theorem observational_laws_agree (exogenous : ℝ) :
    (exogenous, outcomeFromExposure (exogenous, exogenous)) =
      (exogenous, outcomeFromExogenous (exogenous, exogenous)) := by
  simp [outcomeFromExposure, outcomeFromExogenous]

/-- PL Theorem 11.1: under the intervention setting the exposure to one, the first model's
mean outcome is one. -/
theorem intervened_mean_first_model :
    uniformExp Bool (fun draw ↦ outcomeFromExposure (1, signOf draw)) = 1 := by
  simp [uniformExp_apply, outcomeFromExposure, Fintype.card_bool]

/-- PL Theorem 11.1: under the same intervention the second model's mean outcome is zero,
so complete agreement of every observational report does not imply agreement of causes. -/
theorem intervened_mean_second_model :
    uniformExp Bool (fun draw ↦ outcomeFromExogenous (1, signOf draw)) = 0 := by
  simp [uniformExp_apply, outcomeFromExogenous, signOf, Fintype.card_bool]

end

end Descent.Portability.CounterfactualRegion
