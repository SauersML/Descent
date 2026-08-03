import Calibrator.CertificateGrading

/-!
# Finite minimax duality: the ungraded certificate calculus

This file states the genuine finite decision problem behind the slogan
"ungraded mixture certificates are complete by minimax duality".  The problem
contains only an observation kernel and a numerical loss.  In particular, it
does not accept duality, compactness, convexity, or a lower bound as a field.

The minimax theorem is currently an explicit `sorry`.  That visible obligation
is intentional: importing a literature theorem, assuming a duality proposition,
or defining the dual value to equal the primal value would all make the file
green while deleting its mathematical content.
-/

namespace Calibrator.FiniteMinimax

open scoped BigOperators
open Calibrator.CertificateGrading

/-- A finite statistical decision problem.  All three index types are
nonempty (`Fin (n + 1)`), and every observation law is Mathlib's `PMF`. -/
structure Problem (parameterCount actionCount observationCount : ℕ) where
  observation : Fin (parameterCount + 1) → FinitePrior observationCount
  loss : Fin (parameterCount + 1) → Fin (actionCount + 1) → ℝ

/-- Randomized decision rules, represented without side-condition fields. -/
abbrev Rule (actionCount observationCount : ℕ) :=
  Fin (observationCount + 1) → FinitePrior actionCount

namespace Problem

variable {parameterCount actionCount observationCount : ℕ}
    (E : Problem parameterCount actionCount observationCount)

/-- Frequentist risk at one parameter value. -/
noncomputable def risk
    (δ : Rule actionCount observationCount)
    (θ : Fin (parameterCount + 1)) : ℝ :=
  ∑ x, (E.observation θ).probability x *
    ∑ a, (δ x).probability a * E.loss θ a

/-- Worst-case risk of a randomized rule. -/
noncomputable def worstRisk (δ : Rule actionCount observationCount) : ℝ :=
  sSup (Set.range (E.risk δ))

/-- Primal minimax value. -/
noncomputable def minimaxRisk : ℝ :=
  sInf (Set.range E.worstRisk)

/-- Bayes risk of a rule under a finite prior. -/
noncomputable def bayesRisk
    (π : FinitePrior parameterCount)
    (δ : Rule actionCount observationCount) : ℝ :=
  ∑ θ, π.probability θ * E.risk δ θ

/-- Optimal Bayes value at a fixed prior. -/
noncomputable def optimalBayesRisk (π : FinitePrior parameterCount) : ℝ :=
  sInf (Set.range (E.bayesRisk π))

/-- Ungraded mixture-certificate value: optimize over every prior. -/
noncomputable def mixtureDualRisk : ℝ :=
  sSup (Set.range E.optimalBayesRisk)

/-- **Finite minimax duality.**  Ungraded mixture-versus-mixture reasoning is
complete because the primal minimax value equals the optimization over all
Bayes priors.  This is the real theorem, not a definitional equality and not a
caller-supplied proposition. -/
theorem finite_minimax_duality : E.minimaxRisk = E.mixtureDualRisk := by
  sorry

/-- The program's "vacuous ungraded completeness" statement, now tied to an
actual decision problem rather than to a value defined to equal itself. -/
theorem ungraded_certificate_calculus_complete :
    E.minimaxRisk = E.mixtureDualRisk :=
  E.finite_minimax_duality

end Problem

end Calibrator.FiniteMinimax
