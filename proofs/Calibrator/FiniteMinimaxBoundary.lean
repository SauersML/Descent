/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.FiniteMinimax

/-!
# Boundary cases of finite minimax duality

This module proves the one-parameter case directly. It does not invoke the admitted general
finite minimax theorem.

## Main results

- `finite_minimax_duality_parameterZero`: minimax duality when `parameterCount = 0`.
-/

namespace Calibrator.FiniteMinimax

open Calibrator.CertificateGrading

namespace Problem

variable {actionCount observationCount : ℕ}

/-- A prior on the one-point parameter space assigns its unique point mass one. -/
theorem probability_zero_eq_one (π : FinitePrior 0) : π.probability 0 = 1 := by
  have hmass := (finitePrior_probability_mem π).2
  simpa using hmass

/-- On a one-point parameter space, Bayes risk is pointwise risk. -/
theorem bayesRisk_parameterZero
    (E : Problem 0 actionCount observationCount) (π : FinitePrior 0)
    (δ : Rule actionCount observationCount) :
    E.bayesRisk π δ = E.risk δ 0 := by
  simp [bayesRisk, probability_zero_eq_one]

/-- On a one-point parameter space, worst-case risk is pointwise risk. -/
theorem worstRisk_parameterZero
    (E : Problem 0 actionCount observationCount)
    (δ : Rule actionCount observationCount) :
    E.worstRisk δ = E.risk δ 0 := by
  unfold worstRisk
  have hrange : Set.range (E.risk δ) = {E.risk δ 0} := by
    ext value
    constructor
    · rintro ⟨θ, rfl⟩
      simp only [Set.mem_singleton_iff]
      have hθ : θ = 0 := by
        apply Fin.ext
        omega
      exact congrArg (E.risk δ) hθ
    · intro hvalue
      rw [Set.mem_singleton_iff] at hvalue
      exact ⟨0, hvalue.symm⟩
  rw [hrange, csSup_singleton]

/-- Every prior has the same optimal Bayes value on a one-point parameter space. -/
theorem optimalBayesRisk_parameterZero
    (E : Problem 0 actionCount observationCount) (π : FinitePrior 0) :
    E.optimalBayesRisk π = sInf (Set.range fun δ ↦ E.risk δ 0) := by
  unfold optimalBayesRisk
  congr 1
  ext value
  constructor
  · rintro ⟨δ, rfl⟩
    exact ⟨δ, (bayesRisk_parameterZero E π δ).symm⟩
  · rintro ⟨δ, rfl⟩
    exact ⟨δ, bayesRisk_parameterZero E π δ⟩

/-- **Finite minimax duality with one parameter.**

    Both sides reduce to the infimum of the unique parameter's risk over randomized rules. -/
theorem finite_minimax_duality_parameterZero
    (E : Problem 0 actionCount observationCount) :
    E.minimaxRisk = E.mixtureDualRisk := by
  have hminimax : E.minimaxRisk = sInf (Set.range fun δ ↦ E.risk δ 0) := by
    unfold minimaxRisk
    congr 1
    ext value
    constructor
    · rintro ⟨δ, rfl⟩
      exact ⟨δ, (worstRisk_parameterZero E δ).symm⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨δ, worstRisk_parameterZero E δ⟩
  let πzero : FinitePrior 0 := PMF.pure 0
  have hdualRange :
      Set.range E.optimalBayesRisk =
        {sInf (Set.range fun δ ↦ E.risk δ 0)} := by
    ext value
    constructor
    · rintro ⟨π, rfl⟩
      exact Set.mem_singleton_iff.mpr (optimalBayesRisk_parameterZero E π)
    · intro hvalue
      rw [Set.mem_singleton_iff] at hvalue
      exact ⟨πzero, (optimalBayesRisk_parameterZero E πzero).trans hvalue.symm⟩
  unfold mixtureDualRisk
  rw [hdualRange, csSup_singleton, hminimax]

end Problem

end Calibrator.FiniteMinimax
