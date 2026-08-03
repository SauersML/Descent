/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.CertificateGrading

/-!
# Finite minimax duality: the ungraded certificate calculus

This file states the genuine finite decision problem behind the slogan
"ungraded mixture certificates are complete by minimax duality".  The problem
contains only an observation kernel and a numerical loss.  In particular, it
does not accept duality, compactness, convexity, or a lower bound as a field.

The sound inequality `mixtureDualRisk ≤ minimaxRisk` is proved from finite loss bounds. The
reverse inequality is the finite minimax theorem and remains an explicit `sorry`: importing a
literature theorem, assuming a duality proposition, or defining the dual value to equal the
primal value would make the file green while deleting its mathematical content.
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

/-- Forget the action/loss layer while retaining the exact observation kernel
used by the decision problem.  A target and its graded moment probes then make
that same kernel into a genuine mixture-certificate experiment. -/
noncomputable def toMixtureExperiment
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ) :
    FiniteMixtureExperiment parameterCount observationCount where
  target := target
  moment := moment
  observation := E.observation

/-- The bridge is law-preserving: the certificate layer and the decision
layer use exactly the same prior-predictive observation law. -/
@[simp] theorem toMixtureExperiment_mixture
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (π : FinitePrior parameterCount) :
    (E.toMixtureExperiment target moment).mixture π =
      π.bind E.observation := rfl

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

/-- **Half of duality, proved: a prior-averaged risk never exceeds the worst case.**

    `bayesRisk π δ` is an average of `risk δ θ` against a probability vector, and every
    term is at most `worstRisk δ`, which is the supremum over `θ`. The supremum is attained
    on a finite range, so it is a genuine bound rather than a formal `sSup`.

    This is the inequality that makes the mixture certificate sound: no prior can certify
    more than the minimax value. It is stated separately from the duality below because it
    is true unconditionally and needs no minimax theorem. -/
theorem bayesRisk_le_worstRisk (π : FinitePrior parameterCount)
    (δ : Rule actionCount observationCount) :
    E.bayesRisk π δ ≤ E.worstRisk δ := by
  have hbdd : BddAbove (Set.range (E.risk δ)) := (Set.finite_range _).bddAbove
  have hle : ∀ θ, E.risk δ θ ≤ E.worstRisk δ := fun θ ↦ le_csSup hbdd ⟨θ, rfl⟩
  have hmass : ∑ θ, FinitePrior.probability π θ = 1 :=
    (finitePrior_probability_mem π).2
  calc E.bayesRisk π δ = ∑ θ, FinitePrior.probability π θ * E.risk δ θ := rfl
    _ ≤ ∑ θ, FinitePrior.probability π θ * E.worstRisk δ :=
        Finset.sum_le_sum fun θ _ ↦
          mul_le_mul_of_nonneg_left (hle θ) (FinitePrior.probability_nonneg π θ)
    _ = E.worstRisk δ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Absolute loss bound at one parameter. The observation index is included in the sum to avoid
using normalization merely to optimize the constant. -/
noncomputable def pointRiskAbsBound (θ : Fin (parameterCount + 1)) : ℝ :=
  ∑ _x : Fin (observationCount + 1), ∑ a, |E.loss θ a|

/-- Uniform absolute risk bound for the whole finite decision problem. -/
noncomputable def riskAbsBound : ℝ := ∑ θ, E.pointRiskAbsBound θ

/-- Every pointwise risk is bounded by the finite absolute loss table. -/
theorem abs_risk_le_pointRiskAbsBound (δ : Rule actionCount observationCount)
    (θ : Fin (parameterCount + 1)) :
    |E.risk δ θ| ≤ E.pointRiskAbsBound θ := by
  have houter := FinitePrior.abs_mean_le_sum_abs (E.observation θ)
    (fun x ↦ FinitePrior.mean (δ x) (E.loss θ))
  have hinner : ∀ x : Fin (observationCount + 1),
      |FinitePrior.mean (δ x) (E.loss θ)| ≤ ∑ a, |E.loss θ a| :=
    fun x ↦ FinitePrior.abs_mean_le_sum_abs (δ x) (E.loss θ)
  calc
    |E.risk δ θ| =
        |FinitePrior.mean (E.observation θ)
          (fun x ↦ FinitePrior.mean (δ x) (E.loss θ))| := by
            rfl
    _ ≤ ∑ x, |FinitePrior.mean (δ x) (E.loss θ)| := houter
    _ ≤ ∑ x, ∑ a, |E.loss θ a| := Finset.sum_le_sum fun x _ ↦ hinner x
    _ = E.pointRiskAbsBound θ := rfl

/-- Bayes risks are uniformly bounded below, so their real-valued infimum is genuine. -/
theorem bayesRisk_bddBelow (π : FinitePrior parameterCount) :
    BddBelow (Set.range (E.bayesRisk π)) := by
  refine ⟨-E.riskAbsBound, ?_⟩
  rintro value ⟨δ, rfl⟩
  have hmean := FinitePrior.abs_mean_le_sum_abs π (E.risk δ)
  have hrisk : ∑ θ, |E.risk δ θ| ≤ E.riskAbsBound := by
    unfold riskAbsBound
    exact Finset.sum_le_sum fun θ _ ↦ E.abs_risk_le_pointRiskAbsBound δ θ
  exact neg_le_of_abs_le (hmean.trans hrisk)

/-- A fixed prior's optimal Bayes value is below every rule's worst-case risk. -/
theorem optimalBayesRisk_le_worstRisk (π : FinitePrior parameterCount)
    (δ : Rule actionCount observationCount) :
    E.optimalBayesRisk π ≤ E.worstRisk δ := by
  exact (csInf_le (E.bayesRisk_bddBelow π) ⟨δ, rfl⟩).trans
    (E.bayesRisk_le_worstRisk π δ)

/-- **The unconditional sound half of finite minimax duality.**

    Optimizing Bayes risk over every finite prior cannot exceed the minimax risk. This closes
    both order-theoretic layers of the earlier pointwise inequality and uses only the explicit
    finite loss bound above. -/
theorem mixtureDualRisk_le_minimaxRisk : E.mixtureDualRisk ≤ E.minimaxRisk := by
  unfold mixtureDualRisk minimaxRisk
  apply csSup_le (Set.range_nonempty E.optimalBayesRisk)
  intro bayesValue hbayes
  rcases hbayes with ⟨π, rfl⟩
  apply le_csInf (Set.range_nonempty E.worstRisk)
  intro worstValue hworst
  rcases hworst with ⟨δ, rfl⟩
  exact E.optimalBayesRisk_le_worstRisk π δ

/-- **Finite minimax duality.**  Ungraded mixture-versus-mixture reasoning is
complete because the primal minimax value equals the optimization over all
Bayes priors.  This is the real theorem, not a definitional equality and not a
caller-supplied proposition.

    WHAT IS PROVED, AND WHAT IS NOT. `mixtureDualRisk_le_minimaxRisk` proves the sound
    direction unconditionally: finite loss bounds make every real infimum genuine, and an
    average against a prior never exceeds the worst case. The reverse inequality is the minimax
    theorem itself and needs a finite-game separation argument this corpus does not yet carry.

    The `sorry` is the whole equality rather than the missing half, because splitting it
    into a proved inequality plus an assumed one would put the hard direction in a
    hypothesis, where no audit reads it.  Here `AxiomScan` reports it. -/
theorem finite_minimax_duality : E.minimaxRisk = E.mixtureDualRisk := by
  sorry

/-- The program's "vacuous ungraded completeness" statement, now tied to an
actual decision problem rather than to a value defined to equal itself. -/
theorem ungraded_certificate_calculus_complete :
    E.minimaxRisk = E.mixtureDualRisk :=
  E.finite_minimax_duality

end Problem

end Calibrator.FiniteMinimax
