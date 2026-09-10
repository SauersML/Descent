/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# What observed portability can identify about its mechanism

Two explicit populations have the same complete scored-genotype/outcome law,
not merely the same R². One loses tagging with a unit causal effect; the other
has perfect tagging with an attenuated effect and an orthogonal residual.
All variances and covariances are evaluated from four equally likely states.
Thus observational portability alone cannot classify these mechanisms. These
are constructed populations, not an attribution of immune-trait findings.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MechanismIdentification

open Foundations

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

noncomputable section

def marker : Fin 4 → ℝ := ![-1, -1, 1, 1]
def hidden : Fin 4 → ℝ := ![-1, 1, -1, 1]

/-- A standardized causal coordinate imperfectly tagged by the scored marker. -/
def taggingWorld : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1) where
  E := uniformExp (Fin 4)
  X := fun i _ ↦ marker i
  C := fun i _ ↦ (3 * marker i + 4 * hidden i) / 5
  β := fun _ ↦ 1
  h := fun _ ↦ 0

/-- The causal coordinate is the scored marker, with an attenuated effect. -/
def effectWorld : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1) where
  E := uniformExp (Fin 4)
  X := fun i _ ↦ marker i
  C := fun i _ ↦ marker i
  β := fun _ ↦ 3 / 5
  h := fun i ↦ 4 * hidden i / 5

/-- Equality of the individual observables implies equality of every statistic
computed solely from the scored genotypes and outcome, including all thresholds. -/
theorem complete_observational_equivalence :
    taggingWorld.X = effectWorld.X ∧ taggingWorld.phenotype = effectWorld.phenotype := by
  refine ⟨rfl, ?_⟩
  funext i
  simp [DeploymentPopulation.phenotype, causalSignal, dot, taggingWorld, effectWorld]
  ring

/-- Both causal coordinates have unit variance; the two residuals are orthogonal
to their causal coordinate. The ambiguity does not rely on arbitrary confounding. -/
theorem standardized_orthogonal_worlds :
    taggingWorld.sigmaC 0 0 = 1 ∧ effectWorld.sigmaC 0 0 = 1 ∧
      taggingWorld.contextC 0 = 0 ∧ effectWorld.contextC 0 = 0 := by
  norm_num [DeploymentPopulation.sigmaC, DeploymentPopulation.contextC,
    covarianceMatrix, contextCrossCovVector, covariance_eq_expect_mul_sub_means,
    taggingWorld, effectWorld, marker, hidden, uniformExp_apply, Fin.sum_univ_four]

theorem different_tagging_and_effects :
    taggingWorld.kappa 0 0 = 3 / 5 ∧ effectWorld.kappa 0 0 = 1 ∧
      taggingWorld.β 0 = 1 ∧ effectWorld.β 0 = 3 / 5 := by
  norm_num [DeploymentPopulation.kappa, predictorCausalCovariance,
    covariance_eq_expect_mul_sub_means, taggingWorld, effectWorld, marker, hidden,
    uniformExp_apply, Fin.sum_univ_four]

/-- Nondegenerate accuracy evaluated from the generated phenotype. -/
theorem common_accuracy :
    taggingWorld.scoreVariance (fun _ ↦ 1) = 1 ∧
      taggingWorld.outcomeVariance = 1 ∧ taggingWorld.r2 (fun _ ↦ 1) = 9 / 25 ∧
      effectWorld.r2 (fun _ ↦ 1) = 9 / 25 := by
  norm_num [DeploymentPopulation.scoreVariance, DeploymentPopulation.outcomeVariance,
    DeploymentPopulation.r2, DeploymentPopulation.predictiveCovariance,
    DeploymentPopulation.phenotype, DeploymentPopulation.score, causalSignal,
    linScore, dot, variance_eq_expect_sq_sub_sq_mean,
    covariance_eq_expect_mul_sub_means, taggingWorld, effectWorld, marker, hidden,
    uniformExp_apply, Fin.sum_univ_four]

/-- No classifier of the complete scored-genotype/outcome observation can recover
the causal effect for every deployment, even on this fixed four-state probability space. -/
theorem causal_effect_not_identified :
    ¬ ∃ readout : ((Fin 4 → Fin 1 → ℝ) × (Fin 4 → ℝ)) → ℝ,
      ∀ P : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1),
        P.E = uniformExp (Fin 4) → readout (P.X, P.phenotype) = P.β 0 := by
  rintro ⟨readout, h⟩
  have ht := h taggingWorld rfl
  have he := h effectWorld rfl
  rw [complete_observational_equivalence.1, complete_observational_equivalence.2] at ht
  have := ht.symm.trans he
  norm_num [taggingWorld, effectWorld] at this

/-- Making both coordinates available leaves trait biology fixed while allowing
different score construction rules to give different portability. -/
def twoMarkerWorld : DeploymentPopulation (Fin 4) (Fin 2) (Fin 1) where
  E := uniformExp (Fin 4)
  X := fun i ↦ ![marker i, hidden i]
  C := fun i _ ↦ marker i
  β := fun _ ↦ 3 / 5
  h := fun i ↦ 4 * hidden i / 5

theorem score_construction_changes_accuracy :
    twoMarkerWorld.r2 ![1, 0] = 9 / 25 ∧
      twoMarkerWorld.r2 ![3 / 5, 4 / 5] = 1 := by
  norm_num [DeploymentPopulation.r2, DeploymentPopulation.scoreVariance,
    DeploymentPopulation.outcomeVariance, DeploymentPopulation.predictiveCovariance,
    DeploymentPopulation.phenotype, DeploymentPopulation.score, causalSignal,
    linScore, dot, variance_eq_expect_sq_sub_sq_mean,
    covariance_eq_expect_mul_sub_means, twoMarkerWorld, marker, hidden,
    uniformExp_apply, Fin.sum_univ_four, Fin.sum_univ_two]

end

end Descent.Portability.MechanismIdentification
