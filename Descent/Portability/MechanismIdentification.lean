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

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Core.innerSum

noncomputable section

/-- Reassign the additive effect while compensating inside the unrestricted
residual. This preserves every observed phenotype, even if causal genotypes
themselves are included among the observations. -/
def reassignEffect {Ω J L : Type*} [Fintype L]
    (P : DeploymentPopulation Ω J L) (effects : L → ℝ) : DeploymentPopulation Ω J L where
  E := P.E
  X := P.X
  C := P.C
  β := effects
  h := fun ω ↦ P.phenotype ω - causalSignal effects P.C ω

/-- Sharp identification region: with unrestricted residual structure, every
effect vector is compatible with the same complete genetic/phenotypic input.
Exogeneity or an intervention semantics therefore changes the admissible class,
rather than being recoverable from the observational distribution alone. -/
theorem unrestricted_effect_fiber_full {Ω J L : Type*} [Fintype L]
    (P : DeploymentPopulation Ω J L) (effects : L → ℝ) :
    ∃ Q : DeploymentPopulation Ω J L,
      Q.E = P.E ∧ Q.X = P.X ∧ Q.C = P.C ∧ Q.phenotype = P.phenotype ∧ Q.β = effects := by
  refine ⟨reassignEffect P effects, rfl, rfl, rfl, ?_, rfl⟩
  funext ω
  simp [DeploymentPopulation.phenotype, reassignEffect]

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

/-- Observing the causal coordinate supplies a discriminator that the scored
genotype/outcome law lacks. Its covariance with outcome differs in these worlds. -/
theorem causal_observation_separates :
    covariance taggingWorld.E (fun i ↦ taggingWorld.C i 0) taggingWorld.phenotype = 1 ∧
      covariance effectWorld.E (fun i ↦ effectWorld.C i 0) effectWorld.phenotype = 3 / 5 := by
  norm_num [covariance_eq_expect_mul_sub_means, DeploymentPopulation.phenotype,
    causalSignal, dot, taggingWorld, effectWorld, marker, hidden,
    uniformExp_apply, Fin.sum_univ_four]

/-- Same-variance independent standardized loci give additive signal variance
equal to squared effect mass. These two architectures have the same number of loci. -/
def concentratedSignal : Fin 2 → ℝ := ![1, 7]
def evenSignal : Fin 2 → ℝ := ![5, 5]

/-- Centered replication noise is shared by both architectures. The true effects
do not change between discovery and replication; discovery signs are positive. -/
def replicationNoise (b : Bool) : ℝ := if b then 2 else -2

def replicationFlipRate (beta : Fin 2 → ℝ) : ℝ :=
  uniformExp (Fin 2 × Bool) (fun z ↦
    if beta z.1 + replicationNoise z.2 < 0 then 1 else 0)

/-- Matching total genetic signal and replication-noise variance does not match
estimated sign-flip rates, even with no true turnover and the same locus count.
This finite noise model is a counterexample to sufficiency, not a Gaussian fit
or a reproduction of a discovery-selection pipeline. -/
theorem matched_signal_different_flip_rates :
    (∑ j, concentratedSignal j ^ 2) = 50 ∧ (∑ j, evenSignal j ^ 2) = 50 ∧
      uniformExp Bool replicationNoise = 0 ∧
      variance (uniformExp Bool) replicationNoise = 4 ∧
      replicationFlipRate concentratedSignal = 1 / 4 ∧ replicationFlipRate evenSignal = 0 := by
  norm_num [concentratedSignal, evenSignal, replicationNoise, replicationFlipRate,
    variance_eq_expect_sq_sub_sq_mean, uniformExp_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, Fin.sum_univ_two]

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
