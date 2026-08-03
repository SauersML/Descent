/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.TransportIdentities
import Calibrator.EpistasisAndNonAdditivity

namespace Calibrator

/-!
# Why effect sizes move: additivity, not ancestry

Cross-population differences in fitted effect sizes are routinely read as
evidence that the genotype-phenotype relationship itself differs between
populations, through gene-environment interaction, differential selection, or
population-specific causal variants. This file isolates the condition under
which that reading is forced, and it is narrower than usually assumed.

## The invariance

`additive_architecture_weights_are_transport_invariant` shows that if the
genetic architecture is exactly additive, so that the trait value is
`∑ⱼ βⱼ Gⱼ` with no dominance and no epistasis, then the population-optimal
additive weights equal `β` in *every* population, whatever the genotype
distribution. Allele frequencies may differ arbitrarily, linkage
disequilibrium may be reorganized, the covariance operator may be entirely
different; the optimal coefficients do not move. The only requirement is that
the covariance be invertible, which is the usual identifiability condition.

So under a strictly additive architecture, allele-frequency divergence is not
merely a weak explanation of effect-size heterogeneity, as
`Calibrator.HumanDemography` shows for accuracy; it explains none of it. The
optimal weights are a property of the causal map alone.

## The contrapositive, which is the useful direction

If fitted effect sizes differ between populations by more than sampling error,
then at least one of the following holds:

* the architecture is not additive, so that dominance or epistasis makes the
  average effect frequency-dependent, which is exactly
  `average_effect_frequency_dependent` in
  `Calibrator.EpistasisAndNonAdditivity`; or
* the causal map itself differs, through interaction with a differing
  environment or through population-specific causal variants; or
* the fitted score does not use the causal variants, but tags in linkage
  disequilibrium with them, in which case the tag-to-causal map is what moved
  and the causal effects need not have changed at all.

The first and third are artifacts in the sense that the underlying biology is
unchanged; only the second is a genuine difference in the genotype-phenotype
relationship. The invariance below is what makes the trichotomy exhaustive:
with additivity, direct causal predictors, and a fixed causal map, there is
nothing left that could move.

Fisher's average effect `α = a + d(1 - 2p)` is the one-locus instance. When
the dominance deviation `d` vanishes the average effect is `a` regardless of
`p`; when it does not, the average effect tracks allele frequency even though
the genotypic values `a` and `d` are fixed properties of the locus. The
theorem below is the multilocus, arbitrary-covariance form of that fact.
-/

section AdditiveInvariance

variable {Ω : Type*} {J : Type*} [Fintype J] [DecidableEq J]

/-- Under an exactly additive architecture the cross-covariance of the
predictors with the trait is the predictor covariance applied to the causal
effect vector. -/
theorem crossCovVector_causalSignal_self
    (E : ExpFunctional Ω) (X : Ω → J → ℝ) (β : J → ℝ) :
    crossCovVector E X (causalSignal β X) = (covarianceMatrix E X).mulVec β := by
  funext i
  unfold crossCovVector causalSignal dot covarianceMatrix Matrix.mulVec
  rw [covariance_finset_sum_right]
  simp only [Matrix.of_apply, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [show (fun ω ↦ β j * X ω j) = β j • (fun ω ↦ X ω j) from rfl,
    covariance_smul_right]
  ring

/-- **An exactly additive architecture has population-invariant optimal
weights.**

If the trait is `∑ⱼ βⱼ Xⱼ` with no non-additive contribution, the weights that
minimise squared error are `β` under every genotype distribution whose
predictor covariance is invertible. No allele-frequency divergence, however
large, moves them. -/
theorem additive_architecture_weights_are_transport_invariant
    (sigmaInv : Matrix J J ℝ) (E : ExpFunctional Ω) (X : Ω → J → ℝ) (β : J → ℝ)
    (hsigmaInv : covarianceMatrix E X * sigmaInv = 1) :
    optimalWeightsFromMoments sigmaInv E X (causalSignal β X) = β := by
  unfold optimalWeightsFromMoments
  rw [crossCovVector_causalSignal_self, Matrix.mulVec_mulVec,
    Matrix.mul_eq_one_comm.mp hsigmaInv, Matrix.one_mulVec]

/-- **Two populations sharing an additive causal map share their optimal
weights.**

Stated with two independent expectation functionals and two independent
predictor laws, to make explicit that nothing is assumed to be common between
the populations except the causal effect vector. -/
theorem additive_architecture_weights_agree_across_populations
    (sigmaInvP sigmaInvQ : Matrix J J ℝ)
    (EP EQ : ExpFunctional Ω) (XP XQ : Ω → J → ℝ) (β : J → ℝ)
    (hP : covarianceMatrix EP XP * sigmaInvP = 1)
    (hQ : covarianceMatrix EQ XQ * sigmaInvQ = 1) :
    optimalWeightsFromMoments sigmaInvP EP XP (causalSignal β XP) =
      optimalWeightsFromMoments sigmaInvQ EQ XQ (causalSignal β XQ) := by
  rw [additive_architecture_weights_are_transport_invariant sigmaInvP EP XP β hP,
    additive_architecture_weights_are_transport_invariant sigmaInvQ EQ XQ β hQ]

/-- **Contrapositive: differing optimal weights rule out the additive,
direct-predictor, shared-causal-map model.**

If two populations have different optimal additive weights, then they cannot
both be described by the same additive causal effect vector acting directly on
the predictors. Something in the trichotomy of the file docstring must give:
non-additivity, a changed causal map, or predictors that tag rather than cause. -/
theorem differing_weights_refute_shared_additive_map
    (sigmaInvP sigmaInvQ : Matrix J J ℝ)
    (EP EQ : ExpFunctional Ω) (XP XQ : Ω → J → ℝ) (β : J → ℝ)
    (hP : covarianceMatrix EP XP * sigmaInvP = 1)
    (hQ : covarianceMatrix EQ XQ * sigmaInvQ = 1)
    (hdiff :
      optimalWeightsFromMoments sigmaInvP EP XP (causalSignal β XP) ≠
        optimalWeightsFromMoments sigmaInvQ EQ XQ (causalSignal β XQ)) :
    False :=
  hdiff (additive_architecture_weights_agree_across_populations
    sigmaInvP sigmaInvQ EP EQ XP XQ β hP hQ)

end AdditiveInvariance

end Calibrator
