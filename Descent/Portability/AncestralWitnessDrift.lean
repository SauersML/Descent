/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralForwardGenerator

assert_below Descent.Decision Descent.Program

/-!
# The witness drifts (5.5) as time derivatives

§5.2 of the ancestral locality note takes the eight-state witness of
`Descent.Pangenome.AncestralLocality.CompatibilityNeutrality`: features `(a, b, h)`, the single rule
"exchange `a` only when the parents agree at `h`" at unit rate, and the populations
`p = ½δ_000 + ½δ_110` and `q = ½δ_000 + ½δ_111`, which have the same observed law of `(a, b)`.
(5.5) states `d/dt E_p[ab]|_0 = -1/4` and `d/dt E_q[ab]|_0 = 0` under the diffusion (7.1), while
`CompatibilityNeutrality.witness_drift` proves the one-step differences `R_K(p)[ab] - p[ab]`.
This file evaluates the forward generator (7.1) of
`Descent.Portability.AncestralForwardGenerator` on the observable `F(p) = E_p[ab]` and proves the
derivatives themselves.

- `observedProductPolynomial` is `F(p) = ∑_z ab(z) p_z`, a linear polynomial in the genome
  frequencies (`eval_observedProductPolynomial`), whose first partial derivatives are the observed
  product (`eval_pderiv_observedProductPolynomial`).
- `resamplingOperator_observedProductPolynomial`: the resampling half of (7.1) vanishes on `F`,
  because its second partial derivatives vanish.  So at every resampling rate `c` the generator
  on `F` is the checked-exchange drift alone, `L F(p) = R_K(p)[ab] - p[ab]`
  (`forwardGenerator_observedProductPolynomial`).
- `witness_generator`: **(5.5)**, `L F(p) = -1/4` and `L F(q) = 0`, at every resampling rate.
- `tendsto_witnessP_nextGenerationMean`, `tendsto_witnessQ_nextGenerationMean`: the same numbers
  as derivatives on the `N`-generation scale of the finite population (4.5).  One generation of
  `N` offspring changes `E[ab]` by `-1/(4N)` from `p` and by `o(1/N)` from `q`:
  `N (E[F(P')] - F(p)) → -1/4` and `N (E[F(Q')] - F(q)) → 0`.

Scope.  The derivative at `t = 0` is stated as the generator value, and its dynamical reading is
the `N`-generation limit of `AncestralForwardGenerator.tendsto_nextGenerationMean`, at resampling
rate `1`.  The diffusion semigroup of (7.1) is not constructed.

## Empirical status

None.  The bodies are the evaluation of a polynomial generator at two explicit populations, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralWitnessDrift

open Filter Topology MvPolynomial
open Descent.Pangenome.AncestralLocality Descent.Portability.AncestralForwardGenerator
open Descent.Portability.MultinomialMomentExpansion Descent.Portability.MultinomialDriftStage

noncomputable section

/-! ## The observable `E_p[ab]` -/

/-- The observable `F(p) = E_p[ab] = ∑_z ab(z) p_z`, a linear polynomial in the genome
frequencies. -/
def observedProductPolynomial : MvPolynomial (Fin 3 → Bool) ℝ :=
  ∑ z, observedProduct z • X z

/-- At a population, `F` is the mean of the observed product. -/
theorem eval_observedProductPolynomial (p : (Fin 3 → Bool) → ℝ) :
    eval p observedProductPolynomial = ∑ z, p z * observedProduct z := by
  simp only [observedProductPolynomial, map_sum, smul_eval, eval_X]
  exact Finset.sum_congr rfl fun z _ ↦ mul_comm _ _

/-- The first partial derivatives of `F` are the observed product, `∂_z F = ab(z)`. -/
theorem eval_pderiv_observedProductPolynomial (p : (Fin 3 → Bool) → ℝ) (z : Fin 3 → Bool) :
    eval p (pderiv z observedProductPolynomial) = observedProduct z := by
  simp only [observedProductPolynomial, map_sum, Derivation.map_smul, smul_eval,
    eval_pderiv_X_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-- **The resampling half vanishes** on the linear observable: its second partial derivatives
are zero. -/
theorem resamplingOperator_observedProductPolynomial (p : (Fin 3 → Bool) → ℝ) :
    resamplingOperator p observedProductPolynomial = 0 := by
  change resamplingOperatorHom p observedProductPolynomial = 0
  rw [observedProductPolynomial, map_sum]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  change resamplingOperator p (observedProduct z • X z) = 0
  rw [resamplingOperator_smul, resamplingOperator_X, mul_zero]

/-- **At every resampling rate the generator on `F` is the drift alone**: for the witness rule,
`L F(p) = R_K(p)[ab] - p[ab]`. -/
theorem forwardGenerator_observedProductPolynomial (c : ℝ) (p : (Fin 3 → Bool) → ℝ) :
    forwardGenerator witnessGraph c p observedProductPolynomial =
      ∑ z, reproduce (compatibilityKernel witnessGraph) p z * observedProduct z -
        ∑ z, p z * observedProduct z := by
  have hkernel : compatibilityKernel witnessGraph = exchangeKernel 0 2 := by
    funext x y z
    exact compatibilityKernel_singleEdge 0 2 x y z
  rw [forwardGenerator, resamplingOperator_observedProductPolynomial, mul_zero, zero_add, hkernel]
  simp only [witnessGraph, singleEdge, Finset.sum_singleton, one_mul,
    eval_pderiv_observedProductPolynomial, sub_mul, Finset.sum_sub_distrib]

/-! ## (5.5) -/

/-- **(5.5), the derivatives.**  At unit event rate and every resampling rate `c`, the forward
generator (7.1) on `F(p) = E_p[ab]` is `-1/4` at `p` and `0` at `q`, although `p` and `q` have the
same observed law. -/
theorem witness_generator (c : ℝ) :
    forwardGenerator witnessGraph c witnessP observedProductPolynomial = -1 / 4 ∧
      forwardGenerator witnessGraph c witnessQ observedProductPolynomial = 0 := by
  rw [forwardGenerator_observedProductPolynomial, forwardGenerator_observedProductPolynomial]
  exact witness_drift

/-- The witness population `p` as a probability law on genomes. -/
def witnessLawP : FiniteReportLaw (Fin 3 → Bool) where
  mass := witnessP
  mass_nonneg := halfMix_nonneg _ _
  mass_sum := sum_halfMix _ _

/-- The witness population `q` as a probability law on genomes. -/
def witnessLawQ : FiniteReportLaw (Fin 3 → Bool) where
  mass := witnessQ
  mass_nonneg := halfMix_nonneg _ _
  mass_sum := sum_halfMix _ _

/-- **(5.5) on the `N`-generation scale from `p`.**  One generation of `N` offspring of the finite
population (4.5) changes `E[ab]` by `-1/(4N)` to first order: `N (E[F(P')] - F(p)) → -1/4`. -/
theorem tendsto_witnessP_nextGenerationMean :
    Tendsto (fun N : ℕ ↦ (N : ℝ) *
        (nextGenerationMean witnessGraph N witnessP observedProductPolynomial -
          ∑ z, witnessP z * observedProduct z)) atTop (𝓝 (-1 / 4)) := by
  have h : Tendsto (fun N : ℕ ↦ (N : ℝ) *
      (nextGenerationMean witnessGraph N witnessP observedProductPolynomial -
        eval witnessP observedProductPolynomial)) atTop
      (𝓝 (forwardGenerator witnessGraph 1 witnessP observedProductPolynomial)) :=
    tendsto_nextGenerationMean witnessGraph witnessLawP observedProductPolynomial
  rwa [eval_observedProductPolynomial, (witness_generator 1).1] at h

/-- **(5.5) on the `N`-generation scale from `q`.**  One generation of `N` offspring changes
`E[ab]` by `o(1/N)`: `N (E[F(Q')] - F(q)) → 0`. -/
theorem tendsto_witnessQ_nextGenerationMean :
    Tendsto (fun N : ℕ ↦ (N : ℝ) *
        (nextGenerationMean witnessGraph N witnessQ observedProductPolynomial -
          ∑ z, witnessQ z * observedProduct z)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ ↦ (N : ℝ) *
      (nextGenerationMean witnessGraph N witnessQ observedProductPolynomial -
        eval witnessQ observedProductPolynomial)) atTop
      (𝓝 (forwardGenerator witnessGraph 1 witnessQ observedProductPolynomial)) :=
    tendsto_nextGenerationMean witnessGraph witnessLawQ observedProductPolynomial
  rwa [eval_observedProductPolynomial, (witness_generator 1).2] at h

end

end Descent.Portability.AncestralWitnessDrift
