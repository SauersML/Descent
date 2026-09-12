/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Portability.NeutralFellerContinuity

assert_below Descent.Decision Descent.Program

/-!
# The neutral semigroup is a Feller semigroup

NOTE1 §4.2a constructs the neutral Markov kernels `K_t(x, dy)` from the extended neutral semigroup
`T_t` (`NeutralMicroscopicEulerLimit.neutralSemigroupExtension`,
`NeutralMicroscopicEulerLimit.neutralMarkovKernel`) and proves continuity at time zero
(`NeutralFellerContinuity`).  This module completes the Feller structure: strong continuity at
every time, joint continuity of the transition function, and the Feller property in the state.

The semigroup at time zero and the law.  The dual propagator at time zero is the identity, so the
polynomial semigroup and its extension start at the identity
(`neutralPolynomialSemigroup_zero`, `neutralSemigroupExtension_zero`), and the extension obeys
`T_{s+t} = T_s ∘ T_t` (`neutralSemigroupExtension_add`).

The Feller semigroup.  With the contraction bound, positivity, constant preservation and continuity
at time zero, the extended semigroup is a Feller semigroup in the sense of
`Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit.FellerSemigroup`
(`neutralFellerSemigroup`).  Its strong continuity at every time is then
`FellerSemigroup.continuous_operator`: `t ↦ T_t g` is continuous in sup norm for every continuous
observable `g` (`continuous_neutralSemigroupExtension`).

The transition function.  Evaluation is jointly continuous on `C(X, ℝ) × X`, so
`(t, x) ↦ ∫ g dK_t(x, ·)` is jointly continuous (`continuous_integral_neutralMarkovKernel_prod`).
For each fixed time the kernel has the Feller property: `x ↦ ∫ g dK_t(x, ·)` is continuous
(`continuous_integral_neutralMarkovKernel`), and `x ↦ K_t(x, ·)` is continuous into the
probability measures with the weak topology (`continuous_neutralMarkovKernel`), by
`FellerKernelRepresentation.continuous_kernelProbability`.

Scope.  The neutral rates are constant in time.

## Empirical status

None.  The bodies here are functional analysis of a supplied semigroup on the continuous
observables of the frequency simplex, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralFellerProperty

open MeasureTheory ProbabilityTheory Filter Topology Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator NeutralFellerGenerator NeutralPolynomialSemigroup
  PolynomialFellerExtension FellerKernelRepresentation NeutralMicroscopicEulerLimit
  NeutralFellerContinuity Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
open scoped NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The neutral polynomial semigroup starts at the identity.**  At time zero the dual propagator
is the identity matrix, so every polynomial observable is left unchanged. -/
theorem neutralPolynomialSemigroup_zero (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) :
    neutralPolynomialSemigroup rates ℓ₀ hap₀ 0 = LinearMap.id := by
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  have h := norm_neutralPolynomialSemigroup_sub_le rates ℓ₀ hap₀ 0 f
  rw [NNReal.coe_zero, matrixExponential_zero, sub_self, norm_zero, zero_mul, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The extended neutral semigroup starts at the identity. -/
theorem neutralSemigroupExtension_zero (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) :
    neutralSemigroupExtension rates ℓ₀ hap₀ 0
      = ContinuousLinearMap.id ℝ C(FrequencyState Deme Locus Allele, ℝ) :=
  denseExtension_eq_id _ dense_polynomialSubspace _ _
    (neutralPolynomialSemigroup_zero rates ℓ₀ hap₀)

/-- **The semigroup law of the extension**, `T_{s+t} = T_s ∘ T_t`. -/
theorem neutralSemigroupExtension_add (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (s t : ℝ≥0) :
    neutralSemigroupExtension rates ℓ₀ hap₀ (s + t)
      = (neutralSemigroupExtension rates ℓ₀ hap₀ s).comp
          (neutralSemigroupExtension rates ℓ₀ hap₀ t) :=
  denseExtension_add _ dense_polynomialSubspace (neutralPolynomialSemigroup rates ℓ₀ hap₀)
    (norm_neutralPolynomialSemigroup_le rates ℓ₀ hap₀)
    (neutralPolynomialSemigroup_add rates ℓ₀ hap₀) s t

/-- **The neutral Feller semigroup.**  The extended neutral semigroup is a positive sup-norm
contraction semigroup fixing the constants, starting at the identity and strongly continuous at
time zero. -/
def neutralFellerSemigroup (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) :
    FellerSemigroup (FrequencyState Deme Locus Allele) where
  operator := neutralSemigroupExtension rates ℓ₀ hap₀
  norm_le _ g := denseExtension_norm_le _ dense_polynomialSubspace _ _ g
  map_one := neutralSemigroupExtension_one rates ℓ₀ hap₀
  nonneg := neutralSemigroupExtension_nonneg rates ℓ₀ hap₀
  operator_zero := neutralSemigroupExtension_zero rates ℓ₀ hap₀
  operator_add := neutralSemigroupExtension_add rates ℓ₀ hap₀
  tendsto_operator_zero := tendsto_neutralSemigroupExtension_zero rates ℓ₀ hap₀

/-- **Strong continuity at every time.**  For every continuous observable `g`, `t ↦ T_t g` is
continuous in sup norm. -/
theorem continuous_neutralSemigroupExtension (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    Continuous fun t : ℝ≥0 ↦ neutralSemigroupExtension rates ℓ₀ hap₀ t g :=
  (neutralFellerSemigroup rates ℓ₀ hap₀).continuous_operator g

/-- **The transition function is jointly continuous.**  For every continuous observable `g`,
`(t, x) ↦ ∫ g dK_t(x, ·)` is continuous. -/
theorem continuous_integral_neutralMarkovKernel_prod (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    Continuous fun q : ℝ≥0 × FrequencyState Deme Locus Allele ↦
      ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ q.1 q.2) := by
  have hfun : (fun q : ℝ≥0 × FrequencyState Deme Locus Allele ↦
        ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ q.1 q.2))
      = fun q ↦ neutralSemigroupExtension rates ℓ₀ hap₀ q.1 g q.2 :=
    funext fun q ↦ integral_neutralMarkovKernel rates ℓ₀ hap₀ q.1 q.2 g
  rw [hfun]
  exact ContinuousMap.continuous_eval.comp
    ((continuous_neutralSemigroupExtension rates ℓ₀ hap₀ g).prodMap continuous_id)

/-- **The Feller property.**  At every time the neutral kernel carries continuous observables to
continuous observables: `x ↦ ∫ g dK_t(x, ·)` is continuous. -/
theorem continuous_integral_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    Continuous fun x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x) := by
  have hfun : (fun x ↦ ∫ y, g y ∂(neutralMarkovKernel rates ℓ₀ hap₀ t x))
      = ⇑(neutralSemigroupExtension rates ℓ₀ hap₀ t g) :=
    funext fun x ↦ integral_neutralMarkovKernel rates ℓ₀ hap₀ t x g
  rw [hfun]
  exact (neutralSemigroupExtension rates ℓ₀ hap₀ t g).continuous

/-- **Weak continuity in the state.**  At every time `x ↦ K_t(x, ·)` is continuous into the
probability measures on the frequency simplex with the topology of weak convergence. -/
theorem continuous_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0) :
    Continuous fun x : FrequencyState Deme Locus Allele ↦
      (⟨neutralMarkovKernel rates ℓ₀ hap₀ t x,
        (isMarkovKernel_neutralMarkovKernel rates ℓ₀ hap₀ t).isProbabilityMeasure x⟩ :
          ProbabilityMeasure (FrequencyState Deme Locus Allele)) :=
  continuous_kernelProbability (neutralSemigroupExtension rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_nonneg rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_one rates ℓ₀ hap₀ t)

end

end Descent.Portability.NeutralFellerProperty
