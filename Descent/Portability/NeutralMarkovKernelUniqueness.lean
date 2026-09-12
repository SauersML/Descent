/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralMicroscopicEulerLimit

assert_below Descent.Decision Descent.Program

/-!
# Uniqueness of the neutral Markov kernels

NOTE1 §4.2a: the representation theorem for positive functionals on compact spaces supplies a
unique probability kernel `K_t(x, dy)` with `T_t f(x) = ∫ f(y) K_t(x, dy)`.  This module proves the
uniqueness for the neutral model.

A probability measure that integrates every polynomial observable to the neutral polynomial
semigroup at a state integrates every continuous observable to the extended semigroup
(`integral_eq_neutralSemigroupExtension`): integration against a probability measure is
1-Lipschitz in sup norm, the extension is continuous, and the polynomial observables are dense.
On the pseudo-metrizable frequency simplex the representing finite measure is unique
(`FellerKernelRepresentation.kernelMeasure_eq_of_integral_eq`).  So every family of Markov
kernels representing the neutral polynomial semigroup is the family `neutralMarkovKernel`
(`neutralMarkovKernel_unique`), and there is exactly one such family
(`existsUnique_neutralMarkovKernel`).  In particular the kernels supplied by
`NeutralPolynomialPositivity.exists_neutralMarkovKernel` are the neutral Markov kernels, the
limit in law of the microscopic chain.

## Empirical status

None.  The bodies here are measure theory on the frequency simplex, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralMarkovKernelUniqueness

open MeasureTheory ProbabilityTheory Filter Topology NeutralFellerGenerator
  NeutralPolynomialSemigroup NeutralPolynomialPositivity PolynomialFellerExtension
  FellerKernelRepresentation FellerMarkovKernel NeutralMicroscopicEulerLimit
open scoped NNReal

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **A representing probability measure represents the extension.**  A probability measure that
integrates every polynomial observable to the neutral polynomial semigroup at a state integrates
every continuous observable to the extended neutral semigroup at that state. -/
theorem integral_eq_neutralSemigroupExtension (rates : NeutralRates Deme Locus Allele)
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (t : ℝ≥0)
    (x : FrequencyState Deme Locus Allele) (μ : Measure (FrequencyState Deme Locus Allele))
    [IsProbabilityMeasure μ]
    (hμ : ∀ f : PolynomialSubspace Deme Locus Allele,
      ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂μ
        = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
          : C(FrequencyState Deme Locus Allele, ℝ)) x)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ∫ y, g y ∂μ = neutralSemigroupExtension rates ℓ₀ hap₀ t g x := by
  have hi : ∀ h : C(FrequencyState Deme Locus Allele, ℝ), Integrable (fun y ↦ h y) μ :=
    fun h ↦ (BoundedContinuousFunction.mkOfCompact h).integrable μ
  have hint : Continuous fun h : C(FrequencyState Deme Locus Allele, ℝ) ↦ ∫ y, h y ∂μ := by
    refine (LipschitzWith.of_dist_le_mul fun h₁ h₂ ↦ ?_).continuous
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rw [dist_eq_norm, ← integral_sub (hi h₁) (hi h₂), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const
      (ae_of_all μ fun y ↦ ContinuousMap.norm_coe_le_norm (h₁ - h₂) y)).trans_eq ?_
    rw [measureReal_univ_eq_one, mul_one]
  refine dense_polynomialSubspace.denseRange_val.induction_on g
    (isClosed_eq hint ((continuous_eval_const x).comp
      (neutralSemigroupExtension rates ℓ₀ hap₀ t).continuous)) fun f ↦ ?_
  rw [neutralSemigroupExtension, denseExtension_coe]
  exact hμ f

/-- **Uniqueness of the neutral Markov kernels.**  Every family of Markov kernels on the frequency
states that represents the neutral polynomial semigroup is the family of neutral Markov
kernels. -/
theorem neutralMarkovKernel_unique (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [∀ t, IsMarkovKernel (K t)]
    (hrep : ∀ t x (f : PolynomialSubspace Deme Locus Allele),
      ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂(K t x)
        = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
          : C(FrequencyState Deme Locus Allele, ℝ)) x) :
    K = neutralMarkovKernel rates ℓ₀ hap₀ := by
  funext t
  refine DFunLike.ext _ _ fun x ↦ ?_
  exact kernelMeasure_eq_of_integral_eq (neutralSemigroupExtension rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_nonneg rates ℓ₀ hap₀ t)
    (neutralSemigroupExtension_one rates ℓ₀ hap₀ t) x (K t x)
    (integral_eq_neutralSemigroupExtension rates ℓ₀ hap₀ t x (K t x) (hrep t x))

/-- **NOTE1 §4.2a, the unique probability kernel.**  Exactly one family of Markov kernels on the
frequency states represents the neutral polynomial semigroup. -/
theorem existsUnique_neutralMarkovKernel (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) :
    ∃! K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele),
      (∀ t, IsMarkovKernel (K t)) ∧
        ∀ t x (f : PolynomialSubspace Deme Locus Allele),
          ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂(K t x)
            = (neutralPolynomialSemigroup rates ℓ₀ hap₀ t f
              : C(FrequencyState Deme Locus Allele, ℝ)) x := by
  refine ⟨neutralMarkovKernel rates ℓ₀ hap₀,
    ⟨isMarkovKernel_neutralMarkovKernel rates ℓ₀ hap₀,
      integral_neutralMarkovKernel_polynomial rates ℓ₀ hap₀⟩, fun K hK ↦ ?_⟩
  haveI := hK.1
  exact neutralMarkovKernel_unique rates ℓ₀ hap₀ K hK.2

end

end Descent.Portability.NeutralMarkovKernelUniqueness
