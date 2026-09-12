/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeMicroscopicApproximation
import Descent.Portability.PartialHaplotypePanelLikelihood

assert_below Descent.Decision Descent.Program

/-!
# Exact panel reports under the realized neutral expectation family

NOTE1 §4.2 states that (20) gives the exact sampled-genotype probabilities at the full-panel seed
configurations.  `PartialHaplotypePanelLikelihood.expectedPanelReport_eq_matrixExponential`
proves the compiled report identity for every expectation family obeying the forward moment
equation, and `PartialHaplotypeMicroscopicApproximation.realizedExpectation_forward` constructs
such a family, for every neutral model, from the physical microscopic kernel.  This module
combines the two with no hypothesis: under the realized family started at a frequency state, the
expected compiled report of an independently sampled panel at every time `t ≥ 0` is the sum over
panel genotypes of the conditional readout times the seed coordinate of `e^{tQ} H(x₀)`
(`realizedPanelReport_eq_matrixExponential`).

## Empirical status

None.  The bodies here are algebra: finite sums of supplied readouts against a matrix exponential
of supplied rates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeRealizedPanel

open MvPolynomial Descent.Coalescent PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup NeutralFellerGenerator PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePanelLikelihood

noncomputable section

variable {Deme Locus Sample Report : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
  [Fintype Sample] [DecidableEq Sample] [Fintype Report]

/-- The realized family starts at the moments of its initial state. -/
theorem expectedMomentVector_realizedExpectation_zero (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (x0 : FrequencyState Deme Locus Allele) :
    expectedMomentVector capacity (realizedExpectation rates capacity x0) 0
      = budgetMomentFeature capacity x0 := by
  rw [expectedMomentVector_realizedExpectation rates capacity x0 0 le_rfl, matrixExponential_zero,
    Matrix.one_mulVec]

/-- **NOTE1 (20) with (22), unconditionally.**  Under the realized neutral expectation family
started at a frequency state, the expected compiled report of an independently sampled panel at
every nonnegative time is the sum over panel genotypes of the conditional readout times the seed
coordinate of the dual propagator applied to the initial moments. -/
theorem realizedPanelReport_eq_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (ℓ₀ : Locus) (x0 : FrequencyState Deme Locus Allele) (t : ℝ)
    (ht : 0 ≤ t) :
    (realizedExpectation rates (fun _ ↦ Fintype.card Sample) x0 t fun law ↦
        ((FiniteGeneticTransition.piLaw fun draw ↦ law (deme draw)).bind report).expectation
          metric)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric *
            (matrixExponential (dualGenerator rates (fun _ ↦ Fintype.card Sample)) t).mulVec
              (budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0)
              (seedState deme genotype ℓ₀) := by
  rw [expectedPanelReport_eq_matrixExponential rates deme report metric ℓ₀ _
    (realizedExpectation_forward rates _ x0) t ht,
    expectedMomentVector_realizedExpectation_zero]

end

end Descent.Portability.PartialHaplotypeRealizedPanel
