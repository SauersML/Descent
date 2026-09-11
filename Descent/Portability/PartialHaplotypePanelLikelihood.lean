/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualSemigroup
import Descent.Portability.ConditionalReportCompilation

assert_below Descent.Decision Descent.Program

/-!
# Exact panel likelihoods from the partial-haplotype dual semigroup

NOTE1 §4.2 states that (20) gives the exact sampled-genotype probabilities at the full-panel seed
configurations, and §4.3 compiles a finite-cohort report through the genotype likelihood (22).
This module joins the two.  A sampled panel draws one chromosome per sample from the haplotype law
of the sample's deme.  The seed configuration of a genotype of the panel carries one fully retained
carrier per sample (`seedConfiguration`).  Its configuration moment is the probability of that
genotype, `Π_j x_{d_j}[g_j]` (`configurationMoment_seedConfiguration`), and it loads every locus
once per sample, so it lies in the budget-respecting state space whose capacity is the panel size
(`withinBudget_seedConfiguration`, `seedState`).

Combining (22) for the panel,
`Descent.Portability.ConditionalReportCompilation.panel_compiled_expectation_eq_frequency_polynomial`,
with (20), `Descent.Portability.PartialHaplotypeDualSemigroup.expectedMomentVector_eq_matrixExponential`,
gives `expectedPanelReport_eq_matrixExponential`.  For any expectation family obeying the forward
moment equation, the expected compiled report of the panel experiment at time `t` is the finite
sum over genotypes of the conditional readout times the seed coordinate of `e^{tQ} v(0)`.  A
nonlinear finite-cohort metric therefore needs only finitely many coordinates of one matrix
exponential.

Scope.  The forward moment equation is a hypothesis on the expectation family, as in
`PartialHaplotypeDualSemigroup`.  Continuous integrals inside the report kernel are not
evaluated here.

## Empirical status

None.  The bodies here are algebra: products of supplied haplotype masses and finite sums of
supplied readouts against a matrix exponential, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypePanelLikelihood

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open Descent.Coalescent Descent.Foundations MvPolynomial

variable {Deme Locus Sample Report : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
  [Fintype Sample] [DecidableEq Sample] [Fintype Report]

noncomputable section

/-- The seed configuration of a panel genotype: one fully retained carrier per sample, in the
sample's deme and carrying the sample's haplotype.  The locus `ℓ₀` witnesses that loci exist. -/
def seedConfiguration (deme : Sample → Deme) (genotype : Sample → FullHaplotype Locus Allele)
    (ℓ₀ : Locus) : Multiset (PartialType Deme Locus Allele) :=
  Finset.univ.val.map fun draw ↦ fullType (deme draw) (genotype draw) ℓ₀

/-- The configuration moment of a seed configuration is the probability of the panel
genotype. -/
theorem configurationMoment_seedConfiguration
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (deme : Sample → Deme)
    (genotype : Sample → FullHaplotype Locus Allele) (ℓ₀ : Locus) :
    configurationMoment law (seedConfiguration deme genotype ℓ₀)
      = ∏ draw, (law (deme draw)).mass (genotype draw) := by
  rw [configurationMoment, seedConfiguration, Multiset.map_map]
  exact Finset.prod_congr rfl fun draw _ ↦
    marginalFrequency_fullType law (deme draw) (genotype draw) ℓ₀

/-- A seed configuration loads every locus once per sample. -/
theorem load_seedConfiguration (deme : Sample → Deme)
    (genotype : Sample → FullHaplotype Locus Allele) (ℓ₀ ℓ : Locus) :
    load (seedConfiguration deme genotype ℓ₀) ℓ = Fintype.card Sample := by
  rw [load, seedConfiguration, Multiset.countP_map,
    Multiset.filter_eq_self.mpr fun draw _ ↦ by simp [fullType]]
  rfl

/-- A seed configuration respects the budget whose capacity at every locus is the panel size. -/
theorem withinBudget_seedConfiguration (deme : Sample → Deme)
    (genotype : Sample → FullHaplotype Locus Allele) (ℓ₀ : Locus) :
    WithinBudget (fun _ ↦ Fintype.card Sample) (seedConfiguration deme genotype ℓ₀) :=
  fun ℓ ↦ (load_seedConfiguration deme genotype ℓ₀ ℓ).le

/-- The seed configuration of a panel genotype as a state of the budget-respecting chain. -/
def seedState (deme : Sample → Deme) (genotype : Sample → FullHaplotype Locus Allele)
    (ℓ₀ : Locus) : BudgetConfiguration Deme Locus Allele (fun _ ↦ Fintype.card Sample) :=
  ⟨seedConfiguration deme genotype ℓ₀, withinBudget_seedConfiguration deme genotype ℓ₀⟩

/-- **NOTE1 (20) with (22): exact expected panel reports.**  For an expectation family over
per-deme haplotype laws obeying the forward moment equation on `[0, ∞)`, the expected compiled
report of an independently sampled panel at time `t ≥ 0` is the sum over panel genotypes of the
conditional readout times the seed coordinate of `e^{tQ} v(0)`. -/
theorem expectedPanelReport_eq_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (ℓ₀ : Locus)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ Fintype.card Sample),
      ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt
          (fun s ↦ expectedMomentVector (fun _ ↦ Fintype.card Sample) expectationAt s ξ)
          (expectationAt t fun law ↦
            eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
          (Set.Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) :
    (expectationAt t fun law ↦
        ((FiniteGeneticTransition.piLaw fun draw ↦ law (deme draw)).bind report).expectation
          metric)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric *
            (matrixExponential (dualGenerator rates (fun _ ↦ Fintype.card Sample)) t).mulVec
              (expectedMomentVector (fun _ ↦ Fintype.card Sample) expectationAt 0)
              (seedState deme genotype ℓ₀) := by
  have hpoint : (fun law : Deme → FiniteReportLaw (FullHaplotype Locus Allele) ↦
        ((FiniteGeneticTransition.piLaw fun draw ↦ law (deme draw)).bind report).expectation
          metric)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric •
            fun law ↦ configurationMoment law (seedConfiguration deme genotype ℓ₀) := by
    funext law
    rw [ConditionalReportCompilation.panel_compiled_expectation_eq_frequency_polynomial]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, configurationMoment_seedConfiguration]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [hpoint, ExpFunctional.eval_sum]
  simp only [ExpFunctional.smul_eval]
  rw [← expectedMomentVector_eq_matrixExponential rates _ expectationAt hforward t ht]
  rfl

end

end Descent.Portability.PartialHaplotypePanelLikelihood
