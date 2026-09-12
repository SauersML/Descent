/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralIntegrableRateRealization
import Descent.Portability.CaratheodoryFundamentalMatrix

assert_below Descent.Decision Descent.Program

/-!
# The Carathéodory propagator of an integrable neutral rate history

`CaratheodoryFundamentalMatrix` builds the fundamental matrix of an integrable generator path as a
continuous solution of its integral equation. This module applies it to the partial-haplotype dual
generator of NOTE1 (20) along a rate history with integrable rate coordinates, whose generator path
is integrable by `NeutralIntegrableRateRealization.intervalIntegrable_dualGenerator`.

By `NeutralIntegrableRateRealization.neutralIntegrablePropagator_mulVec_mem_realizationBody`, which
holds for every continuous solution of the integral equation, the Carathéodory propagator at the
horizon carries the budget moments of every frequency state into the realization body of the
budget-moment feature (`caratheodoryFundamentalMatrix_dualGenerator_mulVec_mem_realizationBody`),
and a finitely supported probability law on frequency states realizes them
(`exists_caratheodoryDualLaw`).

Scope. The hypothesis is that of `NeutralIntegrableRateRealization`: interval integrability of the
rate coordinates on `[0, T]`. The Markov-kernel limit of the history is not constructed here.

## Empirical status

None. The bodies apply membership in a closed convex set to a solution of an integral equation, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralCaratheodoryRealization

open MeasureTheory Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator PartialHaplotypeMicroscopicApproximation PartialHaplotypePanelLikelihood
  FiniteMixtureKernel RealizationBody KernelRealizationPreservation
  NeutralMicroscopicEulerLimit NeutralKernelPanelLikelihood NeutralHistoryKernel
  NeutralRateLipschitz NeutralIntegrableRateRealization CaratheodoryFundamentalMatrix
open scoped Matrix Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The Carathéodory propagator of an integrable rate history keeps moment vectors realizable.**
For a rate history whose rate coordinates are integrable on `[0, T]`, the Carathéodory fundamental
matrix of its dual generator path, at the horizon, carries the budget moments of every frequency
state into the realization body of the budget-moment feature. -/
theorem caratheodoryFundamentalMatrix_dualGenerator_mulVec_mem_realizationBody
    (rates : ℝ → NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (x0 : FrequencyState Deme Locus Allele) :
    caratheodoryFundamentalMatrix (fun t ↦ dualGenerator (rates t) capacity) hT
        (intervalIntegrable_dualGenerator capacity hintegrable) T
          *ᵥ budgetMomentFeature capacity x0
      ∈ realizationBody
        (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity) := by
  have hgenerator := intervalIntegrable_dualGenerator capacity hintegrable
  exact neutralIntegrablePropagator_mulVec_mem_realizationBody rates capacity hT hintegrable
    (continuous_caratheodoryFundamentalMatrix hT hgenerator)
    (caratheodoryFundamentalMatrix_eq_integral hT hgenerator) x0

/-- **A realizing law for the Carathéodory propagator.** At every initial state there is a finitely
supported probability law on frequency states whose budget-respecting configuration moments are
`U(T) H(x₀)`, for `U` the Carathéodory fundamental matrix of the dual generator path of a rate
history with integrable rate coordinates. -/
theorem exists_caratheodoryDualLaw (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    (x0 : FrequencyState Deme Locus Allele) :
    ∃ w : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ,
      ∃ point : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele,
        (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1
          ∧ featureVector w point (budgetMomentFeature capacity)
            = caratheodoryFundamentalMatrix (fun t ↦ dualGenerator (rates t) capacity) hT
                (intervalIntegrable_dualGenerator capacity hintegrable) T
              *ᵥ budgetMomentFeature capacity x0 :=
  exists_law_of_mem_realizationBody _ _
    (caratheodoryFundamentalMatrix_dualGenerator_mulVec_mem_realizationBody rates capacity hT
      hintegrable x0)

end

end Descent.Portability.NeutralCaratheodoryRealization
