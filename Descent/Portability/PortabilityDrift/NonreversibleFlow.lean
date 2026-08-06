/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift.Definitions
import Descent.Layer

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.NonreversibleFlow`

Part of the split of `Portability/PortabilityDrift.lean`, which was 9,208 lines and 555
declarations -- the largest file in the corpus by both measures, and large enough that
nothing in it could be read without reading past most of it.

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

Sections are reopened and reclosed by name where a cut falls inside one: the original
opened `section PortabilityDrift` and closed it 8,000 lines later. A section scopes
`variable`s, and this file declares none at that level, so the reopening is exact.
-/


/-! ## Nonreversible gene flow: the mixing time is not the transfer time

Everything above this point models divergence with reversible machinery — drift, symmetric
migration, coalescent times. Real gene flow is not reversible: expansions, admixture pulses and
sex-biased migration carry probability around cycles. `Descent.Spectral.CirculationDefect` separates
what that changes from what it does not.

It does not change the degradation calculus: the Dirichlet energy annihilates the circulation, so
every ordering of weighting schemes by that energy survives unchanged.

It does change what a measured mixing time means. Circulation accelerates ergodic averaging
without contributing to the frontier, so the diagnostic reports a shorter time than the one
governing transfer — at equal circulation and dissipation, half of it.

That is a third mechanism alongside the two this file carries. Allele-frequency divergence says
how far apart populations are, tagging mismatch says how much linkage structure carries over, and
this says a well-mixed-looking population can still be a bad transfer target because the rate at
which its environment forgets is not the rate at which a design degrades. -/

section NonreversibleFlow

/-- A mixing-time diagnostic understates the transfer-relevant time. Instance of
    `apparentMixingTime_lt_frontierTime`: with any cyclic component to gene flow, the time
    constant an ergodic-averaging diagnostic measures is strictly shorter than the one setting the
    transfer frontier, so substituting it into a horizon calculus overstates transportability.

    Empirical status: DERIVED; the circulation-to-dissipation ratio of a real demography is the
    unmeasured input this asks for. -/
theorem geneFlowMixingTime_understates_transferTime
    (dissipation circulation : ℝ) (hd : 0 < dissipation) (hc : circulation ≠ 0) :
    Spectral.apparentMixingTime dissipation circulation < Spectral.frontierTime dissipation :=
  Spectral.apparentMixingTime_lt_frontierTime dissipation circulation hd hc

/-- The overstatement is a factor of two at equal circulation and dissipation, and grows
    quadratically in the ratio beyond that.

    Empirical status: DERIVED. -/
theorem transferTime_doubles_at_equal_circulation (dissipation : ℝ) (hd : 0 < dissipation) :
    Spectral.frontierTime dissipation
        = Spectral.transferTimeInflation dissipation dissipation *
            Spectral.apparentMixingTime dissipation dissipation ∧
      Spectral.transferTimeInflation dissipation dissipation = 2 := by
  refine ⟨Spectral.frontierTime_eq_inflation_mul_apparent dissipation dissipation hd, ?_⟩
  unfold Spectral.transferTimeInflation
  rw [div_self (ne_of_gt hd)]
  norm_num

end NonreversibleFlow

end Descent.Portability
