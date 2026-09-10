/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.DGP
import Descent.Spectral.CirculationDefect

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


/-! ## Isotropic circulation: instantaneous energy and integrated correlation

The scalar formulas below concern the two-dimensional mode with generator
`L = -s I + A`, where `A = [[0,a],[-a,0]]` and `s > 0`. Its instantaneous
Dirichlet quadratic form depends on `s` and not on `a`. This statement concerns
instantaneous energy; it does not imply that finite-horizon stale-score loss
is independent of circulation.

In the normalized stationary mode, the correlation is `exp(-s*t) * cos(a*t)`.
Its one-sided integrated correlation is `s / (s^2 + a^2)`, while inverse
dissipation is `1 / s`. The unchanged historical names `apparentMixingTime`
and `frontierTime` denote these two scalar quantities. The former is not a
total-variation mixing time, and the latter is not a universal portability or
prediction frontier. At equal nonzero damping and circulation the integrated
correlation is half the inverse dissipation.

A fixed observable compared with its future value and an optimally transported
predictor define different risks. Finite-horizon stale loss can depend on
circulation even when the instantaneous Dirichlet form is unchanged. -/

section NonreversibleFlow

/-- For an isotropic damped-rotation mode, nonzero circulation makes its
one-sided integrated correlation strictly smaller than inverse dissipation.
The theorem compares the two defined scalars; it does not identify a
population-specific portability endpoint or total-variation mixing time. -/
theorem geneFlowMixingTime_understates_transferTime
    (dissipation circulation : ℝ) (hd : 0 < dissipation) (hc : circulation ≠ 0) :
    Spectral.apparentMixingTime dissipation circulation < Spectral.frontierTime dissipation :=
  Spectral.apparentMixingTime_lt_frontierTime dissipation circulation hd hc

/-- At equal damping and circulation, inverse dissipation is exactly twice
the mode's one-sided integrated correlation. The historical inflation name
refers to that scalar ratio, not to every transfer or prediction risk. -/
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
