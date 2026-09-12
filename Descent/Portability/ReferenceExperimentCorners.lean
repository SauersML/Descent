/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentTable

assert_below Descent.Decision Descent.Program

/-!
# Corner accumulators of the NOTE2 section 9 reference experiment

The corner accumulator of a report in one architecture and environment context, computed from
a tabled terminal law, and the identity that a tabled history report is the context-mass
average of its four corner accumulators. The corner certificates of both histories are decided
in `ReferenceExperimentEarlyMomentCorners`, `ReferenceExperimentEarlyLossCorners`,
`ReferenceExperimentLateMomentCorners` and `ReferenceExperimentLateLossCorners`.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentCorners

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable

/-- The corner accumulator of a report in one architecture and environment context, computed
from a tabled terminal law. -/
def tableCornerReport (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℚ :=
  ∑ atom, if atomMass context atom = 0 then 0
    else atomMass context atom * ∑ terminal, terminalTable entries context terminal *
      report context atom terminal

/-- A tabled history report is the context-mass average of its corner accumulators. -/
theorem tableReport_eq_corners (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    tableReport entries report =
      ∑ context, contextMass context * tableCornerReport entries report context := rfl

end Descent.Portability.ReferenceExperimentCorners
