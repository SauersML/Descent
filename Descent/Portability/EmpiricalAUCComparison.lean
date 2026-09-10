/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Descent.Layer

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

/-!
# AUC pair comparison

The population's finite cohort evaluator and explicit finite-distribution witnesses share
this ranking credit, including the same half-credit convention for ties.
-/

/-- One case-control comparison with half credit for a predicted-risk tie. -/
noncomputable def empiricalAUCComparison (caseRisk controlRisk : ℝ) : ℝ :=
  if controlRisk < caseRisk then 1 else if caseRisk = controlRisk then 1 / 2 else 0

end Descent.Portability
