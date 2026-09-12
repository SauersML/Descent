/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionClockPathLaw
import Descent.Pangenome.GraphCoalescent.FirstConnectionLaw
import Descent.Pangenome.GraphCoalescent.ReportedConnectionFirstStep

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# One connection clock, three constructions

Three modules of this group build the reported connection clock of §6 of the pangenome
hidden-clock note, each from a different object.

* `ReportedConnectionClock` reads the stopping level `B` off a jump-chain trajectory and pairs
  the trajectory with an independent Kingman clock, `trajectoryClockLaw n`; its `connectedProb`
  and `stoppingProb` are `F_k` and `p_b`.
* `FirstConnectionLaw` computes `F_k` as `reportConnectedProbability` against the indicator of a
  connected report, and `p_b` as `firstConnectionProbability` from two consecutive levels of the
  chain.
* `ConnectionClockPathLaw` builds the law `connectionTimeLaw s ξ` of the connection time by
  first-step recursion, holding time convolved with the mixture over the first jump.

This file says they agree.  `connectedProb_eq_reportConnectedProbability` and
`stoppingProb_eq_firstConnectionProbability` identify the two versions of (D5) and (D6).
`connectionTime_mean_eq_lintegral_connectionTimeLaw` identifies the means of the two laws at the
entrance state `⊥`, through `ReportedConnectionFirstStep.connectionTime_mean_eq_meanConnectionTime`
and `ConnectionClockPathLaw.lintegral_coe_connectionTimeLaw`.  The two laws themselves are not
identified here, only their means.

## Empirical status

None.  Every declaration is an identity between definitions of the group, finite sums and lower
integrals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent MeasureTheory
open scoped Classical ENNReal NNReal

/-- **The two versions of `F_k` agree**: the filtered sum of the head law and its integral
against the indicator of a connected report. -/
theorem connectedProb_eq_reportConnectedProbability {n : ℕ} (s : Fin n → Fin n) (k : ℕ) :
    connectedProb s k = reportConnectedProbability s k := by
  unfold connectedProb reportConnectedProbability
  rw [sum_filter]
  refine sum_congr rfl fun π _ ↦ ?_
  split_ifs <;> simp

/-- **The two versions of `p_b` agree**: the stopping level of a trajectory and the first
connection between consecutive levels have the same law, `F_b - F_{b+1}`. -/
theorem stoppingProb_eq_firstConnectionProbability {n b : ℕ} (s : Fin n → Fin n) (hb : 1 ≤ b)
    (hbn : b < n) : stoppingProb s b = firstConnectionProbability s b := by
  rw [stoppingProb_eq s hb hbn, firstConnectionProbability_eq_sub s hb hbn,
    connectedProb_eq_reportConnectedProbability, connectedProb_eq_reportConnectedProbability]

/-- **The path law and the first-step law have the same mean.**  The expectation of the
connection time under the trajectory-and-clock law of `ReportedConnectionClock` is the mean of
`ConnectionClockPathLaw.connectionTimeLaw s ⊥`. -/
theorem connectionTime_mean_eq_lintegral_connectionTimeLaw {n : ℕ} (hn : 2 ≤ n)
    (s : Fin n → Fin n) :
    ∫⁻ p, ENNReal.ofReal (connectionTime s p) ∂(trajectoryClockLaw n)
      = ∫⁻ x, (x : ℝ≥0∞) ∂(connectionTimeLaw s ⊥) := by
  rw [connectionTime_mean_eq_meanConnectionTime hn s, lintegral_coe_connectionTimeLaw]

end Descent.Pangenome.GraphCoalescent
