/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Deficit
import Descent.Pangenome.GraphCoalescent.Visibility

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The group's statements, pinned

A theorem can be weakened without anything noticing.  Add a hypothesis, drop a factor,
turn an equality into the inequality it implies, narrow a quantifier -- the file still
compiles, every guard still passes, and the corpus now claims less than it says it does.
`validation/code/check.py --only laundering` screens the SOURCE TEXT for names that promise
more than their signature delivers, which catches the case where the name stays put; it
cannot catch a statement quietly made smaller along with everything that reads it.

This module closes that by restating each load-bearing result of the group independently and
discharging the restatement with the theorem.  Every `example` is written out from what the
result is supposed to say rather than copied from what it does say, so weakening the theorem
stops this file typechecking, and `lake build Descent` is the thing that fails.

Nothing here is new mathematics and nothing here may be cited: these are `example`s, so they
have no names and cannot become load-bearing themselves.

The two directions are pinned as a matched pair on purpose.  The group's claim is not "the
graph coalescent fails" and not "the graph coalescent is Kingman's"; it is that the FIRST
object fails and the SECOND is the repair, and a pin of either half alone would let the
other be deleted.

## Empirical status

None.  Every statement here restates one proved elsewhere in the group under the group's own
verdict: the mathematics is about a finite lattice of equivalence relations and two harmonic
sums, and no measurement bears on it.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### The identification the group exists to make

The graph's lineage count IS the interface's occupied width.  Neither of the two developments
this group joins could state this, so it is pinned first: without it every theorem below is
about an unrelated integer. -/

example {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.blocks (graphKer s) = Linkage.width s :=
  blocks_graphKer s

/-! ### The obstruction

The report is not a Markov chain, and the hypothesis is one merged pair plus one haplotype
outside it -- not a genericity condition, not a limit, and not an asymptotic. -/

example {n : ℕ} {s : Fin n → Fin n} {a b c : Fin n} (hab : a ≠ b) (hsab : s a = s b)
    (hc : s c ≠ s a) : ¬ ObservablyMarkov s :=
  not_observablyMarkov hab hsab hc

/-- Stated in the width vocabulary, so the threshold is pinned too: at least two occupied
states, and fewer than `n` of them. -/
example {n : ℕ} {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s) (hlt : Linkage.width s < n) :
    ¬ ObservablyMarkov s :=
  not_observablyMarkov_of_width_lt hw hlt

/-- The witness.  A named proposition that nothing ever establishes is an axiom with a
friendly name, and this is the theorem that stops `ObservablyMarkov` being one. -/
example {n : ℕ} {s : Fin n → Fin n} (hs : Function.Injective s) : ObservablyMarkov s :=
  observablyMarkov_of_injective hs

/-! ### The repair

The stratum is closed, the ladder on it is Kingman's unchanged, and the entrance point is the
width.  All three are needed: a stratum that leaked would not carry a process, a stratum with
its own rates would not carry a COALESCENT, and an entrance point other than `w` would make
the group's arithmetic wrong. -/

example {n : ℕ} {s : Fin n → Fin n} {ξ η : Coalescent.ER n} (h : GraphState s ξ)
    (hcov : Coalescent.Covers ξ η) : GraphState s η :=
  graphState_of_covers h hcov

example {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n} (h : GraphState s ξ) :
    (Nat.card {η : Coalescent.ER n // Coalescent.Covers ξ η} : ℝ)
      = Coalescent.deathRate (Coalescent.blocks ξ) :=
  card_covers_graphState h

example {n : ℕ} {s : Fin n → Fin n} {ξ : Coalescent.ER n} (h : GraphState s ξ) :
    Coalescent.blocks ξ ≤ Linkage.width s :=
  blocks_le_width_of_graphState h

/-- The entrance point as a RATE, through the corpus's own pair count.  Pinned separately
from the block count because the two say different things: one is how many lineages the
graph hands the process, the other is how fast the process then runs. -/
example {n : ℕ} (s : Fin n → Fin n) :
    Coalescent.deathRate (Coalescent.blocks (graphKer s))
      = Descent.Core.pairCount (Linkage.width s) :=
  deathRate_blocks_graphKer s

/-- K-G (5.7) at the graph's own sample size.  An EQUALITY, not the bound it implies. -/
example {n : ℕ} {s : Fin n → Fin n} (hw : 1 ≤ Linkage.width s) :
    graphMeanTransitTime s = 2 - 2 / (Linkage.width s : ℝ) :=
  graphMeanTransitTime_eq hw

/-! ### The price

The deficit is exact, it is signed, and it vanishes exactly with the identity loss.  The last
of these is the group's bridge between an entropy and a time, and it is pinned as an `↔` so
that neither implication can be dropped. -/

example {n : ℕ} {s : Fin n → Fin n} (hn : 1 ≤ n) (hw : 1 ≤ Linkage.width s) :
    transitDeficit s = 2 / (Linkage.width s : ℝ) - 2 / (n : ℝ) :=
  transitDeficit_eq hn hw

example {n : ℕ} {s : Fin n → Fin n} (hw : 1 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) : 0 < transitDeficit s :=
  transitDeficit_pos hw hlt

example {n : ℕ} {s : Fin n → Fin n} (hn : 0 < n) :
    transitDeficit s = 0 ↔ Linkage.identityLoss s = 0 :=
  transitDeficit_eq_zero_iff hn

/-! ### The estimator

The reported `θ` and its bias.  The equality pins the factor `a_{w-1} / a_{n-1}` -- both
indices, in that order -- and the strict inequality pins the direction. -/

example {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    graphWatterson θ s = θ.value *
      (Coalescent.harmonicSum (Linkage.width s - 1) / Coalescent.harmonicSum (n - 1)) :=
  graphWatterson_eq θ s

example {n : ℕ} {θ : Descent.Core.Theta} (hθ : 0 < θ.value) {s : Fin n → Fin n}
    (hw : 2 ≤ Linkage.width s) (hlt : Linkage.width s < n) : graphWatterson θ s < θ.value :=
  graphWatterson_lt hθ hw hlt

/-- And the complementary positive result, so that the bias is pinned as a property of the
compression rather than of the estimator. -/
example {n : ℕ} (θ : Descent.Core.Theta) {s : Fin n → Fin n} (hn : 2 ≤ n)
    (h : Linkage.width s = n) : graphWatterson θ s = θ.value :=
  graphWatterson_of_width_eq θ hn h

end Descent.Pangenome.GraphCoalescent
