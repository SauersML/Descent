/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Deficit
import Descent.Pangenome.GraphCoalescent.EstimatorSign
import Descent.Pangenome.GraphCoalescent.MergerDepth
import Descent.Pangenome.GraphCoalescent.Observation
import Descent.Pangenome.GraphCoalescent.Pinned
import Descent.Pangenome.GraphCoalescent.Reduction
import Descent.Pangenome.GraphCoalescent.Visibility
import Descent.Pangenome.GraphCoalescent.WidthProfile

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# `GraphCoalescent` -- the ancestral process a pangenome graph can actually observe

Five modules.  Two of them are the derivation, one is its price, one is the obstruction that
makes the derivation necessary, and one checks the other four.

The question is short.  A pangenome graph is built from a panel, and building it merges
haplotypes: at an interface `s` two threads occupying the same graph state are one object to
the graph (`Descent.Pangenome.Linkage.Interface`).  Kingman's coalescent is a Markov chain on
the equivalence relations of the SAMPLE (`Descent.Coalescent.StateSpace`).  What process does
the graph see?

## The answer, in one line

A pangenome graph does not observe a coalescent of the panel's `n` haplotypes.  It observes a
Kingman coalescent of its own `Linkage.width s` nodes, and the naive object -- the panel's
coalescent read off the graph -- is not a Markov chain at all.

## The order

1. `Observation` -- the report.  `observed s ξ = ξ ⊔ graphKer s`, the coarsest thing a graph
   at interface `s` can say about a coalescent state, which is forced rather than chosen: a
   report must be an equivalence relation, must contain what has coalesced, and must contain
   what the builder merged.  The one identification the group exists to make is here:
   `blocks_graphKer` says the graph's lineage count IS the interface's occupied width.  The
   coalescent half of the corpus has no interfaces and the linkage half has no lineages, so
   neither could have stated it.

2. `Visibility` -- the obstruction.  Rosenblatt's criterion, K-G (5.1) -- the criterion
   `Descent.Coalescent.Lumping` uses to derive the block-count death process -- FAILS for the
   report.  The reason is exact and needs no genericity: `⊥` and `graphKer s` have the same
   report, but from `⊥` two distinct coalescences look alike (merge `a` with `c`, merge `b`
   with `c`, where the interface already merged `a` with `b`) and from `graphKer s` none do.
   The next step depends on how many un-coalesced lineages hide behind a node, which is
   precisely what the graph deleted, and a process whose rates depend on deleted information
   has no rates.

3. `Reduction` -- the repair.  The obstruction lives entirely below `graphKer s`.  On the
   up-set at or above it the report is the identity, the stratum is closed under coalescence,
   and the transition counts are `Descent.Coalescent.StateSpace.card_covers` unchanged -- so
   Kingman's ladder `d_k = k(k-1)/2` applies verbatim.  Nothing is postulated and nothing is
   weakened; what changes is the entrance point, which is `w` and not `n`.

4. `Deficit` -- the price.  `E(T_n) - E(T_w) = 2/w - 2/n`, and `transitDeficit_eq_zero_iff`
   is the group's bridge: that time deficit vanishes exactly when
   `Descent.Pangenome.Linkage.Interface`'s `identityLoss` does.  An entropy in nats and a
   time in coalescent units vanish together because both are read off the same `w`.  Then the
   estimator: a study reading its segregating sites off the graph and its sample size off the
   panel reports `θ · a_{w-1} / a_{n-1}`, strictly below `θ`.

5. `Pinned` -- the check.  Each load-bearing result restated independently and discharged by
   the theorem, so that weakening one stops `lake build Descent` rather than passing every
   guard silently.  It declares nothing and may not be cited.

## Why this is not a second gauge theorem

`Descent.Pangenome.CoalescentGauge` shows that `θ_W` moves with the choice of reference tree,
because `S` counts cotree edges and the tree is a gauge.  That defect is in the NUMERATOR of
Watterson's estimator.  The one here is in the DENOMINATOR: `a_{n-1}` is evaluated at a
sample size the graph does not have.  The two are independent, they have opposite
sensitivities, and a study carrying both has no reason to expect them to cancel.  Naming that
is the reason `Deficit` states the estimator result rather than stopping at the transit time.

## What of the surrounding theory is not here

Stated so the group does not read as complete.  Not formalised: the multi-interface case, in
which each of a chain's separators contributes its own entrance point and the marginal
genealogies along the chain are correlated by recombination -- `Descent.Pangenome.Linkage.Chain`
has the chain and `Descent.Coalescent.Recombination` has the correlation, and joining them is
the natural next module.  Not formalised: the exact per-report transition COUNT from `⊥`,
which is `c_A · c_B` in the fiber sizes of the two states merged; `Visibility` proves the
count is at least two, which is all the obstruction needs, and the exact count would need a
finiteness instance on `𝓔ₙ` that the corpus does not carry.  Not formalised: the variance of
the graph coalescent's transit time, and the site-frequency spectrum at `w`.

## The premise the group carries

Nothing here needs `[Nonempty (Fin n)]` as an instance, because the panel size appears as an
explicit `n` and the nondegeneracy is stated where it is used -- `1 ≤ Linkage.width s`, or
`0 < n`, as a hypothesis with a name.  That is a deliberate difference from
`Descent.Pangenome.Linkage`, whose eighty-odd instance premises `--only laundering` records
as hidden; here there was no reason to hide them.

This file contains no declarations.
-/
