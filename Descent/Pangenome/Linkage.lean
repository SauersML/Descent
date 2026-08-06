/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Barrier
import Descent.Pangenome.Linkage.Chain
import Descent.Pangenome.Linkage.Frequency
import Descent.Pangenome.Linkage.Interface
import Descent.Pangenome.Linkage.Metadata
import Descent.Pangenome.Linkage.Pinned
import Descent.Pangenome.Linkage.Splicing
import Descent.Pangenome.Linkage.Tree

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# `Linkage` -- what a pangenome graph forgets, and what that forces it to admit

Seven modules of mathematics and one that checks them.  The group's whole convexity content
is one inequality, stated in the first.

The import order is `Interface`, `Chain`, `Frequency`, `Barrier`, then `Splicing`,
`Metadata`, `Tree` and `Pinned` in any order.  `Frequency` sits where it does because `Barrier`'s
uniform statement is DERIVED from its weighted one rather than proved beside it; the list
below is a reading order, and takes the headline uniform case first.

## The order

1. `Interface` -- one separator.  Its fibers, its occupied `width`, the `identityLoss` it
   commits (which is `H(J ∣ S)` for a uniform panel), and the split
   `H(J ∣ S) = log (m/w) + D(q ‖ u)` into a width term and an imbalance tax.  The only
   convexity in the group is `sum_mul_log_le_log_sum`, weighted Jensen for `Real.log`, proved
   from `log x ≤ x - 1`; monotonicity of `log` is used besides it, to clear logarithms, and
   nothing else analytic is.

2. `Chain` -- the language.  The derivations a chain of separators admits, the `O(m·r)`
   dynamic program that counts them with a proof that it counts THEM, the exact product
   formula in the balanced case, and the switch grading.  One regrouping lemma,
   `sum_mosaicsFrom`, evaluates all three.

3. `Barrier` -- the theorem.  A geometric mean carried along the chain gains each
   interface's `identityLoss` — by `Frequency`'s weighted step at the uniform law, not by a
   second argument — giving `log m + ∑ H(J ∣ S_j) ≤ log |Ω|` and, with the
   logarithms cleared, `m ^ (r+1) ≤ (∏ w_j) · |Ω|` between natural numbers.  The balanced
   count of `Chain` attains it, so it is exact.  Two consequences: an exact topology-only
   representation cannot merge identity at any linkage-bearing separator, and the phantom
   derivations the width budget forces are counted.

4. `Splicing` -- the transfer.  Blocks that identify their donor make the derivation count a
   count of distinct sequences; a biallelic single-SNP block system already does.  The walk
   form of a splice is stated in the vocabulary of `Descent.Pangenome.Gauge`, so the
   quantity the barrier forces to exist is one that survives a change of reference tree.

5. `Metadata` -- the third option.  `Barrier` leaves an interface able to merge identity and
   keep the missing distinction outside the topology, which is what every haplotype-aware
   index does.  `card_le_width_mul_card_aux` prices it: an exact controller at an interface
   of width `w` needs an auxiliary alphabet of at least `m / w`.  That is the same `m / w`
   the width law charges in derivations, so the two options are one trade rather than an
   escape.

6. `Tree` -- the generality.  Nothing in the argument used the chain.  The same law holds on
   any tree of modules whose edges carry unrelated equivalence relations on the panel, with
   `log m + ∑ H(J ∣ S_e) ≤ log |Ω|` summed over every edge, and balance extremal there too.
   `chainArbor` embeds a chain and the specialisation theorems say every quantity agrees, so
   this is where the result stops being about pangenomes and becomes a counting inequality
   about edge-coloured trees.

7. `Frequency` -- the weighting, and what the uniform statement rests on.  The law holds for any
   strictly positive frequency law `p`, as `H(p) + ∑_j H_p(J ∣ S_j) ≤ log |Ω|`.  A builder
   measuring what a graph forgets about a population uses the population's law, not the
   counting measure on whichever haplotypes were sampled.  `condIdentityLoss_uniform` and
   `panelEntropy_uniform` identify the uniform quantities with the weighted ones at
   `p = 1/m`, which is what lets `Barrier` take its step from here instead of repeating it.

8. `Pinned` -- the check.  Each load-bearing result above, restated independently and
   discharged by the theorem, so that weakening one stops `lake build Descent` rather than
   passing every guard silently.  It declares nothing and may not be cited.

## What of the manuscript is not here

Stated so the group does not read as complete.  Not formalised: the exact variational
(Bethe) formula and the frequency-aware capacity that maximises the bound, with its unique
interior optimiser and fixed-point equation; the random-merger expectations over hashed or
uniformly-drawn surjective state maps; the total-width arithmetic-geometric budget, of which
the max-width form `pow_card_le_pow_width_mul_card_mosaics` is proved instead; the entropy
form of the metadata bound and its Fano version, of which the zero-error cardinality form is
proved instead; the layered DAG whose paths are exactly the compatible splices, of which the
counting half is proved; and the invariance of the tree count under re-rooting.

## Why the group is one group

`Descent.Pangenome.GaugeInvariance` asks which statistics of a variant catalogue survive a
change of reference tree; this group asks what a graph must admit once it has merged
haplotype identity at a separator.  Both are questions about what a representation of a
panel loses, and `Splicing` states the second in the first's vocabulary rather than beside
it.

This file contains no declarations.
-/
