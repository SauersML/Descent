/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Barrier
import Descent.Pangenome.Linkage.Chain
import Descent.Pangenome.Linkage.Interface
import Descent.Pangenome.Linkage.Metadata
import Descent.Pangenome.Linkage.Splicing

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# `Linkage` -- what a pangenome graph forgets, and what that forces it to admit

Five modules.  The first four read in order, each measuring something the previous one
defined; the fifth prices the escape the third leaves open.  The group's whole analytic
content is one inequality, stated in the first module.

## The order

1. `Interface` -- one separator.  Its fibers, its occupied `width`, the `identityLoss` it
   commits (which is `H(J ∣ S)` for a uniform panel), and the split
   `H(J ∣ S) = log (m/w) + D(q ‖ u)` into a width term and an imbalance tax.  The only
   analysis in the group is `sum_mul_log_le_log_sum`, weighted Jensen for `Real.log`, proved
   from `log x ≤ x - 1`.

2. `Chain` -- the language.  The derivations a chain of separators admits, the `O(m·r)`
   dynamic program that counts them with a proof that it counts THEM, the exact product
   formula in the balanced case, and the switch grading.  One regrouping lemma,
   `sum_mosaicsFrom`, evaluates all three.

3. `Barrier` -- the theorem.  A geometric mean carried along the chain gains each
   interface's `identityLoss`, giving `log m + ∑ H(J ∣ S_j) ≤ log |Ω|` and, with the
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

## Why the group is one group

`Descent.Pangenome.GaugeInvariance` asks which statistics of a variant catalogue survive a
change of reference tree; this group asks what a graph must admit once it has merged
haplotype identity at a separator.  Both are questions about what a representation of a
panel loses, and `Splicing` states the second in the first's vocabulary rather than beside
it.

This file contains no declarations.
-/
