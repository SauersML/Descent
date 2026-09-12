/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityCoupling

namespace Descent.Program

/-!
# Ancestral locality

Reference: the research note of 11 September 2026, "Ancestral locality: a heredity-first
foundation for pangenomic population theory", against this archive. Theorem and equation numbers
below are the note's own. Every module listed was checked on the pinned toolchain with axioms
limited to `propext`, `Classical.choice` and `Quot.sound`. Where a statement is proved in a
narrower form, the scope line says so and the module docstring repeats it.

## The object

The hereditary closure of an observation is the least additional genomic information that makes
the observation reproductively autonomous. In the neutral compatibility-copying model it is graph
reachability, so it undergoes a percolation transition while every single feature keeps the
ordinary Wright-Fisher law; a support-aware ancestral decision circuit gives genome-size
independent complexity bounds and a quantitative light cone.

## Theorems

* Corollary 8.1, the light cone as a coupling: `LocalityCoupling`. Two sample laws obtained by
  evaluating one circuit on inputs that coincide off an escape event are within total variation
  the probability of escape (`totalVariation_mixtureLaw_le`); for a circuit reading only inspected
  coordinates on inputs agreeing on a ball, this is (9.3) (`totalVariation_local_le`). The
  support-tag circuit truncated to the induced checking graph on a ball keeps the internal rates
  unchanged (`truncatedRate_of_mem`) and coincides with the full circuit along every run with no
  outside-checking event (`runCircuit_truncatedStep_eq`, `totalVariation_truncated_le`). §9.1:
  `20 e³ ∈ [401.7, 401.72]` (`twenty_mul_exp_three_mem_Icc`) and
  `20 e (2e/20)^20 ≤ 2.64 × 10⁻¹⁰` (`escapeBound_twenty_le`).

Scope. Corollary 8.1 is stated on a common finite probability space, with the escape probability
as a parameter until the escape bound of Theorem 8 is proof-checked. Theorems 1 and 2 (hereditary
closure and its operational characterization), Theorem 3 (neutrality), Theorem 4 (closure is
reachability), Theorem 5 (the locality transition), Theorem 6 (sampling duality), Theorems 7 and 8
(support and escape bounds) and Theorem 9 (the infinite-genome semigroup) are not yet
proof-checked.
-/

end Descent.Program
