/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InfiniteGenomeRate
import Descent.Pangenome.GraphCoalescent.CompressionHiddenStateCount

namespace Descent.Program

/-!
# Research frontiers: theorems beyond the three research notes

The research notes of 11 September 2026 on exact portability laws, the pangenome hidden-lineage
clock and ancestral locality are formalized in `ExactPortabilityLaws`, `PangenomeHiddenClock` and
`AncestralLocality`. This header records theorems proved on top of them that the notes do not
state. Every module listed was checked on the pinned toolchain with axioms limited to `propext`,
`Classical.choice` and `Quot.sound`, and each module docstring carries its own Scope paragraph.

## Results

* An explicit rate for the infinite-genome limit: `InfiniteGenomeRate`. Along an exhaustion by
  balls of radius `ℓ_m`, the finite-genome semigroups converge to the infinite-genome semigroup
  within `2‖f‖ min {1, n|A| e^{DT} (2eDT/ℓ_m)^{ℓ_m}}`
  (`norm_operator_sub_infiniteGenomeSemigroup_le`), and so do sampling polynomials read through a
  finite window (`norm_windowPullback_operator_sub_infiniteGenomeSemigroup_le`).
* How much a pangenome compression hides: `CompressionHiddenStateCount`. The coarsest Markov
  refinement of the report has exactly as many states as the report when the interface is
  injective (`coarsestStateCount_eq_reportStateCount_of_injective`), and strictly more once two
  individuals share a graph state on an interface of width at least two
  (`reportStateCount_lt_coarsestStateCount`).

Scope. The rate takes the sampling duality through the truncated circuit law, and agreement of the
finite models until escape, as hypotheses. The state counts compare numbers of values of the two
statistics; the exact count as a function of the fiber sizes is not yet proved.
-/

end Descent.Program
