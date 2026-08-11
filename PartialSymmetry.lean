/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PartialSymmetry.FiniteGroupoidBisection
import PartialSymmetry.FiniteGroupoidCounting
import PartialSymmetry.FiniteGroupoidFunctor
import PartialSymmetry.FiniteGroupoidPresentation

/-!
# `PartialSymmetry` -- the partial-symmetry library

**Every module under `PartialSymmetry/`, and nothing else.**

A third `lean_lib`, beside `Descent` and `Counterexamples`. What separates it from the
corpus proper is subject matter, not status: these modules are general mathematics about
partial bijections, finite groupoids, and wreath products, with no genetic quantity in
them and no measurement behind them. `Descent/` states laws about the world and every one
of them answers to a simulation; nothing here does, because there is nothing here to
measure -- a groupoid either has the claimed decomposition or it does not.

The material is extracted from a separate development, `nonsofic_existence`
(github.com/SauersML/nonsofic_existence, Apache 2.0, same owner), where it was built to
serve a soficity argument. Each file carries a provenance comment naming its original
path. The namespace was renamed `NonsoficGroupsExist` -> `PartialSymmetry` on the way in,
because the name of a library should say what it contains rather than what it was once
used to disprove.

Why the corpus wants it: a family of homologous genomic copies has a symmetry object that
is not a group. Copies can be matched only partially -- a segment present in one haplotype
and absent from another admits no bijection -- and the composable partial matchings form a
groupoid, not a group. `PartialSymmetry/Wreath.lean` and the bisection decomposition make
that object concrete: internal copy states times copy exchange.

`validation/code/check.py` scans `Descent/` and does not reach here, exactly as it does not
reach `Counterexamples/`. The guards enforce properties of measured laws and none of them
should be asked to hold of a statement about finite groupoids. The style rules are
followed anyway -- lines at or under 100 columns, every declaration docstringed -- because
they are good ones and a reader crossing from `Descent/` should not notice the border.

A build that names its targets must name this one too:
  lake build Descent Counterexamples PartialSymmetry
-/
