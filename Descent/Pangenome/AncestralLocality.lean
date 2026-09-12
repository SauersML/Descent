/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.LocalityTransition

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# `AncestralLocality` -- heredity-first closure of pangenomic observations

The layer head for the research note "Ancestral locality" of 11 September 2026, transcribed as
`ANCESTRAL_LOCALITY.md`. A module of the group is imported here once its proof check has passed
on the bytes on main.

1. `CompatibilityNeutrality` -- the checked-exchange model of §4: ordered children, exchange
   kernels and the compatibility kernel `K_G`; Theorem 3, that every single feature is exactly
   neutral; the finite-population law with its exact binomial count law (§4.1); and the
   eight-state witness of §5.2, two populations with one observed law and two next-generation
   observed laws.

2. `LocalityTransition` -- Theorem 5 and §6.1 in the finite: the law of `G(m, p)` on edge sets,
   the simple-path bound (6.1) `E|Reach(A)| ≤ |A|/(1 - α)` for `0 ≤ α < 1`, the degree-normalized
   rates with `sup_i Σ_j r_ij ≤ β` for every graph, and the unique root `giantFraction α` in
   `(0, 1)` of `s = 1 - e^{-α s}` for `α > 1`.

3. `InfiniteGenomeLimit` -- the operator half of Theorem 9 on any compact space with a separating
   subalgebra: Feller semigroups along an exhaustion that obey the light-cone approximation bound
   converge on every observable, the limit is a Feller semigroup with strong continuity at every
   time, and two Feller semigroups agreeing on the subalgebra agree, so the limit does not depend
   on the exhaustion.

This file contains no declarations.
-/
