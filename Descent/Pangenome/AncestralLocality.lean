/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.ClosureReachability
import Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.JointNonautonomy
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityTransition
import Descent.Pangenome.AncestralLocality.SupercriticalReach

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

3. `SupercriticalReach` -- (6.2) conditional on the Erdős–Rényi theorem: probabilities under
   `G(m, p)`, the tie-free giant-component event, `GiantComponentLaw` carrying the classical
   theorem with its subcritical half proved from (6.1) (witness `giantComponentLaw_half`), and the
   support of the limit law: the reach fraction concentrates near `0` or near `giantFraction α`.

3. `InfiniteGenomeLimit` -- the operator half of Theorem 9 on any compact space with a separating
   subalgebra: Feller semigroups along an exhaustion that obey the light-cone approximation bound
   converge on every observable, the limit is a Feller semigroup with strong continuity at every
   time, and two Feller semigroups agreeing on the subalgebra agree, so the limit does not depend
   on the exhaustion.

4. `LocalityBounds` -- Theorems 7 and 8 and Corollary 8.1: a decision raises the weighted
   support count by at most `w i + 2 w j` and a coalescence does not raise it, so
   `L_anc Z ≤ 3 D Z` and, with light-cone weights, `L_anc Z^{(a)} ≤ D (1 + 2a) Z^{(a)}`. Along
   marginal laws satisfying the Dynkin formula these give (8.2), (8.3) and the escape bound
   (9.1), with the radius identity behind (9.2); outcomes equal off an event are within its
   probability in total variation.

5. `JointNonautonomy` -- §3.2: two observations can each be autonomous while their joint
   observation is not. Under the witness rule of §5.2 the features `a` and `b` each have the
   neutral observed kernel of Theorem 3, and their joint observation `(a, b)` has no kernel.

6. `ClosureReachability` -- Theorem 4 and §5.1: for `|A| ≥ 2` one hereditary refinement step
   of the checking kernel turns `P_{π_A}` into `P_{π_{A ∪ N⁺_G(A)}}` (5.2), through the
   difference formula (5.3); iterating gives `P_{π_{Reach_G(A)}}` (5.1), and singletons and the
   empty observation are their own closure. On a connected undirected graph, the path included,
   every query on two or more features closes to the whole genome, and a pair observation with
   an outside checker is not autonomous (5.4). The kernels and `Φ_K` are local transcriptions
   until the heredity layer can be imported.

This file contains no declarations.
-/
