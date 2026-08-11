/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.HaplotypeGluing

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent.Pangenome.HaplotypeGluing

/-!
# The gluing residual at three loci

`HaplotypeGluing.probabilisticGluingResidual` is the obstruction to assembling a joint mass
from two marginals, and `binaryGluingResidual_eq_tableDeterminant` identifies it with
classical two-locus `D`. At three loci the analogous obstruction is not the same expression
with a third factor appended: a triple can fail to be predictable from its singletons while
every pair is perfectly predictable from its own singletons, and it can also fail for the
uninteresting reason that a pair already failed. Separating those is the whole content of
third order.

## The two forms, and why their agreement is the point

`tripleGluingResidual` is the closed form — the joint mass, less each way of gluing it from
a pair and the remaining singleton, plus twice the all-singleton product, which corrects for
having subtracted that product three times over.

`bennettThreeLocus` is the recursive form: subtract from the joint mass each singleton times
the PAIRWISE residual of the other two, and then the all-singleton product. It is the form a
geneticist writes, because it says explicitly that the third-order term is what survives
after the second-order terms have been accounted for.

`tripleGluingResidual_eq_bennettThreeLocus` proves they are equal. That equality is Möbius
inversion on the partition lattice of a three-element set, specialized and discharged by
`ring`: the closed form is the Möbius sum over partitions and the recursive form is the
inversion, and at three elements the lattice is small enough that the identity is an
algebraic one rather than a structural theorem.

## What pins it down

Two degeneracies fix the normalization, and both are proved rather than assumed.
`tripleGluingResidual_of_independent` gives zero when all three loci are independent, which
is the least a disequilibrium may do. `tripleGluingResidual_of_sure_third` gives zero when
the third locus is certain — a constant carries no information, so a genuine third-order
term must vanish on it, and an expression that did not would be measuring a pair twice.
`tripleGluingResidual_swap_first_two` records that the residual does not privilege an
ordering of the loci.

## Arbitrary order: named, not claimed

The general statement is that the order-`k` residual is the Möbius sum over the partition
lattice of a `k`-element set, with weight `(-1) ^ (|π| - 1) * (|π| - 1)!` on a partition into
`|π|` blocks — the `2` above being that weight at `k = 3`, where the all-singleton partition
has three blocks. This file does not prove that, and does not assert that the tools are
missing: Mathlib carries both `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra` and
`Mathlib.Order.Partition.Finpartition`, so the general case is a question of whether that
Möbius function has been evaluated on the partition lattice in a usable form, which has not
been checked here. What is claimed is only what is proved: the degree-three case, in two
forms, with its degeneracies.
-/

/-- **The third-order gluing residual, in closed form.** The joint mass of three loci, less
each way of gluing it from one pair and the remaining singleton, plus twice the
all-singleton product. -/
noncomputable def tripleGluingResidual
    (triple pairAB pairAC pairBC singleA singleB singleC : ℝ) : ℝ :=
  triple - singleA * pairBC - singleB * pairAC - singleC * pairAB
    + 2 * (singleA * singleB * singleC)

/-- **The third-order residual in recursive form.** Each singleton times the PAIRWISE
residual of the other two is removed, then the all-singleton product. This is the form that
says in its own syntax that third order is what survives second order. -/
noncomputable def bennettThreeLocus
    (triple pairAB pairAC pairBC singleA singleB singleC : ℝ) : ℝ :=
  triple - singleA * probabilisticGluingResidual pairBC singleB singleC
    - singleB * probabilisticGluingResidual pairAC singleA singleC
    - singleC * probabilisticGluingResidual pairAB singleA singleB
    - singleA * singleB * singleC

/-- **The closed form and the recursive form agree.** Möbius inversion on the partition
lattice of a three-element set, at a size where it is an algebraic identity. The pairwise
residuals appearing on one side are exactly `probabilisticGluingResidual`, so third order is
built from second order rather than beside it. -/
theorem tripleGluingResidual_eq_bennettThreeLocus
    (triple pairAB pairAC pairBC singleA singleB singleC : ℝ) :
    tripleGluingResidual triple pairAB pairAC pairBC singleA singleB singleC =
      bennettThreeLocus triple pairAB pairAC pairBC singleA singleB singleC := by
  unfold tripleGluingResidual bennettThreeLocus probabilisticGluingResidual
  ring

/-- **Three independent loci carry no third-order disequilibrium.** -/
theorem tripleGluingResidual_of_independent (singleA singleB singleC : ℝ) :
    tripleGluingResidual (singleA * singleB * singleC) (singleA * singleB)
      (singleA * singleC) (singleB * singleC) singleA singleB singleC = 0 := by
  unfold tripleGluingResidual
  ring

/-- **A certain locus carries no third-order disequilibrium.** With the third locus sure,
every mass involving it reduces to the mass of the rest, and the residual vanishes
identically — including when the remaining pair is in disequilibrium. An expression that did
not vanish here would be reporting a pairwise term as a triple one. -/
theorem tripleGluingResidual_of_sure_third (pairAB singleA singleB : ℝ) :
    tripleGluingResidual pairAB pairAB singleA singleB singleA singleB 1 = 0 := by
  unfold tripleGluingResidual
  ring

/-- The residual does not privilege an ordering of the three loci. -/
theorem tripleGluingResidual_swap_first_two
    (triple pairAB pairAC pairBC singleA singleB singleC : ℝ) :
    tripleGluingResidual triple pairAB pairBC pairAC singleB singleA singleC =
      tripleGluingResidual triple pairAB pairAC pairBC singleA singleB singleC := by
  unfold tripleGluingResidual
  ring

end Descent.Pangenome.HaplotypeGluing
