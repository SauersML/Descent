/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling
import Descent.Pangenome.GaugeInvariance

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

open Descent.Pangenome

/-!
# Gauge freedom is an observational symmetry

`Descent.Pangenome.GaugeInvariance` classifies which functionals of a pangenome variant
catalogue survive a change of reference tree: exactly those whose definition never mentions
one. `Descent.Blindness.ObservationalCeiling` says what a transformation the observation
cannot see costs: every property it moves becomes undecidable from that observation. This
file is the one theorem joining them.

The parameter here is the **choice of reference tree** — the gauge. A gauge-invariant
statistic is an observation that cannot see which gauge was chosen; a gauge-dependent
quantity is a target the choice moves. `observationalSymmetry_of_gaugeInvariant` packages
that pair as an `ObservationalSymmetry`, and everything downstream —
`ObservationalSymmetry.no_target_criterion`, `not_identifiedBy_of_observationalSymmetry` —
applies without further argument.

The consequence for the corpus is `segregatingCount_not_identifiedBy_totalWalkDist`:
Watterson's `S` is not a function of sequence-level diversity, and no procedure reading
sequence-level diversity recovers it. That is not a statement about estimator quality. The
two are different functions of the pangenome, and the witness that they are is the
triallelic site of `Descent.Pangenome.GaugeCounterexample`, whose `S` is `1` under one
spanning tree and `2` under another while every walk-level statistic is unmoved.
-/

/-- **A gauge-invariant observation with a gauge-dependent target is an observational
symmetry.** The transformation is the constant map to the other tree, which is legitimate
precisely because the observation cannot see any tree: invariance under *every* change of
gauge is what `Descent.Pangenome.Gauge.GaugeInvariant` asserts, and it is what the
structure's universal field demands. -/
def observationalSymmetry_of_gaugeInvariant {Edge : Type*} {Observable Quantity : Type*}
    (observation : Gauge.Tree Edge → List (Gauge.Walk Edge) → Observable)
    (quantity : Gauge.Tree Edge → List (Gauge.Walk Edge) → Quantity)
    (hinvariant : Gauge.GaugeInvariant observation)
    (sample : List (Gauge.Walk Edge)) (baseTree otherTree : Gauge.Tree Edge)
    (hmoved : quantity otherTree sample ≠ quantity baseTree sample) :
    ObservationalSymmetry (fun tree ↦ observation tree sample)
      (fun tree ↦ quantity tree sample) where
  transform := fun _tree ↦ otherTree
  observation_invariant := fun tree ↦ hinvariant otherTree tree sample
  moved := baseTree
  target_moved := hmoved

/-- **A gauge-dependent quantity is not identified by any gauge-invariant observation.**
The general statement, for any pair of functionals separated by one sample and two trees. -/
theorem not_identifiedBy_of_gaugeDependent {Edge : Type*} {Observable Quantity : Type*}
    (observation : Gauge.Tree Edge → List (Gauge.Walk Edge) → Observable)
    (quantity : Gauge.Tree Edge → List (Gauge.Walk Edge) → Quantity)
    (hinvariant : Gauge.GaugeInvariant observation)
    (sample : List (Gauge.Walk Edge)) (baseTree otherTree : Gauge.Tree Edge)
    (hmoved : quantity otherTree sample ≠ quantity baseTree sample) :
    ¬ Core.IdentifiedBy (fun tree ↦ observation tree sample) (fun tree ↦ quantity tree sample) :=
  not_identifiedBy_of_observationalSymmetry
    (observationalSymmetry_of_gaugeInvariant observation quantity hinvariant sample
      baseTree otherTree hmoved)

/-- The triallelic witness as a symmetry: sequence-level diversity is the observation,
Watterson's `S` is the target, and the two spanning trees of
`Descent.Pangenome.GaugeCounterexample` are the parameter and its image. -/
def segregatingCountGaugeSymmetry :
    ObservationalSymmetry
      (fun _tree : Gauge.Tree Allele ↦ Gauge.totalWalkDist allEdges Gauge.sampleSub)
      (fun tree : Gauge.Tree Allele ↦
        Gauge.segregatingCount allEdges tree Gauge.sampleSub) :=
  observationalSymmetry_of_gaugeInvariant
    (fun _tree sample ↦ Gauge.totalWalkDist allEdges sample)
    (fun tree sample ↦ Gauge.segregatingCount allEdges tree sample)
    (Gauge.totalWalkDist_gaugeInvariant allEdges) Gauge.sampleSub
    (Gauge.treeOf Allele.A) (Gauge.treeOf Allele.G)
    (by decide)

/-- **What the symmetry moves, in numbers.** Its parameter is the tree keeping the majority
allele, where `S = 1`; its image is the tree keeping the allele no sampled walk carries,
where `S = 2`. The observation is the same number at both, so the gap between one and two is
exactly what no reading of sequence-level diversity can recover. -/
theorem segregatingCountGaugeSymmetry_moves_segregatingCount :
    Gauge.segregatingCount allEdges segregatingCountGaugeSymmetry.moved Gauge.sampleSub = 1
      ∧ Gauge.segregatingCount allEdges
          (segregatingCountGaugeSymmetry.transform segregatingCountGaugeSymmetry.moved)
          Gauge.sampleSub = 2 :=
  ⟨rfl, rfl⟩

/-- **Watterson's `S` is not identified by sequence-level diversity.** Not poorly estimated
by it: not a function of it. The subsample of the triallelic site carries one value of the
walk-level statistic and two values of `S`. -/
theorem segregatingCount_not_identifiedBy_totalWalkDist :
    ¬ Core.IdentifiedBy
      (fun _tree : Gauge.Tree Allele ↦ Gauge.totalWalkDist allEdges Gauge.sampleSub)
      (fun tree : Gauge.Tree Allele ↦
        Gauge.segregatingCount allEdges tree Gauge.sampleSub) :=
  not_identifiedBy_of_observationalSymmetry segregatingCountGaugeSymmetry

/-- **No procedure reading sequence-level diversity decides Watterson's `S`.** The
impossibility, in the form the corpus states impossibilities: for any post-processing of
the observation and any acceptance region, the verdict is the same at both trees while the
answer is not. -/
theorem no_criterion_for_segregatingCount_from_totalWalkDist :
    ¬ ∃ decideValue : ℕ → Prop, ∀ tree : Gauge.Tree Allele,
      Gauge.segregatingCount allEdges tree Gauge.sampleSub
          = Gauge.segregatingCount allEdges (Gauge.treeOf Allele.G) Gauge.sampleSub
        ↔ decideValue (Gauge.totalWalkDist allEdges Gauge.sampleSub) :=
  segregatingCountGaugeSymmetry.no_target_criterion

end Descent.Blindness
