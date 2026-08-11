/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.ChainGluing
import Descent.Pangenome.CoalescentGauge
import Descent.Pangenome.Chart
import Descent.Pangenome.Construction
import Descent.Pangenome.ConstructionCoalescent
import Descent.Pangenome.CoreAccessory
import Descent.Pangenome.GaugeCounterexample
import Descent.Pangenome.GaugeInvariance
import Descent.Pangenome.GraphCoalescent
import Descent.Pangenome.GraphCoalescent.Deficit
import Descent.Pangenome.GraphCoalescent.EstimatorSign
import Descent.Pangenome.GraphCoalescent.MergerDepth
import Descent.Pangenome.GraphCoalescent.Observation
import Descent.Pangenome.GraphCoalescent.Pinned
import Descent.Pangenome.GraphCoalescent.Reduction
import Descent.Pangenome.GraphCoalescent.Visibility
import Descent.Pangenome.GraphCoalescent.WidthProfile
import Descent.Pangenome.GraphSpectrum
import Descent.Pangenome.GraphTransitVariance
import Descent.Pangenome.GromovWeak
import Descent.Pangenome.Growth
import Descent.Pangenome.HaplotypeGluing
import Descent.Pangenome.HomologyGroupoid
import Descent.Pangenome.Linkage
import Descent.Pangenome.Linkage.Barrier
import Descent.Pangenome.Linkage.Chain
import Descent.Pangenome.Linkage.Frequency
import Descent.Pangenome.Linkage.Interface
import Descent.Pangenome.Linkage.Metadata
import Descent.Pangenome.Linkage.Pinned
import Descent.Pangenome.Linkage.Splicing
import Descent.Pangenome.Linkage.Tree
import Descent.Pangenome.PanelGraph
import Descent.Pangenome.Presentation
import Descent.Pangenome.Register
import Descent.Pangenome.Strand
import Descent.Pangenome.Symmetry
import Descent.Pangenome.TripleGluing

/-!
# `Descent.Pangenome` -- the layer head

**Every module under `Descent/Pangenome/`, and nothing else.**

The root file used to import 171 modules directly, with a comment explaining that orphan
modules get named there "rather than left to be picked up by whoever remembers to name
them".  That comment was right about the hazard -- `ResonanceSpectrum` failed all day on a
missing import while every whole-corpus build reported zero errors, because no target ever
named it -- and wrong about the remedy: a list somebody maintains by hand has the same
failure mode as no list, one memory lapse later.

A layer head does not need remembering.  `validation/code/check.py --only heads` reads the
directory and fails if a file in it is missing here, so a new module is either imported or
the build says which one is not.  The root then names eleven heads instead of 171 modules,
and its import list stops being a place where coverage can quietly lapse.

This file contains no declarations.  It is a table of contents, and a table of contents
that states a theorem is a module pretending to be a table of contents.

## What is under it

The organising spine is one pipeline.  `Chart` puts genomic anchors and mass on the canonical
`Descent.Core.FinitePartialBijection` maps, then quotients representatives through the shared
`Descent.Core.GroupoidPresentation` engine to obtain an exact Mathlib groupoid.
`HomologyGroupoid` propositionally truncates that SAME groupoid to `Presentation`; it defines no
second groupoid.  For a fixed panel, presentation objects are surjective coordinate maps and
arrows are commuting coarsenings.  Isomorphism is exactly equality of the induced homology
relation, while invariant statistics are exactly those factoring through it.  The coarse layer
is used only for representation-invariant statistics; symmetry stays on the exact
witness groupoid where its isotropy remains available.

`Construction` supplies the universal coarse object: equivalence closure is the initial
presentation coequalising the reported alignments.  A `PangenomeObject` is then the quotient of
storage graphs by semantic equivalence, so node splitting and merging do not change the object.
`PanelGraph` instantiates it at `Core.Genome`'s phased haplotypes, where the bracket collapses,
support becomes allele-sharing, and `pan = reference + S` is exact.

The remaining modules are structures and observables on that spine.  `Register` and `Strand`
place cyclic copy labels and reverse-complement holonomy inside presentation equivalence.
`Gauge` asks which catalogue statistics descend after a reference-tree decoration is
forgotten.  `CoreAccessory` and `Growth` study kernel-defined counts.  `HaplotypeGluing`
proves that compatible local sections are the least crossover-closed extension of the
observed panel, identifies its one-interface defect exactly with `Linkage.phantoms`, and
recovers classical binary `D` as the normalized probabilistic gluing residual.  `Linkage`
asks what a presentation is forced to admit after merging haplotype identity at a separator,
and
`GraphCoalescent` reads the same presentation kernel as a floor on ancestral resolution.
Its categorical coarsening arrows therefore control linkage loss, transit deficit and bias
in `θ` through one refinement order rather than through parallel notions of graph change.

`Symmetry` introduces no parallel symmetry structure: global chart symmetries are the shared
`Descent.Core.FiniteGroupoid.Bisection`, and the existing bisection theorem identifies them
with the existing `Descent.Core.Wreath` whenever the chart groupoid is connected.  Thus local
isotropy, exchange of equivalent charts, and finite partial correspondences all live in the same
exact groupoid before coarse truncation.
-/
