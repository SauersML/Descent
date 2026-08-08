/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.CoalescentGauge
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
import Descent.Pangenome.Register
import Descent.Pangenome.Strand

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

Three groups, all about what a representation of a haplotype panel loses.  The `Gauge`
modules ask which statistics of a variant catalogue survive a change of reference tree.  The
`Linkage` modules ask what a graph is forced to admit once it has merged haplotype identity
at a separator; `Descent/Pangenome/Linkage.lean` is that group's own table of contents.  The
`GraphCoalescent` modules ask what ancestral process is left once it has, and answer that it
is Kingman's at the graph's width rather than the panel's size;
`Descent/Pangenome/GraphCoalescent.lean` is that group's table of contents.

The third group is where the first two meet the coalescent.  `Gauge` and `Linkage` both
measure a loss in the vocabulary of the representation -- hidden edges, nats of conditional
entropy.  `GraphCoalescent` measures the same loss in the vocabulary of the process, as a
lineage count, a transit time and a bias in `θ`, and `transitDeficit_eq_zero_iff` is the
theorem that says the two vocabularies are describing one thing.

The fourth pair is where the chapter meets the corpus's data objects and its growth law.
`PanelGraph` instantiates the abstract construction at `Core.Genome`'s phased haplotypes --
the bracket collapses, support becomes allele-sharing, and `pan = reference + S` is exact --
and `Growth` takes that identity in expectation, where the pangenome growth curve becomes
`θ` times a harmonic sum, its increments become Watterson's estimator, and openness becomes
the neutral null rather than a finding.
-/
