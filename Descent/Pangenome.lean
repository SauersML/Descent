/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.CoalescentGauge
import Descent.Pangenome.GaugeCounterexample
import Descent.Pangenome.GaugeInvariance
import Descent.Pangenome.Linkage
import Descent.Pangenome.Linkage.Barrier
import Descent.Pangenome.Linkage.Chain
import Descent.Pangenome.Linkage.Interface
import Descent.Pangenome.Linkage.Metadata
import Descent.Pangenome.Linkage.Splicing
import Descent.Pangenome.Linkage.Tree

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

Two groups, both about what a representation of a haplotype panel loses.  The `Gauge`
modules ask which statistics of a variant catalogue survive a change of reference tree.  The
`Linkage` modules ask what a graph is forced to admit once it has merged haplotype identity
at a separator; `Descent/Pangenome/Linkage.lean` is that group's own table of contents.
-/
