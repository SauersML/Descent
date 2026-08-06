/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift.ClosedPopulationRegime
import Descent.Portability.PortabilityDrift.Definitions
import Descent.Portability.PortabilityDrift.Generational
import Descent.Portability.PortabilityDrift.MigrationDrift
import Descent.Portability.PortabilityDrift.MigrationDriftRecurrence
import Descent.Portability.PortabilityDrift.MutationDrift
import Descent.Portability.PortabilityDrift.NonreversibleFlow
import Descent.Portability.PortabilityDrift.PresentDayMetrics
import Descent.Portability.PortabilityDrift.PresentDayMoments
import Descent.Layer

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Program`:
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

/-!
# `Portability.PortabilityDrift` -- the head of a split file

This was 9,208 lines and 555 declarations, the largest file in the corpus by both measures.
It is now nine modules under `PortabilityDrift/`, and this file names all of them -- so
every existing `import Descent.Portability.PortabilityDrift` keeps working and keeps meaning
the same thing.

Naming all of them is what makes that true. The split first chained the parts, each
importing the one before, and a head that named only the last one reached the whole file
through that chain. The parts are now a fan: `Definitions` carries the definitions and the
imports the subsystem draws on from outside itself, and the others import it and whichever
siblings actually declare the names they use. A fan has no last part, so a head naming one
part would silently stop delivering the rest, and the three modules that import this one and
nothing under it -- `Program.OpenQuestions`, `PopGen.HumanDemography` and
`Portability.MechanisticPortabilityWitnesses` -- would lose declarations with nothing to say
so.

The fan also records what the chain hid. `NonreversibleFlow` proves two theorems about
circulation and mixing time out of `Spectral.CirculationDefect` alone; the chain had placed
it downstream of all eight other parts. `Generational` and `ClosedPopulationRegime` name
nothing from any sibling either. What the theory actually stacks is the metric line:
`ClosedPopulationRegime` under `PresentDayMetrics` under `MutationDrift` under
`MigrationDrift` under `MigrationDriftRecurrence`.
-/
