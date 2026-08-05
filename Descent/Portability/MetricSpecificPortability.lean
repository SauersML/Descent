/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.ARoneFrontier
import Descent.Portability.MetricSpecificPortability.CalibrationVsDiscrimination
import Descent.Portability.MetricSpecificPortability.GeneticFrontier
import Descent.Portability.MetricSpecificPortability.MetricAndClinicalDecisions
import Descent.Portability.MetricSpecificPortability.PrecisionRecall
import Descent.Portability.MetricSpecificPortability.R2Decomposition
import Descent.Portability.MetricSpecificPortability.SharedCorrectionFamily

/-!
# `MetricSpecificPortability` -- the head of a split file

This was 3,946 lines. It is now 7 modules under `MetricSpecificPortability/`, and this file
names all of them -- so every existing `import` of this module keeps working and keeps
meaning the same thing.

Naming all of them is what makes that true. The split first chained the parts, each
importing the one before, and a head that named only the last one reached the whole file
through that chain. The parts are now a fan: `R2Decomposition` carries the definitions and
the outside imports, and the others import it and whatever siblings they actually name. A
fan has no last part, so a head that named one part would silently stop delivering the
rest, and `Program.Conventions` -- which imports this module and nothing under it -- would
lose declarations without anything saying so.
-/
