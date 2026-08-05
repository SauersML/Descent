/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.FstDefinitions
import Descent.PopGen.PopulationGeneticsFoundations.CoalescentTheory
import Descent.PopGen.PopulationGeneticsFoundations.SelectionMigrationBalance
import Descent.PopGen.PopulationGeneticsFoundations.WrightFStatistics
import Descent.PopGen.PopulationGeneticsFoundations.MutationDriftBalance
import Descent.PopGen.PopulationGeneticsFoundations.MigrationDriftFoundations
import Descent.PopGen.PopulationGeneticsFoundations.FstDerivationFromDrift
import Descent.PopGen.PopulationGeneticsFoundations.TransientFstDerivation

/-!
# `PopulationGeneticsFoundations` -- the head of a split file

This was 2,740 lines. It is now 8 modules under `PopulationGeneticsFoundations/`, chained in the
order
the original was written, and this file names the last of them -- so every existing
`import` of this module keeps working and keeps meaning the same thing.
-/
