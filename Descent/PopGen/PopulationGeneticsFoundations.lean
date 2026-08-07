/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.SelectionMigrationBalance
import Descent.PopGen.PopulationGeneticsFoundations.MigrationDriftFoundations
import Descent.PopGen.PopulationGeneticsFoundations.FstDerivationFromDrift
import Descent.PopGen.PopulationGeneticsFoundations.TransientFstDerivation

assert_below Descent.Blindness Descent.Conditionals Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Portability`, `Descent.Spectral`:
--   Spectral: reaches 2 module(s) -- `Descent.Spectral.CirculationDefect`,
--   `Descent.Spectral.SpectralDegradation`
--   Portability: reaches 10 module(s) -- `Descent.Portability.PortabilityDrift`,
--   `Descent.Portability.PortabilityDrift.ClosedPopulationRegime`,
--   `Descent.Portability.PortabilityDrift.Definitions` and 7 more
-- The repair is to move what it reaches for DOWN, not to move this file up.

/-!
# `PopulationGeneticsFoundations` -- the head of a split file

This was 2,740 lines. It is now 8 modules under `PopulationGeneticsFoundations/`, chained in the
order
the original was written, and this file names the last of them -- so every existing
`import` of this module keeps working and keeps meaning the same thing.
-/
