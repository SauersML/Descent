/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DynamicsContrast.Tail

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Portability`, `Descent.Program`:
--   Portability: reaches 13 module(s) -- `Descent.Portability.ContinuumCalibration`,
--   `Descent.Portability.CorrectionWidths`, `Descent.Portability.HorizonCurve` and 10 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

/-!
# `DynamicsContrast` -- the head of a split file

This was 3,590 lines. It is now 3 modules under `DynamicsContrast/`, chained in the order
the original was written, and this file names the last of them -- so every existing
`import` of this module keeps working and keeps meaning the same thing.
-/
