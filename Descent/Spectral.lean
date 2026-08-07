/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Spectral.CirculationDefect
import Descent.Spectral.DirichletTransfer
import Descent.Spectral.EnsembleChannel
import Descent.Spectral.ErgodicCovariancePencil
import Descent.Spectral.FoldedSpectrum
import Descent.Spectral.PencilEnvironment
import Descent.Spectral.Permeability
import Descent.Spectral.PolygenicSpectroscopy
import Descent.Spectral.ProjectionShiftBounds
import Descent.Spectral.ProjectionSolve
import Descent.Spectral.QuadraticShift
import Descent.Spectral.ResonanceSpectrum
import Descent.Spectral.ReversibleMarkovSpectrum
import Descent.Spectral.SecondMomentShift
import Descent.Spectral.SpectralDegradation
import Descent.Spectral.WhiteningEquivalence

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`, `Descent.Conditionals`,
-- `Descent.Portability`, `Descent.Program`:
--   Blindness: reaches 15 module(s) -- `Descent.Blindness.BundleRigidity`,
--   `Descent.Blindness.BundleRigidity.Coverage`,
--   `Descent.Blindness.BundleRigidity.CoverageInvariance` and 12 more
--   Conditionals: reaches 2 module(s) -- `Descent.Conditionals.ConditionalGain`,
--   `Descent.Conditionals.LocalToGlobalCoherence`
--   Portability: reaches 11 module(s) -- `Descent.Portability.PCCorrectability.Core`,
--   `Descent.Portability.PortabilityDrift`,
--   `Descent.Portability.PortabilityDrift.ClosedPopulationRegime` and 8 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

/-!
# `Descent.Spectral` -- the layer head

**Every module under `Descent/Spectral/`, and nothing else.**

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
-/
