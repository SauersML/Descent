/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.BlindnessRegistry
import Descent.Blindness.BundleRigidity
import Descent.Blindness.BundleRigidity.Coverage
import Descent.Blindness.BundleRigidity.CoverageInvariance
import Descent.Blindness.BundleRigidity.Cycles
import Descent.Blindness.BundleRigidity.DeploymentCeiling
import Descent.Blindness.BundleRigidity.Dichotomy
import Descent.Blindness.BundleRigidity.EntropySplit
import Descent.Blindness.BundleRigidity.Freshness
import Descent.Blindness.BundleRigidity.LinearSCM
import Descent.Blindness.BundleRigidity.Operator
import Descent.Blindness.BundleRigidity.Realizability
import Descent.Blindness.BundleRigidity.SingleModulus
import Descent.Blindness.BundleRigidity.Telescope
import Descent.Blindness.BundleRigidity.TwoAtom
import Descent.Blindness.Condensation
import Descent.Blindness.CountingInvariantBlindness
import Descent.Blindness.CountingInvariantInstances
import Descent.Blindness.CramerStratum
import Descent.Blindness.CumulantBlindness
import Descent.Blindness.DecoratedGeometryBlindness
import Descent.Blindness.EffectSizeSurgery
import Descent.Blindness.EpistaticChaos
import Descent.Blindness.HiddenConeAmbiguity
import Descent.Blindness.ImitationRigidity
import Descent.Blindness.JetBarrier
import Descent.Blindness.LandscapeSuperposition
import Descent.Blindness.LumpedRateBlindness
import Descent.Blindness.MarkedBreakoutUniversality
import Descent.Blindness.MultipleMergerBlindness
import Descent.Blindness.ObservationalCeiling
import Descent.Blindness.SpectralUniversalityFailure
import Descent.Blindness.SpectrumIdentifiability
import Descent.Blindness.TrafficInvariantSeparation
import Descent.Blindness.TrafficInvariantSeparation.CurieWeissWindow
import Descent.Blindness.TrafficInvariantSeparation.ExponentialProfileCompactness
import Descent.Blindness.TrafficInvariantSeparation.InvariantSeparation
import Descent.Blindness.TrafficInvariantSeparation.MatchedBayesBoundary
import Descent.Blindness.TrafficInvariantSeparation.MesoscopicAmplification
import Descent.Blindness.TrafficInvariantSeparation.PolynomialTraffic
import Descent.Blindness.TrafficInvariantSeparation.RankOneInvisibility
import Descent.Blindness.TrafficInvariantSeparation.SpectralSDPSeparation
import Descent.Blindness.XiFromMarkedBreakouts

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Conditionals`, `Descent.Portability`, `Descent.Program`:
--   Conditionals: reaches 1 module(s) -- `Descent.Conditionals.ConditionalGain`
--   Portability: reaches 22 module(s) -- `Descent.Portability.ClinicalUtilityFairness`, `Descent.Portability.ContinuumCalibration`, `Descent.Portability.MetricSpecificPortability.PrecisionRecall` and 19 more
--   Program: reaches 2 module(s) -- `Descent.Program.Conclusions`, `Descent.Program.OpenQuestions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

/-!
# `Descent.Blindness` -- the layer head

**Every module under `Descent/Blindness/`, and nothing else.**

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
