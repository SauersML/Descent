/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.AdditiveInvariance
import Descent.PopGen.AncestrySpecificArchitecture
import Descent.PopGen.AssortativeMatingPGS
import Descent.PopGen.DGP
import Descent.PopGen.DemographicCapacity
import Descent.PopGen.DemographicHistory
import Descent.PopGen.DriftRegime
import Descent.PopGen.EpistasisAndNonAdditivity
import Descent.PopGen.FrequencySpectrumStability
import Descent.PopGen.GeneEnvironmentInterplay
import Descent.PopGen.GeneticArchitectureDiscovery
import Descent.PopGen.HaplotypeTheory
import Descent.PopGen.HumanDemography
import Descent.PopGen.LDDecayTheory
import Descent.PopGen.PolygenicAdaptation
import Descent.PopGen.PolygenicArchitecture
import Descent.PopGen.PopulationGeneticsFoundations
import Descent.PopGen.PopulationGeneticsFoundations.CoalescentTheory
import Descent.PopGen.PopulationGeneticsFoundations.FstDefinitions
import Descent.PopGen.PopulationGeneticsFoundations.FstDerivationFromDrift
import Descent.PopGen.PopulationGeneticsFoundations.MigrationDriftFoundations
import Descent.PopGen.PopulationGeneticsFoundations.MutationDriftBalance
import Descent.PopGen.PopulationGeneticsFoundations.SelectionMigrationBalance
import Descent.PopGen.PopulationGeneticsFoundations.TransientFstDerivation
import Descent.PopGen.PopulationGeneticsFoundations.WrightFStatistics
import Descent.PopGen.SelectionArchitecture
import Descent.PopGen.SerialFounderChain
import Descent.PopGen.StandardizedGenotypeMoments
import Descent.PopGen.VarianceComponents

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Spectral`, `Descent.Blindness`,
-- `Descent.Conditionals`, `Descent.Portability`, `Descent.Decision`, `Descent.Program`:
--   Spectral: reaches 7 module(s) -- `Descent.Spectral.CirculationDefect`,
--   `Descent.Spectral.EnsembleChannel`, `Descent.Spectral.FoldedSpectrum` and 4 more
--   Blindness: reaches 19 module(s) -- `Descent.Blindness.BundleRigidity`,
--   `Descent.Blindness.BundleRigidity.Coverage`,
--   `Descent.Blindness.BundleRigidity.CoverageInvariance` and 16 more
--   Conditionals: reaches 3 module(s) -- `Descent.Conditionals.ConditionalGain`,
--   `Descent.Conditionals.LatentMechanismCollapse`, `Descent.Conditionals.LocalToGlobalCoherence`
--   Portability: reaches 15 module(s) -- `Descent.Portability.AncestrySpecificPower`,
--   `Descent.Portability.BayesianPGSTheory`, `Descent.Portability.MechanisticPortabilityWitnesses`
--   and 12 more
--   Decision: reaches 2 module(s) -- `Descent.Decision.CertificateGrading`,
--   `Descent.Decision.TransportedMinimax`
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

/-!
# `Descent.PopGen` -- the layer head

**Every module under `Descent/PopGen/`, and nothing else.**

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
