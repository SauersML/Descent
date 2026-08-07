/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestryCalibration
import Descent.Portability.AncestrySpecificPower
import Descent.Portability.BayesianPGSTheory
import Descent.Portability.ClinicalUtilityFairness
import Descent.Portability.ContinuumCalibration
import Descent.Portability.ContinuumCalibrationProgram
import Descent.Portability.CorrectionBiology
import Descent.Portability.CorrectionWidths
import Descent.Portability.EquityAndImplementation
import Descent.Portability.GenerativePortabilityLaw
import Descent.Portability.HorizonCurve
import Descent.Portability.ImputationPortability
import Descent.Portability.LongitudinalPortability
import Descent.Portability.MechanisticPortabilityWitnesses
import Descent.Portability.MetricSpecificPortability
import Descent.Portability.MetricSpecificPortability.ARoneFrontier
import Descent.Portability.MetricSpecificPortability.CalibrationVsDiscrimination
import Descent.Portability.MetricSpecificPortability.GeneticFrontier
import Descent.Portability.MetricSpecificPortability.MetricAndClinicalDecisions
import Descent.Portability.MetricSpecificPortability.PrecisionRecall
import Descent.Portability.MetricSpecificPortability.R2Decomposition
import Descent.Portability.MetricSpecificPortability.SharedCorrectionFamily
import Descent.Portability.MultiAncestryTheory
import Descent.Portability.PCCorrectability
import Descent.Portability.PCCorrectability.Core
import Descent.Portability.PCCorrectability.Design
import Descent.Portability.PCCorrectability.Diagnostic
import Descent.Portability.PCCorrectability.EndToEnd
import Descent.Portability.PCCorrectability.Frequency
import Descent.Portability.PCCorrectability.Geometry
import Descent.Portability.PCCorrectability.ImitationCapacity
import Descent.Portability.PCCorrectability.Nonidentifiability
import Descent.Portability.PCCorrectability.Overlap
import Descent.Portability.PCCorrectability.Phase
import Descent.Portability.PCCorrectability.Threshold
import Descent.Portability.PGSCalibrationTheory
import Descent.Portability.PGSCalibrationTheory.CalibrationDefinitions
import Descent.Portability.PGSCalibrationTheory.CalibrationVsDiscrimination
import Descent.Portability.PGSCalibrationTheory.DecisionImplications
import Descent.Portability.PGSCalibrationTheory.PopulationCalibrationDrift
import Descent.Portability.PGSCalibrationTheory.RecalibrationMethods
import Descent.Portability.PhenomeWidePortability
import Descent.Portability.PolygenicContinuumCalibration
import Descent.Portability.PopulationAUC
import Descent.Portability.PortabilityBounds
import Descent.Portability.PortabilityDrift
import Descent.Portability.PortabilityDrift.ClosedPopulationRegime
import Descent.Portability.PortabilityDrift.Definitions
import Descent.Portability.PortabilityDrift.Generational
import Descent.Portability.PortabilityDrift.MigrationDrift
import Descent.Portability.PortabilityDrift.MigrationDriftRecurrence
import Descent.Portability.PortabilityDrift.MutationDrift
import Descent.Portability.PortabilityDrift.NonreversibleFlow
import Descent.Portability.PortabilityDrift.PresentDayMetrics
import Descent.Portability.PortabilityDrift.PresentDayMoments
import Descent.Portability.PortabilityMasterTheorem
import Descent.Portability.RareVariantPortability
import Descent.Portability.SampleOverlapBias
import Descent.Portability.ScoreDistribution
import Descent.Portability.StatisticalGeneticsMethodology
import Descent.Portability.StratificationConfounding
import Descent.Portability.TransferLearningPGS
import Descent.Portability.TransferLearningPGS.FeatureRepresentation
import Descent.Portability.TransferLearningPGS.FineTuning
import Descent.Portability.TransferLearningPGS.ImportanceWeighting
import Descent.Portability.TransferLearningPGS.PGSPortabilityDerivation
import Descent.Portability.TransplantationStability

assert_below Descent.Program

/-!
# `Descent.Portability` -- the layer head

**Every module under `Descent/Portability/`, and nothing else.**

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
