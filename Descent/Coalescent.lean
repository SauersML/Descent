/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.AlleleCount
import Descent.Coalescent.BertrandDescent
import Descent.Coalescent.Beta
import Descent.Coalescent.BlockCountMatrix
import Descent.Coalescent.BlockMatrixLimit
import Descent.Coalescent.BranchLength
import Descent.Coalescent.ComingDownCriterion
import Descent.Coalescent.ComingDownFromInfinity
import Descent.Coalescent.CompetingRates
import Descent.Coalescent.Convergence
import Descent.Coalescent.CutCount
import Descent.Coalescent.CutSets
import Descent.Coalescent.DecreaseRate
import Descent.Coalescent.DescentTime
import Descent.Coalescent.Duality
import Descent.Coalescent.Encoding
import Descent.Coalescent.EntranceLaw
import Descent.Coalescent.Ewens
import Descent.Coalescent.ExpRemainder
import Descent.Coalescent.Extend
import Descent.Coalescent.FamilySize
import Descent.Coalescent.Fixation
import Descent.Coalescent.FuUrn
import Descent.Coalescent.GeneTreeDiscordance
import Descent.Coalescent.Generator
import Descent.Coalescent.HoldingSecondMoment
import Descent.Coalescent.HoldingTime
import Descent.Coalescent.Infinite
import Descent.Coalescent.IntervalPicture
import Descent.Coalescent.JumpChain
import Descent.Coalescent.Kernel
import Descent.Coalescent.Lambda
import Descent.Coalescent.LaplaceTransform
import Descent.Coalescent.Law
import Descent.Coalescent.Lookdown
import Descent.Coalescent.LookdownClocks
import Descent.Coalescent.Lumping
import Descent.Coalescent.MohleLemma
import Descent.Coalescent.Moran
import Descent.Coalescent.MultiMerge
import Descent.Coalescent.Mutation
import Descent.Coalescent.NeutralMutation
import Descent.Coalescent.Paintbox
import Descent.Coalescent.PaintboxFrequency
import Descent.Coalescent.PairChainLimit
import Descent.Coalescent.PairwiseTimes
import Descent.Coalescent.Path
import Descent.Coalescent.Pedigree
import Descent.Coalescent.PolyaCriterion
import Descent.Coalescent.Process
import Descent.Coalescent.Program
import Descent.Coalescent.QuotientRelation
import Descent.Coalescent.Rates
import Descent.Coalescent.Recombination
import Descent.Coalescent.Restriction
import Descent.Coalescent.SeedBank
import Descent.Coalescent.SegregatingSites
import Descent.Coalescent.Selection
import Descent.Coalescent.SemigroupLimit
import Descent.Coalescent.SiteFrequencySpectrum
import Descent.Coalescent.SpatialCoalescent
import Descent.Coalescent.SpectrumMoments
import Descent.Coalescent.Split
import Descent.Coalescent.StateSpace
import Descent.Coalescent.StepLaw
import Descent.Coalescent.Structured
import Descent.Coalescent.TajimaVariance
import Descent.Coalescent.ThreeSeries
import Descent.Coalescent.Trajectory
import Descent.Coalescent.TrajectoryLaw
import Descent.Coalescent.TransitTransform
import Descent.Coalescent.TransitVariance
import Descent.Coalescent.Uniqueness
import Descent.Coalescent.VariableSize
import Descent.Coalescent.WrightFisher
import Descent.Coalescent.Xi
import Descent.Coalescent.XiRates

/-!
# `Descent.Coalescent` -- the layer head

**Every module under `Descent/Coalescent/`, and nothing else.**

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
