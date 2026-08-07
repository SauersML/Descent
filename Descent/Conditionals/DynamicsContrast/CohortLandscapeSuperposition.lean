/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DeclaredInteractionClass
import Descent.Portability.ContinuumCalibration
import Descent.Portability.CorrectionWidths
import Descent.Conditionals.DescentGeometry
import Descent.Spectral.DirichletTransfer
import Descent.Spectral.ErgodicCovariancePencil
import Descent.Spectral.EnsembleChannel
import Descent.PopGen.FrequencySpectrumStability
import Descent.Portability.HorizonCurve
import Descent.Blindness.LandscapeSuperposition
import Descent.Blindness.XiFromMarkedBreakouts
import Descent.Blindness.SpectralUniversalityFailure
import Descent.Blindness.TrafficInvariantSeparation

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Portability`, `Descent.Program`:
--   Portability: reaches 13 module(s) -- `Descent.Portability.ContinuumCalibration`,
--   `Descent.Portability.CorrectionWidths`, `Descent.Portability.HorizonCurve` and 10 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Conditionals

open Blindness.MarkedBreakout
open Blindness.XiFromMarks
open Blindness.TrafficInvariantSeparation
open scoped Matrix Topology
open scoped BigOperators

/-!
# `DynamicsContrast.CohortLandscapeSuperposition`

Part of the split of `Descent/Conditionals/DynamicsContrast.lean`, which was 3,590 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

section CohortLandscapeSuperposition

variable {Cohort Genotype Overlap : Type*}

/-- A level-resolved forbidden overlap in at least one cohort remains forbidden for the pooled
cohort objective.  In biological language, pooling cannot create a pair of high-fitness
genotypes unless every cohort admits that overlap at the component levels realized by the
pair. -/
theorem pooledCohort_forbiddenOverlap_of_levelResolved_cover
    (active : Finset Cohort) (weight : Cohort → ℝ) (fitness : Cohort → Genotype → ℝ)
    (overlap : Genotype → Genotype → Overlap) (target : ℝ)
    (hweight : ∀ cohort ∈ active, 0 ≤ weight cohort) (q : Overlap)
    (hcover : ∀ leftLevel rightLevel,
      Blindness.AdmissibleLevels active weight target leftLevel →
        Blindness.AdmissibleLevels active weight target rightLevel →
          ∃ cohort ∈ active,
            q ∉ Blindness.ComponentAchievableOverlaps fitness overlap leftLevel rightLevel cohort) :
    q ∉ Blindness.SuperposedAchievableOverlaps active weight fitness overlap target :=
  Blindness.forbiddenOverlap_of_levelResolved_cover active weight fitness overlap target hweight q
    hcover

end CohortLandscapeSuperposition

end Descent.Conditionals
