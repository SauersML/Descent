/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.LandscapeSuperposition
import Descent.Blindness.SpectralUniversalityFailure
import Descent.Blindness.SpectrumIdentifiability
import Descent.Blindness.TrafficInvariantSeparation
import Descent.Blindness.XiFromMarkedBreakouts
import Descent.Portability.CorrectionWidths
import Descent.Spectral.EnsembleChannel
import Descent.Spectral.ErgodicCovariancePencil

namespace Descent.Conditionals

open Blindness.MarkedBreakout
open Blindness.XiFromMarks
open Blindness.TrafficInvariantSeparation
open scoped Matrix Topology
open scoped BigOperators

/-!
# `DynamicsContrast.CohortLandscapeSuperposition`

Part of the split of `Descent/Conditionals/DynamicsContrast.lean`, which was 3,590 lines.

The parts are a FAN: each imports the modules that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against the corpus's
declarations, and the imports above are the answer, so what a part rests on is readable from
its header instead of inherited from its position in a file that no longer exists.

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
  Blindness.forbiddenOverlap_of_levelResolved_cover active weight fitness overlap target hweight q hcover

end CohortLandscapeSuperposition

end Descent.Conditionals
