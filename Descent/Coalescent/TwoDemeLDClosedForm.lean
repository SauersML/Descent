/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Coalescent

/-!
# Concrete two-deme two-locus stationary law

This is the two-population specialization of the Ragsdale--Gravel moment system implemented
by `moments.LD`.  It has three heterozygosity coordinates and fifteen canonical two-locus
coordinates.  Mutation is normalized to one: the heterozygosities scale linearly in mutation
and the two-locus moments quadratically, so the common factor cancels from every `DD` ratio.

`rho` is the recombination rate and `M` is each directional backward migration entry in the
same diffusion time unit.  The operator is exactly

`drift + mutation-coupling + rho * recombination + M * migration`.

Consequently every stationary coordinate, and every ratio of `DD` coordinates, is a literal
rational function of `(rho,M)` by Cramer's rule.

## Empirical status

Stated once here for the component matrices and the solve built from them, because they share
one verdict and twelve copies of it would be twelve places for it to drift.

THE COMPONENT MATRICES ARE THE MODEL. `twoDemeHDrift`, `twoDemeHMigration`, `twoDemeYDrift`,
`twoDemeYRecombination`, `twoDemeMutationCoupling` and `twoDemeYMigration` are the entries of
the Ragsdale--Gravel two-locus generator specialized to two demes, and `publishedTwoDemeLDBase`,
`...Recombination`, `...Migration`, `...Forcing` and `...Operator` assemble them. Writing them
down is choosing a reproduction and migration mechanism, not asserting anything about a
population, so no measurement can bear on an entry of the generator: what could be wrong is
whether a population is described by this generator at all, and that question is asked where
its output is compared against something -- `validation/empirical/momentsld/ld_surface.py`
integrates this system and `Descent.Portability.PortabilityDrift.PresentDayMoments`'s
`momentsLDWitness` reads the surface it returns.

`publishedTwoDemeLDCoordinateValue` is DERIVED and not measured: it is Cramer's rule applied to
the operator above, and `publishedTwoDemeCrossD_eq_rational` and
`publishedTwoDemeDCorrelation_eq_rational` are the proofs. An arithmetic consequence of a model
is true of the model whatever a population does.

WHAT THIS SECTION DOES NOT COVER, named rather than left silent. The quantity this file exists
to supply downstream is `publishedTwoDemeDCorrelation`, and it carries no status of its own.
Unlike the entries above it IS an empirical claim -- it predicts a cross-deme LD correlation at
a recombination rate and a migration rate, which a simulation can contradict -- and the screen
that asks for a marker never asks it, because that screen keys on the NAME and this name
carries no domain word it recognizes while `publishedTwoDemeLDBase` does. So the file's
internal bookkeeping is the part being policed and the prediction is the part that is not.
Supplying it means comparing this rational function against the same system integrated
numerically, which is a measurement nobody has recorded here yet.
-/

/-- Canonical two-deme heterozygosity moments. -/
inductive TwoDemeH where
  | h00 | h01 | h11
deriving DecidableEq, Fintype, Repr

/-- Canonical two-deme `DD`, `Dz`, and `pi2` moments in published order. -/
inductive TwoDemeY where
  | dd00 | dd01 | dd11
  | dz000 | dz001 | dz011 | dz100 | dz101 | dz111
  | pi0000 | pi0001 | pi0011 | pi0101 | pi0111 | pi1111
deriving DecidableEq, Fintype, Repr

/-- The coupled stationary system: heterozygosities first, then two-locus moments. -/
inductive TwoDemeLDCoordinate where
  | h (moment : TwoDemeH)
  | y (moment : TwoDemeY)
deriving DecidableEq, Fintype, Repr

/-! ## Published component matrices -/

/-- Unit-size drift on the three heterozygosity moments. -/
noncomputable def twoDemeHDrift : TwoDemeH → TwoDemeH → ℝ
  | .h00, .h00 => -1
  | .h11, .h11 => -1
  | _, _ => 0

/-- Symmetric unit directional migration on heterozygosities. -/
noncomputable def twoDemeHMigration : TwoDemeH → TwoDemeH → ℝ
  | .h00, .h00 => -2
  | .h00, .h01 => 2
  | .h01, .h00 => 1
  | .h01, .h01 => -2
  | .h01, .h11 => 1
  | .h11, .h01 => 2
  | .h11, .h11 => -2
  | _, _ => 0

/-- Unit-size drift on the fifteen LD coordinates. -/
noncomputable def twoDemeYDrift : TwoDemeY → TwoDemeY → ℝ
  | .dd00, .dd00 => -3
  | .dd00, .dz000 => 1
  | .dd00, .pi0000 => 1
  | .dd01, .dd01 => -2
  | .dd11, .dd11 => -3
  | .dd11, .dz111 => 1
  | .dd11, .pi1111 => 1
  | .dz000, .dd00 => 4
  | .dz000, .dz000 => -5
  | .dz001, .dz001 => -3
  | .dz011, .dd01 => 4
  | .dz011, .dz011 => -1
  | .dz100, .dd01 => 4
  | .dz100, .dz100 => -1
  | .dz101, .dz101 => -3
  | .dz111, .dd11 => 4
  | .dz111, .dz111 => -5
  | .pi0000, .dz000 => 1
  | .pi0000, .pi0000 => -2
  | .pi0001, .dz001 => 1 / 2
  | .pi0001, .pi0001 => -1
  | .pi0011, .pi0011 => -2
  | .pi0101, .dz011 => 1 / 4
  | .pi0101, .dz100 => 1 / 4
  | .pi0111, .dz101 => 1 / 2
  | .pi0111, .pi0111 => -1
  | .pi1111, .dz111 => 1
  | .pi1111, .pi1111 => -2
  | _, _ => 0

/-- Recombination coefficient: `-rho` on `DD`, `-rho/2` on `Dz`, zero on `pi2`. -/
noncomputable def twoDemeYRecombination : TwoDemeY → TwoDemeY → ℝ
  | .dd00, .dd00 => -1
  | .dd01, .dd01 => -1
  | .dd11, .dd11 => -1
  | .dz000, .dz000 => -1 / 2
  | .dz001, .dz001 => -1 / 2
  | .dz011, .dz011 => -1 / 2
  | .dz100, .dz100 => -1 / 2
  | .dz101, .dz101 => -1 / 2
  | .dz111, .dz111 => -1 / 2
  | _, _ => 0

/-- Mutation coupling from heterozygosity into `pi2`, at normalized mutation rate one. -/
noncomputable def twoDemeMutationCoupling : TwoDemeY → TwoDemeH → ℝ
  | .pi0000, .h00 => 1 / 2
  | .pi0001, .h00 => 1 / 4
  | .pi0001, .h01 => 1 / 4
  | .pi0011, .h00 => 1 / 4
  | .pi0011, .h11 => 1 / 4
  | .pi0101, .h01 => 1 / 2
  | .pi0111, .h01 => 1 / 4
  | .pi0111, .h11 => 1 / 4
  | .pi1111, .h11 => 1 / 2
  | _, _ => 0

/-- Symmetric unit directional migration on all fifteen LD moments. -/
noncomputable def twoDemeYMigration : TwoDemeY → TwoDemeY → ℝ
  | .dd00, .dd00 => -2
  | .dd00, .dd01 => 2
  | .dd00, .dz000 => 1 / 2
  | .dd00, .dz001 => -1
  | .dd00, .dz011 => 1 / 2
  | .dd01, .dd00 => 1
  | .dd01, .dd01 => -2
  | .dd01, .dd11 => 1
  | .dd01, .dz000 => 1 / 4
  | .dd01, .dz001 => -1 / 2
  | .dd01, .dz011 => 1 / 4
  | .dd01, .dz100 => 1 / 4
  | .dd01, .dz101 => -1 / 2
  | .dd01, .dz111 => 1 / 4
  | .dd11, .dd01 => 2
  | .dd11, .dd11 => -2
  | .dd11, .dz100 => 1 / 2
  | .dd11, .dz101 => -1
  | .dd11, .dz111 => 1 / 2
  | .dz000, .dz000 => -3
  | .dz000, .dz001 => 2
  | .dz000, .dz100 => 1
  | .dz000, .pi0000 => 4
  | .dz000, .pi0001 => -8
  | .dz000, .pi0101 => 4
  | .dz001, .dz000 => 1
  | .dz001, .dz001 => -3
  | .dz001, .dz011 => 1
  | .dz001, .dz101 => 1
  | .dz001, .pi0001 => 4
  | .dz001, .pi0011 => -4
  | .dz001, .pi0101 => -4
  | .dz001, .pi0111 => 4
  | .dz011, .dz001 => 2
  | .dz011, .dz011 => -3
  | .dz011, .dz111 => 1
  | .dz011, .pi0101 => 4
  | .dz011, .pi0111 => -8
  | .dz011, .pi1111 => 4
  | .dz100, .dz000 => 1
  | .dz100, .dz100 => -3
  | .dz100, .dz101 => 2
  | .dz100, .pi0000 => 4
  | .dz100, .pi0001 => -8
  | .dz100, .pi0101 => 4
  | .dz101, .dz001 => 1
  | .dz101, .dz100 => 1
  | .dz101, .dz101 => -3
  | .dz101, .dz111 => 1
  | .dz101, .pi0001 => 4
  | .dz101, .pi0011 => -4
  | .dz101, .pi0101 => -4
  | .dz101, .pi0111 => 4
  | .dz111, .dz011 => 1
  | .dz111, .dz101 => 2
  | .dz111, .dz111 => -3
  | .dz111, .pi0101 => 4
  | .dz111, .pi0111 => -8
  | .dz111, .pi1111 => 4
  | .pi0000, .pi0000 => -4
  | .pi0000, .pi0001 => 4
  | .pi0001, .pi0000 => 1
  | .pi0001, .pi0001 => -4
  | .pi0001, .pi0011 => 1
  | .pi0001, .pi0101 => 2
  | .pi0011, .pi0001 => 2
  | .pi0011, .pi0011 => -4
  | .pi0011, .pi0111 => 2
  | .pi0101, .pi0001 => 2
  | .pi0101, .pi0101 => -4
  | .pi0101, .pi0111 => 2
  | .pi0111, .pi0011 => 1
  | .pi0111, .pi0101 => 2
  | .pi0111, .pi0111 => -4
  | .pi0111, .pi1111 => 1
  | .pi1111, .pi0111 => 4
  | .pi1111, .pi1111 => -4
  | _, _ => 0

/-! ## Coupled stationary solve -/

/-- Constant part of the coupled operator: drift plus mutation coupling. -/
noncomputable def publishedTwoDemeLDBase :
    Matrix TwoDemeLDCoordinate TwoDemeLDCoordinate ℝ
  | .h row, .h column => twoDemeHDrift row column
  | .y row, .h column => twoDemeMutationCoupling row column
  | .y row, .y column => twoDemeYDrift row column
  | .h _, .y _ => 0

/-- Recombination coefficient matrix. -/
noncomputable def publishedTwoDemeLDRecombination :
    Matrix TwoDemeLDCoordinate TwoDemeLDCoordinate ℝ
  | .y row, .y column => twoDemeYRecombination row column
  | _, _ => 0

/-- Symmetric migration coefficient matrix. -/
noncomputable def publishedTwoDemeLDMigration :
    Matrix TwoDemeLDCoordinate TwoDemeLDCoordinate ℝ
  | .h row, .h column => twoDemeHMigration row column
  | .y row, .y column => twoDemeYMigration row column
  | _, _ => 0

/-- Normalized mutation forcing for heterozygosity; LD is forced through the coupling block. -/
noncomputable def publishedTwoDemeLDForcing : TwoDemeLDCoordinate → ℝ
  | .h _ => 1
  | .y _ => 0

/-- The concrete 18-state stationary operator. -/
noncomputable def publishedTwoDemeLDOperator (rho M : ℝ) :
    Matrix TwoDemeLDCoordinate TwoDemeLDCoordinate ℝ :=
  publishedTwoDemeLDBase + rho • publishedTwoDemeLDRecombination +
    M • publishedTwoDemeLDMigration

/-- One exact stationary coordinate. -/
noncomputable def publishedTwoDemeLDCoordinateValue
    (rho M : ℝ) (coordinate : TwoDemeLDCoordinate) : ℝ :=
  cramerCoordinate (publishedTwoDemeLDOperator rho M)
    (fun row ↦ -publishedTwoDemeLDForcing row) coordinate

/-- Within-source `E[D₀²]`. -/
noncomputable def publishedTwoDemeWithinD (rho M : ℝ) : ℝ :=
  publishedTwoDemeLDCoordinateValue rho M (.y .dd00)

/-- Cross-deme `E[D₀D₁]`. -/
noncomputable def publishedTwoDemeCrossD (rho M : ℝ) : ℝ :=
  publishedTwoDemeLDCoordinateValue rho M (.y .dd01)

/-- Within-target `E[D₁²]`. -/
noncomputable def publishedTwoDemeTargetWithinD (rho M : ℝ) : ℝ :=
  publishedTwoDemeLDCoordinateValue rho M (.y .dd11)

/-- The migration--LD prediction consumed downstream. -/
noncomputable def publishedTwoDemeDCorrelation (rho M : ℝ) : ℝ :=
  publishedTwoDemeCrossD rho M / publishedTwoDemeWithinD rho M

/-- The admissible domain of the concrete law.  Physical rate constraints and both algebraic
poles are carried by the point supplied to downstream consumers. -/
structure PublishedTwoDemeLDPoint where
  rho : ℝ
  migration : ℝ
  rho_nonneg : 0 ≤ rho
  migration_nonneg : 0 ≤ migration
  operator_nonsingular : (publishedTwoDemeLDOperator rho migration).det ≠ 0
  within_numerator_nonzero :
    (replaceColumn (publishedTwoDemeLDOperator rho migration)
      (fun row ↦ -publishedTwoDemeLDForcing row) (.y .dd00)).det ≠ 0

/-- The concrete law evaluated on its typed domain. -/
noncomputable def PublishedTwoDemeLDPoint.correlation
    (point : PublishedTwoDemeLDPoint) : ℝ :=
  publishedTwoDemeDCorrelation point.rho point.migration

/-- The concrete `E[D₀D₁]` family is a rational determinant quotient in `(rho,M)`. -/
theorem publishedTwoDemeCrossD_eq_rational (rho M : ℝ) :
    publishedTwoDemeCrossD rho M =
      (replaceColumn (publishedTwoDemeLDOperator rho M)
        (fun row ↦ -publishedTwoDemeLDForcing row) (.y .dd01)).det /
      (publishedTwoDemeLDOperator rho M).det := rfl

/-- The correlation is the ratio of the cross and within Cramer numerators whenever both
poles are excluded; the common operator determinant cancels exactly. -/
theorem publishedTwoDemeDCorrelation_eq_rational (rho M : ℝ)
    (hoperator : (publishedTwoDemeLDOperator rho M).det ≠ 0)
    (hwithin : (replaceColumn (publishedTwoDemeLDOperator rho M)
      (fun row ↦ -publishedTwoDemeLDForcing row) (.y .dd00)).det ≠ 0) :
    publishedTwoDemeDCorrelation rho M =
      (replaceColumn (publishedTwoDemeLDOperator rho M)
        (fun row ↦ -publishedTwoDemeLDForcing row) (.y .dd01)).det /
      (replaceColumn (publishedTwoDemeLDOperator rho M)
        (fun row ↦ -publishedTwoDemeLDForcing row) (.y .dd00)).det := by
  unfold publishedTwoDemeDCorrelation publishedTwoDemeCrossD publishedTwoDemeWithinD
    publishedTwoDemeLDCoordinateValue cramerCoordinate
  field_simp [hoperator, hwithin]

/-- At zero recombination the recombination block vanishes literally. -/
theorem publishedTwoDemeLDOperator_zero_recombination (M : ℝ) :
    publishedTwoDemeLDOperator 0 M =
      publishedTwoDemeLDBase + M • publishedTwoDemeLDMigration := by
  unfold publishedTwoDemeLDOperator
  simp

/-- At zero migration the migration block vanishes literally. -/
theorem publishedTwoDemeLDOperator_zero_migration (rho : ℝ) :
    publishedTwoDemeLDOperator rho 0 =
      publishedTwoDemeLDBase + rho • publishedTwoDemeLDRecombination := by
  unfold publishedTwoDemeLDOperator
  simp

/-- Panmictic identification collapses within and cross `DD` to one coordinate. -/
inductive PanmicticDD where
  | dd
deriving DecidableEq, Fintype, Repr

/-- The exact panmictic check is one because both reads are the same coordinate. -/
noncomputable def panmicticDCorrelation (moment : PanmicticDD → ℝ) : ℝ :=
  moment .dd / moment .dd

theorem panmicticDCorrelation_eq_one (moment : PanmicticDD → ℝ)
    (hnonzero : moment .dd ≠ 0) : panmicticDCorrelation moment = 1 := by
  unfold panmicticDCorrelation
  exact div_self _

end Descent.Coalescent
