/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.MigrationDriftFoundations

assert_below Descent.Decision Descent.Program

namespace Descent.PopGen

/-!
# Typed migration components

Directional lineage migration, its symmetric and antisymmetric components, scaled flow, and
the finite-deme correction are different quantities.  The typed decomposition lets arbitrary
demographies supply them without letting an estimator silently exchange one for another.
-/

/-- A nonnegative directional backward migration rate. -/
structure DirectionalMigrationRate where
  value : ℝ
  nonneg : 0 ≤ value

/-- A strictly positive population-size scale. -/
structure PositivePopulationSize where
  value : ℝ
  value_pos : 0 < value

/-- A finite island system has at least two demes. -/
structure FiniteDemeCount where
  value : ℕ
  value_gt_one : 1 < value

/-- **The three scalar classes are inhabited.**  Each carries exactly one hypothesis, and a
theorem quantified over an uninhabited structure is true and empty -- kernel-checked, clean
axiom report, no content -- so each needs an exhibited inhabitant before anything stated over
it is a statement about something.  The values are not `0` and not `1`: a witness sitting on
the boundary its own hypothesis excludes, or on a value at which the arithmetic below
degenerates, demonstrates inhabitation while hiding whether the general construction works. -/
noncomputable def DirectionalMigrationRate.witness : DirectionalMigrationRate where
  value := 1 / 100
  nonneg := by norm_num

/-- Inhabitation for the size scale; see `DirectionalMigrationRate.witness`. -/
noncomputable def PositivePopulationSize.witness : PositivePopulationSize where
  value := 1000
  value_pos := by norm_num

/-- Inhabitation for the deme count; see `DirectionalMigrationRate.witness`.  Three rather than
the smallest admissible two, because a two-deme island is the case in which the finite-deme
correction `D / (D - 1)` and several stepping-stone distinctions collapse. -/
def FiniteDemeCount.witness : FiniteDemeCount where
  value := 3
  value_gt_one := by norm_num

/-- Complete two-deme migration decomposition. -/
structure TwoDemeMigrationComponents where
  sourceToTarget : DirectionalMigrationRate
  targetToSource : DirectionalMigrationRate

/-- Symmetric lineage-flow component, the arithmetic midpoint of the two directions. -/
noncomputable def TwoDemeMigrationComponents.symmetric
    (m : TwoDemeMigrationComponents) : ℝ :=
  Descent.Core.midpoint m.sourceToTarget.value m.targetToSource.value

/-- Total lineage mixing rate, which controls the two-lineage separation process. -/
noncomputable def TwoDemeMigrationComponents.total
    (m : TwoDemeMigrationComponents) : ℝ :=
  m.sourceToTarget.value + m.targetToSource.value

/-- Directed imbalance; unlike the symmetric component it changes sign on relabelling. -/
noncomputable def TwoDemeMigrationComponents.net
    (m : TwoDemeMigrationComponents) : ℝ :=
  m.sourceToTarget.value - m.targetToSource.value

/-- Diploid-scaled total mixing rate. -/
noncomputable def TwoDemeMigrationComponents.scaledTotal
    (m : TwoDemeMigrationComponents) (effectiveSize : PositivePopulationSize) : ℝ :=
  4 * effectiveSize.value * m.total

/-- Finite-island correction applied to the symmetric component, kept separate from scaling. -/
noncomputable def TwoDemeMigrationComponents.finiteDemeEffective
    (m : TwoDemeMigrationComponents) (demeCount : FiniteDemeCount) : ℝ :=
  m.symmetric * Descent.Core.islandDemeCorrection demeCount.value

/-- Relabelling demes preserves total mixing. -/
theorem TwoDemeMigrationComponents.total_swap (m : TwoDemeMigrationComponents) :
    ({ sourceToTarget := m.targetToSource,
       targetToSource := m.sourceToTarget } : TwoDemeMigrationComponents).total = m.total := by
  unfold TwoDemeMigrationComponents.total
  ring

/-- Relabelling demes negates directed imbalance. -/
theorem TwoDemeMigrationComponents.net_swap (m : TwoDemeMigrationComponents) :
    ({ sourceToTarget := m.targetToSource,
       targetToSource := m.sourceToTarget } : TwoDemeMigrationComponents).net = -m.net := by
  unfold TwoDemeMigrationComponents.net
  ring

/-- The established effective symmetric migration is precisely this typed midpoint. -/
theorem TwoDemeMigrationComponents.symmetric_eq_effective (m : TwoDemeMigrationComponents) :
    m.symmetric = effectiveSymmetricMigration
      m.sourceToTarget.value m.targetToSource.value := rfl

end Descent.PopGen
