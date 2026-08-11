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
    (m : TwoDemeMigrationComponents) (effectiveSize : ℝ) : ℝ :=
  4 * effectiveSize * m.total

/-- Finite-island correction applied to the symmetric component, kept separate from scaling. -/
noncomputable def TwoDemeMigrationComponents.finiteDemeEffective
    (m : TwoDemeMigrationComponents) (demeCount : ℝ) : ℝ :=
  m.symmetric * Descent.Core.islandDemeCorrection demeCount

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
