/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory

assert_below Descent.Decision Descent.Program

/-!
# Inhabitants of the low-order LD rate, epoch and history structures

The corpus's arbitrary-deme low-order LD system is parameterized by three structures that
carry proof fields: `ManyDemeLDRates` (positive coalescence, nonnegative migration, mutation
and recombination, no self-migration), `LowOrderLDEpoch` (a nonnegative duration and a
generator whose affine constant row vanishes), and `LowOrderLDHistory` (an initial state whose
constant coordinate is one, followed by a list of instructions).  Theorems about the system
take one of them as a parameter.  This module builds one inhabitant of each from data alone,
with no hypothesis, so those theorems are known to range over a nonempty domain.

`ManyDemeLDRates.unitCoalescence D` is the neutral rate law on `D` demes with unit coalescence
rate and no migration, mutation or recombination.  `unitCoalescenceEpoch D` is its epoch of
zero duration, built with the corpus's own `ManyDemeLDRates.epoch`, and
`unitCoalescenceEpoch_propagator` records that it propagates nothing.  `constantOnlyHistory D`
starts from the state that carries only the affine constant and applies no instruction, and
`constantOnlyHistory_present` records that its present state is its initial state.

Scope.  These are witnesses of nonemptiness, not models of a population: nothing here is
calibrated, and nothing about realizability or propagation is proved.

## Empirical status

None.  The bodies here are constant rate functions and two definitional identities, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LowOrderLDWitnesses

open Coalescent

noncomputable section

/-- The neutral rate law on `D` demes: unit coalescence rate in every deme, and no migration,
mutation or recombination.  Every proof field holds for these constant rates, so the structure
is built from the deme count alone. -/
def ManyDemeLDRates.unitCoalescence (D : ℕ) : ManyDemeLDRates D where
  coalescence _ := 1
  migration _ _ := 0
  mutation _ := 0
  recombination _ := 0
  coalescence_pos _ := one_pos
  migration_nonneg _ _ := le_rfl
  migration_self _ := rfl
  mutation_nonneg _ := le_rfl
  recombination_nonneg _ := le_rfl

/-- The zero-duration epoch of the unit-coalescence rate law, built with the corpus's
`ManyDemeLDRates.epoch`. -/
def unitCoalescenceEpoch (D : ℕ) : LowOrderLDEpoch D :=
  (ManyDemeLDRates.unitCoalescence D).epoch 0 le_rfl

/-- A zero-duration epoch propagates nothing: its propagator is the identity matrix. -/
theorem unitCoalescenceEpoch_propagator (D : ℕ) : (unitCoalescenceEpoch D).propagator = 1 :=
  matrixExponential_zero _

/-- The history that starts from the state carrying only the affine constant coordinate and
applies no instruction. -/
def constantOnlyHistory (D : ℕ) : LowOrderLDHistory D where
  initial coordinate := coordinate.elim 1 fun _ ↦ 0
  initial_constant := rfl
  instructions := []

/-- A history with no instruction ends where it starts. -/
theorem constantOnlyHistory_present (D : ℕ) :
    (constantOnlyHistory D).present = (constantOnlyHistory D).initial := rfl

end

end Descent.Portability.LowOrderLDWitnesses
