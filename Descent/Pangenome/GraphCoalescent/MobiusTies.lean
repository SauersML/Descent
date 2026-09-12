/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLaw
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulant
import Descent.Pangenome.GraphCoalescent.PartitionLatticeMobius

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# One Möbius coefficient of the partition lattice

The pangenome hidden-clock note uses the Möbius coefficient `μ(σ, ⊤) = (−1)^(|σ|−1) (|σ|−1)!`
of the partition lattice twice: in the connectivity cumulant (D2)–(D3) and in the connection law
(F4). Two modules proved its defining identity independently. `ConnectivityCumulant` defines
`mobiusCoefficient` and proves the identity on Mathlib's finite partitions, and
`MultiplicativeConnectionLaw` defines `topMobius` and proves it on the coalescent states
`Coalescent.ER n` through a counting argument. `PartitionLatticeMobius.mu_finpartition_top`
identifies `mobiusCoefficient` with the Möbius function of Mathlib's incidence algebra.

`PartitionLatticeMobius.topMobius_eq_mobiusCoefficient` shows that the two definitions agree.
This module adds `topMobius_blocks_eq_mu`: the coefficient `MultiplicativeConnectionLaw`
attaches to a coalescent state is the incidence-algebra Möbius value of that state's partition
against the top partition, so all three are one coefficient on the corpus state space.

## Empirical status

None. The bodies here are identities between definitions of one combinatorial coefficient, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent
open scoped Classical

/-- The Möbius coefficient of a coalescent state on a nonempty sample is the Möbius function of
Mathlib's incidence algebra on the partition lattice, evaluated at the state's partition and the
top partition. -/
theorem topMobius_blocks_eq_mu {n : ℕ} (hn : 0 < n) (σ : ER n) :
    topMobius (blocks σ) = IncidenceAlgebra.mu ℤ (Finpartition.ofSetoid σ) ⊤ := by
  rw [mu_finpartition_top (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (Finpartition.ofSetoid σ),
    card_parts_ofSetoid, topMobius_eq_mobiusCoefficient]

end Descent.Pangenome.GraphCoalescent
