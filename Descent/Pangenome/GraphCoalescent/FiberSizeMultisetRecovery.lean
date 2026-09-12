/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionLawIdentifiability
import Descent.Pangenome.GraphCoalescent.FiberSizeIdentifiability
import Descent.Pangenome.GraphCoalescent.FiberSizeSymmetricRecovery
import Descent.Pangenome.GraphCoalescent.LeadingCoefficientBridges

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The multiset of fiber sizes a compressed pangenome reveals, for widths two and three

`FiberSizeIdentifiability` proves that the connectivity cumulant `C_c(z)` of the fiber sizes
determines their product at every width, and `e_2`, `e_3` at width three on a panel of at least
four individuals. `FiberSizeSymmetricRecovery` recovers a multiset of naturals from its
elementary symmetric functions. `ConnectionLawIdentifiability` proves that the law of the reported
connection time carries exactly the cumulant. This file composes the three.

## Statement

For interfaces `s`, `s'` on the same panel of `n` individuals, with widths at least two:

- `width_eq_of_connectivityCumulant_eq`: equal cumulants give equal widths, since the degree of the
  cumulant is `n - w + 1` (`LeadingCoefficientBridges.natDegree_connectivityCumulant_graphKer_eq`).
- `fiberSizes_eq_of_cumulantOfSizes_eq_two`, `fiberSizes_eq_of_cumulantOfSizes_eq_three`: on two
  fibers, and on three fibers with `n ≥ 4`, sizes with equal totals and equal cumulants are the
  same multiset.
- `fiberSizes_graphKer_eq_of_connectivityCumulant_eq`: the same for the interfaces themselves, the
  multiset of sizes of the parts of `graphKer s`.
- `fiberSizes_graphKer_eq_of_map_connectionTime_eq`: **the law of the reported connection time
  determines the multiset of fiber sizes** at width two, and at width three when `n ≥ 4`.

## Scope

Widths two and three only. Whether the law determines the multiset of fiber sizes at width four or
more is open, and nothing here asserts either answer. The law is the image of `connectionTime`
under `trajectoryClockLaw`, as in `ReportedConnectionClock`.

## Empirical status

None. Every declaration here is an equality of finite multisets of natural numbers derived from an
equality of integer polynomials or of probability measures built from the corpus clock.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset FiberSizeSymmetricRecovery

open scoped Classical

noncomputable section

/-! ### Sizes on an index set -/

/-- **Two fibers: the cumulant determines the multiset of fiber sizes.**

Assumes: two fibers on each side, positive sizes, and equal totals. -/
theorem fiberSizes_eq_of_cumulantOfSizes_eq_two {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : Finset ι} {T' : Finset κ} {c : ι → ℕ} {c' : κ → ℕ} (hT : #T = 2) (hT' : #T' = 2)
    (hc : ∀ i ∈ T, 1 ≤ c i) (hc' : ∀ i ∈ T', 1 ≤ c' i) (hn : ∑ i ∈ T, c i = ∑ i ∈ T', c' i)
    (hC : cumulantOfSizes T c = cumulantOfSizes T' c') :
    Multiset.map c T.val = Multiset.map c' T'.val := by
  have hprod := prod_eq_of_cumulantOfSizes_eq hc hc' (hT.trans hT'.symm) (by omega) hn hC
  obtain ⟨i, j, hij, rfl, hmap⟩ := exists_map_val_eq_pair hT c
  obtain ⟨i', j', hij', rfl, hmap'⟩ := exists_map_val_eq_pair hT' c'
  rw [sum_pair hij, sum_pair hij'] at hn
  rw [prod_pair hij, prod_pair hij'] at hprod
  rw [hmap, hmap']
  exact pair_eq_of_esymm_eq hn hprod

/-- **Three fibers: the cumulant determines the multiset of fiber sizes** on a panel of at least
four individuals.

Assumes: three fibers on each side, positive sizes, equal totals, and a total of at least four. -/
theorem fiberSizes_eq_of_cumulantOfSizes_eq_three {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : Finset ι} {T' : Finset κ} {c : ι → ℕ} {c' : κ → ℕ} (hT : #T = 3) (hT' : #T' = 3)
    (hc : ∀ i ∈ T, 1 ≤ c i) (hc' : ∀ i ∈ T', 1 ≤ c' i) (hn : ∑ i ∈ T, c i = ∑ i ∈ T', c' i)
    (hn4 : 4 ≤ ∑ i ∈ T, c i) (hC : cumulantOfSizes T c = cumulantOfSizes T' c') :
    Multiset.map c T.val = Multiset.map c' T'.val := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl, hmap⟩ := exists_map_val_eq_triple hT c
  obtain ⟨x', y', z', hxy', hxz', hyz', rfl, hmap'⟩ := exists_map_val_eq_triple hT' c'
  have hx : x ∉ ({y, z} : Finset ι) := by simp [hxy, hxz]
  have hx' : x' ∉ ({y', z'} : Finset κ) := by simp [hxy', hxz']
  rw [sum_insert hx, sum_pair hyz, sum_insert hx', sum_pair hyz', ← add_assoc, ← add_assoc] at hn
  rw [sum_insert hx, sum_pair hyz, ← add_assoc] at hn4
  obtain ⟨h3, h2⟩ :=
    esymm_eq_of_cumulantOfSizes_eq_three hxy hxz hyz hxy' hxz' hyz' hc hc' hn hn4 hC
  have e1 : c x * c y + c y * c z + c z * c x = c x * c y + c x * c z + c y * c z := by ring
  have e2 : c' x' * c' y' + c' y' * c' z' + c' z' * c' x' =
      c' x' * c' y' + c' x' * c' z' + c' y' * c' z' := by ring
  rw [hmap, hmap']
  exact values_eq_of_esymm_eq hn (by rw [e1, e2]; exact h2) h3

/-! ### Interfaces -/

/-- The fibers of an interface are nonempty. -/
theorem fiberSizes_graphKer_pos {n : ℕ} (s : Fin n → Fin n) :
    ∀ t ∈ (Finpartition.ofSetoid (graphKer s)).parts, 1 ≤ #t := fun t ht ↦
  card_pos.mpr ((Finpartition.ofSetoid (graphKer s)).nonempty_of_mem_parts ht)

/-- The fibers of an interface cover the panel. -/
theorem sum_card_parts_graphKer {n : ℕ} (s : Fin n → Fin n) :
    ∑ t ∈ (Finpartition.ofSetoid (graphKer s)).parts, #t = n := by
  rw [(Finpartition.ofSetoid (graphKer s)).sum_card_parts, card_univ, Fintype.card_fin]

/-- An interface has as many fibers as its width. -/
theorem card_parts_graphKer {n : ℕ} (s : Fin n → Fin n) :
    #(Finpartition.ofSetoid (graphKer s)).parts = Linkage.width s := by
  rw [card_parts_ofSetoid, blocks_graphKer]

/-- **Equal cumulants give equal widths**, through the exact degree `n - w + 1`.

Assumes: both widths are at least two. -/
theorem width_eq_of_connectivityCumulant_eq {n : ℕ} {s s' : Fin n → Fin n}
    (hw : 2 ≤ Linkage.width s) (hw' : 2 ≤ Linkage.width s')
    (hC : connectivityCumulant (Finpartition.ofSetoid (graphKer s)) =
      connectivityCumulant (Finpartition.ofSetoid (graphKer s'))) :
    Linkage.width s = Linkage.width s' := by
  have h1 := natDegree_connectivityCumulant_graphKer_eq s hw
  have h2 := natDegree_connectivityCumulant_graphKer_eq s' hw'
  rw [hC, h2] at h1
  have hle := blocks_graphKer_le s
  have hle' := blocks_graphKer_le s'
  rw [blocks_graphKer] at hle hle'
  omega

/-- **The cumulant of an interface determines its fiber sizes** at width two, and at width three
on a panel of at least four individuals.

Assumes: both widths are at least two, and the first is two, or three with `n ≥ 4`. -/
theorem fiberSizes_graphKer_eq_of_connectivityCumulant_eq {n : ℕ} {s s' : Fin n → Fin n}
    (hw : 2 ≤ Linkage.width s) (hw' : 2 ≤ Linkage.width s')
    (hsmall : Linkage.width s = 2 ∨ (Linkage.width s = 3 ∧ 4 ≤ n))
    (hC : connectivityCumulant (Finpartition.ofSetoid (graphKer s)) =
      connectivityCumulant (Finpartition.ofSetoid (graphKer s'))) :
    Multiset.map card (Finpartition.ofSetoid (graphKer s)).parts.val =
      Multiset.map card (Finpartition.ofSetoid (graphKer s')).parts.val := by
  have hwid := width_eq_of_connectivityCumulant_eq hw hw' hC
  have hn : ∑ t ∈ (Finpartition.ofSetoid (graphKer s)).parts, #t =
      ∑ t ∈ (Finpartition.ofSetoid (graphKer s')).parts, #t := by
    rw [sum_card_parts_graphKer, sum_card_parts_graphKer]
  rw [connectivityCumulant_eq_cumulantOfSizes, connectivityCumulant_eq_cumulantOfSizes] at hC
  rcases hsmall with h2 | ⟨h3, hn4⟩
  · exact fiberSizes_eq_of_cumulantOfSizes_eq_two (by rw [card_parts_graphKer, h2])
      (by rw [card_parts_graphKer, ← hwid, h2]) (fiberSizes_graphKer_pos s)
      (fiberSizes_graphKer_pos s') hn hC
  · exact fiberSizes_eq_of_cumulantOfSizes_eq_three (by rw [card_parts_graphKer, h3])
      (by rw [card_parts_graphKer, ← hwid, h3]) (fiberSizes_graphKer_pos s)
      (fiberSizes_graphKer_pos s') hn (by rw [sum_card_parts_graphKer]; exact hn4) hC

/-- **The law of the reported connection time determines the multiset of fiber sizes**, at width
two, and at width three on a panel of at least four individuals.

Assumes: both widths are at least two, and the first is two, or three with `n ≥ 4`. -/
theorem fiberSizes_graphKer_eq_of_map_connectionTime_eq {n : ℕ} {s s' : Fin n → Fin n}
    (hw : 2 ≤ Linkage.width s) (hw' : 2 ≤ Linkage.width s')
    (hsmall : Linkage.width s = 2 ∨ (Linkage.width s = 3 ∧ 4 ≤ n))
    (hlaw : (trajectoryClockLaw n).map (connectionTime s) =
      (trajectoryClockLaw n).map (connectionTime s')) :
    Multiset.map card (Finpartition.ofSetoid (graphKer s)).parts.val =
      Multiset.map card (Finpartition.ofSetoid (graphKer s')).parts.val := by
  have hwn : Linkage.width s ≤ n := by
    have h := blocks_graphKer_le s
    rwa [blocks_graphKer] at h
  exact fiberSizes_graphKer_eq_of_connectivityCumulant_eq hw hw' hsmall
    ((ConnectionLawIdentifiability.map_connectionTime_eq_iff_connectivityCumulant_eq
      (hw.trans hwn) s s').mp hlaw)

end

end Descent.Pangenome.GraphCoalescent
