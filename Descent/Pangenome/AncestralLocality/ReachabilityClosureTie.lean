/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.ClosureReachability
import Descent.Pangenome.AncestralLocality.HereditaryClosure

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Theorem 4 as a statement about Theorem 1's closure

`ClosureReachability` proves Theorem 4 of `ANCESTRAL_LOCALITY.md` with its own transcriptions of
the hereditary refinement step (`refinementStep`) and of autonomy (`Autonomous`).
`HereditaryClosure` builds the general objects of §3: the refinement `refinement K P`, the
hereditary closure `hereditaryClosure K P`, and Theorem 1's universal property. This module
identifies the two, so that Theorem 4 is a statement about Theorem 1's closure.

`refinementStep_eq_refinement`: the two refinement steps are the same setoid for every kernel and
partition, because the set summed in `refinementStep` is `block P z` (`block_eq_filter`). Their
iterates agree (`iterate_refinementStep_eq_iterate_refinement`), and the two transcriptions of
(2.2) agree (`autonomous_iff_hereditarilyAutonomous`).

`observeOn A` is the observation `π_A(x) = x|_A`, whose partition is `agreeOn A`
(`ker_observeOn`). A genome on `V` features has at least `|V|` states (`card_le_card_genomes`), so
the `|H|`-th iterate that defines `hereditaryClosure` lies past the stabilisation proved in
`ClosureReachability`. Hence Theorem 4 in Theorem 1's vocabulary, for `|A| ≥ 2` and nonnegative
rates: `hereditaryClosure (checkKernel r) (agreeOn A) = agreeOn (directedReach r A)`
(`hereditaryClosure_checkKernel_agreeOn`). For the observation itself, the closure of `π_A` is
`π_{Reach_G(A)}` (`hereditaryClosure_ker_observeOn`). For `|A| ≤ 1` the observation is its own
closure (`hereditaryClosure_checkKernel_agreeOn_of_card_le_one`).

Theorem 1's universal property then reads as a statement about reachability. For nonnegative rates
the checking kernel is a heredity kernel (`isHeredityKernel_checkKernel`), so for `|A| ≥ 2`:
`agreeOn (directedReach r A)` is the greatest autonomous partition refining `agreeOn A`
(`isGreatest_agreeOn_directedReach`); `π_{Reach_G(A)}` is hereditarily autonomous
(`hereditarilyAutonomous_observeOn_directedReach`); and every hereditarily autonomous observation
that determines `π_A` determines `π_{Reach_G(A)}`
(`ker_le_agreeOn_directedReach_of_hereditarilyAutonomous`). The failure of joins of §5.1 is
restated for the general notion (`not_hereditarilyAutonomous_pair`).

## Empirical status

None. The bodies here are identities between equivalence relations on a finite set and finite
sums of supplied rates; no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Classical

noncomputable section

section General

variable {H : Type*} [Fintype H]

/-- The set summed in `refinementStep` is the block of `HereditaryClosure`. -/
theorem block_eq_filter (P : Setoid H) (z : H) : block P z = univ.filter fun w ↦ P.r w z := by
  ext w
  rw [mem_block_iff, mem_filter]
  exact ⟨fun h ↦ ⟨mem_univ w, h⟩, fun h ↦ h.2⟩

/-- **The two refinement steps agree.** `ClosureReachability`'s transcription `refinementStep` of
(3.1) is `HereditaryClosure`'s `refinement`, for every kernel and every partition. -/
theorem refinementStep_eq_refinement (K : H → H → H → ℝ) (P : Setoid H) :
    refinementStep K P = refinement K P := by
  refine Setoid.ext fun x x' ↦ ?_
  rw [refinement_rel_iff]

/-- The iterates of the two refinement steps agree. -/
theorem iterate_refinementStep_eq_iterate_refinement (K : H → H → H → ℝ) (P : Setoid H)
    (n : ℕ) : (refinementStep K)^[n] P = (refinement K)^[n] P := by
  rw [show refinementStep K = refinement K from funext (refinementStep_eq_refinement K)]

/-- **The two transcriptions of autonomy (2.2) agree.** -/
theorem autonomous_iff_hereditarilyAutonomous {O : Type*} [DecidableEq O] (K : H → H → H → ℝ)
    (f : H → O) : Autonomous K f ↔ HereditarilyAutonomous K f := by
  have hfiber : ∀ o, univ.filter (fun w ↦ f w = o) = fiber f o := fun o ↦ by
    ext w
    rw [mem_filter, mem_fiber_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨mem_univ w, h⟩⟩
  simp only [Autonomous, HereditarilyAutonomous, kernelMass, hfiber]

end General

section Genomes

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genome on `V` features has at least `|V|` states. -/
theorem card_le_card_genomes : Fintype.card V ≤ Fintype.card (V → Bool) := by
  rw [Fintype.card_fun, Fintype.card_bool]
  exact Nat.lt_two_pow_self.le

/-- **The observation `π_A(x) = x|_A`** of the features in `A`. -/
def observeOn (A : Finset V) (x : V → Bool) : A → Bool :=
  fun a ↦ x a

omit [Fintype V] in
/-- The partition of `π_A` is `agreeOn A`. -/
theorem ker_observeOn (A : Finset V) : Setoid.ker (observeOn A) = agreeOn A := by
  refine Setoid.ext fun x x' ↦ ?_
  rw [Setoid.ker_def, agreeOn_r_iff]
  exact ⟨fun h l hl ↦ congrFun h ⟨l, hl⟩, fun h ↦ funext fun a ↦ h a a.2⟩

/-- **Theorem 4 in Theorem 1's vocabulary** (5.1), `|A| ≥ 2`. For nonnegative rates, the hereditary
closure of the checking kernel from `agreeOn A` is the partition by the reach of `A`. -/
theorem hereditaryClosure_checkKernel_agreeOn {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j)
    {A : Finset V} (hA : 2 ≤ A.card) :
    hereditaryClosure (checkKernel r) (agreeOn A) = agreeOn (directedReach r A) := by
  rw [hereditaryClosure, ← iterate_refinementStep_eq_iterate_refinement]
  exact iterate_refinementStep_agreeOn_eq_reach hr hA card_le_card_genomes

/-- **Theorem 4 in Theorem 1's vocabulary** (5.1), `|A| ≤ 1`: the observation is its own
hereditary closure. -/
theorem hereditaryClosure_checkKernel_agreeOn_of_card_le_one (r : V → V → ℝ) {A : Finset V}
    (hA : A.card ≤ 1) : hereditaryClosure (checkKernel r) (agreeOn A) = agreeOn A := by
  rw [hereditaryClosure, ← iterate_refinementStep_eq_iterate_refinement]
  exact iterate_refinementStep_agreeOn_of_card_le_one r hA _

/-- **The closure of `π_A` is `π_{Reach_G(A)}`** (Theorem 4, (5.1)), as partitions of the genomes,
for `|A| ≥ 2` and nonnegative rates. -/
theorem hereditaryClosure_ker_observeOn {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V}
    (hA : 2 ≤ A.card) :
    hereditaryClosure (checkKernel r) (Setoid.ker (observeOn A)) =
      Setoid.ker (observeOn (directedReach r A)) := by
  rw [ker_observeOn, ker_observeOn, hereditaryClosure_checkKernel_agreeOn hr hA]

/-- **The checking kernel is a heredity kernel** for nonnegative rates: every row is a probability
vector and the kernel does not see the order of the parents. -/
theorem isHeredityKernel_checkKernel {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) :
    IsHeredityKernel (checkKernel r) where
  nonneg x y z := by
    unfold checkKernel
    split_ifs
    · unfold copyKernel
      split_ifs <;> norm_num
    · refine div_nonneg (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ mul_nonneg (hr i j) ?_)
        (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hr i j)
      unfold eventKernel
      split_ifs <;> norm_num
  sum_eq_one x y := by
    rw [sum_checkKernel]
    split_ifs with hR
    · rw [sum_copyKernel]
      simp only [mem_univ, ↓reduceIte]
      norm_num
    · have hone : ∀ i j, ∑ w ∈ (univ : Finset (V → Bool)), eventKernel i j x y w = 1 := by
        intro i j
        rw [sum_eventKernel]
        simp only [mem_univ, ↓reduceIte]
        norm_num
      simp only [hone, mul_one]
      exact div_self hR
  symm x y z := by
    unfold checkKernel
    split_ifs
    · unfold copyKernel
      exact add_comm _ _
    · congr 1
      refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
      unfold eventKernel
      rw [add_comm]

/-- **Theorem 1 for reachability**, `|A| ≥ 2`. For nonnegative rates, `agreeOn (directedReach r A)`
is the greatest autonomous partition refining `agreeOn A`. -/
theorem isGreatest_agreeOn_directedReach {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V}
    (hA : 2 ≤ A.card) :
    IsGreatest {Q | IsAutonomous (checkKernel r) Q ∧ Q ≤ agreeOn A}
      (agreeOn (directedReach r A)) := by
  rw [← hereditaryClosure_checkKernel_agreeOn hr hA]
  exact isGreatest_hereditaryClosure (isHeredityKernel_checkKernel hr) (agreeOn A)

/-- **`π_{Reach_G(A)}` is hereditarily autonomous** for `|A| ≥ 2` and nonnegative rates: it is the
quotient map of Theorem 1's closure of `π_A`. -/
theorem hereditarilyAutonomous_observeOn_directedReach {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j)
    {A : Finset V} (hA : 2 ≤ A.card) :
    HereditarilyAutonomous (checkKernel r) (observeOn (directedReach r A)) := by
  rw [hereditarilyAutonomous_iff, ker_observeOn, ← hereditaryClosure_checkKernel_agreeOn hr hA]
  exact isAutonomous_hereditaryClosure (isHeredityKernel_checkKernel hr) _

/-- **Theorem 1's minimality for reachability.** For `|A| ≥ 2` and nonnegative rates, every
hereditarily autonomous observation that determines `π_A` determines `π_{Reach_G(A)}`.
Assumes: `HereditarilyAutonomous (checkKernel r) σ`. -/
theorem ker_le_agreeOn_directedReach_of_hereditarilyAutonomous {O' : Type*} [DecidableEq O']
    {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V} (hA : 2 ≤ A.card)
    {σ : (V → Bool) → O'} (hσ : HereditarilyAutonomous (checkKernel r) σ)
    (hσA : Setoid.ker σ ≤ agreeOn A) : Setoid.ker σ ≤ agreeOn (directedReach r A) := by
  rw [← hereditaryClosure_checkKernel_agreeOn hr hA]
  exact le_hereditaryClosure_of_isAutonomous ((hereditarilyAutonomous_iff _ σ).mp hσ) hσA

/-- **Joins of autonomous features fail in Theorem 1's sense** (§5.1). For nonnegative rates, the
pair `(π_i, π_k)` is not hereditarily autonomous whenever some feature outside `{i, k}` is a
checker of `i` or of `k`. -/
theorem not_hereditarilyAutonomous_pair {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {i k v : V}
    (hik : i ≠ k) (hvi : v ≠ i) (hvk : v ≠ k) (hv : v ∈ outNbhd r {i, k}) :
    ¬ HereditarilyAutonomous (checkKernel r) (fun x : V → Bool ↦ (x i, x k)) := by
  rw [← autonomous_iff_hereditarilyAutonomous]
  exact not_autonomous_pair hr hik hvi hvk hv

end Genomes

end

end Descent.Pangenome.AncestralLocality
