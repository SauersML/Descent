/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Descent.Pangenome.AncestralLocality.HeredityKernel
import Mathlib.SetTheory.Cardinal.Finite

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Hereditary closure: the minimal hereditary context of an observation

`ANCESTRAL_LOCALITY.md` §3. An observation of genome states need not predict how it reproduces:
the observed offspring law can depend on unobserved parental information. This module computes
the least information that must be added, and characterizes autonomy operationally.

**The refinement (3.1).** `refinement K P` is the note's `Φ_K(P)`: two states stay together when
they are together in `P` and give every block of `P` the same mass against every partner
(`refinement_rel_iff`). It only refines (`refinement_le`), and its fixed points are exactly the
partitions whose block masses are invariant in the first parent (`refinement_eq_self_iff`).

**The iteration (3.2).** A strict refinement of a partition of a finite set adds a block
(`card_quotient_lt_of_lt`) and no partition has more than `|H|` blocks (`card_quotient_le`), so a
refining map reaches a fixed point within `|H| - |P|` steps (`iterate_fixed_of_card_le`).
`hereditaryClosure K P` is the `|H|`-th iterate; `refinement_hereditaryClosure` shows it is a
fixed point and `hereditaryClosure_eq_iterate` that it is already the `(|H| - |P|)`-th iterate.
For `H = Fin n` this is a statement about states of `Coalescent.ER n`: closure only adds blocks
and never more than `n` (`blocks_le_blocks_hereditaryClosure`).

**Theorem 1 (minimal hereditary context).** `isAutonomous_hereditaryClosure`: `P_*` is
autonomous, since at a fixed point block masses are invariant in the first parent and symmetry
of the kernel gives the second (`isAutonomous_of_refinement_eq`). `hereditaryClosure_le`: `P_*`
refines `P`. `le_hereditaryClosure_of_isAutonomous`: every autonomous `Q ≤ P` satisfies
`Q ≤ P_*`, because summing `Q`-block masses over a `P`-block (`sum_block_eq_of_le`) puts `Q`
below each iterate (`le_refinement_of_isAutonomous`). Together, `isGreatest_hereditaryClosure`:
`P_*` is the greatest autonomous partition below `P`. For an observation `π`, the quotient map
`Cl_K(π)` onto `H/P_*` is hereditarily autonomous (`hereditarilyAutonomous_closureMap`), and
every hereditarily autonomous observation determining `π` determines it
(`ker_le_hereditaryClosure_of_hereditarilyAutonomous`).

**Theorem 2 (operational characterization).** `hereditarilyAutonomous_iff_pushforward_reproduce`:
for a heredity kernel, `π` is hereditarily autonomous iff `π_# R_K(p)` depends only on `π_# p`
for every probability vector `p`. The converse direction polarizes with `δ_x`, which fixes
`K(x,x;B)` as a function of `πx`, and with `½δ_x + ½δ_y`, whose offspring law is
`¼K(x,x;B) + ½K(x,y;B) + ¼K(y,y;B)`. Its contrapositive is
`exists_pushforward_eq_reproduce_ne_of_not_autonomous`: failure of autonomy yields two
populations with the same observed law and different observed offspring laws.

**§3.1 Representation invariance.** A relabeling `g : H ≃ H'` transports the kernel
(`transportKernel`, a heredity kernel by `isHeredityKernel_transportKernel`), every refinement
step (`refinement_transportKernel`), autonomy (`isAutonomous_transportKernel_iff`) and the
hereditary closure (`hereditaryClosure_transportKernel`, and for observations
`hereditaryClosure_ker_comp_symm`).

**§3.2 Joins.** On states `(a, b, h) : Bool × Bool × Bool`, the gated exchange `gatedExchange`
lets a child take the other parent's `a` only when the parents agree at `h`. Its two-child kernel
`gatedKernel` makes `observeA` and `observeB` autonomous (`hereditarilyAutonomous_observeA`,
`hereditarilyAutonomous_observeB`) while their joint observation is not
(`not_hereditarilyAutonomous_observeAB`); `exists_autonomous_pair_not_autonomous_join` packages
the three.

Scope. The closure is defined as the `|H|`-th iterate; the note's `P_*` is the first fixed point,
and the two agree by `hereditaryClosure_eq_iterate`. The §3.2 example uses the one-rule kernel of
the note's §5.2 witness on three binary features; no general statement about joins beyond this
counterexample is claimed. Theorem 2 is stated for real probability vectors on a finite state
set, and the populations in its converse are explicit mixtures of at most two point masses.

## Empirical status

None. The bodies here are equivalence relations on a finite set and finite sums of supplied real
numbers; the kernel is a supplied function and no measurement can bear on these statements.
-/

namespace Descent.Pangenome.AncestralLocality

noncomputable section

variable {H : Type*} [Fintype H]

/-! ### Counting blocks -/

/-- A partition of a finite set has at most as many blocks as the set has elements. -/
theorem card_quotient_le (P : Setoid H) : Nat.card (Quotient P) ≤ Fintype.card H := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective (Quotient.mk P)
    fun q ↦ Quotient.inductionOn q fun a ↦ ⟨a, rfl⟩

/-- A coarser partition has at most as many blocks. -/
theorem card_quotient_le_of_le {Q P : Setoid H} (hQP : Q ≤ P) :
    Nat.card (Quotient P) ≤ Nat.card (Quotient Q) :=
  Nat.card_le_card_of_surjective
    (Quotient.lift (Quotient.mk P) fun _ _ h ↦ Quotient.sound (hQP h))
    fun q ↦ Quotient.inductionOn q fun a ↦ ⟨Quotient.mk Q a, rfl⟩

/-- **A strict refinement adds a block.** -/
theorem card_quotient_lt_of_lt {Q P : Setoid H} (hQP : Q < P) :
    Nat.card (Quotient P) < Nat.card (Quotient Q) := by
  let g : Quotient Q → Quotient P :=
    Quotient.lift (Quotient.mk P) fun _ _ h ↦ Quotient.sound (hQP.le h)
  have hg : Function.Surjective g :=
    fun q ↦ Quotient.inductionOn q fun a ↦ ⟨Quotient.mk Q a, rfl⟩
  refine lt_of_le_of_ne (Nat.card_le_card_of_surjective g hg) fun hcard ↦ hQP.ne ?_
  have hinj := (hg.bijective_of_nat_card_le hcard.ge).1
  refine le_antisymm hQP.le fun x y hxy ↦ Quotient.exact (hinj ?_)
  show Quotient.mk P x = Quotient.mk P y
  exact Quotient.sound hxy

/-! ### Iterating a refining map -/

/-- Once a map fixes an iterate, the later iterates stay there. -/
theorem iterate_add_eq_of_fixed {f : Setoid H → Setoid H} {P : Setoid H} {r : ℕ}
    (hr : f (f^[r] P) = f^[r] P) (s : ℕ) : f^[s + r] P = f^[r] P := by
  induction s with
  | zero => rw [Nat.zero_add]
  | succ s ih => rw [Nat.add_right_comm, Function.iterate_succ_apply', ih, hr]

/-- **Termination of refinement** (3.2). A map on partitions of a finite set that only refines
reaches a fixed point after `N` steps from `P` whenever `|H| ≤ |P| + N`: every strict step adds a
block, and there is no room for `N + 1` of them. -/
theorem iterate_fixed_of_card_le {f : Setoid H → Setoid H} (hf : ∀ Q, f Q ≤ Q) (P : Setoid H)
    {N : ℕ} (hN : Fintype.card H ≤ Nat.card (Quotient P) + N) : f (f^[N] P) = f^[N] P := by
  by_contra hne
  have hstrict : ∀ r ≤ N, f (f^[r] P) ≠ f^[r] P := by
    intro r hr hfix
    have hs : N = (N - r) + r := by omega
    apply hne
    rw [hs, iterate_add_eq_of_fixed hfix]
    exact hfix
  have hcount : ∀ r ≤ N + 1, Nat.card (Quotient P) + r ≤ Nat.card (Quotient (f^[r] P)) := by
    intro r
    induction r with
    | zero => exact fun _ ↦ by simp
    | succ r ih =>
      intro hr
      have hlt : f^[r + 1] P < f^[r] P := by
        rw [Function.iterate_succ_apply']
        exact lt_of_le_of_ne (hf _) (hstrict r (by omega))
      have h1 := card_quotient_lt_of_lt hlt
      have h2 := ih (by omega)
      omega
  have h1 := hcount (N + 1) le_rfl
  have h2 := card_quotient_le (f^[N + 1] P)
  omega

/-! ### The refinement operator -/

/-- **The refinement `Φ_K`** (3.1): `x ≡ x'` iff `x ≡_P x'` and `K(x,y;B) = K(x',y;B)` for every
state `y` and every block `B` of `P`. -/
def refinement (K : H → H → H → ℝ) (P : Setoid H) : Setoid H where
  r x x' := P x x' ∧ ∀ y w, blockMass K P x y w = blockMass K P x' y w
  iseqv :=
    { refl := fun x ↦ ⟨P.refl' x, fun _ _ ↦ rfl⟩
      symm := fun h ↦ ⟨P.symm' h.1, fun y w ↦ (h.2 y w).symm⟩
      trans := fun h h' ↦ ⟨P.trans' h.1 h'.1, fun y w ↦ (h.2 y w).trans (h'.2 y w)⟩ }

theorem refinement_rel_iff (K : H → H → H → ℝ) (P : Setoid H) (x x' : H) :
    refinement K P x x' ↔ P x x' ∧ ∀ y w, blockMass K P x y w = blockMass K P x' y w :=
  Iff.rfl

/-- `Φ_K` refines. -/
theorem refinement_le (K : H → H → H → ℝ) (P : Setoid H) : refinement K P ≤ P :=
  fun x x' h ↦ ((refinement_rel_iff K P x x').mp h).1

/-- The fixed points of `Φ_K` are the partitions whose block masses are invariant in the first
parent. -/
theorem refinement_eq_self_iff (K : H → H → H → ℝ) (P : Setoid H) :
    refinement K P = P ↔
      ∀ ⦃x x'⦄, P x x' → ∀ y w, blockMass K P x y w = blockMass K P x' y w := by
  constructor
  · intro h x x' hx
    have hx' : refinement K P x x' := by
      rw [h]
      exact hx
    exact ((refinement_rel_iff K P x x').mp hx').2
  · intro h
    exact le_antisymm (refinement_le K P) fun x x' hx ↦
      (refinement_rel_iff K P x x').mpr ⟨hx, h hx⟩

/-- **Autonomy at a fixed point.** If `Φ_K` fixes `P`, block masses are invariant in the first
parent, and symmetry of the kernel gives the second. Assumes: `IsHeredityKernel K`. -/
theorem isAutonomous_of_refinement_eq {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    {P : Setoid H} (hP : refinement K P = P) : IsAutonomous K P := by
  intro x x' y y' hx hy w
  have hfix := (refinement_eq_self_iff K P).mp hP
  calc blockMass K P x y w = blockMass K P x' y w := hfix hx y w
    _ = blockMass K P y x' w := blockMass_symm hK P x' y w
    _ = blockMass K P y' x' w := hfix hy x' w
    _ = blockMass K P x' y' w := blockMass_symm hK P y' x' w

/-- **Summing over a coarser block.** If two functions have equal sums over every block of `Q`,
they have equal sums over every block of a coarser `P`, since a `P`-block is a union of
`Q`-blocks. -/
theorem sum_block_eq_of_le {Q P : Setoid H} (hQP : Q ≤ P) {f g : H → ℝ}
    (h : ∀ u, ∑ z ∈ block Q u, f z = ∑ z ∈ block Q u, g z) (w : H) :
    ∑ z ∈ block P w, f z = ∑ z ∈ block P w, g z := by
  classical
  rw [← Finset.sum_fiberwise (block P w) (Quotient.mk Q) f,
    ← Finset.sum_fiberwise (block P w) (Quotient.mk Q) g]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  by_cases hu : P u w
  · have hset : {z ∈ block P w | Quotient.mk Q z = Quotient.mk Q u} = block Q u := by
      ext z
      rw [Finset.mem_filter, mem_block_iff, mem_block_iff]
      exact ⟨fun hz ↦ Quotient.exact hz.2, fun hz ↦ ⟨P.trans' (hQP hz) hu, Quotient.sound hz⟩⟩
    rw [hset, h u]
  · have hz : ∀ z ∈ {z ∈ block P w | Quotient.mk Q z = Quotient.mk Q u}, False := by
      intro z hz
      rw [Finset.mem_filter, mem_block_iff] at hz
      exact hu (P.trans' (P.symm' (hQP (Quotient.exact hz.2))) hz.1)
    rw [Finset.sum_eq_zero fun z hz' ↦ (hz z hz').elim,
      Finset.sum_eq_zero fun z hz' ↦ (hz z hz').elim]

/-- **Autonomous partitions below `P` stay below `Φ_K(P)`**: sum the `Q`-block masses over a
`P`-block. Assumes: `IsAutonomous K Q`. -/
theorem le_refinement_of_isAutonomous {K : H → H → H → ℝ} {Q P : Setoid H}
    (hQ : IsAutonomous K Q) (hQP : Q ≤ P) : Q ≤ refinement K P := fun x x' hx ↦
  (refinement_rel_iff K P x x').mpr ⟨hQP hx, fun y w ↦
    sum_block_eq_of_le hQP (f := K x y) (g := K x' y) (fun u ↦ hQ hx (Q.refl' y) u) w⟩

/-! ### The hereditary closure and Theorem 1 -/

/-- **The hereditary closure `P_*`** (3.2): `Φ_K` iterated `|H|` times from `P`. -/
def hereditaryClosure (K : H → H → H → ℝ) (P : Setoid H) : Setoid H :=
  (refinement K)^[Fintype.card H] P

theorem iterate_refinement_le (K : H → H → H → ℝ) (P : Setoid H) (r : ℕ) :
    (refinement K)^[r] P ≤ P := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (refinement_le K _) ih

/-- **Theorem 1, refinement.** `P_*` refines `P`. -/
theorem hereditaryClosure_le (K : H → H → H → ℝ) (P : Setoid H) : hereditaryClosure K P ≤ P :=
  iterate_refinement_le K P _

/-- **`P_*` is a fixed point of `Φ_K`.** -/
theorem refinement_hereditaryClosure (K : H → H → H → ℝ) (P : Setoid H) :
    refinement K (hereditaryClosure K P) = hereditaryClosure K P :=
  iterate_fixed_of_card_le (refinement_le K) P (Nat.le_add_left _ _)

/-- **At most `|H| - |P|` strict refinements** (3.2): `P_*` is already the `(|H| - |P|)`-th
iterate. -/
theorem hereditaryClosure_eq_iterate (K : H → H → H → ℝ) (P : Setoid H) :
    hereditaryClosure K P = (refinement K)^[Fintype.card H - Nat.card (Quotient P)] P := by
  have hfix := iterate_fixed_of_card_le (refinement_le K) P
    (N := Fintype.card H - Nat.card (Quotient P)) (by omega)
  have hs : Fintype.card H =
      (Fintype.card H - (Fintype.card H - Nat.card (Quotient P))) +
        (Fintype.card H - Nat.card (Quotient P)) := by
    have := card_quotient_le P
    omega
  unfold hereditaryClosure
  conv_lhs => rw [hs]
  exact iterate_add_eq_of_fixed hfix _

/-- **In the coalescent's vocabulary.** For states `Fin n` a partition is a state of
`Coalescent.ER n`; hereditary closure only adds blocks, and never more than `n`. -/
theorem blocks_le_blocks_hereditaryClosure {n : ℕ} (K : Fin n → Fin n → Fin n → ℝ)
    (P : Coalescent.ER n) :
    Coalescent.blocks P ≤ Coalescent.blocks (hereditaryClosure K P) ∧
      Coalescent.blocks (hereditaryClosure K P) ≤ n := by
  refine ⟨card_quotient_le_of_le (hereditaryClosure_le K P), ?_⟩
  have h := card_quotient_le (hereditaryClosure K P)
  rwa [Fintype.card_fin] at h

/-- **Theorem 1, autonomy.** The hereditary closure is autonomous.
Assumes: `IsHeredityKernel K`. -/
theorem isAutonomous_hereditaryClosure {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    (P : Setoid H) : IsAutonomous K (hereditaryClosure K P) :=
  isAutonomous_of_refinement_eq hK (refinement_hereditaryClosure K P)

/-- Autonomous partitions below `P` stay below every iterate of `Φ_K`.
Assumes: `IsAutonomous K Q`. -/
theorem le_iterate_refinement_of_isAutonomous {K : H → H → H → ℝ} {Q P : Setoid H}
    (hQ : IsAutonomous K Q) (hQP : Q ≤ P) (r : ℕ) : Q ≤ (refinement K)^[r] P := by
  induction r with
  | zero => exact hQP
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact le_refinement_of_isAutonomous hQ ih

/-- **Theorem 1, minimality.** Every autonomous partition refining `P` refines `P_*`.
Assumes: `IsAutonomous K Q`. -/
theorem le_hereditaryClosure_of_isAutonomous {K : H → H → H → ℝ} {Q P : Setoid H}
    (hQ : IsAutonomous K Q) (hQP : Q ≤ P) : Q ≤ hereditaryClosure K P :=
  le_iterate_refinement_of_isAutonomous hQ hQP _

/-- **Theorem 1 (minimal hereditary context).** `P_*` is the greatest autonomous partition
refining `P`. Assumes: `IsHeredityKernel K`. -/
theorem isGreatest_hereditaryClosure {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    (P : Setoid H) : IsGreatest {Q | IsAutonomous K Q ∧ Q ≤ P} (hereditaryClosure K P) :=
  ⟨⟨isAutonomous_hereditaryClosure hK P, hereditaryClosure_le K P⟩,
    fun _ hQ ↦ le_hereditaryClosure_of_isAutonomous hQ.1 hQ.2⟩

open Classical in
/-- **Theorem 1 for observations.** The quotient map `Cl_K(π) : H → H/P_*` is hereditarily
autonomous. Assumes: `IsHeredityKernel K`. -/
theorem hereditarilyAutonomous_closureMap {O : Type*} {K : H → H → H → ℝ}
    (hK : IsHeredityKernel K) (π : H → O) :
    HereditarilyAutonomous K (Quotient.mk (hereditaryClosure K (Setoid.ker π))) := by
  have hker : Setoid.ker (Quotient.mk (hereditaryClosure K (Setoid.ker π))) =
      hereditaryClosure K (Setoid.ker π) :=
    Setoid.ext fun _ _ ↦ ⟨Quotient.exact, Quotient.sound⟩
  rw [hereditarilyAutonomous_iff, hker]
  exact isAutonomous_hereditaryClosure hK _

/-- **Theorem 1, minimality for observations.** A hereditarily autonomous observation `σ` that
determines `π` determines `Cl_K(π)`. Assumes: `HereditarilyAutonomous K σ`. -/
theorem ker_le_hereditaryClosure_of_hereditarilyAutonomous {O O' : Type*} [DecidableEq O']
    {K : H → H → H → ℝ} {π : H → O} {σ : H → O'} (hσ : HereditarilyAutonomous K σ)
    (hσπ : Setoid.ker σ ≤ Setoid.ker π) : Setoid.ker σ ≤ hereditaryClosure K (Setoid.ker π) :=
  le_hereditaryClosure_of_isAutonomous ((hereditarilyAutonomous_iff K σ).mp hσ) hσπ

/-! ### Theorem 2 -/

/-- **Theorem 2 (operational characterization).** For a heredity kernel, `π` is hereditarily
autonomous iff the observed next generation `π_# R_K(p)` depends on the population `p` only
through its observed law `π_# p`. The converse polarizes with `δ_x` and `½δ_x + ½δ_y`.
Assumes: `IsHeredityKernel K`. -/
theorem hereditarilyAutonomous_iff_pushforward_reproduce {O : Type*} [Fintype O]
    [DecidableEq O] [DecidableEq H] {K : H → H → H → ℝ} (hK : IsHeredityKernel K) (π : H → O) :
    HereditarilyAutonomous K π ↔
      ∀ p ∈ stdSimplex ℝ H, ∀ q ∈ stdSimplex ℝ H, pushforward π p = pushforward π q →
        pushforward π (reproduce K p) = pushforward π (reproduce K q) := by
  constructor
  · rintro ⟨Kbar, hKbar⟩ p _ q _ hpq
    funext o
    simp only [pushforward_reproduce, hKbar]
    rw [sum_sum_mul_comp_eq_sum_sum_pushforward π p fun a b ↦ Kbar a b o,
      sum_sum_mul_comp_eq_sum_sum_pushforward π q fun a b ↦ Kbar a b o, hpq]
  · intro hR
    have hdiag : ∀ ⦃x x' : H⦄, π x = π x' → ∀ o,
        kernelMass K x x (fiber π o) = kernelMass K x' x' (fiber π o) := by
      intro x x' hx o
      have h := congrFun (hR (pointMass x) (pointMass_mem_stdSimplex x) (pointMass x')
        (pointMass_mem_stdSimplex x')
        (by rw [pushforward_pointMass, pushforward_pointMass, hx])) o
      rwa [pushforward_reproduce, pushforward_reproduce, sum_sum_pointMass,
        sum_sum_pointMass] at h
    rw [hereditarilyAutonomous_iff]
    intro x x' y y' hx hy w
    have hx' : π x = π x' := Setoid.ker_def.mp hx
    have hy' : π y = π y' := Setoid.ker_def.mp hy
    have h := congrFun (hR (pairMidpoint x y) (pairMidpoint_mem_stdSimplex x y)
      (pairMidpoint x' y') (pairMidpoint_mem_stdSimplex x' y')
      (by rw [pushforward_pairMidpoint, pushforward_pairMidpoint, hx', hy'])) (π w)
    rw [pushforward_reproduce, pushforward_reproduce, sum_sum_pairMidpoint,
      sum_sum_pairMidpoint, hdiag hx' (π w), hdiag hy' (π w), kernelMass_symm hK y x,
      kernelMass_symm hK y' x'] at h
    simp only [blockMass, block_ker]
    linarith

/-- **Failure of autonomy is observable.** If `π` is not hereditarily autonomous, two
populations with the same observed law have different observed offspring laws.
Assumes: `IsHeredityKernel K`. -/
theorem exists_pushforward_eq_reproduce_ne_of_not_autonomous {O : Type*} [Fintype O]
    [DecidableEq O] [DecidableEq H] {K : H → H → H → ℝ} (hK : IsHeredityKernel K) {π : H → O}
    (h : ¬ HereditarilyAutonomous K π) :
    ∃ p ∈ stdSimplex ℝ H, ∃ q ∈ stdSimplex ℝ H, pushforward π p = pushforward π q ∧
      pushforward π (reproduce K p) ≠ pushforward π (reproduce K q) := by
  rw [hereditarilyAutonomous_iff_pushforward_reproduce hK π] at h
  push_neg at h
  exact h

/-! ### Representation invariance (§3.1) -/

section Transport

variable {H' : Type*} [Fintype H']

/-- A kernel transported along a relabeling `g : H ≃ H'`. -/
def transportKernel (g : H ≃ H') (K : H → H → H → ℝ) (x y z : H') : ℝ :=
  K (g.symm x) (g.symm y) (g.symm z)

/-- A transported heredity kernel is a heredity kernel. Assumes: `IsHeredityKernel K`. -/
theorem isHeredityKernel_transportKernel (g : H ≃ H') {K : H → H → H → ℝ}
    (hK : IsHeredityKernel K) : IsHeredityKernel (transportKernel g K) where
  nonneg _ _ _ := hK.nonneg _ _ _
  sum_eq_one x y := by
    rw [← hK.sum_eq_one (g.symm x) (g.symm y)]
    exact Equiv.sum_comp g.symm (K (g.symm x) (g.symm y))
  symm _ _ _ := hK.symm _ _ _

/-- Block masses of a transported kernel are block masses of the original. -/
theorem blockMass_transportKernel (g : H ≃ H') (K : H → H → H → ℝ) (P : Setoid H)
    (x y w : H') :
    blockMass (transportKernel g K) (P.comap g.symm) x y w =
      blockMass K P (g.symm x) (g.symm y) (g.symm w) := by
  refine Finset.sum_equiv g.symm (fun z ↦ ?_) fun z _ ↦ rfl
  simp only [mem_block_iff, Setoid.comap_rel]

/-- **Relabeling transports one refinement step.** -/
theorem refinement_transportKernel (g : H ≃ H') (K : H → H → H → ℝ) (P : Setoid H) :
    refinement (transportKernel g K) (P.comap g.symm) = (refinement K P).comap g.symm := by
  ext x x'
  simp only [Setoid.comap_rel, refinement_rel_iff, blockMass_transportKernel]
  refine and_congr_right fun _ ↦ ⟨fun h y w ↦ ?_, fun h y w ↦ h _ _⟩
  simpa using h (g y) (g w)

theorem iterate_refinement_transportKernel (g : H ≃ H') (K : H → H → H → ℝ) (P : Setoid H)
    (r : ℕ) :
    (refinement (transportKernel g K))^[r] (P.comap g.symm) =
      ((refinement K)^[r] P).comap g.symm := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      refinement_transportKernel]

/-- **§3.1 Representation invariance.** Relabeling the states transports the hereditary
closure. -/
theorem hereditaryClosure_transportKernel (g : H ≃ H') (K : H → H → H → ℝ) (P : Setoid H) :
    hereditaryClosure (transportKernel g K) (P.comap g.symm) =
      (hereditaryClosure K P).comap g.symm := by
  unfold hereditaryClosure
  rw [← Fintype.card_congr g, iterate_refinement_transportKernel]

/-- Relabeling transports autonomy. -/
theorem isAutonomous_transportKernel_iff (g : H ≃ H') (K : H → H → H → ℝ) (P : Setoid H) :
    IsAutonomous (transportKernel g K) (P.comap g.symm) ↔ IsAutonomous K P := by
  constructor
  · intro h x x' y y' hx hy w
    have hx' : P.comap g.symm (g x) (g x') := by simpa [Setoid.comap_rel] using hx
    have hy' : P.comap g.symm (g y) (g y') := by simpa [Setoid.comap_rel] using hy
    simpa [blockMass_transportKernel] using h hx' hy' (g w)
  · intro h x x' y y' hx hy w
    rw [blockMass_transportKernel, blockMass_transportKernel]
    exact h hx hy _

/-- **§3.1 for observations.** Reading an observation through a relabeling transports its
hereditary closure. -/
theorem hereditaryClosure_ker_comp_symm (g : H ≃ H') (K : H → H → H → ℝ) {O : Type*}
    (π : H → O) :
    hereditaryClosure (transportKernel g K) (Setoid.ker (π ∘ g.symm)) =
      (hereditaryClosure K (Setoid.ker π)).comap g.symm := by
  have hker : Setoid.ker (π ∘ g.symm) = (Setoid.ker π).comap g.symm :=
    Setoid.ext fun _ _ ↦ Iff.rfl
  rw [hker, hereditaryClosure_transportKernel]

end Transport

/-! ### Joins of autonomous observations (§3.2) -/

/-- **The gated exchange** on states `(a, b, h)`: the ordered child of `x` and `y` takes `y`'s
feature `a` exactly when the parents agree at the checker `h`, and is `x` otherwise. -/
def gatedExchange (x y : Bool × Bool × Bool) : Bool × Bool × Bool :=
  if x.2.2 = y.2.2 then (y.1, x.2.1, x.2.2) else x

/-- The two-child kernel of the gated exchange: the note's §5.2 witness, one checking rule on
three binary features. -/
def gatedKernel : Bool × Bool × Bool → Bool × Bool × Bool → Bool × Bool × Bool → ℝ :=
  childKernel gatedExchange

/-- The observed feature `a`. -/
def observeA (x : Bool × Bool × Bool) : Bool :=
  x.1

/-- The observed feature `b`. -/
def observeB (x : Bool × Bool × Bool) : Bool :=
  x.2.1

/-- Feature `a` is copied from one of the two parents with probability one half each. -/
theorem kernelMass_gatedKernel_observeA (x y : Bool × Bool × Bool) (o : Bool) :
    kernelMass gatedKernel x y (fiber observeA o) =
      (if x.1 = o then 1 / 2 else 0) + if y.1 = o then 1 / 2 else 0 := by
  simp only [gatedKernel, kernelMass_childKernel, mem_fiber_iff, observeA]
  obtain ⟨a, b, h⟩ := x
  obtain ⟨a', b', h'⟩ := y
  by_cases hh : h = h'
  · subst hh
    have hxy : gatedExchange (a, b, h) (a', b', h) = (a', b, h) := if_pos rfl
    have hyx : gatedExchange (a', b', h) (a, b, h) = (a, b', h) := if_pos rfl
    simp only [hxy, hyx]
    exact add_comm _ _
  · have hxy : gatedExchange (a, b, h) (a', b', h') = (a, b, h) := if_neg hh
    have hyx : gatedExchange (a', b', h') (a, b, h) = (a', b', h') := if_neg (Ne.symm hh)
    simp only [hxy, hyx]

/-- Feature `b` is never exchanged. -/
theorem kernelMass_gatedKernel_observeB (x y : Bool × Bool × Bool) (o : Bool) :
    kernelMass gatedKernel x y (fiber observeB o) =
      (if x.2.1 = o then 1 / 2 else 0) + if y.2.1 = o then 1 / 2 else 0 := by
  have hxy : (gatedExchange x y).2.1 = x.2.1 := by
    unfold gatedExchange
    split_ifs <;> rfl
  have hyx : (gatedExchange y x).2.1 = y.2.1 := by
    unfold gatedExchange
    split_ifs <;> rfl
  simp only [gatedKernel, kernelMass_childKernel, mem_fiber_iff, observeB, hxy, hyx]

/-- **Feature `a` alone is autonomous.** -/
theorem hereditarilyAutonomous_observeA : HereditarilyAutonomous gatedKernel observeA :=
  ⟨fun a b o ↦ (if a = o then 1 / 2 else 0) + if b = o then 1 / 2 else 0,
    kernelMass_gatedKernel_observeA⟩

/-- **Feature `b` alone is autonomous.** -/
theorem hereditarilyAutonomous_observeB : HereditarilyAutonomous gatedKernel observeB :=
  ⟨fun a b o ↦ (if a = o then 1 / 2 else 0) + if b = o then 1 / 2 else 0,
    kernelMass_gatedKernel_observeB⟩

/-- **The joint observation of `a` and `b` is not autonomous.** Parents `(0,0,0)` and `(0,0,1)`
look alike, but against the partner `(1,1,0)` the first exchanges and the second does not, so
the observed configuration `(1,0)` receives mass `½` from one pair and `0` from the other. -/
theorem not_hereditarilyAutonomous_observeAB :
    ¬ HereditarilyAutonomous gatedKernel fun x ↦ (observeA x, observeB x) := by
  rw [hereditarilyAutonomous_iff]
  intro h
  have hne := h (show Setoid.ker (fun x ↦ (observeA x, observeB x))
      (false, false, false) (false, false, true) from rfl)
    (show Setoid.ker (fun x ↦ (observeA x, observeB x)) (true, true, false) (true, true, false)
      from rfl) (true, false, false)
  simp only [blockMass, block_ker, gatedKernel, kernelMass_childKernel, mem_fiber_iff] at hne
  norm_num [gatedExchange, observeA, observeB] at hne

/-- **§3.2: autonomy is not closed under joins.** There is a heredity kernel with two
autonomous observations whose joint observation is not autonomous. -/
theorem exists_autonomous_pair_not_autonomous_join :
    ∃ K : Bool × Bool × Bool → Bool × Bool × Bool → Bool × Bool × Bool → ℝ,
      IsHeredityKernel K ∧ HereditarilyAutonomous K observeA ∧
        HereditarilyAutonomous K observeB ∧
          ¬ HereditarilyAutonomous K fun x ↦ (observeA x, observeB x) :=
  ⟨gatedKernel, isHeredityKernel_childKernel gatedExchange, hereditarilyAutonomous_observeA,
    hereditarilyAutonomous_observeB, not_hereditarilyAutonomous_observeAB⟩

end

end Descent.Pangenome.AncestralLocality
