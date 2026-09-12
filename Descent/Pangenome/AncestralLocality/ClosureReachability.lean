/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Descent.Layer
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Closure is reachability: Theorem 4 of the ancestral-locality note

The spec is `ANCESTRAL_LOCALITY.md` §5. Genomes are `V → Bool`, the states `{0,1}^V`. A directed
checking graph is carried by its rates `r : V → V → ℝ`, with an edge `i → j` exactly when
`0 < r i j`. The event `i → j` recombines at the target `i` when the parents agree at the
checker `j` (`exchange`, spec (4.1)); `eventKernel` is (4.2) and `checkKernel` is `K_G`, (4.3).
The coordinate observation `π_A(x) = x|_A` partitions the genomes into `agreeOn A`, and
`outNbhd r A` is `N⁺_G(A)`.

**The one-step refinement (5.2)**, `refinementStep_agreeOn`: for `|A| ≥ 2` and nonnegative
rates, one hereditary refinement step turns `P_{π_A}` into `P_{π_{A ∪ N⁺_G(A)}}`. Sufficiency
is `sum_checkKernel_congr`: an event with target outside `A` does not move the observation, and
one with target in `A` reads the parents only at `A ∪ {j}` (`exchange_agree_left`,
`exchange_agree_right`). Necessity is the difference formula (5.3),
`sum_checkKernel_mixedBlocks_sub`: with the partner `partner A x` and the union of blocks
`mixedBlocks A x`, `K_G(x,y;B) - K_G(x',y;B) = (1/R) Σ_{i∈A, j∉A, x_j ≠ x'_j} r_ij`, strictly
positive when `x` and `x'` differ at an outside checker of `A` (`mixedBlocks_sub_pos`). A union
of blocks carries equal mass whenever every block does (`sum_eq_of_forall_block`), so the
refinement relation forbids that difference.

**Closure is reachability (5.1).** Iterating, the `n`-th refinement of `agreeOn A` is
`agreeOn ((grow r)^[n] A)` (`iterate_refinementStep_agreeOn`); the layers stabilise at
`directedReach r A` once `n ≥ |V|` (`iterate_grow_eq_reach`), and `agreeOn (directedReach r A)`
is a fixed point (`refinementStep_agreeOn_reach`). So `P_* = P_{π_{Reach_G(A)}}`
(`iterate_refinementStep_agreeOn_eq_reach`). For `|A| ≤ 1` the observation is its own closure
(`refinementStep_agreeOn_of_card_le_one`, `iterate_refinementStep_agreeOn_of_card_le_one`): the
empty observation because nothing is observed, a singleton by the exact neutrality (4.4)
(`sum_checkKernel_coord`).

**§5.1, (5.4).** Every coordinate observation is hereditarily autonomous in the sense (2.2), on
every graph (`autonomous_coord`). On a connected undirected dependency graph with both
orientations present, every query on at least two features has the whole genome as closure
(`iterate_refinementStep_eq_univ_of_connected`); `pathRates` is the path-graph instance
(`iterate_refinementStep_eq_univ_path`). Autonomy is not closed under joins: autonomy forces a
fixed point (`refinementStep_rel_of_autonomous`), so the pair `(π_i, π_k)` is not autonomous
whenever an outside checker of `{i, k}` exists (`not_autonomous_pair`), already on the path of
three features (`not_autonomous_pair_path`).

**The compatibility kernel.** At the rate matrix `edgeRates G` of a `CheckingGraph`, the
checking kernel here is `CompatibilityNeutrality`'s `compatibilityKernel G`
(`checkKernel_edgeRates`, through `exchange_eq_orderedChild`, `eventKernel_eq_exchangeKernel` and
`copyKernel_eq_halfMix`), so (5.2) and (5.1) hold for it verbatim
(`refinementStep_compatibilityKernel_agreeOn`,
`iterate_refinementStep_compatibilityKernel_eq_reach`).

Scope. The hereditary refinement `Φ_K` (`refinementStep`), autonomy (2.2) (`Autonomous`), the
event and checking kernels and the neutrality (4.4) are this file's own transcriptions of the
note's §2-§4, kept because the §6 and Theorem 1 modules of the layer are stated through them. The
kernels are identified with CompatibilityNeutrality's above; the module ReachabilityClosureTie
identifies `refinementStep` and `Autonomous` with HereditaryClosure's refinement and autonomy.
Rates are a matrix `r : V → V → ℝ` with edges where `0 < r i j`. The hereditary closure `P_*` is
read as the stable value of the iteration (3.2): what is proved is the value of every iterate and
the fixed
point, not Theorem 1's universal property, which belongs to HereditaryClosure. The difference
formula (5.3) sums over all pairs `i ∈ A`, `j ∉ A`; restricting to edges changes nothing because
the rates vanish off edges. The runtime remark of §5.1 is not a theorem and is not stated.

## Empirical status

None. The bodies here are finite sums of kernel weights over `{0,1}^V` and reachability in a
supplied graph; the rates and the observed features are supplied, and no measurement bears on a
partition identity.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Classical

noncomputable section

/-! ### Hereditary refinement and autonomy (local transcriptions of §2-§3) -/

/-- **Spec (3.1), one hereditary refinement step `Φ_K(P)`.** Two states stay together when they
were together under `P` and every block of `P` receives the same mass from either of them, with
every second parent `y`. The block of `z` is `{w | P.r w z}`. -/
def refinementStep {H : Type*} [Fintype H] (K : H → H → H → ℝ) (P : Setoid H) : Setoid H where
  r x x' := P.r x x' ∧ ∀ y z, ∑ w ∈ univ.filter (fun w ↦ P.r w z), K x y w =
    ∑ w ∈ univ.filter (fun w ↦ P.r w z), K x' y w
  iseqv := ⟨fun x ↦ ⟨P.iseqv.refl x, fun _ _ ↦ rfl⟩,
    fun h ↦ ⟨P.iseqv.symm h.1, fun y z ↦ (h.2 y z).symm⟩,
    fun h₁ h₂ ↦ ⟨P.iseqv.trans h₁.1 h₂.1, fun y z ↦ (h₁.2 y z).trans (h₂.2 y z)⟩⟩

/-- The refinement relation, unfolded. -/
theorem refinementStep_r_iff {H : Type*} [Fintype H] {K : H → H → H → ℝ} {P : Setoid H}
    {x x' : H} :
    (refinementStep K P).r x x' ↔ P.r x x' ∧ ∀ y z,
      ∑ w ∈ univ.filter (fun w ↦ P.r w z), K x y w =
        ∑ w ∈ univ.filter (fun w ↦ P.r w z), K x' y w :=
  Iff.rfl

/-- **Spec (2.2), hereditary autonomy.** An observation `f` is autonomous for the kernel `K` when
the law of the child's observation is a function `Kbar` of the parents' observations, for every
pair of parental states. -/
def Autonomous {H O : Type*} [Fintype H] [DecidableEq O] (K : H → H → H → ℝ) (f : H → O) :
    Prop :=
  ∃ Kbar : O → O → O → ℝ, ∀ x y o,
    ∑ w ∈ univ.filter (fun w ↦ f w = o), K x y w = Kbar (f x) (f y) o

/-- **Autonomy forces a fixed point.** If `f` is hereditarily autonomous and `P` is its
partition, states with the same observation stay together under one refinement step. -/
theorem refinementStep_rel_of_autonomous {H O : Type*} [Fintype H] [DecidableEq O]
    {K : H → H → H → ℝ} {f : H → O} (hf : Autonomous K f) {P : Setoid H}
    (hP : ∀ w z, P.r w z ↔ f w = f z) {x x' : H} (hxx' : f x = f x') :
    (refinementStep K P).r x x' := by
  obtain ⟨Kbar, hK⟩ := hf
  refine refinementStep_r_iff.mpr ⟨(hP x x').mpr hxx', fun y z ↦ ?_⟩
  have hblock : univ.filter (fun w ↦ P.r w z) = univ.filter (fun w ↦ f w = f z) :=
    filter_congr fun w _ ↦ hP w z
  rw [hblock, hK, hK, hxx']

/-- **A union of blocks carries equal mass when every block does.** If two mass functions agree
on every block of `P`, they agree on every finite set that is a union of blocks. -/
theorem sum_eq_of_forall_block {H : Type*} [Fintype H] (P : Setoid H) {μ ν : H → ℝ}
    (hblock : ∀ z, ∑ w ∈ univ.filter (fun w ↦ P.r w z), μ w =
      ∑ w ∈ univ.filter (fun w ↦ P.r w z), ν w)
    {s : Finset H} (hs : ∀ w w', P.r w w' → (w ∈ s ↔ w' ∈ s)) :
    ∑ w ∈ s, μ w = ∑ w ∈ s, ν w := by
  rw [← sum_fiberwise s (Quotient.mk P) μ, ← sum_fiberwise s (Quotient.mk P) ν]
  refine sum_congr rfl fun q _ ↦ ?_
  obtain ⟨z, rfl⟩ := Quotient.exists_rep q
  have hfiber : s.filter (fun w ↦ Quotient.mk P w = Quotient.mk P z) =
      if z ∈ s then univ.filter (fun w ↦ P.r w z) else ∅ := by
    ext w
    rw [mem_filter]
    split_ifs with hz
    · rw [mem_filter]
      exact ⟨fun h ↦ ⟨mem_univ w, Quotient.exact h.2⟩,
        fun h ↦ ⟨(hs w z h.2).mpr hz, Quotient.sound h.2⟩⟩
    · exact ⟨fun h ↦ absurd ((hs w z (Quotient.exact h.2)).mp h.1) hz, fun h ↦ by simp at h⟩
  rw [hfiber]
  split_ifs
  · exact hblock z
  · simp

/-! ### The checking kernel (local transcriptions of §4) -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Spec (4.1), the ordered child `T_ij(x, y)`.** The child is `x`, except that at the target
`i` it takes `y_i` when the parents agree at the checker `j`. -/
def exchange (i j : V) (x y : V → Bool) : V → Bool :=
  if x j = y j then Function.update x i (y i) else x

/-- **Spec (4.2), the event kernel `K_ij = ½ δ_{T_ij(x,y)} + ½ δ_{T_ij(y,x)}`.** -/
def eventKernel (i j : V) (x y z : V → Bool) : ℝ :=
  (if exchange i j x y = z then 1 / 2 else 0) + (if exchange i j y x = z then 1 / 2 else 0)

/-- The total rate `R = Σ_{i→j} r_ij` of spec (4.3). -/
def totalRate (r : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, r i j

/-- Unbiased parental copying `½ δ_x + ½ δ_y`, the kernel of a graph without edges. -/
def copyKernel (x y z : V → Bool) : ℝ :=
  (if x = z then 1 / 2 else 0) + (if y = z then 1 / 2 else 0)

/-- **Spec (4.3), the checking kernel `K_G`.** The rate-weighted mixture
`(1/R) Σ_{i→j} r_ij K_ij` of the event kernels, and unbiased copying when the total rate is
zero. -/
def checkKernel (r : V → V → ℝ) (x y z : V → Bool) : ℝ :=
  if totalRate r = 0 then copyKernel x y z
  else (∑ i, ∑ j, r i j * eventKernel i j x y z) / totalRate r

/-- **`P_{π_A}`**, the partition by the observation `π_A(x) = x|_A`: two genomes are equivalent
when they agree at every member of `A`. -/
def agreeOn (A : Finset V) : Setoid (V → Bool) where
  r x x' := ∀ l ∈ A, x l = x' l
  iseqv := ⟨fun _ _ _ ↦ rfl, fun h l hl ↦ (h l hl).symm,
    fun h₁ h₂ l hl ↦ (h₁ l hl).trans (h₂ l hl)⟩

omit [Fintype V] [DecidableEq V] in
/-- `π_A`-equivalence, unfolded. -/
theorem agreeOn_r_iff {A : Finset V} {x x' : V → Bool} :
    (agreeOn A).r x x' ↔ ∀ l ∈ A, x l = x' l :=
  Iff.rfl

/-- **`N⁺_G(A)`**, the checkers of the targets in `A`. -/
def outNbhd (r : V → V → ℝ) (A : Finset V) : Finset V :=
  univ.filter fun j ↦ ∃ i ∈ A, 0 < r i j

omit [DecidableEq V] in
/-- Membership in `N⁺_G(A)`, unfolded. -/
theorem mem_outNbhd {r : V → V → ℝ} {A : Finset V} {j : V} :
    j ∈ outNbhd r A ↔ ∃ i ∈ A, 0 < r i j :=
  mem_filter.trans (and_iff_right (mem_univ j))

/-- **`Reach_G(A)`**: `A` together with every feature a directed path from `A` reaches. -/
def directedReach (r : V → V → ℝ) (A : Finset V) : Finset V :=
  univ.filter fun v ↦ ∃ a ∈ A, Relation.ReflTransGen (fun i j ↦ 0 < r i j) a v

omit [DecidableEq V] in
/-- Membership in `Reach_G(A)`, unfolded. -/
theorem mem_directedReach {r : V → V → ℝ} {A : Finset V} {v : V} :
    v ∈ directedReach r A ↔ ∃ a ∈ A, Relation.ReflTransGen (fun i j ↦ 0 < r i j) a v :=
  mem_filter.trans (and_iff_right (mem_univ v))

/-! ### Masses of the kernels -/

/-- The mass an event kernel puts on a finite set of genomes. -/
theorem sum_eventKernel (i j : V) (x y : V → Bool) (s : Finset (V → Bool)) :
    ∑ w ∈ s, eventKernel i j x y w = (if exchange i j x y ∈ s then 1 / 2 else 0) +
      (if exchange i j y x ∈ s then 1 / 2 else 0) := by
  simp only [eventKernel, sum_add_distrib, sum_ite_eq]

omit [DecidableEq V] in
/-- The mass unbiased copying puts on a finite set of genomes. -/
theorem sum_copyKernel (x y : V → Bool) (s : Finset (V → Bool)) :
    ∑ w ∈ s, copyKernel x y w =
      (if x ∈ s then 1 / 2 else 0) + (if y ∈ s then 1 / 2 else 0) := by
  simp only [copyKernel, sum_add_distrib, sum_ite_eq]

/-- **The mass of `K_G` on a set is the rate-weighted mixture of the event masses.** -/
theorem sum_checkKernel (r : V → V → ℝ) (x y : V → Bool) (s : Finset (V → Bool)) :
    ∑ w ∈ s, checkKernel r x y w =
      if totalRate r = 0 then ∑ w ∈ s, copyKernel x y w
      else (∑ i, ∑ j, r i j * ∑ w ∈ s, eventKernel i j x y w) / totalRate r := by
  by_cases hR : totalRate r = 0
  · rw [if_pos hR]
    exact sum_congr rfl fun w _ ↦ if_pos hR
  · rw [if_neg hR]
    have hw : ∀ w, checkKernel r x y w =
        (∑ i, ∑ j, r i j * eventKernel i j x y w) / totalRate r := fun w ↦ if_neg hR
    simp only [hw]
    rw [← sum_div]
    congr 1
    calc ∑ w ∈ s, ∑ i, ∑ j, r i j * eventKernel i j x y w
        = ∑ i, ∑ w ∈ s, ∑ j, r i j * eventKernel i j x y w := sum_comm
      _ = ∑ i, ∑ j, ∑ w ∈ s, r i j * eventKernel i j x y w :=
        sum_congr rfl fun i _ ↦ sum_comm
      _ = ∑ i, ∑ j, r i j * ∑ w ∈ s, eventKernel i j x y w :=
        sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ (mul_sum _ _ _).symm

omit [Fintype V] in
/-- An event with parents agreeing at the checker. -/
theorem exchange_of_eq {i j : V} {x y : V → Bool} (h : x j = y j) :
    exchange i j x y = Function.update x i (y i) :=
  if_pos h

omit [Fintype V] in
/-- An event with parents disagreeing at the checker copies the first parent. -/
theorem exchange_of_ne {i j : V} {x y : V → Bool} (h : x j ≠ y j) : exchange i j x y = x :=
  if_neg h

omit [Fintype V] in
/-- Off its target an event copies the first parent. -/
theorem exchange_apply_of_ne {i j k : V} (x y : V → Bool) (hk : k ≠ i) :
    exchange i j x y k = x k := by
  unfold exchange
  split_ifs
  · exact Function.update_of_ne hk _ _
  · rfl

omit [Fintype V] in
/-- **An exchange preserves the unordered pair of parental values at every coordinate.** -/
theorem exchange_apply_pair (i j k : V) (x y : V → Bool) :
    (exchange i j x y k = x k ∧ exchange i j y x k = y k) ∨
      (exchange i j x y k = y k ∧ exchange i j y x k = x k) := by
  by_cases hk : k = i
  · subst hk
    by_cases h : x j = y j
    · right
      rw [exchange_of_eq h, exchange_of_eq h.symm, Function.update_self, Function.update_self]
      exact ⟨rfl, rfl⟩
    · left
      rw [exchange_of_ne h, exchange_of_ne (x := y) (y := x) fun h' ↦ h h'.symm]
      exact ⟨rfl, rfl⟩
  · exact Or.inl ⟨exchange_apply_of_ne x y hk, exchange_apply_of_ne y x hk⟩

/-- **Spec (4.4) for one event.** An event kernel puts mass `½·1{x_k = a} + ½·1{y_k = a}` on
`{z | z_k = a}`. -/
theorem sum_eventKernel_coord (i j k : V) (x y : V → Bool) (a : Bool) {s : Finset (V → Bool)}
    (hs : ∀ w, w ∈ s ↔ w k = a) :
    ∑ w ∈ s, eventKernel i j x y w =
      (if x k = a then 1 / 2 else 0) + (if y k = a then 1 / 2 else 0) := by
  rw [sum_eventKernel]
  simp only [hs]
  rcases exchange_apply_pair i j k x y with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, add_comm]

/-- **Spec (4.4), every feature is exactly neutral.** The checking kernel puts mass
`½·1{x_k = a} + ½·1{y_k = a}` on `{z | z_k = a}`, for every graph and all rates. -/
theorem sum_checkKernel_coord (r : V → V → ℝ) (k : V) (x y : V → Bool) (a : Bool)
    {s : Finset (V → Bool)} (hs : ∀ w, w ∈ s ↔ w k = a) :
    ∑ w ∈ s, checkKernel r x y w =
      (if x k = a then 1 / 2 else 0) + (if y k = a then 1 / 2 else 0) := by
  rw [sum_checkKernel]
  by_cases hR : totalRate r = 0
  · rw [if_pos hR, sum_copyKernel]
    simp only [hs]
  · rw [if_neg hR]
    simp only [sum_eventKernel_coord _ _ k x y a hs, ← sum_mul]
    exact mul_div_cancel_left₀ _ hR

/-- **Every coordinate observation is hereditarily autonomous** (spec §5.1), on every graph and
for all rates: the child's allele at `k` has the law `½ δ_{x_k} + ½ δ_{y_k}`. -/
theorem autonomous_coord (r : V → V → ℝ) (k : V) :
    Autonomous (checkKernel r) (fun x : V → Bool ↦ x k) :=
  ⟨fun a b o ↦ (if a = o then 1 / 2 else 0) + (if b = o then 1 / 2 else 0),
    fun x y o ↦ sum_checkKernel_coord r k x y o fun w ↦
      mem_filter.trans (and_iff_right (mem_univ w))⟩

/-! ### Sufficiency in (5.2) -/

omit [Fintype V] in
/-- With the parents agreeing at `A` and at every checker of a target in `A`, the child in the
first slot agrees at `A`. -/
theorem exchange_agree_left {A : Finset V} {i j : V} {x x' : V → Bool} (y : V → Bool)
    (hxx' : ∀ l ∈ A, x l = x' l) (hj : i ∈ A → x j = x' j) :
    ∀ l ∈ A, exchange i j x y l = exchange i j x' y l := by
  intro l hl
  by_cases hi : i ∈ A
  · unfold exchange
    rw [hj hi]
    split_ifs
    · by_cases hli : l = i
      · rw [hli, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hli, Function.update_of_ne hli]
        exact hxx' l hl
    · exact hxx' l hl
  · have hli : l ≠ i := fun h ↦ hi (h ▸ hl)
    rw [exchange_apply_of_ne x y hli, exchange_apply_of_ne x' y hli]
    exact hxx' l hl

omit [Fintype V] in
/-- With the parents agreeing at `A` and at every checker of a target in `A`, the child in the
second slot agrees at `A`. -/
theorem exchange_agree_right {A : Finset V} {i j : V} {x x' : V → Bool} (y : V → Bool)
    (hxx' : ∀ l ∈ A, x l = x' l) (hj : i ∈ A → x j = x' j) :
    ∀ l ∈ A, exchange i j y x l = exchange i j y x' l := by
  intro l hl
  by_cases hi : i ∈ A
  · unfold exchange
    rw [hj hi, hxx' i hi]
  · have hli : l ≠ i := fun h ↦ hi (h ▸ hl)
    rw [exchange_apply_of_ne y x hli, exchange_apply_of_ne y x' hli]

/-- **Sufficiency in spec (5.2).** If `x` and `x'` agree at `A` and at every checker of a target
in `A`, the checking kernel gives every union of `π_A`-blocks the same mass from either. -/
theorem sum_checkKernel_congr {r : V → V → ℝ} {A : Finset V} {s : Finset (V → Bool)}
    (hs : ∀ w w', (∀ l ∈ A, w l = w' l) → (w ∈ s ↔ w' ∈ s)) {x x' : V → Bool}
    (hxx' : ∀ l ∈ A, x l = x' l) (hN : ∀ i ∈ A, ∀ j, r i j ≠ 0 → x j = x' j) (y : V → Bool) :
    ∑ w ∈ s, checkKernel r x y w = ∑ w ∈ s, checkKernel r x' y w := by
  rw [sum_checkKernel, sum_checkKernel]
  by_cases hR : totalRate r = 0
  · rw [if_pos hR, if_pos hR, sum_copyKernel, sum_copyKernel]
    simp only [hs x x' hxx']
  · rw [if_neg hR, if_neg hR]
    congr 1
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    by_cases hij : r i j = 0
    · rw [hij, zero_mul, zero_mul]
    · have hj : i ∈ A → x j = x' j := fun hi ↦ hN i hi j hij
      rw [sum_eventKernel, sum_eventKernel]
      simp only [hs _ _ (exchange_agree_left y hxx' hj), hs _ _ (exchange_agree_right y hxx' hj)]

/-! ### Necessity in (5.2): the difference formula (5.3) -/

/-- The partner genome of spec (5.3): `y|_A = 1 - x|_A` and `y = x` off `A`. -/
def partner (A : Finset V) (x : V → Bool) : V → Bool :=
  fun l ↦ if l ∈ A then !x l else x l

omit [Fintype V] in
/-- On `A` the partner flips `x`. -/
theorem partner_of_mem {A : Finset V} {x : V → Bool} {l : V} (hl : l ∈ A) :
    partner A x l = !x l :=
  if_pos hl

omit [Fintype V] in
/-- Off `A` the partner copies `x`. -/
theorem partner_of_not_mem {A : Finset V} {x : V → Bool} {l : V} (hl : l ∉ A) :
    partner A x l = x l :=
  if_neg hl

/-- **The union `B` of spec (5.3)**: the genomes whose observation on `A` is neither `x|_A` nor
`1 - x|_A`, that is, which agree with `x` at some member of `A` and disagree at another. -/
def mixedBlocks (A : Finset V) (x : V → Bool) : Finset (V → Bool) :=
  univ.filter fun w ↦ (∃ l ∈ A, w l = x l) ∧ ∃ l ∈ A, w l ≠ x l

/-- Membership in `B`, unfolded. -/
theorem mem_mixedBlocks {A : Finset V} {x w : V → Bool} :
    w ∈ mixedBlocks A x ↔ (∃ l ∈ A, w l = x l) ∧ ∃ l ∈ A, w l ≠ x l :=
  mem_filter.trans (and_iff_right (mem_univ w))

/-- `B` is a union of `π_A`-blocks. -/
theorem mem_mixedBlocks_congr {A : Finset V} {x w w' : V → Bool} (h : ∀ l ∈ A, w l = w' l) :
    w ∈ mixedBlocks A x ↔ w' ∈ mixedBlocks A x := by
  rw [mem_mixedBlocks, mem_mixedBlocks]
  constructor
  · rintro ⟨⟨l, hl, h₁⟩, ⟨l', hl', h₂⟩⟩
    exact ⟨⟨l, hl, (h l hl).symm.trans h₁⟩, ⟨l', hl', fun e ↦ h₂ ((h l' hl').trans e)⟩⟩
  · rintro ⟨⟨l, hl, h₁⟩, ⟨l', hl', h₂⟩⟩
    exact ⟨⟨l, hl, (h l hl).trans h₁⟩, ⟨l', hl', fun e ↦ h₂ ((h l' hl').symm.trans e)⟩⟩

/-- A genome agreeing with `x` on all of `A` is not in `B`. -/
theorem not_mem_mixedBlocks_of_agree {A : Finset V} {x w : V → Bool}
    (h : ∀ l ∈ A, w l = x l) : w ∉ mixedBlocks A x := by
  rw [mem_mixedBlocks]
  rintro ⟨-, l, hl, hne⟩
  exact hne (h l hl)

/-- A genome disagreeing with `x` on all of `A` is not in `B`. -/
theorem not_mem_mixedBlocks_of_disagree {A : Finset V} {x w : V → Bool}
    (h : ∀ l ∈ A, w l ≠ x l) : w ∉ mixedBlocks A x := by
  rw [mem_mixedBlocks]
  rintro ⟨⟨l, hl, heq⟩, -⟩
  exact h l hl heq

omit [Fintype V] in
/-- The partner disagrees with `x` at every member of `A`. -/
theorem partner_ne {A : Finset V} {x : V → Bool} {l : V} (hl : l ∈ A) : partner A x l ≠ x l := by
  rw [partner_of_mem hl]
  cases x l <;> decide

/-- **The event masses behind spec (5.3).** Let `x'` agree with `x` at `A`, with `|A| ≥ 2`, and
pair it with the partner of `x`. An event puts mass one on `B` exactly when its target is in `A`,
its checker is outside `A`, and `x'` agrees with `x` at the checker; otherwise mass zero. -/
theorem sum_eventKernel_mixedBlocks {A : Finset V} (hA : 2 ≤ A.card) {x x' : V → Bool}
    (hxx' : ∀ l ∈ A, x l = x' l) (i j : V) :
    ∑ w ∈ mixedBlocks A x, eventKernel i j x' (partner A x) w =
      if i ∈ A ∧ j ∉ A ∧ x' j = x j then 1 else 0 := by
  have hx'A : ∀ l ∈ A, x' l = x l := fun l hl ↦ (hxx' l hl).symm
  have hpartner : ∀ l ∈ A, partner A x l ≠ x l := fun l hl ↦ partner_ne hl
  rw [sum_eventKernel]
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · have hne : x' j ≠ partner A x j := by
        rw [hx'A j hj]
        exact fun h ↦ hpartner j hj h.symm
      have hc : ¬ (i ∈ A ∧ j ∉ A ∧ x' j = x j) := fun h ↦ h.2.1 hj
      rw [exchange_of_ne hne, exchange_of_ne (Ne.symm hne),
        if_neg (not_mem_mixedBlocks_of_agree hx'A),
        if_neg (not_mem_mixedBlocks_of_disagree hpartner), if_neg hc]
      norm_num
    · obtain ⟨l, hl, hli⟩ := exists_mem_ne (show 1 < A.card by omega) i
      by_cases hx : x' j = x j
      · have heq : x' j = partner A x j := by rw [partner_of_not_mem hj, hx]
        have hmem₁ : Function.update x' i (partner A x i) ∈ mixedBlocks A x := by
          rw [mem_mixedBlocks]
          refine ⟨⟨l, hl, ?_⟩, ⟨i, hi, ?_⟩⟩
          · rw [Function.update_of_ne hli]
            exact hx'A l hl
          · rw [Function.update_self]
            exact hpartner i hi
        have hmem₂ : Function.update (partner A x) i (x' i) ∈ mixedBlocks A x := by
          rw [mem_mixedBlocks]
          refine ⟨⟨i, hi, ?_⟩, ⟨l, hl, ?_⟩⟩
          · rw [Function.update_self]
            exact hx'A i hi
          · rw [Function.update_of_ne hli]
            exact hpartner l hl
        have hc : i ∈ A ∧ j ∉ A ∧ x' j = x j := ⟨hi, hj, hx⟩
        rw [exchange_of_eq heq, exchange_of_eq heq.symm, if_pos hmem₁, if_pos hmem₂, if_pos hc]
        norm_num
      · have hne : x' j ≠ partner A x j := by rwa [partner_of_not_mem hj]
        have hc : ¬ (i ∈ A ∧ j ∉ A ∧ x' j = x j) := fun h ↦ hx h.2.2
        rw [exchange_of_ne hne, exchange_of_ne (Ne.symm hne),
          if_neg (not_mem_mixedBlocks_of_agree hx'A),
          if_neg (not_mem_mixedBlocks_of_disagree hpartner), if_neg hc]
        norm_num
  · have hagree : ∀ l ∈ A, exchange i j x' (partner A x) l = x l := by
      intro l hl
      have hli : l ≠ i := fun h ↦ hi (h ▸ hl)
      rw [exchange_apply_of_ne x' (partner A x) hli]
      exact hx'A l hl
    have hdisagree : ∀ l ∈ A, exchange i j (partner A x) x' l ≠ x l := by
      intro l hl
      have hli : l ≠ i := fun h ↦ hi (h ▸ hl)
      rw [exchange_apply_of_ne (partner A x) x' hli]
      exact hpartner l hl
    have hc : ¬ (i ∈ A ∧ j ∉ A ∧ x' j = x j) := fun h ↦ hi h.1
    rw [if_neg (not_mem_mixedBlocks_of_agree hagree),
      if_neg (not_mem_mixedBlocks_of_disagree hdisagree), if_neg hc]
    norm_num

/-- **Spec (5.3), the difference formula.** For `|A| ≥ 2`, `x'` agreeing with `x` at `A`, the
partner `y` of `x` and the union `B = mixedBlocks A x`,
`K_G(x,y;B) - K_G(x',y;B) = (1/R) Σ_{i ∈ A, j ∉ A, x_j ≠ x'_j} r_ij`. -/
theorem sum_checkKernel_mixedBlocks_sub {r : V → V → ℝ} {A : Finset V} (hA : 2 ≤ A.card)
    {x x' : V → Bool} (hxx' : ∀ l ∈ A, x l = x' l) :
    ∑ w ∈ mixedBlocks A x, checkKernel r x (partner A x) w -
        ∑ w ∈ mixedBlocks A x, checkKernel r x' (partner A x) w =
      (∑ i, ∑ j, if i ∈ A ∧ j ∉ A ∧ x j ≠ x' j then r i j else 0) / totalRate r := by
  rw [sum_checkKernel, sum_checkKernel]
  by_cases hR : totalRate r = 0
  · have hx : x ∉ mixedBlocks A x := not_mem_mixedBlocks_of_agree fun _ _ ↦ rfl
    have hx' : x' ∉ mixedBlocks A x :=
      not_mem_mixedBlocks_of_agree fun l hl ↦ (hxx' l hl).symm
    have hp : partner A x ∉ mixedBlocks A x :=
      not_mem_mixedBlocks_of_disagree fun _ hl ↦ partner_ne hl
    rw [if_pos hR, if_pos hR, hR, div_zero, sum_copyKernel, sum_copyKernel, if_neg hx,
      if_neg hp, if_neg hx']
    norm_num
  · rw [if_neg hR, if_neg hR, ← sub_div]
    congr 1
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_eventKernel_mixedBlocks hA hxx',
      sum_eventKernel_mixedBlocks hA (x := x) (x' := x) fun _ _ ↦ rfl]
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ A
      · simp [hi, hj]
      · by_cases hx : x' j = x j
        · simp [hi, hj, hx]
        · have hx' : ¬ x j = x' j := fun h ↦ hx h.symm
          simp [hi, hj, hx, hx']
    · simp [hi]

/-- **The difference (5.3) is strictly positive** when some target in `A` has an edge to a
checker outside `A` at which `x` and `x'` differ. -/
theorem mixedBlocks_sub_pos {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V}
    {x x' : V → Bool} {i₀ j₀ : V} (hi₀ : i₀ ∈ A) (hj₀ : j₀ ∉ A) (hx : x j₀ ≠ x' j₀)
    (hrij : 0 < r i₀ j₀) :
    0 < (∑ i, ∑ j, if i ∈ A ∧ j ∉ A ∧ x j ≠ x' j then r i j else 0) / totalRate r := by
  have hterm : ∀ i j, 0 ≤ (if i ∈ A ∧ j ∉ A ∧ x j ≠ x' j then r i j else 0) := by
    intro i j
    split_ifs
    exacts [hr i j, le_rfl]
  have hc : i₀ ∈ A ∧ j₀ ∉ A ∧ x j₀ ≠ x' j₀ := ⟨hi₀, hj₀, hx⟩
  have hnum : r i₀ j₀ ≤ ∑ i, ∑ j, if i ∈ A ∧ j ∉ A ∧ x j ≠ x' j then r i j else 0 := by
    calc r i₀ j₀ = (if i₀ ∈ A ∧ j₀ ∉ A ∧ x j₀ ≠ x' j₀ then r i₀ j₀ else 0) := (if_pos hc).symm
      _ ≤ ∑ j, if i₀ ∈ A ∧ j ∉ A ∧ x j ≠ x' j then r i₀ j else 0 :=
        single_le_sum (fun j _ ↦ hterm i₀ j) (mem_univ j₀)
      _ ≤ ∑ i, ∑ j, if i ∈ A ∧ j ∉ A ∧ x j ≠ x' j then r i j else 0 :=
        single_le_sum (fun i _ ↦ sum_nonneg fun j _ ↦ hterm i j) (mem_univ i₀)
  have hR : r i₀ j₀ ≤ totalRate r :=
    (single_le_sum (fun j _ ↦ hr i₀ j) (mem_univ j₀)).trans
      (single_le_sum (fun i _ ↦ sum_nonneg fun j _ ↦ hr i j) (mem_univ i₀))
  exact div_pos (hrij.trans_le hnum) (hrij.trans_le hR)

/-! ### The one-step refinement (5.2) -/

/-- **Spec (5.2), the one-step refinement.** For `|A| ≥ 2` and nonnegative rates, one
hereditary refinement step of the checking kernel turns `P_{π_A}` into
`P_{π_{A ∪ N⁺_G(A)}}`. -/
theorem refinementStep_agreeOn {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V}
    (hA : 2 ≤ A.card) :
    refinementStep (checkKernel r) (agreeOn A) = agreeOn (A ∪ outNbhd r A) := by
  refine Setoid.ext fun x x' ↦ ?_
  show (refinementStep (checkKernel r) (agreeOn A)).r x x' ↔
    (agreeOn (A ∪ outNbhd r A)).r x x'
  rw [refinementStep_r_iff, agreeOn_r_iff, agreeOn_r_iff]
  constructor
  · rintro ⟨hxx', hblock⟩ l hl
    rcases mem_union.mp hl with hl | hl
    · exact hxx' l hl
    · by_cases hlA : l ∈ A
      · exact hxx' l hlA
      · by_contra hne
        obtain ⟨i, hi, hil⟩ := mem_outNbhd.mp hl
        have hmass := sum_eq_of_forall_block (agreeOn A) (fun z ↦ hblock (partner A x) z)
          (s := mixedBlocks A x) fun _ _ h ↦ mem_mixedBlocks_congr h
        have hdiff := sum_checkKernel_mixedBlocks_sub (r := r) hA hxx'
        rw [hmass, sub_self] at hdiff
        exact (mixedBlocks_sub_pos hr hi hlA hne hil).ne hdiff
  · intro hxx'
    refine ⟨fun l hl ↦ hxx' l (mem_union_left _ hl), fun y z ↦ ?_⟩
    refine sum_checkKernel_congr (fun w w' h ↦ ?_) (fun l hl ↦ hxx' l (mem_union_left _ hl))
      (fun i hi j hij ↦ hxx' j (mem_union_right _ (mem_outNbhd.mpr
        ⟨i, hi, lt_of_le_of_ne (hr i j) (Ne.symm hij)⟩))) y
    rw [mem_filter, mem_filter, agreeOn_r_iff, agreeOn_r_iff]
    exact ⟨fun hw ↦ ⟨mem_univ w', fun l hl ↦ (h l hl).symm.trans (hw.2 l hl)⟩,
      fun hw ↦ ⟨mem_univ w, fun l hl ↦ (h l hl).trans (hw.2 l hl)⟩⟩

/-- **The empty observation is autonomous**: with nothing observed, one refinement step changes
nothing. -/
theorem refinementStep_agreeOn_empty (r : V → V → ℝ) :
    refinementStep (checkKernel r) (agreeOn ∅) = agreeOn ∅ := by
  refine Setoid.ext fun x x' ↦ ?_
  show (refinementStep (checkKernel r) (agreeOn ∅)).r x x' ↔ (agreeOn ∅).r x x'
  rw [refinementStep_r_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun y z ↦ ?_⟩⟩
  refine sum_checkKernel_congr (A := ∅) (fun w w' _ ↦ ?_) h
    (fun i hi ↦ absurd hi (by simp)) y
  rw [mem_filter, mem_filter, agreeOn_r_iff, agreeOn_r_iff]
  simp

/-- **A singleton observation is autonomous** (spec (5.1), `|A| = 1`): by the exact neutrality
(4.4), one refinement step changes nothing. -/
theorem refinementStep_agreeOn_singleton (r : V → V → ℝ) (k : V) :
    refinementStep (checkKernel r) (agreeOn {k}) = agreeOn {k} := by
  refine Setoid.ext fun x x' ↦ ?_
  show (refinementStep (checkKernel r) (agreeOn {k})).r x x' ↔ (agreeOn {k}).r x x'
  rw [refinementStep_r_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun y z ↦ ?_⟩⟩
  have hs : ∀ w, w ∈ univ.filter (fun w ↦ (agreeOn {k}).r w z) ↔ w k = z k := by
    intro w
    rw [mem_filter, agreeOn_r_iff]
    refine ⟨fun hw ↦ hw.2 k (mem_singleton_self k), fun hw ↦ ⟨mem_univ w, fun l hl ↦ ?_⟩⟩
    rw [mem_singleton.mp hl]
    exact hw
  rw [sum_checkKernel_coord r k x y (z k) hs, sum_checkKernel_coord r k x' y (z k) hs,
    agreeOn_r_iff.mp h k (mem_singleton_self k)]

/-- **Spec (5.1), `|A| ≤ 1`.** An observation of at most one feature is its own hereditary
closure. -/
theorem refinementStep_agreeOn_of_card_le_one (r : V → V → ℝ) {A : Finset V}
    (hA : A.card ≤ 1) : refinementStep (checkKernel r) (agreeOn A) = agreeOn A := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hA with h | h
  · rw [card_eq_zero.mp h]
    exact refinementStep_agreeOn_empty r
  · obtain ⟨k, rfl⟩ := card_eq_one.mp h
    exact refinementStep_agreeOn_singleton r k

/-- **Spec (5.1), `|A| ≤ 1`, iterated.** Every refinement of such an observation is itself. -/
theorem iterate_refinementStep_agreeOn_of_card_le_one (r : V → V → ℝ) {A : Finset V}
    (hA : A.card ≤ 1) (n : ℕ) :
    (refinementStep (checkKernel r))^[n] (agreeOn A) = agreeOn A :=
  Function.iterate_fixed (f := refinementStep (checkKernel r))
    (refinementStep_agreeOn_of_card_le_one r hA) n

/-! ### Closure is reachability (5.1) -/

/-- One reachability step `B ↦ B ∪ N⁺_G(B)`; its `n`-th iterate from `A` is the set of features
within `n` directed steps of `A`. -/
def grow (r : V → V → ℝ) (B : Finset V) : Finset V :=
  B ∪ outNbhd r B

/-- The layers grow. -/
theorem iterate_grow_mono (r : V → V → ℝ) (A : Finset V) {m n : ℕ} (h : m ≤ n) :
    (grow r)^[m] A ⊆ (grow r)^[n] A := by
  induction h with
  | refl => exact fun _ ha ↦ ha
  | step _ ih =>
    rw [Function.iterate_succ_apply']
    exact fun _ ha ↦ mem_union_left _ (ih ha)

/-- `A` lies in every layer. -/
theorem subset_iterate_grow (r : V → V → ℝ) (A : Finset V) (n : ℕ) : A ⊆ (grow r)^[n] A :=
  iterate_grow_mono r A (Nat.zero_le n)

omit [DecidableEq V] in
/-- `A` lies in its reach. -/
theorem subset_directedReach (r : V → V → ℝ) (A : Finset V) : A ⊆ directedReach r A :=
  fun a ha ↦ mem_directedReach.mpr ⟨a, ha, Relation.ReflTransGen.refl⟩

omit [DecidableEq V] in
/-- The reach is closed under taking checkers. -/
theorem outNbhd_reach_subset (r : V → V → ℝ) (A : Finset V) :
    outNbhd r (directedReach r A) ⊆ directedReach r A := by
  intro v hv
  obtain ⟨i, hi, hiv⟩ := mem_outNbhd.mp hv
  obtain ⟨a, ha, hai⟩ := mem_directedReach.mp hi
  exact mem_directedReach.mpr ⟨a, ha, hai.tail hiv⟩

/-- Every layer lies in the reach. -/
theorem iterate_grow_subset_reach (r : V → V → ℝ) (A : Finset V) (n : ℕ) :
    (grow r)^[n] A ⊆ directedReach r A := by
  induction n with
  | zero => exact subset_directedReach r A
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact ih hv
    · obtain ⟨i, hi, hiv⟩ := mem_outNbhd.mp hv
      obtain ⟨a, ha, hai⟩ := mem_directedReach.mp (ih hi)
      exact mem_directedReach.mpr ⟨a, ha, hai.tail hiv⟩

/-- Every feature in the reach lies in some layer. -/
theorem exists_mem_iterate_grow (r : V → V → ℝ) {A : Finset V} {v : V}
    (hv : v ∈ directedReach r A) : ∃ n, v ∈ (grow r)^[n] A := by
  obtain ⟨a, ha, hav⟩ := mem_directedReach.mp hv
  clear hv
  induction hav with
  | refl => exact ⟨0, ha⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact mem_union_right _ (mem_outNbhd.mpr ⟨_, hn, hbc⟩)

/-- **The layers stabilise at the reach** once `n ≥ |V|`. -/
theorem iterate_grow_eq_reach (r : V → V → ℝ) (A : Finset V) {n : ℕ}
    (hn : Fintype.card V ≤ n) : (grow r)^[n] A = directedReach r A := by
  have hclaim : ∀ k, (∃ m < k, (grow r)^[m + 1] A = (grow r)^[m] A) ∨
      k ≤ ((grow r)^[k] A).card := by
    intro k
    induction k with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ k ih =>
      rcases ih with ⟨m, hm, hstable⟩ | hk
      · exact Or.inl ⟨m, Nat.lt_succ_of_lt hm, hstable⟩
      · by_cases hstable : (grow r)^[k + 1] A = (grow r)^[k] A
        · exact Or.inl ⟨k, Nat.lt_succ_self k, hstable⟩
        · right
          have hlt : ((grow r)^[k] A).card < ((grow r)^[k + 1] A).card := not_le.mp fun hle ↦
            hstable (eq_of_subset_of_card_le (iterate_grow_mono r A (Nat.le_succ k)) hle).symm
          exact Nat.succ_le_of_lt (hk.trans_lt hlt)
  obtain ⟨m, hm, hstable⟩ : ∃ m < Fintype.card V + 1, (grow r)^[m + 1] A = (grow r)^[m] A := by
    rcases hclaim (Fintype.card V + 1) with h | h
    · exact h
    · exact absurd (h.trans (card_le_univ _)) (Nat.not_succ_le_self _)
  have hforever : ∀ d, (grow r)^[m + d] A = (grow r)^[m] A := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [← Nat.add_assoc, Function.iterate_succ_apply', ih]
      rwa [Function.iterate_succ_apply'] at hstable
  have hreach : directedReach r A ⊆ (grow r)^[m] A := by
    intro v hv
    obtain ⟨d, hd⟩ := exists_mem_iterate_grow r hv
    rcases le_total d m with hdm | hmd
    · exact iterate_grow_mono r A hdm hd
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hmd
      rwa [hforever e] at hd
  exact Subset.antisymm (iterate_grow_subset_reach r A n)
    (Subset.trans hreach (iterate_grow_mono r A ((Nat.lt_succ_iff.mp hm).trans hn)))

/-- **Iterating the one-step refinement.** For `|A| ≥ 2` and nonnegative rates, the `n`-th
refinement of `P_{π_A}` is the partition by the `n`-th layer. -/
theorem iterate_refinementStep_agreeOn {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V}
    (hA : 2 ≤ A.card) (n : ℕ) :
    (refinementStep (checkKernel r))^[n] (agreeOn A) = agreeOn ((grow r)^[n] A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact refinementStep_agreeOn hr (hA.trans (card_le_card (subset_iterate_grow r A n)))

/-- **Spec (5.1), closure is reachability.** For `|A| ≥ 2` and nonnegative rates, every
refinement of `P_{π_A}` from the `|V|`-th on is `P_{π_{Reach_G(A)}}`: the hereditary closure
of `π_A` is `π_{Reach_G(A)}`. -/
theorem iterate_refinementStep_agreeOn_eq_reach {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j)
    {A : Finset V} (hA : 2 ≤ A.card) {n : ℕ} (hn : Fintype.card V ≤ n) :
    (refinementStep (checkKernel r))^[n] (agreeOn A) = agreeOn (directedReach r A) := by
  rw [iterate_refinementStep_agreeOn hr hA n, iterate_grow_eq_reach r A hn]

/-- **The reach is the fixed point** (spec (5.1)): `P_{π_{Reach_G(A)}}` is stable under the
hereditary refinement. -/
theorem refinementStep_agreeOn_reach {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {A : Finset V}
    (hA : 2 ≤ A.card) :
    refinementStep (checkKernel r) (agreeOn (directedReach r A)) = agreeOn (directedReach r A) := by
  rw [refinementStep_agreeOn hr (hA.trans (card_le_card (subset_directedReach r A))),
    union_eq_left.mpr (outNbhd_reach_subset r A)]

/-! ### §5.1: connected graphs, the path, and joins -/

omit [DecidableEq V] in
/-- Observing every feature separates every pair of genomes. -/
theorem agreeOn_univ_r_iff {x x' : V → Bool} : (agreeOn (univ : Finset V)).r x x' ↔ x = x' :=
  ⟨fun h ↦ funext fun l ↦ agreeOn_r_iff.mp h l (mem_univ l),
    fun h ↦ agreeOn_r_iff.mpr fun l _ ↦ congrFun h l⟩

omit [DecidableEq V] in
/-- On a connected undirected graph whose edges carry positive rates in both orientations,
every nonempty set of features reaches the whole genome. -/
theorem reach_eq_univ_of_connected {G : SimpleGraph V} (hG : G.Connected) {r : V → V → ℝ}
    (hrG : ∀ i j, G.Adj i j → 0 < r i j) {A : Finset V} (hA : A.Nonempty) :
    directedReach r A = univ := by
  obtain ⟨a, ha⟩ := hA
  refine eq_univ_of_forall fun v ↦ mem_directedReach.mpr ⟨a, ha, ?_⟩
  exact ((SimpleGraph.reachable_iff_reflTransGen a v).mp (hG.preconnected a v)).mono hrG

/-- **Spec (5.4).** On a connected undirected dependency graph with both orientations present,
every query on at least two features has the whole genome as hereditary closure. -/
theorem iterate_refinementStep_eq_univ_of_connected {G : SimpleGraph V} (hG : G.Connected)
    {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) (hrG : ∀ i j, G.Adj i j → 0 < r i j)
    {A : Finset V} (hA : 2 ≤ A.card) {n : ℕ} (hn : Fintype.card V ≤ n) :
    (refinementStep (checkKernel r))^[n] (agreeOn A) = agreeOn univ := by
  rw [iterate_refinementStep_agreeOn_eq_reach hr hA hn,
    reach_eq_univ_of_connected hG hrG (card_pos.mp (by omega))]

/-- The path graph on `m` features, with unit rates in both orientations of every edge. -/
def pathRates (m : ℕ) (i j : Fin m) : ℝ :=
  if (SimpleGraph.pathGraph m).Adj i j then 1 else 0

/-- Path rates are nonnegative. -/
theorem pathRates_nonneg (m : ℕ) (i j : Fin m) : 0 ≤ pathRates m i j := by
  unfold pathRates
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-- Every edge of the path carries a positive rate. -/
theorem pathRates_pos {m : ℕ} {i j : Fin m} (h : (SimpleGraph.pathGraph m).Adj i j) :
    0 < pathRates m i j := by
  unfold pathRates
  rw [if_pos h]
  exact one_pos

/-- **Spec (5.4) on a path.** On the path of `m + 1` features, every query on at least two
features has the whole genome as hereditary closure. -/
theorem iterate_refinementStep_eq_univ_path {m : ℕ} {A : Finset (Fin (m + 1))}
    (hA : 2 ≤ A.card) {n : ℕ} (hn : m + 1 ≤ n) :
    (refinementStep (checkKernel (pathRates (m + 1))))^[n] (agreeOn A) = agreeOn univ :=
  iterate_refinementStep_eq_univ_of_connected (SimpleGraph.pathGraph_connected m)
    (pathRates_nonneg (m + 1)) (fun _ _ h ↦ pathRates_pos h) hA (by rwa [Fintype.card_fin])

/-- **Autonomy is not closed under joins** (spec §5.1). Each coordinate is autonomous
(`autonomous_coord`), but the joint observation `(π_i, π_k)` is not whenever some feature `v`
outside `{i, k}` is a checker of `i` or of `k`. -/
theorem not_autonomous_pair {r : V → V → ℝ} (hr : ∀ i j, 0 ≤ r i j) {i k v : V} (hik : i ≠ k)
    (hvi : v ≠ i) (hvk : v ≠ k) (hv : v ∈ outNbhd r {i, k}) :
    ¬ Autonomous (checkKernel r) (fun x : V → Bool ↦ (x i, x k)) := by
  intro hf
  have hP : ∀ w z : V → Bool, (agreeOn {i, k}).r w z ↔ (w i, w k) = (z i, z k) := by
    intro w z
    rw [agreeOn_r_iff, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨h i (mem_insert_self i _), h k (mem_insert_of_mem (mem_singleton_self k))⟩
    · rintro ⟨hi, hk⟩ l hl
      rcases mem_insert.mp hl with hl | hl
      · rw [hl]
        exact hi
      · rw [mem_singleton.mp hl]
        exact hk
  have hxx' : ((fun _ ↦ false : V → Bool) i, (fun _ ↦ false : V → Bool) k) =
      (Function.update (fun _ ↦ false) v true i, Function.update (fun _ ↦ false) v true k) := by
    rw [Function.update_of_ne hvi.symm, Function.update_of_ne hvk.symm]
  have hrel := refinementStep_rel_of_autonomous hf hP (x := fun _ ↦ false)
    (x' := Function.update (fun _ ↦ false) v true) hxx'
  rw [refinementStep_agreeOn hr (card_pair hik).ge, agreeOn_r_iff] at hrel
  have hv' := hrel v (mem_union_right _ hv)
  simp at hv'

/-- **Autonomy is not closed under joins, on the path of three features.** Features `0` and `1`
are each autonomous, and their join is not. -/
theorem not_autonomous_pair_path :
    Autonomous (checkKernel (pathRates 3)) (fun x : Fin 3 → Bool ↦ x 0) ∧
      Autonomous (checkKernel (pathRates 3)) (fun x : Fin 3 → Bool ↦ x 1) ∧
      ¬ Autonomous (checkKernel (pathRates 3)) (fun x : Fin 3 → Bool ↦ (x 0, x 1)) :=
  ⟨autonomous_coord _ 0, autonomous_coord _ 1,
    not_autonomous_pair (v := 2) (pathRates_nonneg 3) (by decide) (by decide) (by decide)
      (mem_outNbhd.mpr ⟨1, mem_insert_of_mem (mem_singleton_self 1),
        pathRates_pos (SimpleGraph.pathGraph_adj.mpr (by decide))⟩)⟩

/-! ### The compatibility kernel of `CompatibilityNeutrality` -/

/-- The rates of a checking graph as a rate matrix: `r_ij` on an edge `i → j`, zero off the
edges. -/
def edgeRates (G : CheckingGraph V) (i j : V) : ℝ :=
  if (i, j) ∈ G.edges then G.rate (i, j) else 0

omit [Fintype V] in
/-- The rate matrix of a checking graph is nonnegative. -/
theorem edgeRates_nonneg (G : CheckingGraph V) (i j : V) : 0 ≤ edgeRates G i j := by
  unfold edgeRates
  split_ifs with h
  · exact (G.rate_pos _ h).le
  · exact le_rfl

omit [Fintype V] in
/-- The rate matrix is positive exactly on the edges. -/
theorem edgeRates_pos_iff (G : CheckingGraph V) {i j : V} :
    0 < edgeRates G i j ↔ (i, j) ∈ G.edges := by
  unfold edgeRates
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ G.rate_pos _ h⟩
  · exact ⟨fun h' ↦ absurd h' (lt_irrefl 0), fun h' ↦ absurd h' h⟩

/-- `N⁺_G(A)` at the rate matrix: the checkers of the targets in `A` along the edges. -/
theorem mem_outNbhd_edgeRates (G : CheckingGraph V) {A : Finset V} {j : V} :
    j ∈ outNbhd (edgeRates G) A ↔ ∃ i ∈ A, (i, j) ∈ G.edges := by
  simp only [mem_outNbhd, edgeRates_pos_iff]

/-- A rate-weighted double sum over the rate matrix is the sum over the edges. -/
theorem sum_edgeRates_mul (G : CheckingGraph V) (c : V → V → ℝ) :
    ∑ i, ∑ j, edgeRates G i j * c i j = ∑ e ∈ G.edges, G.rate e * c e.1 e.2 := by
  rw [← Fintype.sum_ite_mem G.edges, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  unfold edgeRates
  split_ifs <;> simp

/-- The total rate of the rate matrix is the graph's total rate `R`. -/
theorem totalRate_edgeRates (G : CheckingGraph V) : totalRate (edgeRates G) = G.totalRate := by
  have h := sum_edgeRates_mul G fun _ _ ↦ 1
  simp only [mul_one] at h
  exact h

omit [Fintype V] in
/-- **The ordered child of this module is `CompatibilityNeutrality`'s**, spec (4.1). -/
theorem exchange_eq_orderedChild (i j : V) (x y : V → Bool) :
    exchange i j x y = orderedChild i j x y := by
  funext k
  by_cases h : x j = y j
  · by_cases hk : k = i
    · subst hk
      rw [exchange_of_eq h, Function.update_self]
      simp [orderedChild, h]
    · rw [exchange_apply_of_ne x y hk]
      simp [orderedChild, hk]
  · rw [exchange_of_ne h]
    simp [orderedChild, h]

/-- **The event kernel of this module is `CompatibilityNeutrality`'s `K_ij`**, spec (4.2). -/
theorem eventKernel_eq_exchangeKernel (i j : V) (x y z : V → Bool) :
    eventKernel i j x y z = exchangeKernel i j x y z := by
  simp only [eventKernel, exchangeKernel, halfMix, exchange_eq_orderedChild]
  split_ifs <;> norm_num

omit [DecidableEq V] in
/-- Unbiased copying of this module is `CompatibilityNeutrality`'s `halfMix`. -/
theorem copyKernel_eq_halfMix (x y z : V → Bool) : copyKernel x y z = halfMix x y z := by
  simp only [copyKernel, halfMix]
  split_ifs <;> norm_num

/-- **The checking kernel of this module is `CompatibilityNeutrality`'s `K_G`**, spec (4.3), at
the rate matrix of the graph. -/
theorem checkKernel_edgeRates (G : CheckingGraph V) :
    checkKernel (edgeRates G) = compatibilityKernel G := by
  funext x y z
  unfold checkKernel compatibilityKernel
  rw [totalRate_edgeRates]
  by_cases h : G.edges = ∅
  · have hR : G.totalRate = 0 := by rw [CheckingGraph.totalRate, h, sum_empty]
    rw [if_pos hR, if_pos h, copyKernel_eq_halfMix]
  · have hR : G.totalRate ≠ 0 := (G.totalRate_pos (nonempty_iff_ne_empty.mpr h)).ne'
    rw [if_neg hR, if_neg h, sum_edgeRates_mul G fun i j ↦ eventKernel i j x y z]
    simp only [eventKernel_eq_exchangeKernel]

/-- **Spec (5.2) for `compatibilityKernel`.** For `|A| ≥ 2`, one hereditary refinement step of
`K_G` turns `P_{π_A}` into `P_{π_{A ∪ N⁺_G(A)}}`. -/
theorem refinementStep_compatibilityKernel_agreeOn (G : CheckingGraph V) {A : Finset V}
    (hA : 2 ≤ A.card) :
    refinementStep (compatibilityKernel G) (agreeOn A) =
      agreeOn (A ∪ outNbhd (edgeRates G) A) := by
  rw [← checkKernel_edgeRates]
  exact refinementStep_agreeOn (edgeRates_nonneg G) hA

/-- **Spec (5.1) for `compatibilityKernel`.** For `|A| ≥ 2`, every refinement of `P_{π_A}` from
the `|V|`-th on is `P_{π_{Reach_G(A)}}`. -/
theorem iterate_refinementStep_compatibilityKernel_eq_reach (G : CheckingGraph V)
    {A : Finset V} (hA : 2 ≤ A.card) {n : ℕ} (hn : Fintype.card V ≤ n) :
    (refinementStep (compatibilityKernel G))^[n] (agreeOn A) =
      agreeOn (directedReach (edgeRates G) A) := by
  rw [← checkKernel_edgeRates]
  exact iterate_refinementStep_agreeOn_eq_reach (edgeRates_nonneg G) hA hn

end

end Descent.Pangenome.AncestralLocality
