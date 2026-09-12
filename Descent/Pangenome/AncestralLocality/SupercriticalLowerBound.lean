/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.BreadthFirstDomination

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The supercritical lower bound: every feature is in a large component with chance at least `s`

For `α > 1` and `s = giantFraction α`, the note's (6.2) needs a component of `G(m, α/m)` of size
near `s m`. `Descent.Pangenome.AncestralLocality.SupercriticalUpperBound` proves the upper half.
This file proves the matching lower bound in expectation, with no hypothesis carrying the
Erdős–Rényi theorem. For every `K` and `ε > 0`, eventually every feature lies in a component of at
least `K` features with probability at least `s - ε` (`eventually_graphProb_card_reach_ge`). So the
expected number of features in components of at least `K` features is at least `(s - ε) m`
(`eventually_graphExpect_card_large_ge`).

**The exploration.** The state is a set `D` of discovered features and a set `A ⊆ D` of active
ones. A step explores the least active feature `a`. Its new neighbours `newNeighbors E D a`, the
undiscovered features joined to `a`, become discovered and active, and `a` stops being active.
`exploreDies E K t D A` says the exploration runs out of active features within `t` steps while
fewer than `K` features are discovered. If a set closed under the edges has fewer than `K`
features, the exploration from inside it dies (`exploreDies_of_closed`). In particular the
exploration from `v` dies when the component of `v` has fewer than `K` features
(`exploreDies_of_card_reach_lt`, through `reach_singleton_closed`).

**The supermartingale.** A step reads only the pairs from `a` to the undiscovered features
(`neighborEdges`), and the later steps read only pairs avoiding the explored features
(`exploreDies_congr`). Conditioning on the pairs read therefore separates the step from the rest
(`graphExpect_newNeighbors`), and the number of new neighbours is binomial
(`card_newNeighbors_of_subset`, through `subsetExpect_pow_card`). While fewer than `K` features are
discovered, at least `m - K` are undiscovered. So if `(1 - p (1 - q))^(m - K) ≤ q`, the chance of
dying from an active set `A` is at most `q^|A|` (`graphProb_exploreDies_le`), by induction on the
number of steps. From one feature, `P(|Reach(v)| < K) ≤ q` (`graphProb_card_reach_lt_le`).

**The constant.** Below the giant fraction the survival map lies above the diagonal:
`e^{-α s'} < 1 - s'` for `0 < s' < s`. Since `1 - x ≤ e^{-x}`,
`(1 - α s'/m)^(m - K) ≤ e^{-α s'} e^{α s' K / m}`, which is eventually at most `1 - s'`
(`eventually_one_sub_pow_le`). Taking `q = 1 - s'` with `s' = s - ε` gives the lower bound. The
same bound holds for every `K ≤ κ₀ m` with some `κ₀ > 0` (`exists_one_sub_pow_le`), so the
threshold may grow linearly in `m` (`exists_forall_graphProb_card_reach_ge`).

Scope. Only the expectation form of the lower half is proved. It does not say that one component of
size near `s m` exists with probability tending to one. That needs concentration of the number of
features in large components, and a merging argument showing that those features lie in a single
component. So this file does not discharge `GiantComponentLaw α`. The comparison is with the
extinction probability `1 - s'` of a branching process, through the supermartingale `q^|A|`. No
branching process is constructed.

## Empirical status

None. The bodies are probabilities under `G(m, α/m)`, counts of explored features and limits in
`m`. The graph law is supplied, and nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### One exploration step -/

/-- **The new neighbours of an explored feature**: the features outside the discovered set `D`
joined to `a` in `E`. -/
def newNeighbors {m : ℕ} (E : Finset (Sym2 (Fin m))) (D : Finset (Fin m)) (a : Fin m) :
    Finset (Fin m) :=
  (univ \ D).filter fun u ↦ s(a, u) ∈ E

/-- Membership in the new neighbours. -/
theorem mem_newNeighbors_iff {m : ℕ} {E : Finset (Sym2 (Fin m))} {D : Finset (Fin m)}
    {a u : Fin m} : u ∈ newNeighbors E D a ↔ u ∉ D ∧ s(a, u) ∈ E := by
  simp [newNeighbors]

/-- The new neighbours are undiscovered. -/
theorem disjoint_newNeighbors {m : ℕ} (E : Finset (Sym2 (Fin m))) (D : Finset (Fin m))
    (a : Fin m) : Disjoint D (newNeighbors E D a) :=
  disjoint_left.mpr fun _ hu hu' ↦ (mem_newNeighbors_iff.mp hu').1 hu

/-- **The pairs one exploration step reads**: from `a` to the undiscovered features. -/
def neighborEdges {m : ℕ} (D : Finset (Fin m)) (a : Fin m) : Finset (Sym2 (Fin m)) :=
  (univ \ D).image fun u ↦ s(a, u)

/-- The pairs from a fixed feature to distinct features are distinct. -/
theorem sym2_mk_right_injective {m : ℕ} (a : Fin m) :
    Function.Injective fun u : Fin m ↦ s(a, u) := fun u u' h ↦ by
  rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · exact h2.trans h1

/-- The pairs read from a discovered feature are potential edges. -/
theorem neighborEdges_subset_potentialEdges {m : ℕ} {D : Finset (Fin m)} {a : Fin m}
    (ha : a ∈ D) : neighborEdges D a ⊆ potentialEdges m := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := mem_image.mp he
  simp only [mem_potentialEdges_iff, Sym2.mk_isDiag_iff]
  exact fun h ↦ (mem_sdiff.mp hu).2 (h ▸ ha)

/-- One step reads one pair per undiscovered feature. -/
theorem card_neighborEdges {m : ℕ} (D : Finset (Fin m)) (a : Fin m) :
    (neighborEdges D a).card = m - D.card := by
  rw [neighborEdges, card_image_of_injective _ (sym2_mk_right_injective a),
    card_sdiff_of_subset (subset_univ D), card_univ, Fintype.card_fin]

/-- **The new neighbours count the present pairs read.** -/
theorem card_newNeighbors_of_subset {m : ℕ} {E : Finset (Sym2 (Fin m))} {D : Finset (Fin m)}
    {a : Fin m} (hE : E ⊆ neighborEdges D a) : (newNeighbors E D a).card = E.card := by
  have himage : E = (newNeighbors E D a).image fun u ↦ s(a, u) := by
    ext e
    constructor
    · intro he
      obtain ⟨u, hu, rfl⟩ := mem_image.mp (hE he)
      exact mem_image.mpr ⟨u, mem_newNeighbors_iff.mpr ⟨(mem_sdiff.mp hu).2, he⟩, rfl⟩
    · intro he
      obtain ⟨u, hu, rfl⟩ := mem_image.mp he
      exact (mem_newNeighbors_iff.mp hu).2
  calc (newNeighbors E D a).card = ((newNeighbors E D a).image fun u ↦ s(a, u)).card :=
        (card_image_of_injective _ (sym2_mk_right_injective a)).symm
    _ = E.card := congrArg card himage.symm

/-- **One exploration step, conditioned on the pairs it reads.** For a quantity `F S E` that sees
`E` only through the pairs avoiding the explored feature `a`, whenever `S` is undiscovered, the
expectation of `F` at the new neighbours of `a` averages, over the pairs `E₁` from `a` to the
undiscovered features, the expectation of `F` at the new neighbours that `E₁` produces. -/
theorem graphExpect_newNeighbors {m : ℕ} (p : ℝ) {D : Finset (Fin m)} {a : Fin m} (ha : a ∈ D)
    (F : Finset (Fin m) → Finset (Sym2 (Fin m)) → ℝ)
    (hF : ∀ S, Disjoint D S → ∀ E E' : Finset (Sym2 (Fin m)),
      (∀ x y, x ≠ a → y ≠ a → (s(x, y) ∈ E ↔ s(x, y) ∈ E')) → F S E = F S E') :
    graphExpect m p (fun E ↦ F (newNeighbors E D a) E) =
      subsetExpect (neighborEdges D a) p
        (fun E₁ ↦ graphExpect m p (F (newNeighbors E₁ D a))) := by
  have hT := neighborEdges_subset_potentialEdges ha
  have hcontains : ∀ e ∈ neighborEdges D a, ∀ x y, x ≠ a → y ≠ a → e ≠ s(x, y) := by
    intro e he x y hx hy heq
    obtain ⟨u, -, rfl⟩ := mem_image.mp he
    rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hx h1.symm
    · exact hy h1.symm
  rw [graphExpect_eq_subsetExpect, subsetExpect_split p hT]
  refine sum_congr rfl fun E₁ hE₁ ↦ ?_
  have hE₁T : E₁ ⊆ neighborEdges D a := mem_powerset.mp hE₁
  have hS := disjoint_newNeighbors E₁ D a
  have hlocal : graphExpect m p (F (newNeighbors E₁ D a)) =
      subsetExpect (potentialEdges m \ neighborEdges D a) p (F (newNeighbors E₁ D a)) := by
    rw [graphExpect_eq_subsetExpect]
    refine subsetExpect_eq_of_local p sdiff_subset fun E₂ _ E₃ hE₃ ↦
      hF _ hS _ _ fun x y hx hy ↦ ?_
    rw [mem_union]
    refine ⟨fun h ↦ h.resolve_right fun h3 ↦ ?_, Or.inl⟩
    have h3' := hE₃ h3
    rw [mem_sdiff, mem_sdiff] at h3'
    exact hcontains _ (by tauto) x y hx hy rfl
  have hinner : subsetExpect (potentialEdges m \ neighborEdges D a) p
      (fun E₂ ↦ F (newNeighbors (E₁ ∪ E₂) D a) (E₁ ∪ E₂)) =
        subsetExpect (potentialEdges m \ neighborEdges D a) p (F (newNeighbors E₁ D a)) := by
    refine sum_congr rfl fun E₂ hE₂ ↦ ?_
    have hE₂T : ∀ e ∈ E₂, e ∉ neighborEdges D a := fun e he ↦
      (mem_sdiff.mp (mem_powerset.mp hE₂ he)).2
    have hnext : newNeighbors (E₁ ∪ E₂) D a = newNeighbors E₁ D a := by
      ext u
      rw [mem_newNeighbors_iff, mem_newNeighbors_iff, mem_union]
      exact and_congr_right fun hu ↦ ⟨fun h ↦ h.resolve_right fun h2 ↦
        hE₂T _ h2 (mem_image.mpr ⟨u, mem_sdiff.mpr ⟨mem_univ u, hu⟩, rfl⟩), Or.inl⟩
    have hF' : F (newNeighbors E₁ D a) (E₁ ∪ E₂) = F (newNeighbors E₁ D a) E₂ :=
      hF _ hS _ _ fun x y hx hy ↦ by
        rw [mem_union]
        exact ⟨fun h ↦ h.resolve_left fun h1 ↦ hcontains _ (hE₁T h1) x y hx hy rfl, Or.inr⟩
    simp only [hnext, hF']
  simp only [hinner, hlocal]

/-! ### The exploration -/

/-- **The exploration dies before `K` features are discovered**, within `t` steps. The state is
the set `D` of discovered features and the set `A` of active ones. A step explores the least
active feature `a`: its new neighbours become discovered and active, and `a` stops being active. -/
def exploreDies {m : ℕ} (E : Finset (Sym2 (Fin m))) (K : ℕ) :
    ℕ → Finset (Fin m) → Finset (Fin m) → Prop
  | 0, D, A => A = ∅ ∧ D.card < K
  | t + 1, D, A => D.card < K ∧
    if h : A.Nonempty then
      exploreDies E K t (D ∪ newNeighbors E D (A.min' h))
        (A.erase (A.min' h) ∪ newNeighbors E D (A.min' h))
    else True

/-- With no steps left the exploration has died exactly when nothing is active. -/
theorem exploreDies_zero {m : ℕ} (E : Finset (Sym2 (Fin m))) (K : ℕ) (D A : Finset (Fin m)) :
    exploreDies E K 0 D A ↔ A = ∅ ∧ D.card < K :=
  Iff.rfl

/-- A step from a nonempty active set explores its least feature. -/
theorem exploreDies_succ_of_nonempty {m : ℕ} (E : Finset (Sym2 (Fin m))) (K t : ℕ)
    {D A : Finset (Fin m)} (h : A.Nonempty) :
    exploreDies E K (t + 1) D A ↔ D.card < K ∧
      exploreDies E K t (D ∪ newNeighbors E D (A.min' h))
        (A.erase (A.min' h) ∪ newNeighbors E D (A.min' h)) := by
  simp only [exploreDies, dif_pos h]

/-- With nothing active the exploration has died while fewer than `K` features are discovered. -/
theorem exploreDies_succ_empty {m : ℕ} (E : Finset (Sym2 (Fin m))) (K t : ℕ)
    (D : Finset (Fin m)) : exploreDies E K (t + 1) D ∅ ↔ D.card < K := by
  simp [exploreDies]

/-- **The exploration reads only the pairs avoiding the explored features** `D \ A`. -/
theorem exploreDies_congr {m K : ℕ} {E E' : Finset (Sym2 (Fin m))} (t : ℕ) :
    ∀ {D A : Finset (Fin m)}, A ⊆ D →
      (∀ x y, x ∉ D \ A → y ∉ D \ A → (s(x, y) ∈ E ↔ s(x, y) ∈ E')) →
        (exploreDies E K t D A ↔ exploreDies E' K t D A) := by
  induction t with
  | zero => exact fun _ _ ↦ Iff.rfl
  | succ t ih =>
    intro D A hAD h
    by_cases hA : A.Nonempty
    · have ha : A.min' hA ∈ A := min'_mem A hA
      have hnext : newNeighbors E D (A.min' hA) = newNeighbors E' D (A.min' hA) := by
        ext u
        rw [mem_newNeighbors_iff, mem_newNeighbors_iff]
        exact and_congr_right fun hu ↦ h _ _ (fun hx ↦ (mem_sdiff.mp hx).2 ha)
          (fun hx ↦ hu (mem_sdiff.mp hx).1)
      rw [exploreDies_succ_of_nonempty E K t hA, exploreDies_succ_of_nonempty E' K t hA, hnext]
      refine and_congr_right fun _ ↦
        ih (union_subset_union ((erase_subset _ _).trans hAD) Subset.rfl) fun x y hx hy ↦ ?_
      have hX : ∀ z, z ∉ (D ∪ newNeighbors E' D (A.min' hA)) \
          (A.erase (A.min' hA) ∪ newNeighbors E' D (A.min' hA)) → z ∉ D \ A := by
        intro z hz hzX
        obtain ⟨hzD, hzA⟩ := mem_sdiff.mp hzX
        refine hz (mem_sdiff.mpr ⟨mem_union_left _ hzD, fun hz' ↦ ?_⟩)
        rcases mem_union.mp hz' with hz' | hz'
        · exact hzA (mem_of_mem_erase hz')
        · exact (mem_newNeighbors_iff.mp hz').1 hzD
      exact h x y (hX x hx) (hX y hy)
    · rw [not_nonempty_iff_eq_empty.mp hA, exploreDies_succ_empty, exploreDies_succ_empty]

/-- A component is closed under the edges. -/
theorem reach_singleton_closed {m : ℕ} (E : Finset (Sym2 (Fin m))) (v : Fin m) :
    ∀ x ∈ reach (edgeGraph E) {v}, ∀ y, s(x, y) ∈ E → y ∈ reach (edgeGraph E) {v} := by
  intro x hx y hxy
  by_cases h : x = y
  · exact h ▸ hx
  · obtain ⟨b, hb, hbx⟩ := (mem_reach_iff _ _ _).mp hx
    exact (mem_reach_iff _ _ _).mpr
      ⟨b, hb, hbx.trans ((edgeGraph_adj_iff E x y).mpr ⟨hxy, h⟩).reachable⟩

/-- **A small closed set makes the exploration die.** If `C` is closed under the edges of `E` and
has fewer than `K` features, the exploration from any discovered set inside `C` dies within as
many steps as there are features not yet explored. -/
theorem exploreDies_of_closed {m K : ℕ} {E : Finset (Sym2 (Fin m))} {C : Finset (Fin m)}
    (hC : ∀ x ∈ C, ∀ y, s(x, y) ∈ E → y ∈ C) (hK : C.card < K) (n : ℕ) :
    ∀ {D A : Finset (Fin m)}, A ⊆ D → D ⊆ C →
      (univ \ (D \ A)).card ≤ n → exploreDies E K n D A := by
  induction n with
  | zero =>
    intro D A _ hDC hn
    have hsub : univ ⊆ D \ A :=
      sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (Nat.le_zero.mp hn))
    have hA : A = ∅ :=
      eq_empty_of_forall_notMem fun a ha ↦ (mem_sdiff.mp (hsub (mem_univ a))).2 ha
    exact ⟨hA, (card_le_card hDC).trans_lt hK⟩
  | succ n ih =>
    intro D A hAD hDC hn
    have hDK : D.card < K := (card_le_card hDC).trans_lt hK
    by_cases hA : A.Nonempty
    · have ha : A.min' hA ∈ A := min'_mem A hA
      have haD : A.min' hA ∈ D := hAD ha
      rw [exploreDies_succ_of_nonempty E K n hA]
      refine ⟨hDK, ih (union_subset_union ((erase_subset _ _).trans hAD) Subset.rfl) ?_ ?_⟩
      · refine union_subset hDC fun u hu ↦ ?_
        exact hC _ (hDC haD) u (mem_newNeighbors_iff.mp hu).2
      · have hX : ∀ z ∈ D \ A, z ∈ (D ∪ newNeighbors E D (A.min' hA)) \
            (A.erase (A.min' hA) ∪ newNeighbors E D (A.min' hA)) := by
          intro z hz
          obtain ⟨hzD, hzA⟩ := mem_sdiff.mp hz
          refine mem_sdiff.mpr ⟨mem_union_left _ hzD, fun hz' ↦ ?_⟩
          rcases mem_union.mp hz' with hz' | hz'
          · exact hzA (mem_of_mem_erase hz')
          · exact (mem_newNeighbors_iff.mp hz').1 hzD
        have ha' : A.min' hA ∈ (D ∪ newNeighbors E D (A.min' hA)) \
            (A.erase (A.min' hA) ∪ newNeighbors E D (A.min' hA)) := by
          refine mem_sdiff.mpr ⟨mem_union_left _ haD, fun h ↦ ?_⟩
          rcases mem_union.mp h with h | h
          · exact notMem_erase _ _ h
          · exact (mem_newNeighbors_iff.mp h).1 haD
        have ha'' : A.min' hA ∈ univ \ (D \ A) :=
          mem_sdiff.mpr ⟨mem_univ _, fun h ↦ (mem_sdiff.mp h).2 ha⟩
        calc (univ \ ((D ∪ newNeighbors E D (A.min' hA)) \
              (A.erase (A.min' hA) ∪ newNeighbors E D (A.min' hA)))).card
            ≤ ((univ \ (D \ A)).erase (A.min' hA)).card := by
              refine card_le_card fun w hw ↦ ?_
              rw [mem_sdiff] at hw
              refine mem_erase.mpr ⟨fun h ↦ hw.2 (by rw [h]; exact ha'), ?_⟩
              exact mem_sdiff.mpr ⟨mem_univ w, fun h ↦ hw.2 (hX w h)⟩
          _ = (univ \ (D \ A)).card - 1 := card_erase_of_mem ha''
          _ ≤ n := by omega
    · rw [not_nonempty_iff_eq_empty.mp hA, exploreDies_succ_empty]
      exact hDK

/-- **A small component makes the exploration die.** If the component of `v` has fewer than `K`
features, the exploration from any discovered set inside it dies within as many steps as there are
features not yet explored. -/
theorem exploreDies_of_card_reach_lt {m K : ℕ} {E : Finset (Sym2 (Fin m))} {v : Fin m}
    (hK : (reach (edgeGraph E) {v}).card < K) (n : ℕ) :
    ∀ {D A : Finset (Fin m)}, A ⊆ D → D ⊆ reach (edgeGraph E) {v} →
      (univ \ (D \ A)).card ≤ n → exploreDies E K n D A :=
  exploreDies_of_closed (reach_singleton_closed E v) hK n

/-! ### The supermartingale -/

/-- An event that never happens has probability zero. -/
theorem graphProb_of_forall_not {m : ℕ} (p : ℝ) {P : Finset (Sym2 (Fin m)) → Prop}
    [DecidablePred P] (h : ∀ E, ¬P E) : graphProb m p P = 0 := by
  rw [← graphExpect_const (m := m) p (0 : ℝ), graphProb]
  exact sum_congr rfl fun E _ ↦ by simp only [if_neg (h E)]

/-- **The exploration is a supermartingale in `q^|A|`.** If `0 ≤ q ≤ 1` and
`(1 - p (1 - q))^(m - K) ≤ q`, the exploration from an active set `A ⊆ D` dies within `t` steps,
before `K` features are discovered, with probability at most `q^|A|`. -/
theorem graphProb_exploreDies_le {m K : ℕ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hq : (1 - p * (1 - q)) ^ (m - K) ≤ q) (t : ℕ) :
    ∀ {D A : Finset (Fin m)}, A ⊆ D →
      graphProb m p (fun E ↦ exploreDies E K t D A) ≤ q ^ A.card := by
  induction t with
  | zero =>
    intro D A _
    by_cases hA : A = ∅
    · rw [hA, card_empty, pow_zero]
      exact graphProb_le_one hp0 hp1 _
    · rw [graphProb_of_forall_not p fun E h ↦ hA ((exploreDies_zero E K D A).mp h).1]
      exact pow_nonneg hq0 _
  | succ t ih =>
    intro D A hAD
    by_cases hA : A.Nonempty
    · by_cases hD : D.card < K
      · have ha : A.min' hA ∈ A := min'_mem A hA
        have haD : A.min' hA ∈ D := hAD ha
        have hF : ∀ S, Disjoint D S → ∀ E E' : Finset (Sym2 (Fin m)),
            (∀ x y, x ≠ A.min' hA → y ≠ A.min' hA → (s(x, y) ∈ E ↔ s(x, y) ∈ E')) →
              (if exploreDies E K t (D ∪ S) (A.erase (A.min' hA) ∪ S) then (1 : ℝ) else 0) =
                if exploreDies E' K t (D ∪ S) (A.erase (A.min' hA) ∪ S) then 1 else 0 := by
          intro S hS E E' hEE'
          have hne : ∀ x, x ∉ (D ∪ S) \ (A.erase (A.min' hA) ∪ S) → x ≠ A.min' hA := by
            intro x hx hxa
            refine hx (mem_sdiff.mpr ⟨mem_union_left _ (hxa ▸ haD), fun h' ↦ ?_⟩)
            rcases mem_union.mp h' with h' | h'
            · exact notMem_erase _ _ (hxa ▸ h')
            · exact disjoint_left.mp hS (hxa ▸ haD) h'
          have hiff := exploreDies_congr (K := K) t
            (union_subset_union ((erase_subset _ _).trans hAD) Subset.rfl)
            fun x y hx hy ↦ hEE' x y (hne x hx) (hne y hy)
          simp only [hiff]
        have hbase0 : 0 ≤ p * q + (1 - p) := by
          have := mul_nonneg hp0 hq0
          linarith
        have hbase1 : p * q + (1 - p) ≤ 1 := by
          have := mul_nonneg hp0 (sub_nonneg.mpr hq1)
          nlinarith
        have hexp : m - K ≤ (neighborEdges D (A.min' hA)).card := by
          rw [card_neighborEdges]
          omega
        have hq' : (p * q + (1 - p)) ^ (m - K) ≤ q := by
          have hring : p * q + (1 - p) = 1 - p * (1 - q) := by ring
          rw [hring]
          exact hq
        calc graphProb m p (fun E ↦ exploreDies E K (t + 1) D A)
            = graphExpect m p (fun E ↦ if exploreDies E K t (D ∪ newNeighbors E D (A.min' hA))
                (A.erase (A.min' hA) ∪ newNeighbors E D (A.min' hA)) then (1 : ℝ) else 0) := by
              rw [graphProb]
              refine sum_congr rfl fun E _ ↦ ?_
              simp only [exploreDies_succ_of_nonempty E K t hA, hD, true_and]
          _ = subsetExpect (neighborEdges D (A.min' hA)) p (fun E₁ ↦ graphExpect m p
                (fun E ↦ if exploreDies E K t (D ∪ newNeighbors E₁ D (A.min' hA))
                  (A.erase (A.min' hA) ∪ newNeighbors E₁ D (A.min' hA)) then (1 : ℝ) else 0)) :=
              graphExpect_newNeighbors p haD
                (fun S E ↦ if exploreDies E K t (D ∪ S) (A.erase (A.min' hA) ∪ S) then (1 : ℝ)
                  else 0) hF
          _ ≤ subsetExpect (neighborEdges D (A.min' hA)) p
                (fun E₁ ↦ q ^ E₁.card * q ^ (A.card - 1)) := by
              refine subsetExpect_mono _ hp0 hp1 fun E₁ hE₁ ↦ ?_
              have hbound := ih (D := D ∪ newNeighbors E₁ D (A.min' hA))
                (A := A.erase (A.min' hA) ∪ newNeighbors E₁ D (A.min' hA))
                (union_subset_union ((erase_subset _ _).trans hAD) Subset.rfl)
              have hcard : (A.erase (A.min' hA) ∪ newNeighbors E₁ D (A.min' hA)).card =
                  E₁.card + (A.card - 1) := by
                rw [card_union_of_disjoint (disjoint_of_subset_left
                  ((erase_subset _ _).trans hAD) (disjoint_newNeighbors E₁ D _)),
                  card_erase_of_mem ha, card_newNeighbors_of_subset hE₁, add_comm]
              rw [← pow_add, ← hcard]
              exact hbound
          _ = (p * q + (1 - p)) ^ (neighborEdges D (A.min' hA)).card * q ^ (A.card - 1) := by
              rw [subsetExpect_mul_const, subsetExpect_pow_card]
          _ ≤ q * q ^ (A.card - 1) :=
              mul_le_mul_of_nonneg_right
                ((pow_le_pow_of_le_one hbase0 hbase1 hexp).trans hq') (pow_nonneg hq0 _)
          _ = q ^ A.card := by
              rw [← pow_succ']
              have := card_pos.mpr hA
              congr 1
              omega
      · rw [graphProb_of_forall_not p fun E h ↦
          hD ((exploreDies_succ_of_nonempty E K t hA).mp h).1]
        exact pow_nonneg hq0 _
    · rw [not_nonempty_iff_eq_empty.mp hA, card_empty, pow_zero]
      exact graphProb_le_one hp0 hp1 _

/-- **A small component is at most as likely as extinction.** If `0 ≤ q ≤ 1` and
`(1 - p (1 - q))^(m - K) ≤ q`, the component of `v` in `G(m, p)` has fewer than `K` features with
probability at most `q`. -/
theorem graphProb_card_reach_lt_le {m K : ℕ} {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : (1 - p * (1 - q)) ^ (m - K) ≤ q) (v : Fin m) :
    graphProb m p (fun E ↦ (reach (edgeGraph E) {v}).card < K) ≤ q := by
  have hmono := graphProb_mono hp0 hp1 (P := fun E ↦ (reach (edgeGraph E) {v}).card < K)
    (Q := fun E ↦ exploreDies E K m {v} {v}) fun E hE ↦
      exploreDies_of_card_reach_lt hE m Subset.rfl (subset_reach (edgeGraph E) {v}) (by simp)
  have hbound := graphProb_exploreDies_le hp0 hp1 hq0 hq1 hq m (D := {v}) (A := {v}) Subset.rfl
  rw [card_singleton, pow_one] at hbound
  exact hmono.trans hbound

/-! ### The constant and the lower bound -/

/-- **Eventually `(1 - α s'/m)^(m - K) ≤ 1 - s'`**, for `α > 1`, `0 < s' < s = giantFraction α` and
every `K`: below the giant fraction the survival map lies strictly above the diagonal. -/
theorem eventually_one_sub_pow_le {α s' : ℝ} (hα : 1 < α) (hs'0 : 0 < s')
    (hs' : s' < giantFraction α) (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, (1 - α / m * (1 - (1 - s'))) ^ (m - K) ≤ 1 - s' := by
  have hα0 : 0 < α := by linarith
  have hlt : Real.exp (-(α * s')) < 1 - s' := by
    have h := lt_survivalMap_of_lt hα0 hs'0 hs' (survivalMap_giantFraction α).ge
    unfold survivalMap at h
    linarith
  have hr1 : 1 < (1 - s') / Real.exp (-(α * s')) := by
    rw [one_lt_div (Real.exp_pos _)]
    exact hlt
  have hlim : Tendsto (fun m : ℕ ↦ Real.exp (α * s' * K / m)) atTop (𝓝 1) := by
    have h1 := (Real.continuous_exp.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (α * s' * K))
    rwa [Real.exp_zero] at h1
  filter_upwards [(tendsto_order.1 hlim).2 _ hr1, eventually_ge_atTop K,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (α * s'), eventually_gt_atTop 0]
    with m h1 h2 h3 h4
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
  have hm' : (m : ℝ) ≠ 0 := hm.ne'
  have hx : 1 - α / m * (1 - (1 - s')) = 1 - α * s' / m := by ring
  have hx0 : 0 ≤ 1 - α * s' / m := by
    rw [sub_nonneg, div_le_one hm]
    exact h3
  have hx1 : 1 - α * s' / m ≤ Real.exp (-(α * s' / m)) := by
    linarith [Real.add_one_le_exp (-(α * s' / m))]
  have hexp : Real.exp (-(α * s' / m)) ^ (m - K) =
      Real.exp (-(α * s')) * Real.exp (α * s' * K / m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sub h2]
    congr 1
    field_simp
    ring
  have h5 : Real.exp (-(α * s')) * Real.exp (α * s' * K / m) < 1 - s' := by
    have h6 := (lt_div_iff₀ (Real.exp_pos (-(α * s')))).mp h1
    linarith
  rw [hx]
  calc (1 - α * s' / m) ^ (m - K) ≤ Real.exp (-(α * s' / m)) ^ (m - K) :=
        pow_le_pow_left₀ hx0 hx1 _
    _ = Real.exp (-(α * s')) * Real.exp (α * s' * K / m) := hexp
    _ ≤ 1 - s' := h5.le

/-- **The bound survives a linear number of discovered features.** For `α > 1` and
`0 < s' < s = giantFraction α` there is `κ₀ > 0` such that `(1 - α s'/m)^(m - K) ≤ 1 - s'` for
every `m ≥ α` and every `K ≤ κ₀ m`. -/
theorem exists_one_sub_pow_le {α s' : ℝ} (hα : 1 < α) (hs'0 : 0 < s')
    (hs' : s' < giantFraction α) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ m K : ℕ, α ≤ m → (K : ℝ) ≤ κ₀ * m →
      (1 - α / m * (1 - (1 - s'))) ^ (m - K) ≤ 1 - s' := by
  have hα0 : 0 < α := by linarith
  have hs'1 : s' < 1 := hs'.trans (giantFraction_mem_Ioo hα).2
  have hlt : Real.exp (-(α * s')) < 1 - s' := by
    have h := lt_survivalMap_of_lt hα0 hs'0 hs' (survivalMap_giantFraction α).ge
    unfold survivalMap at h
    linarith
  have hαs' : 0 < α * s' := mul_pos hα0 hs'0
  have hαs'ne : α * s' ≠ 0 := hαs'.ne'
  have hr0 : 0 < (1 - s') / Real.exp (-(α * s')) := div_pos (by linarith) (Real.exp_pos _)
  have hr1 : 1 < (1 - s') / Real.exp (-(α * s')) := by
    rw [one_lt_div (Real.exp_pos _)]
    exact hlt
  have hlogr : Real.log ((1 - s') / Real.exp (-(α * s'))) < α * s' := by
    rw [Real.log_div (by linarith : (0 : ℝ) < 1 - s').ne' (Real.exp_pos _).ne', Real.log_exp]
    have := Real.log_neg (by linarith : (0 : ℝ) < 1 - s') (by linarith)
    linarith
  refine ⟨Real.log ((1 - s') / Real.exp (-(α * s'))) / (α * s'),
    div_pos (Real.log_pos hr1) hαs', fun m K hm hK ↦ ?_⟩
  have hm0 : (0 : ℝ) < m := hα0.trans_le hm
  have hm' : (m : ℝ) ≠ 0 := hm0.ne'
  have hκ1 : Real.log ((1 - s') / Real.exp (-(α * s'))) / (α * s') < 1 :=
    (div_lt_one hαs').mpr hlogr
  have hKm : K ≤ m := by
    have h1 : (K : ℝ) < m := by nlinarith
    exact_mod_cast h1.le
  have hKlog : α * s' * K / m ≤ Real.log ((1 - s') / Real.exp (-(α * s'))) := by
    rw [div_le_iff₀ hm0]
    calc α * s' * K ≤ α * s' * (Real.log ((1 - s') / Real.exp (-(α * s'))) / (α * s') * m) :=
          mul_le_mul_of_nonneg_left hK hαs'.le
      _ = Real.log ((1 - s') / Real.exp (-(α * s'))) / (α * s') * (α * s') * m := by ring
      _ = Real.log ((1 - s') / Real.exp (-(α * s'))) * m := by
          rw [div_mul_cancel₀ _ hαs'ne]
  have hx0 : 0 ≤ 1 - α * s' / m := by
    rw [sub_nonneg, div_le_one hm0]
    nlinarith
  have hx1 : 1 - α * s' / m ≤ Real.exp (-(α * s' / m)) := by
    linarith [Real.add_one_le_exp (-(α * s' / m))]
  have hx : 1 - α / m * (1 - (1 - s')) = 1 - α * s' / m := by ring
  rw [hx]
  calc (1 - α * s' / m) ^ (m - K) ≤ Real.exp (-(α * s' / m)) ^ (m - K) :=
        pow_le_pow_left₀ hx0 hx1 _
    _ = Real.exp (-(α * s') + α * s' * K / m) := by
        rw [← Real.exp_nat_mul, Nat.cast_sub hKm]
        congr 1
        field_simp
        ring
    _ ≤ Real.exp (-(α * s') + Real.log ((1 - s') / Real.exp (-(α * s')))) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = 1 - s' := by
        rw [Real.exp_add, Real.exp_log hr0, ← mul_div_assoc,
          mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

/-- **The lower bound with a linear threshold.** For `α > 1` and `η > 0` there is `κ₀ > 0` such
that for every `m ≥ α`, every `K ≤ κ₀ m` and every feature `v`, the component of `v` in
`G(m, α/m)` has at least `K` features with probability at least `s - η`. -/
theorem exists_forall_graphProb_card_reach_ge {α η : ℝ} (hα : 1 < α) (hη : 0 < η) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ m K : ℕ, α ≤ m → (K : ℝ) ≤ κ₀ * m → ∀ v : Fin m,
      giantFraction α - η ≤ graphProb m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  obtain ⟨s', hs'0, hs's, hs'η⟩ : ∃ s' : ℝ, 0 < s' ∧ s' < giantFraction α ∧
      giantFraction α - η ≤ s' :=
    ⟨max (giantFraction α - η) (giantFraction α / 2), lt_max_of_lt_right (by linarith),
      max_lt (by linarith) (by linarith), le_max_left _ _⟩
  obtain ⟨κ₀, hκ₀, hbound⟩ := exists_one_sub_pow_le hα hs'0 hs's
  refine ⟨κ₀, hκ₀, fun m K hm hK v ↦ ?_⟩
  have hm0 : (0 : ℝ) < m := hα0.trans_le hm
  have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm0.le
  have hp1 : α / m ≤ 1 := (div_le_one hm0).mpr hm
  have hlt := graphProb_card_reach_lt_le hp0 hp1 (q := 1 - s') (by linarith) (by linarith)
    (hbound m K hm hK) v
  have hadd := graphProb_add_not m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card)
  have hnot : graphProb m (α / m) (fun E ↦ ¬K ≤ (reach (edgeGraph E) {v}).card) ≤
      graphProb m (α / m) (fun E ↦ (reach (edgeGraph E) {v}).card < K) :=
    graphProb_mono hp0 hp1 fun _ h ↦ not_le.mp h
  linarith

/-- **The supercritical lower bound for one feature.** For `α > 1`, every `K` and `ε > 0`,
eventually every feature of `G(m, α/m)` lies in a component of at least `K` features with
probability at least `s - ε`, `s = giantFraction α`. No giant component theorem is assumed. -/
theorem eventually_graphProb_card_reach_ge {α : ℝ} (hα : 1 < α) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ v : Fin m,
      giantFraction α - ε ≤ graphProb m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card) := by
  have hα0 : 0 < α := by linarith
  by_cases hεs : giantFraction α ≤ ε
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h2 h3 v
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h3
    have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
    have hp1 : α / m ≤ 1 := (div_le_one hm).mpr h2
    linarith [graphProb_nonneg hp0 hp1 (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card)]
  · push_neg at hεs
    have hs' : 0 < giantFraction α - ε := by linarith
    have hs's : giantFraction α - ε < giantFraction α := by linarith
    filter_upwards [eventually_one_sub_pow_le hα hs' hs's K,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h1 h2 h3 v
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h3
    have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
    have hp1 : α / m ≤ 1 := (div_le_one hm).mpr h2
    have hs1 : giantFraction α < 1 := (giantFraction_mem_Ioo hα).2
    have hlt := graphProb_card_reach_lt_le hp0 hp1 (q := 1 - (giantFraction α - ε))
      (by linarith) (by linarith) h1 v
    have hadd := graphProb_add_not m (α / m) (fun E ↦ K ≤ (reach (edgeGraph E) {v}).card)
    have hnot : graphProb m (α / m) (fun E ↦ ¬K ≤ (reach (edgeGraph E) {v}).card) ≤
        graphProb m (α / m) (fun E ↦ (reach (edgeGraph E) {v}).card < K) :=
      graphProb_mono hp0 hp1 fun _ h ↦ not_le.mp h
    linarith

/-- **The expectation form of the lower bound.** For `α > 1`, every `K` and `ε > 0`, eventually the
expected number of features of `G(m, α/m)` in components of at least `K` features is at least
`(s - ε) m`. -/
theorem eventually_graphExpect_card_large_ge {α : ℝ} (hα : 1 < α) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (giantFraction α - ε) * m ≤ graphExpect m (α / m)
      (fun E ↦ ((univ.filter fun v ↦ K ≤ (reach (edgeGraph E) {v}).card).card : ℝ)) := by
  filter_upwards [eventually_graphProb_card_reach_ge hα K hε] with m hm
  have hcount : (fun E ↦ ((univ.filter fun v ↦ K ≤ (reach (edgeGraph E) {v}).card).card : ℝ)) =
      fun E ↦ ∑ v : Fin m, if K ≤ (reach (edgeGraph E) {v}).card then (1 : ℝ) else 0 := by
    funext E
    rw [natCast_card_filter]
  rw [hcount, graphExpect_sum]
  calc (giantFraction α - ε) * m = ∑ _v : Fin m, (giantFraction α - ε) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ v : Fin m, graphExpect m (α / m)
          (fun E ↦ if K ≤ (reach (edgeGraph E) {v}).card then (1 : ℝ) else 0) :=
        sum_le_sum fun v _ ↦ hm v

end

end Descent.Pangenome.AncestralLocality
