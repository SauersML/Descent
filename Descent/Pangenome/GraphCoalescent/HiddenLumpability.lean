/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLoads

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Strong lumpability of the hidden-load state, and the three-haplotype example

The spec is `PANGENOME_HIDDEN_CLOCK.md` §3, Theorem A: the claim that the report together with
its loads is a strong lumping of the labeled coalescent, and example (A4).

The hidden state `hiddenState s ξ` is the report `observed s ξ` together with, for every
individual, the load of its report component. A cover lands either on `invisibleTarget X x`,
where the report stays and the loads of `x`'s component drop by one, or on `visibleTarget X x y`,
where the report merges the components of `x` and `y` and the joined component carries
`a + b - 1`; which target it lands on is read off the hidden state `X` of the source
(`hiddenState_merge_of_rel`, `hiddenState_merge_of_not_rel`, `hiddenState_of_covers`). The covers
landing on `invisibleTarget X x` are exactly the invisible covers inside `x`'s component, so
there are `C(L, 2)` of them (`card_covers_invisibleTarget`); those landing on
`visibleTarget X x y` are exactly the visible covers joining the two components, so there are
`L_x L_y` of them (`card_covers_visibleTarget`); and no other hidden state receives a cover.
Hence two coalescent states with the same hidden state have equally many covers into every
hidden state. With Kingman's unit rate per cover this is Rosenblatt's criterion for the hidden
state: strong lumpability (`card_covers_hiddenState_eq`).

Example (A4). Three haplotypes, with `0` and `1` merged by the interface. From the singletons
the loads are `(2, 1)` (`example_loads_bot`), the invisible rate is `1` and the visible rate is
`2` (`example_invisible_rate`, `example_visible_rate`), and the total rate is `3`
(`example_total_rate`). After the invisible merger the loads are `(1, 1)`
(`example_loads_after_invisible`) and the visible rate is `1` (`example_visible_rate_after`).
First-step analysis with these rates gives the mean connection time `1/3 + (1/3)(1) = 2/3`
(`example_mean_connection_time`).

Scope. Rates here are cover counts with unit rate per cover. The continuous-time chain, its
survival function `(1/2) e^{-3t} + (1/2) e^{-t}`, and the probabilistic statement of lumpability
are not constructed; the mean connection time is the first-step arithmetic of the counted rates.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set, and the example's
numbers are those counts, so no measurement can bear on them.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

/-! ### The hidden state and its two kinds of target -/

/-- **The hidden state** `X(ξ) = (Y, L)`: the graph's report, and for every individual the load of
its report component. -/
def hiddenState {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : ER n × (Fin n → ℕ) :=
  (observed s ξ, fun z ↦ hiddenLoad s ξ (Quotient.mk (observed s ξ) z))

/-- The hidden state an invisible merger inside the component of `x` produces: the report stays
and the loads of `x`'s component drop by one. -/
def invisibleTarget {n : ℕ} (X : ER n × (Fin n → ℕ)) (x : Fin n) : ER n × (Fin n → ℕ) :=
  (X.1, fun z ↦ if X.1.r x z then X.2 z - 1 else X.2 z)

/-- The hidden state a visible merger joining the components of `x` and `y` produces: the report
merges the two components and the joined component carries `a + b - 1`. -/
def visibleTarget {n : ℕ} (X : ER n × (Fin n → ℕ)) (x y : Fin n) : ER n × (Fin n → ℕ) :=
  (merge X.1 (Quotient.mk X.1 x) (Quotient.mk X.1 y),
    fun z ↦ if X.1.r x z ∨ X.1.r y z then X.2 x + X.2 y - 1 else X.2 z)

/-- The invisible target depends on `x` only through its report component. -/
theorem invisibleTarget_eq_of_rel {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {u x : Fin n}
    (h : (observed s ξ).r u x) :
    invisibleTarget (hiddenState s ξ) u = invisibleTarget (hiddenState s ξ) x := by
  refine Prod.ext rfl (funext fun z ↦ ?_)
  have hiff : (observed s ξ).r u z ↔ (observed s ξ).r x z :=
    ⟨fun huz ↦ (observed s ξ).iseqv.trans ((observed s ξ).iseqv.symm h) huz,
      fun hxz ↦ (observed s ξ).iseqv.trans h hxz⟩
  show (if (observed s ξ).r u z then hiddenLoad s ξ (Quotient.mk (observed s ξ) z) - 1
      else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)) =
    if (observed s ξ).r x z then hiddenLoad s ξ (Quotient.mk (observed s ξ) z) - 1
      else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)
  simp only [hiff]

/-- The visible target depends on `x` and `y` only through their report components. -/
theorem visibleTarget_eq_of_rel {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {u v x y : Fin n}
    (hu : (observed s ξ).r u x) (hv : (observed s ξ).r v y) :
    visibleTarget (hiddenState s ξ) u v = visibleTarget (hiddenState s ξ) x y := by
  have hux : Quotient.mk (observed s ξ) u = Quotient.mk (observed s ξ) x := Quotient.sound hu
  have hvy : Quotient.mk (observed s ξ) v = Quotient.mk (observed s ξ) y := Quotient.sound hv
  refine Prod.ext ?_ (funext fun z ↦ ?_)
  · show merge (observed s ξ) (Quotient.mk (observed s ξ) u) (Quotient.mk (observed s ξ) v) =
      merge (observed s ξ) (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y)
    rw [hux, hvy]
  · have hiff : ((observed s ξ).r u z ∨ (observed s ξ).r v z) ↔
        ((observed s ξ).r x z ∨ (observed s ξ).r y z) := by
      constructor
      · rintro (h | h)
        · exact Or.inl ((observed s ξ).iseqv.trans ((observed s ξ).iseqv.symm hu) h)
        · exact Or.inr ((observed s ξ).iseqv.trans ((observed s ξ).iseqv.symm hv) h)
      · rintro (h | h)
        · exact Or.inl ((observed s ξ).iseqv.trans hu h)
        · exact Or.inr ((observed s ξ).iseqv.trans hv h)
    show (if (observed s ξ).r u z ∨ (observed s ξ).r v z then
        hiddenLoad s ξ (Quotient.mk (observed s ξ) u) +
          hiddenLoad s ξ (Quotient.mk (observed s ξ) v) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)) =
      if (observed s ξ).r x z ∨ (observed s ξ).r y z then
        hiddenLoad s ξ (Quotient.mk (observed s ξ) x) +
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1
        else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)
    rw [hux, hvy]
    simp only [hiff]

/-- An invisible merger lands on the invisible target of its component. -/
theorem hiddenState_merge_of_rel {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {x y : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : (observed s ξ).r x y) :
    hiddenState s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y)) =
      invisibleTarget (hiddenState s ξ) x := by
  refine Prod.ext (observed_merge_of_rel hab hxy) (funext fun z ↦ ?_)
  show hiddenLoad s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
      (Quotient.mk (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))) z) =
    if (observed s ξ).r x z then hiddenLoad s ξ (Quotient.mk (observed s ξ) z) - 1
      else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)
  by_cases hxz : (observed s ξ).r x z
  · rw [if_pos hxz,
      Quotient.sound (observed_mono s (le_merge ξ _ _) ((observed s ξ).iseqv.symm hxz) :
        (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))).r z x),
      Quotient.sound ((observed s ξ).iseqv.symm hxz : (observed s ξ).r z x)]
    exact hiddenLoad_merge_of_rel_self hab hxy
  · rw [if_neg hxz]
    exact hiddenLoad_merge_of_rel_of_not_rel hab hxy hxz

/-- A visible merger lands on the visible target of the two components it joins. -/
theorem hiddenState_merge_of_not_rel {n : ℕ} {s : Fin n → Fin n} {ξ : ER n} {x y : Fin n}
    (hab : Quotient.mk ξ x ≠ Quotient.mk ξ y) (hxy : ¬ (observed s ξ).r x y) :
    hiddenState s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y)) =
      visibleTarget (hiddenState s ξ) x y := by
  refine Prod.ext (observed_merge_of_not_rel hab hxy) (funext fun z ↦ ?_)
  show hiddenLoad s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
      (Quotient.mk (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))) z) =
    if (observed s ξ).r x z ∨ (observed s ξ).r y z then
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) +
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) - 1
      else hiddenLoad s ξ (Quotient.mk (observed s ξ) z)
  by_cases hz : (observed s ξ).r x z ∨ (observed s ξ).r y z
  · rw [if_pos hz]
    have hzx : (observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))).r z x := by
      rw [observed_merge_of_not_rel hab hxy, merge_rel_iff_of_not_rel _ hxy]
      rcases hz with hxz | hyz
      · exact Or.inl ((observed s ξ).iseqv.symm hxz)
      · exact Or.inr (Or.inr ⟨(observed s ξ).iseqv.symm hyz, (observed s ξ).iseqv.refl x⟩)
    rw [Quotient.sound hzx]
    exact hiddenLoad_merge_of_not_rel_self hab hxy
  · rw [if_neg hz]
    exact hiddenLoad_merge_of_not_rel_of_not_rel hab hxy (fun h ↦ hz (Or.inl h))
      (fun h ↦ hz (Or.inr h))

/-- **Every cover lands on a target read off the source's hidden state.** -/
theorem hiddenState_of_covers {n : ℕ} (s : Fin n → Fin n) {ξ η : ER n} (h : Covers ξ η) :
    (∃ u, hiddenState s η = invisibleTarget (hiddenState s ξ) u) ∨
      ∃ u v, ¬ (observed s ξ).r u v ∧ hiddenState s η = visibleTarget (hiddenState s ξ) u v := by
  obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp h
  obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ A
  obtain ⟨v, rfl⟩ := quotient_mk_surjective ξ B
  by_cases huv : (observed s ξ).r u v
  · exact Or.inl ⟨u, hiddenState_merge_of_rel hAB huv⟩
  · exact Or.inr ⟨u, v, huv, hiddenState_merge_of_not_rel hAB huv⟩

/-! ### Counting the covers into each hidden state -/

/-- The covers landing on the invisible target of `x`'s component are exactly its invisible
covers. -/
theorem covers_hiddenState_eq_invisibleTarget_iff {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    (x : Fin n) (η : ER n) :
    Covers ξ η ∧ hiddenState s η = invisibleTarget (hiddenState s ξ) x ↔
      η ∈ invisibleCovers s ξ (Quotient.mk (observed s ξ) x) := by
  constructor
  · rintro ⟨hcov, hstate⟩
    obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ A
    obtain ⟨v, rfl⟩ := quotient_mk_surjective ξ B
    by_cases huv : (observed s ξ).r u v
    · rw [hiddenState_merge_of_rel hAB huv] at hstate
      have hux : (observed s ξ).r u x := by
        by_contra hux
        have hload := congrFun (congrArg Prod.snd hstate) x
        change (if (observed s ξ).r u x then hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
            else hiddenLoad s ξ (Quotient.mk (observed s ξ) x)) =
          (if (observed s ξ).r x x then hiddenLoad s ξ (Quotient.mk (observed s ξ) x) - 1
            else hiddenLoad s ξ (Quotient.mk (observed s ξ) x)) at hload
        rw [if_neg hux, if_pos ((observed s ξ).iseqv.refl x)] at hload
        have hpos := hiddenLoad_pos s ξ (Quotient.mk (observed s ξ) x)
        omega
      exact ⟨Quotient.mk ξ u, (mk_mem_hiddenBlocks_iff s ξ u x).mpr hux, Quotient.mk ξ v,
        (mk_mem_hiddenBlocks_iff s ξ v x).mpr
          ((observed s ξ).iseqv.trans ((observed s ξ).iseqv.symm huv) hux), hAB, rfl⟩
    · exfalso
      rw [hiddenState_merge_of_not_rel hAB huv] at hstate
      have hfirst : merge (observed s ξ) (Quotient.mk (observed s ξ) u)
          (Quotient.mk (observed s ξ) v) = observed s ξ := congrArg Prod.fst hstate
      have hcov' := merge_covers (observed s ξ)
        (fun hq ↦ huv (Quotient.exact hq) :
          Quotient.mk (observed s ξ) u ≠ Quotient.mk (observed s ξ) v)
      rw [hfirst] at hcov'
      have hblocks := hcov'.2
      omega
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ a
    obtain ⟨v, rfl⟩ := quotient_mk_surjective ξ b
    have hux := (mk_mem_hiddenBlocks_iff s ξ u x).mp ha
    have hvx := (mk_mem_hiddenBlocks_iff s ξ v x).mp hb
    have huv : (observed s ξ).r u v :=
      (observed s ξ).iseqv.trans hux ((observed s ξ).iseqv.symm hvx)
    exact ⟨merge_covers ξ hab,
      (hiddenState_merge_of_rel hab huv).trans (invisibleTarget_eq_of_rel s ξ hux)⟩

/-- The covers landing on the visible target of two components are exactly the visible covers
joining them. -/
theorem covers_hiddenState_eq_visibleTarget_iff {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) (η : ER n) :
    Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) x y ↔
      η ∈ visibleCovers s ξ (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y) := by
  have hCD : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  constructor
  · rintro ⟨hcov, hstate⟩
    obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ A
    obtain ⟨v, rfl⟩ := quotient_mk_surjective ξ B
    by_cases huv : (observed s ξ).r u v
    · exfalso
      rw [hiddenState_merge_of_rel hAB huv] at hstate
      have hfirst : observed s ξ = merge (observed s ξ) (Quotient.mk (observed s ξ) x)
          (Quotient.mk (observed s ξ) y) := congrArg Prod.fst hstate
      have hcov' := merge_covers (observed s ξ) hCD
      rw [← hfirst] at hcov'
      have hblocks := hcov'.2
      omega
    · rw [hiddenState_merge_of_not_rel hAB huv] at hstate
      have hfirst : merge (observed s ξ) (Quotient.mk (observed s ξ) u)
          (Quotient.mk (observed s ξ) v) = merge (observed s ξ) (Quotient.mk (observed s ξ) x)
            (Quotient.mk (observed s ξ) y) := congrArg Prod.fst hstate
      have hUV : Quotient.mk (observed s ξ) u ≠ Quotient.mk (observed s ξ) v :=
        fun hq ↦ huv (Quotient.exact hq)
      have hpair := (merge_eq_merge_iff (observed s ξ) hUV hCD).mp hfirst
      have hu : Quotient.mk (observed s ξ) u ∈
          ({Quotient.mk (observed s ξ) x, Quotient.mk (observed s ξ) y} : Finset _) :=
        hpair ▸ mem_insert_self _ _
      have hv : Quotient.mk (observed s ξ) v ∈
          ({Quotient.mk (observed s ξ) x, Quotient.mk (observed s ξ) y} : Finset _) :=
        hpair ▸ mem_insert_of_mem (mem_singleton_self _)
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with hu | hu
      · rcases hv with hv | hv
        · exact absurd (hu.trans hv.symm) hUV
        · exact ⟨Quotient.mk ξ u, (mk_mem_hiddenBlocks_iff s ξ u x).mpr (Quotient.exact hu),
            Quotient.mk ξ v, (mk_mem_hiddenBlocks_iff s ξ v y).mpr (Quotient.exact hv), rfl⟩
      · rcases hv with hv | hv
        · exact ⟨Quotient.mk ξ v, (mk_mem_hiddenBlocks_iff s ξ v x).mpr (Quotient.exact hv),
            Quotient.mk ξ u, (mk_mem_hiddenBlocks_iff s ξ u y).mpr (Quotient.exact hu),
            merge_comm ξ hAB⟩
        · exact absurd (hu.trans hv.symm) hUV
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ a
    obtain ⟨v, rfl⟩ := quotient_mk_surjective ξ b
    have hux := (mk_mem_hiddenBlocks_iff s ξ u x).mp ha
    have hvy := (mk_mem_hiddenBlocks_iff s ξ v y).mp hb
    have huv : ¬ (observed s ξ).r u v := fun huv ↦ hxy ((observed s ξ).iseqv.trans
      ((observed s ξ).iseqv.symm hux) ((observed s ξ).iseqv.trans huv hvy))
    have hab : Quotient.mk ξ u ≠ Quotient.mk ξ v :=
      fun hq ↦ huv (le_observed s ξ (Quotient.exact hq))
    exact ⟨merge_covers ξ hab,
      (hiddenState_merge_of_not_rel hab huv).trans (visibleTarget_eq_of_rel s ξ hux hvy)⟩

/-- **Spec (A1) as a lumped rate**: the hidden state reached by an invisible merger inside a
component hiding `L` lineages is reached by `C(L, 2)` covers. -/
theorem card_covers_invisibleTarget {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (x : Fin n) :
    Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = invisibleTarget (hiddenState s ξ) x} =
      (hiddenLoad s ξ (Quotient.mk (observed s ξ) x)).choose 2 := by
  rw [← card_invisibleCovers]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun η ↦ covers_hiddenState_eq_invisibleTarget_iff s ξ x η)

/-- **Spec (A2) as a lumped rate**: the hidden state reached by a visible merger of two components
hiding `L_x` and `L_y` lineages is reached by `L_x L_y` covers. -/
theorem card_covers_visibleTarget {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {x y : Fin n}
    (hxy : ¬ (observed s ξ).r x y) :
    Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = visibleTarget (hiddenState s ξ) x y} =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) := by
  rw [← card_visibleCovers s ξ fun hq ↦ hxy (Quotient.exact hq)]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun η ↦ covers_hiddenState_eq_visibleTarget_iff s ξ hxy η)

/-- **Strong lumpability (spec Theorem A).** Two coalescent states with the same report and the
same loads have equally many covers, hence the same aggregate unit rate, into every hidden
state. -/
theorem card_covers_hiddenState_eq {n : ℕ} (s : Fin n → Fin n) {ξ ξ' : ER n}
    (h : hiddenState s ξ = hiddenState s ξ') (v : ER n × (Fin n → ℕ)) :
    Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = v} =
      Nat.card {η : ER n // Covers ξ' η ∧ hiddenState s η = v} := by
  have hreport : observed s ξ = observed s ξ' := congrArg Prod.fst h
  have hload : ∀ x, hiddenLoad s ξ (Quotient.mk (observed s ξ) x) =
      hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) := fun x ↦ congrFun (congrArg Prod.snd h) x
  by_cases hinv : ∃ x, v = invisibleTarget (hiddenState s ξ) x
  · obtain ⟨x, rfl⟩ := hinv
    rw [card_covers_invisibleTarget s ξ x, h, card_covers_invisibleTarget s ξ' x, hload]
  · by_cases hvis : ∃ x y, ¬ (observed s ξ).r x y ∧ v = visibleTarget (hiddenState s ξ) x y
    · obtain ⟨x, y, hxy, rfl⟩ := hvis
      have hxy' : ¬ (observed s ξ').r x y := hreport ▸ hxy
      rw [card_covers_visibleTarget s ξ hxy, h, card_covers_visibleTarget s ξ' hxy', hload,
        hload]
    · have hnone : ∀ ζ : ER n, hiddenState s ζ = hiddenState s ξ →
          IsEmpty {η : ER n // Covers ζ η ∧ hiddenState s η = v} := by
        intro ζ hζ
        refine ⟨fun ⟨η, hcov, hstate⟩ ↦ ?_⟩
        rcases hiddenState_of_covers s hcov with ⟨u, hu⟩ | ⟨u, w, huw, hw⟩
        · exact hinv ⟨u, hstate.symm.trans (hu.trans (by rw [hζ]))⟩
        · have hreportζ : observed s ζ = observed s ξ := congrArg Prod.fst hζ
          exact hvis ⟨u, w, hreportζ ▸ huw, hstate.symm.trans (hw.trans (by rw [hζ]))⟩
      have h1 := hnone ξ rfl
      have h2 := hnone ξ' h.symm
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

/-! ### Example (A4): three haplotypes, two graph states -/

/-- The interface of example (A4): haplotypes `0` and `1` occupy one graph state and `2` is
alone. -/
def exampleInterface : Fin 3 → Fin 3 := ![0, 0, 2]

/-- The graph state of `0` holds two haplotypes. -/
theorem exampleInterface_fiberCard_zero : Linkage.fiberCard exampleInterface 0 = 2 := by
  decide

/-- The graph state of `2` holds one haplotype. -/
theorem exampleInterface_fiberCard_two : Linkage.fiberCard exampleInterface 2 = 1 := by
  decide

/-- The interface reports `0` and `1` together. -/
theorem example_rel_zero_one : (observed exampleInterface ⊥).r 0 1 := by
  rw [observed_bot, graphKer_rel_iff]
  decide

/-- The interface reports `0` and `2` apart. -/
theorem example_not_rel_zero_two : ¬ (observed exampleInterface ⊥).r 0 2 := by
  rw [observed_bot, graphKer_rel_iff]
  decide

/-- Haplotypes `0` and `1` are distinct lineages before any coalescence. -/
theorem example_ne_zero_one : Quotient.mk (⊥ : ER 3) 0 ≠ Quotient.mk (⊥ : ER 3) 1 :=
  fun hq ↦ absurd (Quotient.exact hq : (0 : Fin 3) = 1) (by decide)

/-- **Example (A4), the starting loads `(2, 1)`.** -/
theorem example_loads_bot :
    hiddenLoad exampleInterface ⊥ (Quotient.mk (observed exampleInterface ⊥) 0) = 2 ∧
      hiddenLoad exampleInterface ⊥ (Quotient.mk (observed exampleInterface ⊥) 2) = 1 := by
  rw [hiddenLoad_bot, hiddenLoad_bot, exampleInterface_fiberCard_zero,
    exampleInterface_fiberCard_two]
  exact ⟨rfl, rfl⟩

/-- **Example (A4), invisible rate `1`.** -/
theorem example_invisible_rate :
    Nat.card (invisibleCovers exampleInterface ⊥
      (Quotient.mk (observed exampleInterface ⊥) 0)) = 1 := by
  rw [card_invisibleCovers, example_loads_bot.1]
  rfl

/-- **Example (A4), visible rate `2`.** -/
theorem example_visible_rate :
    Nat.card (visibleCovers exampleInterface ⊥ (Quotient.mk (observed exampleInterface ⊥) 0)
      (Quotient.mk (observed exampleInterface ⊥) 2)) = 2 := by
  rw [card_visibleCovers_bot exampleInterface (by decide), exampleInterface_fiberCard_zero,
    exampleInterface_fiberCard_two]

/-- **Example (A4), total rate `3`**: one invisible and two visible covers, all `C(3, 2)`
covers of the singletons. -/
theorem example_total_rate : Nat.card {η : ER 3 // Covers ⊥ η} = 3 := by
  rw [card_covers, blocks_bot]
  rfl

/-- **Example (A4), the loads `(1, 1)` after the invisible merger.** -/
theorem example_loads_after_invisible :
    hiddenLoad exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))
        (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
          0) = 1 ∧
      hiddenLoad exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))
        (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
          2) = 1 := by
  constructor
  · rw [hiddenLoad_merge_of_rel_self example_ne_zero_one example_rel_zero_one,
      example_loads_bot.1]
  · rw [hiddenLoad_merge_of_rel_of_not_rel example_ne_zero_one example_rel_zero_one
      example_not_rel_zero_two, example_loads_bot.2]

/-- **Example (A4), visible rate `1` after the invisible merger.** -/
theorem example_visible_rate_after :
    Nat.card (visibleCovers exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))
      (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))) 0)
      (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
        2)) = 1 := by
  have hCD : Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0)
      (Quotient.mk ⊥ 1))) 0 ≠ Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0)
        (Quotient.mk ⊥ 1))) 2 := by
    intro hq
    have hrel := Quotient.exact hq
    rw [observed_merge_of_rel example_ne_zero_one example_rel_zero_one] at hrel
    exact example_not_rel_zero_two hrel
  rw [card_visibleCovers _ _ hCD, example_loads_after_invisible.1,
    example_loads_after_invisible.2]

/-- **Example (A4), the mean connection time `2/3`.** From loads `(2, 1)` the total rate is `3`:
the reported connection waits a mean `1/3`, and with probability `1/3` the move is the invisible
merger, after which the only move is the visible merger at rate `1`. -/
theorem example_mean_connection_time :
    (1 : ℝ) / (Nat.card (invisibleCovers exampleInterface ⊥
          (Quotient.mk (observed exampleInterface ⊥) 0)) +
        Nat.card (visibleCovers exampleInterface ⊥ (Quotient.mk (observed exampleInterface ⊥) 0)
          (Quotient.mk (observed exampleInterface ⊥) 2))) +
      (Nat.card (invisibleCovers exampleInterface ⊥
          (Quotient.mk (observed exampleInterface ⊥) 0)) : ℝ) /
        (Nat.card (invisibleCovers exampleInterface ⊥
            (Quotient.mk (observed exampleInterface ⊥) 0)) +
          Nat.card (visibleCovers exampleInterface ⊥
            (Quotient.mk (observed exampleInterface ⊥) 0)
            (Quotient.mk (observed exampleInterface ⊥) 2))) *
        (1 / Nat.card (visibleCovers exampleInterface
          (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))
          (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
            0)
          (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
            2))) = 2 / 3 := by
  rw [example_invisible_rate, example_visible_rate, example_visible_rate_after]
  norm_num

end

end Descent.Pangenome.GraphCoalescent
