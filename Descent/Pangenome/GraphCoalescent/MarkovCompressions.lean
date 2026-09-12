/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Split
import Descent.Pangenome.GraphCoalescent.LumpingVisibleRates
import Descent.Pangenome.GraphCoalescent.Visibility

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Which pangenome compressions keep the reported ancestry Markov

A pangenome interface `s : Fin n → Fin n` of width `w` compresses a panel of `n` haplotypes into
`w` graph states. A graph reports the coalescent state `ξ` as `observed s ξ = ξ ⊔ graphKer s`.
Theorem B of the hidden-lineage clock (`CoarsestRefinement`) gives the coarsest Markov refinement
of a given report. This module answers the reverse question. For which interfaces is the report
process itself a strong lumping of Kingman's coalescent, so that the apparent law of ancestry is
Markov with no hidden state?

**The classification.** `IsReportLumping s` is Rosenblatt's criterion for the report, in the form
of `LumpingVisibleRates`: states with the same report have equally many covers into every other
report. `isReportLumping_iff`: it holds exactly when `w = n` or `w ≤ 1`. An interface that merges
nothing reports the coalescent itself (`isReportLumping_of_injective`), and an interface that
merges everything reports a constant (`isReportLumping_of_width_le_one`). Every other interface
fails, and the failure is a count (`not_isReportLumping_of_width`). The states `⊥` and
`graphKer s` have the same report, and every component of the report of `graphKer s` holds one
true block (`hiddenLoad_graphKer`). So `graphKer s` offers one cover into the merge of two
components (`card_covers_graphKer_merge`), while `⊥` offers `c_a c_c` of them
(`card_covers_bot_merge`). That product is at least two when `a` shares its graph state with
another haplotype and `c` lies in another state.

**The corpus criterion.** `Visibility.ObservablyMarkov` also asks for equally many covers into a
state's own report. `observablyMarkov_iff_injective`: that holds exactly when `w = n`. The two
criteria differ exactly at the collapsing interfaces `w = 1 < n`, where the report is constant
but the covers into it count the true blocks.

**How much state a compression hides.** By Theorem B the minimal extra state is the loads. For
the report component of a haplotype, `componentSize` counts its haplotypes `|C|` and
`componentWidth` its graph states `w_C`. The load satisfies `L_C + w_C ≤ |C| + 1`
(`hiddenLoad_add_componentWidth_le`), with equality at `⊥`, where `L_C = |C|` and `w_C = 1`
(`componentSize_bot`, `componentWidth_bot`). The proof runs along the covering order from `⊥`
(`Split.exists_covers_of_ne_bot`):
- an invisible merger lowers a load and keeps the component;
- a visible merger adds the sizes and the widths of the two components it joins
  (`filter_merge_rel_of_rel`), and adds their loads less one.

Significance. A compression changes the apparent law of ancestry for every interface that merges
something without collapsing the panel. Exactly then the reported coalescent needs hidden loads,
and the load of each component ranges within `1 ≤ L_C ≤ |C| - w_C + 1`.

Not formalized here: that every load vector in that range is attained, and the resulting count of
the values of the coarsest refinement over each report. Those belong to the counting module.

## Empirical status

None. The bodies here are counts of equivalence classes and of covers on a finite set; the
interface is supplied, and no measurement can bear on a cardinality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MarkovCompressions

open Coalescent Finset LumpingVisibleRates
open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### The criterion and the classification -/

/-- **Rosenblatt's criterion for the report.** Two coalescent states with the same report have
equally many covers into every other report: the report process is a strong lumping of Kingman's
coalescent, and its jump rates are functions of the report alone. -/
def IsReportLumping (s : Fin n → Fin n) : Prop :=
  ∀ ξ ξ' : ER n, observed s ξ = observed s ξ' → ∀ v : ER n, v ≠ observed s ξ →
    Nat.card {η : ER n // Covers ξ η ∧ observed s η = v} =
      Nat.card {η : ER n // Covers ξ' η ∧ observed s η = v}

/-- An interface occupies `n` graph states exactly when it merges no two haplotypes. -/
theorem injective_iff_width_eq (s : Fin n → Fin n) :
    Function.Injective s ↔ Linkage.width s = n := by
  constructor
  · intro hs
    rw [Linkage.width, card_image_of_injective _ hs, card_univ, Fintype.card_fin]
  · intro hw
    have hcard : (univ.image s).card = (univ : Finset (Fin n)).card := by
      rw [card_univ, Fintype.card_fin]
      exact hw
    have hinj := card_image_iff.mp hcard
    exact fun x y hxy ↦ hinj (mem_coe.mpr (mem_univ x)) (mem_coe.mpr (mem_univ y)) hxy

/-- **The graph's floor hides nothing.** Every component of the report of `graphKer s` holds
exactly one true block. -/
theorem hiddenLoad_graphKer (s : Fin n → Fin n) (x : Fin n) :
    hiddenLoad s (graphKer s) (Quotient.mk (observed s (graphKer s)) x) = 1 := by
  rw [hiddenLoad, card_eq_one]
  refine ⟨Quotient.mk (graphKer s) x, ?_⟩
  ext b
  obtain ⟨y, rfl⟩ := quotient_mk_surjective (graphKer s) b
  rw [mem_singleton, mk_mem_hiddenBlocks_iff, observed_graphKer]
  exact ⟨fun h ↦ Quotient.sound h, fun h ↦ Quotient.exact h⟩

/-- From the singletons, the covers into the merge of the components of `a` and `c` number the
product of their fiber sizes. -/
theorem card_covers_bot_merge (s : Fin n → Fin n) {a c : Fin n} (hac : s a ≠ s c) :
    Nat.card {η : ER n // Covers ⊥ η ∧ observed s η =
        merge (observed s ⊥) (Quotient.mk (observed s ⊥) a) (Quotient.mk (observed s ⊥) c)} =
      Linkage.fiberCard s a * Linkage.fiberCard s c := by
  have hrel : ¬ (observed s ⊥).r a c := by
    rw [observed_bot, graphKer_rel_iff]
    exact hac
  rw [card_covers_observed_eq_merge s ⊥ hrel, hiddenLoad_bot, hiddenLoad_bot]

/-- From the graph's floor, the covers into the merge of two components number one. -/
theorem card_covers_graphKer_merge (s : Fin n → Fin n) {a c : Fin n} (hac : s a ≠ s c) :
    Nat.card {η : ER n // Covers (graphKer s) η ∧ observed s η =
        merge (observed s ⊥) (Quotient.mk (observed s ⊥) a) (Quotient.mk (observed s ⊥) c)} =
      1 := by
  have hrel : ¬ (observed s (graphKer s)).r a c := by
    rw [observed_graphKer, graphKer_rel_iff]
    exact hac
  have h := card_covers_observed_eq_merge s (graphKer s) hrel
  rw [hiddenLoad_graphKer, hiddenLoad_graphKer, one_mul,
    ← observed_bot_eq_observed_graphKer s] at h
  exact h

/-- **An interface that merges something without collapsing the panel is not a lumping.** For
width at least two and less than `n`, the states `⊥` and `graphKer s` share a report but offer
different numbers of covers into the merge of two components. -/
theorem not_isReportLumping_of_width {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) : ¬ IsReportLumping s := by
  intro hlump
  obtain ⟨a, b, c, hab, hsab, hc⟩ := exists_witness_of_width hw hlt
  have hac : s a ≠ s c := fun h ↦ hc h.symm
  have hrel : ¬ (observed s ⊥).r a c := by
    rw [observed_bot, graphKer_rel_iff]
    exact hac
  have hmerge : merge (observed s ⊥) (Quotient.mk (observed s ⊥) a)
      (Quotient.mk (observed s ⊥) c) ≠ observed s ⊥ := by
    intro h
    have hcov := merge_covers (observed s ⊥)
      (fun hq ↦ hrel (Quotient.exact hq) :
        Quotient.mk (observed s ⊥) a ≠ Quotient.mk (observed s ⊥) c)
    rw [h] at hcov
    have hblocks := hcov.2
    omega
  have hcount := hlump ⊥ (graphKer s) (observed_bot_eq_observed_graphKer s) _ hmerge
  rw [card_covers_bot_merge s hac, card_covers_graphKer_merge s hac] at hcount
  have htwo : 2 ≤ Linkage.fiberCard s a :=
    one_lt_card.mpr ⟨a, Linkage.self_mem_fiber s a, b, Linkage.mem_fiber.mpr hsab.symm, hab⟩
  have hone : 1 ≤ Linkage.fiberCard s c := Linkage.fiberCard_pos s c
  have hproduct := Nat.mul_le_mul htwo hone
  omega

/-- **A faithful interface lumps.** When the interface merges no two haplotypes, states with the
same report are the same state. -/
theorem isReportLumping_of_injective {s : Fin n → Fin n} (hs : Function.Injective s) :
    IsReportLumping s := by
  intro ξ ξ' h v _
  rw [observed_eq_of_injective hs ξ, observed_eq_of_injective hs ξ'] at h
  rw [h]

/-- **A collapsing interface lumps.** When the interface occupies at most one graph state, every
state has the same report, so no cover leads to another report. -/
theorem isReportLumping_of_width_le_one {s : Fin n → Fin n} (hw : Linkage.width s ≤ 1) :
    IsReportLumping s := by
  have hall : ∀ (ξ : ER n) (x y : Fin n), (observed s ξ).r x y := by
    intro ξ x y
    have hxy : s x = s y :=
      card_le_one.mp hw (s x) (mem_image_of_mem s (mem_univ x)) (s y)
        (mem_image_of_mem s (mem_univ y))
    exact graphKer_le_observed s ξ (graphKer_rel_iff.mpr hxy)
  have hreport : ∀ ξ ξ' : ER n, observed s ξ = observed s ξ' := fun ξ ξ' ↦
    Setoid.ext fun x y ↦ ⟨fun _ ↦ hall ξ' x y, fun _ ↦ hall ξ x y⟩
  intro ξ ξ' _ v hv
  have hempty : ∀ ζ : ER n, Nat.card {η : ER n // Covers ζ η ∧ observed s η = v} = 0 := by
    intro ζ
    rw [Nat.card_eq_zero]
    refine Or.inl ⟨?_⟩
    rintro ⟨η, -, hη⟩
    exact hv (hη.symm.trans (hreport η ξ))
  rw [hempty ξ, hempty ξ']

/-- The identity interface satisfies the criterion. -/
theorem isReportLumping_id : IsReportLumping (id : Fin n → Fin n) :=
  isReportLumping_of_injective Function.injective_id

/-- **Which compressions keep the reported ancestry Markov.** The report of an interface is a
strong lumping of Kingman's coalescent exactly when the interface merges nothing, `w = n`, or
collapses the panel, `w ≤ 1`. -/
theorem isReportLumping_iff (s : Fin n → Fin n) :
    IsReportLumping s ↔ Linkage.width s = n ∨ Linkage.width s ≤ 1 := by
  constructor
  · intro hlump
    by_contra hcon
    push_neg at hcon
    have hle : Linkage.width s ≤ n := by
      simpa using Linkage.width_le_card s
    exact not_isReportLumping_of_width (by omega) (lt_of_le_of_ne hle hcon.1) hlump
  · rintro (hw | hw)
    · exact isReportLumping_of_injective ((injective_iff_width_eq s).mpr hw)
    · exact isReportLumping_of_width_le_one hw

/-- **The corpus criterion counts the diagonal too.** `Visibility.ObservablyMarkov`, which also
asks for equally many covers into a state's own report, holds exactly for the faithful
interfaces. At a collapsing interface of at least two haplotypes, `⊥` and `graphKer s` share a
report, and `⊥` has a cover into it while `graphKer s` has no cover at all. -/
theorem observablyMarkov_iff_injective (s : Fin n → Fin n) :
    ObservablyMarkov s ↔ Function.Injective s := by
  refine ⟨fun hM ↦ ?_, observablyMarkov_of_injective⟩
  by_contra hs
  obtain ⟨a, b, hsab, hab⟩ := Function.not_injective_iff.mp hs
  have hwn : Linkage.width s ≠ n := fun hw ↦ hs ((injective_iff_width_eq s).mpr hw)
  have hle : Linkage.width s ≤ n := by
    simpa using Linkage.width_le_card s
  by_cases hw : 2 ≤ Linkage.width s
  · exact not_observablyMarkov_of_width_lt hw (lt_of_le_of_ne hle hwn) hM
  · haveI : NeZero n := ⟨(Fin.pos a).ne'⟩
    have hAB : Quotient.mk (⊥ : ER n) a ≠ Quotient.mk (⊥ : ER n) b :=
      fun hq ↦ hab (Quotient.exact hq)
    have hrel : (observed s ⊥).r a b := by
      rw [observed_bot, graphKer_rel_iff]
      exact hsab
    obtain ⟨e⟩ := hM ⊥ (graphKer s) (observed_bot_eq_observed_graphKer s) (observed s ⊥)
    obtain ⟨η, hcov, -⟩ := e ⟨merge ⊥ (Quotient.mk ⊥ a) (Quotient.mk ⊥ b),
      merge_covers ⊥ hAB, observed_merge_of_rel hAB hrel⟩
    have hblocks := hcov.2
    have hpos := blocks_pos η
    rw [blocks_graphKer] at hblocks
    omega

/-! ### How much state a compression hides -/

/-- The number of haplotypes `|C|` in the report component of `x`. -/
def componentSize (s : Fin n → Fin n) (ξ : ER n) (x : Fin n) : ℕ :=
  (univ.filter fun z ↦ (observed s ξ).r z x).card

/-- The number of graph states `w_C` occupied by the report component of `x`. -/
def componentWidth (s : Fin n → Fin n) (ξ : ER n) (x : Fin n) : ℕ :=
  ((univ.filter fun z ↦ (observed s ξ).r z x).image s).card

/-- From the singletons, the component of `x` is the fiber of `x`. -/
theorem componentSize_bot (s : Fin n → Fin n) (x : Fin n) :
    componentSize s ⊥ x = Linkage.fiberCard s x := by
  rw [componentSize, Linkage.fiberCard]
  congr 1
  ext z
  rw [mem_filter, Linkage.mem_fiber, observed_bot, graphKer_rel_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨mem_univ z, h⟩⟩

/-- From the singletons, the component of `x` occupies one graph state. -/
theorem componentWidth_bot (s : Fin n → Fin n) (x : Fin n) : componentWidth s ⊥ x = 1 := by
  rw [componentWidth, card_eq_one]
  refine ⟨s x, ?_⟩
  ext t
  rw [mem_image, mem_singleton]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_filter, observed_bot, graphKer_rel_iff] at hz
    exact hz.2
  · rintro rfl
    exact ⟨x, mem_filter.mpr ⟨mem_univ x, (observed s ⊥).iseqv.refl x⟩, rfl⟩

/-- In a joined component the haplotypes are those of the two components joined. -/
theorem filter_merge_rel_of_rel (Y : ER n) {u v z : Fin n} (huv : ¬ Y.r u v)
    (hz : Y.r u z ∨ Y.r v z) :
    (univ.filter fun w ↦ (merge Y (Quotient.mk Y u) (Quotient.mk Y v)).r w z) =
      (univ.filter fun w ↦ Y.r w u) ∪ univ.filter fun w ↦ Y.r w v := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_union, merge_rel_iff_of_not_rel Y huv]
  rcases hz with hz | hz
  · constructor
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl (Y.iseqv.trans h (Y.iseqv.symm hz))
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Y.iseqv.trans h hz)
      · exact Or.inr (Or.inr ⟨h, Y.iseqv.symm hz⟩)
  · constructor
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inr (Y.iseqv.trans h (Y.iseqv.symm hz))
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inr (Or.inl ⟨h, Y.iseqv.symm hz⟩)
      · exact Or.inl (Y.iseqv.trans h hz)

/-- A component the merger does not touch keeps its haplotypes. -/
theorem filter_merge_rel_of_not_rel (Y : ER n) {u v z : Fin n} (huv : ¬ Y.r u v)
    (hz : ¬ (Y.r u z ∨ Y.r v z)) :
    (univ.filter fun w ↦ (merge Y (Quotient.mk Y u) (Quotient.mk Y v)).r w z) =
      univ.filter fun w ↦ Y.r w z := by
  ext w
  simp only [mem_filter, mem_univ, true_and, merge_rel_iff_of_not_rel Y huv]
  constructor
  · rintro (h | ⟨-, h⟩ | ⟨-, h⟩)
    · exact h
    · exact absurd (Or.inr (Y.iseqv.symm h)) hz
    · exact absurd (Or.inl (Y.iseqv.symm h)) hz
  · exact fun h ↦ Or.inl h

/-- **The load of a component is bounded by its compression.** In the report component of `x`,
holding `|C|` haplotypes in `w_C` graph states, the number of true ancestral blocks satisfies
`L_C + w_C ≤ |C| + 1`. -/
theorem hiddenLoad_add_componentWidth_le (s : Fin n → Fin n) (ξ : ER n) (x : Fin n) :
    hiddenLoad s ξ (Quotient.mk (observed s ξ) x) + componentWidth s ξ x ≤
      componentSize s ξ x + 1 := by
  have hbound : ∀ k, ∀ ζ : ER n, blocks ζ + k = n →
      ∀ z, (hiddenState s ζ).2 z + componentWidth s ζ z ≤ componentSize s ζ z + 1 := by
    intro k
    induction k with
    | zero =>
      intro ζ hζ z
      have hbot : Delta n = ζ := eq_of_le_of_blocks_eq bot_le (by rw [blocks_bot]; omega)
      subst hbot
      have h1 := hiddenLoad_bot s z
      have h2 := componentWidth_bot s z
      have h3 := componentSize_bot s z
      show hiddenLoad s ⊥ (Quotient.mk (observed s ⊥) z) + componentWidth s ⊥ z ≤
        componentSize s ⊥ z + 1
      omega
    | succ k ih =>
      intro ζ hζ z
      have hne : ζ ≠ Delta n := fun h ↦ by
        rw [h, blocks_bot] at hζ
        omega
      obtain ⟨η, hcov⟩ := exists_covers_of_ne_bot hne
      have hη := ih η (by have := hcov.2; omega)
      obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge η ζ).mp hcov
      obtain ⟨u, rfl⟩ := quotient_mk_surjective η A
      obtain ⟨v, rfl⟩ := quotient_mk_surjective η B
      by_cases huv : (observed s η).r u v
      · have hreport := observed_merge_of_rel hAB huv
        rw [hiddenState_merge_of_rel hAB huv]
        show (if (observed s η).r u z then (hiddenState s η).2 z - 1
            else (hiddenState s η).2 z) +
            componentWidth s (merge η (Quotient.mk η u) (Quotient.mk η v)) z ≤
          componentSize s (merge η (Quotient.mk η u) (Quotient.mk η v)) z + 1
        rw [componentWidth, componentSize, hreport, ← componentWidth, ← componentSize]
        have hz := hη z
        split_ifs <;> omega
      · have hreport := observed_merge_of_not_rel hAB huv
        rw [hiddenState_merge_of_not_rel hAB huv]
        show (if (observed s η).r u z ∨ (observed s η).r v z then
            (hiddenState s η).2 u + (hiddenState s η).2 v - 1 else (hiddenState s η).2 z) +
            componentWidth s (merge η (Quotient.mk η u) (Quotient.mk η v)) z ≤
          componentSize s (merge η (Quotient.mk η u) (Quotient.mk η v)) z + 1
        split_ifs with hz
        · have hdisj : Disjoint (univ.filter fun w ↦ (observed s η).r w u)
              (univ.filter fun w ↦ (observed s η).r w v) := by
            refine disjoint_left.mpr fun w hwu hwv ↦ huv ?_
            exact (observed s η).iseqv.trans ((observed s η).iseqv.symm (mem_filter.mp hwu).2)
              (mem_filter.mp hwv).2
          have himage : Disjoint ((univ.filter fun w ↦ (observed s η).r w u).image s)
              ((univ.filter fun w ↦ (observed s η).r w v).image s) := by
            refine disjoint_left.mpr fun t htu htv ↦ huv ?_
            obtain ⟨w, hw, rfl⟩ := mem_image.mp htu
            obtain ⟨w', hw', hww'⟩ := mem_image.mp htv
            have hrel : (observed s η).r w' w :=
              graphKer_le_observed s η (graphKer_rel_iff.mpr hww')
            exact (observed s η).iseqv.trans ((observed s η).iseqv.symm (mem_filter.mp hw).2)
              ((observed s η).iseqv.trans ((observed s η).iseqv.symm hrel)
                (mem_filter.mp hw').2)
          have hsize : componentSize s (merge η (Quotient.mk η u) (Quotient.mk η v)) z =
              componentSize s η u + componentSize s η v := by
            rw [componentSize, componentSize, componentSize, hreport,
              filter_merge_rel_of_rel _ huv hz, card_union_of_disjoint hdisj]
          have hwidth : componentWidth s (merge η (Quotient.mk η u) (Quotient.mk η v)) z =
              componentWidth s η u + componentWidth s η v := by
            rw [componentWidth, componentWidth, componentWidth, hreport,
              filter_merge_rel_of_rel _ huv hz, image_union, card_union_of_disjoint himage]
          have hu := hη u
          have hv := hη v
          have hpu : 0 < (hiddenState s η).2 u := hiddenLoad_pos s η _
          have hpv : 0 < (hiddenState s η).2 v := hiddenLoad_pos s η _
          rw [hsize, hwidth]
          omega
        · have hsize : componentSize s (merge η (Quotient.mk η u) (Quotient.mk η v)) z =
              componentSize s η z := by
            rw [componentSize, componentSize, hreport, filter_merge_rel_of_not_rel _ huv hz]
          have hwidth : componentWidth s (merge η (Quotient.mk η u) (Quotient.mk η v)) z =
              componentWidth s η z := by
            rw [componentWidth, componentWidth, hreport, filter_merge_rel_of_not_rel _ huv hz]
          rw [hsize, hwidth]
          exact hη z
  have hle : blocks ξ ≤ n := by
    have h : Nat.card (Quotient ξ) ≤ Nat.card (Fin n) :=
      Nat.card_le_card_of_surjective (Quotient.mk ξ) (quotient_mk_surjective ξ)
    rw [Nat.card_fin] at h
    exact h
  exact hbound (n - blocks ξ) ξ (by omega) x

end

end Descent.Pangenome.GraphCoalescent.MarkovCompressions
