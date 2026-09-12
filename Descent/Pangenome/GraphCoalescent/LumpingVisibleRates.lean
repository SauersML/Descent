/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Descent.Pangenome.GraphCoalescent.MinimalRefinement

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# A strong lumping of the Kingman chain determines the visible rates

Theorem B of the hidden-lineage clock asks how much load information a predictive Markov
refinement of a pangenome report must keep. Such a refinement is a deterministic statistic `f` of
the labeled coalescent state that determines the report and is a strong lumping for every initial
labeled state. `MinimalRefinement.refines_loads` shows that, with at least three report
components, a statistic determining the report-visible merger rates `ρ_CD = L_C L_D` determines
the loads, and takes the determination of the rates as its hypothesis. This module proves that
hypothesis from strong lumpability in Rosenblatt's form, the form in which
`card_covers_hiddenState_eq` states Theorem A: from two states with the same value of `f`,
equally many covers lead to every value.

`card_filter_comp_eq` is the counting step: two finite sets with equally many elements at every
value of `f` have equally many at every value of `g ∘ f`. With `g` reading the report off `f`,
`card_covers_observed_eq_of_lumping` concludes that two states with the same value of `f` have
equally many covers into every report. `covers_observed_eq_merge_iff` identifies the covers whose
report merges two components reported apart with the visible covers joining them, so
`card_covers_observed_eq_merge` counts them as `L_C L_D`. Hence `visibleRate_eq_of_lumping`: the
statistic determines every visible rate. `load_eq_of_three_visibleRates` is (B1) at one
component, and `hiddenState_eq_of_lumping` combines the two: while the report has at least three
components, two states with the same value of `f` have the same hidden state, so every such
statistic refines the report together with its loads. `hiddenState_determines_report_and_lumps`
records that the hidden state itself meets both hypotheses.

The states of a finite sample are enumerated by a local `Fintype` instance, since the corpus
instance lives in the measure-theoretic kernel module.

Not formalized here: the second survival derivative in the two-component case of (B2), which
needs the law of the killed chain rather than cover counts; its first derivative is the visible
rate, which `visibleRate_eq_of_lumping` covers.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set: every statement is an
identity between cardinalities of sets of coalescent states, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.LumpingVisibleRates

open Coalescent Finset
open scoped Classical

noncomputable section

variable {n : ℕ}

/-- The coalescent states of a finite sample, enumerated for the counts of this module: a state is
determined by its relation. -/
local instance fintypeStates (n : ℕ) : Fintype (ER n) :=
  @Fintype.ofFinite _ (Finite.of_injective (fun σ : ER n ↦ σ.r) fun _ _ h ↦
    Setoid.ext fun a b ↦ Iff.of_eq (congrFun (congrFun h a) b))

/-! ### Counting through a coarser statistic -/

/-- **A coarser statistic inherits equal counts.** Two finite sets with equally many elements at
every value of `f` have equally many elements at every value of `g ∘ f`. -/
theorem card_filter_comp_eq {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (A B : Finset α)
    (f : α → β) (g : β → γ)
    (hcount : ∀ v, (A.filter fun a ↦ f a = v).card = (B.filter fun a ↦ f a = v).card) (z : γ) :
    (A.filter fun a ↦ g (f a) = z).card = (B.filter fun a ↦ g (f a) = z).card := by
  have hsplit : ∀ C : Finset α, (∀ a ∈ C, f a ∈ A.image f ∪ B.image f) →
      (C.filter fun a ↦ g (f a) = z).card =
        ∑ v ∈ (A.image f ∪ B.image f).filter (fun v ↦ g v = z),
          (C.filter fun a ↦ f a = v).card := by
    intro C hC
    have hmaps : ∀ a ∈ C.filter fun a ↦ g (f a) = z,
        f a ∈ (A.image f ∪ B.image f).filter (fun v ↦ g v = z) :=
      fun a ha ↦ mem_filter.mpr ⟨hC a (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩
    rw [card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl fun v hv ↦ congrArg Finset.card ?_
    ext a
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨ha, -⟩, hav⟩
      exact ⟨ha, hav⟩
    · rintro ⟨ha, hav⟩
      refine ⟨⟨ha, ?_⟩, hav⟩
      rw [hav]
      exact (mem_filter.mp hv).2
  rw [hsplit A fun a ha ↦ mem_union_left _ (mem_image_of_mem f ha),
    hsplit B fun a ha ↦ mem_union_right _ (mem_image_of_mem f ha)]
  exact sum_congr rfl fun v _ ↦ hcount v

/-- The covers of `ξ` with a property, counted as a filter of the covers of `ξ`. -/
theorem natCard_covers_eq (ξ : ER n) (P : ER n → Prop) :
    Nat.card {η : ER n // Covers ξ η ∧ P η} = ((univ.filter (Covers ξ)).filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, filter_filter]

/-! ### The visible rate as a count of covers into a report -/

/-- **The covers into a merged report are the visible covers.** For two individuals reported
apart, the covers of `ξ` whose report merges their two components are exactly the visible covers
joining those components. -/
theorem covers_observed_eq_merge_iff (s : Fin n → Fin n) (ξ : ER n) {x y : Fin n}
    (hxy : ¬ (observed s ξ).r x y) (η : ER n) :
    (Covers ξ η ∧ observed s η =
        merge (observed s ξ) (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y)) ↔
      η ∈ visibleCovers s ξ (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y) := by
  have hCD : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  constructor
  · rintro ⟨hcov, hreport⟩
    obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
    obtain ⟨u, rfl⟩ := quotient_mk_surjective ξ A
    obtain ⟨v, rfl⟩ := quotient_mk_surjective ξ B
    by_cases huv : (observed s ξ).r u v
    · exfalso
      rw [observed_merge_of_rel hAB huv] at hreport
      have hcov' := merge_covers (observed s ξ) hCD
      rw [← hreport] at hcov'
      have hblocks := hcov'.2
      omega
    · rw [observed_merge_of_not_rel hAB huv] at hreport
      have hUV : Quotient.mk (observed s ξ) u ≠ Quotient.mk (observed s ξ) v :=
        fun hq ↦ huv (Quotient.exact hq)
      have hpair := (merge_eq_merge_iff (observed s ξ) hUV hCD).mp hreport
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
    have hu' : Quotient.mk (observed s ξ) u = Quotient.mk (observed s ξ) x := Quotient.sound hux
    have hv' : Quotient.mk (observed s ξ) v = Quotient.mk (observed s ξ) y := Quotient.sound hvy
    refine ⟨merge_covers ξ hab, ?_⟩
    rw [observed_merge_of_not_rel hab huv, hu', hv']

/-- **The visible rate as a count of covers into a report.** For two individuals reported apart,
`L_C L_D` covers of `ξ` lead to the report merging their two components `C` and `D`. -/
theorem card_covers_observed_eq_merge (s : Fin n → Fin n) (ξ : ER n) {x y : Fin n}
    (hxy : ¬ (observed s ξ).r x y) :
    Nat.card {η : ER n // Covers ξ η ∧ observed s η =
        merge (observed s ξ) (Quotient.mk (observed s ξ) x) (Quotient.mk (observed s ξ) y)} =
      hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) := by
  rw [← card_visibleCovers s ξ fun hq ↦ hxy (Quotient.exact hq)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun η ↦ covers_observed_eq_merge_iff s ξ hxy η)

/-! ### The Rosenblatt step -/

/-- **A lumping that determines the report counts the covers into every report alike.** If a
statistic determines the report and, from two states with the same value, equally many covers lead
to every value, then from two states with the same value equally many covers lead to every report.
Assumes: the statistic determines the report, and it is a strong lumping in Rosenblatt's form. -/
theorem card_covers_observed_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v,
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') (Z : ER n) :
    Nat.card {η : ER n // Covers ξ η ∧ observed s η = Z} =
      Nat.card {η : ER n // Covers ξ' η ∧ observed s η = Z} := by
  obtain ⟨g, hg⟩ : ∃ g : Stat → ER n, ∀ η, g (f η) = observed s η := by
    refine ⟨fun v ↦ if h : ∃ ζ, f ζ = v then observed s h.choose else ⊥, fun η ↦ ?_⟩
    have h : ∃ ζ, f ζ = f η := ⟨η, rfl⟩
    show (if h : ∃ ζ, f ζ = f η then observed s h.choose else ⊥) = observed s η
    rw [dif_pos h]
    exact hreport _ _ h.choose_spec
  have hcomp : ∀ ζ : ER n, Nat.card {η : ER n // Covers ζ η ∧ observed s η = Z} =
      ((univ.filter (Covers ζ)).filter fun η ↦ g (f η) = Z).card := by
    intro ζ
    rw [natCard_covers_eq ζ fun η ↦ observed s η = Z]
    congr 1
    exact filter_congr fun η _ ↦ by rw [hg]
  rw [hcomp ξ, hcomp ξ']
  refine card_filter_comp_eq _ _ f g (fun v ↦ ?_) Z
  exact (natCard_covers_eq ξ fun η ↦ f η = v).symm.trans
    ((hlumping ξ ξ' hsame v).trans (natCard_covers_eq ξ' fun η ↦ f η = v))

/-- **Theorem B, the Rosenblatt step.** A statistic that determines the report and is a strong
lumping in Rosenblatt's form determines every report-visible merger rate `ρ_CD = L_C L_D`: two
states with the same value have the same product of loads for every two components reported
apart. Assumes: the statistic determines the report, and it is a strong lumping in Rosenblatt's
form, as the hidden state is by `card_covers_hiddenState_eq`. -/
theorem visibleRate_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v,
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) =
      hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) *
        hiddenLoad s ξ' (Quotient.mk (observed s ξ') y) := by
  have hreports : observed s ξ = observed s ξ' := hreport ξ ξ' hsame
  have hxy' : ¬ (observed s ξ').r x y := hreports ▸ hxy
  rw [← card_covers_observed_eq_merge s ξ hxy, ← card_covers_observed_eq_merge s ξ' hxy',
    card_covers_observed_eq_of_lumping s f hreport hlumping hsame, hreports]

/-- **(B1) at one component.** If two load assignments have the same products on the three pairs
among `i`, `j` and `k`, and `j` and `k` carry positive loads, the assignments agree at `i`:
`L_i² = ρ_ij ρ_ik / ρ_jk`, cleared of the denominator. -/
theorem load_eq_of_three_visibleRates {ι : Type*} (load other : ι → ℕ) (i j k : ι)
    (hj : 0 < load j) (hk : 0 < load k) (hij : load i * load j = other i * other j)
    (hik : load i * load k = other i * other k) (hjk : load j * load k = other j * other k) :
    load i = other i := by
  have hsquare : load i ^ 2 * (load j * load k) = other i ^ 2 * (load j * load k) := by
    rw [MinimalRefinement.load_sq_mul_visibleRate load i j k, hij, hik, hjk,
      ← MinimalRefinement.load_sq_mul_visibleRate other i j k]
  exact Nat.pow_left_injective (by norm_num)
    (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hj hk) hsquare)

/-- **Theorem B with three or more components, the Rosenblatt step discharged.** A statistic that
determines the report and is a strong lumping in Rosenblatt's form determines the loads while the
report has at least three components: two states with the same value have the same hidden state,
so the statistic refines the report together with its loads. Assumes: the statistic determines the
report, and it is a strong lumping in Rosenblatt's form. -/
theorem hiddenState_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v,
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') (hcomponents : 3 ≤ blocks (observed s ξ)) :
    hiddenState s ξ = hiddenState s ξ' := by
  have hreports : observed s ξ = observed s ξ' := hreport ξ ξ' hsame
  refine Prod.ext hreports (funext fun x ↦ ?_)
  show hiddenLoad s ξ (Quotient.mk (observed s ξ) x) =
    hiddenLoad s ξ' (Quotient.mk (observed s ξ') x)
  have hcard : 3 ≤ Fintype.card (Quotient (observed s ξ)) := by
    rw [← Nat.card_eq_fintype_card]
    exact hcomponents
  obtain ⟨D, E, hCD, hCE, hDE⟩ :=
    MinimalRefinement.exists_two_others hcard (Quotient.mk (observed s ξ) x)
  obtain ⟨y, rfl⟩ := quotient_mk_surjective (observed s ξ) D
  obtain ⟨z, rfl⟩ := quotient_mk_surjective (observed s ξ) E
  have hxy : ¬ (observed s ξ).r x y := fun h ↦ hCD (Quotient.sound h)
  have hxz : ¬ (observed s ξ).r x z := fun h ↦ hCE (Quotient.sound h)
  have hyz : ¬ (observed s ξ).r y z := fun h ↦ hDE (Quotient.sound h)
  exact load_eq_of_three_visibleRates (fun u ↦ hiddenLoad s ξ (Quotient.mk (observed s ξ) u))
    (fun u ↦ hiddenLoad s ξ' (Quotient.mk (observed s ξ') u)) x y z (hiddenLoad_pos s ξ _)
    (hiddenLoad_pos s ξ _) (visibleRate_eq_of_lumping s f hreport hlumping hsame hxy)
    (visibleRate_eq_of_lumping s f hreport hlumping hsame hxz)
    (visibleRate_eq_of_lumping s f hreport hlumping hsame hyz)

/-- **The hidden state meets both hypotheses.** It determines the report, and by Theorem A it is a
strong lumping in Rosenblatt's form, so `visibleRate_eq_of_lumping` and
`hiddenState_eq_of_lumping` constrain a nonempty family of statistics. -/
theorem hiddenState_determines_report_and_lumps (s : Fin n → Fin n) :
    (∀ ξ ξ' : ER n, hiddenState s ξ = hiddenState s ξ' → observed s ξ = observed s ξ') ∧
      ∀ ξ ξ' : ER n, hiddenState s ξ = hiddenState s ξ' → ∀ v,
        Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = v} =
          Nat.card {η : ER n // Covers ξ' η ∧ hiddenState s η = v} :=
  ⟨fun _ _ h ↦ congrArg Prod.fst h, fun _ _ h v ↦ card_covers_hiddenState_eq s h v⟩

end

end Descent.Pangenome.GraphCoalescent.LumpingVisibleRates
