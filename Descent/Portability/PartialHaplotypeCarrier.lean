/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
# Per-locus material grading of partial haplotype carriers

A partial haplotype type is a deme label together with an allele assignment on a nonempty
subset of the loci; a sampling configuration is a multiset of such types.  This module
formalizes the material grading of NOTE1 §4.1: the per-locus load of a configuration, the
retention budget (18), the resulting cardinality bound, the finiteness of the retained state
space, the loose configuration count, and the fact that the four ancestral transitions never
violate the budget.

The load of a configuration at a locus counts the carriers that retain that locus.  Because
every partial type retains at least one locus, the number of carriers is bounded by the total
load, hence by the panel budget `B = Σ_ℓ n_ℓ` of (18).  Finiteness of the retained state space
then follows from finiteness of the carrier type together with that cardinality bound: two
budget-respecting configurations with equal clamped multiplicities are equal.

The loose bound of §4.1 is `card_withinBudget_le_choose`: at most `C(K + B, B)` configurations
respect the budget, where `K = d [∏_ℓ (1 + |A_ℓ|) - 1]` is the number of partial types
(`card_partialType`).  The proof is stars and bars.  Padding a configuration with empty slots
to exactly `B` slots (`padWithinBudget`) is injective, and the multisets of `B` slots over the
`K` types and the empty slot number `C(K + B, B)`.  The bound counts configurations; the
cemetery state of §4.1 is one state more.

Migration replaces the deme label and leaves every load unchanged.  Mutation rewrites one
already retained allele label and leaves every load unchanged.  Recombination splits one
carrier's retained loci along a selector into two carriers and leaves every locus load
unchanged; this is the key claim of §4.1, since recombination does raise the number of
carriers.  A cut at `c` is the selector `ℓ ↦ ℓ < c`, so the selector form is the general one.
Coalescence merges two carriers into one whose retained set is the union, so no load
increases; the cemetery transition, which discards carriers outright, is covered by
monotonicity of the budget under multiset inclusion.

The configuration moment `H_ξ(x)` of (17) is the product over the carriers of the marginal
frequency that a haplotype drawn from the carrier's deme agrees with the carrier on its
retained loci.  This is the product form of (17) by construction, and it lies in the unit
interval whenever each deme carries a `Descent.Portability.FiniteReportLaw` on haplotypes.  A
fully retained carrier has marginal frequency equal to the mass of its own haplotype, which is
the seed evaluation of the sampled-genotype representation (22).

The carrier type is inhabited in-corpus by `singleLocusType`, the lineage retaining exactly
one locus, and by `fullType`, the lineage retaining them all.

Not formalized here: the generator identity (19), that is, the coalescent duality with
recombination that identifies the jump rates `q_{ξη}` on configurations.  It is classical and
NOTE1 §4.2 states it without proof.

## Empirical status

None.  The bodies here are algebra: they count retained loci in a finite multiset and multiply
marginal masses of a supplied probability law, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeCarrier

variable {Deme Locus : Type*} {Allele : Locus → Type*}

/-- A partial haplotype type of NOTE1 §4.1: a deme label together with an allele assignment
defined on a nonempty set of loci.  The retained set is the support of the assignment. -/
structure PartialType (Deme Locus : Type*) (Allele : Locus → Type*) where
  /-- The deme in which this material lineage currently sits. -/
  deme : Deme
  /-- The partial allele assignment; `none` marks a locus carrying no material. -/
  allele : ∀ ℓ, Option (Allele ℓ)
  /-- Every retained lineage carries at least one material unit. -/
  retained : ∃ ℓ, (allele ℓ).isSome = true

namespace PartialType

/-- Two partial types with the same deme and the same allele assignment are equal; the
retention proof is irrelevant. -/
theorem eq_of_fields {τ σ : PartialType Deme Locus Allele} (hdeme : τ.deme = σ.deme)
    (hallele : τ.allele = σ.allele) : τ = σ := by
  obtain ⟨d₁, a₁, h₁⟩ := τ
  obtain ⟨d₂, a₂, h₂⟩ := σ
  have hd : d₁ = d₂ := hdeme
  have ha : a₁ = a₂ := hallele
  subst hd
  subst ha
  rfl

instance instFinite [Fintype Deme] [Fintype Locus] [∀ ℓ, Fintype (Allele ℓ)] :
    Finite (PartialType Deme Locus Allele) := by
  have hinj : Function.Injective
      (fun τ : PartialType Deme Locus Allele ↦ (τ.deme, τ.allele)) := by
    intro τ σ h
    exact eq_of_fields (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact Finite.of_injective _ hinj

end PartialType

/-- The carrier fully retaining a haplotype in a deme: the seed configuration entry of (22).
The locus argument is the explicit witness that loci exist. -/
def fullType (i : Deme) (hap : ∀ ℓ, Allele ℓ) (ℓ₀ : Locus) : PartialType Deme Locus Allele where
  deme := i
  allele := fun ℓ ↦ some (hap ℓ)
  retained := ⟨ℓ₀, by simp⟩

/-- The carrier retaining exactly one locus: the smallest material lineage, and the in-corpus
inhabitant of the carrier type.  A deme, a locus and an allele at that locus are all it
needs. -/
def singleLocusType [DecidableEq Locus] (i : Deme) (ℓ₀ : Locus) (a : Allele ℓ₀) :
    PartialType Deme Locus Allele where
  deme := i
  allele := Function.update (fun ℓ ↦ (none : Option (Allele ℓ))) ℓ₀ (some a)
  retained := ⟨ℓ₀, by simp⟩

/-- The material load of a configuration at a locus: the number of carriers retaining it.
This is the left-hand side of the retention constraint (18). -/
def load (ξ : Multiset (PartialType Deme Locus Allele)) (ℓ : Locus) : ℕ :=
  Multiset.countP (fun τ ↦ (τ.allele ℓ).isSome = true) ξ

/-- Adding one carrier raises the load at a locus by one exactly when that carrier retains
the locus. -/
theorem load_cons (τ : PartialType Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) (ℓ : Locus) :
    load (τ ::ₘ ξ) ℓ = load ξ ℓ + (if (τ.allele ℓ).isSome = true then 1 else 0) := by
  simp only [load, Multiset.countP_cons]

/-- The one-locus carrier loads its own locus once and every other locus not at all. -/
theorem load_singleLocusType [DecidableEq Locus] (i : Deme) (ℓ₀ : Locus) (a : Allele ℓ₀)
    (ℓ : Locus) :
    load (singleLocusType i ℓ₀ a ::ₘ (0 : Multiset (PartialType Deme Locus Allele))) ℓ
      = if ℓ = ℓ₀ then 1 else 0 := by
  rw [load_cons]
  by_cases hℓ : ℓ = ℓ₀
  · subst hℓ
    simp [load, singleLocusType]
  · simp [load, singleLocusType, Function.update_of_ne hℓ, hℓ]

/-- The retention constraint (18): a panel requiring `capacity ℓ` chromosome copies at locus
`ℓ` retains only the configurations whose load never exceeds the capacity. -/
def WithinBudget (capacity : Locus → ℕ) (ξ : Multiset (PartialType Deme Locus Allele)) : Prop :=
  ∀ ℓ, load ξ ℓ ≤ capacity ℓ

/-- The empty configuration respects every budget. -/
theorem withinBudget_zero (capacity : Locus → ℕ) :
    WithinBudget capacity (0 : Multiset (PartialType Deme Locus Allele)) := by
  intro ℓ
  simp [load]

/-- A nontrivial budget-respecting configuration: one fully retained haplotype fits whenever
every locus has at least one chromosome copy. -/
theorem withinBudget_fullType (capacity : Locus → ℕ) (i : Deme) (hap : ∀ ℓ, Allele ℓ)
    (ℓ₀ : Locus) (hcap : ∀ ℓ, 1 ≤ capacity ℓ) :
    WithinBudget capacity
      (fullType i hap ℓ₀ ::ₘ (0 : Multiset (PartialType Deme Locus Allele))) := by
  intro ℓ
  rw [load_cons]
  simpa [load, fullType] using hcap ℓ

/-- The budget is inherited by subconfigurations, so discarding carriers into the cemetery of
NOTE1 §4.2 can never violate it. -/
theorem withinBudget_of_le (capacity : Locus → ℕ)
    {ξ ζ : Multiset (PartialType Deme Locus Allele)} (hle : ξ ≤ ζ)
    (h : WithinBudget capacity ζ) : WithinBudget capacity ξ :=
  fun ℓ ↦ le_trans (Multiset.countP_le_of_le _ hle) (h ℓ)

/-- Every carrier retains at least one locus, so the number of carriers never exceeds the
total load. -/
theorem card_le_sum_load [Fintype Locus] (ξ : Multiset (PartialType Deme Locus Allele)) :
    Multiset.card ξ ≤ ∑ ℓ, load ξ ℓ := by
  refine Multiset.induction_on ξ ?_ ?_
  · simp [load]
  · intro τ rest ih
    have hone : 1 ≤ ∑ ℓ, (if (τ.allele ℓ).isSome = true then 1 else 0) := by
      obtain ⟨ℓ₀, hℓ₀⟩ := τ.retained
      have hmem : (if (τ.allele ℓ₀).isSome = true then 1 else 0) ≤
          ∑ ℓ, (if (τ.allele ℓ).isSome = true then 1 else 0) :=
        Finset.single_le_sum
          (f := fun ℓ ↦ if (τ.allele ℓ).isSome = true then 1 else 0)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ ℓ₀)
      simpa [hℓ₀] using hmem
    have hsum : ∑ ℓ, load (τ ::ₘ rest) ℓ =
        (∑ ℓ, load rest ℓ) + ∑ ℓ, (if (τ.allele ℓ).isSome = true then 1 else 0) := by
      simp [load_cons, Finset.sum_add_distrib]
    rw [Multiset.card_cons, hsum]
    omega

/-- The cardinality bound of NOTE1 §4.1: a budget-respecting configuration has at most
`B = Σ_ℓ n_ℓ` carriers. -/
theorem card_le_capacity_total [Fintype Locus] (capacity : Locus → ℕ)
    (ξ : Multiset (PartialType Deme Locus Allele)) (hξ : WithinBudget capacity ξ) :
    Multiset.card ξ ≤ ∑ ℓ, capacity ℓ :=
  le_trans (card_le_sum_load ξ) (Finset.sum_le_sum fun ℓ _ ↦ hξ ℓ)

/-- **The retained state space of NOTE1 §4.1 is finite.**  Budget-respecting configurations
have at most `B` carriers, the carrier type is finite, and multiplicities clamped at `B`
already determine such a configuration. -/
theorem withinBudget_finite [Fintype Deme] [Fintype Locus] [∀ ℓ, Fintype (Allele ℓ)]
    (capacity : Locus → ℕ) :
    {ξ : Multiset (PartialType Deme Locus Allele) | WithinBudget capacity ξ}.Finite := by
  classical
  set bound : ℕ := ∑ ℓ, capacity ℓ
  refine Set.Finite.of_finite_image
    (f := fun ξ ↦ fun τ ↦ (⟨min (Multiset.count τ ξ) bound, by omega⟩ : Fin (bound + 1)))
    (Set.toFinite _) ?_
  intro ξ hξ ζ hζ heq
  refine Multiset.ext.mpr fun τ ↦ ?_
  have hcξ : Multiset.count τ ξ ≤ bound :=
    le_trans (Multiset.count_le_card τ ξ) (card_le_capacity_total capacity ξ hξ)
  have hcζ : Multiset.count τ ζ ≤ bound :=
    le_trans (Multiset.count_le_card τ ζ) (card_le_capacity_total capacity ζ hζ)
  have hval : min (Multiset.count τ ξ) bound = min (Multiset.count τ ζ) bound :=
    congrArg Fin.val (congrFun heq τ)
  omega

section Counting

/-- A partial type is exactly a deme label together with an allele assignment that retains at
least one locus. -/
def partialTypeEquiv :
    PartialType Deme Locus Allele ≃
      Deme × {allele : ∀ ℓ, Option (Allele ℓ) // ∃ ℓ, (allele ℓ).isSome = true} where
  toFun τ := (τ.deme, ⟨τ.allele, τ.retained⟩)
  invFun pair := ⟨pair.1, pair.2.1, pair.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An allele assignment retains some locus exactly when it is not the empty assignment. -/
theorem retains_iff_ne_empty (allele : ∀ ℓ, Option (Allele ℓ)) :
    (∃ ℓ, (allele ℓ).isSome = true) ↔ allele ≠ fun _ ↦ none := by
  constructor
  · rintro ⟨ℓ, hℓ⟩ hempty
    simp [hempty] at hℓ
  · intro hne
    by_contra hnone
    apply hne
    funext ℓ
    cases hℓ : allele ℓ with
    | none => rfl
    | some a => exact (hnone ⟨ℓ, by simp [hℓ]⟩).elim

/-- **The retained-assignment count.**  The allele assignments retaining at least one locus
number `∏_ℓ (1 + |A_ℓ|) - 1`: every locus carries an allele or no material, and only the
empty assignment is excluded. -/
theorem card_retainingAssignment [Fintype Locus] [∀ ℓ, Fintype (Allele ℓ)] :
    Nat.card {allele : ∀ ℓ, Option (Allele ℓ) // ∃ ℓ, (allele ℓ).isSome = true} =
      ∏ ℓ, (1 + Fintype.card (Allele ℓ)) - 1 := by
  classical
  have hoption :
      Nat.card {allele : ∀ ℓ, Option (Allele ℓ) // ∃ ℓ, (allele ℓ).isSome = true} + 1 =
        ∏ ℓ, (1 + Fintype.card (Allele ℓ)) := by
    have hequiv : Option {allele : ∀ ℓ, Option (Allele ℓ) // ∃ ℓ, (allele ℓ).isSome = true} ≃
        ∀ ℓ, Option (Allele ℓ) :=
      (Equiv.subtypeEquivRight (retains_iff_ne_empty (Allele := Allele))).optionCongr.trans
        (Equiv.optionSubtypeNe (fun _ ↦ none : ∀ ℓ, Option (Allele ℓ)))
    rw [← Finite.card_option, Nat.card_congr hequiv, Nat.card_pi]
    exact Finset.prod_congr rfl fun ℓ _ ↦ by
      rw [Finite.card_option, Nat.card_eq_fintype_card, add_comm]
  omega

/-- **The carrier-type count of NOTE1 §4.1.**  There are `K = d [∏_ℓ (1 + |A_ℓ|) - 1]`
partial haplotype types: a deme label together with a nonempty allele assignment. -/
theorem card_partialType [Fintype Deme] [Fintype Locus] [∀ ℓ, Fintype (Allele ℓ)] :
    Nat.card (PartialType Deme Locus Allele) =
      Fintype.card Deme * (∏ ℓ, (1 + Fintype.card (Allele ℓ)) - 1) := by
  rw [Nat.card_congr (partialTypeEquiv (Deme := Deme) (Allele := Allele)), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Deme), card_retainingAssignment]

/-- Padding a configuration with empty slots up to `bound` slots: the stars-and-bars encoding
behind the loose configuration count. -/
def padConfiguration {Carrier : Type*} (bound : ℕ) (ξ : Multiset Carrier) :
    Multiset (Option Carrier) :=
  ξ.map some + Multiset.replicate (bound - Multiset.card ξ) none

/-- A configuration of at most `bound` carriers pads to exactly `bound` slots. -/
theorem card_padConfiguration {Carrier : Type*} (bound : ℕ) (ξ : Multiset Carrier)
    (hle : Multiset.card ξ ≤ bound) : Multiset.card (padConfiguration bound ξ) = bound := by
  simp only [padConfiguration, Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
  omega

/-- Padding keeps the multiplicity of every carrier, so the padded slots determine the
configuration. -/
theorem count_some_padConfiguration {Carrier : Type*} [DecidableEq Carrier] (bound : ℕ)
    (ξ : Multiset Carrier) (τ : Carrier) :
    Multiset.count (some τ) (padConfiguration bound ξ) = Multiset.count τ ξ := by
  rw [padConfiguration, Multiset.count_add,
    Multiset.count_map_eq_count' _ _ (Option.some_injective Carrier), Multiset.count_replicate]
  simp

/-- The stars-and-bars encoding of a budget-respecting configuration: its carriers, padded
with empty slots to exactly `B = Σ_ℓ n_ℓ` slots. -/
def padWithinBudget [Fintype Locus] (capacity : Locus → ℕ)
    (ξ : {ξ : Multiset (PartialType Deme Locus Allele) // WithinBudget capacity ξ}) :
    Sym (Option (PartialType Deme Locus Allele)) (∑ ℓ, capacity ℓ) :=
  Sym.mk (padConfiguration (∑ ℓ, capacity ℓ) ξ.1)
    (card_padConfiguration _ ξ.1 (card_le_capacity_total capacity ξ.1 ξ.2))

/-- Distinct budget-respecting configurations pad to distinct slot multisets. -/
theorem padWithinBudget_injective [Fintype Locus] (capacity : Locus → ℕ) :
    Function.Injective (padWithinBudget (Deme := Deme) (Allele := Allele) capacity) := by
  classical
  intro ξ ζ hpad
  have hslots : padConfiguration (∑ ℓ, capacity ℓ) ξ.1 =
      padConfiguration (∑ ℓ, capacity ℓ) ζ.1 := by
    have hval := congrArg Subtype.val hpad
    exact hval
  refine Subtype.ext (Multiset.ext.mpr fun τ ↦ ?_)
  rw [← count_some_padConfiguration (∑ ℓ, capacity ℓ) ξ.1 τ,
    ← count_some_padConfiguration (∑ ℓ, capacity ℓ) ζ.1 τ, hslots]

/-- **The loose configuration bound of NOTE1 §4.1, over the carrier-type count.**  At most
`C(K + B, B)` configurations respect the budget, where `K` is the number of partial types and
`B = Σ_ℓ n_ℓ`: padding embeds them into the multisets of `B` slots over the `K` types and the
empty slot, of which there are `C(K + 1 + B - 1, B)`. -/
theorem card_withinBudget_le_choose_card [Fintype Deme] [Fintype Locus]
    [∀ ℓ, Fintype (Allele ℓ)] (capacity : Locus → ℕ) :
    Nat.card {ξ : Multiset (PartialType Deme Locus Allele) // WithinBudget capacity ξ} ≤
      (Nat.card (PartialType Deme Locus Allele) + ∑ ℓ, capacity ℓ).choose (∑ ℓ, capacity ℓ) := by
  classical
  have hfintype : Fintype (PartialType Deme Locus Allele) := Fintype.ofFinite _
  refine (Nat.card_le_card_of_injective _
    (padWithinBudget_injective (Deme := Deme) (Allele := Allele) capacity)).trans_eq ?_
  rw [Nat.card_eq_fintype_card
      (α := Sym (Option (PartialType Deme Locus Allele)) (∑ ℓ, capacity ℓ)),
    Sym.card_sym_eq_choose, Fintype.card_option,
    Nat.card_eq_fintype_card (α := PartialType Deme Locus Allele)]
  congr 1
  omega

/-- **The loose configuration bound of NOTE1 §4.1.**  With `K = d [∏_ℓ (1 + |A_ℓ|) - 1]` and
`B = Σ_ℓ n_ℓ`, at most `C(K + B, B)` configurations respect the retention budget (18).  The
cemetery state of §4.1 is one state more. -/
theorem card_withinBudget_le_choose [Fintype Deme] [Fintype Locus] [∀ ℓ, Fintype (Allele ℓ)]
    (capacity : Locus → ℕ) :
    Nat.card {ξ : Multiset (PartialType Deme Locus Allele) // WithinBudget capacity ξ} ≤
      (Fintype.card Deme * (∏ ℓ, (1 + Fintype.card (Allele ℓ)) - 1) + ∑ ℓ, capacity ℓ).choose
        (∑ ℓ, capacity ℓ) := by
  have hbound := card_withinBudget_le_choose_card (Deme := Deme) (Allele := Allele) capacity
  rwa [card_partialType] at hbound

end Counting

section Transitions

/-- Migration of NOTE1 §4.2: a carrier moves to another deme, keeping all of its material. -/
def migrate (τ : PartialType Deme Locus Allele) (target : Deme) :
    PartialType Deme Locus Allele where
  deme := target
  allele := τ.allele
  retained := τ.retained

/-- Migration changes no locus load. -/
theorem load_migrate (τ : PartialType Deme Locus Allele) (target : Deme)
    (rest : Multiset (PartialType Deme Locus Allele)) (ℓ : Locus) :
    load (migrate τ target ::ₘ rest) ℓ = load (τ ::ₘ rest) ℓ := by
  simp [load_cons, migrate]

/-- Migration preserves the retention budget. -/
theorem withinBudget_migrate (capacity : Locus → ℕ) (τ : PartialType Deme Locus Allele)
    (target : Deme) (rest : Multiset (PartialType Deme Locus Allele))
    (h : WithinBudget capacity (τ ::ₘ rest)) :
    WithinBudget capacity (migrate τ target ::ₘ rest) := by
  intro ℓ
  rw [load_migrate]
  exact h ℓ

/-- Mutation of NOTE1 §4.2: one retained allele label is replaced. -/
def mutate [DecidableEq Locus] (τ : PartialType Deme Locus Allele) (ℓ₀ : Locus)
    (a : Allele ℓ₀) : PartialType Deme Locus Allele where
  deme := τ.deme
  allele := Function.update τ.allele ℓ₀ (some a)
  retained := ⟨ℓ₀, by simp⟩

/-- Relabelling an allele at an already retained locus changes no locus load. -/
theorem load_mutate [DecidableEq Locus] (τ : PartialType Deme Locus Allele) (ℓ₀ : Locus)
    (a : Allele ℓ₀) (hret : (τ.allele ℓ₀).isSome = true)
    (rest : Multiset (PartialType Deme Locus Allele)) (ℓ : Locus) :
    load (mutate τ ℓ₀ a ::ₘ rest) ℓ = load (τ ::ₘ rest) ℓ := by
  simp only [load_cons, mutate]
  by_cases hℓ : ℓ = ℓ₀
  · subst hℓ
    simp [hret]
  · simp [Function.update_of_ne hℓ]

/-- Mutation at a retained locus preserves the retention budget. -/
theorem withinBudget_mutate [DecidableEq Locus] (capacity : Locus → ℕ)
    (τ : PartialType Deme Locus Allele) (ℓ₀ : Locus) (a : Allele ℓ₀)
    (hret : (τ.allele ℓ₀).isSome = true)
    (rest : Multiset (PartialType Deme Locus Allele))
    (h : WithinBudget capacity (τ ::ₘ rest)) :
    WithinBudget capacity (mutate τ ℓ₀ a ::ₘ rest) := by
  intro ℓ
  rw [load_mutate τ ℓ₀ a hret]
  exact h ℓ

/-- The selected half of a recombination split: the carrier keeps exactly the loci chosen by
the selector.  A cut at `c` is the selector `ℓ ↦ ℓ < c`. -/
def splitSelected (τ : PartialType Deme Locus Allele) (selector : Locus → Bool)
    (hne : ∃ ℓ, selector ℓ = true ∧ (τ.allele ℓ).isSome = true) :
    PartialType Deme Locus Allele where
  deme := τ.deme
  allele := fun ℓ ↦ if selector ℓ = true then τ.allele ℓ else none
  retained := by
    obtain ⟨ℓ, hs, hr⟩ := hne
    exact ⟨ℓ, by simp [hs, hr]⟩

/-- The complementary half of a recombination split. -/
def splitRejected (τ : PartialType Deme Locus Allele) (selector : Locus → Bool)
    (hne : ∃ ℓ, selector ℓ = false ∧ (τ.allele ℓ).isSome = true) :
    PartialType Deme Locus Allele where
  deme := τ.deme
  allele := fun ℓ ↦ if selector ℓ = true then none else τ.allele ℓ
  retained := by
    obtain ⟨ℓ, hs, hr⟩ := hne
    exact ⟨ℓ, by simp [hs, hr]⟩

/-- **Recombination changes no locus load.**  This is the key claim of NOTE1 §4.1: a split
raises the number of carriers, but every locus is retained by exactly one of the two halves. -/
theorem load_split (τ : PartialType Deme Locus Allele) (selector : Locus → Bool)
    (hsel : ∃ ℓ, selector ℓ = true ∧ (τ.allele ℓ).isSome = true)
    (hrej : ∃ ℓ, selector ℓ = false ∧ (τ.allele ℓ).isSome = true)
    (rest : Multiset (PartialType Deme Locus Allele)) (ℓ : Locus) :
    load (splitSelected τ selector hsel ::ₘ splitRejected τ selector hrej ::ₘ rest) ℓ =
      load (τ ::ₘ rest) ℓ := by
  simp only [load_cons, splitSelected, splitRejected]
  by_cases hs : selector ℓ = true <;> simp [hs]

/-- Recombination preserves the retention budget. -/
theorem withinBudget_split (capacity : Locus → ℕ) (τ : PartialType Deme Locus Allele)
    (selector : Locus → Bool)
    (hsel : ∃ ℓ, selector ℓ = true ∧ (τ.allele ℓ).isSome = true)
    (hrej : ∃ ℓ, selector ℓ = false ∧ (τ.allele ℓ).isSome = true)
    (rest : Multiset (PartialType Deme Locus Allele))
    (h : WithinBudget capacity (τ ::ₘ rest)) :
    WithinBudget capacity
      (splitSelected τ selector hsel ::ₘ splitRejected τ selector hrej ::ₘ rest) := by
  intro ℓ
  rw [load_split τ selector hsel hrej]
  exact h ℓ

/-- Compatibility of two partial assignments: wherever both retain a locus, they agree. -/
def Compatible (τ σ : PartialType Deme Locus Allele) : Prop :=
  ∀ ℓ, (τ.allele ℓ).isSome = true → (σ.allele ℓ).isSome = true → τ.allele ℓ = σ.allele ℓ

/-- Every carrier is compatible with itself. -/
theorem compatible_self (τ : PartialType Deme Locus Allele) : Compatible τ τ :=
  fun _ _ _ ↦ rfl

/-- Disjoint partial lineages are compatible, so they may coalesce; NOTE1 §4.2. -/
theorem compatible_of_disjoint (τ σ : PartialType Deme Locus Allele)
    (hdisj : ∀ ℓ, (τ.allele ℓ).isSome = true → (σ.allele ℓ).isSome = false) :
    Compatible τ σ := by
  intro ℓ hτ hσ
  rw [hdisj ℓ hτ] at hσ
  simp at hσ

/-- Coalescence of NOTE1 §4.2: two carriers in one deme merge into a carrier whose retained
set is the union of theirs. -/
def coalesce (τ σ : PartialType Deme Locus Allele) : PartialType Deme Locus Allele where
  deme := τ.deme
  allele := fun ℓ ↦ (τ.allele ℓ).elim (σ.allele ℓ) some
  retained := by
    obtain ⟨ℓ, h⟩ := τ.retained
    refine ⟨ℓ, ?_⟩
    cases hτ : τ.allele ℓ with
    | none =>
      rw [hτ] at h
      simp at h
    | some a => simp

/-- On a compatible pair the merged assignment agrees with the second carrier wherever the
second carrier retains material, so no allele label is silently overwritten. -/
theorem coalesce_allele_eq_of_compatible (τ σ : PartialType Deme Locus Allele)
    (hcompat : Compatible τ σ) (ℓ : Locus) (hσ : (σ.allele ℓ).isSome = true) :
    (coalesce τ σ).allele ℓ = σ.allele ℓ := by
  cases hτ : τ.allele ℓ with
  | none => simp [coalesce, hτ]
  | some a =>
    have hsome : (τ.allele ℓ).isSome = true := by simp [hτ]
    have hagree := hcompat ℓ hsome hσ
    simp only [coalesce, hτ, Option.elim]
    rw [← hτ, hagree]

/-- **Coalescence never raises a locus load.**  The merged carrier retains a locus exactly
when at least one of the two carriers did. -/
theorem load_coalesce_le (τ σ : PartialType Deme Locus Allele)
    (rest : Multiset (PartialType Deme Locus Allele)) (ℓ : Locus) :
    load (coalesce τ σ ::ₘ rest) ℓ ≤ load (τ ::ₘ σ ::ₘ rest) ℓ := by
  simp only [load_cons, coalesce]
  have key : (if ((τ.allele ℓ).elim (σ.allele ℓ) some).isSome = true then 1 else 0) ≤
      (if (σ.allele ℓ).isSome = true then 1 else 0) +
        (if (τ.allele ℓ).isSome = true then 1 else 0) := by
    cases hτ : τ.allele ℓ with
    | none => simp
    | some a => simp
  omega

/-- Coalescence preserves the retention budget. -/
theorem withinBudget_coalesce (capacity : Locus → ℕ) (τ σ : PartialType Deme Locus Allele)
    (rest : Multiset (PartialType Deme Locus Allele))
    (h : WithinBudget capacity (τ ::ₘ σ ::ₘ rest)) :
    WithinBudget capacity (coalesce τ σ ::ₘ rest) :=
  fun ℓ ↦ le_trans (load_coalesce_le τ σ rest ℓ) (h ℓ)

end Transitions

section Moments

/-- A haplotype agrees with a partial type when it carries the retained allele at every
retained locus. -/
def Agrees (τ : PartialType Deme Locus Allele) (hap : ∀ ℓ, Allele ℓ) : Prop :=
  ∀ ℓ, τ.allele ℓ = none ∨ τ.allele ℓ = some (hap ℓ)

instance decidableAgrees [Fintype Locus] [∀ ℓ, DecidableEq (Allele ℓ)]
    (τ : PartialType Deme Locus Allele) (hap : ∀ ℓ, Allele ℓ) :
    Decidable (Agrees τ hap) := by
  unfold Agrees
  infer_instance

/-- Every haplotype agrees with the fully retained carrier built from it. -/
theorem agrees_fullType (i : Deme) (hap : ∀ ℓ, Allele ℓ) (ℓ₀ : Locus) :
    Agrees (fullType i hap ℓ₀) hap := fun _ ↦ Or.inr rfl

variable [Fintype Locus] [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)]
variable [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- The marginal frequency `x_i[A,a]` of NOTE1 §4.1: the mass of the haplotypes in the
carrier's deme that agree with it on its retained loci. -/
def marginalFrequency (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (τ : PartialType Deme Locus Allele) : ℝ :=
  ∑ hap ∈ Finset.univ.filter (Agrees τ), (law τ.deme).mass hap

/-- The configuration moment `H_ξ(x)` of (17): the product of the marginal frequencies of the
carriers of the configuration. -/
def configurationMoment (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (ξ : Multiset (PartialType Deme Locus Allele)) : ℝ :=
  (ξ.map (marginalFrequency law)).prod

/-- A marginal frequency is a sum of probability masses, hence nonnegative. -/
theorem marginalFrequency_nonneg (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (τ : PartialType Deme Locus Allele) : 0 ≤ marginalFrequency law τ :=
  Finset.sum_nonneg fun hap _ ↦ (law τ.deme).mass_nonneg hap

/-- A marginal frequency never exceeds one. -/
theorem marginalFrequency_le_one (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (τ : PartialType Deme Locus Allele) : marginalFrequency law τ ≤ 1 := by
  have hsub : marginalFrequency law τ ≤ ∑ hap, (law τ.deme).mass hap :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun hap _ _ ↦ (law τ.deme).mass_nonneg hap)
  rwa [(law τ.deme).mass_sum] at hsub

/-- A fully retained carrier has marginal frequency equal to the mass of its haplotype, the
seed evaluation used by the sampled-genotype representation (22). -/
theorem marginalFrequency_fullType (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ)) (i : Deme)
    (hap : ∀ ℓ, Allele ℓ) (ℓ₀ : Locus) :
    marginalFrequency law (fullType i hap ℓ₀) = (law i).mass hap := by
  have hfilter : Finset.univ.filter (Agrees (fullType i hap ℓ₀)) = {hap} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext ℓ
      rcases h ℓ with hc | hc
      · simp [fullType] at hc
      · simp only [fullType, Option.some.injEq] at hc
        exact hc.symm
    · intro h
      subst h
      exact agrees_fullType i g ℓ₀
  unfold marginalFrequency
  rw [hfilter]
  simp [fullType]

/-- The moment of a configuration with one more carrier is (17) read as a recursion. -/
theorem configurationMoment_cons (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (τ : PartialType Deme Locus Allele) (ξ : Multiset (PartialType Deme Locus Allele)) :
    configurationMoment law (τ ::ₘ ξ) =
      marginalFrequency law τ * configurationMoment law ξ := by
  simp [configurationMoment]

/-- Configuration moments multiply over unions of configurations. -/
theorem configurationMoment_add (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (ξ ζ : Multiset (PartialType Deme Locus Allele)) :
    configurationMoment law (ξ + ζ) =
      configurationMoment law ξ * configurationMoment law ζ := by
  simp [configurationMoment, Multiset.prod_add]

/-- Configuration moments are nonnegative. -/
theorem configurationMoment_nonneg (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (ξ : Multiset (PartialType Deme Locus Allele)) : 0 ≤ configurationMoment law ξ := by
  refine Multiset.induction_on ξ ?_ ?_
  · simp [configurationMoment]
  · intro τ rest ih
    rw [configurationMoment_cons]
    exact mul_nonneg (marginalFrequency_nonneg law τ) ih

/-- Configuration moments never exceed one, so (17) evaluates the retained span inside the
unit interval. -/
theorem configurationMoment_le_one (law : Deme → FiniteReportLaw (∀ ℓ, Allele ℓ))
    (ξ : Multiset (PartialType Deme Locus Allele)) : configurationMoment law ξ ≤ 1 := by
  refine Multiset.induction_on ξ ?_ ?_
  · simp [configurationMoment]
  · intro τ rest ih
    rw [configurationMoment_cons]
    have h0 := marginalFrequency_nonneg law τ
    have h1 := marginalFrequency_le_one law τ
    have hn := configurationMoment_nonneg law rest
    nlinarith

end

end Moments

end Descent.Portability.PartialHaplotypeCarrier
