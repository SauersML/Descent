/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualSemigroup

assert_below Descent.Decision Descent.Program

/-!
# The light cone of neutral portability has radius zero

A polygenic score reads genotypes at a set of loci `A`. Its report under NOTE1's neutral model
(drift, migration, recombination and symmetric mutation) is carried by the expected moments of the
allele-labelled partial haplotypes of §4.2, propagated by the dual generator of (20). This module
proves that the report on `A` does not depend on the model outside `A` at all: the light cone of
neutral portability has radius zero.

## No dual transition adds a locus

`LociWithin A ξ` says every carrier of the configuration `ξ` retains material only at loci of `A`.
A migration changes a deme label, a mutation relabels a retained allele, a recombination split
keeps two complementary parts of the retained loci, and a coalescence keeps the union of two
carriers' loci. So every dual transition from a configuration over `A` lands on a configuration
over `A` or on the cemetery (`dualTransitions_lociWithin`). Recombination only shrinks supports,
which is why no escape term appears, in contrast with the compatibility-checked circuit of
`Descent.Pangenome.AncestralLocality`.

## The propagator reads only the block over `A`

The rows of the dual generator at configurations over `A` vanish off them
(`dualGenerator_eq_zero_of_not_lociWithin`). The restriction `localRestriction` to those
configurations therefore intertwines the generator with its block `localGenerator`
(`localRestriction_mul_dualGenerator`), and through `matrixExponential_intertwines` also the
propagators (`localRestriction_mul_matrixExponential`). Two models whose dual generators agree on
the rows over `A` propagate equal initial moments over `A` to equal moments over `A`
(`matrixExponential_mulVec_eq_of_rows_eqOn`, `expectedMomentVector_eq_of_rows_eqOn`).

## Rates that agree on `A` give the same report on `A`

Two rate tables agree on `A` when their coalescence and migration rates are equal, their mutation
rates agree at the loci of `A`, and every pattern of crossovers on `A` has the same total rate. A
selector enters a carrier's split only through its pattern on the carrier's loci
(`splitValue_congr`), so grouping selectors by that pattern (`sum_recombination_mul_splitValue_eq`)
shows that the dual transitions from a configuration over `A` have the same sums against every
table of values (`transitionSum_eq_of_agreeOn`). The dual generators then agree on every row over
`A` (`dualGenerator_eq_of_agreeOn`).

**The theorem** (`expectedMomentVector_eq_of_agreeOn`). Let two expectation families obey the
forward moment equation of NOTE1 (20) under rate tables that agree on `A`, with equal initial
moments on the configurations over `A`. Then at every time `t ≥ 0` their expected moments agree at
every configuration over `A`, the sampled-genotype probabilities of a panel on `A` among them.

Significance. The report of a score on `A` is exactly local. Mutation rates, crossover structure
outside the patterns on `A`, and allele frequencies at loci outside `A` cannot move it, however
close those loci are and however long the history. A genomic window `W ⊇ A` with the crossover
law pushed forward to `W` reproduces the full-genome report exactly, at every radius. Distant loci
can affect portability only through a mechanism that makes the dual read new loci: selection,
compatibility-gated recombination, or a score construction that uses linkage windows.

Scope. The model is NOTE1's neutral model; selection is not covered. The forward moment equation
is a hypothesis on the expectation families, as in
`Descent.Portability.PartialHaplotypeDualSemigroup`. The theorem is stated for one epoch of
constant rates.

## Empirical status

None. The bodies here are finite multiset recursions, sums over crossover selectors and matrix
exponentials of supplied rate tables, so no measurement can bear on them.
-/

namespace Descent.Portability.PortabilityLightCone

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open SubstochasticGeneratorSemigroup Descent.Coalescent Descent.Foundations MvPolynomial Finset

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ### Configurations over `A` -/

/-- **A configuration retains only loci of `A`**: every carrier carries material at loci of `A`
only. -/
def LociWithin (A : Finset Locus) (ξ : Multiset (PartialType Deme Locus Allele)) : Prop :=
  ∀ τ ∈ ξ, ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A

/-- Every configuration retains only loci of the whole genome. -/
theorem lociWithin_univ (ξ : Multiset (PartialType Deme Locus Allele)) : LociWithin univ ξ :=
  fun _ _ ℓ _ ↦ mem_univ ℓ

/-- A sub-configuration of a configuration over `A` is over `A`. -/
theorem LociWithin.of_le {A : Finset Locus} {ξ ζ : Multiset (PartialType Deme Locus Allele)}
    (hle : ξ ≤ ζ) (hζ : LociWithin A ζ) : LociWithin A ξ :=
  fun τ hτ ↦ hζ τ (Multiset.mem_of_le hle hτ)

/-- A sum of configurations is over `A` exactly when both summands are. -/
theorem lociWithin_add {A : Finset Locus} {ξ ζ : Multiset (PartialType Deme Locus Allele)} :
    LociWithin A (ξ + ζ) ↔ LociWithin A ξ ∧ LociWithin A ζ := by
  constructor
  · intro h
    exact ⟨fun τ hτ ↦ h τ (Multiset.mem_add.mpr (Or.inl hτ)),
      fun τ hτ ↦ h τ (Multiset.mem_add.mpr (Or.inr hτ))⟩
  · rintro ⟨h₁, h₂⟩ τ hτ
    rcases Multiset.mem_add.mp hτ with hτ | hτ
    · exact h₁ τ hτ
    · exact h₂ τ hτ

/-- A configuration with one more carrier is over `A` exactly when the carrier and the rest are. -/
theorem lociWithin_cons {A : Finset Locus} {τ : PartialType Deme Locus Allele}
    {ξ : Multiset (PartialType Deme Locus Allele)} :
    LociWithin A (τ ::ₘ ξ) ↔ (∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A) ∧ LociWithin A ξ := by
  simp only [LociWithin, Multiset.forall_mem_cons]

/-- **No dual transition adds a locus.** From a configuration over `A`, every dual transition lands
on a configuration over `A` or on the cemetery. -/
theorem dualTransitions_lociWithin (rates : NeutralRates Deme Locus Allele) {A : Finset Locus}
    {ξ : Multiset (PartialType Deme Locus Allele)} (hξ : LociWithin A ξ) :
    ∀ transition ∈ dualTransitions rates ξ, ∀ η, transition.2 = some η → LociWithin A η := by
  intro transition htransition η hη
  rcases Multiset.mem_add.mp htransition with hmove | hpair
  · obtain ⟨τ, hτ, hτmove⟩ := Multiset.mem_bind.mp hmove
    obtain ⟨move, hmove', rfl⟩ := Multiset.mem_map.mp hτmove
    obtain rfl : move.2 + ξ.erase τ = η := Option.some.inj hη
    have hcarrier : ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A := hξ τ hτ
    refine lociWithin_add.mpr ⟨?_, hξ.of_le (Multiset.erase_le τ ξ)⟩
    rcases Multiset.mem_add.mp hmove' with hmm | hrec
    · rcases Multiset.mem_add.mp hmm with hmig | hmut
      · obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hmig
        intro σ hσ
        simp only [Multiset.mem_singleton] at hσ
        subst hσ
        exact hcarrier
      · obtain ⟨ℓ, _, hℓ⟩ := Multiset.mem_bind.mp hmut
        cases h : τ.allele ℓ with
        | none => simp [h] at hℓ
        | some a =>
          simp only [h, Option.elim] at hℓ
          obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hℓ
          intro σ hσ
          simp only [Multiset.mem_singleton] at hσ
          subst hσ
          intro ℓ' hℓ'
          by_cases hl : ℓ' = ℓ
          · subst hl
            exact hcarrier ℓ' (by simp [h])
          · refine hcarrier ℓ' ?_
            simpa [mutate, Function.update_of_ne hl] using hℓ'
    · obtain ⟨selector, _, hsel⟩ := Multiset.mem_bind.mp hrec
      split_ifs at hsel with hs
      · rw [Multiset.mem_singleton] at hsel
        subst hsel
        intro σ hσ ℓ hℓ
        simp only [Multiset.mem_cons, Multiset.mem_singleton] at hσ
        rcases hσ with rfl | rfl
        · refine hcarrier ℓ ?_
          simp only [splitSelected] at hℓ
          split_ifs at hℓ
          · exact hℓ
          · simp at hℓ
        · refine hcarrier ℓ ?_
          simp only [splitRejected] at hℓ
          split_ifs at hℓ
          · simp at hℓ
          · exact hℓ
      · simp at hsel
  · obtain ⟨τ, hτ, hτpair⟩ := Multiset.mem_bind.mp hpair
    obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.mp hτpair
    have hσ' : σ ∈ ξ := Multiset.mem_of_mem_erase hσ
    by_cases hcompat : Compatible τ σ
    · rw [if_pos hcompat] at hη
      obtain rfl := Option.some.inj hη
      refine lociWithin_cons.mpr
        ⟨fun ℓ hℓ ↦ ?_, hξ.of_le ((Multiset.erase_le σ _).trans (Multiset.erase_le τ ξ))⟩
      cases h : τ.allele ℓ with
      | none =>
        simp only [coalesce, h, Option.elim] at hℓ
        exact hξ σ hσ' ℓ hℓ
      | some a => exact hξ τ hτ ℓ (by simp [h])
    · rw [if_neg hcompat] at hη
      exact absurd hη (by simp)

/-! ### The block of the dual generator over `A` -/

/-- The budget-respecting configurations over `A`. -/
abbrev LocalConfiguration (Deme Locus : Type*) (Allele : Locus → Type*) [Fintype Locus]
    [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)] (capacity : Locus → ℕ) (A : Finset Locus) :=
  {ξ : BudgetConfiguration Deme Locus Allele capacity // LociWithin A ξ.1}

/-- There are finitely many configurations over `A`. -/
noncomputable instance instFintypeLocalConfiguration (capacity : Locus → ℕ) (A : Finset Locus) :
    Fintype (LocalConfiguration Deme Locus Allele capacity A) :=
  Fintype.ofFinite _

/-- **The restriction to the configurations over `A`.** -/
def localRestriction (capacity : Locus → ℕ) (A : Finset Locus) :
    Matrix (LocalConfiguration Deme Locus Allele capacity A)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fun s ξ ↦ if ξ = s.1 then 1 else 0

/-- **The block of the dual generator over `A`.** -/
def localGenerator (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (A : Finset Locus) :
    Matrix (LocalConfiguration Deme Locus Allele capacity A)
      (LocalConfiguration Deme Locus Allele capacity A) ℝ :=
  fun s s' ↦ dualGenerator rates capacity s.1 s'.1

/-- **A row of the dual generator over `A` vanishes off the configurations over `A`.** -/
theorem dualGenerator_eq_zero_of_not_lociWithin (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {A : Finset Locus} {ξ η : BudgetConfiguration Deme Locus Allele capacity}
    (hξ : LociWithin A ξ.1) (hη : ¬LociWithin A η.1) : dualGenerator rates capacity ξ η = 0 := by
  have hne : ξ ≠ η := fun h ↦ hη (h ▸ hξ)
  simp only [dualGenerator, if_neg hne, sub_zero, jumpRate]
  refine Multiset.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨transition, htransition, rfl⟩ := Multiset.mem_map.mp hx
  exact if_neg fun htarget ↦
    hη (dualTransitions_lociWithin rates hξ transition htransition η.1 htarget)

/-- **The restriction intertwines the dual generator with its block over `A`.** -/
theorem localRestriction_mul_dualGenerator (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (A : Finset Locus) :
    localRestriction capacity A * dualGenerator rates capacity =
      localGenerator rates capacity A * localRestriction capacity A := by
  ext s η
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hleft : ∑ ξ, localRestriction capacity A s ξ * dualGenerator rates capacity ξ η =
      dualGenerator rates capacity s.1 η := by
    simp [localRestriction]
  rw [hleft]
  by_cases hη : LociWithin A η.1
  · rw [Finset.sum_eq_single ⟨η, hη⟩]
    · simp [localGenerator, localRestriction]
    · intro s' _ hs'
      simp only [localRestriction]
      rw [if_neg fun heq ↦ hs' (Subtype.ext heq.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dualGenerator_eq_zero_of_not_lociWithin rates capacity s.2 hη]
    exact (Finset.sum_eq_zero fun s' _ ↦ by
      simp only [localRestriction]
      rw [if_neg fun heq ↦ hη (heq ▸ s'.2), mul_zero]).symm

/-- **The restriction intertwines the propagators.** -/
theorem localRestriction_mul_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (A : Finset Locus) (t : ℝ) :
    localRestriction capacity A * matrixExponential (dualGenerator rates capacity) t =
      matrixExponential (localGenerator rates capacity A) t * localRestriction capacity A :=
  matrixExponential_intertwines _ _ _ (localRestriction_mul_dualGenerator rates capacity A) t

/-- **The propagated moments over `A` read only the block over `A`.** If two dual generators agree
on every row over `A` and two initial vectors agree over `A`, the propagated vectors agree at every
configuration over `A`. -/
theorem matrixExponential_mulVec_eq_of_rows_eqOn (rates rates' : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (A : Finset Locus)
    (hrow : ∀ ξ η : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 →
      dualGenerator rates capacity ξ η = dualGenerator rates' capacity ξ η)
    (v v' : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (hv : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 → v ξ = v' ξ)
    (t : ℝ) {ξ : BudgetConfiguration Deme Locus Allele capacity} (hξ : LociWithin A ξ.1) :
    (matrixExponential (dualGenerator rates capacity) t).mulVec v ξ =
      (matrixExponential (dualGenerator rates' capacity) t).mulVec v' ξ := by
  have hgen : localGenerator rates capacity A = localGenerator rates' capacity A := by
    ext s s'
    exact hrow s.1 s'.1 s.2
  have hrestrict : (localRestriction capacity A).mulVec v =
      (localRestriction capacity A).mulVec v' := by
    funext s
    simp [Matrix.mulVec, dotProduct, localRestriction, hv s.1 s.2]
  have hread : ∀ (N : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ) (w : _ → ℝ),
      (localRestriction capacity A).mulVec (N.mulVec w) ⟨ξ, hξ⟩ = N.mulVec w ξ := by
    intro N w
    simp [Matrix.mulVec, dotProduct, localRestriction]
  have hpoint := congrFun (congrArg (fun N ↦ N.mulVec v)
    (localRestriction_mul_matrixExponential rates capacity A t)) ⟨ξ, hξ⟩
  have hpoint' := congrFun (congrArg (fun N ↦ N.mulVec v')
    (localRestriction_mul_matrixExponential rates' capacity A t)) ⟨ξ, hξ⟩
  simp only [← Matrix.mulVec_mulVec] at hpoint hpoint'
  rw [hread, hgen, hrestrict] at hpoint
  rw [hread] at hpoint'
  exact hpoint.trans hpoint'.symm

/-- **The expected moments over `A` read only the block over `A`.** For two expectation families
obeying NOTE1 (20) under rate tables whose dual generators agree on every row over `A`, with equal
initial moments over `A`, the expected moments agree at every configuration over `A` and every
`t ≥ 0`.

Assumes: the forward moment equations `hforward` and `hforward'`, as in
`expectedMomentVector_eq_matrixExponential`. -/
theorem expectedMomentVector_eq_of_rows_eqOn (rates rates' : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (A : Finset Locus)
    (hrow : ∀ ξ η : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 →
      dualGenerator rates capacity ξ η = dualGenerator rates' capacity ξ η)
    (expectationAt expectationAt' :
      ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        (Set.Ici 0) t)
    (hforward' : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt' s ξ)
        (expectationAt' t fun law ↦
          eval (lawPoint law) (neutralGenerator rates' (momentPolynomial ξ.1)))
        (Set.Ici 0) t)
    (hinit : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 →
      expectedMomentVector capacity expectationAt 0 ξ =
        expectedMomentVector capacity expectationAt' 0 ξ)
    (t : ℝ) (ht : 0 ≤ t) {ξ : BudgetConfiguration Deme Locus Allele capacity}
    (hξ : LociWithin A ξ.1) :
    expectedMomentVector capacity expectationAt t ξ =
      expectedMomentVector capacity expectationAt' t ξ := by
  rw [expectedMomentVector_eq_matrixExponential rates capacity expectationAt hforward t ht,
    expectedMomentVector_eq_matrixExponential rates' capacity expectationAt' hforward' t ht]
  exact matrixExponential_mulVec_eq_of_rows_eqOn rates rates' capacity A hrow _ _ hinit t hξ

/-! ### Rates that agree on `A` -/

/-- The pattern a crossover selector draws on the loci of `A`. -/
def selectorOn (A : Finset Locus) (selector : Locus → Bool) : ↥A → Bool :=
  fun ℓ ↦ selector ℓ

/-- The selector that draws a pattern on `A` and `false` elsewhere. -/
def extendSelector (A : Finset Locus) (key : ↥A → Bool) : Locus → Bool :=
  fun ℓ ↦ if h : ℓ ∈ A then key ⟨ℓ, h⟩ else false

/-- The selector drawn from the pattern of a selector agrees with it on `A`. -/
theorem extendSelector_selectorOn (A : Finset Locus) (selector : Locus → Bool) {ℓ : Locus}
    (hℓ : ℓ ∈ A) : extendSelector A (selectorOn A selector) ℓ = selector ℓ := by
  simp only [extendSelector, dif_pos hℓ, selectorOn]

/-- A crossover selector splits a carrier over `A` exactly when a selector with the same pattern on
`A` does. -/
theorem splits_congr {A : Finset Locus} {τ : PartialType Deme Locus Allele}
    (hτ : ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A) {s s' : Locus → Bool}
    (hss' : ∀ ℓ ∈ A, s ℓ = s' ℓ) : Splits τ s ↔ Splits τ s' := by
  unfold Splits
  constructor
  · rintro ⟨⟨ℓ, h₁, h₂⟩, ⟨ℓ', h₁', h₂'⟩⟩
    exact ⟨⟨ℓ, hss' ℓ (hτ ℓ h₂) ▸ h₁, h₂⟩, ⟨ℓ', hss' ℓ' (hτ ℓ' h₂') ▸ h₁', h₂'⟩⟩
  · rintro ⟨⟨ℓ, h₁, h₂⟩, ⟨ℓ', h₁', h₂'⟩⟩
    exact ⟨⟨ℓ, (hss' ℓ (hτ ℓ h₂)).symm ▸ h₁, h₂⟩, ⟨ℓ', (hss' ℓ' (hτ ℓ' h₂')).symm ▸ h₁', h₂'⟩⟩

/-- The value a crossover selector gives a carrier against a table: `F` at the two halves when the
selector splits the carrier, and `0` otherwise. -/
def splitValue (τ : PartialType Deme Locus Allele)
    (F : Multiset (PartialType Deme Locus Allele) → ℝ) (selector : Locus → Bool) : ℝ :=
  if h : Splits τ selector then
    F (splitSelected τ selector h.1 ::ₘ {splitRejected τ selector h.2})
  else 0

/-- **A selector enters a carrier over `A` only through its pattern on `A`.** -/
theorem splitValue_congr {A : Finset Locus} {τ : PartialType Deme Locus Allele}
    (hτ : ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A)
    (F : Multiset (PartialType Deme Locus Allele) → ℝ) {s s' : Locus → Bool}
    (hss' : ∀ ℓ ∈ A, s ℓ = s' ℓ) : splitValue τ F s = splitValue τ F s' := by
  by_cases hs : Splits τ s
  · have hs' : Splits τ s' := (splits_congr hτ hss').mp hs
    have hsel : splitSelected τ s hs.1 = splitSelected τ s' hs'.1 :=
      PartialType.eq_of_fields rfl (funext fun ℓ ↦ by
        by_cases hret : (τ.allele ℓ).isSome = true
        · simp only [splitSelected, hss' ℓ (hτ ℓ hret)]
        · simp only [splitSelected, Option.not_isSome_iff_eq_none.mp hret, ite_self])
    have hrej : splitRejected τ s hs.2 = splitRejected τ s' hs'.2 :=
      PartialType.eq_of_fields rfl (funext fun ℓ ↦ by
        by_cases hret : (τ.allele ℓ).isSome = true
        · simp only [splitRejected, hss' ℓ (hτ ℓ hret)]
        · simp only [splitRejected, Option.not_isSome_iff_eq_none.mp hret, ite_self])
    rw [splitValue, splitValue, dif_pos hs, dif_pos hs', hsel, hrej]
  · have hs' : ¬Splits τ s' := fun h ↦ hs ((splits_congr hτ hss').mpr h)
    rw [splitValue, splitValue, dif_neg hs, dif_neg hs']

/-- The recombination moves of a carrier, read against a table, are a sum over selectors. -/
theorem sum_map_recombinationMoves (rates : NeutralRates Deme Locus Allele)
    (τ : PartialType Deme Locus Allele) (F : Multiset (PartialType Deme Locus Allele) → ℝ) :
    ((recombinationMoves rates τ).map fun move ↦ move.1 * F move.2).sum =
      ∑ selector, rates.recombination selector * splitValue τ F selector := by
  unfold recombinationMoves
  rw [Multiset.map_bind, Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun selector _ ↦ ?_)
  by_cases hs : Splits τ selector
  · rw [dif_pos hs, splitValue, dif_pos hs, Multiset.map_singleton, Multiset.sum_singleton]
  · rw [dif_neg hs, splitValue, dif_neg hs, Multiset.map_zero, Multiset.sum_zero, mul_zero]

/-- **Grouping selectors by their pattern on `A`.** If every pattern of crossovers on `A` has the
same total rate under two rate tables, the recombination sums of a carrier over `A` agree. -/
theorem sum_recombination_mul_splitValue_eq {rates rates' : NeutralRates Deme Locus Allele}
    {A : Finset Locus}
    (hr : ∀ key : ↥A → Bool,
      ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates.recombination s =
        ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates'.recombination s)
    {τ : PartialType Deme Locus Allele} (hτ : ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A)
    (F : Multiset (PartialType Deme Locus Allele) → ℝ) :
    ∑ s, rates.recombination s * splitValue τ F s =
      ∑ s, rates'.recombination s * splitValue τ F s := by
  have hfiber : ∀ Q : NeutralRates Deme Locus Allele,
      ∑ s, Q.recombination s * splitValue τ F s =
        ∑ key : ↥A → Bool, splitValue τ F (extendSelector A key) *
          ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, Q.recombination s := by
    intro Q
    rw [← Finset.sum_fiberwise univ (selectorOn A)]
    refine Finset.sum_congr rfl fun key _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hkey : selectorOn A s = key := (Finset.mem_filter.mp hs).2
    have hcongr : splitValue τ F s = splitValue τ F (extendSelector A key) :=
      splitValue_congr hτ F fun ℓ hℓ ↦ by
        rw [← hkey, extendSelector_selectorOn A s hℓ]
    rw [hcongr, mul_comm]
  rw [hfiber rates, hfiber rates']
  exact Finset.sum_congr rfl fun key _ ↦ by rw [hr key]

/-- Mutation moves of a carrier over `A` read only the mutation rates at the loci of `A`. -/
theorem mutationMoves_eq_of_agreeOn {rates rates' : NeutralRates Deme Locus Allele}
    {A : Finset Locus} (hu : ∀ ℓ ∈ A, rates.mutation ℓ = rates'.mutation ℓ)
    {τ : PartialType Deme Locus Allele} (hτ : ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A) :
    mutationMoves rates τ = mutationMoves rates' τ := by
  unfold mutationMoves
  refine Multiset.bind_congr fun ℓ _ ↦ ?_
  cases h : τ.allele ℓ with
  | none => rfl
  | some a => simp only [Option.elim_some, hu ℓ (hτ ℓ (by simp [h]))]

/-- The dual transitions from `ξ` read against a table of values:
`Σ rate · (value(target) - value(ξ))`, with the cemetery worth `0`. -/
def transitionSum (rates : NeutralRates Deme Locus Allele)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ)
    (ξ : Multiset (PartialType Deme Locus Allele)) : ℝ :=
  ((dualTransitions rates ξ).map fun transition ↦
    transition.1 * (transition.2.elim 0 value - value ξ)).sum

/-- **Rates that agree on `A` have the same transition sums from every configuration over `A`.** -/
theorem transitionSum_eq_of_agreeOn {rates rates' : NeutralRates Deme Locus Allele}
    {A : Finset Locus} (hc : rates.coalescence = rates'.coalescence)
    (hm : rates.migration = rates'.migration)
    (hu : ∀ ℓ ∈ A, rates.mutation ℓ = rates'.mutation ℓ)
    (hr : ∀ key : ↥A → Bool,
      ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates.recombination s =
        ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates'.recombination s)
    {ξ : Multiset (PartialType Deme Locus Allele)} (hξ : LociWithin A ξ)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ) :
    transitionSum rates value ξ = transitionSum rates' value ξ := by
  unfold transitionSum dualTransitions
  simp only [Multiset.map_add, Multiset.sum_add]
  congr 1
  · rw [Multiset.map_bind, Multiset.sum_bind, Multiset.map_bind, Multiset.sum_bind]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun τ hτ ↦ ?_)
    have hcarrier : ∀ ℓ, (τ.allele ℓ).isSome = true → ℓ ∈ A := hξ τ hτ
    simp only [Multiset.map_map, Function.comp_def, Option.elim_some, carrierMoves,
      migrationMoves, Multiset.map_add, Multiset.sum_add, hm,
      mutationMoves_eq_of_agreeOn hu hcarrier]
    congr 1
    exact (sum_map_recombinationMoves rates τ fun m ↦ value (m + ξ.erase τ) - value ξ).trans
      ((sum_recombination_mul_splitValue_eq hr hcarrier _).trans
        (sum_map_recombinationMoves rates' τ fun m ↦ value (m + ξ.erase τ) - value ξ).symm)
  · simp only [hc]

/-- **Rates that agree on `A` give dual generators that agree on every row over `A`.** -/
theorem dualGenerator_eq_of_agreeOn {rates rates' : NeutralRates Deme Locus Allele}
    {A : Finset Locus} (hc : rates.coalescence = rates'.coalescence)
    (hm : rates.migration = rates'.migration)
    (hu : ∀ ℓ ∈ A, rates.mutation ℓ = rates'.mutation ℓ)
    (hr : ∀ key : ↥A → Bool,
      ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates.recombination s =
        ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates'.recombination s)
    (capacity : Locus → ℕ) (ξ η : BudgetConfiguration Deme Locus Allele capacity)
    (hξ : LociWithin A ξ.1) :
    dualGenerator rates capacity ξ η = dualGenerator rates' capacity ξ η := by
  have hindicator : ∀ Q : NeutralRates Deme Locus Allele, dualGenerator Q capacity ξ η =
      transitionSum Q (fun ζ ↦ if ζ = η.1 then (1 : ℝ) else 0) ξ.1 := by
    intro Q
    have h := dualGenerator_mulVec Q capacity (fun ζ ↦ if ζ = η.1 then (1 : ℝ) else 0) ξ
    rw [← transitionSum] at h
    rw [← h]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single η]
    · simp
    · intro ζ _ hζ
      rw [if_neg fun heq ↦ hζ (Subtype.ext heq), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ η) h
  rw [hindicator rates, hindicator rates']
  exact transitionSum_eq_of_agreeOn hc hm hu hr hξ _

/-- **The light cone of neutral portability has radius zero.** Let two rate tables agree on `A`:
equal coalescence and migration rates, equal mutation rates at the loci of `A`, and the same total
rate for every pattern of crossovers on `A`. For two expectation families obeying NOTE1 (20) under
them, with equal initial moments over `A`, the expected moments agree at every configuration over
`A` and every time `t ≥ 0`.

Assumes: the forward moment equations `hforward` and `hforward'`, as in
`expectedMomentVector_eq_matrixExponential`. -/
theorem expectedMomentVector_eq_of_agreeOn {rates rates' : NeutralRates Deme Locus Allele}
    {A : Finset Locus} (hc : rates.coalescence = rates'.coalescence)
    (hm : rates.migration = rates'.migration)
    (hu : ∀ ℓ ∈ A, rates.mutation ℓ = rates'.mutation ℓ)
    (hr : ∀ key : ↥A → Bool,
      ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates.recombination s =
        ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates'.recombination s)
    (capacity : Locus → ℕ)
    (expectationAt expectationAt' :
      ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        (Set.Ici 0) t)
    (hforward' : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt' s ξ)
        (expectationAt' t fun law ↦
          eval (lawPoint law) (neutralGenerator rates' (momentPolynomial ξ.1)))
        (Set.Ici 0) t)
    (hinit : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 →
      expectedMomentVector capacity expectationAt 0 ξ =
        expectedMomentVector capacity expectationAt' 0 ξ)
    (t : ℝ) (ht : 0 ≤ t) {ξ : BudgetConfiguration Deme Locus Allele capacity}
    (hξ : LociWithin A ξ.1) :
    expectedMomentVector capacity expectationAt t ξ =
      expectedMomentVector capacity expectationAt' t ξ :=
  expectedMomentVector_eq_of_rows_eqOn rates rates' capacity A
    (fun _ η hξ' ↦ dualGenerator_eq_of_agreeOn hc hm hu hr capacity _ η hξ') expectationAt
    expectationAt' hforward hforward' hinit t ht hξ

end

end Descent.Portability.PortabilityLightCone
