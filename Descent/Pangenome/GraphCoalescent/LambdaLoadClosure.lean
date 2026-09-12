/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The Λ-coalescent load closure

Section 10 of the hidden-lineage clock extends Theorem A from Kingman's coalescent to
Λ-coalescents. With `K` true ancestral blocks, every particular set of `b ≥ 2` blocks merges into
one at rate `λ_{K,b}`. A merger touches each component `C` of the report through `h_C` of its
`L_C` blocks; the components with `h_C > 0` join, and the joined component carries
`Σ_{h_C > 0} L_C - b + 1` blocks. The note's claim is that the reports with their loads are again a
strong lumping, the merger of profile `(h_C)` running at rate `λ_{K,b} ∏_C C(L_C, h_C)`. This
module proves the counting behind that rate and Rosenblatt's criterion.

`subsetProfile componentOf subset` is the profile of a merging set, the number of its blocks in
each component; the loads are `MultiInterfaceClosure.cellLoad`, the profile of every block
(`subsetProfile_univ`). `card_subsets_with_profile` counts the sets of true blocks with a
prescribed profile as `∏_C C(L_C, h_C)`: choosing such a set is choosing `h_C` blocks inside each
component. `sum_prod_choose_eq_choose` sums that count over the profiles of one size `b` and
recovers `C(K, b)`, so the profiles account for every `b`-subset exactly once.

`lumpedLambdaRate load rate outcome target` is the rate the lumped chain offers into `target`: over
every profile of a merger of at least two blocks with outcome `target`, the rate `λ_{K,b}` of one
merging set times the number of merging sets with that profile. `filter_mergers_with_profile`
sorts the merging sets by profile, `sum_mergerRates_eq_lumpedLambdaRate` shows that the total rate
of the labeled Λ-coalescent into `target` is exactly `lumpedLambdaRate` of the loads, and
`sum_mergerRates_eq_of_cellLoad_eq` concludes Rosenblatt's criterion: two labeled configurations
with the same loads offer the same total rate into every lumped target.
`card_touchedBlocks_after_merger` identifies the joined load: after the merger, the blocks inside
the touched components number `joinedLoad`, the sum of their loads less `b` plus one.

Not formalized here, as in `MultiInterfaceClosure`: that the lumped outcome of a merger depends
only on its profile, which is the hypothesis on the outcome map. Minimality of the lumping and its
pole set are not claimed by the note and are not proved.

## Empirical status

None. The bodies here are combinatorics: blocks, components and merger rates are supplied finite
data, and every statement is a count of subsets or a sum of rates over them, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.LambdaLoadClosure

open Descent.Pangenome.GraphCoalescent.MultiInterfaceClosure

noncomputable section

/-! ### Merging sets counted by profile -/

/-- The component profile of a set of merging blocks: how many of them lie in each component. -/
def subsetProfile {Block Component : Type*} [DecidableEq Component]
    (componentOf : Block → Component) (subset : Finset Block) (component : Component) : ℕ :=
  (subset.filter fun block ↦ componentOf block = component).card

/-- The profile of the set of every true block is the vector of loads. -/
theorem subsetProfile_univ {Block Component : Type*} [Fintype Block] [DecidableEq Block]
    [Fintype Component] [DecidableEq Component] (componentOf : Block → Component) :
    subsetProfile componentOf Finset.univ = cellLoad componentOf :=
  rfl

/-- The profile of a merging set adds up to its size. -/
theorem sum_subsetProfile {Block Component : Type*} [Fintype Component] [DecidableEq Component]
    (componentOf : Block → Component) (subset : Finset Block) :
    ∑ component, subsetProfile componentOf subset component = subset.card :=
  (Finset.card_eq_sum_card_fiberwise (f := componentOf) (s := subset) (t := Finset.univ)
    fun _ _ ↦ Finset.mem_univ _).symm

/-- A family of block sets, each inside its own component, is recovered from its union by
filtering by component. -/
theorem filter_biUnion_of_subset_components {Block Component : Type*} [Fintype Block]
    [DecidableEq Block] [Fintype Component] [DecidableEq Component]
    (componentOf : Block → Component) (parts : Component → Finset Block)
    (hparts : ∀ component,
      parts component ⊆ Finset.univ.filter fun block ↦ componentOf block = component)
    (component : Component) :
    ((Finset.univ.biUnion parts).filter fun block ↦ componentOf block = component) =
      parts component := by
  ext block
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨other, hblock⟩, hcomponent⟩
    have hother : componentOf block = other :=
      (Finset.mem_filter.mp (hparts other hblock)).2
    rw [← hcomponent, hother]
    exact hblock
  · intro hblock
    exact ⟨⟨component, hblock⟩, (Finset.mem_filter.mp (hparts component hblock)).2⟩

/-- **Counting the merging sets by profile.** The sets of true blocks with `h_C` blocks in each
component `C` number `∏_C C(L_C, h_C)`: such a set is a choice of `h_C` blocks inside each
component. -/
theorem card_subsets_with_profile {Block Component : Type*} [Fintype Block] [DecidableEq Block]
    [Fintype Component] [DecidableEq Component] (componentOf : Block → Component)
    (profile : Component → ℕ) :
    (Finset.univ.filter fun subset : Finset Block ↦
      subsetProfile componentOf subset = profile).card =
      ∏ component, (cellLoad componentOf component).choose (profile component) := by
  have hbijection : (Finset.univ.filter fun subset : Finset Block ↦
      subsetProfile componentOf subset = profile).card =
      (Fintype.piFinset fun component ↦
        (Finset.univ.filter fun block ↦ componentOf block = component).powersetCard
          (profile component)).card := by
    refine Finset.card_nbij'
      (fun subset component ↦ subset.filter fun block ↦ componentOf block = component)
      (fun parts ↦ Finset.univ.biUnion parts) ?_ ?_ ?_ ?_
    · intro subset hsubset
      rw [Finset.mem_coe, Finset.mem_filter] at hsubset
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro component
      rw [Finset.mem_powersetCard]
      refine ⟨fun block hblock ↦ ?_, congrFun hsubset.2 component⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hblock).2⟩
    · intro parts hparts
      rw [Finset.mem_coe, Fintype.mem_piFinset] at hparts
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      funext component
      show ((Finset.univ.biUnion parts).filter fun block ↦ componentOf block = component).card =
        profile component
      rw [filter_biUnion_of_subset_components componentOf parts
        (fun other ↦ (Finset.mem_powersetCard.mp (hparts other)).1) component]
      exact (Finset.mem_powersetCard.mp (hparts component)).2
    · intro subset _
      ext block
      simp
    · intro parts hparts
      rw [Finset.mem_coe, Fintype.mem_piFinset] at hparts
      funext component
      exact filter_biUnion_of_subset_components componentOf parts
        (fun other ↦ (Finset.mem_powersetCard.mp (hparts other)).1) component
  rw [hbijection, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun component _ ↦ Finset.card_powersetCard _ _

/-- The component profiles bounded by the loads: a finite set containing the profile of every
merging set. -/
def boundedProfiles {Component : Type*} [Fintype Component] [DecidableEq Component]
    (load : Component → ℕ) : Finset (Component → ℕ) :=
  Fintype.piFinset fun component ↦ Finset.range (load component + 1)

/-- Every merging set has a bounded profile. -/
theorem subsetProfile_mem_boundedProfiles {Block Component : Type*} [Fintype Block]
    [DecidableEq Block] [Fintype Component] [DecidableEq Component]
    (componentOf : Block → Component) (subset : Finset Block) :
    subsetProfile componentOf subset ∈ boundedProfiles (cellLoad componentOf) := by
  rw [boundedProfiles, Fintype.mem_piFinset]
  intro component
  rw [Finset.mem_range]
  refine Nat.lt_succ_of_le (Finset.card_le_card fun block hblock ↦ ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hblock).2⟩

/-- **Every merging set of size `b` has exactly one profile.** Summed over the bounded profiles of
size `b`, the counts `∏_C C(L_C, h_C)` add up to `C(K, b)`. -/
theorem sum_prod_choose_eq_choose {Block Component : Type*} [Fintype Block] [DecidableEq Block]
    [Fintype Component] [DecidableEq Component] (componentOf : Block → Component) (size : ℕ) :
    ∑ profile ∈ (boundedProfiles (cellLoad componentOf)).filter
        (fun profile ↦ ∑ component, profile component = size),
      ∏ component, (cellLoad componentOf component).choose (profile component) =
      (Fintype.card Block).choose size := by
  have hmaps : Set.MapsTo (subsetProfile componentOf)
      (Finset.powersetCard size (Finset.univ : Finset Block))
      ((boundedProfiles (cellLoad componentOf)).filter
        fun profile ↦ ∑ component, profile component = size) := by
    intro subset hsubset
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hsubset
    rw [Finset.mem_coe, Finset.mem_filter, sum_subsetProfile, hsubset.2]
    exact ⟨subsetProfile_mem_boundedProfiles componentOf subset, rfl⟩
  rw [← Finset.card_univ, ← Finset.card_powersetCard, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun profile hprofile ↦ ?_
  rw [← card_subsets_with_profile]
  congr 1
  ext subset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
    Finset.subset_univ]
  constructor
  · intro hsubset
    refine ⟨?_, hsubset⟩
    rw [← sum_subsetProfile componentOf subset, hsubset]
    exact (Finset.mem_filter.mp hprofile).2
  · exact fun hsubset ↦ hsubset.2

/-! ### The lumped rate and Rosenblatt's criterion -/

/-- **The lumped Λ-coalescent rate into `target`.** Over every bounded profile of a merger of at
least two blocks whose outcome is `target`, the rate `λ_{K,b}` of one merging set of that size
times the number `∏_C C(L_C, h_C)` of merging sets with that profile, where `K` is the total load
and `b` the size of the profile. It depends on the configuration only through the loads. -/
def lumpedLambdaRate {Component State : Type*} [Fintype Component] [DecidableEq Component]
    [DecidableEq State] (load : Component → ℕ) (rate : ℕ → ℕ → ℝ)
    (outcome : (Component → ℕ) → State) (target : State) : ℝ :=
  ∑ profile ∈ boundedProfiles load,
    if 2 ≤ (∑ component, profile component) ∧ outcome profile = target then
      rate (∑ component, load component) (∑ component, profile component) *
        ∏ component, ((load component).choose (profile component) : ℝ)
    else 0

/-- **The merging sets of one profile.** Among the sets of at least two blocks whose outcome is
`target`, those with profile `(h_C)` are every set with that profile when the profile has size at
least two and outcome `target`, and there are none otherwise. -/
theorem filter_mergers_with_profile {Block Component State : Type*} [Fintype Block]
    [Fintype Component] [DecidableEq Component] [DecidableEq State]
    (componentOf : Block → Component) (outcome : (Component → ℕ) → State) (target : State)
    (profile : Component → ℕ) :
    (Finset.univ.filter fun subset : Finset Block ↦
        2 ≤ subset.card ∧ outcome (subsetProfile componentOf subset) = target).filter
      (fun subset ↦ subsetProfile componentOf subset = profile) =
      if 2 ≤ (∑ component, profile component) ∧ outcome profile = target then
        Finset.univ.filter fun subset : Finset Block ↦ subsetProfile componentOf subset = profile
      else ∅ := by
  rw [Finset.filter_filter]
  split_ifs with hcondition
  · refine Finset.filter_congr fun subset _ ↦ ⟨fun hsubset ↦ hsubset.2, fun hsubset ↦ ?_⟩
    refine ⟨⟨?_, ?_⟩, hsubset⟩
    · rw [← sum_subsetProfile componentOf subset, hsubset]
      exact hcondition.1
    · rw [hsubset]
      exact hcondition.2
  · rw [Finset.filter_eq_empty_iff]
    rintro subset - ⟨hsize, hprofile⟩
    apply hcondition
    rw [← hprofile, sum_subsetProfile]
    exact hsize

/-- **The closure of the Λ-coalescent, the lumped rate.** The total rate at which the labeled
Λ-coalescent moves into `target`, over every set of at least two blocks whose outcome is `target`,
is `lumpedLambdaRate` of the loads. Assumes: the outcome map describes the next lumped state as a
function of the merger's profile, which is the content of section 10. -/
theorem sum_mergerRates_eq_lumpedLambdaRate {Block Component State : Type*} [Fintype Block]
    [DecidableEq Block] [Fintype Component] [DecidableEq Component] [DecidableEq State]
    (componentOf : Block → Component) (rate : ℕ → ℕ → ℝ) (outcome : (Component → ℕ) → State)
    (target : State) :
    ∑ subset ∈ Finset.univ.filter (fun subset : Finset Block ↦
        2 ≤ subset.card ∧ outcome (subsetProfile componentOf subset) = target),
      rate (Fintype.card Block) subset.card =
      lumpedLambdaRate (cellLoad componentOf) rate outcome target := by
  have hcard : Fintype.card Block = ∑ component, cellLoad componentOf component := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := componentOf) (s := Finset.univ)
      (t := Finset.univ) fun _ _ ↦ Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to (g := subsetProfile componentOf)
    (t := boundedProfiles (cellLoad componentOf))
    fun subset _ ↦ subsetProfile_mem_boundedProfiles componentOf subset, lumpedLambdaRate]
  refine Finset.sum_congr rfl fun profile _ ↦ ?_
  rw [filter_mergers_with_profile]
  split_ifs
  · have hconstant : ∀ subset ∈ Finset.univ.filter (fun subset : Finset Block ↦
        subsetProfile componentOf subset = profile),
        rate (Fintype.card Block) subset.card =
          rate (∑ component, cellLoad componentOf component) (∑ component, profile component) := by
      intro subset hsubset
      rw [hcard, ← (Finset.mem_filter.mp hsubset).2, sum_subsetProfile]
    rw [Finset.sum_congr rfl hconstant, Finset.sum_const, nsmul_eq_mul,
      card_subsets_with_profile, Nat.cast_prod]
    ring
  · exact Finset.sum_empty

/-- **Rosenblatt's criterion for the Λ-coalescent.** Two labeled configurations with the same load
in every component offer, for every outcome map that depends only on the profile of a merger, the
same total rate into every lumped target: the reports together with the loads form a strong
lumping. Assumes: the outcome map describes the next lumped state as a function of the profile. -/
theorem sum_mergerRates_eq_of_cellLoad_eq {Block Block' Component State : Type*} [Fintype Block]
    [DecidableEq Block] [Fintype Block'] [DecidableEq Block'] [Fintype Component]
    [DecidableEq Component] [DecidableEq State] (componentOf : Block → Component)
    (componentOf' : Block' → Component) (hload : cellLoad componentOf = cellLoad componentOf')
    (rate : ℕ → ℕ → ℝ) (outcome : (Component → ℕ) → State) (target : State) :
    (∑ subset ∈ Finset.univ.filter (fun subset : Finset Block ↦
        2 ≤ subset.card ∧ outcome (subsetProfile componentOf subset) = target),
      rate (Fintype.card Block) subset.card) =
      ∑ subset ∈ Finset.univ.filter (fun subset : Finset Block' ↦
          2 ≤ subset.card ∧ outcome (subsetProfile componentOf' subset) = target),
        rate (Fintype.card Block') subset.card := by
  rw [sum_mergerRates_eq_lumpedLambdaRate, sum_mergerRates_eq_lumpedLambdaRate, hload]

/-! ### The joined load -/

/-- The load of the component a Λ-merger creates: the loads of the components it touches, less the
merging blocks, plus the one block they form. -/
def joinedLoad {Component : Type*} [Fintype Component] (load profile : Component → ℕ) : ℕ :=
  (∑ component ∈ Finset.univ.filter (fun component ↦ 0 < profile component), load component) -
    (∑ component, profile component) + 1

/-- **The joined load of a Λ-merger.** After a set of blocks merges into one, the blocks inside the
components it touches, the merged one counted once, number the sum of their loads less the merging
blocks plus one. -/
theorem card_touchedBlocks_after_merger {Block Component : Type*} [Fintype Block]
    [DecidableEq Block] [Fintype Component] [DecidableEq Component]
    (componentOf : Block → Component) (subset : Finset Block) :
    ((Finset.univ.filter fun block ↦
        0 < subsetProfile componentOf subset (componentOf block)) \ subset).card + 1 =
      joinedLoad (cellLoad componentOf) (subsetProfile componentOf subset) := by
  have hsubset : subset ⊆ Finset.univ.filter fun block ↦
      0 < subsetProfile componentOf subset (componentOf block) := by
    intro block hblock
    have hmember : block ∈ subset.filter fun other ↦ componentOf other = componentOf block :=
      Finset.mem_filter.mpr ⟨hblock, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pos.mpr ⟨block, hmember⟩⟩
  have hmaps : Set.MapsTo componentOf
      (Finset.univ.filter fun block ↦ 0 < subsetProfile componentOf subset (componentOf block))
      (Finset.univ.filter fun component ↦ 0 < subsetProfile componentOf subset component) := by
    intro block hblock
    rw [Finset.mem_coe, Finset.mem_filter] at hblock
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hblock.2⟩)
  have htouched : (Finset.univ.filter fun block ↦
      0 < subsetProfile componentOf subset (componentOf block)).card =
      ∑ component ∈ Finset.univ.filter (fun component ↦
        0 < subsetProfile componentOf subset component), cellLoad componentOf component := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun component hcomponent ↦ ?_
    rw [Finset.filter_filter, cellLoad]
    congr 1
    refine Finset.filter_congr fun block _ ↦ ⟨fun hblock ↦ hblock.2, fun hblock ↦ ⟨?_, hblock⟩⟩
    rw [hblock]
    exact (Finset.mem_filter.mp hcomponent).2
  rw [Finset.card_sdiff_of_subset hsubset, joinedLoad, htouched, sum_subsetProfile]

end

end Descent.Pangenome.GraphCoalescent.LambdaLoadClosure
