/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Kernel
import Descent.Pangenome.GraphCoalescent.HiddenLoads
import Descent.Pangenome.GraphCoalescent.MultiplicativeObservation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The report of a compressed pangenome, coupled to a multiplicative coalescent

`Descent.Pangenome.GraphCoalescent.MultiplicativeObservation` proves Theorem F's bound for any
coupled chain whose separation hazard is at most `J/n` and whose deficit drifts by at most
`1/2`.  This file builds the coupled chain of the note's proof and checks those hypotheses.

## The two processes, uniformized

Time is scaled, `u = n² t`, and both processes are uniformized at rate one.

* `kingmanStep`: from a labeled coalescent state `ξ` every cover receives `1/n²` and the chain
  holds with `1 - binom(K, 2)/n²`.  The report is `observed s ξ`.
* `multiplicativeStep`: `Z_p` on the partitions of the individuals, each individual carrying
  mass `1/n`, so a component `C` carries `c(C)/n`.  Two components merge with probability
  `c(C) c(D)/n²`.  Started at `graphKer s` its states are the partitions above the interface,
  which are the partitions of the `w` fiber labels (`Setoid.correspondence`), and the masses are
  the note's `p(C) = ∑_{i ∈ C} c_i/n`.

## The coupling

While the report and `Z_p` agree, a visible merger of `C` and `D` moves both, an invisible
merger moves only the coalescent, and `Z_p` moves alone with the excess `c(C) c(D) - L_C L_D`
over `n²`, at which point the flag records separation.  After separation the two coordinates
run independently.

## Empirical status

None.  Every declaration here is a finite stochastic matrix on pairs of equivalence relations
on a finite set, or a count of covers.  The reading of `s` as a real graph's interface is
stated in `Descent.Pangenome.GraphCoalescent.Observation` and is not asserted of any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset

open scoped Classical

noncomputable section

/-! ### Kingman's coalescent, uniformized in scaled time -/

/-- **Kingman's `n`-coalescent in scaled time `u = n² t`, uniformized at rate one.**  Every
cover of `ξ` receives `1/n²` and the chain holds with the remaining mass.

Empirical status: NOT AN EMPIRICAL CLAIM.  K-C (1.3)'s unit rates, divided by `n²`. -/
def kingmanStep (n : ℕ) (ξ ξ' : ER n) : ℝ :=
  (if Covers ξ ξ' then 1 / (n : ℝ) ^ 2 else 0)
    + if ξ' = ξ then 1 - deathRate (blocks ξ) / (n : ℝ) ^ 2 else 0

/-- Summing a constant over the covers of `ξ` counts them: there are `binom(K, 2)`. -/
theorem sum_ite_covers {n : ℕ} (ξ : ER n) (c : ℝ) :
    ∑ ξ', (if Covers ξ ξ' then c else 0) = deathRate (blocks ξ) * c := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have h1 := card_covers_eq_deathRate ξ
  rw [@Nat.card_eq_fintype_card _ (Subtype.fintype _), Fintype.card_subtype] at h1
  rw [h1]

/-- The uniformized Kingman kernel is stochastic. -/
theorem sum_kingmanStep {n : ℕ} (ξ : ER n) : ∑ ξ', kingmanStep n ξ ξ' = 1 := by
  simp only [kingmanStep, Finset.sum_add_distrib, sum_ite_covers, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/-- The uniformized Kingman kernel is nonnegative once `K ≤ n`. -/
theorem kingmanStep_nonneg {n : ℕ} {ξ : ER n} (hK : blocks ξ ≤ n) (ξ' : ER n) :
    0 ≤ kingmanStep n ξ ξ' := by
  have hhalf := deathRate_div_sq_le_half hK
  unfold kingmanStep
  refine add_nonneg ?_ ?_
  · split_ifs
    · positivity
    · exact le_rfl
  · split_ifs
    · linarith
    · exact le_rfl

/-! ### `Z_p` on the report lattice, uniformized in scaled time -/

/-- **The move named by a set of components**: the merge of its two members when it is a pair,
and no move otherwise.

Empirical status: NOT AN EMPIRICAL CLAIM.  `Coalescent.coverOfPair` without the proof. -/
def mergePair {n : ℕ} (ζ : ER n) (t : Finset (Quotient ζ)) : ER n :=
  if h : t.card = 2 then merge ζ (pairFst h) (pairSnd h) else ζ

/-- **Every individual carries mass `1/n`**, so a component of `n` individuals' partition
carries `c(C)/n`, the note's `p(C)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The empirical distribution of the sample. -/
def unitMass (n : ℕ) : Fin n → ℝ := fun _ ↦ 1 / n

theorem unitMass_nonneg (n : ℕ) (i : Fin n) : 0 ≤ unitMass n i := by
  unfold unitMass
  positivity

theorem sum_unitMass_le_one (n : ℕ) : ∑ i, unitMass n i ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [unitMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [mul_one_div_cancel hnR.ne']

/-- **`Z_p` in scaled time, uniformized at rate one**: two components merge with probability
`p(C) p(D)`, and the chain holds with `1 - κ`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The finite-mass multiplicative coalescent's rates. -/
def multiplicativeStep (n : ℕ) (ζ ζ' : ER n) : ℝ :=
  (∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair ζ t = ζ'),
      ∏ C ∈ t, blockMass (unitMass n) ζ C)
    + if ζ' = ζ then 1 - pairProductSum (blockMass (unitMass n) ζ) else 0

/-- The total merge mass of `Z_p` is at most one half. -/
theorem pairProductSum_blockMass_unitMass_le_half {n : ℕ} (ζ : ER n) :
    pairProductSum (blockMass (unitMass n) ζ) ≤ 1 / 2 := by
  have h := pairProductSum_le_half_sq (blockMass (unitMass n) ζ)
  rw [sum_blockMass] at h
  have hle := sum_unitMass_le_one n
  have hnn : 0 ≤ ∑ i, unitMass n i := Finset.sum_nonneg fun i _ ↦ unitMass_nonneg n i
  nlinarith

/-- The uniformized `Z_p` kernel is stochastic. -/
theorem sum_multiplicativeStep {n : ℕ} (ζ : ER n) : ∑ ζ', multiplicativeStep n ζ ζ' = 1 := by
  simp only [multiplicativeStep, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [Finset.sum_fiberwise ((univ : Finset (Quotient ζ)).powersetCard 2)
    (mergePair ζ) fun t ↦ ∏ C ∈ t, blockMass (unitMass n) ζ C]
  unfold pairProductSum
  ring

/-- The uniformized `Z_p` kernel is nonnegative. -/
theorem multiplicativeStep_nonneg {n : ℕ} (ζ ζ' : ER n) : 0 ≤ multiplicativeStep n ζ ζ' := by
  have hhalf := pairProductSum_blockMass_unitMass_le_half ζ
  have hmass : ∀ C, 0 ≤ blockMass (unitMass n) ζ C :=
    fun C ↦ Finset.sum_nonneg fun i _ ↦ unitMass_nonneg n i
  unfold multiplicativeStep
  refine add_nonneg (Finset.sum_nonneg fun t _ ↦ Finset.prod_nonneg fun C _ ↦ hmass C) ?_
  split_ifs
  · linarith
  · exact le_rfl

/-- The pair `{C, D}` names the merge of `C` and `D`, and no other pair names it. -/
theorem filter_mergePair_merge {n : ℕ} (ζ : ER n) {C D : Quotient ζ} (hCD : C ≠ D) :
    (univ.powersetCard 2).filter (fun t ↦ mergePair ζ t = merge ζ C D) = {{C, D}} := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_powersetCard_univ, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, hmerge⟩
    rw [mergePair, dif_pos ht] at hmerge
    have hspec := pair_spec ht
    exact hspec.2.trans ((merge_eq_merge_iff ζ hspec.1 hCD).mp hmerge)
  · rintro rfl
    refine ⟨Finset.card_pair hCD, ?_⟩
    have hcard := Finset.card_pair hCD
    have hspec := pair_spec hcard
    rw [mergePair, dif_pos hcard]
    exact (merge_eq_merge_iff ζ hspec.1 hCD).mpr hspec.2.symm

/-- **`Z_p` merges `C` and `D` with probability `p(C) p(D)`.** -/
theorem multiplicativeStep_merge {n : ℕ} (ζ : ER n) {C D : Quotient ζ} (hCD : C ≠ D) :
    multiplicativeStep n ζ (merge ζ C D)
      = blockMass (unitMass n) ζ C * blockMass (unitMass n) ζ D := by
  have hne : merge ζ C D ≠ ζ := fun h ↦ by
    have hb := blocks_merge ζ hCD
    rw [h] at hb
    omega
  rw [multiplicativeStep, filter_mergePair_merge ζ hCD, Finset.sum_singleton, if_neg hne,
    add_zero, Finset.prod_pair hCD]

/-- The uniformized kernel is the rate structure `multiplicativeCoverRate` of
`MultiplicativeObservation` on every cover. -/
theorem multiplicativeStep_merge_eq_multiplicativeCoverRate {n : ℕ} (ζ : ER n)
    {C D : Quotient ζ} (hCD : C ≠ D) :
    multiplicativeStep n ζ (merge ζ C D)
      = multiplicativeCoverRate (unitMass n) ζ ⟨merge ζ C D, merge_covers ζ hCD⟩ := by
  rw [multiplicativeStep_merge ζ hCD, multiplicativeCoverRate_merge (unitMass n) ζ hCD]

/-! ### Loads against component sizes -/

/-- **The size of a report component**, `c(C)`: the individuals the graph reports together.

Empirical status: NOT AN EMPIRICAL CLAIM.  A cardinality. -/
def componentSize {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C : Quotient (observed s ξ)) : ℕ :=
  (univ.filter fun i ↦ Quotient.mk (observed s ξ) i = C).card

/-- A component's mass under unit masses is its size over `n`. -/
theorem blockMass_unitMass_observed {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    (C : Quotient (observed s ξ)) :
    blockMass (unitMass n) (observed s ξ) C = (componentSize s ξ C : ℝ) / n := by
  simp only [blockMass, unitMass, Finset.sum_const, nsmul_eq_mul, componentSize]
  rw [mul_one_div]

/-- **A component hides no more lineages than it has individuals**: `L_C ≤ c(C)`. -/
theorem hiddenLoad_le_componentSize {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    (C : Quotient (observed s ξ)) : hiddenLoad s ξ C ≤ componentSize s ξ C := by
  have hsub : hiddenBlocks s ξ C
      ⊆ (univ.filter fun i ↦ Quotient.mk (observed s ξ) i = C).image (Quotient.mk ξ) := by
    intro block hblock
    obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ block
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      (Finset.mem_filter.mp hblock).2⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- The component sizes add up to the panel. -/
theorem sum_componentSize {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ C, componentSize s ξ C = n := by
  unfold componentSize
  rw [← Finset.card_eq_sum_card_fiberwise (f := Quotient.mk (observed s ξ))
    (s := univ) (t := univ) fun i _ ↦ Finset.mem_univ _, Finset.card_univ, Fintype.card_fin]

/-- **The scaled load** `L_C/n`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A count divided by the sample size. -/
def scaledLoad {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (C : Quotient (observed s ξ)) : ℝ :=
  (hiddenLoad s ξ C : ℝ) / n

theorem scaledLoad_nonneg {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    (C : Quotient (observed s ξ)) : 0 ≤ scaledLoad s ξ C := by
  unfold scaledLoad
  positivity

/-- While the reports agree, the scaled load is at most the component's mass. -/
theorem scaledLoad_le_blockMass {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    (C : Quotient (observed s ξ)) :
    scaledLoad s ξ C ≤ blockMass (unitMass n) (observed s ξ) C := by
  rw [blockMass_unitMass_observed, scaledLoad]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hiddenLoad_le_componentSize s ξ C)
    (Nat.cast_nonneg n)

/-- Under unit masses the components carry total mass one. -/
theorem sum_blockMass_unitMass {n : ℕ} (hn : 0 < n) (ζ : ER n) :
    ∑ C, blockMass (unitMass n) ζ C = 1 := by
  rw [sum_blockMass]
  simp only [unitMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_one_div_cancel hnR.ne']

/-- **The scaled deficit is `J/n = (n - K)/n`.** -/
theorem sum_loadDeficit_scaled {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ C, loadDeficit (blockMass (unitMass n) (observed s ξ)) (scaledLoad s ξ) C
      = ((n : ℝ) - blocks ξ) / n := by
  rw [sum_loadDeficit]
  simp only [blockMass_unitMass_observed, scaledLoad, ← Finset.sum_div]
  rw [← sub_div]
  have h1 : (∑ C, (componentSize s ξ C : ℝ)) = n := by exact_mod_cast sum_componentSize s ξ
  have h2 : (∑ C, (hiddenLoad s ξ C : ℝ)) = blocks ξ := by exact_mod_cast sum_hiddenLoad s ξ
  rw [h1, h2]

/-! ### Visible covers, counted by report state -/

/-- **A cover of `ξ` reports the merge of `C` and `D` exactly when it is a visible cover joining
them.** -/
theorem covers_observed_eq_merge_iff {n : ℕ} (s : Fin n → Fin n) (ξ : ER n)
    {C D : Quotient (observed s ξ)} (hCD : C ≠ D) (η : ER n) :
    Covers ξ η ∧ observed s η = merge (observed s ξ) C D ↔ η ∈ visibleCovers s ξ C D := by
  constructor
  · rintro ⟨hcov, hobs⟩
    obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ξ η).mp hcov
    obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ A
    obtain ⟨y, rfl⟩ := quotient_mk_surjective ξ B
    by_cases hxy : (observed s ξ).r x y
    · rw [observed_merge_of_rel hAB hxy] at hobs
      have hb := blocks_merge (observed s ξ) hCD
      rw [← hobs] at hb
      omega
    · rw [observed_merge_of_not_rel hAB hxy] at hobs
      have hxy' : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
        fun h ↦ hxy (Quotient.exact h)
      have hpair := (merge_eq_merge_iff (observed s ξ) hxy' hCD).mp hobs
      have hx : Quotient.mk (observed s ξ) x ∈ ({C, D} : Finset (Quotient (observed s ξ))) :=
        hpair ▸ Finset.mem_insert_self _ _
      have hy : Quotient.mk (observed s ξ) y ∈ ({C, D} : Finset (Quotient (observed s ξ))) :=
        hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact absurd (hx.trans hy.symm) hxy'
      · exact ⟨Quotient.mk ξ x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
          Quotient.mk ξ y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
      · exact ⟨Quotient.mk ξ y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩,
          Quotient.mk ξ x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, merge_comm ξ hAB⟩
      · exact absurd (hx.trans hy.symm) hxy'
  · intro hη
    refine ⟨(covers_covers_of_mem_visibleCovers hCD hη).1, ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hη
    obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
    obtain ⟨y, rfl⟩ := quotient_mk_surjective ξ b
    have hxC : Quotient.mk (observed s ξ) x = C := (Finset.mem_filter.mp ha).2
    have hyD : Quotient.mk (observed s ξ) y = D := (Finset.mem_filter.mp hb).2
    have hxy : ¬ (observed s ξ).r x y :=
      fun h ↦ hCD (hxC.symm.trans ((Quotient.sound h).trans hyD))
    have hab : Quotient.mk ξ x ≠ Quotient.mk ξ y :=
      fun h ↦ hxy (le_observed s ξ (Quotient.exact h))
    rw [observed_merge_of_not_rel hab hxy, hxC, hyD]

/-- **The visible mass into a new report state is the lumped visible rate.**  The covers of `ξ`
whose report is `ζ' ≠ Y`, at `1/n²` each, carry `L_C L_D/n²` when `ζ'` merges `C` and `D`, and
nothing otherwise. -/
theorem card_covers_observed_eq_div {n : ℕ} (s : Fin n → Fin n) (ξ ζ' : ER n)
    (hζ' : ζ' ≠ observed s ξ) :
    (((univ.filter fun η ↦ Covers ξ η ∧ observed s η = ζ').card : ℕ) : ℝ) / (n : ℝ) ^ 2
      = ∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair (observed s ξ) t = ζ'),
          ∏ C ∈ t, scaledLoad s ξ C := by
  by_cases hmerge : ∃ C D : Quotient (observed s ξ), C ≠ D ∧ ζ' = merge (observed s ξ) C D
  · obtain ⟨C, D, hCD, rfl⟩ := hmerge
    rw [filter_mergePair_merge _ hCD, Finset.sum_singleton, Finset.prod_pair hCD, scaledLoad,
      scaledLoad]
    have hcard : (univ.filter fun η ↦ Covers ξ η ∧ observed s η = merge (observed s ξ) C D).card
        = hiddenLoad s ξ C * hiddenLoad s ξ D := by
      rw [← card_visibleCovers s ξ hCD, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr
        (Equiv.subtypeEquivRight fun η ↦ covers_observed_eq_merge_iff s ξ hCD η)
    rw [hcard]
    push_cast
    ring
  · have hempty1 : (univ.filter fun η ↦ Covers ξ η ∧ observed s η = ζ') = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun η _ ⟨hcov, hobs⟩ ↦ ?_
      rcases observed_eq_or_covers s hcov with h | h
      · exact hζ' (hobs.symm.trans h)
      · obtain ⟨C, D, hCD, heq⟩ := (covers_iff_exists_merge _ _).mp h
        exact hmerge ⟨C, D, hCD, hobs.symm.trans heq⟩
    have hempty2 : (univ.powersetCard 2).filter
        (fun t ↦ mergePair (observed s ξ) t = ζ') = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun t ht heq ↦ ?_
      have hcard := Finset.mem_powersetCard_univ.mp ht
      rw [mergePair, dif_pos hcard] at heq
      exact hmerge ⟨_, _, (pair_spec hcard).1, heq.symm⟩
    rw [hempty1, hempty2, Finset.card_empty, Finset.sum_empty]
    simp

/-! ### The excess of `Z_p` -/

/-- **The excess of `Z_p` over the report's visible mass, into a report state**: the probability
with which `Z_p` merges alone and the coupling separates.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of differences of rate products. -/
def excessStep {n : ℕ} (s : Fin n → Fin n) (ξ ζ' : ER n) : ℝ :=
  ∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair (observed s ξ) t = ζ'),
    (∏ C ∈ t, blockMass (unitMass n) (observed s ξ) C - ∏ C ∈ t, scaledLoad s ξ C)

theorem excessStep_nonneg {n : ℕ} (s : Fin n → Fin n) (ξ ζ' : ER n) :
    0 ≤ excessStep s ξ ζ' :=
  Finset.sum_nonneg fun _ _ ↦ sub_nonneg.mpr
    (Finset.prod_le_prod (fun C _ ↦ scaledLoad_nonneg s ξ C)
      fun C _ ↦ scaledLoad_le_blockMass s ξ C)

/-- **The total excess is the pair-sum gap** `∑_{C<D} (p(C) p(D) - L_C L_D/n²)`. -/
theorem sum_excessStep {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ ζ', excessStep s ξ ζ' = pairProductSum (blockMass (unitMass n) (observed s ξ))
      - pairProductSum (scaledLoad s ξ) := by
  unfold excessStep pairProductSum
  rw [Finset.sum_fiberwise ((univ : Finset (Quotient (observed s ξ))).powersetCard 2)
    (mergePair (observed s ξ)) fun t ↦
      ∏ C ∈ t, blockMass (unitMass n) (observed s ξ) C - ∏ C ∈ t, scaledLoad s ξ C,
    Finset.sum_sub_distrib]

/-- **The separation hazard is at most `J/n`**, `J = n - K`. -/
theorem sum_excessStep_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (ξ : ER n) :
    ∑ ζ', excessStep s ξ ζ' ≤ ((n : ℝ) - blocks ξ) / n := by
  rw [sum_excessStep, ← sum_loadDeficit_scaled s ξ]
  have h := pairProductSum_sub_le (c := blockMass (unitMass n) (observed s ξ))
    (L := scaledLoad s ξ) (fun C ↦ Finset.sum_nonneg fun i _ ↦ unitMass_nonneg n i)
    (scaledLoad_le_blockMass s ξ)
  rwa [sum_blockMass_unitMass hn, one_mul] at h

/-! ### The coupled chain -/

/-- A block count never exceeds the sample size. -/
theorem blocks_le_card {n : ℕ} (ξ : ER n) : blocks ξ ≤ n := by
  have h := Nat.card_le_card_of_surjective (Quotient.mk ξ) (quotient_mk_surjective ξ)
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h
  exact h

/-- **A coupled state**: the labeled coalescent state, the state of `Z_p`, and the separation
flag.

Empirical status: NOT AN EMPIRICAL CLAIM.  A product of finite types. -/
abbrev CoupledState (n : ℕ) := ER n × ER n × Bool

/-- **Separated**: the flag is raised, or the report and `Z_p` disagree.

Empirical status: NOT AN EMPIRICAL CLAIM.  A predicate on coupled states. -/
def coupledSep {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) : Prop :=
  X.2.2 = true ∨ X.2.1 ≠ observed s X.1

/-- **The deficit of a coupled state**, `J = n - K`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The Kingman mergers so far. -/
def coupledDeficit {n : ℕ} (X : CoupledState n) : ℝ := (n : ℝ) - blocks X.1

/-- The mass with which the unseparated coupled chain holds.

Empirical status: NOT AN EMPIRICAL CLAIM.  One minus the probabilities of the moves. -/
def coupledHold {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : ℝ :=
  1 - deathRate (blocks ξ) / (n : ℝ) ^ 2 - ∑ ζ', excessStep s ξ ζ'

/-- **The coupled step.**  Separated, the coordinates move independently and the flag stays up.
Unseparated, a cover of the coalescent moves the report and `Z_p` together, the excess moves
`Z_p` alone and raises the flag, and otherwise nothing moves.

Empirical status: NOT AN EMPIRICAL CLAIM.  A stochastic matrix built from the two kernels. -/
def coupledStep {n : ℕ} (s : Fin n → Fin n) (X Y : CoupledState n) : ℝ :=
  if coupledSep s X then
    kingmanStep n X.1 Y.1 * multiplicativeStep n X.2.1 Y.2.1 * (if Y.2.2 = true then 1 else 0)
  else
    (if Y.2.2 = false ∧ Covers X.1 Y.1 ∧ observed s Y.1 = Y.2.1 then 1 / (n : ℝ) ^ 2 else 0)
      + (if Y.2.2 = false ∧ Y.1 = X.1 ∧ Y.2.1 = X.2.1 then coupledHold s X.1 else 0)
      + (if Y.2.2 = true ∧ Y.1 = X.1 then excessStep s X.1 Y.2.1 else 0)

theorem sum_coupledState {n : ℕ} (f : CoupledState n → ℝ) :
    ∑ Y, f Y = ∑ ξ', ∑ ζ', (f (ξ', ζ', true) + f (ξ', ζ', false)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ξ' _ ↦ ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ζ' _ ↦ Fintype.sum_bool _

theorem coupledStep_true_of_not_sep {n : ℕ} {s : Fin n → Fin n} {X : CoupledState n}
    (hX : ¬ coupledSep s X) (ξ' ζ' : ER n) :
    coupledStep s X (ξ', ζ', true) = if ξ' = X.1 then excessStep s X.1 ζ' else 0 := by
  simp [coupledStep, hX]

theorem coupledStep_false_of_not_sep {n : ℕ} {s : Fin n → Fin n} {X : CoupledState n}
    (hX : ¬ coupledSep s X) (ξ' ζ' : ER n) :
    coupledStep s X (ξ', ζ', false)
      = (if Covers X.1 ξ' ∧ observed s ξ' = ζ' then 1 / (n : ℝ) ^ 2 else 0)
        + if ξ' = X.1 ∧ ζ' = X.2.1 then coupledHold s X.1 else 0 := by
  simp [coupledStep, hX]

theorem coupledStep_of_sep {n : ℕ} {s : Fin n → Fin n} {X : CoupledState n}
    (hX : coupledSep s X) (ξ' ζ' : ER n) (b : Bool) :
    coupledStep s X (ξ', ζ', b)
      = kingmanStep n X.1 ξ' * multiplicativeStep n X.2.1 ζ' * (if b = true then 1 else 0) := by
  simp only [coupledStep, if_pos hX]

theorem sum_sum_ite_eq_and_eq {n : ℕ} (a b : ER n) (c : ℝ) :
    ∑ ξ' : ER n, ∑ ζ' : ER n, (if ξ' = a ∧ ζ' = b then c else 0) = c := by
  have hinner : ∀ ξ' : ER n,
      ∑ ζ' : ER n, (if ξ' = a ∧ ζ' = b then c else 0) = if ξ' = a then c else 0 := by
    intro ξ'
    by_cases h : ξ' = a <;> simp [h]
  simp only [hinner, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_sum_ite_covers_observed {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (g : ER n → ℝ) :
    ∑ ξ' : ER n, ∑ ζ' : ER n, (if Covers ξ ξ' ∧ observed s ξ' = ζ' then g ξ' else 0)
      = ∑ ξ' : ER n, if Covers ξ ξ' then g ξ' else 0 := by
  refine Finset.sum_congr rfl fun ξ' _ ↦ ?_
  by_cases h : Covers ξ ξ' <;> simp [h]

theorem sum_sum_ite_eq_left {n : ℕ} (a : ER n) (g : ER n → ℝ) :
    ∑ ξ' : ER n, ∑ ζ' : ER n, (if ξ' = a then g ζ' else 0) = ∑ ζ', g ζ' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ζ' _ ↦ ?_
  simp

/-- The unseparated holding mass is nonnegative. -/
theorem coupledHold_nonneg {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (ξ : ER n) :
    0 ≤ coupledHold s ξ := by
  have h1 := deathRate_div_sq_le_half (blocks_le_card ξ)
  have h2 := pairProductSum_blockMass_unitMass_le_half (observed s ξ)
  have h3 := pairProductSum_nonneg (scaledLoad_nonneg s ξ)
  have h4 := sum_excessStep s ξ
  unfold coupledHold
  linarith

theorem coupledStep_nonneg {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (X Y : CoupledState n) :
    0 ≤ coupledStep s X Y := by
  unfold coupledStep
  by_cases hX : coupledSep s X
  · rw [if_pos hX]
    refine mul_nonneg (mul_nonneg (kingmanStep_nonneg (blocks_le_card _) _)
      (multiplicativeStep_nonneg _ _)) ?_
    split_ifs <;> norm_num
  · rw [if_neg hX]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · split_ifs
      · positivity
      · exact le_rfl
    · split_ifs
      · exact coupledHold_nonneg hn s X.1
      · exact le_rfl
    · split_ifs
      · exact excessStep_nonneg s X.1 Y.2.1
      · exact le_rfl

/-- **The coupled step is stochastic.** -/
theorem sum_coupledStep {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) :
    ∑ Y, coupledStep s X Y = 1 := by
  rw [sum_coupledState]
  by_cases hX : coupledSep s X
  · simp only [coupledStep_of_sep hX, if_true, Bool.false_eq_true, if_false, mul_one, mul_zero,
      add_zero]
    rw [← Finset.sum_mul_sum, sum_kingmanStep, sum_multiplicativeStep, one_mul]
  · simp only [coupledStep_true_of_not_sep hX, coupledStep_false_of_not_sep hX,
      Finset.sum_add_distrib, sum_sum_ite_eq_left, sum_sum_ite_covers_observed,
      sum_sum_ite_eq_and_eq, sum_ite_covers]
    unfold coupledHold
    ring

/-- **Separation is absorbing.** -/
theorem coupledStep_absorb {n : ℕ} (s : Fin n → Fin n) (X Y : CoupledState n)
    (hX : coupledSep s X) (hY : ¬ coupledSep s Y) : coupledStep s X Y = 0 := by
  have hflag : Y.2.2 ≠ true := fun h ↦ hY (Or.inl h)
  simp only [coupledStep, if_pos hX, if_neg hflag, mul_zero]

/-- While unseparated, the report and `Z_p` agree. -/
theorem observed_eq_of_not_coupledSep {n : ℕ} {s : Fin n → Fin n} {X : CoupledState n}
    (hX : ¬ coupledSep s X) : observed s X.1 = X.2.1 := by
  unfold coupledSep at hX
  push_neg at hX
  exact hX.2.symm

theorem coupledDeficit_nonneg {n : ℕ} (X : CoupledState n) : 0 ≤ coupledDeficit X := by
  unfold coupledDeficit
  have h : (blocks X.1 : ℝ) ≤ n := by exact_mod_cast blocks_le_card X.1
  linarith

/-- **The separation hazard of the coupled step is at most `J/n`.** -/
theorem coupledStep_hazard {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (X : CoupledState n)
    (hX : ¬ coupledSep s X) :
    ∑ Y ∈ univ.filter (coupledSep s), coupledStep s X Y ≤ 1 / (n : ℝ) * coupledDeficit X := by
  have hagree := observed_eq_of_not_coupledSep hX
  have hpoint : ∀ Y ∈ univ.filter (coupledSep s),
      coupledStep s X Y = if Y.2.2 = true ∧ Y.1 = X.1 then excessStep s X.1 Y.2.1 else 0 := by
    intro Y hY
    have hYsep := (Finset.mem_filter.mp hY).2
    have h1 : ¬ (Y.2.2 = false ∧ Covers X.1 Y.1 ∧ observed s Y.1 = Y.2.1) := by
      rintro ⟨hb, -, hobs⟩
      rcases hYsep with h | h
      · rw [hb] at h
        exact Bool.false_ne_true h
      · exact h hobs.symm
    have h2 : ¬ (Y.2.2 = false ∧ Y.1 = X.1 ∧ Y.2.1 = X.2.1) := by
      rintro ⟨hb, hY1, hY2⟩
      rcases hYsep with h | h
      · rw [hb] at h
        exact Bool.false_ne_true h
      · exact h (by rw [hY1, hY2, hagree])
    rw [coupledStep, if_neg hX, if_neg h1, if_neg h2, zero_add, zero_add]
  calc ∑ Y ∈ univ.filter (coupledSep s), coupledStep s X Y
      = ∑ Y ∈ univ.filter (coupledSep s),
          (if Y.2.2 = true ∧ Y.1 = X.1 then excessStep s X.1 Y.2.1 else 0) :=
        Finset.sum_congr rfl hpoint
    _ ≤ ∑ Y : CoupledState n,
          (if Y.2.2 = true ∧ Y.1 = X.1 then excessStep s X.1 Y.2.1 else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Y _ _ ↦ by
          split_ifs
          · exact excessStep_nonneg s X.1 Y.2.1
          · exact le_rfl
    _ = ∑ ζ', excessStep s X.1 ζ' := by
        rw [sum_coupledState, ← sum_sum_ite_eq_left X.1 (excessStep s X.1)]
        refine Finset.sum_congr rfl fun ξ' _ ↦ Finset.sum_congr rfl fun ζ' _ ↦ ?_
        by_cases h : ξ' = X.1 <;> simp [h]
    _ ≤ ((n : ℝ) - blocks X.1) / n := sum_excessStep_le hn s X.1
    _ = 1 / (n : ℝ) * coupledDeficit X := by
        unfold coupledDeficit
        ring

/-- **The deficit drifts by at most one half per step.** -/
theorem coupledStep_drift {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (X : CoupledState n)
    (hX : ¬ coupledSep s X) :
    ∑ Y ∈ univ.filter (fun Y ↦ ¬ coupledSep s Y), coupledStep s X Y * coupledDeficit Y
      ≤ coupledDeficit X + 1 / 2 := by
  have hpoint : ∀ Y ∈ univ.filter (fun Y ↦ ¬ coupledSep s Y),
      coupledStep s X Y * coupledDeficit Y
        = coupledDeficit X * coupledStep s X Y
          + if Y.2.2 = false ∧ Covers X.1 Y.1 ∧ observed s Y.1 = Y.2.1
            then 1 / (n : ℝ) ^ 2 else 0 := by
    intro Y hY
    have hYns := (Finset.mem_filter.mp hY).2
    have hflag : ¬ (Y.2.2 = true ∧ Y.1 = X.1) := fun h ↦ hYns (Or.inl h.1)
    rw [coupledStep, if_neg hX, if_neg hflag, add_zero]
    unfold coupledDeficit
    by_cases h1 : Y.2.2 = false ∧ Covers X.1 Y.1 ∧ observed s Y.1 = Y.2.1
    · by_cases h2 : Y.2.2 = false ∧ Y.1 = X.1 ∧ Y.2.1 = X.2.1
      · exfalso
        have hb := h1.2.1.2
        rw [h2.2.1] at hb
        omega
      · rw [if_pos h1, if_neg h2]
        have hb : (blocks Y.1 : ℝ) + 1 = blocks X.1 := by exact_mod_cast h1.2.1.2
        rw [← hb]
        ring
    · rw [if_neg h1]
      by_cases h2 : Y.2.2 = false ∧ Y.1 = X.1 ∧ Y.2.1 = X.2.1
      · rw [if_pos h2, h2.2.1]
        ring
      · rw [if_neg h2]
        ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmass : ∑ Y ∈ univ.filter (fun Y ↦ ¬ coupledSep s Y), coupledStep s X Y ≤ 1 := by
    rw [← sum_coupledStep s X]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun Y _ _ ↦ coupledStep_nonneg hn s X Y
  have hterm : ∑ Y ∈ univ.filter (fun Y ↦ ¬ coupledSep s Y),
      (if Y.2.2 = false ∧ Covers X.1 Y.1 ∧ observed s Y.1 = Y.2.1
        then 1 / (n : ℝ) ^ 2 else 0) ≤ 1 / 2 := by
    calc _ ≤ ∑ Y : CoupledState n, (if Y.2.2 = false ∧ Covers X.1 Y.1 ∧ observed s Y.1 = Y.2.1
          then 1 / (n : ℝ) ^ 2 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Y _ _ ↦ by
            split_ifs
            · positivity
            · exact le_rfl
      _ = deathRate (blocks X.1) * (1 / (n : ℝ) ^ 2) := by
          rw [sum_coupledState, ← sum_ite_covers,
            ← sum_sum_ite_covers_observed s X.1 fun _ ↦ 1 / (n : ℝ) ^ 2]
          refine Finset.sum_congr rfl fun ξ' _ ↦ Finset.sum_congr rfl fun ζ' _ ↦ ?_
          by_cases h : Covers X.1 ξ' ∧ observed s ξ' = ζ' <;> simp [h]
      _ ≤ 1 / 2 := by
          rw [mul_one_div]
          exact deathRate_div_sq_le_half (blocks_le_card X.1)
  have hJ := coupledDeficit_nonneg X
  nlinarith [mul_le_mul_of_nonneg_left hmass hJ]

/-! ### The start -/

/-- **The coupled start**: the panel's singletons, `Z_p` at the interface, the flag down.

Empirical status: NOT AN EMPIRICAL CLAIM.  A point of the coupled state space. -/
def coupledStart {n : ℕ} (s : Fin n → Fin n) : CoupledState n := (⊥, observed s ⊥, false)

/-- The point mass at the coupled start.

Empirical status: NOT AN EMPIRICAL CLAIM.  A point mass. -/
def coupledStartLaw {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) : ℝ :=
  if X = coupledStart s then 1 else 0

theorem coupledStartLaw_nonneg {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) :
    0 ≤ coupledStartLaw s X := by
  unfold coupledStartLaw
  split_ifs <;> norm_num

theorem sum_coupledStartLaw {n : ℕ} (s : Fin n → Fin n) : ∑ X, coupledStartLaw s X = 1 := by
  simp [coupledStartLaw]

theorem not_coupledSep_start {n : ℕ} (s : Fin n → Fin n) : ¬ coupledSep s (coupledStart s) := by
  simp [coupledSep, coupledStart]

theorem coupledDeficit_start {n : ℕ} (s : Fin n → Fin n) :
    coupledDeficit (coupledStart s) = 0 := by
  have h := blocks_bot n
  simp only [coupledDeficit, coupledStart]
  rw [h, sub_self]

theorem separationMass_coupledStart {n : ℕ} (s : Fin n → Fin n) :
    separationMass (coupledStep s) (coupledStartLaw s) (coupledSep s) 0 = 0 := by
  refine Finset.sum_eq_zero fun X hX ↦ ?_
  show coupledStartLaw s X = 0
  refine if_neg fun h ↦ ?_
  rw [h] at hX
  exact not_coupledSep_start s (Finset.mem_filter.mp hX).2

theorem deficitMass_coupledStart {n : ℕ} (s : Fin n → Fin n) :
    deficitMass (coupledStep s) (coupledStartLaw s) (coupledSep s) coupledDeficit 0 ≤ 0 := by
  refine le_of_eq (Finset.sum_eq_zero fun X _ ↦ ?_)
  show coupledStartLaw s X * coupledDeficit X = 0
  unfold coupledStartLaw
  by_cases h : X = coupledStart s
  · rw [if_pos h, h, coupledDeficit_start, mul_zero]
  · rw [if_neg h, zero_mul]

/-- **The coupled chain separates by step `m` with probability at most `m(m-1)/(4n)`.** -/
theorem coupled_separationMass_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (m : ℕ) :
    separationMass (coupledStep s) (coupledStartLaw s) (coupledSep s) m
      ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n) := by
  have h := separationMass_le (J := coupledDeficit) (h := 1 / (n : ℝ)) (ρ := 1 / 2)
    (coupledStep_nonneg hn s) (sum_coupledStep s) (coupledStartLaw_nonneg s)
    (sum_coupledStartLaw s) (by positivity) (by norm_num)
    (fun X Y hX hY ↦ coupledStep_absorb s X Y hX hY) (coupledStep_hazard hn s)
    (coupledStep_drift hn s) (separationMass_coupledStart s) (deficitMass_coupledStart s) m
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc _ ≤ 1 / (n : ℝ) * (1 / 2) * ((m : ℝ) * ((m : ℝ) - 1) / 2) := h
    _ = (m : ℝ) * ((m : ℝ) - 1) / (4 * n) := by
        field_simp
        ring

/-! ### The two marginals -/

theorem sum_filter_fst_coupledState {n : ℕ} (f : CoupledState n → ℝ) (ξ' : ER n) :
    ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.1 = ξ'), f Y
      = ∑ ζ', (f (ξ', ζ', true) + f (ξ', ζ', false)) := by
  rw [Finset.sum_filter, sum_coupledState, Finset.sum_eq_single ξ']
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ ξ') h

theorem sum_filter_snd_coupledState {n : ℕ} (f : CoupledState n → ℝ) (ζ' : ER n) :
    ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.2.1 = ζ'), f Y
      = ∑ ξ', (f (ξ', ζ', true) + f (ξ', ζ', false)) := by
  rw [Finset.sum_filter, sum_coupledState]
  refine Finset.sum_congr rfl fun ξ' _ ↦ ?_
  rw [Finset.sum_eq_single ζ']
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ ζ') h

/-- **The first coordinate of the coupled chain is the uniformized Kingman chain.** -/
theorem sum_coupledStep_fst {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) (ξ' : ER n) :
    ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.1 = ξ'), coupledStep s X Y
      = kingmanStep n X.1 ξ' := by
  rw [sum_filter_fst_coupledState]
  by_cases hX : coupledSep s X
  · simp only [coupledStep_of_sep hX, if_true, Bool.false_eq_true, if_false, mul_one, mul_zero,
      add_zero]
    rw [← Finset.mul_sum, sum_multiplicativeStep, mul_one]
  · simp only [coupledStep_true_of_not_sep hX, coupledStep_false_of_not_sep hX,
      Finset.sum_add_distrib]
    unfold kingmanStep coupledHold
    by_cases hc : Covers X.1 ξ'
    · have hne : ξ' ≠ X.1 := fun h ↦ by
        have hb := hc.2
        rw [h] at hb
        omega
      simp [hc, hne]
    · by_cases he : ξ' = X.1
      · subst he
        simp [hc] <;> ring
      · simp [hc, he]

/-- **The second coordinate of the coupled chain is the uniformized `Z_p`.**  Off the diagonal
the visible mass and the excess add up to `p(C) p(D)`; on it, both kernels are stochastic. -/
theorem sum_coupledStep_snd {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) (ζ' : ER n) :
    ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.2.1 = ζ'), coupledStep s X Y
      = multiplicativeStep n X.2.1 ζ' := by
  rw [sum_filter_snd_coupledState]
  by_cases hX : coupledSep s X
  · simp only [coupledStep_of_sep hX, if_true, Bool.false_eq_true, if_false, mul_one, mul_zero,
      add_zero]
    rw [← Finset.sum_mul, sum_kingmanStep, one_mul]
  · have hagree := observed_eq_of_not_coupledSep hX
    set f : ER n → ℝ := fun ζ'' ↦
      ∑ ξ', (coupledStep s X (ξ', ζ'', true) + coupledStep s X (ξ', ζ'', false)) with hf
    have hoff : ∀ ζ'', ζ'' ≠ X.2.1 → f ζ'' = multiplicativeStep n X.2.1 ζ'' := by
      intro ζ'' hne
      have hne' : ζ'' ≠ observed s X.1 := fun h ↦ hne (h.trans hagree)
      simp only [hf, coupledStep_true_of_not_sep hX, coupledStep_false_of_not_sep hX,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hthird : ∑ ξ' : ER n, (if ξ' = X.1 ∧ ζ'' = X.2.1 then coupledHold s X.1 else 0) = 0 :=
        Finset.sum_eq_zero fun ξ' _ ↦ if_neg fun h ↦ hne h.2
      have hsecond : ∑ ξ' : ER n,
          (if Covers X.1 ξ' ∧ observed s ξ' = ζ'' then 1 / (n : ℝ) ^ 2 else 0)
          = ∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair (observed s X.1) t = ζ''),
              ∏ C ∈ t, scaledLoad s X.1 C := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
          mul_one_div]
        exact card_covers_observed_eq_div s X.1 ζ'' hne'
      rw [hthird, hsecond, add_zero, ← hagree, multiplicativeStep, if_neg hne', add_zero,
        excessStep, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    by_cases hζ : ζ' = X.2.1
    · have htot : ∑ ζ'', f ζ'' = 1 := by
        have h := sum_coupledStep s X
        rw [sum_coupledState, Finset.sum_comm] at h
        exact h
      have h1 := Finset.add_sum_erase univ f (Finset.mem_univ X.2.1)
      have h2 := Finset.add_sum_erase univ (multiplicativeStep n X.2.1) (Finset.mem_univ X.2.1)
      have h3 : ∑ ζ'' ∈ univ.erase X.2.1, f ζ''
          = ∑ ζ'' ∈ univ.erase X.2.1, multiplicativeStep n X.2.1 ζ'' :=
        Finset.sum_congr rfl fun ζ'' hζ'' ↦ hoff ζ'' (Finset.ne_of_mem_erase hζ'')
      rw [sum_multiplicativeStep] at h2
      rw [htot] at h1
      show f ζ' = multiplicativeStep n X.2.1 ζ'
      rw [hζ]
      linarith
    · exact hoff ζ' hζ

/-! ### Path laws -/

/-- **Lumping at path level**: if a kernel's mass into every fiber of `π` depends only on the
image of the source, the image of its path law is the path law of the lumped kernel. -/
theorem sum_filter_path_comp_eq {S X : Type*} [Fintype S] [DecidableEq X]
    (P : S → S → ℝ) (μ₀ : S → ℝ) (Q : X → X → ℝ) (ν₀ : X → ℝ) (π : S → X)
    (hlump : ∀ s x, ∑ t ∈ univ.filter (fun t ↦ π t = x), P s t = Q (π s) x)
    (hinit : ∀ x, ∑ s ∈ univ.filter (fun s ↦ π s = x), μ₀ s = ν₀ x) (m : ℕ)
    (y : Fin (m + 1) → X) :
    ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → S ↦ (fun k ↦ π (ω k)) = y),
        skeletonPathWeight P μ₀ m ω = skeletonPathWeight Q ν₀ m y := by
  induction m generalizing y with
  | zero =>
    have hiff : ∀ ω : Fin 1 → S, ((fun k ↦ π (ω k)) = y) ↔ π (ω 0) = y 0 := by
      intro ω
      constructor
      · intro h
        exact congrFun h 0
      · intro h
        funext k
        rw [Subsingleton.elim k 0]
        exact h
    rw [Finset.sum_filter]
    refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _
      (fun t ↦ if π t = y 0 then μ₀ t else 0) fun ω ↦ ?_).trans ?_
    · show (if (fun k ↦ π (ω k)) = y then
          μ₀ (ω 0) * ∏ k : Fin 0, P (ω k.castSucc) (ω k.succ) else 0)
        = if π (ω 0) = y 0 then μ₀ (ω 0) else 0
      rw [Fin.prod_univ_zero, mul_one]
      by_cases h : π (ω 0) = y 0
      · rw [if_pos ((hiff ω).mpr h), if_pos h]
      · rw [if_neg fun h' ↦ h ((hiff ω).mp h'), if_neg h]
    · rw [← Finset.sum_filter, hinit, skeletonPathWeight, Fin.prod_univ_zero, mul_one]
  | succ m ih =>
    have hiff : ∀ (ω' : Fin (m + 1) → S) (x : S),
        ((fun k ↦ π (Fin.snoc ω' x k)) = y)
          ↔ ((fun k ↦ π (ω' k)) = Fin.init y ∧ π x = y (Fin.last (m + 1))) := by
      intro ω' x
      constructor
      · intro h
        refine ⟨funext fun k ↦ ?_, ?_⟩
        · have hk := congrFun h (Fin.castSucc k)
          simpa [Fin.snoc_castSucc, Fin.init] using hk
        · have hk := congrFun h (Fin.last (m + 1))
          simpa [Fin.snoc_last] using hk
      · rintro ⟨h1, h2⟩
        funext k
        refine Fin.lastCases ?_ (fun j ↦ ?_) k
        · simpa [Fin.snoc_last] using h2
        · have hj := congrFun h1 j
          simpa [Fin.snoc_castSucc, Fin.init] using hj
    rw [Finset.sum_filter, sum_pi_fin_succ]
    calc ∑ ω' : Fin (m + 1) → S, ∑ x : S,
          (if (fun k ↦ π (Fin.snoc ω' x k)) = y then
            skeletonPathWeight P μ₀ (m + 1) (Fin.snoc ω' x) else 0)
        = ∑ ω' : Fin (m + 1) → S,
            (if (fun k ↦ π (ω' k)) = Fin.init y then
              skeletonPathWeight P μ₀ m ω' * Q (π (ω' (Fin.last m))) (y (Fin.last (m + 1)))
            else 0) := by
          refine Finset.sum_congr rfl fun ω' _ ↦ ?_
          by_cases h1 : (fun k ↦ π (ω' k)) = Fin.init y
          · rw [if_pos h1, ← hlump (ω' (Fin.last m)) (y (Fin.last (m + 1))), Finset.mul_sum,
              Finset.sum_filter]
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            by_cases h2 : π x = y (Fin.last (m + 1))
            · rw [if_pos ((hiff ω' x).mpr ⟨h1, h2⟩), if_pos h2, skeletonPathWeight_snoc]
            · rw [if_neg fun h ↦ h2 ((hiff ω' x).mp h).2, if_neg h2, mul_zero]
          · rw [if_neg h1]
            exact Finset.sum_eq_zero fun x _ ↦ if_neg fun h ↦ h1 ((hiff ω' x).mp h).1
      _ = ∑ ω' ∈ univ.filter (fun ω' : Fin (m + 1) → S ↦ (fun k ↦ π (ω' k)) = Fin.init y),
            skeletonPathWeight P μ₀ m ω' * Q (Fin.init y (Fin.last m)) (y (Fin.last (m + 1))) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun ω' _ ↦ ?_
          by_cases h1 : (fun k ↦ π (ω' k)) = Fin.init y
          · rw [if_pos h1, if_pos h1, ← congrFun h1 (Fin.last m)]
          · rw [if_neg h1, if_neg h1]
      _ = skeletonPathWeight Q ν₀ m (Fin.init y)
            * Q (Fin.init y (Fin.last m)) (y (Fin.last (m + 1))) := by
          rw [← Finset.sum_mul, ih]
      _ = skeletonPathWeight Q ν₀ (m + 1) y := by
          rw [← skeletonPathWeight_snoc, Fin.snoc_init_self]

/-- **The law of the report's skeleton path**: the uniformized Kingman path law from the panel's
singletons, read through `observed s`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The image of a finite path law. -/
def reportPathLaw {n : ℕ} (s : Fin n → Fin n) (m : ℕ) (y : Fin (m + 1) → ER n) : ℝ :=
  ∑ ξpath ∈ univ.filter (fun ξpath : Fin (m + 1) → ER n ↦ (fun k ↦ observed s (ξpath k)) = y),
    skeletonPathWeight (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m ξpath

/-- **The law of `Z_p`'s skeleton path**, started at the interface.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite path law. -/
def multiplicativePathLaw {n : ℕ} (s : Fin n → Fin n) (m : ℕ) (y : Fin (m + 1) → ER n) : ℝ :=
  skeletonPathWeight (multiplicativeStep n) (fun ζ ↦ if ζ = graphKer s then 1 else 0) m y

theorem sum_filter_fst_coupledStartLaw {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    ∑ X ∈ univ.filter (fun X : CoupledState n ↦ X.1 = ξ), coupledStartLaw s X
      = if ξ = ⊥ then 1 else 0 := by
  rw [sum_filter_fst_coupledState]
  by_cases h : ξ = ⊥ <;> simp [coupledStartLaw, coupledStart, h]

theorem sum_filter_snd_coupledStartLaw {n : ℕ} (s : Fin n → Fin n) (ζ : ER n) :
    ∑ X ∈ univ.filter (fun X : CoupledState n ↦ X.2.1 = ζ), coupledStartLaw s X
      = if ζ = graphKer s then 1 else 0 := by
  rw [sum_filter_snd_coupledState]
  by_cases h : ζ = graphKer s <;> simp [coupledStartLaw, coupledStart, h, observed_bot]

/-- The coupled path law, read through the report, is the report's path law. -/
theorem sum_filter_coupled_report_eq {n : ℕ} (s : Fin n → Fin n) (m : ℕ)
    (y : Fin (m + 1) → ER n) :
    ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → CoupledState n ↦
        (fun k ↦ observed s (ω k).1) = y),
      skeletonPathWeight (coupledStep s) (coupledStartLaw s) m ω = reportPathLaw s m y := by
  unfold reportPathLaw
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ω : Fin (m + 1) → CoupledState n ↦
    fun k ↦ (ω k).1) (t := univ.filter fun ξpath : Fin (m + 1) → ER n ↦
      (fun k ↦ observed s (ξpath k)) = y)]
  · refine Finset.sum_congr rfl fun ξpath hξ ↦ ?_
    rw [Finset.filter_filter]
    have hcongr : univ.filter (fun ω : Fin (m + 1) → CoupledState n ↦
        (fun k ↦ observed s (ω k).1) = y ∧ (fun k ↦ (ω k).1) = ξpath)
        = univ.filter fun ω : Fin (m + 1) → CoupledState n ↦ (fun k ↦ (ω k).1) = ξpath := by
      refine Finset.filter_congr fun ω _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      rw [← (Finset.mem_filter.mp hξ).2, ← h]
    rw [hcongr]
    exact sum_filter_path_comp_eq (coupledStep s) (coupledStartLaw s) (kingmanStep n)
      (fun ξ ↦ if ξ = ⊥ then 1 else 0) Prod.fst (fun X ξ' ↦ sum_coupledStep_fst s X ξ')
      (sum_filter_fst_coupledStartLaw s) m ξpath
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩

/-- The coupled path law, read through `Z_p`'s coordinate, is `Z_p`'s path law. -/
theorem sum_filter_coupled_multiplicative_eq {n : ℕ} (s : Fin n → Fin n) (m : ℕ)
    (y : Fin (m + 1) → ER n) :
    ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → CoupledState n ↦ (fun k ↦ (ω k).2.1) = y),
      skeletonPathWeight (coupledStep s) (coupledStartLaw s) m ω = multiplicativePathLaw s m y :=
  sum_filter_path_comp_eq (coupledStep s) (coupledStartLaw s) (multiplicativeStep n)
    (fun ζ ↦ if ζ = graphKer s then 1 else 0) (fun X ↦ X.2.1)
    (fun X ζ' ↦ sum_coupledStep_snd s X ζ') (sum_filter_snd_coupledStartLaw s) m y

/-! ### Theorem F -/

/-- **Theorem F, (F1), for the uniformized skeleton.**  After `m` rings of the uniformizing clock
the path of the graph's report and the path of the multiplicative coalescent `Z_p` have total
variation at most `m(m-1)/(4n)`.

Assumes: `0 < n`. -/
theorem report_multiplicative_pathTotalVariation_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (m : ℕ) :
    1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - multiplicativePathLaw s m y|
      ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n) := by
  have htv := pathTotalVariation_le_separationMass (coupledStep_nonneg hn s)
    (coupledStartLaw_nonneg s) (fun X Y hX hY ↦ coupledStep_absorb s X Y hX hY)
    (fun X ↦ observed s X.1) (fun X ↦ X.2.1)
    (fun X hX ↦ observed_eq_of_not_coupledSep hX) m
  simp only [sum_filter_coupled_report_eq, sum_filter_coupled_multiplicative_eq] at htv
  have hsep := coupled_separationMass_le hn s m
  linarith

/-- The total variation of the skeleton paths is a probability. -/
theorem report_multiplicative_pathTotalVariation_le_one {n : ℕ} (hn : 0 < n)
    (s : Fin n → Fin n) (m : ℕ) :
    1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - multiplicativePathLaw s m y| ≤ 1 := by
  have htv := pathTotalVariation_le_separationMass (coupledStep_nonneg hn s)
    (coupledStartLaw_nonneg s) (fun X Y hX hY ↦ coupledStep_absorb s X Y hX hY)
    (fun X ↦ observed s X.1) (fun X ↦ X.2.1)
    (fun X hX ↦ observed_eq_of_not_coupledSep hX) m
  simp only [sum_filter_coupled_report_eq, sum_filter_coupled_multiplicative_eq] at htv
  have hone := sum_filter_not_skeletonLaw_le (coupledStep_nonneg hn s) (sum_coupledStep s)
    (coupledStartLaw_nonneg s) (sum_coupledStartLaw s) (univ.filter (coupledSep s)) m
  have hsm : separationMass (coupledStep s) (coupledStartLaw s) (coupledSep s) m ≤ 1 := hone
  linarith

/-- **Theorem F, (F1).**  Run both skeletons at the rings of a Poisson clock of rate one in scaled
time `u = n² t`; by scaled time `U` the paths of the graph's report and of `Z_p` have total
variation at most `min {1, U²/(4n)}`.

Assumes: `0 < n`. -/
theorem report_multiplicative_poissonTotalVariation_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (U : NNReal) :
    poissonMixture U (fun m ↦
        1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - multiplicativePathLaw s m y|)
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n)) :=
  poissonMixture_le_min (by exact_mod_cast hn)
    (fun m ↦ mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    (report_multiplicative_pathTotalVariation_le_one hn s)
    (report_multiplicative_pathTotalVariation_le hn s)

end

end Descent.Pangenome.GraphCoalescent
