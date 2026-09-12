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

end

end Descent.Pangenome.GraphCoalescent
