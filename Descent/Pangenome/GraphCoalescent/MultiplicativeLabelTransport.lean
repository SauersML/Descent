/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence
import Descent.Pangenome.GraphCoalescent.MultiplicativePerturbation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The multiplicative coalescent on the fiber labels

Theorem F of the hidden-clock note states its bound for `Z_p` on the `w` fiber labels.
`Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling` runs `Z` on the partitions of the `n`
individuals from the interface, with mass `1/n` each, and proves (F1) there.  This file shows the
two are one process, and moves (F1) to the labels.

## The transport

Take an interface given by a surjective labelling `label : Fin n → Fin w`
(`MultiplicativeConnectionConvergence.labelInterface`).  The partitions of the individuals above it
are the pull-backs `Setoid.comap label τ` of the partitions `τ` of the labels.  A class of a
pull-back is a class of `τ` (`labelBlock`, a bijection), merging commutes with pulling back
(`comap_merge_labelBlock`), and the mass of a class is the pushed mass of its label class
(`blockMass_comap`).  So the uniformized kernel of `Z` on individuals, read on pull-backs, is the
uniformized kernel of `Z` on the labels with the pushed masses (`massStep_comap`); with unit masses
the pushed masses are the fiber proportions `p^(n)_i = c_i/n` (`pushMass_unitMass`).

## Main results

- `massStep_comap`: the kernel of `Z` on the individuals, on pull-backs, is the kernel on the
  labels.
- `multiplicativePathLaw_comap`: the path law of `Z_{p^(n)}` on the individuals, on pulled-back
  paths, is the path law on the labels from the singletons.
- `label_report_multiplicative_pathTotalVariation_le`,
  `label_report_multiplicative_poissonTotalVariation_le`: **(F1) on the fiber labels**.  The
  report's path, read on the labels, and `Z_{p^(n)}` on the labels have skeleton total variation at
  most `m(m-1)/(4n)` after `m` rings, and `min {1, U²/(4n)}` at the rings of a Poisson clock of
  mean `U`.

## Scope

As in `MultiplicativeCoupling`, time is the rate-one uniformization in scaled time.  The report
read on the labels is the report's path pulled back through the bijection between partitions above
the interface and partitions of the labels (`labelReportPathLaw`).

## Empirical status

None.  Every declaration here is a finite stochastic matrix on equivalence relations on a finite
set, a finite sum, or the Poisson mass function.  The reading of a labelling as a real graph's
interface is stated in `Descent.Pangenome.GraphCoalescent.Observation` and is not asserted of any
dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset

open scoped Classical

noncomputable section

/-! ### Classes of a pull-back are label classes -/

/-- **The label class of a class of a pull-back**: the class of its individuals' label.

Empirical status: NOT AN EMPIRICAL CLAIM.  The map induced on quotients. -/
def labelBlock {n w : ℕ} (label : Fin n → Fin w) (τ : ER w) :
    Quotient (Setoid.comap label τ) → Quotient τ :=
  Quotient.lift (fun x ↦ Quotient.mk τ (label x)) fun _ _ hab ↦ Quotient.sound hab

theorem labelBlock_mk {n w : ℕ} (label : Fin n → Fin w) (τ : ER w) (x : Fin n) :
    labelBlock label τ (Quotient.mk _ x) = Quotient.mk τ (label x) :=
  rfl

theorem labelBlock_injective {n w : ℕ} (label : Fin n → Fin w) (τ : ER w) :
    Function.Injective (labelBlock label τ) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ fun x y hxy ↦ ?_
  have hlabel : Quotient.mk τ (label x) = Quotient.mk τ (label y) := hxy
  have hrel : τ.r (label x) (label y) := Quotient.exact hlabel
  exact Quotient.sound hrel

theorem labelBlock_surjective {n w : ℕ} {label : Fin n → Fin w}
    (hsurj : Function.Surjective label) (τ : ER w) :
    Function.Surjective (labelBlock label τ) := fun q ↦
  Quotient.inductionOn q fun i ↦
    ⟨Quotient.mk _ (Function.surjInv hsurj i), by
      rw [labelBlock_mk, Function.surjInv_eq hsurj i]⟩

/-- **Pulling back commutes with merging.** -/
theorem comap_merge_labelBlock {n w : ℕ} (label : Fin n → Fin w) (τ : ER w)
    {C D : Quotient (Setoid.comap label τ)} (hCD : C ≠ D) :
    Setoid.comap label (merge τ (labelBlock label τ C) (labelBlock label τ D))
      = merge (Setoid.comap label τ) C D := by
  have hinj := labelBlock_injective label τ
  have hne : labelBlock label τ C ≠ labelBlock label τ D := fun h ↦ hCD (hinj h)
  refine Setoid.ext fun x y ↦ ?_
  show mergeMap τ (labelBlock label τ C) (labelBlock label τ D) (Quotient.mk τ (label x))
      = mergeMap τ (labelBlock label τ C) (labelBlock label τ D) (Quotient.mk τ (label y))
    ↔ mergeMap (Setoid.comap label τ) C D (Quotient.mk _ x)
      = mergeMap (Setoid.comap label τ) C D (Quotient.mk _ y)
  rw [mergeMap_eq_iff τ hne, mergeMap_eq_iff _ hCD, ← labelBlock_mk label τ x,
    ← labelBlock_mk label τ y]
  simp only [hinj.eq_iff]

/-! ### Masses on pull-backs -/

/-- **The masses of the individuals, pushed to the labels.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum over a fiber. -/
def pushMass {n w : ℕ} (label : Fin n → Fin w) (mass : Fin n → ℝ) (i : Fin w) : ℝ :=
  ∑ x ∈ univ.filter (fun x ↦ label x = i), mass x

/-- Unit masses push to the fiber proportions. -/
theorem pushMass_unitMass {n w : ℕ} (label : Fin n → Fin w) :
    pushMass label (unitMass n) = fiberProportion label := by
  funext i
  simp only [pushMass, unitMass, fiberProportion, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The mass of a class of a pull-back is the pushed mass of its label class.** -/
theorem blockMass_comap {n w : ℕ} (label : Fin n → Fin w) (mass : Fin n → ℝ) (τ : ER w)
    (C : Quotient (Setoid.comap label τ)) :
    blockMass mass (Setoid.comap label τ) C
      = blockMass (pushMass label mass) τ (labelBlock label τ C) := by
  have hS : univ.filter (fun x ↦ Quotient.mk (Setoid.comap label τ) x = C)
      = univ.filter (fun x ↦ Quotient.mk τ (label x) = labelBlock label τ C) := by
    refine Finset.filter_congr fun x _ ↦ ?_
    rw [← labelBlock_mk label τ x]
    exact (labelBlock_injective label τ).eq_iff.symm
  unfold blockMass pushMass
  rw [hS, ← Finset.sum_fiberwise_of_maps_to (g := label)
    (t := univ.filter fun i ↦ Quotient.mk τ i = labelBlock label τ C)
    (fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun x _ ↦ ?_) fun _ _ ↦ rfl
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [h]
    exact (Finset.mem_filter.mp hi).2

/-- The total merge mass of a pull-back is that of the label partition with pushed masses. -/
theorem pairProductSum_blockMass_comap {n w : ℕ} {label : Fin n → Fin w}
    (hsurj : Function.Surjective label) (mass : Fin n → ℝ) (τ : ER w) :
    pairProductSum (blockMass mass (Setoid.comap label τ))
      = pairProductSum (blockMass (pushMass label mass) τ) := by
  have hbij : Function.Bijective (labelBlock label τ) :=
    ⟨labelBlock_injective label τ, labelBlock_surjective hsurj τ⟩
  have h1 := two_mul_pairProductSum (blockMass mass (Setoid.comap label τ))
  have h2 := two_mul_pairProductSum (blockMass (pushMass label mass) τ)
  have hs1 : ∑ C, blockMass mass (Setoid.comap label τ) C
      = ∑ E, blockMass (pushMass label mass) τ E := by
    simp only [blockMass_comap label mass τ]
    exact (Equiv.ofBijective _ hbij).sum_comp (blockMass (pushMass label mass) τ)
  have hs2 : ∑ C, blockMass mass (Setoid.comap label τ) C ^ 2
      = ∑ E, blockMass (pushMass label mass) τ E ^ 2 := by
    simp only [blockMass_comap label mass τ]
    exact (Equiv.ofBijective _ hbij).sum_comp fun E ↦ blockMass (pushMass label mass) τ E ^ 2
  rw [hs1, hs2] at h1
  linarith

/-! ### The kernel on pull-backs is the kernel on the labels -/

/-- **The uniformized kernel of `Z` on the individuals, on pull-backs, is the uniformized kernel of
`Z` on the labels with the pushed masses.** -/
theorem massStep_comap {n w : ℕ} {label : Fin n → Fin w} (hsurj : Function.Surjective label)
    (mass : Fin n → ℝ) (τ τ' : ER w) :
    massStep mass (Setoid.comap label τ) (Setoid.comap label τ')
      = massStep (pushMass label mass) τ τ' := by
  have hinj := comap_label_injective hsurj
  have hhold : (if Setoid.comap label τ' = Setoid.comap label τ then
        1 - pairProductSum (blockMass mass (Setoid.comap label τ)) else 0)
      = if τ' = τ then 1 - pairProductSum (blockMass (pushMass label mass) τ) else 0 := by
    rw [pairProductSum_blockMass_comap hsurj mass τ]
    by_cases h : τ' = τ
    · rw [if_pos (congrArg (Setoid.comap label) h), if_pos h]
    · rw [if_neg fun h' ↦ h (hinj h'), if_neg h]
  unfold massStep
  rw [hhold]
  congr 1
  by_cases hmerge : ∃ C D : Quotient (Setoid.comap label τ),
      C ≠ D ∧ Setoid.comap label τ' = merge (Setoid.comap label τ) C D
  · obtain ⟨C, D, hCD, hτ'⟩ := hmerge
    have hne : labelBlock label τ C ≠ labelBlock label τ D :=
      fun h ↦ hCD (labelBlock_injective label τ h)
    have hτ'' : τ' = merge τ (labelBlock label τ C) (labelBlock label τ D) :=
      hinj (hτ'.trans (comap_merge_labelBlock label τ hCD).symm)
    rw [hτ', filter_mergePair_merge _ hCD, hτ'', filter_mergePair_merge _ hne,
      Finset.sum_singleton, Finset.sum_singleton, Finset.prod_pair hCD, Finset.prod_pair hne,
      blockMass_comap label mass τ C, blockMass_comap label mass τ D]
  · have hleft : (univ.powersetCard 2).filter
        (fun t ↦ mergePair (Setoid.comap label τ) t = Setoid.comap label τ') = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun t ht heq ↦ hmerge ?_
      have hcard := Finset.mem_powersetCard_univ.mp ht
      rw [mergePair, dif_pos hcard] at heq
      exact ⟨_, _, (pair_spec hcard).1, heq.symm⟩
    have hright : (univ.powersetCard 2).filter (fun t ↦ mergePair τ t = τ') = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun t ht heq ↦ hmerge ?_
      have hcard := Finset.mem_powersetCard_univ.mp ht
      rw [mergePair, dif_pos hcard] at heq
      obtain ⟨C, hC⟩ := labelBlock_surjective hsurj τ (pairFst hcard)
      obtain ⟨D, hD⟩ := labelBlock_surjective hsurj τ (pairSnd hcard)
      have hCD : C ≠ D := fun h ↦ (pair_spec hcard).1 (by rw [← hC, ← hD, h])
      refine ⟨C, D, hCD, ?_⟩
      rw [← heq, ← hC, ← hD]
      exact comap_merge_labelBlock label τ hCD
    rw [hleft, hright, Finset.sum_empty, Finset.sum_empty]

/-! ### Path laws on the labels -/

/-- **`Z_{p^(n)}` on the fiber labels**: the skeleton path law of the uniformized multiplicative
coalescent on the partitions of the `w` labels, with the panel's fiber proportions, from the
singletons.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite path law. -/
def labelMultiplicativePathLaw {n w : ℕ} (label : Fin n → Fin w) (m : ℕ)
    (y : Fin (m + 1) → ER w) : ℝ :=
  skeletonPathWeight (massStep (fiberProportion label)) (fun τ ↦ if τ = ⊥ then 1 else 0) m y

/-- The interface of a labelling is the pull-back of the singletons of the labels. -/
theorem graphKer_labelInterface_eq_comap_bot {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) :
    graphKer (labelInterface label hsurj) = Setoid.comap label ⊥ := by
  rw [graphKer_labelInterface]
  exact Setoid.ext fun _ _ ↦ Iff.rfl

/-- **The path law of `Z_{p^(n)}` on the individuals, on pulled-back paths, is its path law on the
labels.** -/
theorem multiplicativePathLaw_comap {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) (m : ℕ) (y : Fin (m + 1) → ER w) :
    multiplicativePathLaw (labelInterface label hsurj) m (fun k ↦ Setoid.comap label (y k))
      = labelMultiplicativePathLaw label m y := by
  have hker := graphKer_labelInterface_eq_comap_bot label hsurj
  unfold multiplicativePathLaw labelMultiplicativePathLaw skeletonPathWeight
  congr 1
  · dsimp only
    by_cases h : y 0 = ⊥
    · rw [if_pos h, if_pos (by rw [h, hker])]
    · rw [if_neg h, if_neg fun h' ↦ h (comap_label_injective hsurj (h'.trans hker))]
  · refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [multiplicativeStep_eq_massStep, massStep_comap hsurj, pushMass_unitMass]

/-- **The report's path, read on the labels**: the probability that the report of the uniformized
genealogy follows the pull-back of a path of label partitions.  The report lies above the
interface, so every report path is such a pull-back.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite path law, reindexed. -/
def labelReportPathLaw {n w : ℕ} (label : Fin n → Fin w) (hsurj : Function.Surjective label)
    (m : ℕ) (y : Fin (m + 1) → ER w) : ℝ :=
  reportPathLaw (labelInterface label hsurj) m fun k ↦ Setoid.comap label (y k)

/-- The label-level differences of the two path laws are a sub-sum of the individual-level ones. -/
theorem sum_abs_labelPathLaw_sub_le {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) (m : ℕ) :
    ∑ y : Fin (m + 1) → ER w,
        |labelReportPathLaw label hsurj m y - labelMultiplicativePathLaw label m y|
      ≤ ∑ y : Fin (m + 1) → ER n,
        |reportPathLaw (labelInterface label hsurj) m y
          - multiplicativePathLaw (labelInterface label hsurj) m y| := by
  have hemb : Function.Injective
      (fun y : Fin (m + 1) → ER w ↦ fun k ↦ Setoid.comap label (y k)) := by
    intro y₁ y₂ h
    funext k
    exact comap_label_injective hsurj (congrFun h k)
  calc ∑ y : Fin (m + 1) → ER w,
        |labelReportPathLaw label hsurj m y - labelMultiplicativePathLaw label m y|
      = ∑ y ∈ (univ : Finset (Fin (m + 1) → ER w)).map ⟨_, hemb⟩,
          |reportPathLaw (labelInterface label hsurj) m y
            - multiplicativePathLaw (labelInterface label hsurj) m y| := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        simp only [Function.Embedding.coeFn_mk, labelReportPathLaw, multiplicativePathLaw_comap]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ ↦ abs_nonneg _

/-- **(F1) on the fiber labels, after `m` rings.**

Assumes: `0 < n`. -/
theorem label_report_multiplicative_pathTotalVariation_le {n w : ℕ} (hn : 0 < n)
    (label : Fin n → Fin w) (hsurj : Function.Surjective label) (m : ℕ) :
    1 / 2 * ∑ y : Fin (m + 1) → ER w,
        |labelReportPathLaw label hsurj m y - labelMultiplicativePathLaw label m y|
      ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n) :=
  (mul_le_mul_of_nonneg_left (sum_abs_labelPathLaw_sub_le label hsurj m) (by norm_num)).trans
    (report_multiplicative_pathTotalVariation_le hn (labelInterface label hsurj) m)

/-- **(F1) on the fiber labels**: at the rings of a Poisson clock of mean `U` in scaled time, the
report read on the labels and `Z_{p^(n)}` on the labels have skeleton total variation at most
`min {1, U²/(4n)}`.

Assumes: `0 < n`. -/
theorem label_report_multiplicative_poissonTotalVariation_le {n w : ℕ} (hn : 0 < n)
    (label : Fin n → Fin w) (hsurj : Function.Surjective label) (U : NNReal) :
    poissonMixture U (fun m ↦ 1 / 2 * ∑ y : Fin (m + 1) → ER w,
        |labelReportPathLaw label hsurj m y - labelMultiplicativePathLaw label m y|)
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n)) :=
  poissonMixture_le_min (by exact_mod_cast hn)
    (fun m ↦ mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    (fun m ↦ (mul_le_mul_of_nonneg_left (sum_abs_labelPathLaw_sub_le label hsurj m)
      (by norm_num)).trans
        (report_multiplicative_pathTotalVariation_le_one hn (labelInterface label hsurj) m))
    (label_report_multiplicative_pathTotalVariation_le hn label hsurj)

end

end Descent.Pangenome.GraphCoalescent
