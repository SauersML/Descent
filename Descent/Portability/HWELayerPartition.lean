/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEPatternConditioning
import Mathlib.Data.Finset.Powerset

assert_below Descent.Decision Descent.Program

/-!
Exact decomposition of the original square-biased HWE experiment into its
heterozygosity patterns and count layers. For homogeneous frequencies the count
probabilities are the actual binomial probabilities, derived by counting subsets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWELayerPartition

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHeterozygosityLaw HWEPatternConditioning
open BalancedHWEWeakLimit FiniteIndependentMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The heterozygous set observed in a realized genotype vector. -/
def actualPattern (x : ι → DiploidGenotype) : Finset ι :=
  Finset.univ.filter (fun i ↦ x i = .het)

omit [DecidableEq ι] in
/-- Every genotype vector belongs to exactly one pattern. -/
theorem hasPattern_iff_eq (s : Finset ι) (x : ι → DiploidGenotype) :
    HasPattern s x ↔ s = actualPattern x := by
  constructor
  · intro hx
    ext i
    simpa only [actualPattern, Finset.mem_filter, Finset.mem_univ, true_and] using (hx i).symm
  · rintro rfl
    intro i
    simp [actualPattern]

/-- The real-valued count agrees exactly with the finite pattern cardinality. -/
theorem count_actualPattern (x : ι → DiploidGenotype) :
    count x = ((actualPattern x).card : ℝ) := by
  obtain ⟨b, hb⟩ := (range_patternVector (actualPattern x) x).mpr
    ((hasPattern_iff_eq _ _).mpr rfl)
  calc
    count x = count (patternVector (actualPattern x) b) := congrArg count hb.symm
    _ = _ := count_patternVector _ b

/-- Every finite genotype statistic decomposes exactly over the disjoint pattern events. -/
theorem partition_expectation (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (f : (ι → DiploidGenotype) → ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation f =
      ∑ s : Finset ι, patternMass h s *
        (independentLaw (fun _ : {i // i ∉ s} ↦ signLaw)).expectation
          (fun b ↦ f (patternVector s b)) := by
  classical
  have he (x : ι → DiploidGenotype) :
      (∑ s : Finset ι, if HasPattern s x then f x else 0) = f x := by
    simp only [hasPattern_iff_eq]
    simp
  calc
    _ = ∑ s : Finset ι,
        (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
          (fun x ↦ if HasPattern s x then f x else 0) := by
      simp only [FiniteReportLaw.expectation]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, he]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact pattern_expectation h h0 h1 s f

/-- An exact count layer is the sum of its pattern laws, for any real statistic. -/
theorem layer_expectation (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (r : ℕ) (f : (ι → DiploidGenotype) → ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = (r : ℝ) then f x else 0) =
        ∑ s : Finset ι, if s.card = r then patternMass h s *
          (independentLaw (fun _ : {i // i ∉ s} ↦ signLaw)).expectation
            (fun b ↦ f (patternVector s b)) else 0 := by
  rw [partition_expectation]
  apply Finset.sum_congr rfl
  intro s _
  simp only [count_patternVector, Nat.cast_inj]
  by_cases hs : s.card = r
  · simp only [hs, if_true]
  · simp [hs, FiniteReportLaw.expectation]

/-- Under homogeneous frequencies the pattern mass depends only on its count. -/
theorem homogeneous_patternMass (h : HardyWeinbergModel) (s : Finset ι) :
    patternMass (fun _ : ι ↦ h) s = probability h ^ s.card *
      (1 - probability h) ^ (Fintype.card ι - s.card) := by
  simp [patternMass, Fintype.card_subtype_compl]

/-- The actual probability of a fixed count is the binomial mass. -/
theorem homogeneous_count_mass (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (r : ℕ) :
    (independentLaw (fun _ : ι ↦ squareBiasedLocus h h0 h1)).expectation
      (fun x ↦ if count x = (r : ℝ) then 1 else 0) =
        ((Fintype.card ι).choose r : ℝ) * probability h ^ r *
          (1 - probability h) ^ (Fintype.card ι - r) := by
  rw [layer_expectation (fun _ : ι ↦ h) (fun _ ↦ h0) (fun _ ↦ h1) r (fun _ ↦ 1)]
  simp only [expectation_const, mul_one, homogeneous_patternMass]
  have he : (Finset.univ.filter (fun s : Finset ι ↦ s.card = r)) =
      Finset.univ.powersetCard r := by
    ext s
    simp
  rw [← Finset.sum_filter, he]
  calc
    _ = ∑ _s ∈ Finset.univ.powersetCard r,
        probability h ^ r * (1 - probability h) ^ (Fintype.card ι - r) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]
    _ = _ := by simp [Finset.card_powersetCard, mul_assoc]

end Descent.Portability.HWELayerPartition
