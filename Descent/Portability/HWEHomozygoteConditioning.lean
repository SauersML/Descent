/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHeterozygosityLimit
import Descent.Portability.HWELogCoordinates

assert_below Descent.Decision Descent.Program

/-!
The square-biased HWE block conditioned on zero heterozygotes is exactly a row
of independent fair homozygote signs. The normalization and equality hold for
every finite observable and are derived from the original genotype masses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHomozygoteConditioning

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHeterozygosityLaw HWEHeterozygosityLimit
open BalancedHWEWeakLimit

/-- Encode a fair sign as one of the two homozygous genotypes. -/
def homozygote : Bool → DiploidGenotype
  | false => .homRef
  | true => .homAlt

def encode : DiploidGenotype → Bool
  | .homRef => false
  | .het => false
  | .homAlt => true

theorem homozygote_injective : Function.Injective homozygote := by
  intro a b h
  cases a <;> cases b <;> simp_all [homozygote]

def homoVector {ι : Type*} (b : ι → Bool) : ι → DiploidGenotype :=
  fun i ↦ homozygote (b i)

theorem homoVector_injective {ι : Type*} : Function.Injective (homoVector (ι := ι)) := by
  intro a b h
  funext i
  exact homozygote_injective (congrFun h i)

theorem count_homoVector {ι : Type*} [Fintype ι] (b : ι → Bool) : count (homoVector b) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  change heterozygote (homozygote (b i)) = 0
  cases b i <;> rfl

/-- Exactly the zero-count genotype vectors are obtained from homozygous sign rows. -/
theorem range_homoVector {ι : Type*} [Fintype ι] (x : ι → DiploidGenotype) :
    x ∈ Set.range homoVector ↔ count x = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact count_homoVector b
  · intro hx
    have hn (i : ι) : 0 ≤ heterozygote (x i) := by cases x i <;> norm_num [heterozygote]
    have hz : ∀ i, heterozygote (x i) = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hn i)).mp hx
      exact fun i ↦ hh i (Finset.mem_univ i)
    refine ⟨fun i ↦ encode (x i), ?_⟩
    funext i
    have hi := hz i
    cases hxi : x i <;> simp_all [homoVector, homozygote, encode, heterozygote]

noncomputable def zeroMass {ι : Type*} [Fintype ι] (h : ι → HardyWeinbergModel) : ℝ :=
  ∏ i, (1 - probability (h i))

/-- Valid allele frequencies make the conditioning event strictly positive. -/
theorem zeroMass_pos {ι : Type*} [Fintype ι] (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) : 0 < zeroMass h := by
  apply Finset.prod_pos
  intro i _
  have he : 1 - probability (h i) = 4 * (h i).altFreq * (1 - (h i).altFreq) := by
    unfold probability
    ring
  rw [he]
  exact mul_pos (mul_pos (by norm_num) (h0 i)) (sub_pos.mpr (h1 i))

/-- Every homozygous vector has its fair-sign probability times the event mass. -/
theorem homozygote_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (b : ι → Bool) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).mass (homoVector b) =
      zeroMass h * (independentLaw (fun _ : ι ↦ signLaw)).mass b := by
  simp only [independentLaw, zeroMass, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [squareBiasedLocus_mass]
  simp only [homoVector]
  cases b i <;> simp only [homozygote, signLaw, probability] <;> ring

/-- Exact unnormalized conditioning identity for every genotype statistic. -/
theorem zero_count_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (f : (ι → DiploidGenotype) → ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then f x else 0) =
      zeroMass h * (independentLaw (fun _ : ι ↦ signLaw)).expectation
        (fun b ↦ f (homoVector b)) := by
  classical
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]
  symm
  apply Fintype.sum_of_injective homoVector homoVector_injective
  · intro x hx
    have hc : count x ≠ 0 := fun hc ↦ hx ((range_homoVector x).mpr hc)
    simp [hc]
  · intro b
    rw [count_homoVector, if_pos rfl, homozygote_mass]
    ring

/-- The normalized conditional expectation is exactly that of independent fair signs. -/
theorem conditional_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (f : (ι → DiploidGenotype) → ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if count x = 0 then f x else 0) / zeroMass h =
      (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun b ↦ f (homoVector b)) := by
  rw [zero_count_expectation]
  exact mul_div_cancel_left₀ _ (zeroMass_pos h h0 h1).ne'

end Descent.Portability.HWEHomozygoteConditioning
