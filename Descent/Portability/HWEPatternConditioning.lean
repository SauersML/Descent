/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEHomozygoteConditioning

assert_below Descent.Decision Descent.Program

/-!
Conditioning the actual square-biased genotype law on any specified set of
heterozygous loci leaves independent fair signs at the remaining loci. The
unnormalized identity also covers zero-probability patterns without dividing by
zero. It is the finite-experiment input for higher heterozygosity layers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEPatternConditioning

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHeterozygosityLaw HWEHomozygoteConditioning
open BalancedHWEWeakLimit

variable {ι : Type*} [DecidableEq ι]

/-- Genotypes with exactly the specified heterozygous loci and free homozygous signs. -/
def patternVector (s : Finset ι) (b : {i // i ∉ s} → Bool) : ι → DiploidGenotype :=
  fun i ↦ if hi : i ∈ s then .het else homozygote (b ⟨i, hi⟩)

/-- A pattern specifies the entire heterozygous set, not just its size. -/
def HasPattern (s : Finset ι) (x : ι → DiploidGenotype) : Prop :=
  ∀ i, x i = .het ↔ i ∈ s

/-- Neither homozygous state is heterozygous. -/
theorem homozygote_ne_het (b : Bool) : homozygote b ≠ (.het : DiploidGenotype) := by
  cases b <;> simp [homozygote]

/-- Free signs encode distinct genotype vectors within a fixed pattern. -/
theorem patternVector_injective (s : Finset ι) : Function.Injective (patternVector s) := by
  intro a b h
  funext i
  apply homozygote_injective
  have hh := congrFun h i.val
  simpa only [patternVector, dif_neg i.property] using hh

/-- Every encoded vector has exactly the specified pattern. -/
theorem hasPattern_vector (s : Finset ι) (b : {i // i ∉ s} → Bool) :
    HasPattern s (patternVector s b) := by
  intro i
  by_cases hi : i ∈ s
  · simp [patternVector, hi]
  · simp only [patternVector, hi, iff_false]
    exact homozygote_ne_het _

/-- Every genotype vector in the pattern is obtained from a unique fair-sign coordinate. -/
theorem range_patternVector (s : Finset ι) (x : ι → DiploidGenotype) :
    x ∈ Set.range (patternVector s) ↔ HasPattern s x := by
  constructor
  · rintro ⟨b, rfl⟩
    exact hasPattern_vector s b
  · intro hx
    refine ⟨fun i ↦ encode (x i.val), ?_⟩
    funext i
    by_cases hi : i ∈ s
    · simpa only [patternVector, dif_pos hi] using ((hx i).mpr hi).symm
    · have hn : x i ≠ .het := fun hh ↦ hi ((hx i).mp hh)
      cases hxi : x i <;> simp_all [patternVector, homozygote, encode]

variable [Fintype ι]

instance (s : Finset ι) (x : ι → DiploidGenotype) : Decidable (HasPattern s x) :=
  inferInstanceAs (Decidable (∀ i, x i = .het ↔ i ∈ s))

/-- The count of an encoded pattern is its exact finite cardinality. -/
theorem count_patternVector (s : Finset ι) (b : {i // i ∉ s} → Bool) :
    count (patternVector s b) = (s.card : ℝ) := by
  have he (i : ι) : heterozygote (patternVector s b i) = if i ∈ s then 1 else 0 := by
    by_cases hi : i ∈ s
    · simp [patternVector, hi, heterozygote]
    · simp only [patternVector, dif_neg hi, if_neg hi]
      cases b ⟨i, hi⟩ <;> rfl
  simp only [count, he]
  simp

/-- Exact probability of a heterozygosity pattern under the square-biased HWE law. -/
noncomputable def patternMass (h : ι → HardyWeinbergModel) (s : Finset ι) : ℝ :=
  (∏ i : {i // i ∈ s}, probability (h i.val)) * ∏ i : {i // i ∉ s}, (1 - probability (h i.val))

/-- Each remaining homozygote has one half of the nonheterozygous mass. -/
theorem homozygote_factor (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (b : Bool) :
    (squareBiasedLocus h h0 h1).mass (homozygote b) =
      (1 - probability h) * signLaw.mass b := by
  rw [squareBiasedLocus_mass]
  cases b <;> simp only [homozygote, probability, signLaw] <;> ring

/-- The original genotype probability factors into pattern mass and fair-sign probability. -/
theorem pattern_vector_mass (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (s : Finset ι) (b : {i // i ∉ s} → Bool) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).mass
      (patternVector s b) =
        patternMass h s * (independentLaw (fun _ : {i // i ∉ s} ↦ signLaw)).mass b := by
  change (∏ i, (squareBiasedLocus (h i) (h0 i) (h1 i)).mass (patternVector s b i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i ↦ i ∈ s)]
  have hs (i : {i // i ∈ s}) : (squareBiasedLocus (h i.val) (h0 i.val) (h1 i.val)).mass
      (patternVector s b i.val) = probability (h i.val) := by
    simp [patternVector, i.property, squareBiasedLocus_mass, probability]
  have hc (i : {i // i ∉ s}) :
      (squareBiasedLocus (h i.val) (h0 i.val) (h1 i.val)).mass (patternVector s b i.val) =
        (1 - probability (h i.val)) * signLaw.mass (b i) := by
    simp only [patternVector, dif_neg i.property, homozygote_factor]
  simp only [hs, hc, Finset.prod_mul_distrib, patternMass, independentLaw]
  rw [mul_assoc]
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i _
    rfl

/-- Exact conditioning identity for every real statistic of the original genotype vector. -/
theorem pattern_expectation (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1)
    (s : Finset ι) (f : (ι → DiploidGenotype) → ℝ) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ if HasPattern s x then f x else 0) =
        patternMass h s * (independentLaw (fun _ : {i // i ∉ s} ↦ signLaw)).expectation
          (fun b ↦ f (patternVector s b)) := by
  classical
  simp only [FiniteReportLaw.expectation, Finset.mul_sum]
  symm
  apply Fintype.sum_of_injective (patternVector s) (patternVector_injective s)
  · intro x hx
    have hc : ¬HasPattern s x := fun hc ↦ hx ((range_patternVector s x).mpr hc)
    simp [hc]
  · intro b
    rw [if_pos (hasPattern_vector s b), pattern_vector_mass]
    ring

end Descent.Portability.HWEPatternConditioning
