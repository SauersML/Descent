/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralEpochGenotypeLaw
import Descent.Portability.ExponentialPoissonRace
import Descent.Portability.AncestralMutationTransfer

assert_below Descent.Decision Descent.Program

/-!
Finite independent-coordinate kernels preserve the complete genome law when
composed across a shared interval boundary. Independence is conditional on
the same genealogy and duration; averaging that duration is a later step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.WholeGenomeMutationSemigroup

open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue
open StoppedGenotypeLaw AncestralEpochGenotypeLaw InterleavedMutationExponential
open Coalescent.FiniteGenomeAncestry
open scoped NNReal

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

noncomputable def independentLaw (laws : I → FiniteReportLaw S) :
    FiniteReportLaw (I → S) where
  mass := fun output ↦ ∏ index, (laws index).mass (output index)
  mass_nonneg := fun output ↦ Finset.prod_nonneg (fun index _ ↦
    (laws index).mass_nonneg (output index))
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

variable {T : Type*} [Fintype T]

theorem independent_bind (laws : I → FiniteReportLaw S)
    (kernels : I → S → FiniteReportLaw T) :
    (independentLaw laws).bind (fun input ↦
      independentLaw (fun index ↦ kernels index (input index))) =
        independentLaw (fun index ↦ (laws index).bind (kernels index)) := by
  apply FiniteReportLaw.ext
  intro target
  change (∑ input : I → S, (∏ index, (laws index).mass (input index)) *
    ∏ index, (kernels index (input index)).mass (target index)) =
      ∏ index, ∑ value, (laws index).mass value * (kernels index value).mass (target index)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index value ↦
    (laws index).mass value * (kernels index value).mass (target index))).symm

theorem independent_pointMass (source : I → S) :
    independentLaw (fun index ↦ pointMass (source index)) = pointMass source := by
  classical
  apply FiniteReportLaw.ext
  intro target
  by_cases h : target = source
  · subst target
    simp [independentLaw, pointMass]
  · have hex : ∃ index, target index ≠ source index := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨index, hindex⟩ := hex
    have hp : (∏ i, (if target i = source i then 1 else 0 : ℝ)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg hindex)
    simpa [independentLaw, pointMass, h] using hp

theorem independent_pushforward (laws : I → FiniteReportLaw S) (maps : I → S → T) :
    (independentLaw laws).pushforward (fun input index ↦ maps index (input index)) =
      independentLaw (fun index ↦ (laws index).pushforward (maps index)) := by
  change (independentLaw laws).bind (fun input ↦ pointMass (fun index ↦ maps index (input index))) =
    independentLaw (fun index ↦ (laws index).bind (fun input ↦ pointMass (maps index input)))
  have hpoint (input : I → S) : pointMass (fun index ↦ maps index (input index)) =
      independentLaw (fun index ↦ pointMass (maps index (input index))) :=
    (independent_pointMass _).symm
  simp_rw [hpoint]
  exact independent_bind laws (fun index input ↦ pointMass (maps index input))

variable {D L n : ℕ}

theorem stateInterval_compose (state : State D L n) (locus : Fin L) (rate : ℝ≥0)
    (first second : ℝ≥0) (source : SiteState n) :
    (stateIntervalLaw state locus rate first source).bind
        (stateIntervalLaw state locus rate second) =
      stateIntervalLaw state locus rate ((first + second : ℝ≥0) : ℝ) source := by
  change (stateIntervalLaw state locus rate first source).bind
    (fun output ↦ stateIntervalLaw state locus rate second output) = _
  simpa only [stateIntervalLaw, Real.toNNReal_coe, mul_comm] using
    interval_compose (intervalTemplates state locus) (fun _ ↦ rate) first second source

/-- Exact full-genome semigroup law before averaging the shared duration. -/
theorem intervalGenome_compose (state : State D L n) (rate : ℝ≥0)
    (first second : ℝ≥0) (source : WholeGenome L n) :
    (intervalGenomeKernel state rate first source).bind
        (intervalGenomeKernel state rate second) =
      intervalGenomeKernel state rate ((first + second : ℝ≥0) : ℝ) source := by
  change (independentLaw (fun locus ↦ stateIntervalLaw state locus rate first
    (source locus))).bind (fun input ↦ independentLaw (fun locus ↦
      stateIntervalLaw state locus rate second (input locus))) =
    independentLaw (fun locus ↦ stateIntervalLaw state locus rate
      ((first + second : ℝ≥0) : ℝ) (source locus))
  rw [independent_bind]
  congr 1
  funext locus
  exact stateInterval_compose state locus rate first second (source locus)

/-- The common-root product boundary is exactly the root law used by the
combined ancestry/mutation transfer operator. -/
theorem root_product_eq_transfer :
    independentLaw (fun _ : Fin L ↦ (rootSiteLaw : FiniteReportLaw (SiteState n))) =
      AncestralMutationTransfer.rootGenomeLaw := by
  unfold rootSiteLaw AncestralMutationTransfer.rootGenomeLaw
  exact (independent_pushforward (fun _ ↦ rootLaw) (fun _ ↦ initialState)).symm

end Descent.Portability.WholeGenomeMutationSemigroup
