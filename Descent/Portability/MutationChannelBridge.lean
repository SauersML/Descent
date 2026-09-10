/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.WholeGenomeMutationRace
import Descent.Portability.SignedTransferIdentification

assert_below Descent.Decision Descent.Program

/-!
The genealogy compiler and the marked transfer operator enumerate the same
locus-lineage mutation clocks. Their whole-genome generators coincide.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MutationChannelBridge

open FiniteReportLaw WholeGenomeMutationSemigroup WholeGenomeMutationRace
open FiniteProductExponential InterleavedMutationExponential InterleavedMutationMeasurability
open Coalescent.FiniteGenomeAncestry AncestralBranchExposure AncestralGenealogyLaw
open GenealogyGenotypeLaw OrderedMutationCatalogue StoppedGenotypeLaw
open AncestralMutationTransfer
open scoped NNReal

variable {D L n : ℕ}

noncomputable def lineageBranch (lineage : Lineage D L n) (locus : Fin L)
    (exposure : ℝ≥0) (h : (locusDescendants lineage.2 locus).Nonempty) : Branch n :=
  { descendants := locusDescendants lineage.2 locus
    representative := (locusDescendants lineage.2 locus).min' h
    representative_mem := Finset.min'_mem _ h
    exposure := exposure }

private theorem compiler_sum (lineages : List (Lineage D L n)) (locus : Fin L)
    (exposure : ℝ≥0) (f : Branch n → ℝ) :
    ((intervalBranchesAux locus exposure lineages).map f).sum =
      (lineages.map (fun lineage ↦ if h : (locusDescendants lineage.2 locus).Nonempty
        then f (lineageBranch lineage locus exposure h) else 0)).sum := by
  induction lineages with
  | nil => rfl
  | cons lineage rest ih =>
      by_cases h : (locusDescendants lineage.2 locus).Nonempty
      · simp [intervalBranchesAux, h, lineageBranch, ih]
      · simp [intervalBranchesAux, h, ih]

theorem template_sum (state : State D L n) (locus : Fin L) (f : Branch n → ℝ) :
    (∑ index, f (intervalTemplates state locus index)) =
      ∑ lineage ∈ state.val, if h : (locusDescendants lineage.2 locus).Nonempty
        then f (lineageBranch lineage locus 0 h) else 0 := by
  classical
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ (intervalBranches state locus 0).get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get, intervalBranches, compiler_sum,
    Finset.sum_map_toList]

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

theorem coordinateKernel_eq_pushforward (index : I) (kernel : S → FiniteReportLaw S)
    (source : I → S) :
    coordinateKernel index kernel source =
      (kernel (source index)).pushforward (fun value ↦ Function.update source index value) := by
  classical
  apply FiniteReportLaw.ext
  intro target
  rw [coordinateKernel_mass]
  by_cases h : ∀ other, other ≠ index → target other = source other
  · have hp : (∏ other ∈ Finset.univ.erase index,
        (1 : Matrix S S ℝ) (source other) (target other)) = 1 := by
      apply Finset.prod_eq_one
      intro other ho
      simp [Matrix.one_apply, h other (Finset.mem_erase.mp ho).1]
    rw [hp, one_mul]
    have heq (value : S) : target = Function.update source index value ↔ value = target index := by
      constructor
      · intro ht
        simpa using (congrFun ht index).symm
      · intro hv
        subst value
        funext other
        by_cases ho : other = index
        · subst other; simp
        · simp [Function.update_of_ne ho, h other ho]
    simp [pushforward, FiniteReportLaw.bind, pointMass, heq]
  · push_neg at h
    obtain ⟨other, hother, hne⟩ := h
    have hp : (∏ coordinate ∈ Finset.univ.erase index,
        (1 : Matrix S S ℝ) (source coordinate) (target coordinate)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
      simp [Ne.symm hne]
    rw [hp, zero_mul]
    have heq (value : S) : target ≠ Function.update source index value := by
      intro ht
      have hh := congrFun ht other
      rw [Function.update_of_ne hother] at hh
      exact hne hh
    simp [pushforward, FiniteReportLaw.bind, pointMass, heq]

theorem channel_sum (state : State D L n) (g : Lineage D L n → Fin L → ℝ) :
    (∑ mark : MutationChannel state, g mark.val.1 mark.val.2) =
      ∑ locus, ∑ lineage ∈ state.val,
        if (locusDescendants lineage.2 locus).Nonempty then g lineage locus else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun pair : Lineage D L n × Fin L ↦
    pair.1 ∈ state.val ∧ (locusDescendants pair.1.2 pair.2).Nonempty))
      (by simp) (fun pair ↦ g pair.1 pair.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro locus _
  simp_rw [ite_and]
  rw [← Finset.sum_filter]
  congr 1
  ext lineage
  simp

private theorem coordinate_identity (index : I) (source target : I → S) :
    (∏ other ∈ Finset.univ.erase index, (1 : Matrix S S ℝ) (source other) (target other)) *
        (1 : Matrix S S ℝ) (source index) (target index) =
      (pointMass source).mass target := by
  rw [Finset.prod_erase_mul _ _ (Finset.mem_univ index)]
  have h := congrArg (fun matrix : Matrix (I → S) (I → S) ℝ ↦ matrix source target)
    (productMatrix_one (I := I) (S := S))
  simpa [pointMass, Matrix.one_apply, eq_comm] using h

theorem generator_template_sum (state : State D L n) (rate : ℝ≥0)
    (source target : WholeGenome L n) :
    genomeGenerator state rate source target =
      ∑ locus, ∑ index, (rate : ℝ) *
        ((coordinateKernel locus
          (OrderedMutationCatalogue.mutationKernel (intervalTemplates state locus index))
            source).mass target - (pointMass source).mass target) := by
  classical
  unfold genomeGenerator productGenerator physicalGenerator
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    replaceExposure, kernelMatrix, Finset.mul_sum, coordinateKernel_mass]
  apply Finset.sum_congr rfl
  intro locus _
  apply Finset.sum_congr rfl
  intro index _
  rw [← coordinate_identity locus source target]
  change (∏ other ∈ Finset.univ.erase locus,
      (1 : Matrix (SiteState n) (SiteState n) ℝ) (source other) (target other)) *
    ((rate : ℝ) * ((OrderedMutationCatalogue.mutationKernel
      (intervalTemplates state locus index) (source locus)).mass (target locus) -
        (1 : Matrix (SiteState n) (SiteState n) ℝ) (source locus) (target locus))) = _
  ring

/-- The compiled mutation semigroup has exactly the marked transfer generator. -/
theorem genomeGenerator_eq_channels (state : State D L n) (rate : ℝ≥0)
    (source target : WholeGenome L n) :
    genomeGenerator state rate source target =
      ∑ mark : MutationChannel state, (rate : ℝ) *
        ((AncestralMutationTransfer.mutationKernel mark source).mass target -
          (pointMass source).mass target) := by
  classical
  let g (lineage : Lineage D L n) (locus : Fin L) : ℝ :=
    if h : (locusDescendants lineage.2 locus).Nonempty then
      (rate : ℝ) * ((coordinateKernel locus
        (OrderedMutationCatalogue.mutationKernel (lineageBranch lineage locus 0 h))
          source).mass target - (pointMass source).mass target) else 0
  calc
    genomeGenerator state rate source target =
        ∑ locus, ∑ lineage ∈ state.val, g lineage locus := by
      rw [generator_template_sum]
      apply Finset.sum_congr rfl
      intro locus _
      exact template_sum state locus (fun branch ↦ (rate : ℝ) *
        ((coordinateKernel locus (OrderedMutationCatalogue.mutationKernel branch)
          source).mass target - (pointMass source).mass target))
    _ = ∑ mark : MutationChannel state, g mark.val.1 mark.val.2 := by
      rw [channel_sum]
      apply Finset.sum_congr rfl
      intro locus _
      apply Finset.sum_congr rfl
      intro lineage _
      by_cases h : (locusDescendants lineage.2 locus).Nonempty <;> simp [g, h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mark _
      dsimp only [g]
      rw [dif_pos mark.property.2, coordinateKernel_eq_pushforward]
      rfl

open AncestralEventLaw AncestralAbsorptionLaw AncestralMutationLimit

/-- The law constructed from actual shared ancestry waiting times is the
unique finite joint ancestry/mutation solution. -/
theorem stoppedGenome_eq_limit (rates : Rates D L) (rate : ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (state : State D L n) (hs : SampleComplete state) (hsupported : SupportedAt deme state) :
    stoppedGenomeLaw rates deme state hs hsupported hisolated rate =
      limitLaw rates (fun _ ↦ rate) deme state hs hsupported hisolated :=
  SignedTransferIdentification.stoppedGenome_eq_limit_of_generator rates rate
    (fun state source target ↦ genomeGenerator_eq_channels state rate source target)
      deme hisolated state hs hsupported

end Descent.Portability.MutationChannelBridge
