/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteProductExponential

assert_below Descent.Decision Descent.Program

/-!
One global proposal clock for every coordinate mutation kernel. The product
semigroup and this global clock have exactly the same generator, so averaging
a shared exponential ancestry wait yields a single whole-genome resolvent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.WholeGenomeMutationRace

open FiniteReportLaw WholeGenomeMutationSemigroup InterleavedMutationExponential
open FiniteProductExponential ExponentialPoissonRace MeasureTheory ProbabilityTheory
open scoped NNReal Matrix.Norms.Operator

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

noncomputable def coordinateKernel (index : I) (kernel : S → FiniteReportLaw S)
    (source : I → S) : FiniteReportLaw (I → S) :=
  independentLaw (fun coordinate ↦
    if coordinate = index then kernel (source coordinate) else pointMass (source coordinate))

theorem coordinateKernel_mass (index : I) (kernel : S → FiniteReportLaw S)
    (source target : I → S) :
    (coordinateKernel index kernel source).mass target =
      (∏ other ∈ Finset.univ.erase index, (1 : Matrix S S ℝ) (source other) (target other)) *
        (kernel (source index)).mass (target index) := by
  change (∏ coordinate, _) = _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ index)]
  congr 1
  · apply Finset.prod_congr rfl
    intro other hother
    have hn : other ≠ index := (Finset.mem_erase.mp hother).1
    simp [hn, pointMass, Matrix.one_apply, eq_comm]
  · simp

noncomputable def proposalRate (rates : I → ℝ≥0) : ℝ≥0 := 1 + ∑ index, rates index

omit [DecidableEq I] in
theorem proposalRate_pos (rates : I → ℝ≥0) : 0 < (proposalRate rates : ℝ) := by
  simp only [proposalRate, NNReal.coe_add, NNReal.coe_one]
  positivity

noncomputable def coordinateMarkLaw (rates : I → ℝ≥0) : FiniteReportLaw (Option I) where
  mass := fun mark ↦ match mark with
    | none => 1 / (proposalRate rates : ℝ)
    | some index => (rates index : ℝ) / (proposalRate rates : ℝ)
  mass_nonneg := by
    intro mark
    cases mark with
    | none => positivity
    | some index => positivity
  mass_sum := by
    rw [Fintype.sum_option, ← Finset.sum_div, ← add_div]
    have h : 1 + ∑ index, (rates index : ℝ) = (proposalRate rates : ℝ) := by
      simp [proposalRate]
    rw [h, div_self (ne_of_gt (proposalRate_pos rates))]

noncomputable def globalKernel (rates : I → ℝ≥0) (kernels : I → S → FiniteReportLaw S)
    (source : I → S) : FiniteReportLaw (I → S) :=
  (coordinateMarkLaw rates).bind (fun mark ↦ match mark with
    | none => pointMass source
    | some index => coordinateKernel index (kernels index) source)

omit [DecidableEq S] in
theorem globalKernel_mass (rates : I → ℝ≥0) (kernels : I → S → FiniteReportLaw S)
    (source target : I → S) :
    (globalKernel rates kernels source).mass target =
      ((pointMass source).mass target + ∑ index,
        (rates index : ℝ) * (coordinateKernel index (kernels index) source).mass target) /
          (proposalRate rates : ℝ) := by
  unfold globalKernel FiniteReportLaw.bind coordinateMarkLaw
  dsimp only
  rw [Fintype.sum_option]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, ← add_div, one_mul]

private theorem identity_factor (index : I) (source target : I → S) :
    (∏ other ∈ Finset.univ.erase index, (1 : Matrix S S ℝ) (source other) (target other)) *
        (1 : Matrix S S ℝ) (source index) (target index) =
      (1 : Matrix (I → S) (I → S) ℝ) source target := by
  rw [Finset.prod_erase_mul _ _ (Finset.mem_univ index)]
  exact congrArg (fun matrix : Matrix (I → S) (I → S) ℝ ↦ matrix source target)
    (productMatrix_one (I := I) (S := S))

/-- The global coordinate clock has precisely the product semigroup generator. -/
theorem global_generator (rates : I → ℝ≥0) (kernels : I → S → FiniteReportLaw S) :
    (proposalRate rates : ℝ) • (kernelMatrix (globalKernel rates kernels) - 1) =
      productGenerator (fun index ↦ (rates index : ℝ) • (kernelMatrix (kernels index) - 1)) := by
  ext source target
  change (proposalRate rates : ℝ) *
      ((globalKernel rates kernels source).mass target -
        (1 : Matrix (I → S) (I → S) ℝ) source target) = _
  rw [globalKernel_mass, mul_sub, mul_div_cancel₀ _ (ne_of_gt (proposalRate_pos rates))]
  have hpoint : (pointMass source).mass target =
      (1 : Matrix (I → S) (I → S) ℝ) source target := by simp [pointMass, Matrix.one_apply, eq_comm]
  rw [hpoint]
  simp only [proposalRate, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum,
    add_mul, one_mul, Finset.sum_mul, productGenerator, coordinateKernel_mass,
    Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, kernelMatrix]
  rw [show (1 : Matrix (I → S) (I → S) ℝ) source target +
      (∑ index, (rates index : ℝ) *
        ((∏ other ∈ Finset.univ.erase index,
          (1 : Matrix S S ℝ) (source other) (target other)) *
            (kernels index (source index)).mass (target index))) -
      ((1 : Matrix (I → S) (I → S) ℝ) source target +
        ∑ index, (rates index : ℝ) * (1 : Matrix (I → S) (I → S) ℝ) source target) =
      ∑ index, (rates index : ℝ) *
        ((∏ other ∈ Finset.univ.erase index,
          (1 : Matrix S S ℝ) (source other) (target other)) *
            (kernels index (source index)).mass (target index)) -
        ∑ index, (rates index : ℝ) * (1 : Matrix (I → S) (I → S) ℝ) source target by ring]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  rw [← identity_factor index source target]
  ring

/-- The common waiting time is integrated only after every coordinate has
been assembled into its joint finite transition law. -/
theorem product_expMeasure (rates : I → ℝ≥0) (kernels : I → S → FiniteReportLaw S)
    (ancestry : ℝ) (ha : 0 < ancestry) (source target : I → S) :
    (∫ time : ℝ, productEvolution
      (fun index ↦ (rates index : ℝ) • (kernelMatrix (kernels index) - 1))
        (Real.toNNReal time : ℝ) source target ∂expMeasure ancestry) =
      (raceKernelLaw ancestry ha (proposalRate rates) (globalKernel rates kernels) source).mass
        target := by
  simp_rw [productEvolution_exponential, ← global_generator, smul_smul]
  have hscale (time : ℝ) :
      (Real.toNNReal time : ℝ) * (proposalRate rates : ℝ) =
        ((proposalRate rates * Real.toNNReal time : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_mul, mul_comm]
  simp_rw [hscale]
  exact kernel_exponential_expMeasure ancestry ha (proposalRate rates)
    (globalKernel rates kernels) source target

open Coalescent.FiniteGenomeAncestry GenealogyGenotypeLaw OrderedMutationCatalogue
open StoppedGenotypeLaw AncestralEpochGenotypeLaw InterleavedMutationLaw
open InterleavedMutationMeasurability

variable {D L n : ℕ}

noncomputable def siteProposalRates (state : State D L n) (rate : ℝ≥0) : Fin L → ℝ≥0 :=
  fun locus ↦ proposalParameter (replaceExposure (intervalTemplates state locus) (fun _ ↦ rate))

noncomputable def siteProposalKernels (state : State D L n) (rate : ℝ≥0) :
    Fin L → SiteState n → FiniteReportLaw (SiteState n) :=
  fun locus ↦ intervalKernel (replaceExposure (intervalTemplates state locus) (fun _ ↦ rate))

noncomputable def genomeWaitLaw (ancestry : ℝ) (ha : 0 < ancestry)
    (state : State D L n) (rate : ℝ≥0) (source : WholeGenome L n) :
    FiniteReportLaw (WholeGenome L n) :=
  raceKernelLaw ancestry ha (proposalRate (siteProposalRates state rate))
    (globalKernel (siteProposalRates state rate) (siteProposalKernels state rate)) source

theorem intervalGenome_exponential_real (state : State D L n) (rate : ℝ≥0) (time : ℝ)
    (source target : WholeGenome L n) :
    (intervalGenomeKernel state rate time source).mass target =
      (NormedSpace.exp ℝ ((Real.toNNReal time : ℝ) • genomeGenerator state rate))
        source target := by
  have heq : intervalGenomeKernel state rate time source =
      intervalGenomeKernel state rate (Real.toNNReal time) source := by
    apply FiniteReportLaw.ext
    intro output
    simp only [intervalGenomeKernel, stateIntervalLaw, Real.toNNReal_coe]
  rw [heq]
  exact intervalGenome_exponential state rate (Real.toNNReal time) source target

/-- Complete joint mutation law during the actual exponential ancestry wait.
This identity integrates the common clock once for the whole genome. -/
theorem intervalGenome_expMeasure (ancestry : ℝ) (ha : 0 < ancestry)
    (state : State D L n) (rate : ℝ≥0) (source target : WholeGenome L n) :
    (∫ time : ℝ, (intervalGenomeKernel state rate time source).mass target
      ∂expMeasure ancestry) = (genomeWaitLaw ancestry ha state rate source).mass target := by
  have hpoint (time : ℝ) : (intervalGenomeKernel state rate time source).mass target =
      productEvolution (fun locus ↦ (siteProposalRates state rate locus : ℝ) •
        (kernelMatrix (siteProposalKernels state rate locus) - 1))
          (Real.toNNReal time : ℝ) source target := by
    rw [intervalGenome_exponential_real, productEvolution_exponential]
    have hg : genomeGenerator state rate = productGenerator (fun locus ↦
        (siteProposalRates state rate locus : ℝ) •
          (kernelMatrix (siteProposalKernels state rate locus) - 1)) := by
      unfold genomeGenerator siteProposalRates siteProposalKernels
      simp_rw [generator_matrix]
    rw [hg]
  simp_rw [hpoint]
  exact product_expMeasure (siteProposalRates state rate) (siteProposalKernels state rate)
    ancestry ha source target

/-- The shared-wait law obeys the exact global mutation first-step equation. -/
theorem genomeWait_first_step (ancestry : ℝ) (ha : 0 < ancestry)
    (state : State D L n) (rate : ℝ≥0) (source target : WholeGenome L n) :
    (genomeWaitLaw ancestry ha state rate source).mass target =
      (ancestry / (ancestry + (proposalRate (siteProposalRates state rate) : ℝ))) *
          (pointMass source).mass target +
        ((proposalRate (siteProposalRates state rate) : ℝ) /
          (ancestry + (proposalRate (siteProposalRates state rate) : ℝ))) *
          ((genomeWaitLaw ancestry ha state rate source).bind
            (globalKernel (siteProposalRates state rate) (siteProposalKernels state rate))).mass
              target :=
  raceKernel_first_step ancestry ha _ _ source target

end Descent.Portability.WholeGenomeMutationRace
