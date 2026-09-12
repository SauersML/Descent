/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralHistoryKernel
import Descent.Portability.LinearFundamentalMatrix

assert_below Descent.Decision Descent.Program

/-!
# The neutral dual propagator of a time-varying rate history

NOTE1 §4.2a: measurable time-dependent rate histories follow by the step-function approximation
of §2.4.  This module carries that approximation out for the partial-haplotype dual of NOTE1 (20),
for rate histories whose dual generator is continuous on the horizon.

`dualGeneratorPath rates capacity T` is the dual generator of the rate law at each time, with time
clamped into `[0, T]`, and `rateHistoryDualPropagator rates capacity T` is its fundamental matrix
at `T` (`LinearFundamentalMatrix.fundamentalMatrix`).  `sampledEpochs rates T h n` lists the `n`
epochs of duration `h` under the rate laws at the times `0, h, …, (n - 1) h`; their chronological
dual propagator is the sampled product of the generator path
(`historyPropagator_sampledEpochs`), so it converges to the propagator of the history
(`tendsto_historyPropagator_sampledEpochs`).

Realizability.  Every epoch keeps the realization body of the budget-moment feature invariant, by
NOTE1 Theorem 1 applied to the neutral microscopic approximation, so every chronological product
does (`historyPropagator_mulVec_mem_realizationBody`).  The body is closed, so the propagator of
the history keeps it invariant (`rateHistoryDualPropagator_mulVec_mem_realizationBody`), and at
every initial state there is a finitely supported law on frequency states whose configuration
moments are `U(T) H(x₀)` (`exists_rateHistoryLaw`).

The process law.  The neutral history kernels of the sampled epochs have expected configuration
moments converging to the coordinates of `U(T) H(x)`
(`tendsto_integral_momentPolynomial_sampledEpochs`), and their expected compiled panel reports
converge to the sum over genotypes of the readout times the seed coordinate of `U(T) H(x₀)`
(`tendsto_integral_panelReport_sampledEpochs`).

Scope.  The dual generator of the rate history is assumed continuous on the horizon.  Measurable
rates with merely integrable norm, NOTE1's full hypothesis, are not formalized, as in
`LinearFundamentalMatrix`.  The limit of the sampled history kernels as a Markov kernel of the
time-varying history is not constructed here; the limits are of expected moments and panel
reports.

## Empirical status

None.  The bodies here are products of matrix exponentials of supplied rates, their limits, and
membership in a closed convex set, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralRateHistoryRealization

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator PartialHaplotypeMicroscopicApproximation PartialHaplotypePanelLikelihood
  FiniteMixtureKernel RealizationBody KernelRealizationPreservation LinearFundamentalMatrix
  NeutralMicroscopicEulerLimit NeutralKernelPanelLikelihood NeutralHistoryKernel
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The generator path and its propagator -/

/-- The dual generator path of a rate history on the horizon `[0, T]`: the dual generator of the
rate law at each time, with time clamped into the horizon. -/
def dualGeneratorPath (rates : ℝ → NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (T : ℝ) :
    ℝ → Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fun t ↦ dualGenerator (rates (clampTime T t)) capacity

/-- A dual generator continuous on the horizon gives a continuous generator path on the line. -/
theorem continuous_dualGeneratorPath {rates : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T)) :
    Continuous (dualGeneratorPath rates capacity T) :=
  hcontinuous.comp_continuous (continuous_clampTime T) (clampTime_mem hT)

/-- A dual generator continuous on the compact horizon is bounded there. -/
theorem exists_dualGeneratorPath_bound {rates : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc 0 T, ‖dualGeneratorPath rates capacity T s‖ ≤ K := by
  obtain ⟨maximizer, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT)
    (continuous_dualGeneratorPath hT hcontinuous).norm.continuousOn
  exact ⟨‖dualGeneratorPath rates capacity T maximizer‖, norm_nonneg _,
    fun s hs ↦ isMaxOn_iff.mp hmax s hs⟩

/-- **The dual propagator of a rate history** over `[0, T]`: the fundamental matrix of its dual
generator path at the horizon. -/
def rateHistoryDualPropagator (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (T : ℝ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fundamentalMatrix (dualGeneratorPath rates capacity T) T T

/-! ## Sampled epochs -/

/-- The epochs of the left-endpoint sampling of a rate history at step `h`: `n` consecutive epochs
of duration `h` under the rate laws at the times `0, h, …, (n - 1) h`, clamped into the
horizon. -/
def sampledEpochs (rates : ℝ → NeutralRates Deme Locus Allele) (T : ℝ) (h : ℝ≥0) :
    ℕ → List (NeutralRates Deme Locus Allele × ℝ≥0)
  | 0 => []
  | k + 1 => sampledEpochs rates T h k ++ [(rates (clampTime T ((k : ℝ) * h)), h)]

/-- Appending an epoch at the end of a history multiplies its chronological propagator on the
left by the epoch exponential. -/
theorem historyPropagator_append (capacity : Locus → ℕ) :
    ∀ (epochs : List (NeutralRates Deme Locus Allele × ℝ))
      (epoch : NeutralRates Deme Locus Allele × ℝ),
      historyPropagator capacity (epochs ++ [epoch])
        = matrixExponential (dualGenerator epoch.1 capacity) epoch.2
          * historyPropagator capacity epochs
  | [], epoch => by
    simp only [List.nil_append, historyPropagator, Matrix.one_mul, Matrix.mul_one]
  | head :: rest, epoch => by
    rw [List.cons_append, historyPropagator, historyPropagator_append capacity rest epoch,
      historyPropagator, Matrix.mul_assoc]

/-- The chronological dual propagator of the sampled epochs is the sampled product of the dual
generator path. -/
theorem historyPropagator_sampledEpochs (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (T : ℝ) (h : ℝ≥0) :
    ∀ n : ℕ,
      historyPropagator capacity
          ((sampledEpochs rates T h n).map fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
        = sampledProduct (dualGeneratorPath rates capacity T) h n
  | 0 => rfl
  | k + 1 => by
    simp only [sampledEpochs, List.map_append, List.map_cons, List.map_nil]
    rw [historyPropagator_append, historyPropagator_sampledEpochs rates capacity T h k]
    rfl

/-- **The sampled epoch propagators converge to the propagator of the history.** -/
theorem tendsto_historyPropagator_sampledEpochs {rates : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T)) :
    Tendsto (fun n : ℕ ↦ historyPropagator capacity
        ((sampledEpochs rates T (T / n).toNNReal n).map fun epoch ↦ (epoch.1, (epoch.2 : ℝ))))
      atTop (𝓝 (rateHistoryDualPropagator rates capacity T)) := by
  obtain ⟨K, hK, hbound⟩ := exists_dualGeneratorPath_bound hT hcontinuous
  refine (tendsto_sampledProduct (continuous_dualGeneratorPath hT hcontinuous) hT hK
    hbound).congr fun n ↦ ?_
  rw [historyPropagator_sampledEpochs, Real.coe_toNNReal _ (div_nonneg hT (Nat.cast_nonneg n))]

/-! ## Realizability -/

/-- Every chronological product of epochs with nonnegative durations keeps the realization body of
the budget-moment feature invariant. -/
theorem historyPropagator_mulVec_mem_realizationBody (capacity : Locus → ℕ) :
    ∀ (epochs : List (NeutralRates Deme Locus Allele × ℝ)), (∀ epoch ∈ epochs, 0 ≤ epoch.2) →
      ∀ v ∈ realizationBody
          (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity),
        historyPropagator capacity epochs *ᵥ v
          ∈ realizationBody
            (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity)
  | [], _, v, hv => by
    rw [historyPropagator, Matrix.one_mulVec]
    exact hv
  | epoch :: rest, hdurations, v, hv => by
    rw [historyPropagator, ← Matrix.mulVec_mulVec]
    refine historyPropagator_mulVec_mem_realizationBody capacity rest
      (fun e he ↦ hdurations e (List.mem_cons.mpr (Or.inr he))) _ ?_
    exact exp_mulVec_mem_realizationBody _ _ (neutralMicroscopicApproximation epoch.1 capacity)
      (isClosed_realizationBody _ (continuous_budgetMomentFeature capacity)) epoch.2
      (hdurations epoch (List.mem_cons.mpr (Or.inl rfl))) v hv

/-- **The propagator of a rate history keeps moment vectors realizable.**  For a rate history
whose dual generator is continuous on the horizon, the propagator of the history applied to the
budget moments of a state lies in the realization body of the budget-moment feature. -/
theorem rateHistoryDualPropagator_mulVec_mem_realizationBody
    {rates : ℝ → NeutralRates Deme Locus Allele} {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (x0 : FrequencyState Deme Locus Allele) :
    rateHistoryDualPropagator rates capacity T *ᵥ budgetMomentFeature capacity x0
      ∈ realizationBody
        (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity) := by
  have hlimit : Tendsto (fun n : ℕ ↦ historyPropagator capacity
        ((sampledEpochs rates T (T / n).toNNReal n).map fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
          *ᵥ budgetMomentFeature capacity x0)
      atTop (𝓝 (rateHistoryDualPropagator rates capacity T *ᵥ budgetMomentFeature capacity x0)) :=
    ((EulerInvariantSet.mulVecMap
      (budgetMomentFeature capacity x0)).continuous_of_finiteDimensional.tendsto _).comp
      (tendsto_historyPropagator_sampledEpochs hT hcontinuous)
  refine (isClosed_realizationBody _ (continuous_budgetMomentFeature capacity)).mem_of_tendsto
    hlimit (Eventually.of_forall fun n ↦ ?_)
  refine historyPropagator_mulVec_mem_realizationBody capacity _ (fun epoch he ↦ ?_) _
    (mem_realizationBody_of_range _ x0)
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp he
  exact NNReal.coe_nonneg _

/-- **A realizing law for a rate history.**  For a rate history whose dual generator is continuous
on the horizon, at every initial state there is a finitely supported probability law on
frequency states whose budget-respecting configuration moments are `U(T) H(x₀)`. -/
theorem exists_rateHistoryLaw {rates : ℝ → NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (x0 : FrequencyState Deme Locus Allele) :
    ∃ w : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ,
      ∃ point : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele,
        (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1
          ∧ featureVector w point (budgetMomentFeature capacity)
            = rateHistoryDualPropagator rates capacity T *ᵥ budgetMomentFeature capacity x0 :=
  exists_law_of_mem_realizationBody _ _
    (rateHistoryDualPropagator_mulVec_mem_realizationBody hT hcontinuous x0)

/-! ## The process law of the sampled epochs -/

/-- **Expected moments of the sampled history kernels converge to the propagator of the
history.**  For a rate history whose dual generator is continuous on the horizon, the expected
configuration moments under the neutral history kernels of the sampled epochs converge to the
coordinates of `U(T) H(x)`. -/
theorem tendsto_integral_momentPolynomial_sampledEpochs
    {rates : ℝ → NeutralRates Deme Locus Allele} {capacity : Locus → ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    Tendsto (fun n : ℕ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y
        ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x))
      atTop (𝓝 ((rateHistoryDualPropagator rates capacity T
        *ᵥ budgetMomentFeature capacity x) ξ)) := by
  have hint : (fun n : ℕ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y
        ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x))
      = fun n : ℕ ↦ (historyPropagator capacity
          ((sampledEpochs rates T (T / n).toNNReal n).map fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
            *ᵥ budgetMomentFeature capacity x) ξ :=
    funext fun n ↦ integral_momentPolynomial_neutralHistoryKernel ℓ₀ hap₀ capacity _ x ξ
  rw [hint]
  exact ((continuous_apply ξ).tendsto _).comp
    (((EulerInvariantSet.mulVecMap
      (budgetMomentFeature capacity x)).continuous_of_finiteDimensional.tendsto _).comp
      (tendsto_historyPropagator_sampledEpochs hT hcontinuous))

variable {Sample Report : Type*} [Fintype Sample] [DecidableEq Sample] [Fintype Report]

/-- **NOTE1 (20) with (22) for a time-varying rate history, as a limit of the process law.**  For
a rate history whose dual generator is continuous on the horizon, the expected compiled reports
of an independently sampled panel under the neutral history kernels of the sampled epochs converge
to the sum over panel genotypes of the conditional readout times the seed coordinate of
`U(T) H(x₀)`. -/
theorem tendsto_integral_panelReport_sampledEpochs
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn
      (fun t ↦ dualGenerator (rates t) (fun _ ↦ Fintype.card Sample)) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (x0 : FrequencyState Deme Locus Allele) :
    Tendsto (fun n : ℕ ↦ ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦
          stateLaw y (deme draw)).bind report).expectation metric
        ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x0))
      atTop (𝓝 (∑ genotype : Sample → FullHaplotype Locus Allele,
        (report genotype).expectation metric *
          (rateHistoryDualPropagator rates (fun _ ↦ Fintype.card Sample) T
            *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0)
            (seedState deme genotype ℓ₀))) := by
  have hreport : (fun n : ℕ ↦ ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦
          stateLaw y (deme draw)).bind report).expectation metric
        ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x0))
      = fun n : ℕ ↦ ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric
            * ∫ y, polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
              ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x0) := by
    funext n
    rw [integral_panelReport_neutralHistoryKernel ℓ₀ hap₀ deme report metric _ x0]
    refine Finset.sum_congr rfl fun genotype _ ↦ ?_
    rw [integral_momentPolynomial_neutralHistoryKernel]
  rw [hreport]
  exact tendsto_finset_sum _ fun genotype _ ↦
    (tendsto_integral_momentPolynomial_sampledEpochs hT hcontinuous ℓ₀ hap₀ x0
      (seedState deme genotype ℓ₀)).const_mul _

end

end Descent.Portability.NeutralRateHistoryRealization
