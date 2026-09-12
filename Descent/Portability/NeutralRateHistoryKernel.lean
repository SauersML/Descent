/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralRateHistoryRealization
import Descent.Portability.NeutralMicroscopicFloorLimit

assert_below Descent.Decision Descent.Program

/-!
# The neutral Markov kernel of a time-varying rate history

NOTE1 §4.2a: measurable time-dependent rate histories follow by the step-function approximation of
§2.4.  `NeutralRateHistoryRealization` proves this for moment vectors and panel reports as limits.
This module constructs the Markov kernel of the history itself, for rate histories whose dual
generator is continuous on the horizon at every budget.

History operators.  The neutral history kernel of a list of epochs integrates every continuous
observable to the composition of the extended neutral semigroups of its epochs
(`historyOperator`, `integral_neutralHistoryKernel_eq_historyOperator`), a positive,
constant-preserving sup-norm contraction (`historyOperator_nonneg`, `historyOperator_one`,
`norm_historyOperator_apply_le`).

The limit.  Along the left-endpoint sampling at step `T/n` (`sampledOperator`), a polynomial
observable is sent to a fixed combination of the sampled dual propagators applied to the
configuration moments (`sampledOperator_polynomial`, `abs_dotProduct_mulVec_sub_le`).  Those
propagators converge, so the sampled operators applied to a polynomial observable form a Cauchy
sequence in sup norm.  Every continuous observable is within any `ε` of a polynomial one and every
sampled operator contracts, so `sampledOperator n g` is Cauchy for every continuous `g`
(`cauchySeq_sampledOperator`).  Its limit is a positive, constant-preserving contraction
(`rateHistoryOperator`, `tendsto_rateHistoryOperator`, `rateHistoryOperator_nonneg`,
`rateHistoryOperator_one`).

The kernel.  Its Riesz kernel is a Markov kernel (`rateHistoryKernel`,
`isMarkovKernel_rateHistoryKernel`, `integral_rateHistoryKernel`).  The sampled history kernels
converge to it in law, uniformly in the initial state
(`tendstoUniformly_integral_sampledHistoryKernel`).  For every budget its expected configuration
moments are the propagator of the history applied to the initial moments,
`∫ H_ξ dK_T(x, ·) = (U(T) H(x))_ξ` (`integral_momentPolynomial_rateHistoryKernel`), and the exact
panel reports follow (`integral_panelReport_rateHistoryKernel`).  Constant rates satisfy the
continuity hypothesis (`continuousOn_dualGenerator_const`).

Scope.  The dual generator of the rate history is assumed continuous on the horizon at every
budget; measurable rates with merely integrable norm are not formalized.  A locus `ℓ₀` and a
haplotype `hap₀` are explicit arguments, as in `NeutralPolynomialSemigroup`.

## Empirical status

None.  The bodies here are limits of compositions of positive operators on continuous observables
and integrals against Markov kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralRateHistoryKernel

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup NeutralPolynomialPositivity
  PartialHaplotypeMicroscopicApproximation PartialHaplotypePanelLikelihood
  PolynomialFellerExtension FellerMarkovKernel NeutralMicroscopicEulerLimit
  NeutralMicroscopicFloorLimit NeutralKernelPanelLikelihood NeutralHistoryKernel
  NeutralRateHistoryRealization
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## History operators -/

/-- The operator of a list of epochs on continuous observables: the extended neutral semigroup of
the head epoch applied after the operator of the rest of the history. -/
def historyOperator (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    List (NeutralRates Deme Locus Allele × ℝ≥0) →
      C(FrequencyState Deme Locus Allele, ℝ) →L[ℝ] C(FrequencyState Deme Locus Allele, ℝ)
  | [] => ContinuousLinearMap.id ℝ _
  | epoch :: rest =>
      (neutralSemigroupExtension epoch.1 ℓ₀ hap₀ epoch.2).comp (historyOperator ℓ₀ hap₀ rest)

/-- The neutral history kernel integrates every continuous observable to the history operator. -/
theorem integral_neutralHistoryKernel_eq_historyOperator (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) :
    ∀ (epochs : List (NeutralRates Deme Locus Allele × ℝ≥0))
      (x : FrequencyState Deme Locus Allele) (g : C(FrequencyState Deme Locus Allele, ℝ)),
      ∫ y, g y ∂(neutralHistoryKernel ℓ₀ hap₀ epochs x) = historyOperator ℓ₀ hap₀ epochs g x
  | [], x, g => by
    rw [neutralHistoryKernel, Kernel.id_apply,
      integral_dirac' _ _ g.continuous.stronglyMeasurable]
    rfl
  | epoch :: rest, x, g => by
    haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ rest
    haveI := isMarkovKernel_neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2
    have hcomp : Integrable (fun y ↦ g y)
        ((neutralHistoryKernel ℓ₀ hap₀ rest ∘ₖ neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2) x) :=
      (BoundedContinuousFunction.mkOfCompact g).integrable _
    rw [neutralHistoryKernel, Kernel.integral_comp hcomp]
    simp only [integral_neutralHistoryKernel_eq_historyOperator ℓ₀ hap₀ rest]
    exact integral_neutralMarkovKernel epoch.1 ℓ₀ hap₀ epoch.2 x _

/-- History operators are positive. -/
theorem historyOperator_nonneg (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ≥0))
    (g : C(FrequencyState Deme Locus Allele, ℝ)) (hg : 0 ≤ g) :
    0 ≤ historyOperator ℓ₀ hap₀ epochs g := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  rw [ContinuousMap.zero_apply, ← integral_neutralHistoryKernel_eq_historyOperator]
  refine integral_nonneg fun y ↦ ?_
  have hy := ContinuousMap.le_def.mp hg y
  rw [ContinuousMap.zero_apply] at hy
  exact hy

/-- History operators fix the constant observable. -/
theorem historyOperator_one (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ≥0)) :
    historyOperator ℓ₀ hap₀ epochs 1 = 1 := by
  haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ epochs
  refine ContinuousMap.ext fun x ↦ ?_
  rw [← integral_neutralHistoryKernel_eq_historyOperator]
  simp only [ContinuousMap.one_apply, integral_const, measureReal_univ_eq_one, smul_eq_mul,
    mul_one]

/-- History operators contract sup norms. -/
theorem norm_historyOperator_apply_le (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (epochs : List (NeutralRates Deme Locus Allele × ℝ≥0))
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ‖historyOperator ℓ₀ hap₀ epochs g‖ ≤ ‖g‖ := by
  haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ epochs
  refine (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x ↦ ?_
  rw [← integral_neutralHistoryKernel_eq_historyOperator]
  refine (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun y ↦ ContinuousMap.norm_coe_le_norm g y)).trans_eq ?_
  rw [measureReal_univ_eq_one, mul_one]

/-! ## The limit along the sampled epochs -/

/-- The operator of the left-endpoint sampling of a rate history at step `T/n`. -/
def sampledOperator (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (T : ℝ) (n : ℕ) :
    C(FrequencyState Deme Locus Allele, ℝ) →L[ℝ] C(FrequencyState Deme Locus Allele, ℝ) :=
  historyOperator ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n)

/-- A combination of configuration moments moves under a change of propagator by at most the
coefficient mass times the operator distance of the propagators times the feature bound. -/
theorem abs_dotProduct_mulVec_sub_le (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (c : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (P Q : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (x : FrequencyState Deme Locus Allele) :
    |c ⬝ᵥ (P *ᵥ budgetMomentFeature capacity x) - c ⬝ᵥ (Q *ᵥ budgetMomentFeature capacity x)|
      ≤ (∑ η, |c η|) * (‖P - Q‖ * featureBound rates capacity) := by
  have hvec : ‖P *ᵥ budgetMomentFeature capacity x - Q *ᵥ budgetMomentFeature capacity x‖
      ≤ ‖P - Q‖ * featureBound rates capacity := by
    rw [← Matrix.sub_mulVec]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (norm_budgetMomentFeature_le rates capacity x) (norm_nonneg _))
  rw [← dotProduct_sub]
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun η _ ↦ ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ η).trans hvec

/-- The sampled operator sends a polynomial observable to the combination of the sampled dual
propagator applied to the configuration moments of its support budget. -/
theorem sampledOperator_polynomial (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (T : ℝ) (n : ℕ)
    (f : PolynomialSubspace Deme Locus Allele) (x : FrequencyState Deme Locus Allele) :
    sampledOperator rates ℓ₀ hap₀ T n (f : C(FrequencyState Deme Locus Allele, ℝ)) x
      = supportCoefficients ℓ₀ (representative f)
          ⬝ᵥ (historyPropagator (supportBudget ℓ₀ (representative f))
              ((sampledEpochs rates T (T / n).toNNReal n).map
                fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
            *ᵥ budgetMomentFeature (supportBudget ℓ₀ (representative f)) x) := by
  haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀
    (sampledEpochs rates T (T / n).toNNReal n)
  rw [sampledOperator, ← integral_neutralHistoryKernel_eq_historyOperator]
  have hf : ∀ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y
      = ∑ η, supportCoefficients ℓ₀ (representative f) η
          * polynomialFunction (momentPolynomial η.1) y := fun y ↦
    congrFun (coe_polynomialSubspace_eq_dotProduct ℓ₀ f) y
  have hint : ∀ η : BudgetConfiguration Deme Locus Allele (supportBudget ℓ₀ (representative f)),
      Integrable (fun y ↦ polynomialFunction (momentPolynomial η.1) y)
        (neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x) := fun η ↦
    (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial η.1))).integrable _
  simp only [hf]
  rw [integral_finset_sum Finset.univ fun η _ ↦
    (hint η).const_mul (supportCoefficients ℓ₀ (representative f) η)]
  simp only [integral_const_mul, integral_momentPolynomial_neutralHistoryKernel]
  rfl

/-- **The sampled operators converge on every continuous observable.**  For a rate history whose
dual generator is continuous on the horizon at every budget, `sampledOperator n g` is a Cauchy
sequence in sup norm for every continuous observable `g`. -/
theorem cauchySeq_sampledOperator {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    CauchySeq fun n : ℕ ↦ sampledOperator rates ℓ₀ hap₀ T n g := by
  have hpoly : ∀ f : PolynomialSubspace Deme Locus Allele, CauchySeq fun n : ℕ ↦
      sampledOperator rates ℓ₀ hap₀ T n (f : C(FrequencyState Deme Locus Allele, ℝ)) := by
    intro f
    have hP := (tendsto_historyPropagator_sampledEpochs hT
      (hcontinuous (supportBudget ℓ₀ (representative f)))).cauchySeq
    rw [Metric.cauchySeq_iff] at hP ⊢
    intro ε hε
    have hB : 0 ≤ (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
        * featureBound (rates 0) (supportBudget ℓ₀ (representative f)) :=
      mul_nonneg (Finset.sum_nonneg fun η _ ↦ abs_nonneg _)
        (Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec (rates 0) _ ξ).1)
    have hpos : 0 < (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
        * featureBound (rates 0) (supportBudget ℓ₀ (representative f)) + 1 := by linarith
    obtain ⟨N, hN⟩ := hP (ε / ((∑ η, |supportCoefficients ℓ₀ (representative f) η|)
      * featureBound (rates 0) (supportBudget ℓ₀ (representative f)) + 1)) (div_pos hε hpos)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hmn := hN m hm n hn
    rw [dist_eq_norm] at hmn ⊢
    have hbound : ‖sampledOperator rates ℓ₀ hap₀ T m (f : C(FrequencyState Deme Locus Allele, ℝ))
          - sampledOperator rates ℓ₀ hap₀ T n (f : C(FrequencyState Deme Locus Allele, ℝ))‖
        ≤ (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
          * featureBound (rates 0) (supportBudget ℓ₀ (representative f))
          * ‖historyPropagator (supportBudget ℓ₀ (representative f))
              ((sampledEpochs rates T (T / m).toNNReal m).map
                fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
            - historyPropagator (supportBudget ℓ₀ (representative f))
              ((sampledEpochs rates T (T / n).toNNReal n).map
                fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))‖ := by
      refine (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg _))).mpr fun x ↦ ?_
      rw [ContinuousMap.sub_apply, Real.norm_eq_abs, sampledOperator_polynomial,
        sampledOperator_polynomial]
      refine (abs_dotProduct_mulVec_sub_le (rates 0) _ _ _ _ x).trans_eq ?_
      ring
    refine hbound.trans_lt ?_
    calc (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
            * featureBound (rates 0) (supportBudget ℓ₀ (representative f))
            * ‖historyPropagator (supportBudget ℓ₀ (representative f))
                ((sampledEpochs rates T (T / m).toNNReal m).map
                  fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
              - historyPropagator (supportBudget ℓ₀ (representative f))
                ((sampledEpochs rates T (T / n).toNNReal n).map
                  fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))‖
          ≤ (∑ η, |supportCoefficients ℓ₀ (representative f) η|)
            * featureBound (rates 0) (supportBudget ℓ₀ (representative f))
            * (ε / ((∑ η, |supportCoefficients ℓ₀ (representative f) η|)
              * featureBound (rates 0) (supportBudget ℓ₀ (representative f)) + 1)) :=
            mul_le_mul_of_nonneg_left hmn.le hB
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ hpos]
            nlinarith
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨f, hf⟩ := dense_polynomialSubspace.denseRange_val.exists_dist_lt g hε3
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hpoly f) (ε / 3) hε3
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hcontract : ∀ k : ℕ, dist (sampledOperator rates ℓ₀ hap₀ T k g)
      (sampledOperator rates ℓ₀ hap₀ T k (f : C(FrequencyState Deme Locus Allele, ℝ)))
        < ε / 3 := by
    intro k
    rw [dist_eq_norm, ← map_sub]
    refine (norm_historyOperator_apply_le ℓ₀ hap₀ _ _).trans_lt ?_
    rwa [← dist_eq_norm]
  calc dist (sampledOperator rates ℓ₀ hap₀ T m g) (sampledOperator rates ℓ₀ hap₀ T n g)
      ≤ dist (sampledOperator rates ℓ₀ hap₀ T m g)
          (sampledOperator rates ℓ₀ hap₀ T m (f : C(FrequencyState Deme Locus Allele, ℝ)))
        + dist (sampledOperator rates ℓ₀ hap₀ T m (f : C(FrequencyState Deme Locus Allele, ℝ)))
          (sampledOperator rates ℓ₀ hap₀ T n (f : C(FrequencyState Deme Locus Allele, ℝ)))
        + dist (sampledOperator rates ℓ₀ hap₀ T n (f : C(FrequencyState Deme Locus Allele, ℝ)))
          (sampledOperator rates ℓ₀ hap₀ T n g) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
        add_lt_add (add_lt_add (hcontract m) (hN m hm n hn)) (by rw [dist_comm]; exact hcontract n)
    _ = ε := by ring

/-- The limit of the sampled operators applied to an observable. -/
def rateHistoryOperatorValue (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (T : ℝ) (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    C(FrequencyState Deme Locus Allele, ℝ) :=
  limUnder atTop fun n : ℕ ↦ sampledOperator rates ℓ₀ hap₀ T n g

/-- The sampled operators applied to an observable converge to the limit value. -/
theorem tendsto_rateHistoryOperatorValue {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    Tendsto (fun n : ℕ ↦ sampledOperator rates ℓ₀ hap₀ T n g) atTop
      (𝓝 (rateHistoryOperatorValue rates ℓ₀ hap₀ T g)) :=
  (cauchySeq_sampledOperator hT hcontinuous ℓ₀ hap₀ g).tendsto_limUnder

/-- The limit value is additive in the observable. -/
theorem rateHistoryOperatorValue_add {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g h : C(FrequencyState Deme Locus Allele, ℝ)) :
    rateHistoryOperatorValue rates ℓ₀ hap₀ T (g + h)
      = rateHistoryOperatorValue rates ℓ₀ hap₀ T g
        + rateHistoryOperatorValue rates ℓ₀ hap₀ T h := by
  have hsum := (tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ g).add
    (tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ h)
  exact tendsto_nhds_unique (tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ (g + h))
    (hsum.congr fun n ↦ (map_add (sampledOperator rates ℓ₀ hap₀ T n) g h).symm)

/-- The limit value commutes with scaling the observable. -/
theorem rateHistoryOperatorValue_smul {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (a : ℝ)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    rateHistoryOperatorValue rates ℓ₀ hap₀ T (a • g)
      = a • rateHistoryOperatorValue rates ℓ₀ hap₀ T g := by
  have hscaled := (tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ g).const_smul a
  exact tendsto_nhds_unique (tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ (a • g))
    (hscaled.congr fun n ↦ (map_smul (sampledOperator rates ℓ₀ hap₀ T n) a g).symm)

/-- The limit value contracts sup norms. -/
theorem norm_rateHistoryOperatorValue_le {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ‖rateHistoryOperatorValue rates ℓ₀ hap₀ T g‖ ≤ ‖g‖ := by
  have hnorm := (continuous_norm.tendsto _).comp
    (tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ g)
  exact le_of_tendsto hnorm
    (Eventually.of_forall fun n ↦ norm_historyOperator_apply_le ℓ₀ hap₀ _ g)

/-- **The operator of a rate history** on continuous observables: the limit of the sampled
operators. -/
def rateHistoryOperator (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T)) :
    C(FrequencyState Deme Locus Allele, ℝ) →L[ℝ] C(FrequencyState Deme Locus Allele, ℝ) :=
  LinearMap.mkContinuous
    { toFun := rateHistoryOperatorValue rates ℓ₀ hap₀ T
      map_add' := rateHistoryOperatorValue_add hT hcontinuous ℓ₀ hap₀
      map_smul' := rateHistoryOperatorValue_smul hT hcontinuous ℓ₀ hap₀ }
    1 fun g ↦ by
      rw [one_mul]
      exact norm_rateHistoryOperatorValue_le hT hcontinuous ℓ₀ hap₀ g

/-- The operator of a rate history is the limit value. -/
theorem rateHistoryOperator_apply (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous g
      = rateHistoryOperatorValue rates ℓ₀ hap₀ T g :=
  rfl

/-- The sampled operators converge to the operator of the rate history in sup norm. -/
theorem tendsto_rateHistoryOperator {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    Tendsto (fun n : ℕ ↦ sampledOperator rates ℓ₀ hap₀ T n g) atTop
      (𝓝 (rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous g)) := by
  rw [rateHistoryOperator_apply]
  exact tendsto_rateHistoryOperatorValue hT hcontinuous ℓ₀ hap₀ g

/-- The sampled operators converge to the operator of the rate history at every state. -/
theorem tendsto_sampledOperator_apply {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) (x : FrequencyState Deme Locus Allele) :
    Tendsto (fun n : ℕ ↦ sampledOperator rates ℓ₀ hap₀ T n g x) atTop
      (𝓝 (rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous g x)) :=
  ((continuous_eval_const x).tendsto _).comp (tendsto_rateHistoryOperator hT hcontinuous ℓ₀ hap₀ g)

/-- The operator of a rate history is positive. -/
theorem rateHistoryOperator_nonneg {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) (hg : 0 ≤ g) :
    0 ≤ rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous g := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  rw [ContinuousMap.zero_apply]
  refine ge_of_tendsto' (tendsto_sampledOperator_apply hT hcontinuous ℓ₀ hap₀ g x) fun n ↦ ?_
  have h := ContinuousMap.le_def.mp
    (historyOperator_nonneg ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) g hg) x
  rw [ContinuousMap.zero_apply] at h
  exact h

/-- The operator of a rate history fixes the constant observable. -/
theorem rateHistoryOperator_one {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous 1 = 1 :=
  tendsto_nhds_unique (tendsto_rateHistoryOperator hT hcontinuous ℓ₀ hap₀ 1)
    (tendsto_const_nhds.congr fun n ↦
      (historyOperator_one ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n)).symm)

/-! ## The kernel of a rate history -/

/-- **The neutral Markov kernel of a rate history** over `[0, T]`: the Riesz kernel of the operator
of the history. -/
def rateHistoryKernel (rates : ℝ → NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T)) :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele) :=
  markovKernel (rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous)
    (rateHistoryOperator_nonneg hT hcontinuous ℓ₀ hap₀)
    (rateHistoryOperator_one hT hcontinuous ℓ₀ hap₀)

/-- The kernel of a rate history is a Markov kernel. -/
theorem isMarkovKernel_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) :
    IsMarkovKernel (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) :=
  isMarkovKernel_markovKernel _ _ _

/-- The kernel of a rate history integrates every continuous observable to the operator of the
history. -/
theorem integral_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x : FrequencyState Deme Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    ∫ y, g y ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x)
      = rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous g x :=
  integral_markovKernel _ _ _ x g

/-- **NOTE1 §4.2a for a rate history, convergence in law.**  The neutral history kernels of the
sampled epochs converge to the kernel of the rate history: for every continuous observable `g`,
`∫ g dK_n(x, ·) → ∫ g dK_T(x, ·)` uniformly in the initial state. -/
theorem tendstoUniformly_integral_sampledHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (g : C(FrequencyState Deme Locus Allele, ℝ)) :
    TendstoUniformly
      (fun (n : ℕ) x ↦ ∫ y, g y
        ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x))
      (fun x ↦ ∫ y, g y ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x)) atTop := by
  have hsampled : (fun (n : ℕ) x ↦ ∫ y, g y
        ∂(neutralHistoryKernel ℓ₀ hap₀ (sampledEpochs rates T (T / n).toNNReal n) x))
      = fun (n : ℕ) x ↦ sampledOperator rates ℓ₀ hap₀ T n g x :=
    funext fun n ↦ funext fun x ↦ integral_neutralHistoryKernel_eq_historyOperator ℓ₀ hap₀ _ x g
  have hlimit : (fun x ↦ ∫ y, g y ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x))
      = ⇑(rateHistoryOperator rates ℓ₀ hap₀ hT hcontinuous g) :=
    funext fun x ↦ integral_rateHistoryKernel hT hcontinuous ℓ₀ hap₀ x g
  rw [hsampled, hlimit]
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (tendsto_rateHistoryOperator hT hcontinuous ℓ₀ hap₀ g)

/-- **NOTE1 (20) for a rate history, under the process law.**  For every budget, the expected
configuration moments under the kernel of a rate history are the propagator of the history
applied to the moments of the initial state. -/
theorem integral_momentPolynomial_rateHistoryKernel
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x)
      = (rateHistoryDualPropagator rates capacity T *ᵥ budgetMomentFeature capacity x) ξ := by
  rw [integral_rateHistoryKernel]
  refine tendsto_nhds_unique (tendsto_sampledOperator_apply hT hcontinuous ℓ₀ hap₀ _ x) ?_
  exact (tendsto_integral_momentPolynomial_sampledEpochs hT (hcontinuous capacity) ℓ₀ hap₀ x
    ξ).congr fun n ↦ integral_neutralHistoryKernel_eq_historyOperator ℓ₀ hap₀ _ x _

/-- Constant rates have a continuous dual generator at every budget, so they satisfy the
hypothesis of the rate-history kernel. -/
theorem continuousOn_dualGenerator_const (rates : NeutralRates Deme Locus Allele) (T : ℝ) :
    ∀ capacity : Locus → ℕ,
      ContinuousOn (fun _ : ℝ ↦ dualGenerator rates capacity) (Set.Icc 0 T) :=
  fun _ ↦ continuousOn_const

variable {Sample Report : Type*} [Fintype Sample] [DecidableEq Sample] [Fintype Report]

/-- **NOTE1 (20) with (22) for a rate history, under the process law.**  The expected compiled
report of an independently sampled panel under the kernel of a rate history, started at a
frequency state, is the sum over panel genotypes of the conditional readout times the seed
coordinate of the propagator of the history applied to the initial moments. -/
theorem integral_panelReport_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele}
    {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (deme : Sample → Deme)
    (report : (Sample → FullHaplotype Locus Allele) → FiniteReportLaw Report)
    (metric : Report → ℝ) (x0 : FrequencyState Deme Locus Allele) :
    ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
        report).expectation metric ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric *
            (rateHistoryDualPropagator rates (fun _ ↦ Fintype.card Sample) T
              *ᵥ budgetMomentFeature (fun _ ↦ Fintype.card Sample) x0)
              (seedState deme genotype ℓ₀) := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  have hint : ∀ genotype : Sample → FullHaplotype Locus Allele,
      Integrable (fun y ↦ (report genotype).expectation metric
        * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y)
        (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0) := fun genotype ↦
    Integrable.const_mul ((BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1))).integrable _) _
  calc ∫ y, ((FiniteGeneticTransition.piLaw fun draw ↦ stateLaw y (deme draw)).bind
          report).expectation metric ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)
      = ∫ y, ∑ genotype : Sample → FullHaplotype Locus Allele,
          (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0) := by
        congr 1
        funext y
        exact panelReport_eq_sum_seedMoment deme report metric ℓ₀ y
    _ = ∑ genotype : Sample → FullHaplotype Locus Allele,
          ∫ y, (report genotype).expectation metric
            * polynomialFunction (momentPolynomial (seedState deme genotype ℓ₀).1) y
          ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0) :=
        integral_finset_sum Finset.univ fun genotype _ ↦ hint genotype
    _ = _ := by
        refine Finset.sum_congr rfl fun genotype _ ↦ ?_
        rw [integral_const_mul, integral_momentPolynomial_rateHistoryKernel]

end

end Descent.Portability.NeutralRateHistoryKernel
