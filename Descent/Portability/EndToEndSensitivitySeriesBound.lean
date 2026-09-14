/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSensitivitySeries
import Descent.Portability.EndToEndDecisionCertificates
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

assert_below Descent.Decision Descent.Program

/-!
# The summable sensitivity bound of the correlation series, and why it is not discharged

`EndToEndSensitivitySeries` differentiates the expected squared correlation `Σₖ E[N (1 - D)ᵏ]`
along a segment history termwise, under the hypothesis that one summable sequence bounds the term
sensitivities at every parameter in `(0, 1)`.  This module neither discharges nor refutes that
hypothesis for the history kernels.  It shows that two majorant shapes fail, exhibits a series with
the same term structure on which termwise differentiation holds while a bound of that shape fails,
and differentiates every truncation of the correlation series with no hypothesis.

No summable majorant of the terms.  Over `0 ≤ N ≤ D ≤ 1` the `k`-th term `N (1 - D)ᵏ` is at least
`1 / (4 (k + 1))` at `N = D = 1 / (2 (k + 1))`, by Bernoulli's inequality
(`one_div_four_mul_succ_le_expansion_term`).  So no sequence bounding the terms over that region is
summable (`not_summable_of_expansion_term_le`): the factor `(1 - D)ᵏ` is not bounded away from one
where `D` is small, and `D`, sixteen times a product of variances, vanishes wherever the score or
the outcome is constant on the haplotype law of the deme.

The shape of the hypothesis.  A bound on `(0, 1)` dominates the limits of the terms at `0` from the
right, so when those limits do not tend to zero no bound of that shape is summable
(`not_summable_of_tendsto_nhdsGT_zero`).  The witness is the expansion `Σₖ θ (1 - θ)ᵏ` of `θ / θ`
(`witnessTerm`, `witnessTermDerivative`, `hasDerivAt_witnessTerm`).  It sums to one on `(0, 1]`, so
its derivative is zero (`tsum_witnessTerm`, `hasDerivAt_tsum_witnessTerm`).  On `(a, 1)` with
`0 < a` its term derivatives are bounded by the summable sequence `(1 - a)ᵏ + k (1 - a)ᵏ⁻¹`
(`witnessLocalBound`, `abs_witnessTermDerivative_le`, `summable_witnessLocalBound`), so the series
differentiates termwise at every interior parameter (`tsum_witnessTermDerivative`).  Yet every term
derivative tends to one at `0` (`tendsto_witnessTermDerivative`), so no summable sequence bounds
them on `(0, 1)` (`not_summable_of_witnessTermDerivative_le`,
`witness_termwise_derivative_without_summable_bound`).  The obstruction sits where the denominator
vanishes, and a bound local to a neighbourhood of the parameter avoids it.

The truncations.  For every `K`, the sum of the first `K` expected series terms along a segment
history has as derivative the sum of their term sensitivities at every interior parameter, with no
hypothesis (`hasDerivAt_truncatedSeries_segmentHistory`).  Under every Markov kernel, in particular
at every parameter of a segment history, that sum lies below the expected squared correlation by
at most `E[(1 - D)ᴷ]` (`expectedSquaredCorrelation_truncation`), by the tail certificate
`EndToEndDecisionCertificates.integral_quotient_truncation`.

Scope.  The summable bound of `EndToEndSensitivitySeries` is neither discharged nor refuted for the
history kernels.  The obstructions here concern majorant shapes: a bound uniform over
`0 ≤ N ≤ D ≤ 1`, or over `(0, 1)` when the endpoint limits do not vanish.  They do not show that the
expected-term sensitivities of any history kernel fail to be summable.  The pointwise route is
closed because the fixation states, where `D = 0`, lie in the support of the state law along a
history with drift, so `(1 - D)ᵏ` is not bounded away from one there.  No bound on the term
sensitivities through the law of the state near those states is proved.  The operator bound
through the coefficient norm of `N (1 - D)ᵏ` and the generator norm at budget `4 (k + 1)` is not
formalized.  The witness is a scalar series and is not realized as a demographic history, and the
limits at `0` of the term sensitivities of a history are not computed.

## Empirical status

None.  The bodies here are Bernoulli's inequality, a comparison with the harmonic series,
derivatives of polynomials in one variable, finite sums of propagator sensitivities and a pointwise
geometric tail integrated against a Markov kernel, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivitySeriesBound

open Filter Topology MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel ReplicaMetricInstances
  PositiveRatioExpansion EndToEndPortabilityLaw EndToEndCorrelationSeries EndToEndSensitivityLaw
  EndToEndSensitivityRates
open scoped Matrix NNReal

noncomputable section

/-! ## No summable majorant of the expansion terms -/

/-- The shifted harmonic sequence `1 / (k + 1)` is not summable. -/
theorem not_summable_one_div_succ : ¬ Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := by
  have h := mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).mp
    Real.not_summable_one_div_natCast
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- At `N = D = 1 / (2 (k + 1))` the `k`-th expansion term is at least `1 / (4 (k + 1))`. -/
theorem one_div_four_mul_succ_le_expansion_term (k : ℕ) :
    1 / (4 * ((k : ℝ) + 1))
      ≤ 1 / (2 * ((k : ℝ) + 1)) * (1 - 1 / (2 * ((k : ℝ) + 1))) ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsmall : 1 / (2 * ((k : ℝ) + 1)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hbernoulli :=
    one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (2 * ((k : ℝ) + 1))) by linarith) k
  have hmul : (k : ℝ) * (1 / (2 * ((k : ℝ) + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hhalf : (1 : ℝ) / 2 ≤ (1 - 1 / (2 * ((k : ℝ) + 1))) ^ k := by
    rw [sub_eq_add_neg]
    linarith
  calc 1 / (4 * ((k : ℝ) + 1)) = 1 / (2 * ((k : ℝ) + 1)) * (1 / 2) := by
        generalize (k : ℝ) + 1 = c
        ring
    _ ≤ 1 / (2 * ((k : ℝ) + 1)) * (1 - 1 / (2 * ((k : ℝ) + 1))) ^ k :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)

/-- **No summable majorant of the expansion terms.**  A sequence bounding the `k`-th term
`N (1 - D)ᵏ` of the positive ratio expansion at every `0 ≤ N ≤ D ≤ 1` is not summable.  This
concerns that majorant shape, not the expected terms under a history kernel. -/
theorem not_summable_of_expansion_term_le {bound : ℕ → ℝ}
    (hbound : ∀ (k : ℕ) (num den : ℝ), 0 ≤ num → num ≤ den → den ≤ 1 →
      num * (1 - den) ^ k ≤ bound k) :
    ¬ Summable bound := by
  intro hsummable
  have hle : ∀ k : ℕ, 1 / (4 * ((k : ℝ) + 1)) ≤ bound k := fun k ↦ by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hden : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact (one_div_four_mul_succ_le_expansion_term k).trans
      (hbound k (1 / (2 * ((k : ℝ) + 1))) (1 / (2 * ((k : ℝ) + 1))) (by positivity) le_rfl hden)
  have hquarter : Summable fun k : ℕ ↦ 1 / (4 * ((k : ℝ) + 1)) :=
    Summable.of_nonneg_of_le (fun k ↦ by positivity) hle hsummable
  refine not_summable_one_div_succ ((hquarter.mul_left 4).congr fun k ↦ ?_)
  show 4 * (1 / (4 * ((k : ℝ) + 1))) = 1 / ((k : ℝ) + 1)
  generalize (k : ℝ) + 1 = c
  ring

/-! ## The shape of the hypothesis -/

/-- **A bound on `(0, 1)` dominates the endpoint limits.**  If the `k`-th function tends to `L k`
at `0` from the right and one sequence bounds the absolute values of all of them on `(0, 1)`, then
that sequence is not summable unless `L` tends to zero. -/
theorem not_summable_of_tendsto_nhdsGT_zero {g : ℕ → ℝ → ℝ} {L : ℕ → ℝ}
    (hlimit : ∀ k, Tendsto (g k) (𝓝[>] 0) (𝓝 (L k))) (hL : ¬ Tendsto L atTop (𝓝 0))
    {bound : ℕ → ℝ} (hbound : ∀ k, ∀ θ ∈ Set.Ioo (0 : ℝ) 1, |g k θ| ≤ bound k) :
    ¬ Summable bound := by
  intro hsummable
  have habs : ∀ k, ‖L k‖ ≤ bound k := fun k ↦ by
    refine le_of_tendsto (hlimit k).norm ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with θ hθ
    rw [Real.norm_eq_abs]
    exact hbound k θ hθ
  exact hL (tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun k ↦ by simpa only [sub_zero] using habs k) hsummable.tendsto_atTop_zero))

/-- **The witness terms**: the terms `θ (1 - θ)ᵏ` of the positive ratio expansion of `θ / θ`,
whose numerator and denominator are both the parameter. -/
def witnessTerm (k : ℕ) (θ : ℝ) : ℝ :=
  θ * (1 - θ) ^ k

/-- The derivative `(1 - θ)ᵏ - θ k (1 - θ)ᵏ⁻¹` of the `k`-th witness term. -/
def witnessTermDerivative (k : ℕ) (θ : ℝ) : ℝ :=
  (1 - θ) ^ k - θ * (k * (1 - θ) ^ (k - 1))

/-- The local bound `(1 - a)ᵏ + k (1 - a)ᵏ⁻¹` of the witness term derivatives on `(a, 1)`. -/
def witnessLocalBound (a : ℝ) (k : ℕ) : ℝ :=
  (1 - a) ^ k + k * (1 - a) ^ (k - 1)

/-- The `k`-th witness term has derivative `witnessTermDerivative k θ` at every parameter. -/
theorem hasDerivAt_witnessTerm (k : ℕ) (θ : ℝ) :
    HasDerivAt (witnessTerm k) (witnessTermDerivative k θ) θ := by
  have hpower : HasDerivAt (fun θ' : ℝ ↦ (1 - θ') ^ k) (k * (1 - θ) ^ (k - 1) * -1) θ :=
    ((hasDerivAt_id' (x := θ)).const_sub 1).fun_pow k
  refine ((hasDerivAt_id' (x := θ)).mul hpower).congr_deriv ?_
  rw [witnessTermDerivative]
  ring

/-- On `(0, 1]` the witness series sums to one, the ratio `θ / θ`. -/
theorem tsum_witnessTerm {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) 1) :
    ∑' k : ℕ, witnessTerm k θ = 1 := by
  simp only [witnessTerm]
  rw [tsum_expansion_terms θ θ hθ.1.le le_rfl hθ.2, if_pos hθ.1, div_self hθ.1.ne']

/-- The witness series has derivative zero at every interior parameter. -/
theorem hasDerivAt_tsum_witnessTerm {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun θ ↦ ∑' k : ℕ, witnessTerm k θ) 0 θ₀ := by
  refine (hasDerivAt_const θ₀ (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ₀.1 hθ₀.2] with θ hθ
  exact tsum_witnessTerm ⟨hθ.1, hθ.2.le⟩

/-- On `(a, 1)` with `0 ≤ a` the witness term derivatives are bounded by the local bound. -/
theorem abs_witnessTermDerivative_le {a : ℝ} (ha : 0 ≤ a) (k : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo a 1) : |witnessTermDerivative k θ| ≤ witnessLocalBound a k := by
  have hθ0 : 0 ≤ θ := ha.trans hθ.1.le
  have hdeficit : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hle : 1 - θ ≤ 1 - a := by linarith [hθ.1]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hfirst : (1 - θ) ^ k ≤ (1 - a) ^ k := pow_le_pow_left₀ hdeficit hle k
  have hfirst0 : 0 ≤ (1 - θ) ^ k := pow_nonneg hdeficit k
  have hsecond0 : 0 ≤ θ * (k * (1 - θ) ^ (k - 1)) :=
    mul_nonneg hθ0 (mul_nonneg hk (pow_nonneg hdeficit (k - 1)))
  have hsecond : θ * (k * (1 - θ) ^ (k - 1)) ≤ k * (1 - a) ^ (k - 1) :=
    calc θ * (k * (1 - θ) ^ (k - 1)) ≤ 1 * (k * (1 - θ) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_right hθ.2.le (mul_nonneg hk (pow_nonneg hdeficit (k - 1)))
      _ = k * (1 - θ) ^ (k - 1) := one_mul _
      _ ≤ k * (1 - a) ^ (k - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdeficit hle (k - 1)) hk
  rw [witnessTermDerivative, witnessLocalBound, abs_le]
  constructor <;> linarith

/-- For `0 < a ≤ 1` the local bound is summable. -/
theorem summable_witnessLocalBound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Summable (witnessLocalBound a) := by
  have hr0 : 0 ≤ 1 - a := by linarith
  have hr1 : 1 - a < 1 := by linarith
  have hgeometric := summable_geometric_of_lt_one hr0 hr1
  have hnorm : ‖1 - a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hshifted : Summable fun k : ℕ ↦ (k : ℝ) * (1 - a) ^ (k - 1) := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).add hgeometric).congr
      fun k ↦ ?_
    simp only [pow_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    ring
  exact hgeometric.add hshifted

/-- **The witness series differentiates termwise.**  At every interior parameter the witness term
derivatives sum to zero, the derivative of the witness series, by the local summable bound on
`(θ₀ / 2, 1)`. -/
theorem tsum_witnessTermDerivative {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∑' k : ℕ, witnessTermDerivative k θ₀ = 0 := by
  have ha : 0 < θ₀ / 2 := half_pos hθ₀.1
  have hmem : θ₀ ∈ Set.Ioo (θ₀ / 2) 1 := ⟨half_lt_self hθ₀.1, hθ₀.2⟩
  have hseries := hasDerivAt_tsum_of_isPreconnected
    (summable_witnessLocalBound ha (by linarith [hθ₀.2]))
    (isOpen_Ioo : IsOpen (Set.Ioo (θ₀ / 2) 1)) isPreconnected_Ioo
    (fun k θ _ ↦ hasDerivAt_witnessTerm k θ)
    (fun k θ hθ ↦ by
      rw [Real.norm_eq_abs]
      exact abs_witnessTermDerivative_le ha.le k hθ)
    hmem (summable_expansion_terms θ₀ θ₀ hθ₀.1.le le_rfl hθ₀.2.le) hmem
  exact hseries.unique (hasDerivAt_tsum_witnessTerm hθ₀)

/-- Every witness term derivative tends to one at `0` from the right. -/
theorem tendsto_witnessTermDerivative (k : ℕ) :
    Tendsto (witnessTermDerivative k) (𝓝[>] 0) (𝓝 1) := by
  have hcontinuous : Continuous (witnessTermDerivative k) := by
    show Continuous fun θ : ℝ ↦ (1 - θ) ^ k - θ * ((k : ℝ) * (1 - θ) ^ (k - 1))
    fun_prop
  have hvalue : witnessTermDerivative k 0 = 1 := by
    simp [witnessTermDerivative]
  have hlimit := (hcontinuous.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rwa [hvalue] at hlimit

/-- No summable sequence bounds the witness term derivatives on `(0, 1)`. -/
theorem not_summable_of_witnessTermDerivative_le {bound : ℕ → ℝ}
    (hbound : ∀ k, ∀ θ ∈ Set.Ioo (0 : ℝ) 1, |witnessTermDerivative k θ| ≤ bound k) :
    ¬ Summable bound :=
  not_summable_of_tendsto_nhdsGT_zero (L := fun _ ↦ 1) tendsto_witnessTermDerivative
    (fun h ↦ one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)) hbound

/-- **The obstruction.**  The witness series `Σₖ θ (1 - θ)ᵏ` differentiates termwise at every
interior parameter, yet no summable sequence bounds its term derivatives on `(0, 1)`, the shape of
the bound that `EndToEndSensitivitySeries.hasDerivAt_expectedSquaredCorrelation_segmentHistory`
takes as a hypothesis.  It neither discharges nor refutes that hypothesis for any history
kernel. -/
theorem witness_termwise_derivative_without_summable_bound :
    (∀ θ₀ ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun θ ↦ ∑' k : ℕ, witnessTerm k θ)
        (∑' k : ℕ, witnessTermDerivative k θ₀) θ₀)
      ∧ ∀ bound : ℕ → ℝ,
        (∀ k, ∀ θ ∈ Set.Ioo (0 : ℝ) 1, |witnessTermDerivative k θ| ≤ bound k) →
          ¬ Summable bound := by
  refine ⟨fun θ₀ hθ₀ ↦ ?_, fun _ hbound ↦ not_summable_of_witnessTermDerivative_le hbound⟩
  rw [tsum_witnessTermDerivative hθ₀]
  exact hasDerivAt_tsum_witnessTerm hθ₀

/-! ## The truncations along a segment history -/

section Truncation

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The truncated correlation series along a segment history, with no hypothesis.**  For every
`K`, the sum of the first `K` expected terms `E[N (1 - D)ᵏ]` has as derivative at every interior
parameter the sum of their term sensitivities. -/
theorem hasDerivAt_truncatedSeries_segmentHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (history : List ((NeutralRates Deme Locus Allele × NeutralRates Deme Locus Allele × ℝ≥0)
      ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ) (K : ℕ) :
    HasDerivAt (fun θ ↦ ∑ k ∈ Finset.range K,
        ∫ y, correlationNumerator (stateLaw y deme) score outcome
          * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k
          ∂(historyEventKernel ℓ₀ hap₀ ((history.map segmentEvent).map fun event ↦ event θ) x0))
      (∑ k ∈ Finset.range K, historySensitivity (fun _ ↦ 4 * (k + 1)) θ₀
        (history.map segmentEvent) (familyDerivative (fun _ ↦ 4 * (k + 1)) θ₀)
        (budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1)) (seriesTermPolynomial deme score outcome k))
        (budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0)) θ₀ :=
  HasDerivAt.fun_sum fun k _ ↦
    (hasDerivAt_dotProduct_segmentHistory (fun _ ↦ 4 * (k + 1)) hθ₀ history
      (budgetCoefficients ℓ₀ (fun _ ↦ 4 * (k + 1)) (seriesTermPolynomial deme score outcome k))
      (budgetMomentFeature (fun _ ↦ 4 * (k + 1)) x0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun θ ↦
        integral_seriesTerm_historyEventKernel ℓ₀ hap₀
          ((history.map segmentEvent).map fun event ↦ event θ) x0 deme score outcome k)

/-- **The truncation error of the correlation series.**  Under every Markov kernel, for a score and
an outcome in the unit interval, the expected squared correlation minus the sum of its first `K`
expected series terms lies between zero and `E[(1 - D)ᴷ]`. -/
theorem expectedSquaredCorrelation_truncation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (hscore0 : ∀ hap, 0 ≤ score hap) (hscore1 : ∀ hap, score hap ≤ 1)
    (houtcome0 : ∀ hap, 0 ≤ outcome hap) (houtcome1 : ∀ hap, outcome hap ≤ 1) (K : ℕ) :
    0 ≤ expectedSquaredCorrelation κ x0 deme score outcome
        - ∑ k ∈ Finset.range K, ∫ y, correlationNumerator (stateLaw y deme) score outcome
          * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k ∂(κ x0)
      ∧ expectedSquaredCorrelation κ x0 deme score outcome
          - ∑ k ∈ Finset.range K, ∫ y, correlationNumerator (stateLaw y deme) score outcome
            * (1 - correlationDenominator (stateLaw y deme) score outcome) ^ k ∂(κ x0)
        ≤ ∫ y, (1 - correlationDenominator (stateLaw y deme) score outcome) ^ K ∂(κ x0) := by
  have hbounds : ∀ y : FrequencyState Deme Locus Allele,
      0 ≤ correlationNumerator (stateLaw y deme) score outcome
        ∧ correlationNumerator (stateLaw y deme) score outcome
          ≤ correlationDenominator (stateLaw y deme) score outcome
        ∧ correlationDenominator (stateLaw y deme) score outcome ≤ 1 := fun y ↦
    ⟨correlationNumerator_nonneg _ score outcome,
      correlationNumerator_le_denominator _ score outcome,
      correlationDenominator_le_one _ score outcome hscore0 hscore1 houtcome0 houtcome1⟩
  have htruncation := EndToEndDecisionCertificates.integral_quotient_truncation (κ x0)
    (fun y ↦ correlationNumerator (stateLaw y deme) score outcome)
    (fun y ↦ correlationDenominator (stateLaw y deme) score outcome)
    (measurable_correlationNumerator deme score outcome)
    (measurable_correlationDenominator deme score outcome)
    (fun y ↦ (hbounds y).1) (fun y ↦ (hbounds y).2.1) (fun y ↦ (hbounds y).2.2) K
  have hvalue : expectedSquaredCorrelation κ x0 deme score outcome
      = ∫ y, correlationNumerator (stateLaw y deme) score outcome
        / correlationDenominator (stateLaw y deme) score outcome ∂(κ x0) := by
    rw [expectedSquaredCorrelation]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    show ((stateLaw y deme).squaredCorrelation score outcome).getD 0
      = correlationNumerator (stateLaw y deme) score outcome
        / correlationDenominator (stateLaw y deme) score outcome
    rw [getD_squaredCorrelation_stateLaw]
    show (if 0 < correlationDenominator (stateLaw y deme) score outcome then
        correlationNumerator (stateLaw y deme) score outcome
          / correlationDenominator (stateLaw y deme) score outcome
      else 0) = _
    split_ifs with hpositive
    · rfl
    · rw [le_antisymm (not_lt.mp hpositive) ((hbounds y).1.trans (hbounds y).2.1), div_zero]
  rw [hvalue, htruncation.1]
  exact htruncation.2

end Truncation

end

end Descent.Portability.EndToEndSensitivitySeriesBound
