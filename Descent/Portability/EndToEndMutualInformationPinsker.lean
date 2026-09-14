/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndLogLossBounds
import Descent.Portability.EntropyQuadraticFactor

assert_below Descent.Decision Descent.Program

/-!
# Pinsker's inequality for the report law

`EndToEndLogLossBounds` writes the mutual information of a score-outcome report law as the sum of
the divergence summands `x log (x / y) - x + y` of its cell masses against the products `q_s p_b`
of its marginals, and shows that it vanishes exactly at independence.  This module turns that
equality case into a quantitative bound: the information is at least half the square of the
distance from independence.

The second-order bound.  The entropy integrand `klFun t = t log t + 1 - t` satisfies
`3 (t - 1)² ≤ (2t + 4) klFun t` for `t ≥ 0` (`padeGap_nonneg`).  The logarithmic factor
`(t + 1) log t - 2 (t - 1)` (`logFactor`) has derivative `log t + (t + 1) / t - 2`, which is
nonnegative (`hasDerivAt_logFactor`), so its sign is the sign of `t - 1` (`logFactor_sign`).  The
gap `(2t + 4) klFun t - 3 (t - 1)²` (`padeGap`) has derivative `4 logFactor t`
(`hasDerivAt_padeGap`), so it decreases to `0` on `[0, 1]` and increases from `0` on `[1, ∞)`.
Equivalently the corpus quadratic factor is at least `3 / (2t + 4)` (`quadraticFactor_ge`), beside
its upper bound `1`.  For a mass `x ≥ 0` against `y > 0` this reads
`3 (x - y)² ≤ (2x + 4y) (x log (x / y) - x + y)` (`sq_sub_le_mul_divergenceTerm`).

Pinsker.  For two finite laws with `q > 0` wherever `p > 0`, Cauchy–Schwarz against the weights
`2p + 4q`, which sum to `6`, gives `(Σ |p - q|)² / 2 ≤ Σ divergence summands` (`pinsker_finite`):
the constant `½` is `3 / 6`.  The product of the marginals is a report law (`productMarginalLaw`,
`productMarginalLaw_mass`, `sum_productMarginals`).  The independence gap `Σ |m_{s,b} - q_s p_b|`
(`independenceGap`) is twice the corpus total variation from it
(`independenceGap_eq_two_mul_totalVariation`).  Hence `I(S; Y) ≥ ½ gap²`
(`half_sq_independenceGap_le_mutualInformation`), `I(S; Y) ≥ 2 TV²`
(`two_mul_sq_totalVariation_le_mutualInformation`), and pseudo-`R² ≥ gap² / (2 H(Y))`
(`sq_independenceGap_div_le_pseudoRSquared`).

Through a kernel.  The gap is a continuous observable (`continuous_independenceGap`).  Under every
Markov kernel `E I ≥ ½ E gap²` (`half_integral_sq_independenceGap_le_expectedMutualInformation`).
Since `E gap ≤ √(E gap²)`, also `E I ≥ ½ (E gap)²`
(`half_sq_integral_independenceGap_le_expectedMutualInformation`), and pseudo-`R²` in
ratio-of-expectations form is at least `(E gap)² / (2 E H(Y))`
(`sq_integral_independenceGap_div_le_expectedPseudoRSquared`).  All three hold along a history of
epochs, splits and pulses and along a rate history (`pinsker_historyEventKernel`,
`pinsker_rateHistoryKernel`).

Significance.  Under every demographic history, the information a risk score carries about the
outcome, and its pseudo-`R²`, are bounded below by the squared expected distance of the
populations the history produces from independence of score and outcome.

Scope.  Score groups form a finite alphabet and outcomes are binary; one chromosome is sampled per
individual.  A ratio whose denominator vanishes reads zero.  The constant `½` is not improved here.

## Empirical status

None.  The bodies here are inequalities of the logarithm proved from derivative signs, the
Cauchy–Schwarz inequality for finite sums, and integrals of continuous observables against Markov
kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndMutualInformationPinsker

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndLogLossLaw EndToEndLogLossBounds
open InformationTheory Set
open scoped Matrix NNReal

noncomputable section

/-! ## A second-order lower bound on the entropy integrand -/

/-- The logarithmic factor `(t + 1) log t - 2 (t - 1)`, whose sign is the sign of `t - 1`. -/
def logFactor (t : ℝ) : ℝ :=
  (t + 1) * Real.log t - 2 * (t - 1)

/-- The logarithmic factor has derivative `log t + (t + 1) / t - 2` on the positive reals. -/
theorem hasDerivAt_logFactor (t : ℝ) (ht : 0 < t) :
    HasDerivAt logFactor (1 * Real.log t + (t + 1) * t⁻¹ - 2 * 1) t := by
  have hlinear := (hasDerivAt_id' (x := t)).add_const 1
  have hprimary := hlinear.fun_mul (Real.hasDerivAt_log ht.ne')
  have hsecondary := ((hasDerivAt_id' (x := t)).sub_const 1).const_mul 2
  exact hprimary.fun_sub hsecondary

/-- **The logarithmic factor has the sign of `t - 1`.**  Its derivative is
`log t + 1 / t - 1 ≥ 0`, so it increases on the positive reals, and it vanishes at `t = 1`. -/
theorem logFactor_sign (t : ℝ) (ht : 0 < t) : 0 ≤ (t - 1) * logFactor t := by
  have hmono : MonotoneOn logFactor (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro s hs
      exact (hasDerivAt_logFactor s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [isOpen_Ioi.interior_eq] at hs
      exact (hasDerivAt_logFactor s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [isOpen_Ioi.interior_eq] at hs
      rw [(hasDerivAt_logFactor s hs).deriv]
      have hinverse := Real.one_sub_inv_le_log_of_pos hs
      have hsplit : (s + 1) * s⁻¹ = 1 + s⁻¹ := by
        rw [add_mul, one_mul, mul_inv_cancel₀ hs.ne']
      linarith
  have hone : logFactor 1 = 0 := by simp [logFactor]
  have hunit : (0 : ℝ) < 1 := zero_lt_one
  rcases le_total t 1 with hle | hge
  · have hvalue := hmono ht hunit hle
    rw [hone] at hvalue
    have hproduct := mul_nonneg (sub_nonneg.mpr hle) (neg_nonneg.mpr hvalue)
    linarith
  · have hvalue := hmono hunit ht hge
    rw [hone] at hvalue
    exact mul_nonneg (sub_nonneg.mpr hge) hvalue

/-- The second-order gap `(2t + 4) klFun t - 3 (t - 1)²` of the entropy integrand
`klFun t = t log t + 1 - t`. -/
def padeGap (t : ℝ) : ℝ :=
  (2 * t + 4) * klFun t - 3 * ((t - 1) * (t - 1))

/-- The second-order gap has derivative `4 logFactor t` on the positive reals. -/
theorem hasDerivAt_padeGap (t : ℝ) (ht : 0 < t) : HasDerivAt padeGap (4 * logFactor t) t := by
  have hlinear := ((hasDerivAt_id' (x := t)).const_mul 2).add_const 4
  have hproduct := hlinear.fun_mul (hasDerivAt_klFun ht.ne')
  have hshift := (hasDerivAt_id' (x := t)).sub_const 1
  have hsquare := (hshift.fun_mul hshift).const_mul 3
  refine (hproduct.fun_sub hsquare).congr_deriv ?_
  rw [klFun_apply, logFactor]
  ring

/-- **The second-order lower bound on the entropy integrand**: `3 (t - 1)² ≤ (2t + 4) klFun t` for
`t ≥ 0`.  The gap vanishes at `t = 1` and its derivative has the sign of `t - 1`, so it decreases
on `[0, 1]` and increases on `[1, ∞)`. -/
theorem padeGap_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ padeGap t := by
  have hcontinuous : Continuous padeGap := by
    unfold padeGap
    exact ((by fun_prop : Continuous fun s : ℝ ↦ 2 * s + 4).mul continuous_klFun).sub
      (by fun_prop : Continuous fun s : ℝ ↦ 3 * ((s - 1) * (s - 1)))
  have hone : padeGap 1 = 0 := by simp [padeGap, klFun_one]
  have hderiv : ∀ s : ℝ, 0 < s → deriv padeGap s = 4 * logFactor s := fun s hs ↦
    (hasDerivAt_padeGap s hs).deriv
  rcases le_total t 1 with hle | hge
  · have hanti : AntitoneOn padeGap (Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcontinuous.continuousOn ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs
        exact (hasDerivAt_padeGap s hs.1).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [hderiv s hs.1]
        have hsign := logFactor_sign s hs.1
        have hbelow : s - 1 < 0 := by linarith [hs.2]
        by_contra hpositive
        have hfactor : 0 < logFactor s := by linarith
        have hproduct := mul_neg_of_neg_of_pos hbelow hfactor
        linarith
    have hvalue := hanti ⟨ht, hle⟩ ⟨zero_le_one, le_rfl⟩ hle
    linarith
  · have hmono : MonotoneOn padeGap (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) hcontinuous.continuousOn ?_ ?_
      · intro s hs
        rw [interior_Ici] at hs
        exact (hasDerivAt_padeGap s (zero_lt_one.trans hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        rw [hderiv s (zero_lt_one.trans hs)]
        have hsign := logFactor_sign s (zero_lt_one.trans hs)
        have habove : 0 < s - 1 := by linarith [hs]
        by_contra hnegative
        have hfactor : logFactor s < 0 := by linarith
        have hproduct := mul_neg_of_pos_of_neg habove hfactor
        linarith
    have hvalue := hmono left_mem_Ici hge hge
    linarith

/-- **A lower bound for the corpus quadratic factor**: `3 / (2t + 4) ≤ quadraticFactor t` for
`t ≥ 0`, beside its upper bound `1` (`EntropyQuadraticFactor.quadraticFactor_bounds`). -/
theorem quadraticFactor_ge (t : ℝ) (ht : 0 ≤ t) :
    3 / (2 * t + 4) ≤ EntropyQuadraticFactor.quadraticFactor t := by
  have hgap := padeGap_nonneg t ht
  have hpositive : 0 < 2 * t + 4 := by linarith
  by_cases hone : t = 1
  · subst hone
    norm_num [EntropyQuadraticFactor.quadraticFactor]
  · have hsquare : 0 < (t - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hone)
    simp only [EntropyQuadraticFactor.quadraticFactor, if_neg hone]
    rw [div_le_div_iff₀ hpositive hsquare]
    unfold padeGap at hgap
    have hexpand : (t - 1) ^ 2 = (t - 1) * (t - 1) := sq (t - 1)
    rw [hexpand]
    linarith

/-- **The second-order bound for a divergence summand**:
`3 (x - y)² ≤ (2x + 4y) (x log (x / y) - x + y)` for a mass `x ≥ 0` against a mass `y > 0`. -/
theorem sq_sub_le_mul_divergenceTerm (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    3 * (x - y) ^ 2 ≤ (2 * x + 4 * y) * divergenceTerm x y := by
  obtain ⟨t, rfl⟩ : ∃ t, x = t * y := ⟨x / y, (div_mul_cancel₀ x hy.ne').symm⟩
  have ht : 0 ≤ t := le_of_mul_le_mul_right (by rw [zero_mul]; exact hx) hy
  have hproduct := mul_nonneg (sq_nonneg y) (padeGap_nonneg t ht)
  have hidentity : (2 * (t * y) + 4 * y) * divergenceTerm (t * y) y - 3 * (t * y - y) ^ 2
      = y ^ 2 * padeGap t := by
    rw [divergenceTerm, mul_div_cancel_right₀ t hy.ne', padeGap, klFun_apply]
    ring
  linarith

/-! ## Pinsker's inequality -/

/-- **Pinsker's inequality for finite laws.**  For two finite laws `p` and `q` with `q > 0` wherever
`p > 0`, `(Σ |p - q|)² / 2 ≤ Σ (p log (p / q) - p + q)`.  Each summand is at least
`3 (p - q)² / (2p + 4q)`, the weights `2p + 4q` sum to `6`, and Cauchy–Schwarz gives `3 / 6`. -/
theorem pinsker_finite {Report : Type*} [Fintype Report] (p q : FiniteReportLaw Report)
    (hsupport : ∀ report, 0 < p.mass report → 0 < q.mass report) :
    (∑ report, |p.mass report - q.mass report|) ^ 2 / 2
      ≤ ∑ report, divergenceTerm (p.mass report) (q.mass report) := by
  have hweight : ∀ report, 0 ≤ 2 * p.mass report + 4 * q.mass report := fun report ↦ by
    linarith [p.mass_nonneg report, q.mass_nonneg report]
  have hdivergence : ∀ report, 0 ≤ divergenceTerm (p.mass report) (q.mass report) :=
    fun report ↦ divergenceTerm_nonneg _ _ (p.mass_nonneg report) (q.mass_nonneg report)
      (hsupport report)
  have hcell : ∀ report, Real.sqrt 3 * |p.mass report - q.mass report|
      ≤ Real.sqrt (2 * p.mass report + 4 * q.mass report)
        * Real.sqrt (divergenceTerm (p.mass report) (q.mass report)) := by
    intro report
    rcases (q.mass_nonneg report).eq_or_lt with hzero | hpos
    · have hmass : p.mass report = 0 := by
        rcases (p.mass_nonneg report).eq_or_lt with hp | hp
        · exact hp.symm
        · exfalso
          linarith [hsupport report hp]
      rw [hmass, ← hzero, sub_zero, abs_zero, mul_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · rw [← Real.sqrt_mul (hweight report), ← Real.sqrt_sq_eq_abs,
        ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      exact Real.sqrt_le_sqrt (sq_sub_le_mul_divergenceTerm _ _ (p.mass_nonneg report) hpos)
  have hsum : Real.sqrt 3 * ∑ report, |p.mass report - q.mass report|
      ≤ ∑ report, Real.sqrt (2 * p.mass report + 4 * q.mass report)
        * Real.sqrt (divergenceTerm (p.mass report) (q.mass report)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun report _ ↦ hcell report
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun report ↦ Real.sqrt (2 * p.mass report + 4 * q.mass report))
    (fun report ↦ Real.sqrt (divergenceTerm (p.mass report) (q.mass report)))
  simp only [Real.sq_sqrt (hweight _), Real.sq_sqrt (hdivergence _)] at hcauchy
  have hweights : ∑ report, (2 * p.mass report + 4 * q.mass report) = 6 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.mass_sum, q.mass_sum]
    norm_num
  rw [hweights] at hcauchy
  have hleft : 0 ≤ Real.sqrt 3 * ∑ report, |p.mass report - q.mass report| :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun report _ ↦ abs_nonneg _)
  have hsquare := mul_self_le_mul_self hleft hsum
  have hthree : Real.sqrt 3 * ∑ report, |p.mass report - q.mass report|
      * (Real.sqrt 3 * ∑ report, |p.mass report - q.mass report|)
      = 3 * (∑ report, |p.mass report - q.mass report|) ^ 2 := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3), sq]
  have hright : (∑ report, Real.sqrt (2 * p.mass report + 4 * q.mass report)
        * Real.sqrt (divergenceTerm (p.mass report) (q.mass report)))
      * ∑ report, Real.sqrt (2 * p.mass report + 4 * q.mass report)
        * Real.sqrt (divergenceTerm (p.mass report) (q.mass report))
      = (∑ report, Real.sqrt (2 * p.mass report + 4 * q.mass report)
        * Real.sqrt (divergenceTerm (p.mass report) (q.mass report))) ^ 2 := (sq _).symm
  linarith

section ScoreOutcome

variable {Score : Type*} [Fintype Score]

/-- The products `q_s p_b` of the marginals of a score-outcome law sum to one. -/
theorem sum_productMarginals (law : FiniteReportLaw (Score × Bool)) :
    ∑ cell : Score × Bool, scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2
      = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, (law.pushforward Prod.snd).mass_sum, mul_one, sum_scoreGroupMass]

/-- The product of the marginals of a score-outcome law, as a report law. -/
def productMarginalLaw (law : FiniteReportLaw (Score × Bool)) : FiniteReportLaw (Score × Bool) where
  mass cell := scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2
  mass_nonneg cell := productMarginals_nonneg law cell
  mass_sum := sum_productMarginals law

/-- The mass of the product of the marginals at a cell is `q_s p_b`. -/
theorem productMarginalLaw_mass (law : FiniteReportLaw (Score × Bool)) (cell : Score × Bool) :
    (productMarginalLaw law).mass cell
      = scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2 :=
  rfl

/-- **The independence gap** `Σ_{s,b} |m_{s,b} - q_s p_b|`: the `L¹` distance of a score-outcome
law from the product of its marginals. -/
def independenceGap (law : FiniteReportLaw (Score × Bool)) : ℝ :=
  ∑ cell, |law.mass cell - scoreGroupMass law cell.1 * (law.pushforward Prod.snd).mass cell.2|

/-- **The independence gap is twice the total variation** from the product of the marginals, in
the corpus `FiniteReportLaw.totalVariation`. -/
theorem independenceGap_eq_two_mul_totalVariation (law : FiniteReportLaw (Score × Bool)) :
    independenceGap law = 2 * law.totalVariation (productMarginalLaw law) := by
  rw [FiniteReportLaw.totalVariation_eq_half_sum_abs, independenceGap]
  simp only [productMarginalLaw_mass]
  ring

/-- **Pinsker's inequality for the report law**: `I(S; Y) ≥ ½ (Σ_{s,b} |m_{s,b} - q_s p_b|)²`. -/
theorem half_sq_independenceGap_le_mutualInformation (law : FiniteReportLaw (Score × Bool)) :
    independenceGap law ^ 2 / 2 ≤ mutualInformation law := by
  rw [mutualInformation_eq_sum_divergenceTerm]
  exact pinsker_finite law (productMarginalLaw law) (productMarginals_pos law)

/-- **Pinsker's inequality in total-variation form**: `2 TV(law, q ⊗ p)² ≤ I(S; Y)`. -/
theorem two_mul_sq_totalVariation_le_mutualInformation (law : FiniteReportLaw (Score × Bool)) :
    2 * law.totalVariation (productMarginalLaw law) ^ 2 ≤ mutualInformation law := by
  have hpinsker := half_sq_independenceGap_le_mutualInformation law
  rw [independenceGap_eq_two_mul_totalVariation] at hpinsker
  have hscale : (2 * law.totalVariation (productMarginalLaw law)) ^ 2 / 2
      = 2 * law.totalVariation (productMarginalLaw law) ^ 2 := by ring
  linarith

/-- **Pseudo-`R²` is bounded below by the independence gap**:
`gap² / (2 H(Y)) ≤ I(S; Y) / H(Y)`, both sides read as zero when `H(Y) = 0`. -/
theorem sq_independenceGap_div_le_pseudoRSquared (law : FiniteReportLaw (Score × Bool)) :
    independenceGap law ^ 2 / (2 * reportEntropy (law.pushforward Prod.snd))
      ≤ mutualInformation law / reportEntropy (law.pushforward Prod.snd) := by
  have hentropy : 0 ≤ reportEntropy (law.pushforward Prod.snd) :=
    (mutualInformation_nonneg law).trans (mutualInformation_le_outcomeEntropy law)
  rw [← div_div]
  exact div_le_div_of_nonneg_right (half_sq_independenceGap_le_mutualInformation law) hentropy

end ScoreOutcome

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score : Type*} [Fintype Score] [DecidableEq Score]

/-! ## Pinsker's inequality through a kernel -/

/-- The independence gap of the report law of a deme is a continuous observable of the frequency
state. -/
theorem continuous_independenceGap (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    Continuous fun y : FrequencyState Deme Locus Allele ↦
      independenceGap ((stateLaw y deme).pushforward report) := by
  have hpoint : (fun y : FrequencyState Deme Locus Allele ↦
      independenceGap ((stateLaw y deme).pushforward report))
      = fun y ↦ ∑ cell : Score × Bool, |((stateLaw y deme).pushforward report).mass cell
        - scoreGroupMass ((stateLaw y deme).pushforward report) cell.1
          * ∑ group, ((stateLaw y deme).pushforward report).mass (group, cell.2)| :=
    funext fun y ↦ by simp only [independenceGap, pushforward_snd_mass]
  rw [hpoint]
  exact continuous_finset_sum _ fun cell _ ↦ ((continuous_pushforwardMass deme report cell).sub
    (((continuous_pushforwardMass deme report (cell.1, false)).add
      (continuous_pushforwardMass deme report (cell.1, true))).mul
      (continuous_finset_sum _ fun group _ ↦
        continuous_pushforwardMass deme report (group, cell.2)))).abs

/-- **Pinsker's inequality under a kernel**: the expected mutual information is at least half the
expected square of the independence gap. -/
theorem half_integral_sq_independenceGap_le_expectedMutualInformation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    (∫ y, independenceGap ((stateLaw y deme).pushforward report) ^ 2 ∂(κ x0)) / 2
      ≤ expectedMutualInformation κ x0 deme report := by
  have hsquare := integrable_continuousObservable κ x0
    ((continuous_independenceGap deme report).pow 2)
  have hinformation := integrable_continuousObservable κ x0
    (continuous_mutualInformation deme report)
  unfold expectedMutualInformation
  rw [← integral_div]
  exact integral_mono (hsquare.div_const 2) hinformation fun y ↦
    half_sq_independenceGap_le_mutualInformation _

/-- **Pinsker's inequality for the expected independence gap**: `E I ≥ ½ (E gap)²`, since
`E gap ≤ √(E gap²)` (`EndToEndBrierLaw.meanAbs_le_sqrt_meanSquare`). -/
theorem half_sq_integral_independenceGap_le_expectedMutualInformation
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    (∫ y, independenceGap ((stateLaw y deme).pushforward report) ∂(κ x0)) ^ 2 / 2
      ≤ expectedMutualInformation κ x0 deme report := by
  have hgap := integrable_continuousObservable κ x0 (continuous_independenceGap deme report)
  have hsquare := integrable_continuousObservable κ x0
    ((continuous_independenceGap deme report).pow 2)
  have hnonneg : ∀ y : FrequencyState Deme Locus Allele,
      0 ≤ independenceGap ((stateLaw y deme).pushforward report) := fun y ↦
    Finset.sum_nonneg fun cell _ ↦ abs_nonneg _
  have hroot := meanAbs_le_sqrt_meanSquare (κ x0) hgap hsquare
  simp only [abs_of_nonneg (hnonneg _)] at hroot
  have hmeanNonneg : 0 ≤ ∫ y, independenceGap ((stateLaw y deme).pushforward report) ∂(κ x0) :=
    integral_nonneg hnonneg
  have hsquareNonneg : 0 ≤ ∫ y, independenceGap ((stateLaw y deme).pushforward report) ^ 2
      ∂(κ x0) := integral_nonneg fun y ↦ sq_nonneg _
  have hmean := mul_self_le_mul_self hmeanNonneg hroot
  rw [Real.mul_self_sqrt hsquareNonneg, ← sq] at hmean
  exact (div_le_div_of_nonneg_right hmean (by norm_num)).trans
    (half_integral_sq_independenceGap_le_expectedMutualInformation κ x0 deme report)

/-- **Pseudo-`R²` is bounded below by the expected independence gap**:
`(E gap)² / (2 E H(Y)) ≤ E I / E H(Y)`. -/
theorem sq_integral_independenceGap_div_le_expectedPseudoRSquared
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    (∫ y, independenceGap ((stateLaw y deme).pushforward report) ∂(κ x0)) ^ 2
        / (2 * expectedEntropy κ x0 deme (fun hap ↦ (report hap).2))
      ≤ expectedPseudoRSquared κ x0 deme report := by
  have hentropy : 0 ≤ expectedEntropy κ x0 deme (fun hap ↦ (report hap).2) :=
    (expectedMutualInformation_nonneg κ x0 deme report).trans
      (expectedMutualInformation_le_expectedEntropy κ x0 deme report)
  unfold expectedPseudoRSquared
  rw [← div_div]
  exact div_le_div_of_nonneg_right
    (half_sq_integral_independenceGap_le_expectedMutualInformation κ x0 deme report) hentropy

/-- **Pinsker's inequality along a history of epochs, splits and pulses.** -/
theorem pinsker_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) :
    (∫ y, independenceGap ((stateLaw y deme).pushforward report) ^ 2
        ∂(historyEventKernel ℓ₀ hap₀ events x0)) / 2
      ≤ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report
    ∧ (∫ y, independenceGap ((stateLaw y deme).pushforward report)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)) ^ 2 / 2
      ≤ expectedMutualInformation (historyEventKernel ℓ₀ hap₀ events) x0 deme report
    ∧ (∫ y, independenceGap ((stateLaw y deme).pushforward report)
        ∂(historyEventKernel ℓ₀ hap₀ events x0)) ^ 2
        / (2 * expectedEntropy (historyEventKernel ℓ₀ hap₀ events) x0 deme
          (fun hap ↦ (report hap).2))
      ≤ expectedPseudoRSquared (historyEventKernel ℓ₀ hap₀ events) x0 deme report := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ events
  exact ⟨half_integral_sq_independenceGap_le_expectedMutualInformation _ x0 deme report,
    half_sq_integral_independenceGap_le_expectedMutualInformation _ x0 deme report,
    sq_integral_independenceGap_div_le_expectedPseudoRSquared _ x0 deme report⟩

/-- **Pinsker's inequality along a time-varying rate history.** -/
theorem pinsker_rateHistoryKernel {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T) (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele) (x0 : FrequencyState Deme Locus Allele)
    (deme : Deme) (report : FullHaplotype Locus Allele → Score × Bool) :
    (∫ y, independenceGap ((stateLaw y deme).pushforward report) ^ 2
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)) / 2
      ≤ expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
    ∧ (∫ y, independenceGap ((stateLaw y deme).pushforward report)
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)) ^ 2 / 2
      ≤ expectedMutualInformation (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report
    ∧ (∫ y, independenceGap ((stateLaw y deme).pushforward report)
        ∂(rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous x0)) ^ 2
        / (2 * expectedEntropy (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme
          (fun hap ↦ (report hap).2))
      ≤ expectedPseudoRSquared (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x0 deme report := by
  haveI := isMarkovKernel_rateHistoryKernel hT hcontinuous ℓ₀ hap₀
  exact ⟨half_integral_sq_independenceGap_le_expectedMutualInformation _ x0 deme report,
    half_sq_integral_independenceGap_le_expectedMutualInformation _ x0 deme report,
    sq_integral_independenceGap_div_le_expectedPseudoRSquared _ x0 deme report⟩

end

end Descent.Portability.EndToEndMutualInformationPinsker
