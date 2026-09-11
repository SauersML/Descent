/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeMicroscopicStages
import Descent.Portability.KernelRealizationPreservation

assert_below Descent.Decision Descent.Program

/-!
# The neutral microscopic approximation realizes the dual moments

This module discharges the forward-moment hypothesis of NOTE1 (20) for every neutral model.
`PartialHaplotypeDualSemigroup.expectedMomentVector_eq_matrixExponential` assumes an expectation
family over population states whose expected configuration moments obey the forward moment
equation.  Such a family exists: at every time `t ≥ 0` there is a finitely supported law on
multi-deme haplotype-frequency states whose budget-respecting configuration moments are
`e^{tQ} H(x₀)`, and the Dirac mixtures at these laws satisfy the forward equation.

The construction is NOTE1 Theorem 1 applied to the partial-haplotype carrier.  The physical
kernel `neutralMicroscopicKernel` picks one of `S = |demes| + 1` stages uniformly: the drift stage
of `PartialHaplotypeMicroscopicStages` at fraction `S h κ`, or the resampling stage of one deme at
fraction `√(S h c_i)`.  For every frequency polynomial the kernel advances the polynomial by `h`
times the neutral generator, up to `h · C √h` for small steps (`expansion_small`) and a crude
bound for large steps (`expansion_large`).  Applied to the budget-moment feature, whose generator
image is the dual generator by (19) in matrix form, this is a `MicroscopicApproximation` of the
dual generator (`neutralMicroscopicApproximation`).  The corpus theorem
`KernelRealizationPreservation.exp_mulVec_mem_realizationBody` then keeps the realization body
invariant under `e^{tQ}` (`dualPropagator_mem_realizationBody`), and Carathéodory gives the
finitely supported law (`realizedLaw`).

`realizedExpectation` is the Dirac mixture at that law.  Its expected moment vector is
`e^{tQ} H(x₀)` (`expectedMomentVector_realizedExpectation`), and it satisfies the forward moment
equation with no hypothesis (`realizedExpectation_forward`).

Scope.  The realized family matches the diffusion on the budget-respecting moments of one fixed
budget; it is not shown to be the marginal law of a single process across budgets.

## Empirical status

None.  The bodies here are algebra and elementary inequalities about polynomials and finite
mixtures of population states, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeMicroscopicApproximation

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open PartialHaplotypeLineTaylor PartialHaplotypeMicroscopicStages NeutralFellerGenerator
open FiniteMixtureKernel RealizationBody KernelRealizationPreservation
open Descent.Coalescent Descent.Foundations MvPolynomial Filter Topology

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## The mixture kernel -/

/-- The number of stages: one drift stage and one resampling stage per deme. -/
def stageCount (Deme : Type*) [Fintype Deme] : ℝ :=
  (Fintype.card Deme : ℝ) + 1

/-- There is at least one stage. -/
theorem one_le_stageCount : 1 ≤ stageCount Deme := by
  unfold stageCount
  linarith [(Nat.cast_nonneg (Fintype.card Deme) : (0 : ℝ) ≤ Fintype.card Deme)]

/-- The drift fraction at step size `h`: `S h κ`, clamped to the unit interval. -/
def driftFraction (rates : NeutralRates Deme Locus Allele) (h : ℝ) : ℝ :=
  min (stageCount Deme * max h 0 * rateScale rates) 1

/-- The drift fraction lies in the unit interval. -/
theorem driftFraction_mem (rates : NeutralRates Deme Locus Allele) (h : ℝ) :
    0 ≤ driftFraction rates h ∧ driftFraction rates h ≤ 1 := by
  have hS := one_le_stageCount (Deme := Deme)
  have hκ := one_le_rateScale rates
  exact ⟨le_min (mul_nonneg (mul_nonneg (by linarith) (le_max_right h 0)) (by linarith))
    zero_le_one, min_le_right _ _⟩

/-- The resampling fraction of deme `i` at step size `h`: `√(S h c_i)`, clamped to the unit
interval. -/
def resamplingFraction (rates : NeutralRates Deme Locus Allele) (i : Deme) (h : ℝ) : ℝ :=
  min (Real.sqrt (stageCount Deme * max h 0 * rates.coalescence i)) 1

/-- The resampling fraction lies in the unit interval. -/
theorem resamplingFraction_mem (rates : NeutralRates Deme Locus Allele) (i : Deme) (h : ℝ) :
    0 ≤ resamplingFraction rates i h ∧ resamplingFraction rates i h ≤ 1 :=
  ⟨le_min (Real.sqrt_nonneg _) zero_le_one, min_le_right _ _⟩

/-- The drift stage move at step size `h`. -/
def driftStageMove (rates : NeutralRates Deme Locus Allele) (h : ℝ)
    (x : FrequencyState Deme Locus Allele) : FrequencyState Deme Locus Allele :=
  driftMove rates (driftFraction rates h) (driftFraction_mem rates h).1
    (driftFraction_mem rates h).2 x

/-- The resampling stage move of deme `i` toward haplotype `g` at step size `h`. -/
def resamplingStageMove (rates : NeutralRates Deme Locus Allele) (h : ℝ) (i : Deme)
    (g : FullHaplotype Locus Allele) (x : FrequencyState Deme Locus Allele) :
    FrequencyState Deme Locus Allele :=
  resamplingMove i g (resamplingFraction rates i h) (resamplingFraction_mem rates i h).1
    (resamplingFraction_mem rates i h).2 x

/-- **The neutral microscopic kernel.**  With probability `1 / S` the drift stage runs; with
probability `x_i[g] / S` the resampling stage of deme `i` draws haplotype `g`. -/
def neutralMicroscopicKernel (rates : NeutralRates Deme Locus Allele) (h : ℝ) :
    FiniteMixtureKernel (Option (Deme × FullHaplotype Locus Allele))
      (FrequencyState Deme Locus Allele) where
  weight x b := b.elim (stageCount Deme)⁻¹ fun c ↦ (stageCount Deme)⁻¹ * x.1 c
  move b x := b.elim (driftStageMove rates h x) fun c ↦ resamplingStageMove rates h c.1 c.2 x
  weight_nonneg x b := by
    have hS := one_le_stageCount (Deme := Deme)
    cases b with
    | none => exact inv_nonneg.mpr (by linarith)
    | some c => exact mul_nonneg (inv_nonneg.mpr (by linarith)) (x.2.1 c)
  weight_sum x := by
    have hS := one_le_stageCount (Deme := Deme)
    have hS0 : stageCount Deme ≠ 0 := ne_of_gt (by linarith)
    rw [Fintype.sum_option]
    simp only [Option.elim, ← Finset.mul_sum, Fintype.sum_prod_type, x.2.2, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
    unfold stageCount
    ring

/-- The kernel averages the drift stage and the resampling stages. -/
theorem apply_neutralMicroscopicKernel (rates : NeutralRates Deme Locus Allele) (h : ℝ)
    (f : FrequencyState Deme Locus Allele → ℝ) (x : FrequencyState Deme Locus Allele) :
    (neutralMicroscopicKernel rates h).apply f x
      = (stageCount Deme)⁻¹ * (f (driftStageMove rates h x)
          + ∑ i, ∑ g, x.1 (i, g) * f (resamplingStageMove rates h i g x)) := by
  simp only [FiniteMixtureKernel.apply, neutralMicroscopicKernel, Fintype.sum_option, Option.elim,
    Fintype.sum_prod_type, mul_add, Finset.mul_sum, mul_assoc]

/-! ## Expansions -/

/-- The step size below which no stage fraction is clamped. -/
def smallStep (rates : NeutralRates Deme Locus Allele) : ℝ :=
  (stageCount Deme * rateScale rates * (1 + ∑ i, rates.coalescence i))⁻¹

/-- The total coalescence rate is nonnegative. -/
theorem sum_coalescence_nonneg (rates : NeutralRates Deme Locus Allele) :
    0 ≤ ∑ i, rates.coalescence i :=
  Finset.sum_nonneg fun i _ ↦ rates.coalescence_nonneg i

/-- The unclamped step bound is positive. -/
theorem smallStep_pos (rates : NeutralRates Deme Locus Allele) : 0 < smallStep rates := by
  have hS := one_le_stageCount (Deme := Deme)
  have hκ := one_le_rateScale rates
  have hc := sum_coalescence_nonneg rates
  unfold smallStep
  positivity

/-- Below the small step, the step times the clamping denominator is at most one. -/
theorem mul_denominator_le_one (rates : NeutralRates Deme Locus Allele) (h : ℝ) (hh0 : 0 ≤ h)
    (hsmall : h ≤ smallStep rates) :
    h * (stageCount Deme * rateScale rates * (1 + ∑ i, rates.coalescence i)) ≤ 1 := by
  have hS := one_le_stageCount (Deme := Deme)
  have hκ := one_le_rateScale rates
  have hc := sum_coalescence_nonneg rates
  have hD : 0 < stageCount Deme * rateScale rates * (1 + ∑ i, rates.coalescence i) := by
    positivity
  calc h * (stageCount Deme * rateScale rates * (1 + ∑ i, rates.coalescence i))
      ≤ smallStep rates * (stageCount Deme * rateScale rates * (1 + ∑ i, rates.coalescence i)) :=
        mul_le_mul_of_nonneg_right hsmall hD.le
    _ = 1 := by rw [smallStep, inv_mul_cancel₀ hD.ne']

/-- Below the small step the drift fraction is unclamped. -/
theorem driftFraction_of_le (rates : NeutralRates Deme Locus Allele) (h : ℝ) (hh0 : 0 ≤ h)
    (hsmall : h ≤ smallStep rates) :
    driftFraction rates h = stageCount Deme * h * rateScale rates := by
  have hS := one_le_stageCount (Deme := Deme)
  have hκ := one_le_rateScale rates
  have hc := sum_coalescence_nonneg rates
  have hbound := mul_denominator_le_one rates h hh0 hsmall
  rw [driftFraction, max_eq_left hh0, min_eq_left]
  nlinarith [mul_nonneg (mul_nonneg hh0 (by linarith : (0 : ℝ) ≤ stageCount Deme))
    (by linarith : (0 : ℝ) ≤ rateScale rates)]

/-- Below the small step the resampling fraction is unclamped. -/
theorem resamplingFraction_of_le (rates : NeutralRates Deme Locus Allele) (i : Deme) (h : ℝ)
    (hh0 : 0 ≤ h) (hsmall : h ≤ smallStep rates) :
    resamplingFraction rates i h = Real.sqrt (stageCount Deme * h * rates.coalescence i) := by
  have hS := one_le_stageCount (Deme := Deme)
  have hκ := one_le_rateScale rates
  have hc := sum_coalescence_nonneg rates
  have hci : rates.coalescence i ≤ ∑ j, rates.coalescence j :=
    Finset.single_le_sum (fun j _ ↦ rates.coalescence_nonneg j) (Finset.mem_univ i)
  have hbound := mul_denominator_le_one rates h hh0 hsmall
  have hinner : stageCount Deme * h * rates.coalescence i ≤ 1 := by
    have h1 : stageCount Deme * h * rates.coalescence i
        ≤ h * (stageCount Deme * rateScale rates * (1 + ∑ j, rates.coalescence j)) := by
      have hSh : 0 ≤ stageCount Deme * h := mul_nonneg (by linarith) hh0
      nlinarith [rates.coalescence_nonneg i]
    linarith
  rw [resamplingFraction, max_eq_left hh0, min_eq_left]
  rw [Real.sqrt_le_one]
  exact hinner

/-- The constant of the small-step remainder. -/
def smallConstant (rates : NeutralRates Deme Locus Allele) (B : ℝ) : ℝ :=
  2 * B * stageCount Deme * rateScale rates ^ 2
    + B * ∑ i, rates.coalescence i * Real.sqrt (stageCount Deme * rates.coalescence i)

/-- The small-step constant is nonnegative. -/
theorem smallConstant_nonneg (rates : NeutralRates Deme Locus Allele) (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ smallConstant rates B := by
  have hS := one_le_stageCount (Deme := Deme)
  unfold smallConstant
  have hsum : 0 ≤ ∑ i, rates.coalescence i * Real.sqrt (stageCount Deme * rates.coalescence i) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (rates.coalescence_nonneg i) (Real.sqrt_nonneg _)
  have hκ : 0 ≤ rateScale rates ^ 2 := sq_nonneg _
  positivity

/-- The value of the neutral generator: the drift derivative plus half the coalescence rate
times each deme's Wright–Fisher operator. -/
theorem eval_neutralGenerator_eq (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (p : FrequencyPolynomial Deme Locus Allele) :
    eval x (neutralGenerator rates p)
      = eval x (∑ u, driftPolynomial rates u * pderiv u p)
        + ∑ i, rates.coalescence i / 2 * eval x (demeSecondOrder i p) := by
  simp only [neutralGenerator, map_add, map_sum, map_mul, eval_C]

/-- **The small-step expansion.**  For step sizes up to `smallStep`, the microscopic kernel
advances a frequency polynomial by `h` times the neutral generator, up to `h · C √h`. -/
theorem expansion_small (rates : NeutralRates Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x v : FrequencyVariable Deme Locus Allele → ℝ, (∀ u, |x u| ≤ 1) → (∀ u, |v u| ≤ 2) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        |secondDirectionalDerivative p x v| ≤ B ∧ |lineRemainder p x v ε| ≤ B * ε ^ 3)
    (h : ℝ) (hh0 : 0 < h) (hsmall : h ≤ smallStep rates) (x : FrequencyState Deme Locus Allele) :
    |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x - eval x.1 p
        - h * eval x.1 (neutralGenerator rates p)| ≤ h * (smallConstant rates B * Real.sqrt h) := by
  have hS := one_le_stageCount (Deme := Deme)
  have hκ := one_le_rateScale rates
  have hS0 : stageCount Deme ≠ 0 := ne_of_gt (by linarith)
  have hκ0 : rateScale rates ≠ 0 := ne_of_gt (by linarith)
  have hh1 : h ≤ 1 := by
    have hbound := mul_denominator_le_one rates h hh0.le hsmall
    have hc := sum_coalescence_nonneg rates
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ stageCount Deme * rateScale rates - 1) hh0.le,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ stageCount Deme)
        (by linarith : (0 : ℝ) ≤ rateScale rates)) (mul_nonneg hh0.le hc)]
  set εd := driftFraction rates h with hεd
  have hεd_eq : εd = stageCount Deme * h * rateScale rates :=
    driftFraction_of_le rates h hh0.le hsmall
  have hdrift := drift_expansion rates εd (driftFraction_mem rates h).1
    (driftFraction_mem rates h).2 p B hB0 hB x
  have hres : ∀ i, |∑ g, x.1 (i, g) * eval (resamplingStageMove rates h i g x).1 p - eval x.1 p
        - resamplingFraction rates i h ^ 2 / 2 * eval x.1 (demeSecondOrder i p)|
      ≤ B * resamplingFraction rates i h ^ 3 := fun i ↦
    resampling_expansion i (resamplingFraction rates i h) (resamplingFraction_mem rates i h).1
      (resamplingFraction_mem rates i h).2 p B
      (fun y v hy hv ε hε0 hε1 ↦ (hB y v hy hv ε hε0 hε1).2) x
  have hsq : ∀ i, resamplingFraction rates i h ^ 2 = stageCount Deme * h * rates.coalescence i := by
    intro i
    rw [resamplingFraction_of_le rates i h hh0.le hsmall, Real.sq_sqrt]
    exact mul_nonneg (mul_nonneg (by linarith) hh0.le) (rates.coalescence_nonneg i)
  have hcube : ∀ i, resamplingFraction rates i h ^ 3
      = h * (rates.coalescence i * Real.sqrt (stageCount Deme * rates.coalescence i))
        * (stageCount Deme * Real.sqrt h) := by
    intro i
    have hsplit : resamplingFraction rates i h ^ 3
        = resamplingFraction rates i h ^ 2 * resamplingFraction rates i h := by ring
    rw [hsplit, hsq, resamplingFraction_of_le rates i h hh0.le hsmall,
      show stageCount Deme * h * rates.coalescence i
        = (stageCount Deme * rates.coalescence i) * h by ring,
      Real.sqrt_mul (mul_nonneg (by linarith) (rates.coalescence_nonneg i))]
    ring
  set drift := eval (driftStageMove rates h x).1 p - eval x.1 p
      - εd / rateScale rates * eval x.1 (∑ u, driftPolynomial rates u * pderiv u p) with hdriftdef
  set resampling := fun i ↦ ∑ g, x.1 (i, g) * eval (resamplingStageMove rates h i g x).1 p
      - eval x.1 p - resamplingFraction rates i h ^ 2 / 2 * eval x.1 (demeSecondOrder i p)
    with hresdef
  have hidentity : (neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x - eval x.1 p
        - h * eval x.1 (neutralGenerator rates p)
      = (stageCount Deme)⁻¹ * (drift + ∑ i, resampling i) := by
    rw [apply_neutralMicroscopicKernel, eval_neutralGenerator_eq, hdriftdef, hresdef]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsq]
    have hmul : ∑ i, stageCount Deme * h * rates.coalescence i / 2 * eval x.1 (demeSecondOrder i p)
        = stageCount Deme * h * ∑ i, rates.coalescence i / 2 * eval x.1 (demeSecondOrder i p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hmul, hεd_eq]
    field_simp
    unfold stageCount
    ring
  rw [hidentity]
  have hdriftbound : |drift| ≤ 2 * B * (stageCount Deme * h * rateScale rates) ^ 2 := by
    rw [← hεd_eq]
    exact hdrift
  have hresbound : ∀ i, |resampling i|
      ≤ B * (h * (rates.coalescence i * Real.sqrt (stageCount Deme * rates.coalescence i))
        * (stageCount Deme * Real.sqrt h)) := by
    intro i
    rw [← hcube]
    exact hres i
  have hsqrt_ge : h ≤ Real.sqrt h := by
    have := Real.sqrt_le_sqrt (show h * h ≤ h by nlinarith)
    rwa [Real.sqrt_mul_self hh0.le] at this
  have hsqrt0 : 0 ≤ Real.sqrt h := Real.sqrt_nonneg h
  calc |(stageCount Deme)⁻¹ * (drift + ∑ i, resampling i)|
      = (stageCount Deme)⁻¹ * |drift + ∑ i, resampling i| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr (show (0 : ℝ) < stageCount Deme by linarith))]
    _ ≤ (stageCount Deme)⁻¹ * (|drift| + ∑ i, |resampling i|) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
          (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))) (inv_nonneg.mpr (by linarith))
    _ ≤ (stageCount Deme)⁻¹ * (2 * B * (stageCount Deme * h * rateScale rates) ^ 2
          + ∑ i, B * (h * (rates.coalescence i * Real.sqrt (stageCount Deme * rates.coalescence i))
            * (stageCount Deme * Real.sqrt h))) :=
        mul_le_mul_of_nonneg_left (add_le_add hdriftbound (Finset.sum_le_sum fun i _ ↦ hresbound i))
          (inv_nonneg.mpr (by linarith))
    _ = h * (2 * B * stageCount Deme * rateScale rates ^ 2 * h
          + B * (∑ i, rates.coalescence i * Real.sqrt (stageCount Deme * rates.coalescence i))
            * Real.sqrt h) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        field_simp
        ring
    _ ≤ h * (smallConstant rates B * Real.sqrt h) := by
        unfold smallConstant
        have hA : 0 ≤ 2 * B * stageCount Deme * rateScale rates ^ 2 := by
          have := sq_nonneg (rateScale rates)
          positivity
        have hsum : 0 ≤ ∑ i, rates.coalescence i
            * Real.sqrt (stageCount Deme * rates.coalescence i) :=
          Finset.sum_nonneg fun i _ ↦ mul_nonneg (rates.coalescence_nonneg i) (Real.sqrt_nonneg _)
        have hstep : 2 * B * stageCount Deme * rateScale rates ^ 2 * h
            ≤ 2 * B * stageCount Deme * rateScale rates ^ 2 * Real.sqrt h :=
          mul_le_mul_of_nonneg_left hsqrt_ge hA
        nlinarith [mul_nonneg hh0.le hA]

/-- **The large-step bound.**  For every step size the kernel changes a polynomial bounded by
`B` on states by at most `2 B + h B_L`, where `B_L` bounds its generator on states. -/
theorem expansion_large (rates : NeutralRates Deme Locus Allele)
    (p : FrequencyPolynomial Deme Locus Allele) (B BL : ℝ)
    (hB : ∀ y : FrequencyState Deme Locus Allele, |eval y.1 p| ≤ B)
    (hBL : ∀ y : FrequencyState Deme Locus Allele, |eval y.1 (neutralGenerator rates p)| ≤ BL)
    (h : ℝ) (hh0 : 0 ≤ h) (x : FrequencyState Deme Locus Allele) :
    |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x - eval x.1 p
        - h * eval x.1 (neutralGenerator rates p)| ≤ 2 * B + h * BL := by
  have happly : |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x| ≤ B :=
    abs_law_average_le ((neutralMicroscopicKernel rates h).weight x)
      ((neutralMicroscopicKernel rates h).weight_nonneg x)
      ((neutralMicroscopicKernel rates h).weight_sum x) _ B
      fun b ↦ hB ((neutralMicroscopicKernel rates h).move b x)
  have htriangle : ∀ a b c : ℝ, |a - b - c| ≤ |a| + |b| + |c| := by
    intro a b c
    have h1 : |a - b - c| ≤ |a - b| + |c| := by
      simpa [sub_eq_add_neg] using abs_add_le (a - b) (-c)
    have h2 : |a - b| ≤ |a| + |b| := by
      simpa [sub_eq_add_neg] using abs_add_le a (-b)
    linarith
  calc |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x - eval x.1 p
        - h * eval x.1 (neutralGenerator rates p)|
      ≤ |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x| + |eval x.1 p|
        + |h * eval x.1 (neutralGenerator rates p)| := htriangle _ _ _
    _ = |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 p) x| + |eval x.1 p|
        + h * |eval x.1 (neutralGenerator rates p)| := by
        rw [abs_mul, abs_of_nonneg hh0]
    _ ≤ B + B + h * BL :=
        add_le_add (add_le_add happly (hB x)) (mul_le_mul_of_nonneg_left (hBL x) hh0)
    _ = 2 * B + h * BL := by ring

/-! ## The microscopic approximation of the dual generator -/

/-- The budget-moment feature of a state: its configuration moments over the budget-respecting
configurations. -/
def budgetMomentFeature (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun ξ ↦ eval x.1 (momentPolynomial ξ.1)

/-- The Taylor constant of one configuration moment. -/
def momentBound (capacity : Locus → ℕ) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ℝ :=
  Classical.choose (exists_lineTaylor_bound (momentPolynomial ξ.1))

/-- The Taylor constant of the generator image of one configuration moment. -/
def generatorBound (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) : ℝ :=
  Classical.choose (exists_lineTaylor_bound (neutralGenerator rates (momentPolynomial ξ.1)))

/-- The sum of the Taylor constants of all configuration moments. -/
def featureBound (capacity : Locus → ℕ) : ℝ :=
  ∑ ξ : BudgetConfiguration Deme Locus Allele capacity, momentBound capacity ξ

/-- The sum of the Taylor constants of all generator images. -/
def generatorFeatureBound (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) : ℝ :=
  ∑ ξ : BudgetConfiguration Deme Locus Allele capacity, generatorBound rates capacity ξ

/-- Each moment constant is nonnegative and at most the summed constant, and bounds the
moment's Taylor data. -/
theorem momentBound_spec (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    0 ≤ momentBound capacity ξ ∧ momentBound capacity ξ ≤ featureBound capacity
      ∧ ∀ x v : FrequencyVariable Deme Locus Allele → ℝ, (∀ u, |x u| ≤ 1) → (∀ u, |v u| ≤ 2) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          |eval x (momentPolynomial ξ.1)| ≤ momentBound capacity ξ
            ∧ |secondDirectionalDerivative (momentPolynomial ξ.1) x v| ≤ momentBound capacity ξ
            ∧ |lineRemainder (momentPolynomial ξ.1) x v ε| ≤ momentBound capacity ξ * ε ^ 3 := by
  have hspec := Classical.choose_spec (exists_lineTaylor_bound (momentPolynomial ξ.1))
  refine ⟨hspec.1, ?_, fun x v hx hv ε hε0 hε1 ↦ ?_⟩
  · exact Finset.single_le_sum (f := fun η ↦ momentBound capacity η)
      (fun η _ ↦ (Classical.choose_spec (exists_lineTaylor_bound (momentPolynomial η.1))).1)
      (Finset.mem_univ ξ)
  · obtain ⟨h1, _, _, h4, h5⟩ := hspec.2 x v hx hv ε hε0 hε1
    exact ⟨h1, h4, h5⟩

/-- Each generator constant is at most the summed constant and bounds the generator image on
states. -/
theorem generatorBound_spec (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    generatorBound rates capacity ξ ≤ generatorFeatureBound rates capacity
      ∧ ∀ y : FrequencyState Deme Locus Allele,
        |eval y.1 (neutralGenerator rates (momentPolynomial ξ.1))|
          ≤ generatorBound rates capacity ξ := by
  have hspec := Classical.choose_spec
    (exists_lineTaylor_bound (neutralGenerator rates (momentPolynomial ξ.1)))
  refine ⟨?_, fun y ↦ ?_⟩
  · exact Finset.single_le_sum (f := fun η ↦ generatorBound rates capacity η)
      (fun η _ ↦ (Classical.choose_spec
        (exists_lineTaylor_bound (neutralGenerator rates (momentPolynomial η.1)))).1)
      (Finset.mem_univ ξ)
  · exact (hspec.2 y.1 0 (abs_state_le_one y) (fun _ ↦ by norm_num) 0 le_rfl zero_le_one).1

/-- The remainder bound of the microscopic approximation. -/
def microscopicError (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) (h : ℝ) :
    ℝ :=
  if h ≤ smallStep rates then smallConstant rates (featureBound capacity) * Real.sqrt h
  else (2 * featureBound capacity + h * generatorFeatureBound rates capacity) / h

/-- **The neutral microscopic approximation of the dual generator.**  The neutral microscopic
kernel approximates the dual generator on the budget-moment feature, as NOTE1 Theorem 1
requires. -/
def neutralMicroscopicApproximation (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) :
    MicroscopicApproximation (B := Option (Deme × FullHaplotype Locus Allele))
      (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity)
      (dualGenerator rates capacity) where
  kernel := neutralMicroscopicKernel rates
  error := microscopicError rates capacity
  error_nonneg h := by
    have hfeature : 0 ≤ featureBound (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity :=
      Finset.sum_nonneg fun ξ _ ↦ (momentBound_spec capacity ξ).1
    have hgenerator : 0 ≤ generatorFeatureBound rates capacity :=
      Finset.sum_nonneg fun ξ _ ↦ (Classical.choose_spec
        (exists_lineTaylor_bound (neutralGenerator rates (momentPolynomial ξ.1)))).1
    unfold microscopicError
    split_ifs with hsmall
    · exact mul_nonneg (smallConstant_nonneg rates _ hfeature) (Real.sqrt_nonneg h)
    · have hpos : 0 < h := (smallStep_pos rates).trans (lt_of_not_ge hsmall)
      exact div_nonneg (add_nonneg (by linarith) (mul_nonneg hpos.le hgenerator)) hpos.le
  error_tendsto := by
    have hsqrt : Tendsto (fun h : ℝ ↦ smallConstant rates (featureBound capacity) * Real.sqrt h)
        (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuous_sqrt.tendsto 0).const_mul
        (smallConstant rates (featureBound (Deme := Deme) (Locus := Locus) (Allele := Allele)
          capacity))).mono_left nhdsWithin_le_nhds
      simpa using h
    refine hsqrt.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (smallStep_pos rates)] with h hh
    simp [microscopicError, hh.2.le]
  expansion h hh x ξ := by
    have hfeature : budgetMomentFeature capacity x
        = fun η : BudgetConfiguration Deme Locus Allele capacity ↦
          configurationMoment (stateLaw x) η.1 := by
      funext η
      exact eval_momentPolynomial (stateLaw x) η.1
    have hQ : (dualGenerator rates capacity).mulVec (budgetMomentFeature capacity x) ξ
        = eval x.1 (neutralGenerator rates (momentPolynomial ξ.1)) := by
      rw [hfeature]
      exact dualGenerator_mulVec_configurationMoment rates capacity (stateLaw x) ξ
    rw [hQ]
    obtain ⟨hB0, hBle, hBspec⟩ := momentBound_spec capacity ξ
    obtain ⟨hGle, hGspec⟩ := generatorBound_spec rates capacity ξ
    show |(neutralMicroscopicKernel rates h).apply (fun y ↦ eval y.1 (momentPolynomial ξ.1)) x
        - eval x.1 (momentPolynomial ξ.1)
        - h * eval x.1 (neutralGenerator rates (momentPolynomial ξ.1))|
      ≤ h * microscopicError rates capacity h
    unfold microscopicError
    split_ifs with hsmall
    · have hsum0 : 0 ≤ featureBound (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity :=
        hB0.trans hBle
      refine expansion_small rates (momentPolynomial ξ.1) (featureBound capacity) hsum0
        (fun y v hy hv ε hε0 hε1 ↦ ?_) h hh hsmall x
      obtain ⟨_, h2, h3⟩ := hBspec y v hy hv ε hε0 hε1
      exact ⟨h2.trans hBle, h3.trans (mul_le_mul_of_nonneg_right hBle (pow_nonneg hε0 3))⟩
    · have hbound := expansion_large rates (momentPolynomial ξ.1) (featureBound capacity)
        (generatorFeatureBound rates capacity)
        (fun y ↦ ((hBspec y.1 0 (abs_state_le_one y) (fun _ ↦ by norm_num) 0 le_rfl
          zero_le_one).1).trans hBle)
        (fun y ↦ (hGspec y).trans hGle) h hh.le x
      rwa [mul_div_cancel₀ _ hh.ne']

/-! ## The realized expectation family -/

/-- The budget-moment feature is continuous. -/
theorem continuous_budgetMomentFeature (capacity : Locus → ℕ) :
    Continuous (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity) :=
  continuous_pi fun ξ ↦ (MvPolynomial.continuous_eval _).comp continuous_subtype_val

/-- **The dual propagator keeps moment vectors realizable.**  At every nonnegative time, the dual
propagator applied to the budget moments of a state lies in the realization body of the
budget-moment feature. -/
theorem dualPropagator_mem_realizationBody (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (x0 : FrequencyState Deme Locus Allele) (t : ℝ) (ht : 0 ≤ t) :
    (matrixExponential (dualGenerator rates capacity) t).mulVec (budgetMomentFeature capacity x0)
      ∈ realizationBody (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele)
        capacity) :=
  exp_mulVec_mem_realizationBody _ _ (neutralMicroscopicApproximation rates capacity)
    (isClosed_realizationBody _ (continuous_budgetMomentFeature capacity)) t ht _
    (mem_realizationBody_of_range _ x0)

/-- A finitely supported law on states with the dual moments at a nonnegative time. -/
theorem exists_realizedLaw (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (x0 : FrequencyState Deme Locus Allele) (t : ℝ) (ht : 0 ≤ t) :
    ∃ q : (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
        × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele),
      (∀ k, 0 ≤ q.1 k) ∧ ∑ k, q.1 k = 1
        ∧ featureVector q.1 q.2 (budgetMomentFeature capacity)
          = (matrixExponential (dualGenerator rates capacity) t).mulVec
              (budgetMomentFeature capacity x0) := by
  obtain ⟨p, point, hp, hsum, hfeature⟩ := exists_law_of_mem_realizationBody _ _
    (dualPropagator_mem_realizationBody rates capacity x0 t ht)
  exact ⟨(p, point), hp, hsum, hfeature⟩

/-- The realized law at time `t`, clamped to time zero for negative times. -/
def realizedLaw (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (x0 : FrequencyState Deme Locus Allele) (t : ℝ) :
    (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ)
      × (Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
        → FrequencyState Deme Locus Allele) :=
  Classical.choose (exists_realizedLaw rates capacity x0 (max t 0) (le_max_right t 0))

/-- The realized law is a probability law with the dual moments at the clamped time. -/
theorem realizedLaw_spec (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (x0 : FrequencyState Deme Locus Allele) (t : ℝ) :
    (∀ k, 0 ≤ (realizedLaw rates capacity x0 t).1 k)
      ∧ ∑ k, (realizedLaw rates capacity x0 t).1 k = 1
      ∧ featureVector (realizedLaw rates capacity x0 t).1 (realizedLaw rates capacity x0 t).2
          (budgetMomentFeature capacity)
        = (matrixExponential (dualGenerator rates capacity) (max t 0)).mulVec
            (budgetMomentFeature capacity x0) :=
  Classical.choose_spec (exists_realizedLaw rates capacity x0 (max t 0) (le_max_right t 0))

/-- The expectation of a finite mixture of population states. -/
def mixtureExpectation {n : ℕ} (weight : Fin n → ℝ) (hweight : ∀ k, 0 ≤ weight k)
    (hsum : ∑ k, weight k = 1) (point : Fin n → FrequencyState Deme Locus Allele) :
    ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)) where
  eval f := ∑ k, weight k * f (stateLaw (point k))
  add_eval f g := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_eval c f := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  const_one := by simpa using hsum
  nonneg_eval f hf := Finset.sum_nonneg fun k _ ↦ mul_nonneg (hweight k) (hf _)

/-- **The realized expectation family.**  At time `t` it is the Dirac mixture at the realized
law. -/
def realizedExpectation (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (x0 : FrequencyState Deme Locus Allele) (t : ℝ) :
    ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :=
  mixtureExpectation (realizedLaw rates capacity x0 t).1 (realizedLaw_spec rates capacity x0 t).1
    (realizedLaw_spec rates capacity x0 t).2.1 (realizedLaw rates capacity x0 t).2

/-- The realized family has the dual moments at every nonnegative time. -/
theorem expectedMomentVector_realizedExpectation (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (x0 : FrequencyState Deme Locus Allele) (t : ℝ) (ht : 0 ≤ t) :
    expectedMomentVector capacity (realizedExpectation rates capacity x0) t
      = (matrixExponential (dualGenerator rates capacity) t).mulVec
          (budgetMomentFeature capacity x0) := by
  have hspec := (realizedLaw_spec rates capacity x0 t).2.2
  rw [max_eq_left ht] at hspec
  funext ξ
  rw [← hspec, featureVector_apply]
  show ∑ k, (realizedLaw rates capacity x0 t).1 k
      * configurationMoment (stateLaw ((realizedLaw rates capacity x0 t).2 k)) ξ.1 = _
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  show (realizedLaw rates capacity x0 t).1 k
      * configurationMoment (stateLaw ((realizedLaw rates capacity x0 t).2 k)) ξ.1 = _
  rw [← eval_momentPolynomial]
  rfl

/-- **The forward moment equation holds for the realized family, with no hypothesis.**  The
realized expectation family satisfies the forward moment equation of NOTE1 (20) at every
budget-respecting configuration and every time `t ≥ 0`. -/
theorem realizedExpectation_forward (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (x0 : FrequencyState Deme Locus Allele) :
    ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt
        (fun s ↦ expectedMomentVector capacity (realizedExpectation rates capacity x0) s ξ)
        (realizedExpectation rates capacity x0 t fun law ↦
          eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        (Set.Ici 0) t := by
  intro ξ t ht
  have horbit := hasDerivAt_pi.mp
    (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec
      (dualGenerator rates capacity) (budgetMomentFeature capacity x0) t) ξ
  have hvalue : (realizedExpectation rates capacity x0 t fun law ↦
        eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
      = (dualGenerator rates capacity).mulVec
          ((matrixExponential (dualGenerator rates capacity) t).mulVec
            (budgetMomentFeature capacity x0)) ξ := by
    rw [← expectedMomentVector_realizedExpectation rates capacity x0 t ht,
      ← expectedGenerator_eq_mulVec]
  rw [hvalue]
  refine horbit.hasDerivWithinAt.congr (fun s hs ↦ ?_) ?_
  · exact congrFun (expectedMomentVector_realizedExpectation rates capacity x0 s hs) ξ
  · exact congrFun (expectedMomentVector_realizedExpectation rates capacity x0 t ht) ξ

end

end Descent.Portability.PartialHaplotypeMicroscopicApproximation
