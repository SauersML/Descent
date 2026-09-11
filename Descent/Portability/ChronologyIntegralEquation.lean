/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdmixtureChronologyLaw
import Descent.Portability.IntegrableGeneratorPropagator

assert_below Descent.Decision Descent.Program

/-!
# The chronology equations for integrable rates, in integral form

NOTE1 section 6.1 solves the admixture chronology `p' = m (1 - p)`,
`D' = -(m + r) D + m (1 - p)²` of equation (27) by the integrating factor (28).
`Descent.Portability.AdmixtureChronologyLaw` proves (27) everywhere for continuous rates, and
almost everywhere for locally integrable ones, and proves that (28) is the unique solution among
everywhere differentiable candidates when the rates are continuous.  It leaves open the case NOTE1
actually states: integrable rates, where the solutions are absolutely continuous and solve (27)
in integral form.  This module closes it.

The integral form of (27).  `integratingFactorSolution a b initial` is `e^{-A(t)} (initial +
∫₀ᵗ e^{A} b)` for the cumulative total `A` of `a`.  For continuous `a` and `b` it solves
`u(t) = initial + ∫₀ᵗ (-a u + b)` by the fundamental theorem of calculus
(`integratingFactorSolution_eq_integral_of_continuous`).  For merely integrable `a` and `b`,
`integratingFactorSolution_eq_integral` proves the same identity by approximation: continuous
coefficients within `ε` in `L¹` give solutions within a fixed multiple of `ε` of the integrable
one, uniformly on the horizon, and both sides of the equation move by a fixed multiple of `ε`.
`donorFraction_eq_integral` and `admixtureLinkage_eq_integral` are then NOTE1 (27) in integral
form for locally integrable rates, with the corpus `donorFraction` and `admixtureLinkage`.

Uniqueness.  `eq_of_linear_integral_eq` proves that the scalar linear integral equation has at
most one continuous solution on the horizon when the coefficients are integrable: the difference
of two solutions is controlled by a continuous approximation of the coefficient, Gronwall's
inequality with a continuous coefficient (`IntegrableGeneratorPropagator`) bounds it by an
arbitrarily small multiple of the approximation error, and so it vanishes.
`eq_donorFraction_of_integral_eq` and `eq_admixtureLinkage_of_integral_eq` are the uniqueness of
(27) among continuous solutions, which for integrable rates is uniqueness among absolutely
continuous solutions.

Scope.  The rates are locally integrable and of arbitrary sign in the identities; nonnegativity is
not needed.  The almost-everywhere derivative form of (27) is `AdmixtureChronologyLaw`'s.

## Empirical status

None.  The bodies here are calculus: integral identities for primitives of integrable functions,
their continuous approximation in `L¹`, and Gronwall's inequality, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ChronologyIntegralEquation

open MeasureTheory
open Descent.Portability.AdmixtureChronologyLaw
open Descent.Portability.IntegrableGeneratorPropagator

noncomputable section

/-! ## Elementary bounds -/

/-- Convexity of the exponential from above: `e^x - e^y ≤ e^x (x - y)`. -/
theorem exp_sub_exp_le_mul (x y : ℝ) : Real.exp x - Real.exp y ≤ Real.exp x * (x - y) := by
  have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - x)) (Real.exp_pos x).le
  have hexp : Real.exp x * Real.exp (y - x) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hmul
  linarith

/-- The exponential is Lipschitz with constant `e^L` on `[-L, L]`. -/
theorem abs_exp_sub_exp_le_of_abs_le {x y L : ℝ} (hx : |x| ≤ L) (hy : |y| ≤ L) :
    |Real.exp x - Real.exp y| ≤ Real.exp L * |x - y| := by
  have hxL : Real.exp x ≤ Real.exp L := Real.exp_le_exp.mpr ((le_abs_self x).trans hx)
  have hyL : Real.exp y ≤ Real.exp L := Real.exp_le_exp.mpr ((le_abs_self y).trans hy)
  have hscale : 0 ≤ Real.exp L * |x - y| := mul_nonneg (Real.exp_pos L).le (abs_nonneg _)
  rw [abs_le]
  constructor
  · have hbase := exp_sub_exp_le_mul y x
    have hcompare : Real.exp y * (y - x) ≤ Real.exp L * |x - y| := by
      rcases le_total x y with hxy | hyx
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
        exact mul_le_mul_of_nonneg_right hyL (sub_nonneg.mpr hxy)
      · have hnonpos : Real.exp y * (y - x) ≤ 0 := by nlinarith [Real.exp_pos y]
        linarith
    linarith
  · have hbase := exp_sub_exp_le_mul x y
    have hcompare : Real.exp x * (x - y) ≤ Real.exp L * |x - y| := by
      rcases le_total y x with hyx | hxy
      · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        exact mul_le_mul_of_nonneg_right hxL (sub_nonneg.mpr hyx)
      · have hnonpos : Real.exp x * (x - y) ≤ 0 := by nlinarith [Real.exp_pos x]
        linarith
    linarith

/-- The integral of a norm over a subinterval of the horizon is at most its integral over the
horizon. -/
theorem integral_norm_le_horizon {f : ℝ → ℝ} {T t : ℝ} (hf : IntervalIntegrable f volume 0 T)
    (ht : t ∈ Set.Icc 0 T) : ∫ s in (0 : ℝ)..t, ‖f s‖ ≤ ∫ s in (0 : ℝ)..T, ‖f s‖ :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (ae_of_all _ fun _ ↦ norm_nonneg _)
    hf.norm

/-- A cumulative total over a subinterval of the horizon is bounded by the integrated norm of the
rate over the horizon. -/
theorem abs_cumulativeRate_le {a : ℝ → ℝ} {T t : ℝ} (ha : IntervalIntegrable a volume 0 T)
    (ht : t ∈ Set.Icc 0 T) : |cumulativeRate a t| ≤ ∫ s in (0 : ℝ)..T, ‖a s‖ := by
  rw [← Real.norm_eq_abs]
  exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
    (integral_norm_le_horizon ha ht)

/-- A rate integrable on the horizon is integrable on every initial subinterval. -/
theorem intervalIntegrable_of_mem_horizon {f : ℝ → ℝ} {T t : ℝ}
    (hf : IntervalIntegrable f volume 0 T) (ht : t ∈ Set.Icc 0 T) :
    IntervalIntegrable f volume 0 t :=
  hf.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le ht.1 ht.2))

/-- A locally integrable rate is integrable on every interval. -/
theorem intervalIntegrable_of_locallyIntegrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  intervalIntegrable_iff.mpr
    ((hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)

/-- The cumulative total of a rate integrable on the horizon is continuous on the horizon. -/
theorem continuousOn_cumulativeRate {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) : ContinuousOn (cumulativeRate a) (Set.Icc 0 T) := by
  have hprimitive := intervalIntegral.continuousOn_primitive_interval' ha Set.left_mem_uIcc
  rwa [Set.uIcc_of_le hT] at hprimitive

/-- The cumulative total of a locally integrable rate is continuous. -/
theorem continuous_cumulativeRate_of_locallyIntegrable {a : ℝ → ℝ}
    (ha : LocallyIntegrable a volume) : Continuous (cumulativeRate a) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_of_locallyIntegrable ha) 0

/-! ## The integrating-factor solution -/

/-- The integrating-factor solution of `u' = -a u + b` from `initial` at time zero:
`e^{-A(t)} (initial + ∫₀ᵗ e^{A(s)} b(s) ds)`, with `A` the cumulative total of `a`. -/
def integratingFactorSolution (a b : ℝ → ℝ) (initial t : ℝ) : ℝ :=
  Real.exp (-cumulativeRate a t) *
    (initial + ∫ s in (0 : ℝ)..t, Real.exp (cumulativeRate a s) * b s)

/-- The integrating-factor solution starts at its initial value. -/
theorem integratingFactorSolution_zero (a b : ℝ → ℝ) (initial : ℝ) :
    integratingFactorSolution a b initial 0 = initial := by
  simp [integratingFactorSolution]

/-- The integrand of the forcing integral is integrable on the horizon. -/
theorem intervalIntegrable_exp_mul {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T) :
    IntervalIntegrable (fun s ↦ Real.exp (cumulativeRate a s) * b s) volume 0 T :=
  hb.continuousOn_mul (by
    rw [Set.uIcc_of_le hT]
    exact (continuousOn_cumulativeRate hT ha).rexp)

/-- The integrating-factor solution of integrable coefficients is continuous on the horizon. -/
theorem continuousOn_integratingFactorSolution {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (initial : ℝ) : ContinuousOn (integratingFactorSolution a b initial) (Set.Icc 0 T) := by
  have hforcing := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_exp_mul hT ha hb) Set.left_mem_uIcc
  rw [Set.uIcc_of_le hT] at hforcing
  exact (continuousOn_cumulativeRate hT ha).neg.rexp.mul (continuousOn_const.add hforcing)

/-- For continuous coefficients the integrating-factor solution solves `u' = -a u + b`
everywhere. -/
theorem hasDerivAt_integratingFactorSolution {a b : ℝ → ℝ} (ha : Continuous a)
    (hb : Continuous b) (initial t : ℝ) :
    HasDerivAt (integratingFactorSolution a b initial)
      (-a t * integratingFactorSolution a b initial t + b t) t := by
  have hA := hasDerivAt_cumulativeRate a ha t
  have hcontinuous : Continuous fun s ↦ Real.exp (cumulativeRate a s) * b s :=
    (continuous_cumulativeRate a ha).rexp.mul hb
  have hforcing : HasDerivAt (fun v ↦ ∫ s in (0 : ℝ)..v, Real.exp (cumulativeRate a s) * b s)
      (Real.exp (cumulativeRate a t) * b t) t :=
    intervalIntegral.integral_hasDerivAt_right (hcontinuous.intervalIntegrable _ _)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter hcontinuous.continuousAt
  have hproduct : Real.exp (-cumulativeRate a t) * Real.exp (cumulativeRate a t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  refine (hA.fun_neg.exp.fun_mul (hforcing.const_add initial)).congr_deriv ?_
  unfold integratingFactorSolution
  linear_combination (b t) * hproduct

/-- **The integral equation for continuous coefficients.**  The integrating-factor solution
satisfies `u(t) = initial + ∫₀ᵗ (-a u + b)`, by the fundamental theorem of calculus. -/
theorem integratingFactorSolution_eq_integral_of_continuous {a b : ℝ → ℝ} (ha : Continuous a)
    (hb : Continuous b) (initial t : ℝ) :
    integratingFactorSolution a b initial t =
      initial + ∫ s in (0 : ℝ)..t, (-a s * integratingFactorSolution a b initial s + b s) := by
  have hderiv := hasDerivAt_integratingFactorSolution ha hb initial
  have hcontinuous : Continuous (integratingFactorSolution a b initial) :=
    continuous_iff_continuousAt.mpr fun s ↦ (hderiv s).continuousAt
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
    (((ha.neg.mul hcontinuous).add hb).intervalIntegrable 0 t)
  rw [hintegral, integratingFactorSolution_zero]
  ring

/-- **The integral equation for integrable coefficients.**  For coefficients integrable on the
horizon, the integrating-factor solution satisfies `u(t) = initial + ∫₀ᵗ (-a u + b)` at every
time of the horizon.  Continuous coefficients within `ε` in `L¹` have solutions within a fixed
multiple of `ε` of this one, and both sides of the equation move by a fixed multiple of `ε`. -/
theorem integratingFactorSolution_eq_integral {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (initial : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    integratingFactorSolution a b initial t =
      initial + ∫ s in (0 : ℝ)..t, (-a s * integratingFactorSolution a b initial s + b s) := by
  have hIa : 0 ≤ ∫ s in (0 : ℝ)..T, ‖a s‖ :=
    intervalIntegral.integral_nonneg hT fun _ _ ↦ norm_nonneg _
  have hIb : 0 ≤ ∫ s in (0 : ℝ)..T, ‖b s‖ :=
    intervalIntegral.integral_nonneg hT fun _ _ ↦ norm_nonneg _
  set L := (∫ s in (0 : ℝ)..T, ‖a s‖) + 1 with hL
  set Ib := ∫ s in (0 : ℝ)..T, ‖b s‖ with hIbdef
  have hexpL : 0 ≤ Real.exp L := (Real.exp_pos L).le
  have hA : ∀ s ∈ Set.Icc 0 T, |cumulativeRate a s| ≤ L := fun s hs ↦
    (abs_cumulativeRate_le ha hs).trans (by linarith)
  have hexpA : ∀ s ∈ Set.Icc 0 T, Real.exp (cumulativeRate a s) ≤ Real.exp L := fun s hs ↦
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hA s hs))
  have hexpNegA : ∀ s ∈ Set.Icc 0 T, Real.exp (-cumulativeRate a s) ≤ Real.exp L := fun s hs ↦
    Real.exp_le_exp.mpr ((neg_le_abs _).trans (hA s hs))
  have hforcingBound : ∀ s ∈ Set.Icc 0 T,
      |∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate a u) * b u| ≤ Real.exp L * Ib := by
    intro s hs
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le hs.1 (ae_of_all _ fun u hu ↦ ?_)
      ((intervalIntegrable_of_mem_horizon hb hs).norm.const_mul (Real.exp L))).trans ?_
    · have humem : u ∈ Set.Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hexpA u humem) (norm_nonneg _)
    · rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_le_horizon hb hs) hexpL
  set S := Real.exp L * (|initial| + Real.exp L * Ib) with hS
  have hS0 : 0 ≤ S := mul_nonneg hexpL (add_nonneg (abs_nonneg _) (mul_nonneg hexpL hIb))
  have hsolution : ∀ s ∈ Set.Icc 0 T, |integratingFactorSolution a b initial s| ≤ S := by
    intro s hs
    unfold integratingFactorSolution
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hexpNegA s hs)
      ((abs_add_le _ _).trans (add_le_add le_rfl (hforcingBound s hs))) (abs_nonneg _) hexpL
  set K := S + Real.exp L * Real.exp L * (Ib + 2) with hK
  have hK0 : 0 ≤ K := add_nonneg hS0 (mul_nonneg (mul_nonneg hexpL hexpL) (by linarith))
  have hSK : S ≤ K := by
    have hextra : 0 ≤ Real.exp L * Real.exp L * (Ib + 2) :=
      mul_nonneg (mul_nonneg hexpL hexpL) (by linarith)
    linarith
  have hsolutionOn : ContinuousOn (integratingFactorSolution a b initial) (Set.uIcc 0 t) :=
    (continuousOn_integratingFactorSolution hT ha hb initial).mono (by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2)
  have hsmall : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |integratingFactorSolution a b initial t -
        (initial + ∫ s in (0 : ℝ)..t, (-a s * integratingFactorSolution a b initial s + b s))| ≤
        ε * (2 * K + L * K + 1) := by
    intro ε hε hεone
    obtain ⟨α, hα, hαclose⟩ := exists_continuous_integral_norm_sub_le hT ha hε
    obtain ⟨β, hβ, hβclose⟩ := exists_continuous_integral_norm_sub_le hT hb hε
    have hαint : IntervalIntegrable α volume 0 T := hα.intervalIntegrable _ _
    have hβint : IntervalIntegrable β volume 0 T := hβ.intervalIntegrable _ _
    have hαmass : ∫ s in (0 : ℝ)..T, ‖α s‖ ≤ (∫ s in (0 : ℝ)..T, ‖a s‖) + ε := by
      have hle : ∫ s in (0 : ℝ)..T, ‖α s‖ ≤ ∫ s in (0 : ℝ)..T, (‖a s‖ + ‖a s - α s‖) :=
        intervalIntegral.integral_mono_on hT (hα.norm.intervalIntegrable _ _)
          (ha.norm.add (ha.sub hαint).norm) fun s _ ↦
            calc ‖α s‖ = ‖a s - (a s - α s)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖a s‖ + ‖a s - α s‖ := norm_sub_le _ _
      rw [intervalIntegral.integral_add ha.norm (ha.sub hαint).norm] at hle
      linarith
    have hβmass : ∫ s in (0 : ℝ)..T, ‖β s‖ ≤ Ib + ε := by
      have hle : ∫ s in (0 : ℝ)..T, ‖β s‖ ≤ ∫ s in (0 : ℝ)..T, (‖b s‖ + ‖b s - β s‖) :=
        intervalIntegral.integral_mono_on hT (hβ.norm.intervalIntegrable _ _)
          (hb.norm.add (hb.sub hβint).norm) fun s _ ↦
            calc ‖β s‖ = ‖b s - (b s - β s)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖b s‖ + ‖b s - β s‖ := norm_sub_le _ _
      rw [intervalIntegral.integral_add hb.norm (hb.sub hβint).norm] at hle
      linarith
    have hAc : ∀ s ∈ Set.Icc 0 T, |cumulativeRate α s| ≤ L := fun s hs ↦
      (abs_cumulativeRate_le hαint hs).trans (by linarith)
    have hAdiff : ∀ s ∈ Set.Icc 0 T, |cumulativeRate a s - cumulativeRate α s| ≤ ε := by
      intro s hs
      have hsplit : cumulativeRate a s - cumulativeRate α s = ∫ u in (0 : ℝ)..s, (a u - α u) :=
        (intervalIntegral.integral_sub (intervalIntegrable_of_mem_horizon ha hs)
          (intervalIntegrable_of_mem_horizon hαint hs)).symm
      rw [hsplit, ← Real.norm_eq_abs]
      exact (intervalIntegral.norm_integral_le_integral_norm hs.1).trans
        ((integral_norm_le_horizon (ha.sub hαint) hs).trans hαclose)
    have hexpDiff : ∀ s ∈ Set.Icc 0 T,
        |Real.exp (cumulativeRate a s) - Real.exp (cumulativeRate α s)| ≤ Real.exp L * ε :=
      fun s hs ↦ (abs_exp_sub_exp_le_of_abs_le (hA s hs) (hAc s hs)).trans
        (mul_le_mul_of_nonneg_left (hAdiff s hs) hexpL)
    have hexpNegDiff : ∀ s ∈ Set.Icc 0 T,
        |Real.exp (-cumulativeRate a s) - Real.exp (-cumulativeRate α s)| ≤ Real.exp L * ε := by
      intro s hs
      have hnegA : |-cumulativeRate a s| ≤ L := by rw [abs_neg]; exact hA s hs
      have hnegAc : |-cumulativeRate α s| ≤ L := by rw [abs_neg]; exact hAc s hs
      refine (abs_exp_sub_exp_le_of_abs_le hnegA hnegAc).trans ?_
      rw [neg_sub_neg, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (hAdiff s hs) hexpL
    have hcontinuousForcing : Continuous fun u ↦ Real.exp (cumulativeRate α u) * β u :=
      (continuous_cumulativeRate α hα).rexp.mul hβ
    have hforcingDiff : ∀ s ∈ Set.Icc 0 T,
        |(∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate a u) * b u) -
          ∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate α u) * β u| ≤
          Real.exp L * ε * (Ib + 2) := by
      intro s hs
      rw [← intervalIntegral.integral_sub
        (intervalIntegrable_of_mem_horizon (intervalIntegrable_exp_mul hT ha hb) hs)
        (hcontinuousForcing.intervalIntegrable _ _), ← Real.norm_eq_abs]
      have hmajorant : IntervalIntegrable
          (fun u ↦ Real.exp L * ‖b u - β u‖ + Real.exp L * ε * ‖β u‖) volume 0 s :=
        ((intervalIntegrable_of_mem_horizon (hb.sub hβint) hs).norm.const_mul _).add
          ((hβ.norm.intervalIntegrable 0 s).const_mul _)
      refine (intervalIntegral.norm_integral_le_of_norm_le hs.1 (ae_of_all _ fun u hu ↦ ?_)
        hmajorant).trans ?_
      · have humem : u ∈ Set.Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
        have hsplit : Real.exp (cumulativeRate a u) * b u -
            Real.exp (cumulativeRate α u) * β u =
            Real.exp (cumulativeRate a u) * (b u - β u) +
              β u * (Real.exp (cumulativeRate a u) - Real.exp (cumulativeRate α u)) := by ring
        rw [hsplit]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (hexpA u humem) (norm_nonneg _)
        · rw [norm_mul, Real.norm_eq_abs (Real.exp _ - _)]
          calc ‖β u‖ * |Real.exp (cumulativeRate a u) - Real.exp (cumulativeRate α u)|
              ≤ ‖β u‖ * (Real.exp L * ε) :=
                mul_le_mul_of_nonneg_left (hexpDiff u humem) (norm_nonneg _)
            _ = Real.exp L * ε * ‖β u‖ := by ring
      · rw [intervalIntegral.integral_add
          ((intervalIntegrable_of_mem_horizon (hb.sub hβint) hs).norm.const_mul _)
          ((hβ.norm.intervalIntegrable 0 s).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have hfirst : Real.exp L * ∫ u in (0 : ℝ)..s, ‖b u - β u‖ ≤ Real.exp L * ε :=
          mul_le_mul_of_nonneg_left ((integral_norm_le_horizon (hb.sub hβint) hs).trans hβclose)
            hexpL
        have hsecond : Real.exp L * ε * ∫ u in (0 : ℝ)..s, ‖β u‖ ≤
            Real.exp L * ε * (Ib + ε) :=
          mul_le_mul_of_nonneg_left ((integral_norm_le_horizon hβint hs).trans hβmass)
            (mul_nonneg hexpL hε.le)
        have hthird : Real.exp L * ε * ε ≤ Real.exp L * ε * 1 :=
          mul_le_mul_of_nonneg_left hεone (mul_nonneg hexpL hε.le)
        linarith
    have hsolutionDiff : ∀ s ∈ Set.Icc 0 T,
        |integratingFactorSolution a b initial s - integratingFactorSolution α β initial s| ≤
          ε * K := by
      intro s hs
      unfold integratingFactorSolution
      have hsplit : Real.exp (-cumulativeRate a s) *
            (initial + ∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate a u) * b u) -
          Real.exp (-cumulativeRate α s) *
            (initial + ∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate α u) * β u) =
          (Real.exp (-cumulativeRate a s) - Real.exp (-cumulativeRate α s)) *
              (initial + ∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate a u) * b u) +
            Real.exp (-cumulativeRate α s) *
              ((∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate a u) * b u) -
                ∫ u in (0 : ℝ)..s, Real.exp (cumulativeRate α u) * β u) := by ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-cumulativeRate α s))]
      have hfirst := mul_le_mul (hexpNegDiff s hs)
        ((abs_add_le _ _).trans (add_le_add le_rfl (hforcingBound s hs))) (abs_nonneg _)
        (mul_nonneg hexpL hε.le)
      have hsecond := mul_le_mul
        (Real.exp_le_exp.mpr ((neg_le_abs (cumulativeRate α s)).trans (hAc s hs)))
        (hforcingDiff s hs) (abs_nonneg _) hexpL
      calc _ ≤ Real.exp L * ε * (|initial| + Real.exp L * Ib) +
            Real.exp L * (Real.exp L * ε * (Ib + 2)) := add_le_add hfirst hsecond
        _ = ε * K := by rw [hK, hS]; ring
    have hcontinuousSolution : Continuous (integratingFactorSolution α β initial) :=
      continuous_iff_continuousAt.mpr fun s ↦
        (hasDerivAt_integratingFactorSolution hα hβ initial s).continuousAt
    have hcontinuousIntegrand : IntervalIntegrable
        (fun s ↦ -α s * integratingFactorSolution α β initial s + β s) volume 0 t :=
      ((hα.neg.mul hcontinuousSolution).add hβ).intervalIntegrable 0 t
    have hintegrableIntegrand : IntervalIntegrable
        (fun s ↦ -a s * integratingFactorSolution a b initial s + b s) volume 0 t :=
      ((intervalIntegrable_of_mem_horizon ha ht).neg.mul_continuousOn hsolutionOn).add
        (intervalIntegrable_of_mem_horizon hb ht)
    have hdifference : (∫ s in (0 : ℝ)..t,
          (-α s * integratingFactorSolution α β initial s + β s)) -
        ∫ s in (0 : ℝ)..t, (-a s * integratingFactorSolution a b initial s + b s) =
        ∫ s in (0 : ℝ)..t, ((a s - α s) * integratingFactorSolution a b initial s +
          α s * (integratingFactorSolution a b initial s -
            integratingFactorSolution α β initial s) - (b s - β s)) := by
      rw [← intervalIntegral.integral_sub hcontinuousIntegrand hintegrableIntegrand]
      congr 1
      funext s
      ring
    have hrewrite : integratingFactorSolution a b initial t -
        (initial + ∫ s in (0 : ℝ)..t, (-a s * integratingFactorSolution a b initial s + b s)) =
        (integratingFactorSolution a b initial t - integratingFactorSolution α β initial t) +
          ∫ s in (0 : ℝ)..t, ((a s - α s) * integratingFactorSolution a b initial s +
            α s * (integratingFactorSolution a b initial s -
              integratingFactorSolution α β initial s) - (b s - β s)) := by
      rw [← hdifference, integratingFactorSolution_eq_integral_of_continuous hα hβ initial t]
      ring
    have hintegralBound : |∫ s in (0 : ℝ)..t, ((a s - α s) * integratingFactorSolution a b initial s +
          α s * (integratingFactorSolution a b initial s -
            integratingFactorSolution α β initial s) - (b s - β s))| ≤
        ε * S + ε * K * L + ε := by
      rw [← Real.norm_eq_abs]
      have hfirstPart : IntervalIntegrable (fun u ↦ ‖a u - α u‖ * S) volume 0 t :=
        (intervalIntegrable_of_mem_horizon (ha.sub hαint) ht).norm.mul_const _
      have hsecondPart : IntervalIntegrable (fun u ↦ ‖α u‖ * (ε * K)) volume 0 t :=
        (hα.norm.intervalIntegrable 0 t).mul_const _
      have hthirdPart : IntervalIntegrable (fun u ↦ ‖b u - β u‖) volume 0 t :=
        (intervalIntegrable_of_mem_horizon (hb.sub hβint) ht).norm
      refine (intervalIntegral.norm_integral_le_of_norm_le ht.1 (ae_of_all _ fun u hu ↦ ?_)
        ((hfirstPart.add hsecondPart).add hthirdPart)).trans ?_
      · have humem : u ∈ Set.Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
        refine (norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
        · rw [norm_mul, Real.norm_eq_abs (integratingFactorSolution a b initial u)]
          exact mul_le_mul_of_nonneg_left (hsolution u humem) (norm_nonneg _)
        · rw [norm_mul, Real.norm_eq_abs (integratingFactorSolution a b initial u - _)]
          exact mul_le_mul_of_nonneg_left (hsolutionDiff u humem) (norm_nonneg _)
      · rw [intervalIntegral.integral_add (hfirstPart.add hsecondPart) hthirdPart,
          intervalIntegral.integral_add hfirstPart hsecondPart,
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        have hfirst : (∫ u in (0 : ℝ)..t, ‖a u - α u‖) * S ≤ ε * S :=
          mul_le_mul_of_nonneg_right
            ((integral_norm_le_horizon (ha.sub hαint) ht).trans hαclose) hS0
        have hsecond : (∫ u in (0 : ℝ)..t, ‖α u‖) * (ε * K) ≤ L * (ε * K) :=
          mul_le_mul_of_nonneg_right ((integral_norm_le_horizon hαint ht).trans (by linarith))
            (mul_nonneg hε.le hK0)
        have hthird : ∫ u in (0 : ℝ)..t, ‖b u - β u‖ ≤ ε :=
          (integral_norm_le_horizon (hb.sub hβint) ht).trans hβclose
        linarith
    rw [hrewrite]
    refine (abs_add_le _ _).trans ?_
    have hsolutionAt := hsolutionDiff t ht
    have hscaled := mul_le_mul_of_nonneg_left hSK hε.le
    linarith
  set C := 2 * K + L * K + 1 with hC
  have hCpos : 0 < C := by nlinarith
  refine eq_of_forall_dist_le fun δ hδ ↦ ?_
  rw [Real.dist_eq]
  have hεpos : 0 < min 1 (δ / C) := lt_min one_pos (div_pos hδ hCpos)
  refine (hsmall _ hεpos (min_le_left _ _)).trans ?_
  calc min 1 (δ / C) * C ≤ δ / C * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hCpos.le
    _ = δ := div_mul_cancel₀ δ hCpos.ne'

/-! ## Uniqueness among continuous solutions -/

/-- **The scalar linear integral equation has at most one continuous solution.**  For coefficients
integrable on the horizon, two continuous solutions of `u(t) = initial + ∫₀ᵗ (-a u + b)` agree on
the horizon: their difference is bounded, through a continuous approximation of `a` and
Gronwall's inequality, by an arbitrarily small multiple of the approximation error. -/
theorem eq_of_linear_integral_eq {a b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (initial : ℝ) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hueq : ∀ t ∈ Set.Icc 0 T, u t = initial + ∫ s in (0 : ℝ)..t, (-a s * u s + b s))
    (hveq : ∀ t ∈ Set.Icc 0 T, v t = initial + ∫ s in (0 : ℝ)..t, (-a s * v s + b s)) :
    ∀ t ∈ Set.Icc 0 T, u t = v t := by
  obtain ⟨maximizer, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT)
    (hu.sub hv).norm.continuousOn
  have hbound : ∀ s ∈ Set.Icc 0 T, ‖u s - v s‖ ≤ ‖u maximizer - v maximizer‖ :=
    fun s hs ↦ isMaxOn_iff.mp hmax s hs
  set W := ‖u maximizer - v maximizer‖ with hW
  have hW0 : 0 ≤ W := norm_nonneg _
  intro t ht
  set E := Real.exp ((∫ s in (0 : ℝ)..T, ‖a s‖) + 1) with hE
  have hsmall : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖u t - v t‖ ≤ ε * (W * E) := by
    intro ε hε hεone
    obtain ⟨α, hα, hclose⟩ := exists_continuous_integral_norm_sub_le hT ha hε
    have hαint : IntervalIntegrable α volume 0 T := hα.intervalIntegrable _ _
    have hstep : ∀ r ∈ Set.Icc 0 T,
        ‖u r - v r‖ ≤ W * ε + ∫ s in (0 : ℝ)..r, ‖α s‖ * ‖u s - v s‖ := by
      intro r hr
      have har := intervalIntegrable_of_mem_horizon ha hr
      have hbr := intervalIntegrable_of_mem_horizon hb hr
      have hsplit : u r - v r = -((∫ s in (0 : ℝ)..r, α s * (u s - v s)) +
          ∫ s in (0 : ℝ)..r, (a s - α s) * (u s - v s)) := by
        rw [hueq r hr, hveq r hr, add_sub_add_left_eq_sub,
          ← intervalIntegral.integral_sub ((har.neg.mul_continuousOn hu.continuousOn).add hbr)
            ((har.neg.mul_continuousOn hv.continuousOn).add hbr),
          ← intervalIntegral.integral_add ((hα.mul (hu.sub hv)).intervalIntegrable _ _)
            ((intervalIntegrable_of_mem_horizon (ha.sub hαint) hr).mul_continuousOn
              (hu.sub hv).continuousOn),
          ← intervalIntegral.integral_neg]
        congr 1
        funext s
        ring
      have hfirst : ‖∫ s in (0 : ℝ)..r, α s * (u s - v s)‖ ≤
          ∫ s in (0 : ℝ)..r, ‖α s‖ * ‖u s - v s‖ :=
        (intervalIntegral.norm_integral_le_integral_norm hr.1).trans
          (intervalIntegral.integral_mono_on hr.1
            ((hα.mul (hu.sub hv)).norm.intervalIntegrable _ _)
            ((hα.norm.mul (hu.sub hv).norm).intervalIntegrable _ _) fun s _ ↦
              (norm_mul _ _).le)
      have hsecond : ‖∫ s in (0 : ℝ)..r, (a s - α s) * (u s - v s)‖ ≤ W * ε := by
        refine (intervalIntegral.norm_integral_le_integral_norm hr.1).trans ?_
        calc ∫ s in (0 : ℝ)..r, ‖(a s - α s) * (u s - v s)‖
            ≤ ∫ s in (0 : ℝ)..r, ‖a s - α s‖ * W := by
              refine intervalIntegral.integral_mono_on hr.1
                ((intervalIntegrable_of_mem_horizon (ha.sub hαint) hr).mul_continuousOn
                  (hu.sub hv).continuousOn).norm
                ((intervalIntegrable_of_mem_horizon (ha.sub hαint) hr).norm.mul_const _)
                fun s hs ↦ ?_
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hbound s ⟨hs.1, hs.2.trans hr.2⟩)
                (norm_nonneg _)
          _ = (∫ s in (0 : ℝ)..r, ‖a s - α s‖) * W := intervalIntegral.integral_mul_const _ _
          _ ≤ ε * W := mul_le_mul_of_nonneg_right
              ((integral_norm_le_horizon (ha.sub hαint) hr).trans hclose) hW0
          _ = W * ε := mul_comm _ _
      rw [hsplit, norm_neg]
      exact (norm_add_le _ _).trans (by linarith)
    have hgronwall := le_mul_exp_integral_of_le_add_integral (a := fun s ↦ ‖α s‖)
      (u := fun s ↦ ‖u s - v s‖) hα.norm (hu.sub hv).norm (fun s _ ↦ norm_nonneg _) hstep t ht
    have hmass : (∫ s in (0 : ℝ)..t, ‖α s‖) ≤ (∫ s in (0 : ℝ)..T, ‖a s‖) + 1 := by
      have hle : ∫ s in (0 : ℝ)..T, ‖α s‖ ≤ ∫ s in (0 : ℝ)..T, (‖a s‖ + ‖a s - α s‖) :=
        intervalIntegral.integral_mono_on hT (hα.norm.intervalIntegrable _ _)
          (ha.norm.add (ha.sub hαint).norm) fun s _ ↦
            calc ‖α s‖ = ‖a s - (a s - α s)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖a s‖ + ‖a s - α s‖ := norm_sub_le _ _
      rw [intervalIntegral.integral_add ha.norm (ha.sub hαint).norm] at hle
      have htail := integral_norm_le_horizon hαint ht
      linarith
    calc ‖u t - v t‖ ≤ W * ε * Real.exp (∫ s in (0 : ℝ)..t, ‖α s‖) := hgronwall
      _ ≤ W * ε * E := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmass)
          (mul_nonneg hW0 hε.le)
      _ = ε * (W * E) := by ring
  have hC : 0 < W * E + 1 := by
    have hWE : 0 ≤ W * E := mul_nonneg hW0 (Real.exp_pos _).le
    linarith
  refine eq_of_forall_dist_le fun δ hδ ↦ ?_
  rw [dist_eq_norm]
  have hεpos : 0 < min 1 (δ / (W * E + 1)) := lt_min one_pos (div_pos hδ hC)
  refine (hsmall _ hεpos (min_le_left _ _)).trans ?_
  have hWE : 0 ≤ W * E := mul_nonneg hW0 (Real.exp_pos _).le
  calc min 1 (δ / (W * E + 1)) * (W * E) ≤ δ / (W * E + 1) * (W * E + 1) :=
        mul_le_mul (min_le_right _ _) (by linarith) hWE (div_pos hδ hC).le
    _ = δ := div_mul_cancel₀ δ hC.ne'

/-! ## NOTE1 (27) in integral form for integrable rates -/

/-- The donor fraction of a locally integrable migration rate is continuous. -/
theorem continuous_donorFraction {m : ℝ → ℝ} (hm : LocallyIntegrable m volume) :
    Continuous (donorFraction m) :=
  continuous_const.sub (continuous_cumulativeRate_of_locallyIntegrable hm).neg.rexp

/-- The linkage (28) of locally integrable rates is continuous. -/
theorem continuous_admixtureLinkage {m r : ℝ → ℝ} (hm : LocallyIntegrable m volume)
    (hr : LocallyIntegrable r volume) : Continuous (admixtureLinkage m r) := by
  have hM := continuous_cumulativeRate_of_locallyIntegrable hm
  have hR := continuous_cumulativeRate_of_locallyIntegrable hr
  have hintegrand : ∀ a b : ℝ, IntervalIntegrable
      (fun s ↦ m s * Real.exp (-cumulativeRate m s + cumulativeRate r s)) volume a b :=
    fun a b ↦ (intervalIntegrable_of_locallyIntegrable hm a b).mul_continuousOn
      (hM.neg.add hR).rexp.continuousOn
  exact (hM.neg.sub hR).rexp.mul (intervalIntegral.continuous_primitive hintegrand 0)

/-- **NOTE1 (27), first equation, in integral form.**  For a locally integrable migration rate
the donor fraction satisfies `p(t) = ∫₀ᵗ m (1 - p)` at every nonnegative time. -/
theorem donorFraction_eq_integral {m : ℝ → ℝ} (hm : LocallyIntegrable m volume) {t : ℝ}
    (ht : 0 ≤ t) : donorFraction m t = ∫ s in (0 : ℝ)..t, m s * (1 - donorFraction m s) := by
  have hgeneral := integratingFactorSolution_eq_integral (b := fun _ ↦ 0) ht
    (intervalIntegrable_of_locallyIntegrable hm 0 t) intervalIntegrable_const 1 ⟨ht, le_rfl⟩
  simp only [integratingFactorSolution, mul_zero, intervalIntegral.integral_zero, add_zero,
    mul_one] at hgeneral
  have hnegative : (∫ s in (0 : ℝ)..t, -m s * Real.exp (-cumulativeRate m s)) =
      -∫ s in (0 : ℝ)..t, m s * Real.exp (-cumulativeRate m s) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext s
    ring
  rw [hnegative] at hgeneral
  simp only [one_sub_donorFraction]
  rw [donorFraction]
  linarith

/-- **NOTE1 (27), second equation, in integral form.**  For locally integrable migration and
recombination rates the linkage (28) satisfies
`D(t) = ∫₀ᵗ (-(m + r) D + m (1 - p)²)` at every nonnegative time. -/
theorem admixtureLinkage_eq_integral {m r : ℝ → ℝ} (hm : LocallyIntegrable m volume)
    (hr : LocallyIntegrable r volume) {t : ℝ} (ht : 0 ≤ t) :
    admixtureLinkage m r t = ∫ s in (0 : ℝ)..t,
      (-(m s + r s) * admixtureLinkage m r s + m s * (1 - donorFraction m s) ^ 2) := by
  have hmint := intervalIntegrable_of_locallyIntegrable hm
  have hrint := intervalIntegrable_of_locallyIntegrable hr
  have hsum : ∀ s, cumulativeRate (fun u ↦ m u + r u) s =
      cumulativeRate m s + cumulativeRate r s :=
    fun s ↦ intervalIntegral.integral_add (hmint 0 s) (hrint 0 s)
  have hsolution : ∀ s, integratingFactorSolution (fun u ↦ m u + r u)
      (fun u ↦ m u * (1 - donorFraction m u) ^ 2) 0 s = admixtureLinkage m r s := by
    intro s
    unfold integratingFactorSolution admixtureLinkage
    rw [hsum, zero_add, neg_add']
    congr 1
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    simp only [hsum, one_sub_donorFraction]
    have hexponent : Real.exp (-cumulativeRate m u + cumulativeRate r u) =
        Real.exp (cumulativeRate m u + cumulativeRate r u) *
          (Real.exp (-cumulativeRate m u) * Real.exp (-cumulativeRate m u)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hexponent]
    ring
  have hforcing : IntervalIntegrable (fun u ↦ m u * (1 - donorFraction m u) ^ 2) volume 0 t :=
    (hmint 0 t).mul_continuousOn
      ((continuous_const.sub (continuous_donorFraction hm)).pow 2).continuousOn
  have hgeneral := integratingFactorSolution_eq_integral ht ((hmint 0 t).add (hrint 0 t))
    hforcing 0 ⟨ht, le_rfl⟩
  simp only [hsolution, zero_add] at hgeneral
  exact hgeneral

/-- **Uniqueness of the donor fraction.**  For a locally integrable migration rate, every
continuous solution of `P(t) = ∫₀ᵗ m (1 - P)` on the horizon is the donor fraction there. -/
theorem eq_donorFraction_of_integral_eq {m : ℝ → ℝ} (hm : LocallyIntegrable m volume) {T : ℝ}
    (hT : 0 ≤ T) {F : ℝ → ℝ} (hF : Continuous F)
    (hFeq : ∀ t ∈ Set.Icc 0 T, F t = ∫ s in (0 : ℝ)..t, m s * (1 - F s)) :
    ∀ t ∈ Set.Icc 0 T, F t = donorFraction m t := by
  have hmint := intervalIntegrable_of_locallyIntegrable hm 0 T
  have hlinear : ∀ {G : ℝ → ℝ}, (∀ t ∈ Set.Icc 0 T, G t = ∫ s in (0 : ℝ)..t, m s * (1 - G s)) →
      ∀ t ∈ Set.Icc 0 T, G t = 0 + ∫ s in (0 : ℝ)..t, (-m s * G s + m s) := by
    intro G hG t ht
    rw [hG t ht, zero_add]
    congr 1
    funext s
    ring
  exact eq_of_linear_integral_eq hT hmint hmint 0 hF (continuous_donorFraction hm)
    (hlinear hFeq) (hlinear fun t ht ↦ donorFraction_eq_integral hm ht.1)

/-- **Uniqueness of the linkage (28).**  For locally integrable migration and recombination rates,
every continuous solution of `F(t) = ∫₀ᵗ (-(m + r) F + m (1 - p)²)` on the horizon is the
linkage (28) there. -/
theorem eq_admixtureLinkage_of_integral_eq {m r : ℝ → ℝ} (hm : LocallyIntegrable m volume)
    (hr : LocallyIntegrable r volume) {T : ℝ} (hT : 0 ≤ T) {F : ℝ → ℝ} (hF : Continuous F)
    (hFeq : ∀ t ∈ Set.Icc 0 T, F t = ∫ s in (0 : ℝ)..t,
      (-(m s + r s) * F s + m s * (1 - donorFraction m s) ^ 2)) :
    ∀ t ∈ Set.Icc 0 T, F t = admixtureLinkage m r t := by
  have hmint := intervalIntegrable_of_locallyIntegrable hm 0 T
  have hrint := intervalIntegrable_of_locallyIntegrable hr 0 T
  have hforcing : IntervalIntegrable (fun u ↦ m u * (1 - donorFraction m u) ^ 2) volume 0 T :=
    hmint.mul_continuousOn
      ((continuous_const.sub (continuous_donorFraction hm)).pow 2).continuousOn
  refine eq_of_linear_integral_eq hT (hmint.add hrint) hforcing 0 hF
    (continuous_admixtureLinkage hm hr) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · rw [hFeq t ht, zero_add]
  · rw [admixtureLinkage_eq_integral hm hr ht.1, zero_add]

end

end Descent.Portability.ChronologyIntegralEquation
