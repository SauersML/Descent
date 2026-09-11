/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmallDenominatorRates
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Measure.Prod

assert_below Descent.Decision Descent.Program

/-!
# Layer cakes and sharp gamma constants for small-denominator rates

`SmallDenominatorRates` bounds the mass a truncated replica expansion leaves unresolved by
splitting at one threshold. NOTE 2 sections 5.3 and 6.3 state the sharp forms instead, and this
module proves them. The engine is the pointwise layer cake: for a denominator `D ≤ 1` and a
density with a primitive on `(0, 1]`, the increment of the primitive from `D` to `1`, read as
zero where `D` is not positive, is the integral over `t ∈ [0, 1]` of the density against the
selector of the small-denominator event `0 < D ≤ t` (`primitive_eq_integral_selector`). Three
densities are instantiated: `K (1 - t)^(K-1)` gives `1_{D>0} (1 - D)^K`
(`truncation_layerCake`, the display in the proof of NOTE 2 equation (20)); `t⁻²` gives
`1_{D>0} (D⁻¹ - 1)` (`inverse_layerCake`, the tail of `D⁻¹` over `[1, ∞)` in the proof of (28)
after the substitution `s = 1/t`); and `(K (1-t)^(K-1) t + (1-t)^K) / t²`, minus the derivative
of `(1 - t)^K / t`, gives `1_{D>0} (1 - D)^K / D` (`remainder_layerCake`, the proof of (29)).

Over a finite report law the exchange of the report sum with the integral turns each identity
into an expectation form against `SmallDenominatorRates.smallDenominatorMass`
(`expectation_profile_eq_integral`); `unresolvedMass_eq_integral` is the layer cake for the
corpus quantity `ReplicaDomainCertificate.unresolvedMass`. Inserting the power law
`P(0 < D ≤ t) ≤ C t^α` and evaluating beta integrals through Mathlib's
`Complex.Gamma_mul_Gamma_eq_betaIntegral` (`integral_rpow_mul_one_sub_pow`) gives
`unresolvedMass_le_gamma`, NOTE 2 equation (20) with its constant
`C Γ(α+1) Γ(K+1) / Γ(K+α+1)`; `expectation_inverse_le`, equation (28); and
`unresolvedNumerator_le_gamma`, equation (29) with its constant
`M C Γ(α+1)/(α-1) · Γ(K+1)/Γ(K+α)`, where the two beta integrals combine through
`Γ(α) + Γ(α-1) = α Γ(α-1)` (`remainderDensity_beta_bound`).

Over an s-finite measure Tonelli's theorem gives the same identities as upper integrals
(`lintegral_profile_eq_lintegral`), and the three bounds follow with the rate stated in
extended nonnegative reals (`lintegral_truncation_le_gamma`, `lintegral_inverse_le`,
`lintegral_unresolvedNumerator_le_gamma`). The divergence criterion of NOTE 2 section 6.3 is
`lintegral_ratioOnDefined_eq_top`: over a finite measure, a matching lower bound
`μ(0 < D ≤ t) ≥ c t^α` with `c > 0` and exponent `α ≤ 1` for `0 < t ≤ θ`, together with a
numerator at least `ν > 0` on `0 < D ≤ θ`, makes the upper integral of the ratio infinite. The
note's caveat that denominator bounds alone decide nothing is
`uniformDenominator_divergence_depends_on_numerator`: under the uniform law the same clipped
denominator gives an infinite expectation with numerator one, the note's slope `1/U`, and an
expectation at most one with numerator equal to the denominator.

Narrower and stronger than the note. The beta evaluation and (20) hold for every real `α > -1`,
not only `α > 0`, and the power law is used only on `0 < t ≤ 1`. Equation (29) needs no sign
on the numerator, only the ceiling `N ≤ M`. All results take the bounds `0 ≤ D ≤ 1`
pointwise, as the corpus certificates do, and the measure results take the denominator
measurable. The divergence criterion is proved for finite measures, the setting of a
probability law; signed numerators, which the note splits into positive and negative parts,
are not treated.

## Empirical status

None. The bodies here are integral identities and inequalities between expectations of
functions of a denominator under a stated power law, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmallDenominatorLayerCake

open MeasureTheory Set
open SublawReportCertificate PositiveRatioExpansion ReplicaDomainCertificate
  SmallDenominatorRates

noncomputable section

section Beta

/-- **Beta integral with a natural exponent.** For real `β > -1` and natural `n`,
`∫_0^1 t^β (1 - t)^n dt = Γ(β + 1) Γ(n + 1) / Γ(β + n + 2)`, the real restriction of the
complex beta integral through `Complex.Gamma_mul_Gamma_eq_betaIntegral`. -/
theorem integral_rpow_mul_one_sub_pow (β : ℝ) (hβ : -1 < β) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ β * (1 - t) ^ n =
      Real.Gamma (β + 1) * Real.Gamma (n + 1) / Real.Gamma (β + n + 2) := by
  have hleft : 0 < (((β + 1 : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  have hright : 0 < (((n + 1 : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have hcomplex := Complex.Gamma_mul_Gamma_eq_betaIntegral hleft hright
  have hbeta : Complex.betaIntegral ((β + 1 : ℝ) : ℂ) ((n + 1 : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..1, t ^ β * (1 - t) ^ n : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hexponentLeft : ((β + 1 : ℝ) : ℂ) - 1 = (β : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_right]
    have hexponentRight : ((n + 1 : ℝ) : ℂ) - 1 = ((n : ℕ) : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_right, Complex.ofReal_natCast]
    simp only [hexponentLeft, hexponentRight, Complex.cpow_natCast,
      ← Complex.ofReal_cpow ht.1]
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  have hsum : ((β + 1 : ℝ) : ℂ) + ((n + 1 : ℝ) : ℂ) = ((β + n + 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    congr 1
    ring
  rw [hsum, hbeta] at hcomplex
  simp only [Complex.Gamma_ofReal] at hcomplex
  have hreal : Real.Gamma (β + 1) * Real.Gamma (n + 1) =
      Real.Gamma (β + n + 2) * ∫ t in (0 : ℝ)..1, t ^ β * (1 - t) ^ n := by
    exact_mod_cast hcomplex
  have hpos : 0 < Real.Gamma (β + n + 2) := by
    apply Real.Gamma_pos_of_pos
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [eq_div_iff hpos.ne', hreal]
  ring

/-- **NOTE 2 equation (20), the beta constant.** For real `α > -1` and natural `K ≥ 1`,
`∫_0^1 K (1 - t)^(K-1) t^α dt = Γ(α + 1) Γ(K + 1) / Γ(K + α + 1)`. -/
theorem integral_truncationDensity_mul_rpow (α : ℝ) (hα : -1 < α) (K : ℕ) (hK : 1 ≤ K) :
    ∫ t in (0 : ℝ)..1, (K : ℝ) * (1 - t) ^ (K - 1) * t ^ α =
      Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1) := by
  have hbeta := integral_rpow_mul_one_sub_pow α hα (K - 1)
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one]
  have hleft : (K : ℝ) - 1 + 1 = K := by ring
  have hright : α + ((K : ℝ) - 1) + 2 = K + α + 1 := by ring
  rw [hcast, hleft, hright] at hbeta
  have hK0 : (K : ℝ) ≠ 0 := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    exact hKpos.ne'
  calc ∫ t in (0 : ℝ)..1, (K : ℝ) * (1 - t) ^ (K - 1) * t ^ α
      = (K : ℝ) * ∫ t in (0 : ℝ)..1, t ^ α * (1 - t) ^ (K - 1) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext t
        ring
    _ = Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1) := by
        rw [hbeta, Real.Gamma_add_one hK0]
        ring

/-- **The constants of NOTE 2 equation (20).** For `K ≥ 1` and `α > -1` the truncation density
`K (1 - t)^(K-1)` is continuous and nonnegative on `(0, 1]`, its product with `C t^α` is
integrable over `[0, 1]`, and that integral is `C Γ(α + 1) Γ(K + 1) / Γ(K + α + 1)`. -/
theorem truncationDensity_beta_bound (K : ℕ) (hK : 1 ≤ K) (scale α : ℝ) (hα : -1 < α) :
    ContinuousOn (fun t : ℝ ↦ (K : ℝ) * (1 - t) ^ (K - 1)) (Ioc 0 1) ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (K : ℝ) * (1 - t) ^ (K - 1)) ∧
    IntervalIntegrable (fun t : ℝ ↦ scale * ((K : ℝ) * (1 - t) ^ (K - 1) * t ^ α)) volume 0 1 ∧
    ∫ t in (0 : ℝ)..1, scale * ((K : ℝ) * (1 - t) ^ (K - 1) * t ^ α) =
      scale * (Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1)) := by
  refine ⟨by fun_prop, fun t ht ↦ mul_nonneg (Nat.cast_nonneg K)
    (pow_nonneg (by linarith [ht.2]) (K - 1)),
    ((intervalIntegral.intervalIntegrable_rpow' hα).continuousOn_mul (by fun_prop)).const_mul
      scale, ?_⟩
  rw [intervalIntegral.integral_const_mul, integral_truncationDensity_mul_rpow α hα K hK]

/-- **The constants of NOTE 2 equation (28).** For `α > 1` the density `t⁻²` is continuous and
nonnegative on `(0, 1]`; its product with `C t^α` is dominated there by `C t^(α-2)`, which is
integrable over `[0, 1]` with integral `C / (α - 1)`. -/
theorem inverseDensity_beta_bound (scale α : ℝ) (hα : 1 < α) :
    ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioc 0 1) ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (t ^ 2)⁻¹) ∧
    IntervalIntegrable (fun t : ℝ ↦ scale * t ^ (α - 2)) volume 0 1 ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, (t ^ 2)⁻¹ * (scale * t ^ α) ≤ scale * t ^ (α - 2)) ∧
    ∫ t in (0 : ℝ)..1, scale * t ^ (α - 2) = scale / (α - 1) := by
  refine ⟨(continuous_pow 2).continuousOn.inv₀ fun t ht ↦ pow_ne_zero 2 ht.1.ne',
    fun t _ ↦ inv_nonneg.mpr (sq_nonneg t),
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul scale, fun t ht ↦ ?_, ?_⟩
  · refine le_of_eq ?_
    rw [Real.rpow_sub ht.1 α 2, Real.rpow_two]
    ring
  · rw [intervalIntegral.integral_const_mul, integral_rpow (r := α - 2) (Or.inl (by linarith)),
      Real.one_rpow, Real.zero_rpow (by linarith : (0 : ℝ) < α - 2 + 1).ne']
    ring

/-- **The constants of NOTE 2 equation (29).** For `K ≥ 1` and `α > 1` the remainder density
`(K (1-t)^(K-1) t + (1-t)^K) / t²` is continuous and nonnegative on `(0, 1]`; its product with
`C t^α` is dominated there by `C (K t^(α-1) (1-t)^(K-1) + t^(α-2) (1-t)^K)`, which is integrable
over `[0, 1]` with integral `C Γ(α + 1) / (α - 1) · Γ(K + 1) / Γ(K + α)`. The two beta
integrals combine through `Γ(α) + Γ(α - 1) = α Γ(α - 1)`. -/
theorem remainderDensity_beta_bound (K : ℕ) (hK : 1 ≤ K) (scale α : ℝ) (hα : 1 < α) :
    ContinuousOn (fun t : ℝ ↦ ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2)
      (Ioc 0 1) ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2) ∧
    IntervalIntegrable (fun t : ℝ ↦ scale *
      ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K)) volume 0 1 ∧
    (∀ t ∈ Ioc (0 : ℝ) 1,
      ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 * (scale * t ^ α) ≤
        scale * ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K)) ∧
    ∫ t in (0 : ℝ)..1, scale *
      ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) =
      scale * (Real.Gamma (α + 1) / (α - 1) * (Real.Gamma (K + 1) / Real.Gamma (K + α))) := by
  have hcont : ContinuousOn
      (fun t : ℝ ↦ ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2) (Ioc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ ↦
      (K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K).continuousOn.div
      (continuous_pow 2).continuousOn fun t ht ↦ pow_ne_zero 2 ht.1.ne'
  have hdensity : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 ≤ ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 := by
    intro t ht
    have hdeficit : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
    exact div_nonneg (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg K)
      (pow_nonneg hdeficit _)) ht.1.le) (pow_nonneg hdeficit K)) (sq_nonneg t)
  have hfirst : IntervalIntegrable (fun t : ℝ ↦ t ^ (α - 1) * (1 - t) ^ (K - 1)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn (by fun_prop)
  have hsecond : IntervalIntegrable (fun t : ℝ ↦ t ^ (α - 2) * (1 - t) ^ K) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn (by fun_prop)
  have hdominates : ∀ t ∈ Ioc (0 : ℝ) 1,
      ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 * (scale * t ^ α) ≤
        scale * ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    refine le_of_eq ?_
    rw [Real.rpow_sub ht.1 α 1, Real.rpow_sub ht.1 α 2, Real.rpow_one, Real.rpow_two]
    field_simp
  have hK0 : (K : ℝ) ≠ 0 := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    exact hKpos.ne'
  have hαne : α - 1 ≠ 0 := (by linarith : (0 : ℝ) < α - 1).ne'
  have hGammaPos : Real.Gamma (K + α) ≠ 0 := by
    have hKnonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hvalue : ∫ t in (0 : ℝ)..1, scale *
      ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) =
      scale * (Real.Gamma (α + 1) / (α - 1) * (Real.Gamma (K + 1) / Real.Gamma (K + α))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hfirst.const_mul (K : ℝ)) hsecond,
      intervalIntegral.integral_const_mul,
      integral_rpow_mul_one_sub_pow (α - 1) (by linarith) (K - 1),
      integral_rpow_mul_one_sub_pow (α - 2) (by linarith) K]
    have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub hK, Nat.cast_one]
    have harg1 : α - 1 + 1 = α := by ring
    have harg2 : (K : ℝ) - 1 + 1 = K := by ring
    have harg3 : α - 1 + ((K : ℝ) - 1) + 2 = K + α := by ring
    have harg4 : α - 2 + 1 = α - 1 := by ring
    have harg5 : α - 2 + (K : ℝ) + 2 = K + α := by ring
    rw [hcast, harg1, harg2, harg3, harg4, harg5]
    have hGammaAlpha : Real.Gamma (α + 1) = α * Real.Gamma α :=
      Real.Gamma_add_one (by linarith : (0 : ℝ) < α).ne'
    have hGammaShift : Real.Gamma α = (α - 1) * Real.Gamma (α - 1) := by
      have hshift := Real.Gamma_add_one hαne
      rwa [harg1] at hshift
    rw [hGammaAlpha, hGammaShift, Real.Gamma_add_one hK0]
    field_simp
    ring
  exact ⟨hcont, hdensity, ((hfirst.const_mul (K : ℝ)).add hsecond).const_mul scale, hdominates,
    hvalue⟩

end Beta

section Pointwise

/-- On a positive denominator, the density times the selector of `0 < D ≤ t` is the density
restricted to the half-line `t ≥ D`. -/
theorem selector_eq_indicator (density : ℝ → ℝ) (D : ℝ) (hpos : 0 < D) :
    (fun t ↦ density t * (if 0 < D ∧ D ≤ t then 1 else 0)) = (Ici D).indicator density := by
  funext t
  by_cases ht : D ≤ t
  · simp [hpos, ht]
  · simp [hpos, ht]

/-- **Layer cake against a density, one positive denominator.** For `0 < D ≤ 1` and a density
with a primitive on `[D, 1]`, integrating the density against the selector of `0 < D ≤ t` over
`t ∈ [0, 1]` returns the increment of the primitive from `D` to `1`. -/
theorem integral_density_mul_selector (density primitive : ℝ → ℝ) (D : ℝ) (hpos : 0 < D)
    (hD1 : D ≤ 1) (hcont : ContinuousOn density (Icc D 1))
    (hderiv : ∀ t ∈ Icc D 1, HasDerivAt primitive (density t) t) :
    ∫ t in (0 : ℝ)..1, density t * (if 0 < D ∧ D ≤ t then 1 else 0) =
      primitive 1 - primitive D := by
  have hset : Ioc (0 : ℝ) 1 ∩ Ici D = Icc D 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, ht1⟩, htD⟩
      exact ⟨htD, ht1⟩
    · rintro ⟨htD, ht1⟩
      exact ⟨⟨lt_of_lt_of_le hpos htD, ht1⟩, htD⟩
  rw [selector_eq_indicator density D hpos, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hD1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
  · rw [uIcc_of_le hD1]
    exact hderiv
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hD1]
    exact hcont

/-- The density times the selector of `0 < D ≤ t` is integrable over `[0, 1]` whenever the
density is continuous on `(0, 1]` and the denominator is nonnegative. -/
theorem intervalIntegrable_density_mul_selector (density : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1)) (D : ℝ) (hD : 0 ≤ D) :
    IntervalIntegrable (fun t ↦ density t * (if 0 < D ∧ D ≤ t then 1 else 0)) volume 0 1 := by
  rcases hD.eq_or_lt with hzero | hpos
  · have hfun : (fun t ↦ density t * (if 0 < D ∧ D ≤ t then 1 else 0)) = fun _ ↦ 0 := by
      funext t
      simp [← hzero]
    rw [hfun]
    exact continuous_const.intervalIntegrable 0 1
  · have hon : IntegrableOn density (Icc D 1) volume :=
      (hcont.mono fun t ht ↦ ⟨lt_of_lt_of_le hpos ht.1, ht.2⟩).integrableOn_Icc
    rw [selector_eq_indicator density D hpos,
      intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn,
      integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ici]
    exact hon.mono_set fun t ht ↦ ⟨ht.1, ht.2.2⟩

/-- **Layer cake, one denominator at most one.** If a density continuous on `(0, 1]` has a
primitive there, the increment of the primitive from `D` to `1`, read as zero where `D` is not
positive, is the integral over `[0, 1]` of the density against the selector of `0 < D ≤ t`. -/
theorem primitive_eq_integral_selector (density primitive : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1))
    (hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt primitive (density t) t) (D : ℝ) (hD1 : D ≤ 1) :
    (if 0 < D then primitive 1 - primitive D else 0) =
      ∫ t in (0 : ℝ)..1, density t * (if 0 < D ∧ D ≤ t then 1 else 0) := by
  by_cases hpos : 0 < D
  · rw [if_pos hpos, integral_density_mul_selector density primitive D hpos hD1
      (hcont.mono fun t ht ↦ ⟨lt_of_lt_of_le hpos ht.1, ht.2⟩)
      fun t ht ↦ hderiv t ⟨lt_of_lt_of_le hpos ht.1, ht.2⟩]
  · rw [if_neg hpos]
    simp [hpos]

/-- **NOTE 2 section 5.3, the pointwise layer cake behind equation (20).** For `D ≤ 1` and
`K ≥ 1`, `1_{D>0} (1 - D)^K = ∫_0^1 K (1 - t)^(K-1) 1_{0<D≤t} dt`. -/
theorem truncation_layerCake (D : ℝ) (hD1 : D ≤ 1) (K : ℕ) (hK : 1 ≤ K) :
    (if 0 < D then (1 - D) ^ K else 0) =
      ∫ t in (0 : ℝ)..1, (K : ℝ) * (1 - t) ^ (K - 1) * (if 0 < D ∧ D ≤ t then 1 else 0) := by
  have hderiv : ∀ t ∈ Ioc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ -(1 - s) ^ K) ((K : ℝ) * (1 - t) ^ (K - 1)) t := by
    intro t _
    have hbase : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hneg : HasDerivAt (fun s : ℝ ↦ -(1 - s) ^ K)
        (-((K : ℝ) * (1 - t) ^ (K - 1) * -1)) t := (hbase.fun_pow K).neg
    convert hneg using 1
    ring
  have hvalue : (fun s : ℝ ↦ -(1 - s) ^ K) 1 - (fun s : ℝ ↦ -(1 - s) ^ K) D = (1 - D) ^ K := by
    simp only [sub_self, zero_pow (Nat.one_le_iff_ne_zero.mp hK), neg_zero, zero_sub, neg_neg]
  rw [← primitive_eq_integral_selector (fun t ↦ (K : ℝ) * (1 - t) ^ (K - 1))
    (fun s ↦ -(1 - s) ^ K) (by fun_prop) hderiv D hD1, hvalue]

/-- **NOTE 2 equation (28), the pointwise layer cake.** For `D ≤ 1`,
`1_{D>0} (D⁻¹ - 1) = ∫_0^1 t⁻² 1_{0<D≤t} dt`: the tail of `D⁻¹` over `[1, ∞)` of the note's
proof, after the substitution `s = 1/t`. -/
theorem inverse_layerCake (D : ℝ) (hD1 : D ≤ 1) :
    (if 0 < D then D⁻¹ - 1 else 0) =
      ∫ t in (0 : ℝ)..1, (t ^ 2)⁻¹ * (if 0 < D ∧ D ≤ t then 1 else 0) := by
  have hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ -s⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    have hneg : HasDerivAt (fun s : ℝ ↦ -s⁻¹) (-(-(t ^ 2)⁻¹)) t :=
      (hasDerivAt_inv ht.1.ne').neg
    rwa [neg_neg] at hneg
  have hvalue : (fun s : ℝ ↦ -s⁻¹) 1 - (fun s : ℝ ↦ -s⁻¹) D = D⁻¹ - 1 := by
    simp only [inv_one]
    ring
  rw [← primitive_eq_integral_selector (fun t ↦ (t ^ 2)⁻¹) (fun s ↦ -s⁻¹)
    (inverseDensity_beta_bound 0 2 one_lt_two).1 hderiv D hD1, hvalue]

/-- **NOTE 2 equation (29), the pointwise layer cake.** For `D ≤ 1` and `K ≥ 1`,
`1_{D>0} (1 - D)^K / D = ∫_0^1 ((K (1-t)^(K-1) t + (1-t)^K) / t²) 1_{0<D≤t} dt`; the density
is minus the derivative of the decreasing function `(1 - t)^K / t`, which vanishes at `t = 1`. -/
theorem remainder_layerCake (D : ℝ) (hD1 : D ≤ 1) (K : ℕ) (hK : 1 ≤ K) :
    (if 0 < D then (1 - D) ^ K / D else 0) =
      ∫ t in (0 : ℝ)..1, ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 *
        (if 0 < D ∧ D ≤ t then 1 else 0) := by
  have hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ -((1 - s) ^ K / s))
      (((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2) t := by
    intro t ht
    have hbase : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hneg : HasDerivAt (fun s : ℝ ↦ -((1 - s) ^ K / s))
        (-(((K : ℝ) * (1 - t) ^ (K - 1) * -1 * t - (1 - t) ^ K * 1) / t ^ 2)) t :=
      ((hbase.fun_pow K).fun_div (hasDerivAt_id' t) ht.1.ne').neg
    convert hneg using 1
    ring
  have hvalue : (fun s : ℝ ↦ -((1 - s) ^ K / s)) 1 - (fun s : ℝ ↦ -((1 - s) ^ K / s)) D =
      (1 - D) ^ K / D := by
    simp only [sub_self, zero_pow (Nat.one_le_iff_ne_zero.mp hK), zero_div, neg_zero, zero_sub,
      neg_neg]
  rw [← primitive_eq_integral_selector _ (fun s ↦ -((1 - s) ^ K / s))
    (remainderDensity_beta_bound K hK 0 2 one_lt_two).1 hderiv D hD1, hvalue]

/-- Pointwise, a numerator below a ceiling `M` makes the discarded ratio term
`1_{D>0} (N / D) (1 - D)^K` at most `M 1_{D>0} (1 - D)^K / D` whenever `D ≤ 1`. -/
theorem ratio_mul_decay_le (num den ceilingValue : ℝ) (hceiling : num ≤ ceilingValue)
    (hone : den ≤ 1) (K : ℕ) :
    (if 0 < den then num / den else 0) * (1 - den) ^ K ≤
      ceilingValue * (if 0 < den then (1 - den) ^ K / den else 0) := by
  by_cases hpos : 0 < den
  · rw [if_pos hpos, if_pos hpos]
    have hdecay : 0 ≤ (1 - den) ^ K := pow_nonneg (by linarith) K
    calc num / den * (1 - den) ^ K = num * (1 - den) ^ K / den := by ring
      _ ≤ ceilingValue * (1 - den) ^ K / den :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hceiling hdecay) hpos.le
      _ = ceilingValue * ((1 - den) ^ K / den) := by ring
  · simp [hpos]

end Pointwise

section FiniteReport

variable {Report : Type*} [Fintype Report]

/-- The density times the small-denominator mass is the report sum of the masses times the
density against each report's selector. -/
theorem density_mul_smallDenominatorMass (law : FiniteReportLaw Report)
    (den : Report → ℝ) (density : ℝ → ℝ) (t : ℝ) :
    density t * smallDenominatorMass law den t =
      ∑ report, law.mass report *
        (density t * (if 0 < den report ∧ den report ≤ t then 1 else 0)) := by
  simp only [smallDenominatorMass, FiniteReportLaw.expectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun report _ ↦ mul_left_comm _ _ _

/-- A density continuous on `(0, 1]` times the small-denominator mass of a report law is
integrable over `[0, 1]`: it is a finite sum of integrable selector terms. -/
theorem intervalIntegrable_density_mul_smallDenominatorMass (law : FiniteReportLaw Report)
    (den : Report → ℝ) (hnonneg : ∀ report, 0 ≤ den report) (density : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1)) :
    IntervalIntegrable (fun t ↦ density t * smallDenominatorMass law den t) volume 0 1 := by
  rw [funext (density_mul_smallDenominatorMass law den density),
    intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine integrable_finset_sum Finset.univ fun report _ ↦ ?_
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    ((intervalIntegrable_density_mul_selector density hcont (den report)
      (hnonneg report)).const_mul (law.mass report))

/-- **Layer cake over a finite report law.** If a profile of the denominator has a layer-cake
representation against a density continuous on `(0, 1]`, its expectation on the defined event
is the integral of the density against the small-denominator mass. The content is the exchange
of the report sum with the integral. -/
theorem expectation_profile_eq_integral (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1)
    (density profile : ℝ → ℝ) (hcont : ContinuousOn density (Ioc 0 1))
    (hprofile : ∀ D : ℝ, D ≤ 1 → (if 0 < D then profile D else 0) =
      ∫ t in (0 : ℝ)..1, density t * (if 0 < D ∧ D ≤ t then 1 else 0)) :
    law.expectation (fun report ↦ if 0 < den report then profile (den report) else 0) =
      ∫ t in (0 : ℝ)..1, density t * smallDenominatorMass law den t := by
  rw [funext (density_mul_smallDenominatorMass law den density),
    intervalIntegral.integral_finset_sum fun report _ ↦
      (intervalIntegrable_density_mul_selector density hcont (den report)
        (hnonneg report)).const_mul (law.mass report)]
  unfold FiniteReportLaw.expectation
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  rw [intervalIntegral.integral_const_mul, ← hprofile (den report) (hone report)]

/-- **Power-law insertion over a finite report law.** Under `P(0 < D ≤ t) ≤ C t^α` for
`0 < t ≤ 1`, a density nonnegative on `(0, 1]` integrated against the small-denominator mass is
at most the integral of any integrable function dominating the density times `C t^α`. -/
theorem integral_density_mul_smallDenominatorMass_le (law : FiniteReportLaw Report)
    (den : Report → ℝ) (hnonneg : ∀ report, 0 ≤ den report) (density : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1)) (hdensity : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ density t)
    (scale α : ℝ) (bound : ℝ → ℝ) (hbound : IntervalIntegrable bound volume 0 1)
    (hdominates : ∀ t ∈ Ioc (0 : ℝ) 1, density t * (scale * t ^ α) ≤ bound t)
    (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α) :
    ∫ t in (0 : ℝ)..1, density t * smallDenominatorMass law den t ≤
      ∫ t in (0 : ℝ)..1, bound t := by
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (intervalIntegrable_density_mul_smallDenominatorMass law den hnonneg density hcont)
    hbound fun t ht ↦ ?_
  exact (mul_le_mul_of_nonneg_left (hrate t ht.1 ht.2.le)
    (hdensity t ⟨ht.1, ht.2.le⟩)).trans (hdominates t ⟨ht.1, ht.2.le⟩)

/-- **NOTE 2 section 5.3, the layer cake for the unresolved mass.** For `K ≥ 1` the definedness
mass a `K`-term truncation leaves unresolved is `∫_0^1 K (1 - t)^(K-1) P(0 < D ≤ t) dt`. -/
theorem unresolvedMass_eq_integral (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1) (K : ℕ)
    (hK : 1 ≤ K) :
    unresolvedMass law den K =
      ∫ t in (0 : ℝ)..1, (K : ℝ) * (1 - t) ^ (K - 1) * smallDenominatorMass law den t := by
  refine Eq.trans ?_ (expectation_profile_eq_integral law den hnonneg hone
    (fun t ↦ (K : ℝ) * (1 - t) ^ (K - 1)) (fun D ↦ (1 - D) ^ K) (by fun_prop)
    fun D hD1 ↦ truncation_layerCake D hD1 K hK)
  unfold unresolvedMass
  congr 1
  funext report
  by_cases hpos : 0 < den report
  · simp [definedIndicator, hpos]
  · simp [definedIndicator, hpos]

/-- **NOTE 2 equation (20).** If `P(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1` with `α > -1`, the
definedness mass left unresolved after `K ≥ 1` terms is at most
`C Γ(α + 1) Γ(K + 1) / Γ(K + α + 1)`. -/
theorem unresolvedMass_le_gamma (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1) (scale α : ℝ)
    (hα : -1 < α) (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α)
    (K : ℕ) (hK : 1 ≤ K) :
    unresolvedMass law den K ≤
      scale * (Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1)) := by
  obtain ⟨hcont, hdensity, hbound, hvalue⟩ := truncationDensity_beta_bound K hK scale α hα
  rw [unresolvedMass_eq_integral law den hnonneg hone K hK, ← hvalue]
  exact integral_density_mul_smallDenominatorMass_le law den hnonneg _ hcont hdensity scale α _
    hbound (fun t _ ↦ le_of_eq (by ring)) hrate

/-- **NOTE 2 equations (18) and (20) together.** Under `0 ≤ N ≤ D ≤ 1` and the power law
`P(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1` with `α > -1`, the normalization-aware replica
certificate holds after `K ≥ 1` terms with the sharp tolerance
`τ_K = C Γ(α + 1) Γ(K + 1) / Γ(K + α + 1)`, whenever the retained mass is positive. -/
theorem replica_certificate_of_rate (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (hnum : ∀ report, 0 ≤ num report) (hle : ∀ report, num report ≤ den report)
    (hone : ∀ report, den report ≤ 1) (scale α : ℝ) (hα : -1 < α)
    (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α) (K : ℕ)
    (hK : 1 ≤ K) (hretained : 0 < retainedMass law den K) :
    retainedNumerator law num den K / (retainedMass law den K +
        scale * (Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1))) ≤
        conditionalExpectation law (fun other ↦ 0 < den other) (ratioOnDefined num den) ∧
      conditionalExpectation law (fun other ↦ 0 < den other) (ratioOnDefined num den) ≤
        (retainedNumerator law num den K +
            scale * (Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1))) /
          (retainedMass law den K +
            scale * (Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1))) :=
  replica_certificate law num den hnum hle hone K _
    (unresolvedMass_le_gamma law den (fun report ↦ (hnum report).trans (hle report)) hone scale
      α hα hrate K hK) hretained

/-- **NOTE 2 equation (28).** If `P(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1` with `α > 1`, the
expected inverse denominator on the defined event is at most `P(D > 0) + C / (α - 1)`. -/
theorem expectation_inverse_le (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1) (scale α : ℝ)
    (hα : 1 < α) (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α) :
    law.expectation (ratioOnDefined (fun _ ↦ 1) den) ≤
      law.expectation (definedIndicator (fun report ↦ 0 < den report)) + scale / (α - 1) := by
  obtain ⟨hcont, hdensity, hbound, hdominates, hvalue⟩ := inverseDensity_beta_bound scale α hα
  have hlayer : law.expectation (fun report ↦
      if 0 < den report then (den report)⁻¹ - 1 else 0) =
      ∫ t in (0 : ℝ)..1, (t ^ 2)⁻¹ * smallDenominatorMass law den t :=
    expectation_profile_eq_integral law den hnonneg hone _ (fun D ↦ D⁻¹ - 1) hcont
      fun D hD1 ↦ inverse_layerCake D hD1
  have hsplit : law.expectation (ratioOnDefined (fun _ ↦ 1) den) =
      law.expectation (definedIndicator (fun report ↦ 0 < den report)) +
        law.expectation (fun report ↦ if 0 < den report then (den report)⁻¹ - 1 else 0) := by
    unfold FiniteReportLaw.expectation
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun report _ ↦ ?_
    by_cases hpos : 0 < den report
    · simp only [ratioOnDefined, definedIndicator, if_pos hpos]
      ring
    · simp only [ratioOnDefined, definedIndicator, if_neg hpos]
      ring
  have hle : ∫ t in (0 : ℝ)..1, (t ^ 2)⁻¹ * smallDenominatorMass law den t ≤
      ∫ t in (0 : ℝ)..1, scale * t ^ (α - 2) :=
    integral_density_mul_smallDenominatorMass_le law den hnonneg _ hcont hdensity scale α _
      hbound hdominates hrate
  rw [hsplit, hlayer]
  linarith [hle, hvalue]

/-- **NOTE 2 equation (29).** Let `N ≤ M` with `M ≥ 0`, `0 ≤ D ≤ 1`, `P(0 < D ≤ t) ≤ C t^α` for
`0 < t ≤ 1` with `α > 1`, and `K ≥ 1`. The numerator a `K`-term geometric truncation leaves
unresolved is at most `M C Γ(α + 1) / (α - 1) · Γ(K + 1) / Γ(K + α)`. -/
theorem unresolvedNumerator_le_gamma (law : FiniteReportLaw Report) (num den : Report → ℝ)
    (ceilingValue : ℝ) (hceilingNonneg : 0 ≤ ceilingValue)
    (hceiling : ∀ report, num report ≤ ceilingValue)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1) (scale α : ℝ)
    (hα : 1 < α) (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α)
    (K : ℕ) (hK : 1 ≤ K) :
    unresolvedNumerator law num den K ≤
      ceilingValue * scale * (Real.Gamma (α + 1) / (α - 1)) *
        (Real.Gamma (K + 1) / Real.Gamma (K + α)) := by
  obtain ⟨hcont, hdensity, hbound, hdominates, hvalue⟩ :=
    remainderDensity_beta_bound K hK scale α hα
  have hceilingStep : unresolvedNumerator law num den K ≤ ceilingValue *
      law.expectation (fun report ↦
        if 0 < den report then (1 - den report) ^ K / den report else 0) := by
    unfold unresolvedNumerator FiniteReportLaw.expectation
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun report _ ↦ ?_
    calc law.mass report * (ratioOnDefined num den report * (1 - den report) ^ K)
        ≤ law.mass report * (ceilingValue *
          (if 0 < den report then (1 - den report) ^ K / den report else 0)) :=
          mul_le_mul_of_nonneg_left (ratio_mul_decay_le (num report) (den report) ceilingValue
            (hceiling report) (hone report) K) (law.mass_nonneg report)
      _ = ceilingValue * (law.mass report *
          (if 0 < den report then (1 - den report) ^ K / den report else 0)) := by ring
  have hlayer : law.expectation (fun report ↦
      if 0 < den report then (1 - den report) ^ K / den report else 0) =
      ∫ t in (0 : ℝ)..1, ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 *
        smallDenominatorMass law den t :=
    expectation_profile_eq_integral law den hnonneg hone _ (fun D ↦ (1 - D) ^ K / D) hcont
      fun D hD1 ↦ remainder_layerCake D hD1 K hK
  have hle : ∫ t in (0 : ℝ)..1, ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 *
      smallDenominatorMass law den t ≤ ∫ t in (0 : ℝ)..1, scale *
        ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) :=
    integral_density_mul_smallDenominatorMass_le law den hnonneg _ hcont hdensity scale α _
      hbound hdominates hrate
  calc unresolvedNumerator law num den K
      ≤ ceilingValue * law.expectation (fun report ↦
          if 0 < den report then (1 - den report) ^ K / den report else 0) := hceilingStep
    _ = ceilingValue * ∫ t in (0 : ℝ)..1,
          ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 *
            smallDenominatorMass law den t := by rw [hlayer]
    _ ≤ ceilingValue * ∫ t in (0 : ℝ)..1, scale *
          ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) :=
        mul_le_mul_of_nonneg_left hle hceilingNonneg
    _ = ceilingValue * scale * (Real.Gamma (α + 1) / (α - 1)) *
          (Real.Gamma (K + 1) / Real.Gamma (K + α)) := by
        rw [hvalue]
        ring

end FiniteReport

section Measure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **NOTE 2 section 5.3, the layer cake over a measure.** For an s-finite measure and a
measurable denominator in `[0, 1]`, if a profile has a layer-cake representation against a
measurable density that is continuous and nonnegative on `(0, 1]`, the upper integral of the
profile on the defined event is `∫_(0,1] density(t) μ(0 < D ≤ t) dt`. The content is Tonelli's
exchange of the two integrals. -/
theorem lintegral_profile_eq_lintegral (μ : Measure Ω) [SFinite μ] (den : Ω → ℝ)
    (hmeas : Measurable den) (hnonneg : ∀ ω, 0 ≤ den ω) (hone : ∀ ω, den ω ≤ 1)
    (density profile : ℝ → ℝ) (hdensityMeasurable : Measurable density)
    (hcont : ContinuousOn density (Ioc 0 1)) (hdensity : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ density t)
    (hprofile : ∀ D : ℝ, D ≤ 1 → (if 0 < D then profile D else 0) =
      ∫ t in (0 : ℝ)..1, density t * (if 0 < D ∧ D ≤ t then 1 else 0)) :
    ∫⁻ ω, ENNReal.ofReal (if 0 < den ω then profile (den ω) else 0) ∂μ =
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (density t) * μ {ω | 0 < den ω ∧ den ω ≤ t} := by
  have hslice : ∀ ω, ENNReal.ofReal (if 0 < den ω then profile (den ω) else 0) =
      ∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0)) := by
    intro ω
    have hint : IntegrableOn
        (fun t ↦ density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0)) (Ioc 0 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegrable_density_mul_selector density hcont (den ω) (hnonneg ω))
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun t ↦ density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      show (0 : ℝ) ≤ density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0)
      exact mul_nonneg (hdensity t ht) (by split_ifs <;> norm_num)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
      ← intervalIntegral.integral_of_le zero_le_one, hprofile (den ω) (hone ω)]
  have hevent : ∀ t : ℝ, MeasurableSet {ω | 0 < den ω ∧ den ω ≤ t} := fun t ↦
    (measurableSet_lt measurable_const hmeas).inter (measurableSet_le hmeas measurable_const)
  have hsection : ∀ t : ℝ, ∫⁻ ω,
      ENNReal.ofReal (density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0)) ∂μ =
        ENNReal.ofReal (density t) * μ {ω | 0 < den ω ∧ den ω ≤ t} := by
    intro t
    have hfun : (fun ω ↦ ENNReal.ofReal
        (density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0))) =
        fun ω ↦ ENNReal.ofReal (density t) * {ω | 0 < den ω ∧ den ω ≤ t}.indicator 1 ω := by
      funext ω
      by_cases hω : 0 < den ω ∧ den ω ≤ t
      · simp [hω]
      · simp [hω]
    rw [hfun, lintegral_const_mul _ (measurable_one.indicator (hevent t)),
      lintegral_indicator_one (hevent t)]
  have hjoint : Measurable fun p : Ω × ℝ ↦
      ENNReal.ofReal (density p.2 * (if 0 < den p.1 ∧ den p.1 ≤ p.2 then 1 else 0)) := by
    have hset : MeasurableSet {p : Ω × ℝ | 0 < den p.1 ∧ den p.1 ≤ p.2} :=
      (measurableSet_lt measurable_const (hmeas.comp measurable_fst)).inter
        (measurableSet_le (hmeas.comp measurable_fst) measurable_snd)
    exact ENNReal.measurable_ofReal.comp ((hdensityMeasurable.comp measurable_snd).mul
      (Measurable.ite hset measurable_const measurable_const))
  calc ∫⁻ ω, ENNReal.ofReal (if 0 < den ω then profile (den ω) else 0) ∂μ
      = ∫⁻ ω, (∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0))) ∂μ :=
        lintegral_congr hslice
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, (∫⁻ ω,
          ENNReal.ofReal (density t * (if 0 < den ω ∧ den ω ≤ t then 1 else 0)) ∂μ) :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (density t) * μ {ω | 0 < den ω ∧ den ω ≤ t} :=
        lintegral_congr hsection

/-- **Power-law insertion over a measure.** Under `μ(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1` with
`C ≥ 0`, the layer-cake integral of a density nonnegative on `(0, 1]` is at most the integral of
any integrable function dominating the density times `C t^α` there. -/
theorem lintegral_density_mul_measure_le (μ : Measure Ω) (den : Ω → ℝ) (density : ℝ → ℝ)
    (hdensity : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ density t) (scale α : ℝ) (hscale : 0 ≤ scale)
    (bound : ℝ → ℝ) (hbound : IntervalIntegrable bound volume 0 1)
    (hdominates : ∀ t ∈ Ioc (0 : ℝ) 1, density t * (scale * t ^ α) ≤ bound t)
    (hrate : ∀ t, 0 < t → t ≤ 1 →
      μ {ω | 0 < den ω ∧ den ω ≤ t} ≤ ENNReal.ofReal (scale * t ^ α)) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (density t) * μ {ω | 0 < den ω ∧ den ω ≤ t} ≤
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, bound t) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    show (0 : ℝ) ≤ bound t
    exact (mul_nonneg (hdensity t ht)
      (mul_nonneg hscale (Real.rpow_nonneg ht.1.le α))).trans (hdominates t ht)
  rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hbound) hnn]
  refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
  calc ENNReal.ofReal (density t) * μ {ω | 0 < den ω ∧ den ω ≤ t}
      ≤ ENNReal.ofReal (density t) * ENNReal.ofReal (scale * t ^ α) :=
        mul_le_mul_left' (hrate t ht.1 ht.2) _
    _ = ENNReal.ofReal (density t * (scale * t ^ α)) :=
        (ENNReal.ofReal_mul (hdensity t ht)).symm
    _ ≤ ENNReal.ofReal (bound t) := ENNReal.ofReal_le_ofReal (hdominates t ht)

/-- **NOTE 2 equation (20) over a measure.** For an s-finite measure, a measurable denominator
in `[0, 1]` with `μ(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1`, `C ≥ 0`, `α > -1` and `K ≥ 1`, the
upper integral of `1_{D>0} (1 - D)^K` is at most `C Γ(α + 1) Γ(K + 1) / Γ(K + α + 1)`. -/
theorem lintegral_truncation_le_gamma (μ : Measure Ω) [SFinite μ] (den : Ω → ℝ)
    (hmeas : Measurable den) (hnonneg : ∀ ω, 0 ≤ den ω) (hone : ∀ ω, den ω ≤ 1) (scale α : ℝ)
    (hscale : 0 ≤ scale) (hα : -1 < α)
    (hrate : ∀ t, 0 < t → t ≤ 1 →
      μ {ω | 0 < den ω ∧ den ω ≤ t} ≤ ENNReal.ofReal (scale * t ^ α)) (K : ℕ) (hK : 1 ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (if 0 < den ω then (1 - den ω) ^ K else 0) ∂μ ≤
      ENNReal.ofReal
        (scale * (Real.Gamma (α + 1) * Real.Gamma (K + 1) / Real.Gamma (K + α + 1))) := by
  obtain ⟨hcont, hdensity, hbound, hvalue⟩ := truncationDensity_beta_bound K hK scale α hα
  rw [lintegral_profile_eq_lintegral μ den hmeas hnonneg hone _ (fun D ↦ (1 - D) ^ K)
    (by fun_prop) hcont hdensity fun D hD1 ↦ truncation_layerCake D hD1 K hK, ← hvalue]
  exact lintegral_density_mul_measure_le μ den _ hdensity scale α hscale _ hbound
    (fun t _ ↦ le_of_eq (by ring)) hrate

/-- **NOTE 2 equation (28) over a measure.** For an s-finite measure and a measurable
denominator in `[0, 1]` with `μ(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1`, `C ≥ 0` and `α > 1`, the
upper integral of `1_{D>0} D⁻¹` is at most `μ(D > 0) + C / (α - 1)`. -/
theorem lintegral_inverse_le (μ : Measure Ω) [SFinite μ] (den : Ω → ℝ) (hmeas : Measurable den)
    (hnonneg : ∀ ω, 0 ≤ den ω) (hone : ∀ ω, den ω ≤ 1) (scale α : ℝ) (hscale : 0 ≤ scale)
    (hα : 1 < α)
    (hrate : ∀ t, 0 < t → t ≤ 1 →
      μ {ω | 0 < den ω ∧ den ω ≤ t} ≤ ENNReal.ofReal (scale * t ^ α)) :
    ∫⁻ ω, ENNReal.ofReal (ratioOnDefined (fun _ ↦ 1) den ω) ∂μ ≤
      μ {ω | 0 < den ω} + ENNReal.ofReal (scale / (α - 1)) := by
  obtain ⟨hcont, hdensity, hbound, hdominates, hvalue⟩ := inverseDensity_beta_bound scale α hα
  have hpositive : MeasurableSet {ω | 0 < den ω} := measurableSet_lt measurable_const hmeas
  have hsplit : ∀ ω, ENNReal.ofReal (ratioOnDefined (fun _ ↦ 1) den ω) =
      {ω | 0 < den ω}.indicator 1 ω +
        ENNReal.ofReal (if 0 < den ω then (den ω)⁻¹ - 1 else 0) := by
    intro ω
    by_cases hpos : 0 < den ω
    · have hinv : (0 : ℝ) ≤ (den ω)⁻¹ - 1 := by
        have hle := (one_le_inv₀ hpos).mpr (hone ω)
        linarith
      simp only [ratioOnDefined, if_pos hpos,
        Set.indicator_of_mem (show ω ∈ {ω | 0 < den ω} from hpos), Pi.one_apply]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hinv]
      congr 1
      ring
    · simp [ratioOnDefined, hpos]
  have hlayer := lintegral_profile_eq_lintegral μ den hmeas hnonneg hone _ (fun D ↦ D⁻¹ - 1)
    (by fun_prop) hcont hdensity fun D hD1 ↦ inverse_layerCake D hD1
  have hle := lintegral_density_mul_measure_le μ den _ hdensity scale α hscale _ hbound
    hdominates hrate
  rw [lintegral_congr hsplit, lintegral_add_left (measurable_one.indicator hpositive),
    lintegral_indicator_one hpositive, hlayer, ← hvalue]
  exact add_le_add_left hle _

/-- **NOTE 2 equation (29) over a measure.** For an s-finite measure, `N ≤ M` with `M ≥ 0`, a
measurable denominator in `[0, 1]` with `μ(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1`, `C ≥ 0`,
`α > 1` and `K ≥ 1`, the upper integral of the discarded term `1_{D>0} (N / D) (1 - D)^K` is at
most `M C Γ(α + 1) / (α - 1) · Γ(K + 1) / Γ(K + α)`. -/
theorem lintegral_unresolvedNumerator_le_gamma (μ : Measure Ω) [SFinite μ] (num den : Ω → ℝ)
    (hmeas : Measurable den) (ceilingValue : ℝ) (hceilingNonneg : 0 ≤ ceilingValue)
    (hceiling : ∀ ω, num ω ≤ ceilingValue) (hnonneg : ∀ ω, 0 ≤ den ω) (hone : ∀ ω, den ω ≤ 1)
    (scale α : ℝ) (hscale : 0 ≤ scale) (hα : 1 < α)
    (hrate : ∀ t, 0 < t → t ≤ 1 →
      μ {ω | 0 < den ω ∧ den ω ≤ t} ≤ ENNReal.ofReal (scale * t ^ α)) (K : ℕ) (hK : 1 ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (ratioOnDefined num den ω * (1 - den ω) ^ K) ∂μ ≤
      ENNReal.ofReal (ceilingValue * scale * (Real.Gamma (α + 1) / (α - 1)) *
        (Real.Gamma (K + 1) / Real.Gamma (K + α))) := by
  obtain ⟨hcont, hdensity, hbound, hdominates, hvalue⟩ :=
    remainderDensity_beta_bound K hK scale α hα
  have hlayer := lintegral_profile_eq_lintegral μ den hmeas hnonneg hone _
    (fun D ↦ (1 - D) ^ K / D) (by fun_prop) hcont hdensity
    fun D hD1 ↦ remainder_layerCake D hD1 K hK
  have hle := lintegral_density_mul_measure_le μ den _ hdensity scale α hscale _ hbound
    hdominates hrate
  calc ∫⁻ ω, ENNReal.ofReal (ratioOnDefined num den ω * (1 - den ω) ^ K) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ceilingValue *
          ENNReal.ofReal (if 0 < den ω then (1 - den ω) ^ K / den ω else 0) ∂μ :=
        lintegral_mono fun ω ↦ (ENNReal.ofReal_le_ofReal (ratio_mul_decay_le (num ω) (den ω)
          ceilingValue (hceiling ω) (hone ω) K)).trans_eq (ENNReal.ofReal_mul hceilingNonneg)
    _ = ENNReal.ofReal ceilingValue * ∫⁻ ω,
          ENNReal.ofReal (if 0 < den ω then (1 - den ω) ^ K / den ω else 0) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ceilingValue * ENNReal.ofReal (∫ t in (0 : ℝ)..1, scale *
          ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K)) := by
        rw [hlayer]
        exact mul_le_mul_left' hle _
    _ = ENNReal.ofReal (ceilingValue * scale * (Real.Gamma (α + 1) / (α - 1)) *
          (Real.Gamma (K + 1) / Real.Gamma (K + α))) := by
        rw [hvalue, ← ENNReal.ofReal_mul hceilingNonneg]
        congr 1
        ring

/-- **NOTE 2 section 6.3, the divergence criterion.** Let `μ` be a finite measure and `D` a
measurable denominator in `[0, 1]`. If a matching lower small-denominator bound
`μ(0 < D ≤ t) ≥ c t^α` holds for `0 < t ≤ θ` with `c > 0`, `0 < θ ≤ 1` and exponent `α ≤ 1`,
and the numerator is at least `ν > 0` on the small-denominator event `0 < D ≤ θ`, then the upper
integral of the ratio on its defined event is infinite. -/
theorem lintegral_ratioOnDefined_eq_top (μ : Measure Ω) [IsFiniteMeasure μ] (num den : Ω → ℝ)
    (hmeas : Measurable den) (hnonneg : ∀ ω, 0 ≤ den ω) (hone : ∀ ω, den ω ≤ 1)
    (scale α threshold level : ℝ) (hscale : 0 < scale) (hα : α ≤ 1)
    (hthreshold : 0 < threshold) (hthresholdOne : threshold ≤ 1) (hlevel : 0 < level)
    (hrate : ∀ t, 0 < t → t ≤ threshold →
      ENNReal.ofReal (scale * t ^ α) ≤ μ {ω | 0 < den ω ∧ den ω ≤ t})
    (hlower : ∀ ω, 0 < den ω → den ω ≤ threshold → level ≤ num ω) :
    ∫⁻ ω, ENNReal.ofReal (ratioOnDefined num den ω) ∂μ = ⊤ := by
  have hinvtop : ∫⁻ t in Ioc (0 : ℝ) threshold, ENNReal.ofReal t⁻¹ = ⊤ := by
    by_contra hfinite
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) threshold)] fun t : ℝ ↦ t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      show (0 : ℝ) ≤ t⁻¹
      exact inv_nonneg.mpr ht.1.le
    have hon : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Ioc 0 threshold) volume :=
      ⟨measurable_id.inv.aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_top_iff_ne_top.mpr hfinite)⟩
    have hinterval := (intervalIntegrable_iff_integrableOn_Ioc_of_le hthreshold.le).mpr hon
    rw [intervalIntegrable_inv_iff, uIcc_of_le hthreshold.le] at hinterval
    rcases hinterval with hzero | hnot
    · exact hthreshold.ne hzero
    · exact hnot ⟨le_rfl, hthreshold.le⟩
  have hlayertop : ∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((t ^ 2)⁻¹) * μ {ω | 0 < den ω ∧ den ω ≤ t} = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : ENNReal)
        = ENNReal.ofReal scale * ∫⁻ t in Ioc (0 : ℝ) threshold, ENNReal.ofReal t⁻¹ := by
          rw [hinvtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hscale).ne']
      _ = ∫⁻ t in Ioc (0 : ℝ) threshold, ENNReal.ofReal scale * ENNReal.ofReal t⁻¹ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) threshold,
            ENNReal.ofReal ((t ^ 2)⁻¹) * μ {ω | 0 < den ω ∧ den ω ≤ t} := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
          have ht0 : t ≠ 0 := ht.1.ne'
          have hpow : t ≤ t ^ α := by
            simpa using Real.rpow_le_rpow_of_exponent_ge ht.1 (ht.2.trans hthresholdOne) hα
          have hreal : scale * t⁻¹ ≤ (t ^ 2)⁻¹ * (scale * t ^ α) := by
            calc scale * t⁻¹ = scale * (t * t⁻¹) * t⁻¹ := by rw [mul_inv_cancel₀ ht0, mul_one]
              _ = (t ^ 2)⁻¹ * (scale * t) := by ring
              _ ≤ (t ^ 2)⁻¹ * (scale * t ^ α) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hscale.le)
                  (inv_nonneg.mpr (sq_nonneg t))
          calc ENNReal.ofReal scale * ENNReal.ofReal t⁻¹ = ENNReal.ofReal (scale * t⁻¹) :=
                (ENNReal.ofReal_mul hscale.le).symm
            _ ≤ ENNReal.ofReal ((t ^ 2)⁻¹ * (scale * t ^ α)) := ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal ((t ^ 2)⁻¹) * ENNReal.ofReal (scale * t ^ α) :=
                ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg t))
            _ ≤ ENNReal.ofReal ((t ^ 2)⁻¹) * μ {ω | 0 < den ω ∧ den ω ≤ t} :=
                mul_le_mul_left' (hrate t ht.1 ht.2) _
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1,
            ENNReal.ofReal ((t ^ 2)⁻¹) * μ {ω | 0 < den ω ∧ den ω ≤ t} :=
          lintegral_mono_set (Ioc_subset_Ioc_right hthresholdOne)
  obtain ⟨hcont, hdensity, -, -, -⟩ := inverseDensity_beta_bound 1 2 one_lt_two
  have hlayer : ∫⁻ ω, ENNReal.ofReal (if 0 < den ω then (den ω)⁻¹ - 1 else 0) ∂μ = ⊤ := by
    rw [lintegral_profile_eq_lintegral μ den hmeas hnonneg hone _ (fun D ↦ D⁻¹ - 1)
      (by fun_prop) hcont hdensity fun D hD1 ↦ inverse_layerCake D hD1]
    exact hlayertop
  have hpoint : ∀ ω, ENNReal.ofReal level *
      ENNReal.ofReal (if 0 < den ω then (den ω)⁻¹ - 1 else 0) ≤
        ENNReal.ofReal (ratioOnDefined num den ω) + ENNReal.ofReal (level * threshold⁻¹) := by
    intro ω
    rw [← ENNReal.ofReal_mul hlevel.le]
    by_cases hpos : 0 < den ω
    · simp only [ratioOnDefined, if_pos hpos]
      by_cases hsmall : den ω ≤ threshold
      · have hstep : level * ((den ω)⁻¹ - 1) ≤ num ω / den ω := by
          have hinvNonneg : 0 ≤ (den ω)⁻¹ := inv_nonneg.mpr hpos.le
          calc level * ((den ω)⁻¹ - 1) ≤ level * (den ω)⁻¹ :=
                mul_le_mul_of_nonneg_left (by linarith) hlevel.le
            _ ≤ num ω * (den ω)⁻¹ :=
                mul_le_mul_of_nonneg_right (hlower ω hpos hsmall) hinvNonneg
            _ = num ω / den ω := (div_eq_mul_inv _ _).symm
        exact (ENNReal.ofReal_le_ofReal hstep).trans le_self_add
      · have hstep : level * ((den ω)⁻¹ - 1) ≤ level * threshold⁻¹ := by
          have hinv : (den ω)⁻¹ ≤ threshold⁻¹ := inv_anti₀ hthreshold (not_le.mp hsmall).le
          exact mul_le_mul_of_nonneg_left (by linarith) hlevel.le
        exact (ENNReal.ofReal_le_ofReal hstep).trans le_add_self
    · simp only [ratioOnDefined, if_neg hpos, mul_zero, ENNReal.ofReal_zero]
      exact zero_le _
  have hsum : ⊤ ≤ ∫⁻ ω, ENNReal.ofReal (ratioOnDefined num den ω) ∂μ +
      ENNReal.ofReal (level * threshold⁻¹) * μ univ := by
    calc (⊤ : ENNReal)
        = ENNReal.ofReal level *
            ∫⁻ ω, ENNReal.ofReal (if 0 < den ω then (den ω)⁻¹ - 1 else 0) ∂μ := by
          rw [hlayer, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hlevel).ne']
      _ = ∫⁻ ω, ENNReal.ofReal level *
            ENNReal.ofReal (if 0 < den ω then (den ω)⁻¹ - 1 else 0) ∂μ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (ratioOnDefined num den ω) +
            ENNReal.ofReal (level * threshold⁻¹)) ∂μ := lintegral_mono hpoint
      _ = ∫⁻ ω, ENNReal.ofReal (ratioOnDefined num den ω) ∂μ +
            ENNReal.ofReal (level * threshold⁻¹) * μ univ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
  by_contra hfinite
  have hlt : ∫⁻ ω, ENNReal.ofReal (ratioOnDefined num den ω) ∂μ +
      ENNReal.ofReal (level * threshold⁻¹) * μ univ < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hfinite,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)⟩
  exact hlt.ne (top_le_iff.mp hsum)

/-- **NOTE 2 section 6.3, denominator bounds alone do not decide divergence.** Under the uniform
law on `(0, 1]` the clipped identity denominator `U = max 0 (min ω 1)` has the matching lower
bound `μ(0 < U ≤ t) ≥ t` with exponent one. With numerator one the ratio `1/U`, the note's
slope, has infinite expectation, as the divergence criterion predicts; with numerator `U`, which
vanishes as fast as the denominator, the same denominator law gives expectation at most one. -/
theorem uniformDenominator_divergence_depends_on_numerator :
    (∀ t : ℝ, 0 < t → t ≤ 1 → ENNReal.ofReal (1 * t ^ (1 : ℝ)) ≤
      volume.restrict (Ioc (0 : ℝ) 1) {ω | 0 < max 0 (min ω 1) ∧ max 0 (min ω 1) ≤ t}) ∧
    ∫⁻ ω in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (ratioOnDefined (fun _ ↦ 1) (fun ω : ℝ ↦ max 0 (min ω 1)) ω) = ⊤ ∧
    ∫⁻ ω in Ioc (0 : ℝ) 1, ENNReal.ofReal (ratioOnDefined (fun ω : ℝ ↦ max 0 (min ω 1))
      (fun ω : ℝ ↦ max 0 (min ω 1)) ω) ≤ 1 := by
  have hmeas : Measurable fun ω : ℝ ↦ max 0 (min ω 1) :=
    measurable_const.max (measurable_id.min measurable_const)
  have hnonneg : ∀ ω : ℝ, 0 ≤ max 0 (min ω 1) := fun ω ↦ le_max_left _ _
  have hone : ∀ ω : ℝ, max 0 (min ω 1) ≤ 1 := fun ω ↦ max_le zero_le_one (min_le_right _ _)
  have hrate : ∀ t : ℝ, 0 < t → t ≤ 1 → ENNReal.ofReal (1 * t ^ (1 : ℝ)) ≤
      volume.restrict (Ioc (0 : ℝ) 1) {ω | 0 < max 0 (min ω 1) ∧ max 0 (min ω 1) ≤ t} := by
    intro t ht ht1
    have hset : {ω : ℝ | 0 < max 0 (min ω 1) ∧ max 0 (min ω 1) ≤ t} ∩ Ioc 0 1 = Ioc 0 t := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioc]
      constructor
      · rintro ⟨⟨_, hle⟩, hω0, hω1⟩
        rw [min_eq_left hω1, max_eq_right hω0.le] at hle
        exact ⟨hω0, hle⟩
      · rintro ⟨hω0, hωt⟩
        have hω1 : ω ≤ 1 := hωt.trans ht1
        rw [min_eq_left hω1, max_eq_right hω0.le]
        exact ⟨⟨hω0, hωt⟩, hω0, hω1⟩
    refine le_of_eq ?_
    have hevent : MeasurableSet {ω : ℝ | 0 < max 0 (min ω 1) ∧ max 0 (min ω 1) ≤ t} :=
      (measurableSet_lt measurable_const hmeas).inter (measurableSet_le hmeas measurable_const)
    rw [Measure.restrict_apply hevent, hset, Real.volume_Ioc, Real.rpow_one, one_mul, sub_zero]
  refine ⟨hrate, ?_, ?_⟩
  · exact lintegral_ratioOnDefined_eq_top (volume.restrict (Ioc (0 : ℝ) 1)) (fun _ ↦ 1) _ hmeas
      hnonneg hone 1 1 1 1 one_pos le_rfl one_pos le_rfl one_pos hrate fun _ _ _ ↦ le_rfl
  · calc ∫⁻ ω in Ioc (0 : ℝ) 1, ENNReal.ofReal (ratioOnDefined (fun ω : ℝ ↦ max 0 (min ω 1))
          (fun ω : ℝ ↦ max 0 (min ω 1)) ω)
        ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, 1 := lintegral_mono fun ω ↦
          (ENNReal.ofReal_le_ofReal (ratioOnDefined_le_one _ _ (fun _ ↦ le_rfl) ω)).trans_eq
            ENNReal.ofReal_one
      _ = 1 := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
            ENNReal.ofReal_one, one_mul]

end Measure

end

end Descent.Portability.SmallDenominatorLayerCake
