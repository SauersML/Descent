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
module proves them. The engine is the pointwise layer cake: for a denominator `D` in `[0, 1]`
and a density with a primitive on `(0, 1]`, the increment of the primitive from `D` to `1`,
read as zero where `D` vanishes, is the integral over `t ∈ [0, 1]` of the density against the
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
`Γ(α) + Γ(α-1) = α Γ(α-1)`.

Narrower and stronger than the note. The beta evaluation and (20) hold for every real `α > -1`,
not only `α > 0`. The power law is used only on `0 < t < 1`. The report-law results take the
bounds `0 ≤ D ≤ 1` pointwise, as the corpus certificates do.

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

section Pointwise

/-- On a positive denominator, the density times the selector of `0 < D ≤ t` is the density
restricted to the half-line `t ≥ D`. -/
theorem selector_eq_indicator (density : ℝ → ℝ) (D : ℝ) (hpos : 0 < D) :
    (fun t ↦ density t * (if 0 < D ∧ D ≤ t then 1 else 0)) = (Ici D).indicator density := by
  funext t
  by_cases ht : D ≤ t
  · simp [Set.indicator_apply, hpos, ht]
  · simp [Set.indicator_apply, hpos, ht]

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
density is continuous on `(0, 1]` and the denominator lies in `[0, 1]`. -/
theorem intervalIntegrable_density_mul_selector (density : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1)) (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1) :
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
  have hcont : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioc 0 1) :=
    (continuous_pow 2).continuousOn.inv₀ fun t ht ↦ pow_ne_zero 2 ht.1.ne'
  have hvalue : (fun s : ℝ ↦ -s⁻¹) 1 - (fun s : ℝ ↦ -s⁻¹) D = D⁻¹ - 1 := by
    simp only [inv_one]
    ring
  rw [← primitive_eq_integral_selector (fun t ↦ (t ^ 2)⁻¹) (fun s ↦ -s⁻¹) hcont hderiv D hD1,
    hvalue]

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
      ((hbase.fun_pow K).fun_div hasDerivAt_id' ht.1.ne').neg
    convert hneg using 1
    ring
  have hcont : ContinuousOn
      (fun t : ℝ ↦ ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2) (Ioc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ ↦
      (K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K).continuousOn.div
      (continuous_pow 2).continuousOn fun t ht ↦ pow_ne_zero 2 ht.1.ne'
  have hvalue : (fun s : ℝ ↦ -((1 - s) ^ K / s)) 1 - (fun s : ℝ ↦ -((1 - s) ^ K / s)) D =
      (1 - D) ^ K / D := by
    simp only [sub_self, zero_pow (Nat.one_le_iff_ne_zero.mp hK), zero_div, neg_zero, zero_sub,
      neg_neg]
  rw [← primitive_eq_integral_selector _ (fun s ↦ -((1 - s) ^ K / s)) hcont hderiv D hD1,
    hvalue]

end Pointwise

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

end Beta

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
    (den : Report → ℝ) (hnonneg : ∀ report, 0 ≤ den report)
    (hone : ∀ report, den report ≤ 1) (density : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1)) :
    IntervalIntegrable (fun t ↦ density t * smallDenominatorMass law den t) volume 0 1 := by
  rw [funext (density_mul_smallDenominatorMass law den density),
    intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine integrable_finset_sum Finset.univ fun report _ ↦ ?_
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    ((intervalIntegrable_density_mul_selector density hcont (den report) (hnonneg report)
      (hone report)).const_mul (law.mass report))

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
      (intervalIntegrable_density_mul_selector density hcont (den report) (hnonneg report)
        (hone report)).const_mul (law.mass report)]
  unfold FiniteReportLaw.expectation
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  rw [intervalIntegral.integral_const_mul, hprofile (den report) (hone report)]

/-- **Power-law insertion over a finite report law.** Under `P(0 < D ≤ t) ≤ C t^α` for
`0 < t ≤ 1`, a density nonnegative on `(0, 1]` integrated against the small-denominator mass is
at most the integral of any integrable function dominating the density times `C t^α`. -/
theorem integral_density_mul_smallDenominatorMass_le (law : FiniteReportLaw Report)
    (den : Report → ℝ) (hnonneg : ∀ report, 0 ≤ den report)
    (hone : ∀ report, den report ≤ 1) (density : ℝ → ℝ)
    (hcont : ContinuousOn density (Ioc 0 1)) (hdensity : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ density t)
    (scale α : ℝ) (bound : ℝ → ℝ) (hbound : IntervalIntegrable bound volume 0 1)
    (hdominates : ∀ t ∈ Ioo (0 : ℝ) 1, density t * (scale * t ^ α) ≤ bound t)
    (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α) :
    ∫ t in (0 : ℝ)..1, density t * smallDenominatorMass law den t ≤
      ∫ t in (0 : ℝ)..1, bound t := by
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (intervalIntegrable_density_mul_smallDenominatorMass law den hnonneg hone density hcont)
    hbound fun t ht ↦ ?_
  exact (mul_le_mul_of_nonneg_left (hrate t ht.1 ht.2.le)
    (hdensity t ⟨ht.1, ht.2.le⟩)).trans (hdominates t ht)

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
  have hbound : IntervalIntegrable
      (fun t : ℝ ↦ scale * ((K : ℝ) * (1 - t) ^ (K - 1) * t ^ α)) volume 0 1 :=
    ((intervalIntegral.intervalIntegrable_rpow' hα).continuousOn_mul
      (by fun_prop)).const_mul scale
  have hdensity : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (K : ℝ) * (1 - t) ^ (K - 1) := fun t ht ↦
    mul_nonneg (Nat.cast_nonneg K) (pow_nonneg (by linarith [ht.2]) (K - 1))
  have hle : ∫ t in (0 : ℝ)..1, (K : ℝ) * (1 - t) ^ (K - 1) * smallDenominatorMass law den t ≤
      ∫ t in (0 : ℝ)..1, scale * ((K : ℝ) * (1 - t) ^ (K - 1) * t ^ α) :=
    integral_density_mul_smallDenominatorMass_le law den hnonneg hone
      (fun t ↦ (K : ℝ) * (1 - t) ^ (K - 1)) (by fun_prop) hdensity scale α _ hbound
      (fun t _ ↦ le_of_eq (by ring)) hrate
  rw [unresolvedMass_eq_integral law den hnonneg hone K hK,
    ← integral_truncationDensity_mul_rpow α hα K hK, ← intervalIntegral.integral_const_mul]
  exact hle

/-- **NOTE 2 equation (28).** If `P(0 < D ≤ t) ≤ C t^α` for `0 < t ≤ 1` with `α > 1`, the
expected inverse denominator on the defined event is at most `P(D > 0) + C / (α - 1)`. -/
theorem expectation_inverse_le (law : FiniteReportLaw Report) (den : Report → ℝ)
    (hnonneg : ∀ report, 0 ≤ den report) (hone : ∀ report, den report ≤ 1) (scale α : ℝ)
    (hα : 1 < α) (hrate : ∀ t, 0 < t → t ≤ 1 → smallDenominatorMass law den t ≤ scale * t ^ α) :
    law.expectation (ratioOnDefined (fun _ ↦ 1) den) ≤
      law.expectation (definedIndicator (fun report ↦ 0 < den report)) + scale / (α - 1) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioc 0 1) :=
    (continuous_pow 2).continuousOn.inv₀ fun t ht ↦ pow_ne_zero 2 ht.1.ne'
  have hlayer : law.expectation (fun report ↦ if 0 < den report then (den report)⁻¹ - 1 else 0) =
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
  have hbound : IntervalIntegrable (fun t : ℝ ↦ scale * t ^ (α - 2)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul scale
  have hdominates : ∀ t ∈ Ioo (0 : ℝ) 1, (t ^ 2)⁻¹ * (scale * t ^ α) ≤ scale * t ^ (α - 2) := by
    intro t ht
    refine le_of_eq ?_
    rw [Real.rpow_sub ht.1 α 2, Real.rpow_two]
    ring
  have hle : ∫ t in (0 : ℝ)..1, (t ^ 2)⁻¹ * smallDenominatorMass law den t ≤
      ∫ t in (0 : ℝ)..1, scale * t ^ (α - 2) :=
    integral_density_mul_smallDenominatorMass_le law den hnonneg hone _ hcont
      (fun t _ ↦ inv_nonneg.mpr (sq_nonneg t)) scale α _ hbound hdominates hrate
  have hvalue : ∫ t in (0 : ℝ)..1, scale * t ^ (α - 2) = scale / (α - 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (r := α - 2) (Or.inl (by linarith)),
      Real.one_rpow, Real.zero_rpow (by linarith : (0 : ℝ) < α - 2 + 1).ne']
    ring
  rw [hsplit, hlayer]
  linarith [hle, hvalue]

/-- **NOTE 2 equation (29).** Let `0 ≤ N ≤ M`, `0 ≤ D ≤ 1`, `P(0 < D ≤ t) ≤ C t^α` for
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
  have hceilingStep : unresolvedNumerator law num den K ≤ ceilingValue *
      law.expectation (fun report ↦
        if 0 < den report then (1 - den report) ^ K / den report else 0) := by
    unfold unresolvedNumerator FiniteReportLaw.expectation
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun report _ ↦ ?_
    by_cases hpos : 0 < den report
    · simp only [ratioOnDefined, if_pos hpos]
      have hdecay : 0 ≤ (1 - den report) ^ K := pow_nonneg (by linarith [hone report]) K
      have hstep : num report * (1 - den report) ^ K ≤ ceilingValue * (1 - den report) ^ K :=
        mul_le_mul_of_nonneg_right (hceiling report) hdecay
      have hratio : num report / den report * (1 - den report) ^ K ≤
          ceilingValue * ((1 - den report) ^ K / den report) := by
        calc num report / den report * (1 - den report) ^ K
            = num report * (1 - den report) ^ K / den report := by ring
          _ ≤ ceilingValue * (1 - den report) ^ K / den report :=
            div_le_div_of_nonneg_right hstep hpos.le
          _ = ceilingValue * ((1 - den report) ^ K / den report) := by ring
      calc law.mass report * (num report / den report * (1 - den report) ^ K)
          ≤ law.mass report * (ceilingValue * ((1 - den report) ^ K / den report)) :=
            mul_le_mul_of_nonneg_left hratio (law.mass_nonneg report)
        _ = ceilingValue * (law.mass report * ((1 - den report) ^ K / den report)) := by ring
    · simp only [ratioOnDefined, if_neg hpos]
      simp
  have hcont : ContinuousOn
      (fun t : ℝ ↦ ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2) (Ioc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ ↦
      (K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K).continuousOn.div
      (continuous_pow 2).continuousOn fun t ht ↦ pow_ne_zero 2 ht.1.ne'
  have hlayer : law.expectation (fun report ↦
      if 0 < den report then (1 - den report) ^ K / den report else 0) =
      ∫ t in (0 : ℝ)..1, ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 *
        smallDenominatorMass law den t :=
    expectation_profile_eq_integral law den hnonneg hone _ (fun D ↦ (1 - D) ^ K / D) hcont
      fun D hD1 ↦ remainder_layerCake D hD1 K hK
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
  have hbound : IntervalIntegrable (fun t : ℝ ↦ scale *
      ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K)) volume 0 1 :=
    ((hfirst.const_mul (K : ℝ)).add hsecond).const_mul scale
  have hdominates : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 * (scale * t ^ α) ≤
        scale * ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    refine le_of_eq ?_
    rw [Real.rpow_sub ht.1 α 1, Real.rpow_sub ht.1 α 2, Real.rpow_one, Real.rpow_two]
    field_simp
    ring
  have hle : ∫ t in (0 : ℝ)..1, ((K : ℝ) * (1 - t) ^ (K - 1) * t + (1 - t) ^ K) / t ^ 2 *
      smallDenominatorMass law den t ≤ ∫ t in (0 : ℝ)..1, scale *
        ((K : ℝ) * (t ^ (α - 1) * (1 - t) ^ (K - 1)) + t ^ (α - 2) * (1 - t) ^ K) :=
    integral_density_mul_smallDenominatorMass_le law den hnonneg hone _ hcont hdensity scale α _
      hbound hdominates hrate
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

end

end Descent.Portability.SmallDenominatorLayerCake
