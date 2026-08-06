/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.HoldingTime
import Descent.Coalescent.TransitVariance
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The clock's second moment, and the variance `TransitVariance` was assuming

`Descent.Coalescent.HoldingTime` computes the mean of K-C (1.7)'s exponential clock from its
density -- `∫ t · d e^{-dt} dt = d⁻¹`, which is `Γ(2) = 1` after rescaling -- and
`Descent.Coalescent.Rates.meanTransitTime` sums those means.  `Descent.Coalescent.TransitVariance`
then sums `d⁻²` and says in its docstring that `d⁻²` is the variance of that clock, without
proving it.  `Descent.Coalescent.SpectrumMoments` inherits the same debt through `Var(L_n)`.

One more integral against the same density settles it.  `Γ(3) = 2! = 2`, so

  `∫ t² · d e^{-dt} dt = 2/d²`,   hence   `Var = 2/d² - (d⁻¹)² = d⁻²`,

and the summands of `varTransitTime` and `varTotalBranchLength` are now computed from
K-C (1.7) rather than quoted.  What those files still ASSUME -- and say they assume -- is
that the clocks are INDEPENDENT, so that variances add.  That is K-C Theorem 1, and
`Descent.Coalescent.Program` item 4 tracks it.  The per-clock variance is no longer part of
the debt.

## Main results

- `integral_sq_mul_exp_neg`: `∫ x² e^{-x} = 2`, which is `Γ(3) = 2!`.
- `integral_sq_mul_holdDensity`: **`∫ t² · d e^{-dt} = 2/d²`**.
- `variance_holdTime`: **`Var = d⁻²`**, the summand `TransitVariance` was assuming.
- `variance_holdTime_deathRate`: at the coalescent's own rates.
-/

namespace Coalescent

open MeasureTheory Set

/-- `∫_0^∞ x² e^{-x} dx = 2`, which is `Γ(3) = 2! = 2` -- the same computation that gave
`HoldingTime.integral_id_mul_exp_neg` its `Γ(2) = 1`, one index along. -/
theorem integral_sq_mul_exp_neg : ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x) = 2 := by
  have hgamma : Real.Gamma 3 = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((3 : ℝ) - 1) :=
    Real.Gamma_eq_integral (by norm_num)
  have htwo : Real.Gamma 3 = 2 := by
    have h : Real.Gamma ((2 : ℕ) + 1) = ((Nat.factorial 2 : ℕ) : ℝ) :=
      Real.Gamma_nat_eq_factorial 2
    norm_num at h
    simpa using h
  rw [htwo] at hgamma
  rw [hgamma]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
  rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- **The second moment of Kingman's clock: `2/d²`.**  Rescaling `t ↦ dt` turns the density
into the standard exponential and pulls out `d⁻²` -- the same substitution
`HoldingTime.integral_id_mul_holdDensity` makes, with one more factor of `t`. -/
theorem integral_sq_mul_holdDensity {d : ℝ} (hd : 0 < d) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 * (d * Real.exp (-(d * t))) = 2 / d ^ 2 := by
  have hdne : d ≠ 0 := ne_of_gt hd
  have hpt : ∀ t : ℝ, t ^ 2 * (d * Real.exp (-(d * t)))
      = d⁻¹ * ((fun x : ℝ ↦ x ^ 2 * Real.exp (-x)) (d * t)) := by
    intro t
    show t ^ 2 * (d * Real.exp (-(d * t)))
      = d⁻¹ * ((d * t) ^ 2 * Real.exp (-(d * t)))
    field_simp
  have hcomp : ∫ t in Ioi (0 : ℝ), (fun x : ℝ ↦ x ^ 2 * Real.exp (-x)) (d * t)
      = d⁻¹ • ∫ x in Ioi (d * (0 : ℝ)), x ^ 2 * Real.exp (-x) :=
    integral_comp_mul_left_Ioi (fun x : ℝ ↦ x ^ 2 * Real.exp (-x)) 0 hd
  calc ∫ t in Ioi (0 : ℝ), t ^ 2 * (d * Real.exp (-(d * t)))
      = ∫ t in Ioi (0 : ℝ), d⁻¹ * ((fun x : ℝ ↦ x ^ 2 * Real.exp (-x)) (d * t)) := by
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ hpt t
    _ = d⁻¹ * ∫ t in Ioi (0 : ℝ), (fun x : ℝ ↦ x ^ 2 * Real.exp (-x)) (d * t) := by
        rw [integral_const_mul]
    _ = d⁻¹ * (d⁻¹ • ∫ x in Ioi (d * (0 : ℝ)), x ^ 2 * Real.exp (-x)) := by rw [hcomp]
    _ = 2 / d ^ 2 := by
        rw [mul_zero, integral_sq_mul_exp_neg, smul_eq_mul]
        field_simp

/-- **`Var = d⁻²`.**  Second moment minus squared mean, both computed from K-C (1.7)'s
density.  This is the summand `Descent.Coalescent.TransitVariance.varTransitTime` sums and
`Descent.Coalescent.SpectrumMoments.varTotalBranchLength` squares. -/
theorem variance_holdTime {d : ℝ} (hd : 0 < d) :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * (d * Real.exp (-(d * t))))
        - (∫ t in Ioi (0 : ℝ), t * (d * Real.exp (-(d * t)))) ^ 2
      = 1 / d ^ 2 := by
  rw [integral_sq_mul_holdDensity hd, integral_id_mul_holdDensity hd]
  have hdne : d ≠ 0 := ne_of_gt hd
  field_simp
  ring

/-- The same at the coalescent's own rates, so `varTransitTime`'s summand `1/d_k²` is now
computed rather than assumed. -/
theorem variance_holdTime_deathRate {k : ℕ} (hk : 2 ≤ k) :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * (deathRate k * Real.exp (-(deathRate k * t))))
        - (∫ t in Ioi (0 : ℝ), t * (deathRate k * Real.exp (-(deathRate k * t)))) ^ 2
      = (1 / deathRate k) ^ 2 := by
  rw [variance_holdTime (deathRate_pos hk)]
  rw [div_pow, one_pow]

end Coalescent

end Descent
