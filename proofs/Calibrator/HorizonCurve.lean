/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators

/-!
# The portability decay curve: the flat estimator, the shape law, and the crossing

Self-contained: imports only Mathlib.

`Calibrator.DirichletTransfer` builds a horizon calculus on a decay curve and reads a crossover
`τ_c = log 2 / λ` off it. Three facts about that curve are checked here.

## The naive estimator is flat

Averaging a one-endpoint efficiency profile over the invariant law and then over the coupling,

`R(τ) = E_{x ~ π} E_{y ~ P_τ(x, ·)} [ efficiency(y) ]`,

gives the same number at every `τ`. The proof is a sum swap plus `Σ_x π(x) P(x,y) = π(y)`
(`naiveHorizonCurve_flat`, `naiveHorizonCurve_independent_of_horizon`). A decay measured this
way therefore comes from the sampling, the refitting, or non-stationarity, not from the coupling.

Three functionals get conflated, and the horizon calculus needs the last two:

* static mean `Σ_y π(y) f(y)`, the flat one, a property of the one-point law;
* profile autocorrelation `⟨f, P_τ f⟩_π`, which a spectral decay law describes;
* regret `E_x E_{y ~ P_τ(x,·)} [ ρ(x, y) ]`: choose at `x`, evaluate at `y`.

`regret_moves_while_naive_curve_is_flat` separates them on two states: two kernels stationary for
the same uniform law, equal naive curves, regrets `1` and `0`. The horizon information is carried
by the integrand's dependence on the starting point, which the naive average integrates away.

## The measured decay rate cannot rise

For a positive mixture of exponentials the effective rate `-d/dτ log M(τ)` is nonincreasing in
`τ`. `effectiveRate_nonincreasing` proves the two-mode case in cleared multiplicative form, so
nothing is divided by and no derivative is taken. A curve whose apparent rate rises with horizon
is not the relaxation curve of a stationary reversible coupling. The stronger stochastic-ordering
statement — that spectral mass itself migrates downward — is not asserted here.

## The crossing need not be unique

`twoMode_premium_strictAnti` gives uniqueness for any positive two-mode mixture: the premium is
strictly decreasing, hence crosses at most once. `DirichletTransfer.stalenessCrossover`'s
uniqueness claim holds under that hypothesis and not in general. In `u = e^{-τ}`, running from
`1` at zero horizon to `0` at infinite horizon,

`S = 8u⁴ - 12u³ + (148/25)u² - (24/25)u = 8u(u - 2/5)(u - 1/2)(u - 3/5)`

has in-sample edge `24/25` and three sign changes (`horizon_three_crossings`): stale beats blind,
loses, beats, and loses again. The endpoint signs are forced — positive at zero horizon,
negative at infinite horizon where the design meets an independent draw — so a crossing always
exists; the interior signs are model geometry. Inverting `τ_c = log 2 / λ` on a multi-mode value
signal therefore returns a number with no referent. Uniqueness needs one sign change in the
coefficient sequence ordered by rate, which is a hypothesis about the value signal.

Empirical status: the flatness identity, the two-state separation, the shape law and the
three-crossing witness are PROVED as stated. That a cohort decay curve is a positive exponential
mixture is an ASSERTED input, and the shape law is what makes it testable.
-/

/-! ## The naive horizon curve -/

section Flatness

variable {ι : Type*} [Fintype ι]

/-- A kernel `P` preserves the law `π`: `Σ_x π(x) P(x,y) = π(y)` for every `y`. -/
def IsStationaryKernel (π : ι → ℝ) (P : ι → ι → ℝ) : Prop :=
  ∀ y, ∑ x, π x * P x y = π y

/-- The naive horizon curve is the static mean: averaging a one-endpoint profile over the
invariant law and then over one step of a law-preserving kernel returns the invariant average.
Stationarity is the only hypothesis, and the identity is exact. -/
theorem naiveHorizonCurve_flat (π : ι → ℝ) (P : ι → ι → ℝ) (f : ι → ℝ)
    (h : IsStationaryKernel π P) :
    ∑ x, π x * ∑ y, P x y * f y = ∑ y, π y * f y := by
  have hstep : ∀ x : ι, π x * ∑ y, P x y * f y = ∑ y, π x * (P x y * f y) := by
    intro x
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : ∀ x ∈ (Finset.univ : Finset ι), π x * (P x y * f y) = π x * P x y * f y :=
    fun x _ => by ring
  rw [Finset.sum_congr rfl hy, ← Finset.sum_mul, h y]

/-- Two horizons of one stationary family give the same number, so this estimator carries no
horizon information. -/
theorem naiveHorizonCurve_independent_of_horizon
    (π : ι → ℝ) (P : ℝ → ι → ι → ℝ) (f : ι → ℝ)
    (h : ∀ t, IsStationaryKernel π (P t)) (t₁ t₂ : ℝ) :
    ∑ x, π x * ∑ y, P t₁ x y * f y = ∑ x, π x * ∑ y, P t₂ x y * f y := by
  rw [naiveHorizonCurve_flat π (P t₁) f (h t₁), naiveHorizonCurve_flat π (P t₂) f (h t₂)]

end Flatness

/-! ## Two states that separate the naive curve from the regret -/

/-- The uniform law on two states. -/
noncomputable def uniformTwo : Fin 2 → ℝ := fun _ => 1 / 2

/-- The kernel that never moves. -/
def stayKernel (i j : Fin 2) : ℝ := if i = j then 1 else 0

/-- The kernel that always moves. -/
def swapKernel (i j : Fin 2) : ℝ := if i = j then 0 else 1

/-- Efficiency at `y` of the design chosen optimally at `x`: full at the state it was built
for, none at the other. This is the two-endpoint integrand the naive average cannot see. -/
def agreement (i j : Fin 2) : ℝ := if i = j then 1 else 0

/-- Regret: choose the design optimally at `x`, evaluate it at `y`. -/
noncomputable def regretCurve (π : Fin 2 → ℝ) (P ρ : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ x, π x * ∑ y, P x y * ρ x y

theorem uniformTwo_stationary_stay : IsStationaryKernel uniformTwo stayKernel := by
  intro y
  fin_cases y <;> norm_num [uniformTwo, stayKernel, Fin.sum_univ_two]

theorem uniformTwo_stationary_swap : IsStationaryKernel uniformTwo swapKernel := by
  intro y
  fin_cases y <;> norm_num [uniformTwo, swapKernel, Fin.sum_univ_two]

/-- Both kernels preserve the uniform law, so by `naiveHorizonCurve_flat` their naive curves
    agree for every one-endpoint profile. Their regrets are `1` and `0`. -/
theorem regret_moves_while_naive_curve_is_flat :
    regretCurve uniformTwo stayKernel agreement = 1 ∧
      regretCurve uniformTwo swapKernel agreement = 0 := by
  constructor <;>
    norm_num [regretCurve, uniformTwo, stayKernel, swapKernel, agreement, Fin.sum_univ_two]

/-! ## The shape law -/

/-- Algebraic core of the shape law with the exponentials abstracted: for nonnegative weights
and ordered rates, the cross-multiplied comparison holds whenever `a·d ≤ c·b`. -/
theorem crossRate_aux (p q l1 l2 a b c d : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hl : l1 ≤ l2) (h : a * d ≤ c * b) :
    (p * l1 * c + q * l2 * d) * (p * a + q * b)
      ≤ (p * l1 * a + q * l2 * b) * (p * c + q * d) := by
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hp hq) (sub_nonneg.mpr hl))
    (sub_nonneg.mpr h)]

/-- The measured decay rate is nonincreasing in the horizon: for `M(τ) = p e^{-λ₁τ} + q e^{-λ₂τ}`
    the effective rate `-M'(τ)/M(τ)` falls as `τ` grows. Stated in cleared multiplicative form —
    later-horizon numerator against earlier-horizon denominator — so no division or
    differentiability is needed. A curve whose apparent rate rises is not the relaxation curve
    of a stationary reversible coupling. -/
theorem effectiveRate_nonincreasing (p q lam1 lam2 τ₁ τ₂ : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hlam : lam1 ≤ lam2) (hτ : τ₁ ≤ τ₂) :
    (p * lam1 * Real.exp (-(lam1 * τ₂)) + q * lam2 * Real.exp (-(lam2 * τ₂))) *
        (p * Real.exp (-(lam1 * τ₁)) + q * Real.exp (-(lam2 * τ₁)))
      ≤ (p * lam1 * Real.exp (-(lam1 * τ₁)) + q * lam2 * Real.exp (-(lam2 * τ₁))) *
        (p * Real.exp (-(lam1 * τ₂)) + q * Real.exp (-(lam2 * τ₂))) := by
  have key : Real.exp (-(lam1 * τ₁)) * Real.exp (-(lam2 * τ₂))
      ≤ Real.exp (-(lam1 * τ₂)) * Real.exp (-(lam2 * τ₁)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr hτ)]
  exact crossRate_aux p q lam1 lam2 (Real.exp (-(lam1 * τ₁))) (Real.exp (-(lam2 * τ₁)))
    (Real.exp (-(lam1 * τ₂))) (Real.exp (-(lam2 * τ₂))) hp hq hlam key

/-! ## Uniqueness of the crossing: two modes against four -/

/-- At two positive modes the premium is strictly decreasing, so it crosses zero at most once.
    This is the hypothesis under which `DirichletTransfer.stalenessCrossover` may be inverted
    for a relaxation time. -/
theorem twoMode_premium_strictAnti (p q lam1 lam2 c τ₁ τ₂ : ℝ)
    (hp : 0 < p) (hq : 0 ≤ q) (h1 : 0 < lam1) (h2 : 0 ≤ lam2) (hτ : τ₁ < τ₂) :
    p * Real.exp (-(lam1 * τ₂)) + q * Real.exp (-(lam2 * τ₂)) - c
      < p * Real.exp (-(lam1 * τ₁)) + q * Real.exp (-(lam2 * τ₁)) - c := by
  have e1 : Real.exp (-(lam1 * τ₂)) < Real.exp (-(lam1 * τ₁)) := by
    refine Real.exp_lt_exp.mpr ?_
    nlinarith [mul_pos h1 (sub_pos.mpr hτ)]
  have e2 : Real.exp (-(lam2 * τ₂)) ≤ Real.exp (-(lam2 * τ₁)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg h2 (sub_pos.mpr hτ).le]
  have h1' : p * Real.exp (-(lam1 * τ₂)) < p * Real.exp (-(lam1 * τ₁)) :=
    mul_lt_mul_of_pos_left e1 hp
  have h2' : q * Real.exp (-(lam2 * τ₂)) ≤ q * Real.exp (-(lam2 * τ₁)) :=
    mul_le_mul_of_nonneg_left e2 hq
  linarith

/-- A four-mode stale premium in `u = e^{-τ}`, which runs from `1` at zero separation to `0` at
infinite separation. -/
noncomputable def horizonPolynomial (u : ℝ) : ℝ :=
  8 * u ^ 4 - 12 * u ^ 3 + (148 / 25) * u ^ 2 - (24 / 25) * u

/-- The premium factors with three interior roots. -/
theorem horizonPolynomial_factored (u : ℝ) :
    horizonPolynomial u = 8 * u * (u - 2 / 5) * (u - 1 / 2) * (u - 3 / 5) := by
  unfold horizonPolynomial; ring

/-- At zero horizon the stale design beats the blind one. -/
theorem horizonPolynomial_inSample : horizonPolynomial 1 = 24 / 25 := by
  unfold horizonPolynomial; norm_num

/-- Three sign changes, by evaluation. Read along increasing horizon (decreasing `u`) the stale
    design beats the blind one, loses, beats it again, and loses. A single measured crossover
    therefore does not identify a relaxation time. -/
theorem horizon_three_crossings :
    horizonPolynomial (2 / 5) = 0 ∧ horizonPolynomial (1 / 2) = 0 ∧
      horizonPolynomial (3 / 5) = 0 ∧ horizonPolynomial (3 / 10) < 0 ∧
      0 < horizonPolynomial (9 / 20) ∧ horizonPolynomial (11 / 20) < 0 ∧
      0 < horizonPolynomial (4 / 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · unfold horizonPolynomial; norm_num

end Calibrator
