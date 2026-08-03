import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators

/-!
# The portability decay curve: what it is not, what it is, and why its crossing is not a
# half-life

This module is **self-contained: it imports only Mathlib.**

`Calibrator.DirichletTransfer` builds a horizon calculus on top of a decay curve and reads a
crossover `τ_c = log 2 / λ` off it. That calculus is correct, but it inherits two things from
its source that were never checked here, and one of them is a measurement bug that would show
up in any attempt to estimate the curve from cohort data.

## The measurement bug: the naive curve is identically flat

The object one is tempted to average is "efficiency of the design, evaluated on the population
as it stands `τ` later":

`R(τ) = E_{x ~ π} E_{y ~ P_τ(x, ·)} [ efficiency(y) ]`.

Under stationarity this is **constant in `τ`**, and not approximately: exactly, at every
horizon, for every kernel that preserves `π`. `naiveHorizonCurve_flat` is the one-line proof —
sum swap plus the stationarity identity `Σ_x π(x) P(x,y) = π(y)` — and
`naiveHorizonCurve_independent_of_horizon` states the consequence in the form that matters:
two different horizons give the same number.

This is not a pedantic point. It says that **any decay a study reports from this estimator is
an artefact** — of non-stationarity in the sampling, of the design being refit, or of the
evaluation set not being drawn from the invariant law. A reported decay curve that was in fact
computed this way is measuring its own sampling scheme. The corpus already has a register for
results of this shape; this is the horizon entry.

## The three objects that are actually different

Once the flat one is removed, three genuinely distinct functionals remain, and the horizon
calculus needs the second and third, never the first:

* the **static mean** `Σ_y π(y) f(y)` — the flat quantity above, a property of the one-point
  law alone;
* the **profile autocorrelation** `⟨f, P_τ f⟩_π` — how the efficiency profile itself decorrelates,
  which is what a spectral decay law describes;
* the **regret** `E_x E_{y ~ P_τ(x,·)} [ ρ(x, y) ]` — choose the design optimally *at* `x`,
  evaluate it *at* `y`. This is the operationally motivating object, and it is the only one of
  the three whose integrand depends on both endpoints.

`regret_moves_while_naive_curve_is_flat` separates them on two states: two kernels, both
stationary for the same uniform law, whose naive curves are therefore equal, and whose regrets
are `1` and `0`. The whole informational content of the horizon lives in the dependence of the
integrand on the *starting* point, which the naive average integrates away.

## The shape law: a measured decay rate can only fall

For a decay curve that is a positive mixture of exponentials — which is what a reversible
coupling produces — the **effective decay rate** `-d/dτ log M(τ)` is nonincreasing in `τ`.
`effectiveRate_nonincreasing` proves the two-mode case in cleared multiplicative form, so
nothing is divided by and no derivative is taken.

That is a falsifiable shape constraint on any measured portability decay curve: **a curve whose
apparent decay rate increases with horizon is not a relaxation curve of a stationary reversible
coupling**, whatever else it is. It is the correct form of "mass migrates to the low-lying
modes"; the stronger stochastic-ordering statement is not asserted here and is expected to be
false, because the admissible design cone owes the spectral order nothing.

## The crossing is not a half-life

`DirichletTransfer.stalenessCrossover` gives `τ_c = log 2 / λ` and its surrounding prose says
the premium "crosses zero at a unique `τ_c`". At a **single** relaxation rate that is right, and
`twoMode_premium_strictAnti` extends the uniqueness to any positive two-mode mixture: the
premium is strictly decreasing, so it crosses at most once.

**Beyond that it is false.** `horizonPolynomial` is an exact four-mode premium — in the variable
`u = e^{-τ}`, which runs from `1` at zero horizon down to `0` at infinite horizon —

`S = 8u⁴ - 12u³ + (148/25)u² - (24/25)u = 8u(u - 2/5)(u - 1/2)(u - 3/5)`,

with in-sample edge `S = 24/25` at `u = 1`. `horizon_three_crossings` exhibits its three sign
changes. Read along increasing horizon, a design built on stale information **beats** the
environment-blind design, then loses to it, then beats it again, and finally loses for good.

The endpoint signs are laws — positive at zero horizon by construction, negative at infinite
horizon because the design is then evaluated against an independent draw — so a crossing always
exists. The interior sign is model geometry. Consequently **a single measured crossover does not
identify a relaxation time**: inverting `τ_c = log 2 / λ` on data that came from a multi-mode
value signal returns a number with no referent. Uniqueness needs one sign change in the
coefficient sequence ordered by rate, and that is a hypothesis about the value signal, not a
property of the coupling.

Empirical status: the flatness identity, the two-state separation, the shape law and the
three-crossing witness are all PROVED here as stated. That a real cohort decay curve is a
positive exponential mixture is an ASSERTED input, and it is exactly what the shape law makes
testable.
-/

/-! ## The naive horizon curve, and why it does not move -/

section Flatness

variable {ι : Type*} [Fintype ι]

/-- A kernel `P` preserves the law `π`: `Σ_x π(x) P(x,y) = π(y)` for every `y`. -/
def IsStationaryKernel (π : ι → ℝ) (P : ι → ι → ℝ) : Prop :=
  ∀ y, ∑ x, π x * P x y = π y

/-- **The naive horizon curve is the static mean.**

    Averaging a one-endpoint efficiency profile over the invariant law and then over one step
    of a law-preserving kernel returns the plain invariant average. No property of `P` beyond
    stationarity is used, and no approximation is made. -/
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

/-- **Therefore the naive curve carries no horizon information at all.**

    Two horizons of one stationary family give the same number, so a decay reported from this
    estimator is a property of the sampling and not of the coupling. -/
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

/-- Efficiency of the design chosen optimally at `x` when it is evaluated at `y`: full at the
state it was built for, none at the other. This is the two-endpoint integrand that the naive
average cannot see. -/
def agreement (i j : Fin 2) : ℝ := if i = j then 1 else 0

/-- **Regret**: choose the design optimally at `x`, evaluate it at `y`. -/
noncomputable def regretCurve (π : Fin 2 → ℝ) (P ρ : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ x, π x * ∑ y, P x y * ρ x y

theorem uniformTwo_stationary_stay : IsStationaryKernel uniformTwo stayKernel := by
  intro y
  fin_cases y <;> norm_num [uniformTwo, stayKernel, Fin.sum_univ_two]

theorem uniformTwo_stationary_swap : IsStationaryKernel uniformTwo swapKernel := by
  intro y
  fin_cases y <;> norm_num [uniformTwo, swapKernel, Fin.sum_univ_two]

/-- **The separation.** Both kernels preserve the uniform law, so by `naiveHorizonCurve_flat`
    their naive curves agree for every one-endpoint profile. Their regrets are `1` and `0`.

    Everything the horizon calculus is about survives only in the dependence of the integrand
    on the starting point. -/
theorem regret_moves_while_naive_curve_is_flat :
    regretCurve uniformTwo stayKernel agreement = 1 ∧
      regretCurve uniformTwo swapKernel agreement = 0 := by
  constructor <;>
    norm_num [regretCurve, uniformTwo, stayKernel, swapKernel, agreement, Fin.sum_univ_two]

/-! ## The shape law: an effective decay rate cannot rise -/

/-- Algebraic core of the shape law, with the exponentials abstracted.  For nonnegative
weights and ordered rates, the cross-multiplied effective-rate comparison holds whenever the
exponential factors satisfy `a·d ≤ c·b`. -/
theorem crossRate_aux (p q l1 l2 a b c d : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hl : l1 ≤ l2) (h : a * d ≤ c * b) :
    (p * l1 * c + q * l2 * d) * (p * a + q * b)
      ≤ (p * l1 * a + q * l2 * b) * (p * c + q * d) := by
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hp hq) (sub_nonneg.mpr hl))
    (sub_nonneg.mpr h)]

/-- **The measured decay rate is nonincreasing in the horizon.**

    For the two-mode curve `M(τ) = p e^{-λ₁τ} + q e^{-λ₂τ}` the effective rate
    `-M'(τ)/M(τ)` falls as the horizon grows. Stated in cleared multiplicative form — the
    numerator at the later horizon against the denominator at the earlier one — so that
    nothing is divided by and no differentiability hypothesis is needed.

    A measured curve whose apparent rate rises with horizon is therefore not the relaxation
    curve of a stationary reversible coupling. -/
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

/-! ## Uniqueness of the crossing holds at two modes and fails at four -/

/-- **At two positive modes the premium is strictly decreasing**, hence crosses zero at most
    once and the crossover is a well-defined horizon.  This is the hypothesis under which
    `DirichletTransfer.stalenessCrossover` may be inverted for a relaxation time. -/
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

/-- A four-mode stale premium, written in `u = e^{-τ}`.  The horizon runs from `u = 1` at zero
separation down to `u = 0` at infinite separation. -/
noncomputable def horizonPolynomial (u : ℝ) : ℝ :=
  8 * u ^ 4 - 12 * u ^ 3 + (148 / 25) * u ^ 2 - (24 / 25) * u

/-- The premium factors with three interior roots. -/
theorem horizonPolynomial_factored (u : ℝ) :
    horizonPolynomial u = 8 * u * (u - 2 / 5) * (u - 1 / 2) * (u - 3 / 5) := by
  unfold horizonPolynomial; ring

/-- The in-sample edge is positive: at zero horizon the stale design beats the blind one. -/
theorem horizonPolynomial_inSample : horizonPolynomial 1 = 24 / 25 := by
  unfold horizonPolynomial; norm_num

/-- **The crossover is not unique.**

    Three sign changes, exhibited by evaluation. Read along increasing horizon (decreasing
    `u`), the stale design beats the blind one, loses to it, beats it again, and finally loses.
    A single measured crossover therefore does not identify a relaxation time. -/
theorem horizon_three_crossings :
    horizonPolynomial (2 / 5) = 0 ∧ horizonPolynomial (1 / 2) = 0 ∧
      horizonPolynomial (3 / 5) = 0 ∧ horizonPolynomial (3 / 10) < 0 ∧
      0 < horizonPolynomial (9 / 20) ∧ horizonPolynomial (11 / 20) < 0 ∧
      0 < horizonPolynomial (4 / 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · unfold horizonPolynomial; norm_num

end Calibrator
