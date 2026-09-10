/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision
assert_below Descent.Program

namespace Descent.Spectral

/-!
# Instantaneous energy and integrated correlation in an isotropic mode

This file proves scalar algebra for the two-dimensional generator
`L = -s I + A`, where `A = [[0,a],[-a,0]]`. The antisymmetric quadratic form
vanishes, so its instantaneous Dirichlet energy is `s * (x^2 + y^2)`.
This does not determine the finite-horizon error of a fixed observable.

For `s > 0`, the normalized stationary mode has correlation
`exp(-s*t) * cos(a*t)`. Its one-sided integrated correlation is
`s / (s^2 + a^2)`. The inverse dissipation is `1 / s`, and the exact gap is
`a^2 / (s * (s^2 + a^2))`.

The historical names `apparentMixingTime`, `frontierTime`, and
`transferTimeInflation` below denote this integrated correlation, inverse
dissipation, and their ratio. They do not establish a total-variation mixing
time or a universal portability frontier. Instantaneous energy, finite-time
stale-observable loss, optimal transported prediction risk, and integrated
correlation are separate endpoints. Circulation can affect them differently.

The formal content here is the displayed quadratic and rational identities.
It neither estimates a circulation ratio for a real demography nor proves the
general operator resolvent identity outside this isotropic two-dimensional
special case. The zero-denominator lemmas record Lean's totalized algebra;
positive damping is required for the stated stationary timescale interpretation.
-/

/-! ## Circulation is invisible to the Dirichlet form -/

/-- Quadratic form of the antisymmetric part `[[0, a], [-a, 0]]` at the vector `(x, y)`. -/
def circulationQuadraticForm (a x y : ℝ) : ℝ := x * (a * y) + y * (-(a * x))

/-- The quadratic form of an antisymmetric operator vanishes identically. -/
theorem circulationQuadraticForm_eq_zero (a x y : ℝ) :
    circulationQuadraticForm a x y = 0 := by
  unfold circulationQuadraticForm; ring

/-- Dirichlet form of a generator with isotropic dissipation `s` and circulation `a`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- `drift` here is the drift term
    of a diffusion generator, not genetic drift. The body is a quadratic form. -/
def driftGeneratorForm (s a x y : ℝ) : ℝ :=
  s * (x ^ 2 + y ^ 2) + circulationQuadraticForm a x y

/-- The Dirichlet form is the dissipative form. -/
theorem driftGeneratorForm_eq_dissipative (s a x y : ℝ) :
    driftGeneratorForm s a x y = s * (x ^ 2 + y ^ 2) := by
  unfold driftGeneratorForm
  rw [circulationQuadraticForm_eq_zero]
  ring

/-- Isotropic modes with equal damping have the same instantaneous Dirichlet
quadratic form for every circulation value. This equality does not extend by
itself to finite-horizon stale-observable loss. -/
theorem driftGeneratorForm_independent_of_circulation (s a a' x y : ℝ) :
    driftGeneratorForm s a x y = driftGeneratorForm s a' x y := by
  rw [driftGeneratorForm_eq_dissipative, driftGeneratorForm_eq_dissipative]

/-! ## The autocorrelation time is not blind to it -/

/-- Inverse dissipation of the isotropic mode. The historical name does not
assert that this scalar is the frontier for an unspecified prediction task. -/
noncomputable def frontierTime (s : ℝ) : ℝ := 1 / s

/-- Lean's totalized inverse at zero is zero. The positive-damping timescale
interpretation requires `s > 0`; the one-sided limit as `s` decreases to zero
is divergent and is not represented by this value. -/
theorem frontierTime_zero_s_is_junk :
    frontierTime 0 = 0 := by
  unfold frontierTime
  simp

/-- One-sided integrated correlation of the normalized isotropic mode,
equivalently the symmetric resolvent coefficient. This is not a general
mixing-time or semigroup-relaxation definition. -/
noncomputable def apparentMixingTime (s a : ℝ) : ℝ := s / (s ^ 2 + a ^ 2)

/-- The rational formula has zero denominator at `(s,a)=(0,0)`.
Lean returns zero there; this value has no stationary timescale interpretation. -/
theorem apparentMixingTime_at_s0a0_is_junk :
    apparentMixingTime 0 0 = 0 := by
  unfold apparentMixingTime
  norm_num

/-- The exact gap between the two. -/
noncomputable def circulationDefect (s a : ℝ) : ℝ := a ^ 2 / (s * (s ^ 2 + a ^ 2))

/-- Lean returns zero when the displayed rational gap has zero damping in
its denominator. This totalized value does not describe the positive-damping
limit and is excluded from the timescale interpretation. -/
theorem circulationDefect_zero_s_is_junk (a : ℝ) :
    circulationDefect 0 a = 0 := by
  unfold circulationDefect
  simp

/-- The gap between the two times, in cleared form. -/
theorem circulationDefect_eq_sub (s a : ℝ) (hs : 0 < s) :
    frontierTime s - apparentMixingTime s a = circulationDefect s a := by
  have h1 : s ≠ 0 := ne_of_gt hs
  have h2 : s ^ 2 + a ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg a))
  unfold frontierTime apparentMixingTime circulationDefect
  field_simp [h1, h2]
  ring

/-- Inverse dissipation equals one-sided integrated correlation plus the
nonnegative rational gap for this isotropic mode. -/
theorem circulationDefect_identity (s a : ℝ) (hs : 0 < s) :
    frontierTime s = apparentMixingTime s a + circulationDefect s a := by
  have h := circulationDefect_eq_sub s a hs
  linarith

/-- The defect is nonnegative always, and strictly positive as soon as there is circulation. -/
theorem circulationDefect_pos (s a : ℝ) (hs : 0 < s) (ha : a ≠ 0) :
    0 < circulationDefect s a := by
  have h2 : (0 : ℝ) < s ^ 2 + a ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg a)
  have ha2 : (0 : ℝ) < a ^ 2 :=
    lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
  unfold circulationDefect
  exact div_pos ha2 (mul_pos hs h2)

/-- Nonzero circulation makes integrated correlation strictly smaller than
inverse dissipation in the isotropic mode. -/
theorem apparentMixingTime_lt_frontierTime (s a : ℝ) (hs : 0 < s) (ha : a ≠ 0) :
    apparentMixingTime s a < frontierTime s := by
  have hid := circulationDefect_identity s a hs
  have hpos := circulationDefect_pos s a hs ha
  linarith

/-- At unit damping and circulation, the one-sided integrated correlation
is exactly one half, distinguishing the intended squared-sum denominator
from alternative rational formulas. -/
theorem apparentMixingTime_at_equal_parts :
    apparentMixingTime 1 1 = 1 / 2 := by
  unfold apparentMixingTime
  norm_num

/-- Ratio of inverse dissipation to one-sided integrated correlation when
`s > 0`. The historical name does not assign this ratio to arbitrary risks. -/
noncomputable def transferTimeInflation (s a : ℝ) : ℝ := 1 + (a / s) ^ 2

/-- At zero damping Lean returns one for the totalized ratio formula.
This is not the ratio of finite stationary timescales, which requires `s > 0`. -/
theorem transferTimeInflation_zero_symmetric_is_junk (a : ℝ) :
    transferTimeInflation 0 a = 1 := by
  unfold transferTimeInflation
  simp

/-- The exact scalar ratio is quadratic in circulation divided by damping;
at equal nonzero strengths, inverse dissipation is twice integrated correlation. -/
theorem frontierTime_eq_inflation_mul_apparent (s a : ℝ) (hs : 0 < s) :
    frontierTime s = transferTimeInflation s a * apparentMixingTime s a := by
  have h1 : s ≠ 0 := ne_of_gt hs
  have h2 : (0 : ℝ) < s ^ 2 + a ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg a)
  unfold frontierTime transferTimeInflation apparentMixingTime
  field_simp [h1, ne_of_gt h2]

/-- The algebraic ratio formula is at least one. At zero damping this uses
Lean's totalized quotient; the stationary interpretation requires `s > 0`. -/
theorem transferTimeInflation_ge_one (s a : ℝ) :
    1 ≤ transferTimeInflation s a := by
  unfold transferTimeInflation
  nlinarith [sq_nonneg (a / s)]

/-- With positive damping, the scalar ratio equals one exactly when the
antisymmetric component vanishes. The damping guard excludes the totalized
zero-denominator equality. -/
theorem transferTimeInflation_eq_one_iff (s a : ℝ) (hs : 0 < s) :
    transferTimeInflation s a = 1 ↔ a = 0 := by
  unfold transferTimeInflation
  constructor
  · intro h
    have hsq : (a / s) ^ 2 = 0 := by linarith
    have hdiv : a / s = 0 := by
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    rcases div_eq_zero_iff.mp hdiv with ha | hs0
    · exact ha
    · exact absurd hs0 (ne_of_gt hs)
  · intro h
    rw [h]
    simp

end Descent.Spectral
