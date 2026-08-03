/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Calibrator

/-!
# Nonreversible gene flow: the mixing time is not the transfer time

Self-contained: imports only Mathlib.

`Calibrator.DirichletTransfer` derives its construction rule — among schemes with equal source
performance, the one with the smallest Dirichlet energy degrades slowest — under a reversible
coupling, and reads the sharp floor as an integrated autocorrelation time. Gene flow is not
reversible: directional migration, admixture pulses, sex-biased flow and serial founder expansion
carry probability around cycles. Splitting the generator into a symmetric part `S` and an
antisymmetric part `A` separates what changes from what does not.

The Dirichlet form does not see `A`. The quadratic form of an antisymmetric operator vanishes
identically (`driftGeneratorForm_independent_of_circulation`), so the energy governing degradation
is the energy of `S`, and the construction rule holds verbatim for nonreversible couplings with
`S` in place of `-L`.

The autocorrelation time does see `A`. The asymptotic variance of a time-average is governed by
the symmetric part of the resolvent, `s/(s² + a²)`, not by the inverse of the symmetric part,
`1/s`, and the two differ by an exact nonnegative amount:

`1/s = s/(s² + a²) + a²/(s(s² + a²))`     (`circulationDefect_identity`).

So circulation accelerates ergodic averaging without contributing to the frontier: a mixing-time
diagnostic reports a shorter time than the one governing transfer, by the factor
`transferTimeInflation s a = 1 + (a/s)²` — two at equal strengths, growing quadratically in the
circulation-to-dissipation ratio, unbounded.

That is a third mechanism alongside the two the corpus already carries. Allele-frequency
divergence says how far apart two populations are; tagging mismatch says how much linkage
structure carries over; this says the rate at which the environment forgets and the rate at which
a design degrades are different numbers, with the gap set by how much of the flow is cyclic.

Scope: everything here is the two-dimensional model with isotropic symmetric part, where the
algebra is closed-form. The general operator identity
`⟨g, S⁻¹g⟩ = ⟨g, Re(-L)⁻¹g⟩ + ‖S^{-1/2}A(S+A)^{-1}g‖²`, of which the display is the
two-dimensional instance, is not asserted, and neither is any circulation ratio for a particular
demography.

Empirical status: DERIVED. The identity is proved; the circulation-to-dissipation ratio of a real
demography is an unmeasured input.
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

/-- Two demographies with the same dissipation and different circulation have the same Dirichlet
energy at every design, so every ordering derived from that energy is unchanged. -/
theorem driftGeneratorForm_independent_of_circulation (s a a' x y : ℝ) :
    driftGeneratorForm s a x y = driftGeneratorForm s a' x y := by
  rw [driftGeneratorForm_eq_dissipative, driftGeneratorForm_eq_dissipative]

/-! ## The autocorrelation time is not blind to it -/

/-- The time constant that sets the transfer frontier: the inverse dissipation. -/
noncomputable def frontierTime (s : ℝ) : ℝ := 1 / s

/-- The integrated autocorrelation time an ergodic-averaging diagnostic actually measures: the
symmetric part of the resolvent of `S + A`. -/
noncomputable def apparentMixingTime (s a : ℝ) : ℝ := s / (s ^ 2 + a ^ 2)

/-- The exact gap between the two. -/
noncomputable def circulationDefect (s a : ℝ) : ℝ := a ^ 2 / (s * (s ^ 2 + a ^ 2))

/-- The gap between the two times, in cleared form. -/
theorem circulationDefect_eq_sub (s a : ℝ) (hs : 0 < s) :
    frontierTime s - apparentMixingTime s a = circulationDefect s a := by
  have h1 : s ≠ 0 := ne_of_gt hs
  have h2 : s ^ 2 + a ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg a))
  unfold frontierTime apparentMixingTime circulationDefect
  field_simp [h1, h2]
  ring

/-- The frontier time is the measured mixing time plus a nonnegative defect carried entirely by
the circulation. -/
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

/-- A mixing diagnostic understates the transfer time whenever the demography circulates. -/
theorem apparentMixingTime_lt_frontierTime (s a : ℝ) (hs : 0 < s) (ha : a ≠ 0) :
    apparentMixingTime s a < frontierTime s := by
  have hid := circulationDefect_identity s a hs
  have hpos := circulationDefect_pos s a hs ha
  linarith

/-- The factor by which a mixing-time diagnostic understates the transfer-relevant time. -/
noncomputable def transferTimeInflation (s a : ℝ) : ℝ := 1 + (a / s) ^ 2

/-- The bias is the inflation factor: quadratic in the circulation-to-dissipation ratio, and
twice the measured mixing time at equal strengths. -/
theorem frontierTime_eq_inflation_mul_apparent (s a : ℝ) (hs : 0 < s) :
    frontierTime s = transferTimeInflation s a * apparentMixingTime s a := by
  have h1 : s ≠ 0 := ne_of_gt hs
  have h2 : (0 : ℝ) < s ^ 2 + a ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg a)
  unfold frontierTime transferTimeInflation apparentMixingTime
  field_simp [h1, ne_of_gt h2]

/-- The inflation factor is at least one. The dissipation must be positive: at `s = 0` Lean's
`a / 0 = 0` makes the factor exactly one for every circulation, so without the hypothesis the
bound holds for the wrong reason at the one point where it matters most. -/
theorem transferTimeInflation_ge_one (s a : ℝ) (hs : 0 < s) :
    1 ≤ transferTimeInflation s a := by
  unfold transferTimeInflation
  nlinarith [sq_nonneg (a / s)]

/-- **Equality holds exactly at reversibility**, which is the half the inequality alone does not
carry. Stated as a theorem rather than asserted in prose beside `transferTimeInflation_ge_one`,
because at `s = 0` the junk quotient gives equality at maximal circulation and the prose reading
would be false there. -/
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

end Calibrator
