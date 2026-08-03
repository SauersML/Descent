import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Calibrator

/-!
# Nonreversible demography mixes faster and transports no better

This module is **self-contained: it imports only Mathlib.**

`Calibrator.DirichletTransfer` derives its construction rule — among schemes with equal source
performance, the one with the smallest Dirichlet energy degrades slowest — under a **reversible**
coupling, and reads the sharp floor as an integrated autocorrelation time. Human demography is
not reversible: directional migration, admixture pulses, sex-biased gene flow and serial founder
expansion all carry probability around a cycle rather than back and forth. This module asks what
of the calculus survives, and the answer is unusually clean: **the frontier survives untouched,
the interpretation does not.**

## The two halves

Write the generator as a symmetric part `S` and an antisymmetric part `A`. Then:

* **The Dirichlet form does not see `A` at all.** `driftGeneratorForm_independent_of_circulation`
  is that statement in the two-dimensional model: the quadratic form of an antisymmetric operator
  vanishes identically, so the energy that governs degradation is the energy of `S`. Every
  energy comparison built only from this two-dimensional quadratic form is therefore
  unchanged when `a` changes.  Extending that observation to a general nonnormal generator
  requires an operator theorem and is not asserted here.

* **The autocorrelation time does see `A`, and shrinks.** The asymptotic variance of a
  time-average is governed by the symmetric part of the *resolvent*, `s/(s² + a²)`, not by the
  inverse of the symmetric part, `1/s`. The two differ by an exact nonnegative amount:

  `1/s  =  s/(s² + a²)  +  a²/(s(s² + a²))`,

  which is `circulationDefect_identity`. The defect is strictly positive whenever there is any
  circulation at all.

## What that means for a study

Circulation **accelerates ergodic averaging** — a nonreversible demography decorrelates its own
environmental signals faster, and any mixing-time diagnostic estimated from data will report a
shorter time — while contributing **nothing** to the transfer frontier, which harvests only
dissipation. So a mixing time read off the data and substituted into the horizon calculus
*systematically overstates transportability*, and the overstatement is not a modelling
imprecision but an exactly computable factor:

`transferTimeInflation s a = 1 + (a/s)²`,

the ratio of the frontier time to the apparent mixing time. At equal symmetric and antisymmetric
strength the transfer-relevant time is twice what the mixing diagnostic reports; the bias grows
quadratically in the circulation-to-dissipation ratio and is unbounded.

This is the mechanism by which a population that looks well mixed can still be a bad transfer
target, and it is worth separating from the two mechanisms the corpus already carries. It is not
allele-frequency divergence and it is not linkage-disequilibrium mismatch: those describe how far
apart two populations are. This describes a demography in which the *rate at which the
environment forgets* and the *rate at which a design degrades* are different numbers, with the gap
set by how much of the flow is cyclic. Any protocol that estimates one and uses the other inherits
the defect.

## Scope, stated exactly

Proved here: the vanishing of the antisymmetric quadratic form, the exact defect identity, its
strict positivity under nonzero circulation, and the inflation factor — all in the
two-dimensional model with isotropic symmetric part, where the algebra is closed-form. Not
asserted here: the general operator identity
`⟨g, S⁻¹g⟩ = ⟨g, Re(-L)⁻¹g⟩ + ‖S^{-1/2}A(S+A)^{-1}g‖²`, of which the display above is the
two-dimensional instance, nor any claim that a particular human demography has a particular
circulation ratio.

Empirical status: DERIVED. The identity is proved; the circulation-to-dissipation ratio of a real
demography is an unmeasured input, and naming it is the empirical work this result asks for.
-/

/-! ## Circulation is invisible to the Dirichlet form -/

/-- Quadratic form of the antisymmetric part `[[0, a], [-a, 0]]` at the vector `(x, y)`. -/
def circulationQuadraticForm (a x y : ℝ) : ℝ := x * (a * y) + y * (-(a * x))

/-- **The circulation carries no energy.** The quadratic form of an antisymmetric operator
vanishes identically — not on average, and not to first order. -/
theorem circulationQuadraticForm_eq_zero (a x y : ℝ) :
    circulationQuadraticForm a x y = 0 := by
  unfold circulationQuadraticForm; ring

/-- Dirichlet form of a generator with isotropic dissipation `s` and circulation `a`. -/
def driftGeneratorForm (s a x y : ℝ) : ℝ :=
  s * (x ^ 2 + y ^ 2) + circulationQuadraticForm a x y

/-- The Dirichlet form is the dissipative form. -/
theorem driftGeneratorForm_eq_dissipative (s a x y : ℝ) :
    driftGeneratorForm s a x y = s * (x ^ 2 + y ^ 2) := by
  unfold driftGeneratorForm
  rw [circulationQuadraticForm_eq_zero]
  ring

/-- **Therefore the degradation calculus is blind to nonreversibility.** Two demographies with
the same dissipation and different circulation have the same Dirichlet energy at every design,
so every ordering derived from that energy is unchanged. -/
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

/-- **The circulation defect identity.** The frontier time is the measured mixing time plus a
nonnegative defect carried entirely by the circulation. -/
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

/-- **A mixing diagnostic understates the transfer time whenever the demography circulates.** -/
theorem apparentMixingTime_lt_frontierTime (s a : ℝ) (hs : 0 < s) (ha : a ≠ 0) :
    apparentMixingTime s a < frontierTime s := by
  have hid := circulationDefect_identity s a hs
  have hpos := circulationDefect_pos s a hs ha
  linarith

/-- The factor by which a mixing-time diagnostic understates the transfer-relevant time. -/
noncomputable def transferTimeInflation (s a : ℝ) : ℝ := 1 + (a / s) ^ 2

/-- **The bias is exactly the inflation factor**, quadratic in the circulation-to-dissipation
ratio and unbounded. At equal strengths the transfer time is twice the measured mixing time. -/
theorem frontierTime_eq_inflation_mul_apparent (s a : ℝ) (hs : 0 < s) :
    frontierTime s = transferTimeInflation s a * apparentMixingTime s a := by
  have h1 : s ≠ 0 := ne_of_gt hs
  have h2 : (0 : ℝ) < s ^ 2 + a ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg a)
  unfold frontierTime transferTimeInflation apparentMixingTime
  field_simp [h1, ne_of_gt h2]

/-- The inflation factor is at least one, with equality exactly at reversibility. -/
theorem transferTimeInflation_ge_one (s a : ℝ) : 1 ≤ transferTimeInflation s a := by
  unfold transferTimeInflation
  nlinarith [sq_nonneg (a / s)]

end Calibrator
