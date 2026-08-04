/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Calibrator.MultipleMergerBlindness

namespace Calibrator

/-!
# Marked successful families are the branching-front universality object

The broad Brunet--Derrida universality claim cannot be expressed by one universal coalescent
measure or one universal clock.  The exact model-independent reduction starts one level higher.
A successful reproductive event has two marks: its eventual population fraction `x` and the
front displacement `r` it causes.  Its limiting intensity is a measure `ν` on `(x,r)`.

This file formalizes the consequences that follow *after* such a marked-event limit is known:

* `genealogyMeasure ν` is the weighted fraction marginal `Λ₀(dx) = x² ν(dx, ℝ)`;
* a speed tilt produces `speedTiltedGenealogyMeasure θ ν`, with weight `x² exp(-θr)`;
* the successful-family participation probability is exactly the corresponding
  `Λ`-coalescent integrand;
* the Beta interpolation follows from, and requires at transform level, a logarithmic response
  in the surviving population fraction;
* two displacement responses with the same unconditioned genealogy have different tilted
  three-lineage rates;
* the pioneer change of variables produces both the inverse-square family intensity and the
  front-width timescale.

No theorem below asserts the missing model-specific point-process convergence for an `N`-BRW or
`N`-BBM.  In particular, the file does not promote the still-open light-tailed hard-selection
genealogy limit to an axiom.  It formalizes exactly what that convergence would imply.
-/

namespace MarkedBreakout

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## The marked measure and its genealogy projection -/

/-- A successful family is marked by eventual population fraction and front displacement. -/
abbrev SuccessfulFamilyMark := ℝ × ℝ

/-- Eventual fraction of the population descended from a successful family. -/
def familyFraction (mark : SuccessfulFamilyMark) : ℝ := mark.1

/-- Displacement of the front caused by a successful family. -/
def frontDisplacement (mark : SuccessfulFamilyMark) : ℝ := mark.2

/-- The unconditioned genealogy measure induced by a marked successful-family intensity.

This is the literal measure-theoretic formula `Λ₀(dx) = x² ν(dx, ℝ)`: weight the marked measure
by `x²`, then push it forward along the family-fraction coordinate. -/
noncomputable def genealogyMeasure (ν : Measure SuccessfulFamilyMark) : Measure ℝ :=
  Measure.map familyFraction
    (ν.withDensity fun mark => ENNReal.ofReal (familyFraction mark ^ 2))

/-- Evaluation of `Λ₀` on a measurable family-fraction set. -/
theorem genealogyMeasure_apply (ν : Measure SuccessfulFamilyMark) {s : Set ℝ}
    (hs : MeasurableSet s) :
    genealogyMeasure ν s =
      ∫⁻ mark in familyFraction ⁻¹' s,
        ENNReal.ofReal (familyFraction mark ^ 2) ∂ν := by
  rw [genealogyMeasure, Measure.map_apply (by fun_prop) hs,
    Measure.withDensity_apply _ ((by fun_prop : Measurable familyFraction).measurableSet_preimage hs)]

/-- Exponential weight applied to a marked breakout by a canonical front-speed tilt. -/
noncomputable def speedTiltWeight (theta : ℝ) (mark : SuccessfulFamilyMark) : ℝ :=
  Real.exp (-(theta * frontDisplacement mark))

/-- The complete conditioned genealogy formula
`Λθ(dx) = x² ∫ exp(-θr) ν(dx,dr)` as an actual measure. -/
noncomputable def speedTiltedGenealogyMeasure
    (theta : ℝ) (ν : Measure SuccessfulFamilyMark) : Measure ℝ :=
  Measure.map familyFraction
    (ν.withDensity fun mark =>
      ENNReal.ofReal (familyFraction mark ^ 2 * speedTiltWeight theta mark))

/-- Evaluation of the speed-tilted genealogy measure on a measurable fraction set. -/
theorem speedTiltedGenealogyMeasure_apply
    (theta : ℝ) (ν : Measure SuccessfulFamilyMark) {s : Set ℝ}
    (hs : MeasurableSet s) :
    speedTiltedGenealogyMeasure theta ν s =
      ∫⁻ mark in familyFraction ⁻¹' s,
        ENNReal.ofReal
          (familyFraction mark ^ 2 * Real.exp (-(theta * frontDisplacement mark))) ∂ν := by
  rw [speedTiltedGenealogyMeasure, Measure.map_apply (by fun_prop) hs,
    Measure.withDensity_apply _ ((by fun_prop : Measurable familyFraction).measurableSet_preimage hs)]
  rfl

/-- Zero speed tilt is exactly the unconditioned genealogy, not merely a proportional measure. -/
@[simp] theorem speedTiltedGenealogyMeasure_zero (ν : Measure SuccessfulFamilyMark) :
    speedTiltedGenealogyMeasure 0 ν = genealogyMeasure ν := by
  simp [speedTiltedGenealogyMeasure, genealogyMeasure, speedTiltWeight]

/-! ## Why the unconditioned genealogy sees only the weighted `x`-marginal -/

/-- **The whole content of the reduction `Λ₀(dx) = x² ν(dx, ℝ)`.**  The probability that a
specified `k`-tuple of `b` blocks is caught by a family of size `x` factors as `x²` times the
`Λ`-coalescent integrand. -/
theorem markedParticipation_factors (x : ℝ) (b k : ℕ) (hk : 2 ≤ k) :
    x ^ k * (1 - x) ^ (b - k) = x ^ 2 * (x ^ (k - 2) * (1 - x) ^ (b - k)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [← mul_assoc, ← pow_add]
  congr 2
  omega

/-- Rate functional obtained directly from Bernoulli participation in marked events.  It is
`ℝ≥0∞`-valued so the definition remains meaningful before imposing the finite-second-moment
assumption used for a finite-rate coalescent. -/
noncomputable def markedEventMergerRate
    (ν : Measure SuccessfulFamilyMark) (b k : ℕ) : ℝ≥0∞ :=
  ∫⁻ mark, ENNReal.ofReal
    (familyFraction mark ^ k * (1 - familyFraction mark) ^ (b - k)) ∂ν

/-- The same rate written in `Λ`-coalescent form with the `x²` genealogical weight exposed. -/
noncomputable def markedLambdaMergerRate
    (ν : Measure SuccessfulFamilyMark) (b k : ℕ) : ℝ≥0∞ :=
  ∫⁻ mark, ENNReal.ofReal
    (familyFraction mark ^ 2 *
      (familyFraction mark ^ (k - 2) * (1 - familyFraction mark) ^ (b - k))) ∂ν

/-- **Genealogy from the marked measure.**  For every biological merger size `2 ≤ k`, the
successful-event rate is exactly the merger rate generated by the weighted marginal `Λ₀`.
This is the rate-level conclusion of the rare-breakout assumptions; the particle-system
point-process convergence needed to instantiate `ν` is deliberately separate. -/
theorem markedEventMergerRate_eq_lambda
    (ν : Measure SuccessfulFamilyMark) (b k : ℕ) (hk : 2 ≤ k) :
    markedEventMergerRate ν b k = markedLambdaMergerRate ν b k := by
  apply lintegral_congr
  intro mark
  rw [markedParticipation_factors (familyFraction mark) b k hk]

/-- A deterministic time change cannot repair loss of the response mark: proportional marked
genealogy measures have the same normalized merger law, but arbitrary equality of their
unconditioned projections says nothing about their tilted projections. -/
theorem same_marked_projection_gives_same_unconditioned_genealogy
    {ν₁ ν₂ : Measure SuccessfulFamilyMark}
    (hprojection : genealogyMeasure ν₁ = genealogyMeasure ν₂) :
    speedTiltedGenealogyMeasure 0 ν₁ = speedTiltedGenealogyMeasure 0 ν₂ := by
  simpa using hprojection

/-! ## The exact invariant behind the Beta interpolation -/

/-- Front displacement caused by a family that reaches fraction `x`, in the form that produces
the Beta family: logarithmic in the surviving fraction, with rate constant `γ`. -/
noncomputable def logDisplacement (gamma x : ℝ) : ℝ :=
  -(1 / gamma) * Real.log (1 - x)

/-- **The tilt factorizes exactly.**  Under the logarithmic displacement law the exponential
tilt `exp(-θ r(x))` is the power `(1-x)^(θ/γ)`. -/
theorem logDisplacement_laplace_factors (gamma theta x : ℝ) (hg : gamma ≠ 0) (hx : x < 1) :
    Real.exp (-(theta * logDisplacement gamma x)) = (1 - x) ^ (theta / gamma) := by
  have hpos : 0 < 1 - x := by linarith
  rw [Real.rpow_def_of_pos hpos]
  unfold logDisplacement
  congr 1
  field_simp
  ring

/-- Additive displacement noise independent of the family fraction contributes an `x`-independent
factor, so pair-rate normalization removes it. -/
theorem displacementNoise_factors (gamma theta x noise : ℝ)
    (hg : gamma ≠ 0) (hx : x < 1) :
    Real.exp (-(theta * (logDisplacement gamma x + noise))) =
      (1 - x) ^ (theta / gamma) * Real.exp (-(theta * noise)) := by
  rw [← logDisplacement_laplace_factors gamma theta x hg hx, ← Real.exp_add]
  congr 1
  ring

/-- Conditional Laplace transforms have the Beta invariant when centering by the logarithmic
response leaves a transform independent of the family fraction.  If Laplace transforms determine
the conditional laws, this is precisely the distributional representation
`R | X=x = -γ⁻¹ log(1-x) + Z` with the law of `Z` independent of `x`. -/
def HasBetaTiltInvariant (gamma : ℝ) (conditionalLaplace : ℝ → ℝ → ℝ) : Prop :=
  ∀ x theta, x < 1 →
    conditionalLaplace x theta =
      conditionalLaplace 0 theta * (1 - x) ^ (theta / gamma)

/-- The invariant gives the normalized Beta density factor and shows exactly which information
normalization discards: only the transform at the reference fraction, independent of `x`. -/
theorem betaTiltInvariant_factorization
    {gamma : ℝ} {conditionalLaplace : ℝ → ℝ → ℝ}
    (h : HasBetaTiltInvariant gamma conditionalLaplace)
    (x theta : ℝ) (hx : x < 1) :
    conditionalLaplace x theta =
      conditionalLaplace 0 theta * (1 - x) ^ (theta / gamma) :=
  h x theta hx

/-! ## A displacement law with the same unconditioned genealogy and a different tilt -/

/-- Normalized three-lineage merger rate for the same unconditioned uniform `Λ₀`, but with
linear response `r(x)=x`.  This is
`∫₀¹ x exp(-θx) dx / ∫₀¹ exp(-θx) dx` in closed form. -/
noncomputable def linearDisplacementTripleRate (theta : ℝ) : ℝ :=
  (1 - (1 + theta) * Real.exp (-theta)) / (theta * (1 - Real.exp (-theta)))

/-- The logarithmic law's unit-tilt three-lineage coordinate. -/
theorem logDisplacementTripleRate_at_unit_tilt :
    speedTiltBetaMergerRate 1 3 3 = 1 / 3 := by
  norm_num

/-- The linear law's unit-tilt three-lineage coordinate in closed form. -/
theorem linearDisplacementTripleRate_at_unit_tilt :
    linearDisplacementTripleRate 1 = (Real.exp 1 - 2) / (Real.exp 1 - 1) := by
  have he : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
  have hne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  unfold linearDisplacementTripleRate
  rw [he]
  field_simp
  ring

/-- A short Taylor lower bound sufficient to separate the two exact rate formulas. -/
theorem five_halves_lt_exp_one : (5 / 2 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- **Nonuniversality of the speed-conditioned family.**  Two marked mechanisms with identical
unconditioned uniform genealogy have different normalized conditioned three-lineage rates at
`θ=1`, so deterministic rescaling of time cannot identify the two conditioned laws. -/
theorem tripleRate_separates_at_unit_tilt :
    linearDisplacementTripleRate 1 ≠ speedTiltBetaMergerRate 1 3 3 := by
  rw [linearDisplacementTripleRate_at_unit_tilt, logDisplacementTripleRate_at_unit_tilt]
  have h1 : Real.exp 1 - 1 ≠ 0 := by
    nlinarith [five_halves_lt_exp_one]
  intro heq
  rw [div_eq_div_iff h1 (by norm_num : (3 : ℝ) ≠ 0)] at heq
  nlinarith [five_halves_lt_exp_one]

/-! ## Where the timescale exponent comes from -/

/-- Population fraction eventually reached by a pioneer of `advantage = B exp(γδ)`, after
relaxation against a front of width `width` with susceptibility exponent `p`. -/
noncomputable def pioneerFraction (advantage width : ℝ) (p : ℕ) : ℝ :=
  (advantage / width ^ p) / (1 + advantage / width ^ p)

/-- Inverting the relaxation map: the advantage needed to reach fraction `x` is
`width^p x/(1-x)`. -/
theorem pioneerFraction_inverse (x width : ℝ) (p : ℕ) (hw : 0 < width ^ p)
    (hx0 : 0 < x) (hx1 : x < 1) :
    pioneerFraction (width ^ p * (x / (1 - x))) width p = x := by
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  have hwne : width ^ p ≠ 0 := ne_of_gt hw
  unfold pioneerFraction
  field_simp
  ring

/-- **The pioneer substitution produces the inverse-square intensity exactly.**

The overshoot intensity `A exp(-γδ)dδ` becomes
`(AB/(γ width^p)) x⁻² dx`: the exponential tail contributes
`B/(width^p x/(1-x))` and the Jacobian contributes `1/(γx(1-x))`. -/
theorem pioneerIntensity_eq_inverseSquare
    (A B gamma width x : ℝ) (p : ℕ)
    (hg : gamma ≠ 0) (hw : width ^ p ≠ 0) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (A * (B / (width ^ p * (x / (1 - x))))) * (1 / (gamma * (x * (1 - x)))) =
      (A * B / (gamma * width ^ p)) * (1 / x ^ 2) := by
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  field_simp
  ring

/-- Genealogical timescale produced by the pioneer substitution. -/
noncomputable def genealogicalTimescale (width : ℝ) (p : ℕ) : ℝ := width ^ p

/-- Width powers compose exactly, locating the clock exponent entirely in front susceptibility. -/
theorem genealogicalTimescale_add (width : ℝ) (p q : ℕ) :
    genealogicalTimescale width (p + q) =
      genealogicalTimescale width p * genealogicalTimescale width q := by
  simp [genealogicalTimescale, pow_add]

/-- With susceptibility exponent three, the pioneer clock is the front-width cube. -/
@[simp] theorem genealogicalTimescale_three (width : ℝ) :
    genealogicalTimescale width 3 = width ^ 3 := rfl

end MarkedBreakout

end Calibrator
