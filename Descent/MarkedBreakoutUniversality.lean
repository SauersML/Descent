/-
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Descent.MultipleMergerBlindness

namespace Descent

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
open Filter
open scoped BigOperators ENNReal

/-! ## The marked measure and its genealogy projection -/

/-- A successful family is marked by eventual population fraction and front displacement. -/
abbrev SuccessfulFamilyMark := ℝ × ℝ

/-- Eventual fraction of the population descended from a successful family. -/
def familyFraction : SuccessfulFamilyMark → ℝ := Prod.fst

/-- Displacement of the front caused by a successful family. -/
def frontDisplacement : SuccessfulFamilyMark → ℝ := Prod.snd

@[measurability, fun_prop]
theorem measurable_familyFraction : Measurable familyFraction := measurable_fst

@[measurability, fun_prop]
theorem measurable_frontDisplacement : Measurable frontDisplacement := measurable_snd

/-- The unconditioned genealogy measure induced by a marked successful-family intensity.

This is the literal measure-theoretic formula `Λ₀(dx) = x² ν(dx, ℝ)`: weight the marked measure
by `x²`, then push it forward along the family-fraction coordinate. -/
noncomputable def genealogyMeasure (ν : Measure SuccessfulFamilyMark) : Measure ℝ :=
  Measure.map familyFraction
    (ν.withDensity fun mark ↦ ENNReal.ofReal (familyFraction mark ^ 2))

/-- The finite-second-moment hypothesis on the marked successful-family intensity.  It is exactly
the condition ensuring that the induced genealogy measure has finite total mass. -/
def HasFiniteGenealogicalIntensity (ν : Measure SuccessfulFamilyMark) : Prop :=
  (∫⁻ mark, ENNReal.ofReal (familyFraction mark ^ 2) ∂ν) < ∞

/-- The zero successful-family intensity is a concrete finite-rate instance. -/
theorem hasFiniteGenealogicalIntensity_zero :
    HasFiniteGenealogicalIntensity (0 : Measure SuccessfulFamilyMark) := by
  simp [HasFiniteGenealogicalIntensity]

/-- Evaluation of `Λ₀` on a measurable family-fraction set. -/
theorem genealogyMeasure_apply (ν : Measure SuccessfulFamilyMark) {s : Set ℝ}
    (hs : MeasurableSet s) :
    genealogyMeasure ν s =
      ∫⁻ mark in familyFraction ⁻¹' s,
        ENNReal.ofReal (familyFraction mark ^ 2) ∂ν := by
  rw [genealogyMeasure, Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ (measurable_familyFraction hs)]

/-- The weighted fraction marginal is finite under the marked measure's second-moment bound. -/
theorem genealogyMeasure_finite_of_secondMoment
    {ν : Measure SuccessfulFamilyMark} (hν : HasFiniteGenealogicalIntensity ν) :
    genealogyMeasure ν Set.univ < ∞ := by
  rw [genealogyMeasure_apply ν MeasurableSet.univ]
  simpa [HasFiniteGenealogicalIntensity] using hν

/-- Exponential weight applied to a marked breakout by a canonical front-speed tilt. -/
noncomputable def speedTiltWeight (theta : ℝ) (mark : SuccessfulFamilyMark) : ℝ :=
  Real.exp (-(theta * frontDisplacement mark))

/-- The complete conditioned genealogy formula
`Λθ(dx) = x² ∫ exp(-θr) ν(dx,dr)` as an actual measure. -/
noncomputable def speedTiltedGenealogyMeasure
    (theta : ℝ) (ν : Measure SuccessfulFamilyMark) : Measure ℝ :=
  Measure.map familyFraction
    (ν.withDensity fun mark ↦
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
    withDensity_apply _ (measurable_familyFraction hs)]
  rfl

/-- Zero speed tilt is exactly the unconditioned genealogy, not merely a proportional measure. -/
@[simp] theorem speedTiltedGenealogyMeasure_zero (ν : Measure SuccessfulFamilyMark) :
    speedTiltedGenealogyMeasure 0 ν = genealogyMeasure ν := by
  simp [speedTiltedGenealogyMeasure, genealogyMeasure, speedTiltWeight]

/-- Speed tilts form an exact additive semigroup on every successful-family mark. -/
theorem speedTiltWeight_add (theta eta : ℝ) (mark : SuccessfulFamilyMark) :
    speedTiltWeight (theta + eta) mark =
      speedTiltWeight theta mark * speedTiltWeight eta mark := by
  rw [speedTiltWeight, speedTiltWeight, speedTiltWeight, ← Real.exp_add]
  congr 1
  ring

/-- Every speed-tilt weight is strictly positive. -/
theorem speedTiltWeight_pos (theta : ℝ) (mark : SuccessfulFamilyMark) :
    0 < speedTiltWeight theta mark := by
  exact Real.exp_pos _

/-- Positive speed bias strictly suppresses larger front displacements. -/
theorem speedTiltWeight_strictAnti_displacement
    (theta x r₁ r₂ : ℝ) (htheta : 0 < theta) (hr : r₁ < r₂) :
    speedTiltWeight theta (x, r₂) < speedTiltWeight theta (x, r₁) := by
  unfold speedTiltWeight frontDisplacement
  exact Real.exp_lt_exp.mpr (by nlinarith)

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

/-- Larger successful families cause strictly larger logarithmic front displacements whenever
the front scale is positive.  This is the order-theoretic mechanism behind speed conditioning:
the canonical tilt does not merely change a normalization, it penalizes the large-family tail. -/
theorem logDisplacement_strictMono
    {gamma x y : ℝ} (hgamma : 0 < gamma) (hxy : x < y) (hy : y < 1) :
    logDisplacement gamma x < logDisplacement gamma y := by
  have hypos : 0 < 1 - y := by linarith
  have hxpos : 0 < 1 - x := by linarith
  have hlog : Real.log (1 - y) < Real.log (1 - x) :=
    Real.strictMonoOn_log hypos hxpos (by linarith)
  unfold logDisplacement
  have hcoefficient : -(1 / gamma) < 0 := neg_lt_zero.mpr (one_div_pos.mpr hgamma)
  exact mul_lt_mul_of_neg_left hlog hcoefficient

/-- A positive canonical speed penalty strictly suppresses larger successful-family fractions
under the logarithmic response law. -/
theorem logDisplacement_speedTilt_strictAnti
    {gamma theta x y : ℝ} (hgamma : 0 < gamma) (htheta : 0 < theta)
    (hxy : x < y) (hy : y < 1) :
    Real.exp (-(theta * logDisplacement gamma y)) <
      Real.exp (-(theta * logDisplacement gamma x)) := by
  apply Real.exp_lt_exp.mpr
  have hdisplacement : logDisplacement gamma x < logDisplacement gamma y :=
    logDisplacement_strictMono hgamma hxy hy
  nlinarith

/-- **The tilt factorizes exactly.**  Under the logarithmic displacement law the exponential
tilt `exp(-θ r(x))` is the power `(1-x)^(θ/γ)`. -/
theorem logDisplacement_laplace_factors (gamma theta x : ℝ) (hg : gamma ≠ 0) (hx : x < 1) :
    Real.exp (-(theta * logDisplacement gamma x)) = (1 - x) ^ (theta / gamma) := by
  have hpos : 0 < 1 - x := by linarith
  rw [Real.rpow_def_of_pos hpos]
  unfold logDisplacement
  congr 1
  field_simp

/-- **The logarithmic displacement response is forced.** At any nonzero tilt, a deterministic
response produces the Beta power `(1-x)^(θ/γ)` only if it is exactly
`-γ⁻¹ log(1-x)`. Thus within deterministic response models, the Beta interpolation is not just
generated by the logarithmic law: it characterizes that law pointwise. -/
theorem response_eq_logDisplacement_of_laplace_factor
    (gamma theta x response : ℝ) (hgamma : gamma ≠ 0) (htheta : theta ≠ 0)
    (hx : x < 1)
    (hfactor : Real.exp (-(theta * response)) = (1 - x) ^ (theta / gamma)) :
    response = logDisplacement gamma x := by
  have hpos : 0 < 1 - x := by linarith
  rw [Real.rpow_def_of_pos hpos] at hfactor
  have hexponent := Real.exp_injective hfactor
  unfold logDisplacement
  field_simp [hgamma, htheta] at hexponent ⊢
  nlinarith

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

/-- Centering a conditional displacement transform by the logarithmic response leaves the same
Laplace transform at every family fraction. -/
def HasFractionIndependentCenteredTransform
    (gamma : ℝ) (conditionalLaplace : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y theta, x < 1 → y < 1 →
    conditionalLaplace x theta / (1 - x) ^ (theta / gamma) =
      conditionalLaplace y theta / (1 - y) ^ (theta / gamma)

/-- **Necessary and sufficient Beta criterion at transform level.**  The normalized speed tilt
has the Beta power factor exactly when subtracting the logarithmic response leaves an
`x`-independent conditional Laplace transform.  Under uniqueness of conditional Laplace
transforms this is equivalent to a single additive-noise law independent of `x`. -/
theorem hasBetaTiltInvariant_iff_centeredTransformIndependent
    (gamma : ℝ) (conditionalLaplace : ℝ → ℝ → ℝ) :
    HasBetaTiltInvariant gamma conditionalLaplace ↔
      HasFractionIndependentCenteredTransform gamma conditionalLaplace := by
  constructor
  · intro h x y theta hx hy
    rw [h x theta hx, h y theta hy]
    have hxpow : (1 - x) ^ (theta / gamma) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    have hypow : (1 - y) ^ (theta / gamma) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    simp [hxpow, hypow]
  · intro h x theta hx
    have hcentered := h x 0 theta hx (by norm_num)
    have hxpow : (1 - x) ^ (theta / gamma) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    simpa [hxpow] using (div_eq_iff hxpow).mp hcentered

/-! ## A displacement law with the same unconditioned genealogy and a different tilt -/

/-- Normalized three-lineage merger rate for the same unconditioned uniform `Λ₀`, but with
linear response `r(x)=x`.  This is
`∫₀¹ x exp(-θx) dx / ∫₀¹ exp(-θx) dx` in closed form. -/
noncomputable def linearDisplacementTripleRate (theta : ℝ) : ℝ :=
  (1 - (1 + theta) * Real.exp (-theta)) / (theta * (1 - Real.exp (-theta)))

/-- Under logarithmic response, the normalized three-lineage rate depends only on the
dimensionless speed-bias ratio `theta / gamma`. -/
@[simp] theorem logDisplacementTripleRate (gamma theta : ℝ) :
    speedTiltBetaMergerRate (theta / gamma) 3 3 =
      1 / (theta / gamma + 2) := by
  simp

/-- **The first non-pairwise genealogy coordinate recovers the speed-bias ratio exactly.**
Pairwise rates are normalized to one and see no regime; taking the reciprocal of the
three-lineage rate and subtracting two returns `theta / gamma`. -/
theorem tiltRatio_eq_tripleRate_inv_sub_two (gamma theta : ℝ) :
    theta / gamma = (speedTiltBetaMergerRate (theta / gamma) 3 3)⁻¹ - 2 := by
  rw [logDisplacementTripleRate]
  simp

/-- If the front response scale is known and nonzero, the three-lineage genealogy coordinate
recovers the canonical speed-bias parameter itself. -/
theorem speedBias_eq_gamma_mul_tripleRate_transform
    (gamma theta : ℝ) (hgamma : gamma ≠ 0) :
    theta = gamma * ((speedTiltBetaMergerRate (theta / gamma) 3 3)⁻¹ - 2) := by
  rw [← tiltRatio_eq_tripleRate_inv_sub_two]
  field_simp

/-- **Kingman endpoint for logarithmic front response.** At every positive response scale,
increasing canonical speed bias suppresses every specified merger of three or more lineages. -/
theorem tendsto_logDisplacement_mergerRate_three_or_more_atTop
    (gamma : ℝ) (hgamma : 0 < gamma) (b extra : ℕ) :
    Tendsto
      (fun theta : ℝ ↦ speedTiltBetaMergerRate (theta / gamma) b (extra + 3))
      atTop (nhds 0) := by
  have hratio : Tendsto (fun theta : ℝ ↦ theta / gamma) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hgamma).2 tendsto_id
  exact (tendsto_speedTiltBetaMergerRate_three_or_more_atTop b extra).comp hratio

/-- At the same endpoint, every specified binary-merger rate converges to the Kingman
normalization one. -/
theorem tendsto_logDisplacement_binaryMergerRate_atTop
    (gamma : ℝ) (hgamma : 0 < gamma) (extra : ℕ) :
    Tendsto
      (fun theta : ℝ ↦ speedTiltBetaMergerRate (theta / gamma) (extra + 2) 2)
      atTop (nhds 1) := by
  have hratio : Tendsto (fun theta : ℝ ↦ theta / gamma) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hgamma).2 tendsto_id
  exact (tendsto_speedTiltBetaMergerRate_two_with_outside_atTop extra).comp hratio

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

/-- **The side condition of the pioneer substitution.**  Every identity in `w = x / (1 - x)`
clears its denominators against this one nonvanishing, so it is named here rather than
re-derived at each use -- including in `XiFromMarkedBreakouts`, which imports this file. -/
theorem pioneer_one_sub_ne_zero {x : ℝ} (hx1 : x ≠ 1) : (1 : ℝ) - x ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm hx1)

/-- **The pioneer substitution produces the inverse-square intensity exactly.**

The overshoot intensity `A exp(-γδ)dδ` becomes
`(AB/(γ width^p)) x⁻² dx`: the exponential tail contributes
`B/(width^p x/(1-x))` and the Jacobian contributes `1/(γx(1-x))`. -/
theorem pioneerIntensity_eq_inverseSquare
    (A B gamma width x : ℝ) (p : ℕ)
    (hg : gamma ≠ 0) (hw : width ^ p ≠ 0) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (A * (B / (width ^ p * (x / (1 - x))))) * (1 / (gamma * (x * (1 - x)))) =
      (A * B / (gamma * width ^ p)) * (1 / x ^ 2) := by
  have h1 := pioneer_one_sub_ne_zero hx1
  field_simp

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

/-! ## Reference evaluations and junk-value boundaries

Every definition in this file is pinned at a reference point, and every point where Mathlib's
totalisation of a partial operation supplies a junk value is named. -/

/-- A mark's fraction coordinate is its first component. -/
@[simp] theorem familyFraction_mk (x r : ℝ) : familyFraction (x, r) = x := rfl

/-- A mark's displacement coordinate is its second component. -/
@[simp] theorem frontDisplacement_mk (x r : ℝ) : frontDisplacement (x, r) = r := rfl

/-- At zero tilt every mark carries unit weight: no conditioning, no reweighting. -/
@[simp] theorem speedTiltWeight_zero (mark : SuccessfulFamilyMark) :
    speedTiltWeight 0 mark = 1 := by
  simp [speedTiltWeight]

/-- A family that reaches unit displacement at unit tilt is downweighted by exactly `e⁻¹`. -/
theorem speedTiltWeight_at_unit_mark (x : ℝ) :
    speedTiltWeight 1 (x, 1) = (Real.exp 1)⁻¹ := by
  simp [speedTiltWeight, Real.exp_neg]

/-- A family that reaches no one displaces the front by nothing. -/
@[simp] theorem logDisplacement_at_zero_fraction (gamma : ℝ) :
    logDisplacement gamma 0 = 0 := by
  simp [logDisplacement]

/-- Reference value: at unit rate constant, a family reaching half the population displaces the
front by `log 2`. -/
theorem logDisplacement_at_half : logDisplacement 1 (1 / 2) = Real.log 2 := by
  unfold logDisplacement
  rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- `Real.log (1 - x)` at `x = 1` is Mathlib's junk `0`, so `logDisplacement` reports no
displacement for a family that takes the whole population.  The true displacement diverges
there; the biological range is `x < 1`, which every theorem above assumes. -/
theorem logDisplacement_at_full_fraction_is_junk (gamma : ℝ) :
    logDisplacement gamma 1 = 0 := by
  simp [logDisplacement]

/-- `1 / gamma` at `gamma = 0` is Mathlib's junk `0`, so a zero rate constant reports no
displacement.  A zero rate constant has no front, so the case is outside the model rather than
a value to be trusted; `logDisplacement_laplace_factors` excludes it. -/
theorem logDisplacement_at_zero_rate_is_junk (x : ℝ) : logDisplacement 0 x = 0 := by
  simp [logDisplacement]

/-- The linear-displacement triple rate at `theta = 0` divides by zero.  Mathlib returns `0`,
whereas the limit is `1 / 2` -- the Bolthausen--Sznitman value, since zero tilt is no
conditioning.  This is a junk value that disagrees with the limit, so the definition must not
be read at `theta = 0`; `tripleRate_separates_at_unit_tilt` evaluates at `theta = 1`. -/
theorem linearDisplacementTripleRate_at_zero_is_junk :
    linearDisplacementTripleRate 0 = 0 := by
  simp [linearDisplacementTripleRate]

/-- A pioneer with no advantage reaches no one. -/
@[simp] theorem pioneerFraction_zero_advantage (width : ℝ) (p : ℕ) :
    pioneerFraction 0 width p = 0 := by
  simp [pioneerFraction]

/-- Reference value: an advantage equal to the susceptibility scale reaches exactly half. -/
theorem pioneerFraction_at_unit_ratio (width : ℝ) (p : ℕ) (hw : width ^ p ≠ 0) :
    pioneerFraction (width ^ p) width p = 1 / 2 := by
  unfold pioneerFraction
  rw [div_self hw]
  norm_num

/-- `advantage / width ^ p` at `width = 0` with positive `p` is Mathlib's junk `0`, so a
zero-width front reports that no pioneer reaches anyone.  The relaxation map is undefined
there; every theorem above carries `width ^ p ne 0`. -/
theorem pioneerFraction_at_zero_width_is_junk (advantage : ℝ) (p : ℕ) (hp : p ≠ 0) :
    pioneerFraction advantage 0 p = 0 := by
  unfold pioneerFraction
  rw [zero_pow hp]
  simp

/-- The timescale at unit front width is one, whatever the susceptibility exponent. -/
@[simp] theorem genealogicalTimescale_one (p : ℕ) : genealogicalTimescale 1 p = 1 := by
  simp [genealogicalTimescale]

/-- Reference value: front width two with the cubic susceptibility exponent gives clock `8`. -/
theorem genealogicalTimescale_at_two : genealogicalTimescale 2 3 = 8 := by
  norm_num [genealogicalTimescale]


end MarkedBreakout

end Descent
