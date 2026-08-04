/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

namespace Calibrator

/-!
# Which lineage summaries can see a multiple-merger regime?

A finite measure `Λ` on merger fractions determines the standard `Λ`-coalescent rate

`λ b k = ∫ x^(k-2) (1-x)^(b-k) dΛ(x)`

at which a specified `k`-tuple among `b` active lineages merges.  This file formalizes the
smallest possible identifiability calculation.  When `Λ` is normalized to a probability
measure, `λ 2 2 = 1` for every model: no normalized pair-merger-rate statistic can identify
the selection or reproduction regime.  At three lineages, however, `λ 3 3 = ∫ x dΛ`; the
first moment of the merger-fraction law is already visible.

This is an exact information boundary, not an asymptotic approximation.  The Dirac witnesses
show that two normalized merger laws can agree on every two-lineage rate while their
three-lineage rates are separated by an arbitrary change in merger fraction.  The final
section develops the complete normalized `Beta(1, β + 1)` rate chart and proves positivity,
strict monotonicity, and exact parameter recovery on its biological domain `β > -1`.

The file deliberately does not assert that a particular selected-front model converges to a
given `Λ`-coalescent.  Such convergence requires model-specific front and genealogy theorems;
the results below say exactly what becomes identifiable once a normalized `Λ` law is given.
-/

open MeasureTheory

/-- Rate at which a specified `k`-tuple among `b` active lineages merges in a
`Λ`-coalescent.  Natural-number subtraction makes the definition total; the biological range
is `2 ≤ k ≤ b`. -/
noncomputable def lambdaCoalescentMergerRate
    (Λ : Measure ℝ) (b k : ℕ) : ℝ :=
  ∫ x, x ^ (k - 2) * (1 - x) ^ (b - k) ∂Λ

/-- **Universal pairwise blindness.**  After the conventional probability normalization of
`Λ`, every multiple-merger model has the same two-lineage merger rate. -/
@[simp] theorem lambdaCoalescentMergerRate_two_two
    (Λ : Measure ℝ) [IsProbabilityMeasure Λ] :
    lambdaCoalescentMergerRate Λ 2 2 = 1 := by
  simp [lambdaCoalescentMergerRate]

/-- Therefore no statistic that sees a normalized `Λ` only through its pair-merger rate can
distinguish two merger laws. -/
theorem lambdaCoalescent_pairwise_rate_blind
    (Λ₁ Λ₂ : Measure ℝ) [IsProbabilityMeasure Λ₁] [IsProbabilityMeasure Λ₂] :
    lambdaCoalescentMergerRate Λ₁ 2 2 =
      lambdaCoalescentMergerRate Λ₂ 2 2 := by
  simp

/-- Three simultaneous lineages expose the first moment of the merger-fraction law. -/
theorem lambdaCoalescentMergerRate_three_three (Λ : Measure ℝ) :
    lambdaCoalescentMergerRate Λ 3 3 = ∫ x, x ∂Λ := by
  simp [lambdaCoalescentMergerRate]

/-- A point-mass merger law has three-lineage rate equal to its merger fraction. -/
@[simp] theorem lambdaCoalescentMergerRate_dirac_three_three (fraction : ℝ) :
    lambdaCoalescentMergerRate (Measure.dirac fraction) 3 3 = fraction := by
  rw [lambdaCoalescentMergerRate_three_three]
  simp

/-- **Exact smallest-sample separation.**  Point-mass merger laws at fractions zero and one
are indistinguishable at two lineages and maximally separated at three lineages. -/
theorem pairwise_blind_three_lineage_separates_dirac :
    lambdaCoalescentMergerRate (Measure.dirac 0) 2 2 =
        lambdaCoalescentMergerRate (Measure.dirac 1) 2 2 ∧
      lambdaCoalescentMergerRate (Measure.dirac 0) 3 3 = 0 ∧
      lambdaCoalescentMergerRate (Measure.dirac 1) 3 3 = 1 := by
  simp

/-! ## Complete normalized speed-tilt rate chart -/

/-- Full-merger moment for `extra + 2` lineages under the normalized
`Beta(1, β + 1)` merger law.  The product form is the integer identity

`(β + 1) B(extra + 1, β + 1)
  = ∏ j < extra, (j + 1) / (β + j + 2)`.

Using `extra` rather than a merger size makes the total definition free of truncated
subtraction. -/
noncomputable def speedTiltFullMergerRate (β : ℝ) (extra : ℕ) : ℝ :=
  ∏ j ∈ Finset.range extra, ((j : ℝ) + 1) / (β + (j : ℝ) + 2)

/-- Pair merger is normalized to one. -/
@[simp] theorem speedTiltFullMergerRate_zero (β : ℝ) :
    speedTiltFullMergerRate β 0 = 1 := by
  simp [speedTiltFullMergerRate]

/-- Three-lineage merger is the first nontrivial coordinate of the speed tilt. -/
@[simp] theorem speedTiltFullMergerRate_one (β : ℝ) :
    speedTiltFullMergerRate β 1 = 1 / (β + 2) := by
  simp [speedTiltFullMergerRate]

/-- Exact recurrence for every higher simultaneous full-merger rate. -/
theorem speedTiltFullMergerRate_succ (β : ℝ) (extra : ℕ) :
    speedTiltFullMergerRate β (extra + 1) =
      speedTiltFullMergerRate β extra *
        (((extra : ℝ) + 1) / (β + (extra : ℝ) + 2)) := by
  simp only [speedTiltFullMergerRate, Finset.prod_range_succ]

/-- Every normalized full-merger coordinate is positive on the probability-law domain
`Beta(1, β + 1)`, namely `β > -1`. -/
theorem speedTiltFullMergerRate_pos
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    0 < speedTiltFullMergerRate β extra := by
  unfold speedTiltFullMergerRate
  apply Finset.prod_pos
  intro j _
  apply div_pos
  · positivity
  · have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith

/-- Each additional lineage makes a full simultaneous merger strictly less likely on the
biological domain. -/
theorem speedTiltFullMergerRate_strictAnti_extra
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    speedTiltFullMergerRate β (extra + 1) < speedTiltFullMergerRate β extra := by
  rw [speedTiltFullMergerRate_succ]
  have hrate : 0 < speedTiltFullMergerRate β extra :=
    speedTiltFullMergerRate_pos hβ extra
  have hden : 0 < β + (extra : ℝ) + 2 := by
    have hextra : 0 ≤ (extra : ℝ) := Nat.cast_nonneg extra
    linarith
  have hfactor : ((extra : ℝ) + 1) / (β + (extra : ℝ) + 2) < 1 := by
    apply (div_lt_one hden).2
    linarith
  calc
    speedTiltFullMergerRate β extra *
        (((extra : ℝ) + 1) / (β + (extra : ℝ) + 2)) <
        speedTiltFullMergerRate β extra * 1 :=
      mul_lt_mul_of_pos_left hfactor hrate
    _ = speedTiltFullMergerRate β extra := mul_one _

/-- Every normalized full-merger coordinate is at most the pair-merger normalization. -/
theorem speedTiltFullMergerRate_le_one
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    speedTiltFullMergerRate β extra ≤ 1 := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      exact (speedTiltFullMergerRate_strictAnti_extra hβ extra).le.trans ih

/-- Full-merger coordinates belong to `(0, 1]`; the upper endpoint occurs only at the
normalized pair rate. -/
theorem speedTiltFullMergerRate_mem_Ioc
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    speedTiltFullMergerRate β extra ∈ Set.Ioc 0 1 :=
  ⟨speedTiltFullMergerRate_pos hβ extra, speedTiltFullMergerRate_le_one hβ extra⟩

/-- All `b`-lineage, specified-`k`-tuple rates obtained by expanding
`(1-x)^(b-k)` against the full-merger moments. -/
noncomputable def speedTiltBetaMergerRate (β : ℝ) (b k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (b - k + 1),
    (-1 : ℝ) ^ j * ((b - k).choose j : ℝ) *
      speedTiltFullMergerRate β (k - 2 + j)

/-- The complete rate chart retains the universal pairwise normalization. -/
@[simp] theorem speedTiltBetaMergerRate_two_two (β : ℝ) :
    speedTiltBetaMergerRate β 2 2 = 1 := by
  simp [speedTiltBetaMergerRate]

/-- The complete rate chart exposes `β` at three lineages. -/
@[simp] theorem speedTiltBetaMergerRate_three_three (β : ℝ) :
    speedTiltBetaMergerRate β 3 3 = 1 / (β + 2) := by
  simp [speedTiltBetaMergerRate]

/-- The first visible coordinate is a genuine probability on the biological domain. -/
theorem speedTiltBetaMergerRate_three_three_mem_Ioo
    {β : ℝ} (hβ : -1 < β) :
    speedTiltBetaMergerRate β 3 3 ∈ Set.Ioo 0 1 := by
  rw [speedTiltBetaMergerRate_three_three]
  constructor
  · exact one_div_pos.mpr (by linarith)
  · have hden : 1 < β + 2 := by linarith
    calc
      1 / (β + 2) < 1 / 1 := one_div_lt_one_div_of_lt (by norm_num) hden
      _ = 1 := by norm_num

/-- Increasing the speed-bias parameter strictly suppresses the first visible multiple-merger
coordinate. -/
theorem speedTiltBetaMergerRate_three_three_strictAnti
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ : β₁ < β₂) :
    speedTiltBetaMergerRate β₂ 3 3 < speedTiltBetaMergerRate β₁ 3 3 := by
  rw [speedTiltBetaMergerRate_three_three, speedTiltBetaMergerRate_three_three]
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- Three lineages identify the speed-bias parameter on the entire probability-law domain. -/
theorem speedTiltBetaMergerRate_three_three_injective_on
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ₂ : -1 < β₂)
    (hrate : speedTiltBetaMergerRate β₁ 3 3 = speedTiltBetaMergerRate β₂ 3 3) :
    β₁ = β₂ := by
  rw [speedTiltBetaMergerRate_three_three, speedTiltBetaMergerRate_three_three] at hrate
  have hne₁ : β₁ + 2 ≠ 0 := by linarith
  have hne₂ : β₂ + 2 ≠ 0 := by linarith
  field_simp [hne₁, hne₂] at hrate
  linarith

/-- Parameter readout from the normalized three-lineage rate. -/
noncomputable def speedBiasParameterFromTripleRate (rate : ℝ) : ℝ :=
  rate⁻¹ - 2

/-- **Exact speed-bias recovery.**  Throughout the admissible domain, the first non-pairwise
genealogical coordinate recovers the tilt parameter without approximation. -/
theorem speedBiasParameterFromTripleRate_recovers
    (β : ℝ) :
    speedBiasParameterFromTripleRate (speedTiltBetaMergerRate β 3 3) = β := by
  simp [speedBiasParameterFromTripleRate]

/-- Speed tilt after a front-displacement scale `γ`: the genealogy sees `θ / γ`. -/
noncomputable def frontSpeedBiasParameter (θ γ : ℝ) : ℝ :=
  θ / γ

/-- Observable three-lineage rate for a front tilt `θ` and displacement scale `γ`. -/
theorem frontSpeedBias_tripleMergerRate (θ γ : ℝ) :
    speedTiltBetaMergerRate (frontSpeedBiasParameter θ γ) 3 3 =
      1 / (θ / γ + 2) := by
  simp [frontSpeedBiasParameter]

/-- A nonnegative speed penalty at positive displacement scale moves the genealogy from the
Bolthausen--Sznitman coordinate `1/2` toward Kingman, never toward the star coalescent. -/
theorem frontSpeedBias_tripleMergerRate_le_half
    {θ γ : ℝ} (hθ : 0 ≤ θ) (hγ : 0 < γ) :
    speedTiltBetaMergerRate (frontSpeedBiasParameter θ γ) 3 3 ≤ 1 / 2 := by
  rw [frontSpeedBias_tripleMergerRate]
  have hratio : 0 ≤ θ / γ := div_nonneg hθ hγ.le
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- A strictly positive speed penalty strictly suppresses the three-lineage merger rate. -/
theorem frontSpeedBias_tripleMergerRate_lt_half
    {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    speedTiltBetaMergerRate (frontSpeedBiasParameter θ γ) 3 3 < 1 / 2 := by
  rw [frontSpeedBias_tripleMergerRate]
  have hratio : 0 < θ / γ := div_pos hθ hγ
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- No speed tilt gives the Bolthausen--Sznitman three-lineage coordinate `1/2`. -/
@[simp] theorem speedTiltBetaMergerRate_three_three_zero :
    speedTiltBetaMergerRate 0 3 3 = 1 / 2 := by
  norm_num

/-! ## Bolthausen--Sznitman total-rate ladder -/

/-- Telescoping collision-rate sum with `n + 1` active blocks.  For the uniform merger law,
the total rate contributed by mergers of every possible size is this sum: the multiplicity
times the rate for size `j + 2` reduces to
`(n + 1) (1 / (j + 1) - 1 / (j + 2))`. -/
noncomputable def bolthausenSznitmanTotalMergerRate (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    ((n : ℝ) + 1) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2))

/-- The reciprocal differences telescope exactly. -/
theorem reciprocalDifference_sum (n : ℕ) :
    ∑ j ∈ Finset.range n,
      (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) =
        1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **Exact BS rate law.**  With `n + 1` active blocks the next merger occurs at total rate
`n`; equivalently, with `b` blocks the rate is `b - 1`. -/
@[simp] theorem bolthausenSznitmanTotalMergerRate_eq (n : ℕ) :
    bolthausenSznitmanTotalMergerRate n = n := by
  unfold bolthausenSznitmanTotalMergerRate
  rw [← Finset.mul_sum, reciprocalDifference_sum]
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **The BS reciprocal-rate ladder diverges.**  Unlike Kingman's quadratic ladder, the
linear BS total rate does not satisfy the convergent reciprocal-sum condition that creates
localized Müntz null directions.  This removes that particular obstruction; it does not by
itself prove injectivity of a nonlinear demographic model. -/
theorem not_summable_one_div_bolthausenSznitmanTotalMergerRate :
    ¬ Summable fun n : ℕ ↦ 1 / bolthausenSznitmanTotalMergerRate (n + 1) := by
  intro h
  refine Real.not_summable_one_div_natCast ?_
  refine (summable_nat_add_iff 1).mp ?_
  simpa using h

end Calibrator
