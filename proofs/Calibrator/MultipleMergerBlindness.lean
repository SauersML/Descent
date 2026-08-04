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

/-- At the excluded parameter the first factor divides by zero, so Mathlib returns `0` for the
whole product: every merger of three or more lineages is reported as impossible. -/
theorem speedTiltFullMergerRate_at_minus_two_is_junk (extra : ℕ) :
    speedTiltFullMergerRate (-2) (extra + 1) = 0 := by
  simp [speedTiltFullMergerRate, Finset.prod_range_succ']


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

/-- The algebraic chart extends continuously to the star boundary `β = -1`: every full merger
coordinate equals one there. -/
@[simp] theorem speedTiltFullMergerRate_neg_one (extra : ℕ) :
    speedTiltFullMergerRate (-1) extra = 1 := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [speedTiltFullMergerRate_succ, ih, one_mul]
      have hne : (extra : ℝ) + 1 ≠ 0 := by positivity
      rw [show (-1 : ℝ) + (extra : ℝ) + 2 = (extra : ℝ) + 1 by ring]
      exact div_self hne

/-- Uniform Kingman-side envelope: every full merger of at least three lineages is bounded by
the three-lineage coordinate `1 / (β + 2)`. -/
theorem speedTiltFullMergerRate_succ_le_threeLineage
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    speedTiltFullMergerRate β (extra + 1) ≤ 1 / (β + 2) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      exact (speedTiltFullMergerRate_strictAnti_extra hβ (extra + 1)).le.trans ih

/-- Multiplicative penalty contributed by `extra` lineages outside a specified merging
`k`-tuple.  This is the finite Gamma-ratio identity

`Gamma(β + extra + 1) / Gamma(β + 1) * Gamma(β + k) / Gamma(β + k + extra)`.

The product form stays elementary and makes positivity transparent on `β > -1`, `2 ≤ k`. -/
noncomputable def speedTiltNonMergerFactor (β : ℝ) (k extra : ℕ) : ℝ :=
  ∏ j ∈ Finset.range extra,
    (β + (j : ℝ) + 1) / (β + (k : ℝ) + (j : ℝ))

/-- No outside lineage contributes no survival penalty. -/
@[simp] theorem speedTiltNonMergerFactor_zero (β : ℝ) (k : ℕ) :
    speedTiltNonMergerFactor β k 0 = 1 := by
  simp [speedTiltNonMergerFactor]

/-- Exact recurrence when one more lineage must avoid the specified merging parent. -/
theorem speedTiltNonMergerFactor_succ (β : ℝ) (k extra : ℕ) :
    speedTiltNonMergerFactor β k (extra + 1) =
      speedTiltNonMergerFactor β k extra *
        ((β + (extra : ℝ) + 1) / (β + (k : ℝ) + (extra : ℝ))) := by
  simp only [speedTiltNonMergerFactor, Finset.prod_range_succ]

/-- The outside-lineage factor is positive throughout the probability-law domain. -/
theorem speedTiltNonMergerFactor_pos
    {β : ℝ} (hβ : -1 < β) {k : ℕ} (hk : 2 ≤ k) (extra : ℕ) :
    0 < speedTiltNonMergerFactor β k extra := by
  unfold speedTiltNonMergerFactor
  apply Finset.prod_pos
  intro j _
  apply div_pos
  · have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  · have hkReal : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith

/-- Each additional nonmerging lineage strictly lowers a specified merger rate. -/
theorem speedTiltNonMergerFactor_strictAnti_extra
    {β : ℝ} (hβ : -1 < β) {k : ℕ} (hk : 2 ≤ k) (extra : ℕ) :
    speedTiltNonMergerFactor β k (extra + 1) <
      speedTiltNonMergerFactor β k extra := by
  rw [speedTiltNonMergerFactor_succ]
  have hfactorPos : 0 < speedTiltNonMergerFactor β k extra :=
    speedTiltNonMergerFactor_pos hβ hk extra
  have hden : 0 < β + (k : ℝ) + (extra : ℝ) := by
    have hkReal : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hextra : 0 ≤ (extra : ℝ) := Nat.cast_nonneg extra
    linarith
  have hratio :
      (β + (extra : ℝ) + 1) / (β + (k : ℝ) + (extra : ℝ)) < 1 := by
    apply (div_lt_one hden).2
    have hkReal : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  calc
    speedTiltNonMergerFactor β k extra *
        ((β + (extra : ℝ) + 1) / (β + (k : ℝ) + (extra : ℝ))) <
        speedTiltNonMergerFactor β k extra * 1 :=
      mul_lt_mul_of_pos_left hratio hfactorPos
    _ = speedTiltNonMergerFactor β k extra := mul_one _

/-- The outside-lineage factor belongs to `(0, 1]`. -/
theorem speedTiltNonMergerFactor_le_one
    {β : ℝ} (hβ : -1 < β) {k : ℕ} (hk : 2 ≤ k) (extra : ℕ) :
    speedTiltNonMergerFactor β k extra ≤ 1 := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      exact (speedTiltNonMergerFactor_strictAnti_extra hβ hk extra).le.trans ih

/-- At the star boundary, the presence of any outside lineage kills a full simultaneous merger:
the first outside-lineage factor is exactly zero. -/
@[simp] theorem speedTiltNonMergerFactor_neg_one_succ (k extra : ℕ) :
    speedTiltNonMergerFactor (-1) k (extra + 1) = 0 := by
  induction extra with
  | zero => simp [speedTiltNonMergerFactor_succ]
  | succ extra ih =>
      rw [speedTiltNonMergerFactor_succ, ih, zero_mul]

/-- For a specified binary merger, the outside-lineage product telescopes exactly.  This is the
finite-`β` approach to the Kingman rate one. -/
theorem speedTiltNonMergerFactor_two_eq
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    speedTiltNonMergerFactor β 2 extra =
      (β + 1) / (β + (extra : ℝ) + 1) := by
  induction extra with
  | zero =>
      rw [speedTiltNonMergerFactor_zero]
      have hne : β + 1 ≠ 0 := by linarith
      norm_num
      exact (div_self hne).symm
  | succ extra ih =>
      rw [speedTiltNonMergerFactor_succ, ih]
      have hmiddle : β + (extra : ℝ) + 1 ≠ 0 := by
        have hextra : 0 ≤ (extra : ℝ) := Nat.cast_nonneg extra
        linarith
      calc
        (β + 1) / (β + (extra : ℝ) + 1) *
            ((β + (extra : ℝ) + 1) / (β + (2 : ℝ) + (extra : ℝ))) =
            (β + 1) * ((β + (extra : ℝ) + 1)⁻¹ *
              (β + (extra : ℝ) + 1)) *
                (β + (2 : ℝ) + (extra : ℝ))⁻¹ := by
          simp only [div_eq_mul_inv]
          ring
        _ = (β + 1) * (β + (2 : ℝ) + (extra : ℝ))⁻¹ := by
          rw [inv_mul_cancel₀ hmiddle, mul_one]
        _ = (β + 1) / (β + ((extra + 1 : ℕ) : ℝ) + 1) := by
          rw [div_eq_mul_inv]
          congr 2
          push_cast
          ring

/-- All `b`-lineage, specified-`k`-tuple rates under the normalized
`Beta(1, β + 1)` law.  This is the exact finite-product form of

`(β + 1) * B(k - 1, β + b - k + 1)`.

The first factor is the full `k`-merger moment; the second is the penalty that each of the
`b-k` outside lineages avoids the merging parent. -/
noncomputable def speedTiltBetaMergerRate (β : ℝ) (b k : ℕ) : ℝ :=
  speedTiltFullMergerRate β (k - 2) * speedTiltNonMergerFactor β k (b - k)

/-- With no outside lineage, the general rate reduces to the full-merger coordinate. -/
theorem speedTiltBetaMergerRate_self (β : ℝ) (k : ℕ) :
    speedTiltBetaMergerRate β k k = speedTiltFullMergerRate β (k - 2) := by
  simp [speedTiltBetaMergerRate]

/-- Every specified merger rate is positive on the biological domain. -/
theorem speedTiltBetaMergerRate_pos
    {β : ℝ} (hβ : -1 < β) {b k : ℕ} (hk : 2 ≤ k) :
    0 < speedTiltBetaMergerRate β b k := by
  unfold speedTiltBetaMergerRate
  exact mul_pos (speedTiltFullMergerRate_pos hβ (k - 2))
    (speedTiltNonMergerFactor_pos hβ hk (b - k))

/-- Every specified merger coordinate belongs to `(0, 1]`. -/
theorem speedTiltBetaMergerRate_mem_Ioc
    {β : ℝ} (hβ : -1 < β) {b k : ℕ} (hk : 2 ≤ k) :
    speedTiltBetaMergerRate β b k ∈ Set.Ioc 0 1 := by
  refine ⟨speedTiltBetaMergerRate_pos hβ hk, ?_⟩
  unfold speedTiltBetaMergerRate
  exact (mul_le_mul
      (speedTiltFullMergerRate_le_one hβ (k - 2))
      (speedTiltNonMergerFactor_le_one hβ hk (b - k))
      (speedTiltNonMergerFactor_pos hβ hk (b - k)).le
      (by norm_num)).trans (by norm_num)

/-- Exact `Beta(1, β + 1)` recurrence after adding one outside lineage. -/
theorem speedTiltBetaMergerRate_add_outside_succ
    (β : ℝ) (k extra : ℕ) :
    speedTiltBetaMergerRate β (k + (extra + 1)) k =
      speedTiltBetaMergerRate β (k + extra) k *
        ((β + (extra : ℝ) + 1) / (β + (k : ℝ) + (extra : ℝ))) := by
  simp only [speedTiltBetaMergerRate, Nat.add_sub_cancel_left,
    speedTiltNonMergerFactor_succ]
  ring

/-- For a fixed specified merger, each additional outside lineage strictly lowers its rate. -/
theorem speedTiltBetaMergerRate_add_outside_strictAnti
    {β : ℝ} (hβ : -1 < β) {k : ℕ} (hk : 2 ≤ k) (extra : ℕ) :
    speedTiltBetaMergerRate β (k + (extra + 1)) k <
      speedTiltBetaMergerRate β (k + extra) k := by
  simp only [speedTiltBetaMergerRate, Nat.add_sub_cancel_left]
  exact mul_lt_mul_of_pos_left
    (speedTiltNonMergerFactor_strictAnti_extra hβ hk extra)
    (speedTiltFullMergerRate_pos hβ (k - 2))

/-- At the star boundary, every full merger has rate one. -/
@[simp] theorem speedTiltBetaMergerRate_neg_one_self (k : ℕ) :
    speedTiltBetaMergerRate (-1) k k = 1 := by
  rw [speedTiltBetaMergerRate_self, speedTiltFullMergerRate_neg_one]

/-- At the star boundary, a specified merger has rate zero as soon as one outside lineage must
avoid the common parent. -/
@[simp] theorem speedTiltBetaMergerRate_neg_one_add_outside_succ (k extra : ℕ) :
    speedTiltBetaMergerRate (-1) (k + (extra + 1)) k = 0 := by
  simp [speedTiltBetaMergerRate]

/-- Uniform Kingman-side envelope for the complete chart: every merger of three or more lineages
is at most the normalized triple-merger coordinate. -/
theorem speedTiltBetaMergerRate_three_or_more_le_triple
    {β : ℝ} (hβ : -1 < β) (b extra : ℕ) :
    speedTiltBetaMergerRate β b (extra + 3) ≤ 1 / (β + 2) := by
  unfold speedTiltBetaMergerRate
  have hk : 2 ≤ extra + 3 := by omega
  calc
    speedTiltFullMergerRate β (extra + 3 - 2) *
        speedTiltNonMergerFactor β (extra + 3) (b - (extra + 3)) ≤
        speedTiltFullMergerRate β (extra + 3 - 2) :=
      mul_le_of_le_one_right
        (speedTiltFullMergerRate_pos hβ (extra + 3 - 2)).le
        (speedTiltNonMergerFactor_le_one hβ hk (b - (extra + 3)))
    _ = speedTiltFullMergerRate β (extra + 1) := rfl
    _ ≤ 1 / (β + 2) := speedTiltFullMergerRate_succ_le_threeLineage hβ extra

/-- Exact finite-`β` specified binary-merger rate in the presence of `extra` outside lineages. -/
theorem speedTiltBetaMergerRate_two_with_outside_eq
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    speedTiltBetaMergerRate β (extra + 2) 2 =
      (β + 1) / (β + (extra : ℝ) + 1) := by
  unfold speedTiltBetaMergerRate
  rw [speedTiltFullMergerRate_zero]
  simp only [one_mul]
  simpa using speedTiltNonMergerFactor_two_eq hβ extra

/-- Exact Kingman-side error of the specified binary-merger coordinate. -/
theorem one_sub_speedTiltBetaMergerRate_two_with_outside
    {β : ℝ} (hβ : -1 < β) (extra : ℕ) :
    1 - speedTiltBetaMergerRate β (extra + 2) 2 =
      (extra : ℝ) / (β + (extra : ℝ) + 1) := by
  rw [speedTiltBetaMergerRate_two_with_outside_eq hβ]
  have hden : β + (extra : ℝ) + 1 ≠ 0 := by
    have hextra : 0 ≤ (extra : ℝ) := Nat.cast_nonneg extra
    linarith
  field_simp
  ring

/-! ### Raw regular-variation scale versus pair-rate normalization -/

/-- Pair-collision coefficient relative to the tail scale `d_N` in the index-one
regular-variation theorem.  The asymptotic clock is
`c_(N,β) ∼ d_N * speedTiltCollisionScaleCoefficient β`. -/
noncomputable def speedTiltCollisionScaleCoefficient (β : ℝ) : ℝ :=
  1 / (β + 1)

/-- At the excluded parameter the coefficient divides by zero and Mathlib returns `0`. -/
theorem speedTiltCollisionScaleCoefficient_at_minus_one_is_junk :
    speedTiltCollisionScaleCoefficient (-1) = 0 := by
  norm_num [speedTiltCollisionScaleCoefficient]


/-- The collision-clock coefficient is positive exactly on the speed-tilt probability domain. -/
theorem speedTiltCollisionScaleCoefficient_pos
    {β : ℝ} (hβ : -1 < β) :
    0 < speedTiltCollisionScaleCoefficient β := by
  unfold speedTiltCollisionScaleCoefficient
  exact one_div_pos.mpr (by linarith)

/-- Increasing the speed penalty shortens the pair-collision coefficient on the raw tail scale. -/
theorem speedTiltCollisionScaleCoefficient_strictAnti
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ : β₁ < β₂) :
    speedTiltCollisionScaleCoefficient β₂ < speedTiltCollisionScaleCoefficient β₁ := by
  unfold speedTiltCollisionScaleCoefficient
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- Raw merger coefficient on the `d_N` timescale before pair-rate normalization. -/
noncomputable def speedTiltRawMergerCoefficient (β : ℝ) (b k : ℕ) : ℝ :=
  speedTiltCollisionScaleCoefficient β * speedTiltBetaMergerRate β b k

/-- The raw pair coefficient is exactly the regular-variation collision-clock coefficient. -/
@[simp] theorem speedTiltRawMergerCoefficient_two_two (β : ℝ) :
    speedTiltRawMergerCoefficient β 2 2 = speedTiltCollisionScaleCoefficient β := by
  unfold speedTiltRawMergerCoefficient
  rw [speedTiltBetaMergerRate_self, speedTiltFullMergerRate_zero, mul_one]

/-- **Clock normalization identity.**  Dividing every raw regular-variation coefficient by the
raw pair coefficient recovers the normalized `Beta(1, β + 1)` rate chart exactly. -/
theorem speedTiltRawMergerCoefficient_div_pair
    {β : ℝ} (hβ : -1 < β) (b k : ℕ) :
    speedTiltRawMergerCoefficient β b k /
        speedTiltRawMergerCoefficient β 2 2 =
      speedTiltBetaMergerRate β b k := by
  rw [speedTiltRawMergerCoefficient_two_two]
  unfold speedTiltRawMergerCoefficient
  field_simp [(speedTiltCollisionScaleCoefficient_pos hβ).ne']

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

/-- A zero observed triple rate inverts to Mathlib's junk `0`, so the readout reports the
parameter `-2` -- the excluded endpoint of the biological domain, not a measurement. -/
theorem speedBiasParameterFromTripleRate_at_zero_rate_is_junk :
    speedBiasParameterFromTripleRate 0 = -2 := by
  norm_num [speedBiasParameterFromTripleRate]


/-- **Exact speed-bias recovery.**  Throughout the admissible domain, the first non-pairwise
genealogical coordinate recovers the tilt parameter without approximation. -/
theorem speedBiasParameterFromTripleRate_recovers
    (β : ℝ) :
    speedBiasParameterFromTripleRate (speedTiltBetaMergerRate β 3 3) = β := by
  simp [speedBiasParameterFromTripleRate]

/-- Speed tilt after a front-displacement scale `γ`: the genealogy sees `θ / γ`. -/
noncomputable def frontSpeedBiasParameter (θ γ : ℝ) : ℝ :=
  θ / γ

/-- A zero displacement scale divides by zero and Mathlib returns `0`: the genealogy is
reported as untilted whatever the front tilt actually is. -/
theorem frontSpeedBiasParameter_at_zero_scale_is_junk (θ : ℝ) :
    frontSpeedBiasParameter θ 0 = 0 := by
  simp [frontSpeedBiasParameter]


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

/-- Any positive merger-rate ladder bounded above by the linear ladder has a divergent
reciprocal sum.  This is the reusable spectral criterion behind the Bolthausen--Sznitman
comparison: linear-or-slower collision clocks cannot exhibit Kingman's summable reciprocal-rate
obstruction. -/
theorem not_summable_reciprocal_of_rate_le_natSucc
    (rate : ℕ → ℝ) (hpos : ∀ n, 0 < rate n)
    (hle : ∀ n, rate n ≤ (n : ℝ) + 1) :
    ¬ Summable fun n ↦ 1 / rate n := by
  intro hsummable
  have hharmonic : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) :=
    Summable.of_nonneg_of_le
      (fun n ↦ by positivity)
      (fun n ↦ one_div_le_one_div_of_le (hpos n) (hle n))
      hsummable
  refine Real.not_summable_one_div_natCast ?_
  refine (summable_nat_add_iff 1).mp ?_
  simpa only [Nat.cast_add, Nat.cast_one] using hharmonic

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
  apply not_summable_reciprocal_of_rate_le_natSucc
  · intro n
    rw [bolthausenSznitmanTotalMergerRate_eq]
    positivity
  · intro n
    rw [bolthausenSznitmanTotalMergerRate_eq]
    norm_num

end Calibrator
