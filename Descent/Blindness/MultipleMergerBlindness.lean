/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Descent.Core.Ratios

namespace Descent.Blindness

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

## Main results

- `lambdaCoalescent_pairwise_rate_blind`: universal pair-rate blindness.
- `speedTilt_pairwise_blind_triple_separates`: three lineages are minimal for speed tilts.
- `speedBiasParameterFromTripleRate_recovers`: exact inverse of the triple-rate chart.
- `frontSpeedBias_tripleMergerRate_injective`: front-speed identification at fixed scale.
- `tendsto_speedTiltTwoFamilyToPairRatio_zero`: simultaneous disjoint mergers disappear on
  the pair-collision timescale.
- `tendsto_speedTiltBetaMergerRate_three_or_more_atTop`: multiple mergers vanish at Kingman.
- `not_summable_one_div_bolthausenSznitmanTotalMergerRate`: the linear-rate contrast.
- `pulled_semipushed_reciprocal_dichotomy`: linear pulled clocks have divergent reciprocal
  ladders, while every superlinear stable clock has a summable reciprocal ladder.
-/

open MeasureTheory
open Filter

/-- Rate at which a specified `k`-tuple among `b` active lineages merges in a
`Λ`-coalescent.  Natural-number subtraction makes the definition total; the biological range
is `2 ≤ k ≤ b`.

Empirical status: NOT AN EMPIRICAL CLAIM. The integral IS the definition of a
`Λ`-coalescent (Pitman 1999, Sagitov 1999): a `Λ`-coalescent is by construction the process
whose `k`-of-`b` merger rate is `∫ x^(k-2) (1-x)^(b-k) dΛ`, so no population can make this
formula a different one. It is a modelling frame, and the only empirical questions --
which `Λ` a real population has, and whether one exists at all -- are claims about the
INPUT `Λ`, which is exactly what this file shows the pairwise spectrum cannot answer.
`lambdaCoalescentMergerRate_two_two` is the sharpest form of that: after normalization the
pair rate is `1` for every `Λ`, so it carries no information about which one. -/
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

/-- Every full-merger coordinate involving at least three lineages is strictly decreasing in
the speed-bias parameter throughout the biological domain. -/
theorem speedTiltFullMergerRate_strictAnti_beta
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ : β₁ < β₂) (extra : ℕ) :
    speedTiltFullMergerRate β₂ (extra + 1) <
      speedTiltFullMergerRate β₁ (extra + 1) := by
  have hβ₂ : -1 < β₂ := hβ₁.trans hβ
  induction extra with
  | zero =>
      simp only [Nat.zero_add, speedTiltFullMergerRate_one]
      exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  | succ extra ih =>
      change speedTiltFullMergerRate β₂ ((extra + 1) + 1) <
        speedTiltFullMergerRate β₁ ((extra + 1) + 1)
      rw [speedTiltFullMergerRate_succ β₂ (extra + 1),
        speedTiltFullMergerRate_succ β₁ (extra + 1)]
      have hfactor₂ :
          0 < (((extra + 1 : ℕ) : ℝ) + 1) /
            (β₂ + ((extra + 1 : ℕ) : ℝ) + 2) := by
        apply div_pos
        · positivity
        · have hextra : 0 ≤ (((extra + 1 : ℕ) : ℝ)) := by positivity
          linarith
      have hfactor :
          (((extra + 1 : ℕ) : ℝ) + 1) /
              (β₂ + ((extra + 1 : ℕ) : ℝ) + 2) <
            (((extra + 1 : ℕ) : ℝ) + 1) /
              (β₁ + ((extra + 1 : ℕ) : ℝ) + 2) := by
        exact div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)
      calc
        speedTiltFullMergerRate β₂ (extra + 1) *
            ((((extra + 1 : ℕ) : ℝ) + 1) /
              (β₂ + ((extra + 1 : ℕ) : ℝ) + 2)) <
            speedTiltFullMergerRate β₁ (extra + 1) *
              ((((extra + 1 : ℕ) : ℝ) + 1) /
                (β₂ + ((extra + 1 : ℕ) : ℝ) + 2)) :=
          mul_lt_mul_of_pos_right ih hfactor₂
        _ < speedTiltFullMergerRate β₁ (extra + 1) *
              ((((extra + 1 : ℕ) : ℝ) + 1) /
                (β₁ + ((extra + 1 : ℕ) : ℝ) + 2)) :=
          mul_lt_mul_of_pos_left hfactor
            (speedTiltFullMergerRate_pos hβ₁ (extra + 1))

/-- Any one full-merger coordinate of order at least three identifies the speed-bias parameter
on the entire admissible domain. The triple rate is the smallest such coordinate, not the only
one. -/
theorem speedTiltFullMergerRate_injective_on
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ₂ : -1 < β₂) (extra : ℕ)
    (hrate : speedTiltFullMergerRate β₁ (extra + 1) =
      speedTiltFullMergerRate β₂ (extra + 1)) :
    β₁ = β₂ := by
  rcases lt_trichotomy β₁ β₂ with hlt | heq | hgt
  · exact False.elim ((speedTiltFullMergerRate_strictAnti_beta hβ₁ hlt extra).ne hrate.symm)
  · exact heq
  · exact False.elim ((speedTiltFullMergerRate_strictAnti_beta hβ₂ hgt extra).ne hrate)

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

/-- **Exact Bolthausen--Sznitman full-merger chart.** At zero speed tilt, the normalized rate
for all `extra + 2` lineages to merge simultaneously is `1 / (extra + 1)`. Equivalently,
`λ k k = 1 / (k - 1)` throughout the untilted endpoint. -/
theorem speedTiltFullMergerRate_zero_beta (extra : ℕ) :
    speedTiltFullMergerRate 0 extra = 1 / ((extra : ℝ) + 1) := by
  induction extra with
  | zero => norm_num
  | succ extra ih =>
      rw [speedTiltFullMergerRate_succ, ih]
      have hleft : (extra : ℝ) + 1 ≠ 0 := by positivity
      have hright : (extra : ℝ) + 2 ≠ 0 := by positivity
      rw [show (0 : ℝ) + (extra : ℝ) + 2 = (extra : ℝ) + 2 by ring]
      push_cast
      field_simp
      ring

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

/-- Where the first factor's denominator vanishes Mathlib returns `0` for the whole product, so
every survival penalty is reported as total. -/
theorem speedTiltNonMergerFactor_at_zero_first_denominator_is_junk
    (β : ℝ) (k extra : ℕ) (hzero : β + (k : ℝ) = 0) :
    speedTiltNonMergerFactor β k (extra + 1) = 0 := by
  unfold speedTiltNonMergerFactor
  rw [Finset.prod_range_succ']
  simp [hzero]


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

/-- Every full-merger coordinate in the general rate API with at least three active lineages
identifies the speed-bias parameter. -/
theorem speedTiltBetaMergerRate_self_injective_on
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ₂ : -1 < β₂) (extra : ℕ)
    (hrate :
      speedTiltBetaMergerRate β₁ (extra + 3) (extra + 3) =
        speedTiltBetaMergerRate β₂ (extra + 3) (extra + 3)) :
    β₁ = β₂ := by
  rw [speedTiltBetaMergerRate_self, speedTiltBetaMergerRate_self] at hrate
  have hsimplify : extra + 3 - 2 = extra + 1 := by omega
  rw [hsimplify] at hrate
  exact speedTiltFullMergerRate_injective_on hβ₁ hβ₂ extra hrate

/-- The general merger-rate API inherits the exact Bolthausen--Sznitman full-merger law. -/
@[simp] theorem speedTiltBetaMergerRate_zero_beta_self (extra : ℕ) :
    speedTiltBetaMergerRate 0 (extra + 2) (extra + 2) =
      1 / ((extra : ℝ) + 1) := by
  rw [speedTiltBetaMergerRate_self]
  simpa using speedTiltFullMergerRate_zero_beta extra

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

/-- Every full merger involving at least three lineages vanishes at the Kingman endpoint
`β → ∞`. -/
theorem tendsto_speedTiltFullMergerRate_succ_atTop (extra : ℕ) :
    Tendsto (fun β : ℝ ↦ speedTiltFullMergerRate β (extra + 1)) atTop (nhds 0) := by
  have hden : Tendsto (fun β : ℝ ↦ β + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hupper : Tendsto (fun β : ℝ ↦ 1 / (β + 2)) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (-1 : ℝ)] with β hβ
    exact (speedTiltFullMergerRate_pos hβ (extra + 1)).le
  · filter_upwards [eventually_gt_atTop (-1 : ℝ)] with β hβ
    exact speedTiltFullMergerRate_succ_le_threeLineage hβ extra

/-- In the complete rate chart, every specified merger of at least three lineages vanishes at
the Kingman endpoint. -/
theorem tendsto_speedTiltBetaMergerRate_three_or_more_atTop (b extra : ℕ) :
    Tendsto (fun β : ℝ ↦ speedTiltBetaMergerRate β b (extra + 3)) atTop (nhds 0) := by
  have hden : Tendsto (fun β : ℝ ↦ β + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hupper : Tendsto (fun β : ℝ ↦ 1 / (β + 2)) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (-1 : ℝ)] with β hβ
    exact (speedTiltBetaMergerRate_pos hβ (by omega : 2 ≤ extra + 3)).le
  · filter_upwards [eventually_gt_atTop (-1 : ℝ)] with β hβ
    exact speedTiltBetaMergerRate_three_or_more_le_triple hβ b extra

/-- Specified binary-merger rates converge to one at the Kingman endpoint, regardless of the
fixed number of outside lineages. -/
theorem tendsto_speedTiltBetaMergerRate_two_with_outside_atTop (extra : ℕ) :
    Tendsto (fun β : ℝ ↦ speedTiltBetaMergerRate β (extra + 2) 2) atTop (nhds 1) := by
  have hden : Tendsto (fun β : ℝ ↦ β + (extra : ℝ) + 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop ((extra : ℝ) + 1) tendsto_id using 1
    funext β
    dsimp
    ring
  have hzero : Tendsto (fun β : ℝ ↦ (extra : ℝ) / (β + (extra : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (extra : ℝ)
  have hlimit : Tendsto (fun β : ℝ ↦ 1 - (extra : ℝ) / (β + (extra : ℝ) + 1))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hzero
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (-1 : ℝ)] with β hβ
  linarith [one_sub_speedTiltBetaMergerRate_two_with_outside hβ extra]

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

/-! ### Why simultaneous disjoint mergers disappear -/

/-- Pair-collision asymptotic at tail scale `d`. In the index-one regular-variation theorem
this represents `c_(N,β) ∼ d_N / (β + 1)`. -/
noncomputable def speedTiltPairCollisionScale (β d : ℝ) : ℝ :=
  d * speedTiltCollisionScaleCoefficient β

/-- Two-family pair-pair collision asymptotic at tail scale `d`. Its quadratic dependence on
`d` is the mechanism excluding simultaneous disjoint mergers from the limiting coalescent. -/
noncomputable def speedTiltTwoFamilyCollisionScale (β d : ℝ) : ℝ :=
  d ^ 2 / ((β + 2) * (β + 3))

/-- **Exact simultaneous-to-single collision ratio.** Relative to one pair collision, the
two-family event carries one extra power of the rare-family scale. -/
theorem speedTiltTwoFamilyCollisionScale_div_pair
    {β d : ℝ} (hβ : -1 < β) (hd : d ≠ 0) :
    speedTiltTwoFamilyCollisionScale β d / speedTiltPairCollisionScale β d =
      d * (β + 1) / ((β + 2) * (β + 3)) := by
  unfold speedTiltTwoFamilyCollisionScale speedTiltPairCollisionScale
    speedTiltCollisionScaleCoefficient
  have hβ1 : β + 1 ≠ 0 := by linarith
  have hβ2 : β + 2 ≠ 0 := by linarith
  have hβ3 : β + 3 ≠ 0 := by linarith
  field_simp

/-- **No simultaneous-merger limit.** The two-family event is negligible on the pair-collision
clock as the regular-variation tail scale tends to zero. -/
theorem tendsto_speedTiltTwoFamilyToPairRatio_zero (β : ℝ) :
    Tendsto (fun d : ℝ ↦ d * (β + 1) / ((β + 2) * (β + 3)))
      (nhds 0) (nhds 0) := by
  have hid : Tendsto (fun d : ℝ ↦ d) (nhds 0) (nhds 0) := tendsto_id
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hid.const_mul ((β + 1) / ((β + 2) * (β + 3)))

/-- The same negligibility conclusion along any asymptotic tail-scale sequence. -/
theorem tendsto_speedTiltTwoFamilyToPairRatio_comp
    {ι : Type*} {l : Filter ι} (β : ℝ) {tailScale : ι → ℝ}
    (hscale : Tendsto tailScale l (nhds 0)) :
    Tendsto
      (fun index ↦ tailScale index * (β + 1) / ((β + 2) * (β + 3)))
      l (nhds 0) :=
  (tendsto_speedTiltTwoFamilyToPairRatio_zero β).comp hscale

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
  exact speedTiltBetaMergerRate_self_injective_on hβ₁ hβ₂ 0 hrate

/-- **Pairwise blindness, three-lineage identification.** Distinct admissible speed tilts
agree exactly at the normalized pair rate and disagree at the first multiple-merger
coordinate. Thus three lineages are both necessary and sufficient inside this family. -/
theorem speedTilt_pairwise_blind_triple_separates
    {β₁ β₂ : ℝ} (hβ₁ : -1 < β₁) (hβ₂ : -1 < β₂) (hne : β₁ ≠ β₂) :
    speedTiltBetaMergerRate β₁ 2 2 = speedTiltBetaMergerRate β₂ 2 2 ∧
      speedTiltBetaMergerRate β₁ 3 3 ≠ speedTiltBetaMergerRate β₂ 3 3 := by
  constructor
  · simp
  · intro hrate
    exact hne (speedTiltBetaMergerRate_three_three_injective_on hβ₁ hβ₂ hrate)

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

/-- The inverse chart maps every genuine triple-merger probability back into the admissible
speed-tilt domain. -/
theorem speedBiasParameterFromTripleRate_mem_domain
    {rate : ℝ} (hrate : rate ∈ Set.Ioo 0 1) :
    -1 < speedBiasParameterFromTripleRate rate := by
  have hinv : 1 < rate⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hrate.1 hrate.2
  unfold speedBiasParameterFromTripleRate
  linarith

/-- **Surjectivity of the triple-rate chart.** Every candidate rate is recovered after
conversion to its speed-bias parameter. On `(0,1)` the preceding theorem additionally certifies
that this parameter belongs to the biological domain; at zero Mathlib's total inverse passes
through the excluded junk parameter `-2`. -/
theorem speedTiltBetaMergerRate_speedBiasParameterFromTripleRate (rate : ℝ) :
    speedTiltBetaMergerRate (speedBiasParameterFromTripleRate rate) 3 3 = rate := by
  simp [speedBiasParameterFromTripleRate]

/-- Speed tilt after a front-displacement scale `γ`: the genealogy sees `θ / γ`. -/
noncomputable def frontSpeedBiasParameter (θ γ : ℝ) : ℝ :=
  Descent.Core.ratio θ γ

/-- A zero displacement scale divides by zero and Mathlib returns `0`: the genealogy is
reported as untilted whatever the front tilt actually is. -/
theorem frontSpeedBiasParameter_at_zero_scale_is_junk (θ : ℝ) :
    frontSpeedBiasParameter θ 0 = 0 := by
  simp [frontSpeedBiasParameter, Descent.Core.ratio]


/-- Observable three-lineage rate for a front tilt `θ` and displacement scale `γ`. -/
theorem frontSpeedBias_tripleMergerRate (θ γ : ℝ) :
    speedTiltBetaMergerRate (frontSpeedBiasParameter θ γ) 3 3 =
      1 / (θ / γ + 2) := by
  simp [frontSpeedBiasParameter, Descent.Core.ratio]

/-- **Speed identification at a fixed front scale.** On the admissible microcanonical-tilt
domain `-γ < θ`, the normalized three-lineage merger rate identifies the front-speed tilt
exactly whenever the displacement scale is positive. -/
theorem frontSpeedBias_tripleMergerRate_injective
    {θ₁ θ₂ γ : ℝ} (hγ : 0 < γ) (hθ₁ : -γ < θ₁) (hθ₂ : -γ < θ₂)
    (hrate :
      speedTiltBetaMergerRate (frontSpeedBiasParameter θ₁ γ) 3 3 =
        speedTiltBetaMergerRate (frontSpeedBiasParameter θ₂ γ) 3 3) :
    θ₁ = θ₂ := by
  have hβ₁ : -1 < frontSpeedBiasParameter θ₁ γ := by
    unfold frontSpeedBiasParameter Descent.Core.ratio
    apply (lt_div_iff₀ hγ).2
    simpa using hθ₁
  have hβ₂ : -1 < frontSpeedBiasParameter θ₂ γ := by
    unfold frontSpeedBiasParameter Descent.Core.ratio
    apply (lt_div_iff₀ hγ).2
    simpa using hθ₂
  have hparameter := speedTiltBetaMergerRate_three_three_injective_on hβ₁ hβ₂ hrate
  unfold frontSpeedBiasParameter Descent.Core.ratio at hparameter
  exact (div_left_inj' hγ.ne').mp hparameter

/-- Front-speed tilt reconstructed from an observed normalized triple-merger rate and a known
positive displacement scale. -/
noncomputable def frontSpeedTiltFromTripleRate (rate γ : ℝ) : ℝ :=
  γ * speedBiasParameterFromTripleRate rate

/-- **At the Bolthausen--Sznitman triple rate the recovered front tilt is zero, which is the
untilted genealogy.**

The zero of the readout, and a real fact about where the Bolthausen--Sznitman point sits --
but not a reference evaluation. It holds for EVERY `γ`, which is the tell: the displacement
scale drops out entirely, so the theorem says nothing about how `γ` enters and a competitor
scaled by any factor satisfies it. Renamed rather than moved, with the evaluation that does
pin the form supplied below. -/
theorem frontSpeedTiltFromTripleRate_at_bolthausen_sznitman (γ : ℝ) :
    frontSpeedTiltFromTripleRate (1 / 2) γ = 0 := by
  unfold frontSpeedTiltFromTripleRate speedBiasParameterFromTripleRate
  norm_num

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem frontSpeedTiltFromTripleRate_at_reference_point :
    frontSpeedTiltFromTripleRate (1 / 4) 3 = 6 := by
  unfold frontSpeedTiltFromTripleRate speedBiasParameterFromTripleRate
  norm_num


/-- **Exact dimensional speed recovery.** Once the displacement scale is known, the first
non-pairwise genealogical coordinate recovers the original front-speed tilt exactly. -/
theorem frontSpeedTiltFromTripleRate_recovers
    (θ γ : ℝ) (hγ : γ ≠ 0) :
    frontSpeedTiltFromTripleRate
        (speedTiltBetaMergerRate (frontSpeedBiasParameter θ γ) 3 3) γ = θ := by
  unfold frontSpeedTiltFromTripleRate
  rw [speedBiasParameterFromTripleRate_recovers]
  unfold frontSpeedBiasParameter Descent.Core.ratio
  field_simp

/-- A valid triple-merger probability reconstructs an admissible dimensional speed tilt at
every positive front-displacement scale. -/
theorem frontSpeedTiltFromTripleRate_mem_domain
    {rate γ : ℝ} (hrate : rate ∈ Set.Ioo 0 1) (hγ : 0 < γ) :
    -γ < frontSpeedTiltFromTripleRate rate γ := by
  unfold frontSpeedTiltFromTripleRate
  have hβ := speedBiasParameterFromTripleRate_mem_domain hrate
  nlinarith

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
  simp

/-! ## Bolthausen--Sznitman total-rate ladder -/

/-- Any positive merger-rate ladder bounded above by a positive multiple of the linear ladder
has a divergent reciprocal sum. This is the scale-invariant spectral criterion behind the
Bolthausen--Sznitman comparison: linear-or-slower collision clocks cannot exhibit Kingman's
summable reciprocal-rate obstruction. -/
theorem not_summable_reciprocal_of_rate_le_scaled_natSucc
    (rate : ℕ → ℝ) (scale : ℝ) (hpos : ∀ n, 0 < rate n)
    (hle : ∀ n, rate n ≤ scale * ((n : ℝ) + 1)) :
    ¬ Summable fun n ↦ 1 / rate n := by
  intro hsummable
  have hscaledSummable : Summable fun n ↦ scale * (1 / rate n) :=
    hsummable.mul_left scale
  have hharmonic : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) :=
    Summable.of_nonneg_of_le
      (fun n ↦ by positivity)
      (fun n ↦ by
        have hn : 0 < (n : ℝ) + 1 := by positivity
        have hcomparison : 1 / ((n : ℝ) + 1) ≤ scale / rate n :=
          (div_le_div_iff₀ hn (hpos n)).2 (by simpa using hle n)
        simpa [div_eq_mul_inv] using hcomparison)
      hscaledSummable
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
  apply not_summable_reciprocal_of_rate_le_scaled_natSucc _ 1
  · intro n
    rw [bolthausenSznitmanTotalMergerRate_eq]
    positivity
  · intro n
    rw [bolthausenSznitmanTotalMergerRate_eq]
    norm_num

/-! ## The Müntz inversion at the pulled/semipushed boundary -/

/-- Canonical positive linear ladder representing a critically pulled total collision rate.
The normalized `Beta(1, β + 1)` family has this order with coefficient `β + 1`; the analytic
identification of that coefficient is separate from the summability argument. -/
noncomputable def criticallyPulledLinearRateLadder
    (coefficient : ℝ) (n : ℕ) : ℝ :=
  coefficient * ((n : ℝ) + 1)

/-- Every positive linear pulled ladder has a divergent reciprocal sum. -/
theorem not_summable_one_div_criticallyPulledLinearRateLadder
    (coefficient : ℝ) (hcoefficient : 0 < coefficient) :
    ¬Summable fun n : ℕ ↦
      1 / criticallyPulledLinearRateLadder coefficient n := by
  apply not_summable_reciprocal_of_rate_le_scaled_natSucc _ coefficient
  · intro n
    exact mul_pos hcoefficient (by positivity)
  · intro n
    exact le_rfl

/-- Canonical power-law ladder for an `α`-stable semipushed genealogy.  Multiplying this by a
positive constant, such as `1 / Γ(α+1)`, does not change reciprocal summability.

Empirical status: NOT AN EMPIRICAL CLAIM; this is the comparison sequence used to formalize
the reciprocal-rate summability boundary. -/
noncomputable def stablePowerRateLadder (alpha : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ alpha

/-- Every superlinear stable ladder has a summable reciprocal series. -/
theorem summable_one_div_stablePowerRateLadder
    (alpha : ℝ) (halpha : 1 < alpha) :
    Summable fun n : ℕ ↦ 1 / stablePowerRateLadder alpha n := by
  have hseries := (Real.summable_one_div_nat_add_rpow 1 alpha).2 halpha
  unfold stablePowerRateLadder
  apply hseries.congr
  intro n
  rw [abs_of_nonneg]
  positivity

/-- The same power-law argument includes the quadratic Kingman order. -/
theorem summable_one_div_quadraticRateLadder :
    Summable fun n : ℕ ↦ 1 / stablePowerRateLadder 2 n := by
  exact summable_one_div_stablePowerRateLadder 2 (by norm_num)

/-- **Müntz-rate inversion.**  The critically pulled linear ladder is nonsummable, whereas every
semipushed exponent `1 < α` is summable.  The statement is about completeness of the candidate
exponential system only after a separate theorem identifies that system with these total rates. -/
theorem pulled_semipushed_reciprocal_dichotomy
    (coefficient alpha : ℝ) (hcoefficient : 0 < coefficient) (halpha : 1 < alpha) :
    (¬Summable fun n : ℕ ↦
        1 / criticallyPulledLinearRateLadder coefficient n) ∧
      Summable fun n : ℕ ↦ 1 / stablePowerRateLadder alpha n :=
  ⟨not_summable_one_div_criticallyPulledLinearRateLadder coefficient hcoefficient,
    summable_one_div_stablePowerRateLadder alpha halpha⟩

end Descent.Blindness
