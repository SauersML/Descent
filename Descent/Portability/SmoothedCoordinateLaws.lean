/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndependentRadialLaws
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

assert_below Descent.Decision Descent.Program

/-!
# Convolving the coordinate laws with uniform noise

PL Theorem 7.4, the absolutely continuous refinement. Each finitely supported coordinate
law of the product construction is convolved with the same uniform law on `[-ε, ε]`. Two
facts are proved here.

First, the convolution preserves matched moments: the `j`-th raw moment of the smoothed
law is a fixed combination of the original moments of order at most `j` with the uniform
noise moments, so two coordinate laws agreeing through degree `k` still agree through
degree `k` after both are smoothed with the same `ε`. This is the manuscript's own
binomial-expansion step for equation (7.7), and it is exact, not asymptotic.

Second, the smoothed law is absolutely continuous with a density bounded by `1/(2ε)`:
the density is the `p`-weighted sum of the indicators of the windows `[v z - ε, v z + ε]`,
normalized, and it integrates to one.

## Scope

What is NOT proved here, and remains the single open item of the obstruction package: the
product of the smoothed marginals over the coordinates, and the convergence of the
expected fitted report under that product law to the finitely supported value. The latter
needs the report's almost-everywhere continuity off the Lebesgue-null zero set of its
denominator together with dominated convergence, neither of which is formalized. The
finitely supported, genuinely independent core is
`IndependentRadialLaws.independent_radial_obstruction`.

## Empirical status

None. The bodies here are algebra and one-dimensional integration: a convolved moment and
a window density are claims about a model, and what carries an empirical status is a named
quantity in a subsystem module asserting that this algebra computes something measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SmoothedCoordinateLaws

open Foundations RadialInterpolation IndependentRadialLaws

noncomputable section

variable {Z : Type*} [Fintype Z]

/-- The `m`-th raw moment of the uniform law on `[-ε, ε]`. -/
def uniformMoment (ε : ℝ) (m : ℕ) : ℝ := (1 / (2 * ε)) * ∫ u in (-ε)..ε, u ^ m

/-- The uniform noise moments in closed form. -/
theorem uniformMoment_eq (ε : ℝ) (m : ℕ) :
    uniformMoment ε m =
      (1 / (2 * ε)) * ((ε ^ (m + 1) - (-ε) ^ (m + 1)) / (m + 1)) := by
  unfold uniformMoment
  rw [integral_pow]

/-- Odd noise moments vanish by symmetry. -/
theorem uniformMoment_odd (ε : ℝ) (m : ℕ) (hm : ¬ Even m) : uniformMoment ε m = 0 := by
  have hpar : Even (m + 1) := Nat.even_add_one.mpr hm
  rw [uniformMoment_eq, hpar.neg_pow]
  ring

/-- **The convolved moment of one atom.** Smoothing an atom at `a` by uniform noise gives
a fixed combination of powers of `a` with the noise moments. -/
theorem smoothed_atom_moment (a ε : ℝ) (j : ℕ) :
    (1 / (2 * ε)) * ∫ u in (-ε)..ε, (a + u) ^ j =
      ∑ m ∈ Finset.range (j + 1), a ^ m * (j.choose m : ℝ) * uniformMoment ε (j - m) := by
  have hcont : ∀ m : ℕ, Continuous fun u : ℝ ↦ a ^ m * u ^ (j - m) * (j.choose m : ℝ) :=
    fun m ↦ (continuous_const.mul (continuous_pow _)).mul continuous_const
  have hint : (∫ u in (-ε)..ε, (a + u) ^ j) =
      ∑ m ∈ Finset.range (j + 1),
        a ^ m * (j.choose m : ℝ) * ∫ u in (-ε)..ε, u ^ (j - m) := by
    rw [intervalIntegral.integral_congr
      (g := fun u ↦ ∑ m ∈ Finset.range (j + 1), a ^ m * u ^ (j - m) * (j.choose m : ℝ))
      (fun u _ ↦ add_pow a u j)]
    rw [intervalIntegral.integral_finset_sum
      (fun m _ ↦ (hcont m).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    ring
  rw [hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  unfold uniformMoment
  ring

/-- **PL equation (7.7) after convolution.** Two finitely supported coordinate laws whose
raw moments agree through degree `k` still agree through degree `k` after both are
convolved with the same uniform noise. -/
theorem smoothed_moment_match (p q v : Z → ℝ) (k : ℕ)
    (hmatch : ∀ r, r ≤ k → (∑ z, p z * v z ^ r) = ∑ z, q z * v z ^ r)
    (ε : ℝ) (j : ℕ) (hj : j ≤ k) :
    (∑ z, p z * ((1 / (2 * ε)) * ∫ u in (-ε)..ε, (v z + u) ^ j)) =
      ∑ z, q z * ((1 / (2 * ε)) * ∫ u in (-ε)..ε, (v z + u) ^ j) := by
  have hrw : ∀ w : Z → ℝ,
      (∑ z, w z * ((1 / (2 * ε)) * ∫ u in (-ε)..ε, (v z + u) ^ j)) =
        ∑ m ∈ Finset.range (j + 1),
          ((j.choose m : ℝ) * uniformMoment ε (j - m)) * ∑ z, w z * v z ^ m := by
    intro w
    have hterm : ∀ z : Z,
        w z * ((1 / (2 * ε)) * ∫ u in (-ε)..ε, (v z + u) ^ j) =
          ∑ m ∈ Finset.range (j + 1),
            ((j.choose m : ℝ) * uniformMoment ε (j - m)) * (w z * v z ^ m) := by
      intro z
      rw [smoothed_atom_moment (v z) ε j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ ↦ by ring
    rw [Finset.sum_congr rfl fun z _ ↦ hterm z, Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ ↦ (Finset.mul_sum _ _ _).symm
  rw [hrw p, hrw q]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [hmatch m (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hj)]

/-- The density of a finitely supported law convolved with uniform noise on `[-ε, ε]`:
the weighted sum of the window indicators, normalized. -/
def smoothDensity (p v : Z → ℝ) (ε : ℝ) (y : ℝ) : ℝ :=
  (∑ z, p z * Set.indicator (Set.Icc (v z - ε) (v z + ε)) (fun _ ↦ (1 : ℝ)) y) / (2 * ε)

/-- A window indicator takes values in `[0,1]`. -/
theorem indicator_mem_unitInterval (c : ℝ) (s : Set ℝ) (y : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ Set.indicator s (fun _ ↦ c) y ∧ Set.indicator s (fun _ ↦ c) y ≤ 1 := by
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy]
    exact ⟨hc, hc1⟩
  · rw [Set.indicator_of_notMem hy]
    exact ⟨le_rfl, by norm_num⟩

/-- The smoothed density is nonnegative. -/
theorem smoothDensity_nonneg (p v : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (ε : ℝ) (hε : 0 < ε)
    (y : ℝ) : 0 ≤ smoothDensity p v ε y := by
  unfold smoothDensity
  refine div_nonneg (Finset.sum_nonneg fun z _ ↦ mul_nonneg (hp z) ?_) (by linarith)
  exact (indicator_mem_unitInterval 1 _ y zero_le_one le_rfl).1

/-- **The smoothed law has a bounded density.** -/
theorem smoothDensity_le (p v : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hps : ∑ z, p z = 1)
    (ε : ℝ) (hε : 0 < ε) (y : ℝ) : smoothDensity p v ε y ≤ 1 / (2 * ε) := by
  have h2 : (0 : ℝ) < 2 * ε := by linarith
  have hle : (∑ z, p z *
      Set.indicator (Set.Icc (v z - ε) (v z + ε)) (fun _ ↦ (1 : ℝ)) y) ≤ ∑ z, p z := by
    refine Finset.sum_le_sum fun z _ ↦ ?_
    have hind :=
      indicator_mem_unitInterval 1 (Set.Icc (v z - ε) (v z + ε)) y zero_le_one le_rfl
    exact mul_le_of_le_one_right (hp z) hind.2
  rw [hps] at hle
  have hnum : (∑ z, p z *
      Set.indicator (Set.Icc (v z - ε) (v z + ε)) (fun _ ↦ (1 : ℝ)) y) ≤ 1 := hle
  unfold smoothDensity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr h2))

/-- **The smoothed density is a probability density.** -/
theorem smoothDensity_integral (p v : Z → ℝ) (hps : ∑ z, p z = 1) (ε : ℝ) (hε : 0 < ε) :
    ∫ y, smoothDensity p v ε y = 1 := by
  have h2 : (0 : ℝ) < 2 * ε := by linarith
  have hwin : ∀ z : Z,
      (∫ y, p z * Set.indicator (Set.Icc (v z - ε) (v z + ε)) (fun _ ↦ (1 : ℝ)) y) =
        p z * (2 * ε) := by
    intro z
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  have hintegrable : ∀ z ∈ Finset.univ,
      MeasureTheory.Integrable
        (fun y ↦ p z *
          Set.indicator (Set.Icc (v z - ε) (v z + ε)) (fun _ ↦ (1 : ℝ)) y) := by
    intro z _
    refine MeasureTheory.Integrable.const_mul ?_ _
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  unfold smoothDensity
  rw [MeasureTheory.integral_div, MeasureTheory.integral_finset_sum _ hintegrable]
  rw [Finset.sum_congr rfl fun z _ ↦ hwin z, ← Finset.sum_mul, hps, one_mul]
  field_simp

/-- **PL Theorem 7.4, smoothed radial coordinates.** Convolving a radial coordinate law
with uniform noise preserves the matched raw moments through degree `k`. -/
theorem radial_smoothed_moment_match {k : ℕ} (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (a b ε : ℝ) (j : ℕ) (hj : j ≤ k) :
    (∑ z, radialLaw r false z *
        ((1 / (2 * ε)) * ∫ u in (-ε)..ε, (coordValue r a b z + u) ^ j)) =
      ∑ z, radialLaw r true z *
        ((1 / (2 * ε)) * ∫ u in (-ε)..ε, (coordValue r a b z + u) ^ j) :=
  smoothed_moment_match (radialLaw r false) (radialLaw r true) (coordValue r a b) k
    (fun m hm ↦ coord_moment_match r hinj a b m hm) ε j hj

/-- The smoothed radial coordinate law has a density bounded by `1/(2ε)`. -/
theorem radial_smoothDensity_le {k : ℕ} (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (s : Bool) (a b ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    smoothDensity (radialLaw r s) (coordValue r a b) ε y ≤ 1 / (2 * ε) :=
  smoothDensity_le (radialLaw r s) (coordValue r a b) (radialLaw_nonneg r s)
    (radialLaw_sum r hinj s) ε hε y

end

end Descent.Portability.SmoothedCoordinateLaws
