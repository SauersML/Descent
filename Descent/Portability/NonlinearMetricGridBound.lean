/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMetricIdentification

assert_below Descent.Decision Descent.Program

/-!
# A certified finite grid for a nonlinear report metric

The compatible laws of a specified linear information system form a polytope, and a nonlinear
report metric on it is not handled by the exact interval of the linear case. When the metric
is Lipschitz in total variation, rounding the mixture weights of any compatible law down to
multiples of one over the grid size, and giving the last vertex the remaining mass, produces
a grid law whose metric value exceeds the original by at most the Lipschitz constant times
twice the number of non-final vertices over the grid size. Every grid law is itself a
compatible mixture, so the grid values never fall below the true minimum.

This is TQ Proposition 7.4 (7.8). The rounded weights are an explicit `def`, and each of its
required properties is proved: nonnegativity, total mass one, being an integer multiple of
one over the grid size, and the total-variation distance bound. The Lipschitz hypothesis is
required only between mixtures of the given vertices, which is where the manuscript uses it,
and the manuscript's warning about a vanishing denominator is respected by taking the
constant as given rather than deriving one.

The vertices are indexed by `Fin (count + 1)`, so the manuscript's `m - 1` appears as `count`
and no truncated subtraction is needed. The hypotheses are the manuscript's domain
conditions: a positive grid size, vertices that are probability laws, and a Lipschitz
constant valid on the mixtures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonlinearMetricGridBound

noncomputable section

variable {S : Type*} [Fintype S]

/-- The integer numerator of a rounded-down mixture weight. -/
def floorCount (steps : ℕ) (value : ℝ) : ℕ := ⌊(steps : ℝ) * value⌋₊

/-- The grid weights of TQ Proposition 7.4: every weight but the last is rounded down to a
multiple of one over the grid size, and the last vertex receives the remaining mass. -/
def roundedWeights (count steps : ℕ) (weight : Fin (count + 1) → ℝ) :
    Fin (count + 1) → ℝ :=
  Fin.lastCases
    (1 - ∑ k : Fin count, (floorCount steps (weight k.castSucc) : ℝ) / steps)
    fun k ↦ (floorCount steps (weight k.castSucc) : ℝ) / steps

/-- The grid weight at a non-final vertex. -/
theorem roundedWeights_castSucc (count steps : ℕ) (weight : Fin (count + 1) → ℝ)
    (k : Fin count) :
    roundedWeights count steps weight k.castSucc =
      (floorCount steps (weight k.castSucc) : ℝ) / steps := by
  simp [roundedWeights]

/-- The grid weight at the final vertex. -/
theorem roundedWeights_last (count steps : ℕ) (weight : Fin (count + 1) → ℝ) :
    roundedWeights count steps weight (Fin.last count) =
      1 - ∑ k : Fin count, (floorCount steps (weight k.castSucc) : ℝ) / steps := by
  simp [roundedWeights]

/-- Rounding down never increases a weight, and loses less than one grid step. -/
theorem floorCount_bounds (steps : ℕ) (hsteps : 0 < steps) (value : ℝ) (hvalue : 0 ≤ value) :
    (floorCount steps value : ℝ) / steps ≤ value ∧
      value - (floorCount steps value : ℝ) / steps ≤ 1 / steps := by
  have hpos : (0 : ℝ) < steps := by exact_mod_cast hsteps
  have hnn : (0 : ℝ) ≤ (steps : ℝ) * value := by positivity
  have hle : ((floorCount steps value : ℕ) : ℝ) ≤ (steps : ℝ) * value :=
    Nat.floor_le hnn
  have hlt : (steps : ℝ) * value < ((floorCount steps value : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  constructor
  · rw [div_le_iff₀ hpos]
    linarith
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
    linarith

/-- The grid weights are nonnegative, sum to one, and are integer multiples of one grid
step, so a grid law is itself a compatible mixture of the vertices. -/
theorem roundedWeights_valid (count steps : ℕ) (hsteps : 0 < steps)
    (weight : Fin (count + 1) → ℝ) (hw0 : ∀ k, 0 ≤ weight k) (hw1 : ∑ k, weight k = 1) :
    (∀ k, 0 ≤ roundedWeights count steps weight k) ∧
      (∑ k, roundedWeights count steps weight k = 1) ∧
      ∀ k, ∃ numerator : ℕ,
        roundedWeights count steps weight k = (numerator : ℝ) / steps := by
  have hpos : (0 : ℝ) < steps := by exact_mod_cast hsteps
  have hsplit : ∑ k : Fin count, weight k.castSucc + weight (Fin.last count) = 1 := by
    rw [← Fin.sum_univ_castSucc]
    exact hw1
  have hlower : ∀ k : Fin count,
      (floorCount steps (weight k.castSucc) : ℝ) / steps ≤ weight k.castSucc := fun k ↦
    (floorCount_bounds steps hsteps _ (hw0 k.castSucc)).1
  have hsum_le : (∑ k : Fin count, (floorCount steps (weight k.castSucc) : ℝ) / steps) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun k _ ↦ hlower k) ?_
    have := hw0 (Fin.last count)
    linarith
  have hnat : (∑ k : Fin count, floorCount steps (weight k.castSucc)) ≤ steps := by
    have hcast : ((∑ k : Fin count, floorCount steps (weight k.castSucc) : ℕ) : ℝ) ≤
        (steps : ℝ) := by
      rw [Nat.cast_sum]
      rw [← div_le_one hpos]
      rw [Finset.sum_div]
      exact hsum_le
    exact_mod_cast hcast
  refine ⟨fun k ↦ ?_, ?_, fun k ↦ ?_⟩
  · refine Fin.lastCases ?_ ?_ k
    · rw [roundedWeights_last]
      linarith
    · intro j
      rw [roundedWeights_castSucc]
      positivity
  · rw [Fin.sum_univ_castSucc]
    have hcast : ∑ k : Fin count, roundedWeights count steps weight k.castSucc =
        ∑ k : Fin count, (floorCount steps (weight k.castSucc) : ℝ) / steps :=
      Finset.sum_congr rfl fun k _ ↦ roundedWeights_castSucc count steps weight k
    rw [hcast, roundedWeights_last]
    ring
  · refine Fin.lastCases ?_ ?_ k
    · refine ⟨steps - ∑ j : Fin count, floorCount steps (weight j.castSucc), ?_⟩
      rw [roundedWeights_last, Nat.cast_sub hnat, Nat.cast_sum, sub_div,
        div_self (ne_of_gt hpos), Finset.sum_div]
    · intro j
      exact ⟨floorCount steps (weight j.castSucc), roundedWeights_castSucc count steps weight j⟩

/-- The rounding error of TQ (7.8): the grid weights differ from the original weights by at
most twice the number of non-final vertices over the grid size. -/
theorem roundedWeights_close (count steps : ℕ) (hsteps : 0 < steps)
    (weight : Fin (count + 1) → ℝ) (hw0 : ∀ k, 0 ≤ weight k) (hw1 : ∑ k, weight k = 1) :
    ∑ k, |weight k - roundedWeights count steps weight k| ≤ 2 * count / steps := by
  have hpos : (0 : ℝ) < steps := by exact_mod_cast hsteps
  have hgap : ∀ k : Fin count,
      |weight k.castSucc - roundedWeights count steps weight k.castSucc| ≤ 1 / steps := by
    intro k
    rw [roundedWeights_castSucc]
    obtain ⟨hle, hclose⟩ := floorCount_bounds steps hsteps _ (hw0 k.castSucc)
    rw [abs_of_nonneg (by linarith)]
    exact hclose
  have hhead : ∑ k : Fin count,
      |weight k.castSucc - roundedWeights count steps weight k.castSucc| ≤ count / steps := by
    refine le_trans (Finset.sum_le_sum fun k _ ↦ hgap k) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div]
  have hsplit : ∑ k : Fin count, weight k.castSucc + weight (Fin.last count) = 1 := by
    rw [← Fin.sum_univ_castSucc]
    exact hw1
  have hcast : ∑ k : Fin count, roundedWeights count steps weight k.castSucc =
      ∑ k : Fin count, (floorCount steps (weight k.castSucc) : ℝ) / steps :=
    Finset.sum_congr rfl fun k _ ↦ roundedWeights_castSucc count steps weight k
  have htaildiff : weight (Fin.last count) - roundedWeights count steps weight
      (Fin.last count) =
        ∑ k : Fin count, (roundedWeights count steps weight k.castSucc - weight k.castSucc) := by
    rw [Finset.sum_sub_distrib, roundedWeights_last, ← hcast]
    linarith
  have htail : |weight (Fin.last count) -
      roundedWeights count steps weight (Fin.last count)| ≤ count / steps := by
    rw [htaildiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) hhead
    rw [abs_sub_comm]
  rw [Fin.sum_univ_castSucc]
  have hcombine : (count : ℝ) / steps + (count : ℝ) / steps = 2 * count / steps := by
    ring
  linarith

/-- The total variation between two mixtures of probability vertices is at most the total
variation between their weights. -/
theorem mixture_distance_le (count : ℕ) (vertex : Fin (count + 1) → (S → ℝ))
    (hnonneg : ∀ k s, 0 ≤ vertex k s) (hmass : ∀ k, ∑ s, vertex k s = 1)
    (first second : Fin (count + 1) → ℝ) :
    ∑ s, |(∑ k, first k • vertex k) s - (∑ k, second k • vertex k) s| ≤
      ∑ k, |first k - second k| := by
  have hpoint : ∀ s : S,
      |(∑ k, first k • vertex k) s - (∑ k, second k • vertex k) s| ≤
        ∑ k, |first k - second k| * vertex k s := by
    intro s
    have hrw : (∑ k, first k • vertex k) s - (∑ k, second k • vertex k) s =
        ∑ k, (first k - second k) * vertex k s := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hrw]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (hnonneg k s)]
  refine le_trans (Finset.sum_le_sum fun s _ ↦ hpoint s) ?_
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [← Finset.mul_sum, hmass k, mul_one]

/-- TQ Proposition 7.4 (7.8): for every compatible mixture there is a grid mixture whose
metric value exceeds it by at most the Lipschitz constant times twice the number of non-final
vertices over the grid size, and that grid mixture is itself a compatible mixture, so the
grid values never fall below the true minimum. -/
theorem exists_grid_mixture_near (count steps : ℕ) (hsteps : 0 < steps)
    (vertex : Fin (count + 1) → (S → ℝ)) (hnonneg : ∀ k s, 0 ≤ vertex k s)
    (hmass : ∀ k, ∑ s, vertex k s = 1) (weight : Fin (count + 1) → ℝ)
    (hw0 : ∀ k, 0 ≤ weight k) (hw1 : ∑ k, weight k = 1) (metric : (S → ℝ) → ℝ) (lip : ℝ)
    (hlip0 : 0 ≤ lip)
    (hlip : ∀ first second : Fin (count + 1) → ℝ,
      |metric (∑ k, first k • vertex k) - metric (∑ k, second k • vertex k)| ≤
        lip * ∑ s, |(∑ k, first k • vertex k) s - (∑ k, second k • vertex k) s|) :
    ∃ grid : Fin (count + 1) → ℝ, (∀ k, 0 ≤ grid k) ∧ (∑ k, grid k = 1) ∧
      (∀ k, ∃ numerator : ℕ, grid k = (numerator : ℝ) / steps) ∧
      metric (∑ k, grid k • vertex k) ≤
        metric (∑ k, weight k • vertex k) + lip * (2 * count / steps) := by
  obtain ⟨hg0, hg1, hgrid⟩ := roundedWeights_valid count steps hsteps weight hw0 hw1
  refine ⟨roundedWeights count steps weight, hg0, hg1, hgrid, ?_⟩
  have hclose := roundedWeights_close count steps hsteps weight hw0 hw1
  have hdist := mixture_distance_le count vertex hnonneg hmass
    (roundedWeights count steps weight) weight
  have hweights : ∑ k, |roundedWeights count steps weight k - weight k| ≤
      2 * count / steps := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ ↦ ?_)) hclose
    rw [abs_sub_comm]
  have hlipbound := hlip (roundedWeights count steps weight) weight
  have habs := abs_le.1 hlipbound
  have hchain : lip * ∑ s, |(∑ k, roundedWeights count steps weight k • vertex k) s -
      (∑ k, weight k • vertex k) s| ≤ lip * (2 * count / steps) :=
    mul_le_mul_of_nonneg_left (le_trans hdist hweights) hlip0
  linarith [habs.2]

end

end Descent.Portability.NonlinearMetricGridBound
